use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use chrono::{TimeZone, Utc};
use rusqlite::{params, Connection};
use serde::Serialize;
use serde_json::{json, Value as JsonValue};
use toml_edit::Document;

use crate::modules;

const DEFAULT_INSTANCE_ID: &str = "__default__";
const DEFAULT_INSTANCE_NAME: &str = "默认实例";
const DEFAULT_PROVIDER_ID: &str = "openai";
const STATE_DB_FILE: &str = "state_5.sqlite";
const CONFIG_FILE_NAME: &str = "config.toml";
const SESSION_INDEX_FILE: &str = "session_index.jsonl";
const GLOBAL_STATE_FILE: &str = ".codex-global-state.json";
const THREAD_PROJECT_ASSIGNMENTS_KEY: &str = "thread-project-assignments";
const PROJECT_ORDER_KEY: &str = "project-order";
const ELECTRON_SAVED_WORKSPACE_ROOTS_KEY: &str = "electron-saved-workspace-roots";
const SESSION_DIRS: [&str; 2] = ["sessions", "archived_sessions"];
const SESSION_VISIBILITY_REPAIR_BACKUP_PREFIX: &str = "backup-";
const SESSION_VISIBILITY_REPAIR_BACKUP_SUFFIX: &str = "-session-visibility-repair";
const MAX_SESSION_VISIBILITY_REPAIR_BACKUPS: usize = 1;
const RECENT_CONVERSATION_PAGE_SIZE: usize = 50;
const RECENT_CONVERSATION_REBALANCE_SCAN_LIMIT: usize = 15;

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CodexSessionVisibilityRepairItem {
    pub instance_id: String,
    pub instance_name: String,
    pub target_provider: String,
    pub changed_rollout_file_count: usize,
    pub updated_sqlite_row_count: usize,
    pub added_session_index_entry_count: usize,
    pub updated_session_index_entry_count: usize,
    pub updated_thread_project_assignment_count: usize,
    pub updated_recent_window_thread_count: usize,
    pub skipped_sqlite_file: bool,
    pub backup_dir: Option<String>,
    pub running: bool,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CodexSessionVisibilityRepairSummary {
    pub instance_count: usize,
    pub mutated_instance_count: usize,
    pub changed_rollout_file_count: usize,
    pub updated_sqlite_row_count: usize,
    pub added_session_index_entry_count: usize,
    pub updated_session_index_entry_count: usize,
    pub updated_thread_project_assignment_count: usize,
    pub updated_recent_window_thread_count: usize,
    pub skipped_sqlite_file_count: usize,
    pub items: Vec<CodexSessionVisibilityRepairItem>,
    pub backup_dirs: Vec<String>,
    pub message: String,
}

#[derive(Debug, Clone)]
struct CodexSyncInstance {
    id: String,
    name: String,
    data_dir: PathBuf,
    last_pid: Option<u32>,
}

#[derive(Debug, Clone)]
struct RolloutProviderChange {
    relative_path: PathBuf,
    absolute_path: PathBuf,
    updated_first_line: Option<String>,
    target_modified_at: Option<SystemTime>,
}

#[derive(Debug, Clone, Copy)]
struct SqliteProviderScan {
    rows_to_update: usize,
    skipped_unusable_database: bool,
}

#[derive(Debug, Clone, Copy)]
struct ThreadsTableColumns {
    updated_at: bool,
    updated_at_ms: bool,
    model_provider: bool,
    has_user_event: bool,
    first_user_message: bool,
    thread_source: bool,
}

#[derive(Debug, Clone)]
struct SqliteThreadIndexRow {
    id: String,
    title: String,
    updated_at: Option<i64>,
    updated_at_ms: Option<i64>,
    cwd: Option<String>,
    archived: Option<i64>,
    first_user_message: Option<String>,
    thread_source: Option<String>,
    has_updated_at_column: bool,
    has_updated_at_ms_column: bool,
    has_first_user_message_column: bool,
    has_thread_source_column: bool,
}

#[derive(Debug, Clone)]
struct RecentWindowRebalanceChange {
    thread_id: String,
    updated_at: Option<i64>,
    updated_at_ms: Option<i64>,
}

#[derive(Debug, Clone, Copy, Default)]
struct SessionIndexDrift {
    missing_entries: usize,
    updated_entries: usize,
}

impl SessionIndexDrift {
    fn needs_repair(self) -> bool {
        self.missing_entries > 0 || self.updated_entries > 0
    }
}

pub fn repair_session_visibility_across_instances(
) -> Result<CodexSessionVisibilityRepairSummary, String> {
    let instances = collect_instances()?;
    let process_entries = modules::process::collect_codex_process_entries();
    let mut items = Vec::with_capacity(instances.len());
    let mut backup_dirs = Vec::new();
    let mut mutated_instance_count = 0usize;
    let mut changed_rollout_file_count = 0usize;
    let mut updated_sqlite_row_count = 0usize;
    let mut added_session_index_entry_count = 0usize;
    let mut updated_session_index_entry_count = 0usize;
    let mut updated_thread_project_assignment_count = 0usize;
    let mut updated_recent_window_thread_count = 0usize;
    let mut skipped_sqlite_file_count = 0usize;
    let mut mutated_running_instance_count = 0usize;

    for instance in &instances {
        let running = is_instance_running(instance, &process_entries);
        let target_provider = read_target_provider(&instance.data_dir)?;
        let rollout_changes =
            collect_rollout_provider_changes(&instance.data_dir, &target_provider)?;
        let sqlite_scan = count_sqlite_rows_to_update(&instance.data_dir, &target_provider)?;
        let sqlite_rows_to_update = sqlite_scan.rows_to_update;
        let session_index_drift = count_session_index_drift(&instance.data_dir)?;
        if sqlite_scan.skipped_unusable_database {
            skipped_sqlite_file_count += 1;
        }

        let missing_thread_project_assignments =
            count_missing_thread_project_assignments(&instance.data_dir)?;
        let recent_window_rows_to_rebalance =
            count_recent_window_rows_to_rebalance(&instance.data_dir)?;
        let reconcile_session_index =
            session_index_drift.needs_repair() || recent_window_rows_to_rebalance > 0;
        if rollout_changes.is_empty()
            && sqlite_rows_to_update == 0
            && !reconcile_session_index
            && missing_thread_project_assignments == 0
            && recent_window_rows_to_rebalance == 0
        {
            items.push(CodexSessionVisibilityRepairItem {
                instance_id: instance.id.clone(),
                instance_name: instance.name.clone(),
                target_provider,
                changed_rollout_file_count: 0,
                updated_sqlite_row_count: 0,
                added_session_index_entry_count: 0,
                updated_session_index_entry_count: 0,
                updated_thread_project_assignment_count: 0,
                updated_recent_window_thread_count: 0,
                skipped_sqlite_file: sqlite_scan.skipped_unusable_database,
                backup_dir: None,
                running,
            });
            continue;
        }

        let backup_dir = backup_instance_files(
            &instance.data_dir,
            &rollout_changes,
            sqlite_rows_to_update > 0 || recent_window_rows_to_rebalance > 0,
            reconcile_session_index,
            missing_thread_project_assignments > 0,
            &instance.id,
            &target_provider,
        )?;
        let backup_dir_string = backup_dir.to_string_lossy().to_string();

        let repaired = repair_single_instance(
            &instance.data_dir,
            &target_provider,
            &rollout_changes,
            sqlite_rows_to_update > 0,
            reconcile_session_index,
            missing_thread_project_assignments > 0,
            recent_window_rows_to_rebalance > 0,
        );
        let (
            sqlite_rows_updated,
            session_index_entries_added,
            session_index_entries_updated,
            thread_project_assignments_updated,
            recent_window_threads_updated,
        ) = match repaired {
            Ok(value) => value,
            Err(error) => {
                let restore_result = restore_instance_files_from_backup(
                    &instance.data_dir,
                    &backup_dir,
                    sqlite_rows_to_update > 0 || recent_window_rows_to_rebalance > 0,
                    missing_thread_project_assignments > 0,
                );
                if let Err(restore_error) = restore_result {
                    return Err(format!(
                        "修复实例历史会话可见性失败 ({}): {}；自动回滚也失败: {}；备份目录: {}",
                        instance.name,
                        error,
                        restore_error,
                        backup_dir.display()
                    ));
                }
                return Err(format!(
                    "修复实例历史会话可见性失败 ({}): {}；已自动回滚，备份目录: {}",
                    instance.name,
                    error,
                    backup_dir.display()
                ));
            }
        };

        mutated_instance_count += 1;
        changed_rollout_file_count += rollout_changes.len();
        updated_sqlite_row_count += sqlite_rows_updated;
        added_session_index_entry_count += session_index_entries_added;
        updated_session_index_entry_count += session_index_entries_updated;
        updated_thread_project_assignment_count += thread_project_assignments_updated;
        updated_recent_window_thread_count += recent_window_threads_updated;
        if running {
            mutated_running_instance_count += 1;
        }
        backup_dirs.push(backup_dir_string.clone());
        items.push(CodexSessionVisibilityRepairItem {
            instance_id: instance.id.clone(),
            instance_name: instance.name.clone(),
            target_provider,
            changed_rollout_file_count: rollout_changes.len(),
            updated_sqlite_row_count: sqlite_rows_updated,
            added_session_index_entry_count: session_index_entries_added,
            updated_session_index_entry_count: session_index_entries_updated,
            updated_thread_project_assignment_count: thread_project_assignments_updated,
            updated_recent_window_thread_count: recent_window_threads_updated,
            skipped_sqlite_file: sqlite_scan.skipped_unusable_database,
            backup_dir: Some(backup_dir_string),
            running,
        });
    }

    prune_session_visibility_repair_backups(&instances);

    let message = build_summary_message(
        mutated_instance_count,
        changed_rollout_file_count,
        updated_sqlite_row_count,
        added_session_index_entry_count,
        updated_session_index_entry_count,
        updated_thread_project_assignment_count,
        updated_recent_window_thread_count,
        mutated_running_instance_count,
        skipped_sqlite_file_count,
    );

    Ok(CodexSessionVisibilityRepairSummary {
        instance_count: instances.len(),
        mutated_instance_count,
        changed_rollout_file_count,
        updated_sqlite_row_count,
        added_session_index_entry_count,
        updated_session_index_entry_count,
        updated_thread_project_assignment_count,
        updated_recent_window_thread_count,
        skipped_sqlite_file_count,
        items,
        backup_dirs,
        message,
    })
}

pub fn read_history_visibility_provider_for_dir(data_dir: &Path) -> Result<String, String> {
    read_target_provider(data_dir)
}

fn repair_single_instance(
    data_dir: &Path,
    target_provider: &str,
    rollout_changes: &[RolloutProviderChange],
    update_sqlite: bool,
    reconcile_session_index: bool,
    reconcile_project_assignments: bool,
    rebalance_recent_window: bool,
) -> Result<(usize, usize, usize, usize, usize), String> {
    let sqlite_rows_updated = if update_sqlite {
        update_sqlite_provider(data_dir, target_provider)?
    } else {
        0
    };
    for change in rollout_changes {
        rewrite_rollout_provider(change)?;
    }
    let recent_window_threads_updated = if rebalance_recent_window {
        rebalance_recent_window_order(data_dir)?
    } else {
        0
    };
    let (session_index_entries_added, session_index_entries_updated) = if reconcile_session_index {
        reconcile_session_index_from_sqlite(data_dir, rebalance_recent_window)?
    } else {
        (0, 0)
    };
    let thread_project_assignments_updated = if reconcile_project_assignments {
        reconcile_thread_project_assignments(data_dir)?
    } else {
        0
    };
    Ok((
        sqlite_rows_updated,
        session_index_entries_added,
        session_index_entries_updated,
        thread_project_assignments_updated,
        recent_window_threads_updated,
    ))
}

fn build_summary_message(
    mutated_instance_count: usize,
    changed_rollout_file_count: usize,
    updated_sqlite_row_count: usize,
    added_session_index_entry_count: usize,
    updated_session_index_entry_count: usize,
    updated_thread_project_assignment_count: usize,
    updated_recent_window_thread_count: usize,
    mutated_running_instance_count: usize,
    _skipped_sqlite_file_count: usize,
) -> String {
    if mutated_instance_count == 0 {
        return "默认 Codex 实例的历史会话 provider 元数据、session_index 与最近会话窗口已一致，无需修复"
            .to_string();
    }

    let index_suffix = if added_session_index_entry_count > 0 {
        format!(
            "，补写 {} 条 session_index 记录",
            added_session_index_entry_count
        )
    } else {
        String::new()
    };
    let index_reorder_suffix = if updated_session_index_entry_count > 0 {
        format!(
            "，重排/更新 {} 条 session_index 记录",
            updated_session_index_entry_count
        )
    } else {
        String::new()
    };
    let assignment_suffix = if updated_thread_project_assignment_count > 0 {
        format!(
            "，补写 {} 条项目归属",
            updated_thread_project_assignment_count
        )
    } else {
        String::new()
    };
    let recent_window_suffix = if updated_recent_window_thread_count > 0 {
        format!(
            "，调整 {} 条最近会话排序时间",
            updated_recent_window_thread_count
        )
    } else {
        String::new()
    };

    if mutated_running_instance_count > 0 {
        return format!(
            "已为默认 Codex 实例修复历史会话可见性：改写 {} 个 rollout 文件，更新 {} 条 SQLite 记录{}{}{}{}。运行中的实例可能需要重启后显示",
            changed_rollout_file_count,
            updated_sqlite_row_count,
            index_suffix,
            index_reorder_suffix,
            assignment_suffix,
            recent_window_suffix
        );
    }

    format!(
        "已为默认 Codex 实例修复历史会话可见性：改写 {} 个 rollout 文件，更新 {} 条 SQLite 记录{}{}{}{}",
        changed_rollout_file_count,
        updated_sqlite_row_count,
        index_suffix,
        index_reorder_suffix,
        assignment_suffix,
        recent_window_suffix
    )
}

fn collect_instances() -> Result<Vec<CodexSyncInstance>, String> {
    let default_dir = modules::codex_instance::get_default_codex_home()?;
    Ok(vec![CodexSyncInstance {
        id: DEFAULT_INSTANCE_ID.to_string(),
        name: DEFAULT_INSTANCE_NAME.to_string(),
        data_dir: default_dir,
        last_pid: None,
    }])
}

fn is_instance_running(
    instance: &CodexSyncInstance,
    process_entries: &[(u32, Option<String>)],
) -> bool {
    let codex_home = instance.data_dir.to_str();
    modules::process::resolve_codex_pid_from_entries(instance.last_pid, codex_home, process_entries)
        .is_some()
}

fn read_target_provider(data_dir: &Path) -> Result<String, String> {
    let config_path = data_dir.join(CONFIG_FILE_NAME);
    if !config_path.exists() {
        return Ok(DEFAULT_PROVIDER_ID.to_string());
    }

    let content = fs::read_to_string(&config_path).map_err(|error| {
        format!(
            "读取 config.toml 失败 ({}): {}",
            config_path.display(),
            error
        )
    })?;
    if content.trim().is_empty() {
        return Ok(DEFAULT_PROVIDER_ID.to_string());
    }

    let doc = content.parse::<Document>().map_err(|error| {
        format!(
            "解析 config.toml 失败 ({}): {}",
            config_path.display(),
            error
        )
    })?;
    let provider = doc
        .get("model_provider")
        .and_then(|item| item.as_str())
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .unwrap_or(DEFAULT_PROVIDER_ID);
    Ok(provider.to_string())
}

fn collect_rollout_provider_changes(
    data_dir: &Path,
    target_provider: &str,
) -> Result<Vec<RolloutProviderChange>, String> {
    let session_index_map = match read_session_index_map(data_dir) {
        Ok(value) => value,
        Err(error) => {
            modules::logger::log_warn(&format!(
                "读取 Codex session_index.jsonl 失败，跳过该时间来源并继续修复会话可见性: {}",
                error
            ));
            HashMap::new()
        }
    };
    let mut changes = Vec::new();

    for dir_name in SESSION_DIRS {
        let root_dir = data_dir.join(dir_name);
        if !root_dir.exists() {
            continue;
        }
        let rollout_paths = list_rollout_files(&root_dir)?;
        for rollout_path in rollout_paths {
            let Some((first_line, _separator)) = read_first_line(&rollout_path)? else {
                continue;
            };
            let Some(mut parsed) = parse_session_meta_record(&first_line) else {
                continue;
            };
            let session_id = session_meta_id(&parsed);
            let target_modified_at = session_id
                .as_deref()
                .and_then(|id| session_index_map.get(id))
                .and_then(parse_session_index_updated_at_ms)
                .or_else(|| rollout_file_activity_ms(&rollout_path))
                .and_then(modules::codex_session_file_time::system_time_from_unix_millis);
            let current_modified_at =
                modules::codex_session_file_time::read_modified_time(&rollout_path);
            let current_provider = parsed["payload"]
                .get("model_provider")
                .and_then(JsonValue::as_str)
                .unwrap_or("");
            let provider_matches = current_provider == target_provider;
            let missing_user_thread_source = should_mark_rollout_thread_source_user(&parsed);
            let modified_time_matches = target_modified_at.is_none()
                || modules::codex_session_file_time::same_modified_time_millis(
                    current_modified_at,
                    target_modified_at,
                );
            if provider_matches && !missing_user_thread_source && modified_time_matches {
                continue;
            }

            let updated_first_line = if !provider_matches || missing_user_thread_source {
                if let Some(payload) = parsed.get_mut("payload").and_then(JsonValue::as_object_mut)
                {
                    if !provider_matches {
                        payload.insert(
                            "model_provider".to_string(),
                            JsonValue::String(target_provider.to_string()),
                        );
                    }
                    if missing_user_thread_source {
                        payload.insert(
                            "thread_source".to_string(),
                            JsonValue::String("user".to_string()),
                        );
                    }
                    Some(
                        serde_json::to_string(&parsed)
                            .map_err(|error| format!("序列化 session_meta 失败: {}", error))?,
                    )
                } else {
                    None
                }
            } else {
                None
            };

            let relative_path = rollout_path
                .strip_prefix(data_dir)
                .map_err(|_| format!("无法计算 rollout 相对路径: {}", rollout_path.display()))?;
            changes.push(RolloutProviderChange {
                relative_path: relative_path.to_path_buf(),
                absolute_path: rollout_path,
                updated_first_line,
                target_modified_at,
            });
        }
    }

    changes.sort_by(|left, right| left.relative_path.cmp(&right.relative_path));
    Ok(changes)
}

fn should_mark_rollout_thread_source_user(meta: &JsonValue) -> bool {
    let Some(payload) = meta.get("payload") else {
        return false;
    };
    let existing_thread_source = payload
        .get("thread_source")
        .and_then(JsonValue::as_str)
        .map(str::trim)
        .unwrap_or("");
    if !existing_thread_source.is_empty() {
        return false;
    }

    matches!(
        payload.get("source").and_then(JsonValue::as_str),
        Some("cli" | "vscode" | "appServer")
    )
}

fn list_rollout_files(root_dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut result = Vec::new();
    let entries = fs::read_dir(root_dir)
        .map_err(|error| format!("读取目录失败 ({}): {}", root_dir.display(), error))?;

    for entry in entries {
        let entry =
            entry.map_err(|error| format!("读取目录项失败 ({}): {}", root_dir.display(), error))?;
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("读取文件类型失败 ({}): {}", path.display(), error))?;
        if file_type.is_dir() {
            result.extend(list_rollout_files(&path)?);
            continue;
        }
        if file_type.is_file() {
            let file_name = path
                .file_name()
                .and_then(|item| item.to_str())
                .unwrap_or_default();
            if file_name.starts_with("rollout-") && file_name.ends_with(".jsonl") {
                result.push(path);
            }
        }
    }

    result.sort();
    Ok(result)
}

fn read_first_line(path: &Path) -> Result<Option<(String, String)>, String> {
    let file = fs::File::open(path)
        .map_err(|error| format!("打开 rollout 文件失败 ({}): {}", path.display(), error))?;
    let mut reader = BufReader::new(file);
    let mut buffer = Vec::new();
    let bytes_read = reader
        .read_until(b'\n', &mut buffer)
        .map_err(|error| format!("读取 rollout 首行失败 ({}): {}", path.display(), error))?;
    if bytes_read == 0 {
        return Ok(None);
    }

    let (line_bytes, separator) = if buffer.ends_with(b"\r\n") {
        (&buffer[..buffer.len() - 2], "\r\n")
    } else if buffer.ends_with(b"\n") {
        (&buffer[..buffer.len() - 1], "\n")
    } else {
        (&buffer[..], "")
    };

    let line = String::from_utf8(line_bytes.to_vec()).map_err(|error| {
        format!(
            "解析 rollout 首行 UTF-8 失败 ({}): {}",
            path.display(),
            error
        )
    })?;
    Ok(Some((line, separator.to_string())))
}

fn parse_session_meta_record(first_line: &str) -> Option<JsonValue> {
    if first_line.trim().is_empty() {
        return None;
    }

    let parsed = serde_json::from_str::<JsonValue>(first_line).ok()?;
    if parsed.get("type").and_then(JsonValue::as_str) != Some("session_meta") {
        return None;
    }
    if !parsed.get("payload").is_some_and(JsonValue::is_object) {
        return None;
    }
    Some(parsed)
}

fn session_meta_id(meta: &JsonValue) -> Option<String> {
    meta.get("payload")
        .and_then(|payload| payload.get("id").or_else(|| payload.get("session_id")))
        .and_then(JsonValue::as_str)
        .map(str::to_string)
        .or_else(|| {
            meta.get("id")
                .or_else(|| meta.get("session_id"))
                .and_then(JsonValue::as_str)
                .map(str::to_string)
        })
}

fn read_session_index_map(root_dir: &Path) -> Result<HashMap<String, JsonValue>, String> {
    let path = root_dir.join(SESSION_INDEX_FILE);
    if !path.exists() {
        return Ok(HashMap::new());
    }

    let content = fs::read_to_string(&path).map_err(|error| {
        format!(
            "读取 session_index.jsonl 失败 ({}): {}",
            path.display(),
            error
        )
    })?;
    let mut entries = HashMap::new();
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        let Ok(entry) = serde_json::from_str::<JsonValue>(trimmed) else {
            continue;
        };
        let Some(id) = entry.get("id").and_then(JsonValue::as_str) else {
            continue;
        };
        entries.insert(id.to_string(), entry);
    }
    Ok(entries)
}

fn count_missing_session_index_entries(data_dir: &Path) -> Result<usize, String> {
    Ok(count_session_index_drift(data_dir)?.missing_entries)
}

fn count_session_index_drift(data_dir: &Path) -> Result<SessionIndexDrift, String> {
    let session_index_map = read_session_index_map(data_dir)?;
    let visible_rows = collect_session_index_visible_rows(data_dir)?;
    if visible_rows.is_empty() {
        return Ok(SessionIndexDrift::default());
    }

    let visible_ids = visible_rows
        .iter()
        .map(|row| row.id.clone())
        .collect::<HashSet<_>>();
    let missing_entries = visible_rows
        .iter()
        .filter(|row| !session_index_map.contains_key(&row.id))
        .count();
    let existing_tail = read_session_index_lines(data_dir)?
        .into_iter()
        .filter_map(|line| serde_json::from_str::<JsonValue>(line.trim()).ok())
        .filter_map(|entry| {
            entry
                .get("id")
                .and_then(JsonValue::as_str)
                .map(str::to_string)
        })
        .rev()
        .filter(|id| visible_ids.contains(id))
        .take(visible_rows.len())
        .collect::<Vec<_>>();
    let expected_tail = visible_rows
        .iter()
        .rev()
        .map(|row| row.id.clone())
        .collect::<Vec<_>>();
    let mut updated_entries = 0usize;
    if existing_tail != expected_tail {
        updated_entries = visible_rows.len().saturating_sub(missing_entries);
    }

    Ok(SessionIndexDrift {
        missing_entries,
        updated_entries,
    })
}

fn load_sqlite_thread_index_rows(data_dir: &Path) -> Result<Vec<SqliteThreadIndexRow>, String> {
    let db_path = data_dir.join(STATE_DB_FILE);
    if !db_path.exists() {
        return Ok(Vec::new());
    }

    let connection = match Connection::open(&db_path) {
        Ok(connection) => connection,
        Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(Vec::new());
        }
        Err(error) => {
            return Err(format!(
                "打开实例数据库失败 ({}): {}",
                db_path.display(),
                error
            ));
        }
    };

    let mut statement = match connection.prepare("PRAGMA table_info(threads)") {
        Ok(statement) => statement,
        Err(error) if is_missing_threads_table_error(&error) => return Ok(Vec::new()),
        Err(error) => {
            return Err(format_sqlite_read_error(
                &db_path,
                "读取 SQLite threads 表结构失败",
                &error,
            ));
        }
    };
    let rows = statement
        .query_map([], |row| row.get::<usize, String>(1))
        .map_err(|error| {
            format_sqlite_read_error(&db_path, "读取 SQLite threads 表结构失败", &error)
        })?;
    let mut names = HashSet::new();
    for row in rows {
        names.insert(row.map_err(|error| {
            format_sqlite_read_error(&db_path, "读取 SQLite threads 表结构失败", &error)
        })?);
    }
    if !names.contains("id") {
        return Ok(Vec::new());
    }

    let title_expr = if names.contains("title") {
        "COALESCE(title, '')"
    } else {
        "''"
    };
    let updated_at_expr = if names.contains("updated_at") {
        "updated_at"
    } else {
        "NULL"
    };
    let updated_at_ms_expr = if names.contains("updated_at_ms") {
        "updated_at_ms"
    } else {
        "NULL"
    };
    let cwd_expr = if names.contains("cwd") {
        "COALESCE(cwd, '')"
    } else {
        "''"
    };
    let archived_expr = if names.contains("archived") {
        "archived"
    } else {
        "0"
    };
    let first_user_message_expr = if names.contains("first_user_message") {
        "COALESCE(first_user_message, '')"
    } else {
        "''"
    };
    let thread_source_expr = if names.contains("thread_source") {
        "COALESCE(thread_source, '')"
    } else {
        "''"
    };
    let sql =
        format!("SELECT id, {title_expr}, {updated_at_expr}, {updated_at_ms_expr}, {cwd_expr}, {archived_expr}, {first_user_message_expr}, {thread_source_expr} FROM threads ORDER BY COALESCE({updated_at_ms_expr}, {updated_at_expr} * 1000, 0) DESC");
    let mut statement = connection.prepare(sql.as_str()).map_err(|error| {
        format!(
            "准备 SQLite 会话索引查询失败 ({}): {}",
            db_path.display(),
            error
        )
    })?;
    let mapped = statement
        .query_map([], |row| {
            Ok(SqliteThreadIndexRow {
                id: row.get(0)?,
                title: row.get(1)?,
                updated_at: row.get(2)?,
                updated_at_ms: row.get(3)?,
                cwd: row.get(4)?,
                archived: row.get(5)?,
                first_user_message: row.get(6)?,
                thread_source: row.get(7)?,
                has_updated_at_column: names.contains("updated_at"),
                has_updated_at_ms_column: names.contains("updated_at_ms"),
                has_first_user_message_column: names.contains("first_user_message"),
                has_thread_source_column: names.contains("thread_source"),
            })
        })
        .map_err(|error| {
            format!(
                "查询 SQLite 会话索引行失败 ({}): {}",
                db_path.display(),
                error
            )
        })?;
    let mut result = Vec::new();
    for row in mapped {
        result.push(row.map_err(|error| {
            format!(
                "读取 SQLite 会话索引行失败 ({}): {}",
                db_path.display(),
                error
            )
        })?);
    }
    Ok(result)
}

fn format_thread_updated_at_iso_for_row(row: &SqliteThreadIndexRow) -> String {
    let millis = row
        .updated_at_ms
        .map(normalize_codex_timestamp_ms)
        .or_else(|| row.updated_at.map(normalize_codex_timestamp_ms))
        .unwrap_or_else(|| Utc::now().timestamp_millis() as i128);
    let seconds = (millis / 1_000) as i64;
    let nanos = ((millis % 1_000).max(0) as u32) * 1_000_000;
    Utc.timestamp_opt(seconds, nanos)
        .single()
        .unwrap_or_else(Utc::now)
        .to_rfc3339_opts(chrono::SecondsFormat::Micros, true)
}

fn build_session_index_entry_from_thread(row: &SqliteThreadIndexRow) -> JsonValue {
    json!({
        "id": row.id,
        "thread_name": if row.title.trim().is_empty() {
            "Untitled"
        } else {
            row.title.as_str()
        },
        "updated_at": format_thread_updated_at_iso_for_row(row),
    })
}

fn read_session_index_lines(data_dir: &Path) -> Result<Vec<String>, String> {
    let path = data_dir.join(SESSION_INDEX_FILE);
    if !path.exists() {
        return Ok(Vec::new());
    }
    Ok(fs::read_to_string(&path)
        .map_err(|error| {
            format!(
                "读取 session_index.jsonl 失败 ({}): {}",
                path.display(),
                error
            )
        })?
        .lines()
        .map(str::to_string)
        .collect::<Vec<_>>())
}

fn collect_session_index_visible_rows(
    data_dir: &Path,
) -> Result<Vec<SqliteThreadIndexRow>, String> {
    let mut rows = load_sqlite_thread_index_rows(data_dir)?
        .into_iter()
        .filter(|row| {
            if row.has_first_user_message_column || row.has_thread_source_column {
                is_user_visible_thread_row(row)
            } else {
                true
            }
        })
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| {
        let left_time = left
            .updated_at_ms
            .map(normalize_codex_timestamp_ms)
            .or_else(|| left.updated_at.map(normalize_codex_timestamp_ms))
            .unwrap_or_default();
        let right_time = right
            .updated_at_ms
            .map(normalize_codex_timestamp_ms)
            .or_else(|| right.updated_at.map(normalize_codex_timestamp_ms))
            .unwrap_or_default();
        left_time
            .cmp(&right_time)
            .then_with(|| left.id.cmp(&right.id))
    });
    Ok(rows)
}

fn reconcile_session_index_from_sqlite(
    data_dir: &Path,
    force_rebuild_visible_tail: bool,
) -> Result<(usize, usize), String> {
    let drift = count_session_index_drift(data_dir)?;
    if !force_rebuild_visible_tail && !drift.needs_repair() {
        return Ok((0, 0));
    }

    let rows = collect_session_index_visible_rows(data_dir)?;
    let visible_ids = rows
        .iter()
        .map(|row| row.id.clone())
        .collect::<HashSet<_>>();
    let mut seen_preserved_ids = HashSet::new();
    let mut lines = read_session_index_lines(data_dir)?
        .into_iter()
        .filter(|line| {
            let Ok(entry) = serde_json::from_str::<JsonValue>(line.trim()) else {
                return true;
            };
            let Some(id) = entry.get("id").and_then(JsonValue::as_str) else {
                return true;
            };
            if visible_ids.contains(id) {
                return false;
            }
            seen_preserved_ids.insert(id.to_string())
        })
        .collect::<Vec<_>>();
    while lines.last().is_some_and(|line| line.trim().is_empty()) {
        lines.pop();
    }

    for row in &rows {
        let entry = build_session_index_entry_from_thread(row);
        let line = serde_json::to_string(&entry)
            .map_err(|error| format!("序列化 session_index 条目失败: {}", error))?;
        lines.push(line);
    }

    let mut output = lines.join("\n");
    output.push('\n');
    let path = data_dir.join(SESSION_INDEX_FILE);
    modules::atomic_write::write_string_atomic(&path, &output).map_err(|error| {
        format!(
            "写入 session_index.jsonl 失败 ({}): {}",
            path.display(),
            error
        )
    })?;
    let updated_entries = if force_rebuild_visible_tail && drift.updated_entries == 0 {
        rows.len().saturating_sub(drift.missing_entries)
    } else {
        drift.updated_entries
    };
    Ok((drift.missing_entries, updated_entries))
}

fn is_user_visible_thread_row(row: &SqliteThreadIndexRow) -> bool {
    if row.archived.unwrap_or_default() != 0 {
        return false;
    }
    if row.cwd.as_deref().unwrap_or_default().trim().is_empty() {
        return false;
    }
    if row.has_first_user_message_column
        && row
            .first_user_message
            .as_deref()
            .unwrap_or_default()
            .trim()
            .is_empty()
    {
        return false;
    }
    !row.has_thread_source_column
        || row.thread_source.as_deref().unwrap_or_default().trim() == "user"
}

fn collect_user_visible_thread_project_rows(
    data_dir: &Path,
) -> Result<Vec<SqliteThreadIndexRow>, String> {
    Ok(load_sqlite_thread_index_rows(data_dir)?
        .into_iter()
        .filter(is_user_visible_thread_row)
        .collect())
}

fn sorted_user_visible_thread_rows(data_dir: &Path) -> Result<Vec<SqliteThreadIndexRow>, String> {
    let mut rows = collect_user_visible_thread_project_rows(data_dir)?;
    rows.sort_by(|left, right| {
        let left_time = thread_updated_at_ms_for_sort(left);
        let right_time = thread_updated_at_ms_for_sort(right);
        right_time
            .cmp(&left_time)
            .then_with(|| left.id.cmp(&right.id))
    });
    Ok(rows)
}

fn thread_updated_at_ms_for_sort(row: &SqliteThreadIndexRow) -> i128 {
    row.updated_at_ms
        .map(normalize_codex_timestamp_ms)
        .or_else(|| row.updated_at.map(normalize_codex_timestamp_ms))
        .unwrap_or_default()
}

fn build_recent_window_rebalance_plan(
    rows: &[SqliteThreadIndexRow],
) -> Vec<RecentWindowRebalanceChange> {
    if rows.len() <= RECENT_CONVERSATION_PAGE_SIZE {
        return Vec::new();
    }

    let scan_end = rows
        .len()
        .min(RECENT_CONVERSATION_PAGE_SIZE + RECENT_CONVERSATION_REBALANCE_SCAN_LIMIT);
    let mut top_counts: HashMap<String, usize> = HashMap::new();
    for cwd in rows
        .iter()
        .take(RECENT_CONVERSATION_PAGE_SIZE)
        .filter_map(|row| row.cwd.as_deref().map(str::trim))
        .filter(|cwd| !cwd.is_empty())
    {
        *top_counts.entry(cwd.to_string()).or_default() += 1;
    }
    if top_counts.is_empty() {
        return Vec::new();
    }

    let mut grouped_rows = Vec::new();
    let mut inserted_tail_ids = HashSet::new();
    for top_row in rows.iter().take(RECENT_CONVERSATION_PAGE_SIZE) {
        grouped_rows.push(top_row.clone());
        let Some(cwd) = top_row
            .cwd
            .as_deref()
            .map(str::trim)
            .filter(|cwd| !cwd.is_empty())
        else {
            continue;
        };
        if top_counts.get(cwd).copied().unwrap_or_default() != 1 {
            continue;
        }
        for tail_row in rows
            .iter()
            .skip(RECENT_CONVERSATION_PAGE_SIZE)
            .take(RECENT_CONVERSATION_REBALANCE_SCAN_LIMIT)
            .filter(|row| row.cwd.as_deref().map(str::trim) == Some(cwd))
        {
            if inserted_tail_ids.insert(tail_row.id.clone()) {
                grouped_rows.push(tail_row.clone());
            }
        }
    }
    if inserted_tail_ids.is_empty() {
        return Vec::new();
    }

    let grouped_ids = grouped_rows
        .iter()
        .map(|row| row.id.clone())
        .collect::<HashSet<_>>();
    for row in rows
        .iter()
        .take(scan_end)
        .filter(|row| !grouped_ids.contains(&row.id))
    {
        grouped_rows.push(row.clone());
    }

    if grouped_rows.len() < 2 {
        return Vec::new();
    }

    let original_ids = rows
        .iter()
        .take(grouped_rows.len())
        .map(|row| row.id.as_str())
        .collect::<Vec<_>>();
    let next_ids = grouped_rows
        .iter()
        .map(|row| row.id.as_str())
        .collect::<Vec<_>>();
    if original_ids == next_ids {
        return Vec::new();
    }

    let base_time = rows
        .first()
        .map(thread_updated_at_ms_for_sort)
        .unwrap_or_default();
    grouped_rows
        .into_iter()
        .enumerate()
        .filter_map(|(index, row)| {
            let next_ms = base_time - index as i128 * 1_000;
            let next_ms = next_ms.max(0);
            let current_ms = thread_updated_at_ms_for_sort(&row);
            if current_ms == next_ms {
                return None;
            }

            let updated_at_ms = if row.has_updated_at_ms_column {
                Some(next_ms as i64)
            } else {
                None
            };
            let updated_at = if row.has_updated_at_column {
                Some((next_ms / 1_000) as i64)
            } else {
                None
            };
            if updated_at_ms.is_none() && updated_at.is_none() {
                return None;
            }
            Some(RecentWindowRebalanceChange {
                thread_id: row.id,
                updated_at,
                updated_at_ms,
            })
        })
        .collect()
}

fn count_recent_window_rows_to_rebalance(data_dir: &Path) -> Result<usize, String> {
    let rows = sorted_user_visible_thread_rows(data_dir)?;
    Ok(build_recent_window_rebalance_plan(&rows).len())
}

fn rebalance_recent_window_order(data_dir: &Path) -> Result<usize, String> {
    let rows = sorted_user_visible_thread_rows(data_dir)?;
    let changes = build_recent_window_rebalance_plan(&rows);
    if changes.is_empty() {
        return Ok(0);
    }

    let db_path = data_dir.join(STATE_DB_FILE);
    if !db_path.exists() {
        return Ok(0);
    }
    let mut connection = match Connection::open(&db_path) {
        Ok(connection) => connection,
        Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(0);
        }
        Err(error) => {
            return Err(format!(
                "打开实例数据库失败 ({}): {}",
                db_path.display(),
                error
            ));
        }
    };
    connection
        .busy_timeout(Duration::from_secs(3))
        .map_err(|error| {
            format!(
                "设置 SQLite busy_timeout 失败 ({}): {}",
                db_path.display(),
                error
            )
        })?;
    let columns = match read_threads_table_columns(&connection) {
        Ok(columns) => columns,
        Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(0);
        }
        Err(error) => {
            return Err(format_sqlite_read_error(
                &db_path,
                "读取 SQLite threads 表结构失败",
                &error,
            ));
        }
    };
    let Some(columns) = columns else {
        return Ok(0);
    };
    if !columns.updated_at && !columns.updated_at_ms {
        return Ok(0);
    }

    let transaction = connection
        .transaction()
        .map_err(|error| format_sqlite_write_error(&db_path, &error))?;
    let mut updated_rows = 0usize;
    for change in &changes {
        let update_result = match (columns.updated_at, columns.updated_at_ms) {
            (true, true) => transaction.execute(
                "UPDATE threads SET updated_at = ?1, updated_at_ms = ?2 WHERE id = ?3",
                params![
                    change.updated_at.unwrap_or_default(),
                    change.updated_at_ms.unwrap_or_default(),
                    change.thread_id
                ],
            ),
            (true, false) => transaction.execute(
                "UPDATE threads SET updated_at = ?1 WHERE id = ?2",
                params![change.updated_at.unwrap_or_default(), change.thread_id],
            ),
            (false, true) => transaction.execute(
                "UPDATE threads SET updated_at_ms = ?1 WHERE id = ?2",
                params![change.updated_at_ms.unwrap_or_default(), change.thread_id],
            ),
            (false, false) => Ok(0),
        };
        match update_result {
            Ok(count) => updated_rows += count,
            Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
                log_skipped_sqlite_database(&db_path, &error.to_string());
                return Ok(updated_rows);
            }
            Err(error) if is_missing_threads_table_error(&error) => return Ok(updated_rows),
            Err(error) => return Err(format_sqlite_write_error(&db_path, &error)),
        }
    }
    if let Err(error) = transaction.commit() {
        if modules::db::is_unusable_sqlite_database_error(&error) {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(updated_rows);
        }
        return Err(format_sqlite_write_error(&db_path, &error));
    }
    Ok(updated_rows)
}

fn global_state_path(data_dir: &Path) -> PathBuf {
    data_dir.join(GLOBAL_STATE_FILE)
}

fn read_global_state(data_dir: &Path) -> Result<JsonValue, String> {
    let path = global_state_path(data_dir);
    if !path.exists() {
        return Ok(json!({}));
    }
    let content = fs::read_to_string(&path)
        .map_err(|error| format!("读取全局状态失败 ({}): {}", path.display(), error))?;
    if content.trim().is_empty() {
        return Ok(json!({}));
    }
    serde_json::from_str::<JsonValue>(&content)
        .map_err(|error| format!("解析全局状态失败 ({}): {}", path.display(), error))
}

fn write_global_state(data_dir: &Path, value: &JsonValue) -> Result<(), String> {
    let path = global_state_path(data_dir);
    let content = serde_json::to_string_pretty(value)
        .map_err(|error| format!("序列化全局状态失败: {}", error))?;
    modules::atomic_write::write_string_atomic(&path, &format!("{}\n", content))
        .map_err(|error| format!("写入全局状态失败 ({}): {}", path.display(), error))
}

fn merge_global_state_string_array(
    object: &mut serde_json::Map<String, JsonValue>,
    key: &str,
    additions: &[String],
) -> bool {
    let mut changed = false;
    let mut values = object
        .get(key)
        .and_then(JsonValue::as_array)
        .cloned()
        .unwrap_or_default()
        .into_iter()
        .filter_map(|item| item.as_str().map(|value| value.trim().to_string()))
        .filter(|value| !value.is_empty())
        .collect::<Vec<_>>();
    let mut existing = values.iter().cloned().collect::<HashSet<_>>();

    for addition in additions {
        let trimmed = addition.trim();
        if trimmed.is_empty() {
            continue;
        }
        if existing.insert(trimmed.to_string()) {
            values.push(trimmed.to_string());
            changed = true;
        }
    }

    if changed {
        object.insert(
            key.to_string(),
            JsonValue::Array(values.into_iter().map(JsonValue::String).collect()),
        );
    }
    changed
}

fn thread_project_assignment_for_row(row: &SqliteThreadIndexRow) -> Option<JsonValue> {
    let cwd = row.cwd.as_deref()?.trim();
    if cwd.is_empty() {
        return None;
    }
    Some(json!({
        "projectKind": "local",
        "projectId": cwd,
        "path": cwd,
        "cwd": cwd,
        "pendingCoreUpdate": false,
    }))
}

fn count_missing_thread_project_assignments(data_dir: &Path) -> Result<usize, String> {
    let rows = collect_user_visible_thread_project_rows(data_dir)?;
    if rows.is_empty() {
        return Ok(0);
    }
    let state = read_global_state(data_dir)?;
    let assignments = state
        .get(THREAD_PROJECT_ASSIGNMENTS_KEY)
        .and_then(JsonValue::as_object);
    Ok(rows
        .iter()
        .filter(|row| {
            let Some(expected) = thread_project_assignment_for_row(row) else {
                return false;
            };
            assignments
                .and_then(|items| items.get(&row.id))
                .map_or(true, |existing| existing != &expected)
        })
        .count())
}

fn reconcile_thread_project_assignments(data_dir: &Path) -> Result<usize, String> {
    let rows = collect_user_visible_thread_project_rows(data_dir)?;
    if rows.is_empty() {
        return Ok(0);
    }

    let mut state = read_global_state(data_dir)?;
    if !state.is_object() {
        state = json!({});
    }
    let Some(object) = state.as_object_mut() else {
        return Err("全局状态文件格式无效".to_string());
    };

    let mut assignments = object
        .get(THREAD_PROJECT_ASSIGNMENTS_KEY)
        .and_then(JsonValue::as_object)
        .cloned()
        .unwrap_or_default();
    let mut updated_assignments = 0usize;
    let mut roots = Vec::new();

    for row in &rows {
        let Some(assignment) = thread_project_assignment_for_row(row) else {
            continue;
        };
        let cwd = row.cwd.as_deref().unwrap_or_default().trim();
        if !cwd.is_empty() {
            roots.push(cwd.to_string());
        }
        if assignments
            .get(&row.id)
            .map_or(true, |existing| existing != &assignment)
        {
            assignments.insert(row.id.clone(), assignment);
            updated_assignments += 1;
        }
    }

    let mut changed = updated_assignments > 0;
    if updated_assignments > 0 {
        object.insert(
            THREAD_PROJECT_ASSIGNMENTS_KEY.to_string(),
            JsonValue::Object(assignments),
        );
    }
    changed |= merge_global_state_string_array(object, PROJECT_ORDER_KEY, &roots);
    changed |= merge_global_state_string_array(object, ELECTRON_SAVED_WORKSPACE_ROOTS_KEY, &roots);

    if changed {
        write_global_state(data_dir, &state)?;
    }

    Ok(updated_assignments)
}

fn normalize_codex_timestamp_ms(timestamp: i64) -> i128 {
    let timestamp = timestamp as i128;
    if timestamp > 10_000_000_000_000 {
        timestamp / 1_000
    } else if timestamp > 10_000_000_000 {
        timestamp
    } else {
        timestamp * 1_000
    }
}

fn parse_timestamp_ms(value: &JsonValue) -> Option<i128> {
    match value {
        JsonValue::Number(number) => number.as_i64().map(normalize_codex_timestamp_ms),
        JsonValue::String(text) => chrono::DateTime::parse_from_rfc3339(text)
            .ok()
            .map(|value| value.timestamp_millis() as i128)
            .or_else(|| text.parse::<i64>().ok().map(normalize_codex_timestamp_ms)),
        _ => None,
    }
}

fn parse_session_index_updated_at_ms(entry: &JsonValue) -> Option<i128> {
    [
        "updated_at",
        "updatedAt",
        "last_updated_at",
        "lastUpdatedAt",
    ]
    .iter()
    .filter_map(|key| entry.get(*key))
    .find_map(parse_timestamp_ms)
}

fn parse_rollout_line_timestamp_ms(value: &JsonValue) -> Option<i128> {
    value
        .get("timestamp")
        .or_else(|| value.get("time"))
        .or_else(|| value.get("created_at"))
        .or_else(|| value.get("createdAt"))
        .and_then(parse_timestamp_ms)
        .or_else(|| {
            value
                .get("payload")
                .and_then(|payload| {
                    payload
                        .get("timestamp")
                        .or_else(|| payload.get("time"))
                        .or_else(|| payload.get("created_at"))
                        .or_else(|| payload.get("createdAt"))
                })
                .and_then(parse_timestamp_ms)
        })
}

fn rollout_file_activity_ms(path: &Path) -> Option<i128> {
    let content = fs::read_to_string(path).ok()?;
    content
        .lines()
        .filter_map(|line| serde_json::from_str::<JsonValue>(line.trim()).ok())
        .filter_map(|value| parse_rollout_line_timestamp_ms(&value))
        .max()
}

fn is_missing_threads_table_error(error: &rusqlite::Error) -> bool {
    error
        .to_string()
        .to_ascii_lowercase()
        .contains("no such table: threads")
}

fn log_skipped_sqlite_database(path: &Path, reason: &str) {
    modules::logger::log_warn(&format!(
        "跳过无效或损坏的 Codex state_5.sqlite ({}): {}",
        path.display(),
        reason
    ));
}

fn count_sqlite_rows_to_update(
    data_dir: &Path,
    target_provider: &str,
) -> Result<SqliteProviderScan, String> {
    let db_path = data_dir.join(STATE_DB_FILE);
    if !db_path.exists() {
        return Ok(SqliteProviderScan {
            rows_to_update: 0,
            skipped_unusable_database: false,
        });
    }

    let connection = match Connection::open(&db_path) {
        Ok(connection) => connection,
        Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(SqliteProviderScan {
                rows_to_update: 0,
                skipped_unusable_database: true,
            });
        }
        Err(error) => {
            return Err(format!(
                "打开实例数据库失败 ({}): {}",
                db_path.display(),
                error
            ));
        }
    };
    let columns = match read_threads_table_columns(&connection) {
        Ok(columns) => columns,
        Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(SqliteProviderScan {
                rows_to_update: 0,
                skipped_unusable_database: true,
            });
        }
        Err(error) => {
            return Err(format_sqlite_read_error(
                &db_path,
                "读取 SQLite threads 表结构失败",
                &error,
            ));
        }
    };
    let Some(columns) = columns else {
        return Ok(SqliteProviderScan {
            rows_to_update: 0,
            skipped_unusable_database: false,
        });
    };
    let Some(where_clause) = build_threads_repair_where_clause(columns) else {
        return Ok(SqliteProviderScan {
            rows_to_update: 0,
            skipped_unusable_database: false,
        });
    };
    let sql = format!("SELECT COUNT(*) FROM threads WHERE {where_clause}");
    let count_result = if columns.model_provider {
        connection.query_row(sql.as_str(), [target_provider], |row| {
            row.get::<usize, i64>(0)
        })
    } else {
        connection.query_row(sql.as_str(), [], |row| row.get::<usize, i64>(0))
    };
    let count = match count_result {
        Ok(count) => count,
        Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(SqliteProviderScan {
                rows_to_update: 0,
                skipped_unusable_database: true,
            });
        }
        Err(error) if is_missing_threads_table_error(&error) => {
            return Ok(SqliteProviderScan {
                rows_to_update: 0,
                skipped_unusable_database: false,
            });
        }
        Err(error) => {
            return Err(format!(
                "统计 SQLite 会话可见性差异失败 ({}): {}",
                db_path.display(),
                error
            ));
        }
    };
    Ok(SqliteProviderScan {
        rows_to_update: count.max(0) as usize,
        skipped_unusable_database: false,
    })
}

fn update_sqlite_provider(data_dir: &Path, target_provider: &str) -> Result<usize, String> {
    let db_path = data_dir.join(STATE_DB_FILE);
    if !db_path.exists() {
        return Ok(0);
    }

    let mut connection = match Connection::open(&db_path) {
        Ok(connection) => connection,
        Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(0);
        }
        Err(error) => {
            return Err(format!(
                "打开实例数据库失败 ({}): {}",
                db_path.display(),
                error
            ));
        }
    };
    connection
        .busy_timeout(Duration::from_secs(3))
        .map_err(|error| {
            format!(
                "设置 SQLite busy_timeout 失败 ({}): {}",
                db_path.display(),
                error
            )
        })?;
    let columns = match read_threads_table_columns(&connection) {
        Ok(columns) => columns,
        Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(0);
        }
        Err(error) => {
            return Err(format_sqlite_read_error(
                &db_path,
                "读取 SQLite threads 表结构失败",
                &error,
            ));
        }
    };
    let Some(columns) = columns else {
        return Ok(0);
    };
    let Some(where_clause) = build_threads_repair_where_clause(columns) else {
        return Ok(0);
    };
    let set_clause = build_threads_repair_set_clause(columns);
    let transaction = connection
        .transaction()
        .map_err(|error| format_sqlite_write_error(&db_path, &error))?;
    let sql = format!("UPDATE threads SET {set_clause} WHERE {where_clause}");
    let update_result = if columns.model_provider {
        transaction.execute(sql.as_str(), [target_provider])
    } else {
        transaction.execute(sql.as_str(), [])
    };
    let updated_rows = match update_result {
        Ok(updated_rows) => updated_rows,
        Err(error) if modules::db::is_unusable_sqlite_database_error(&error) => {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(0);
        }
        Err(error) if is_missing_threads_table_error(&error) => {
            return Ok(0);
        }
        Err(error) => return Err(format_sqlite_write_error(&db_path, &error)),
    };
    if let Err(error) = transaction.commit() {
        if modules::db::is_unusable_sqlite_database_error(&error) {
            log_skipped_sqlite_database(&db_path, &error.to_string());
            return Ok(0);
        }
        return Err(format_sqlite_write_error(&db_path, &error));
    }
    Ok(updated_rows)
}

fn read_threads_table_columns(
    connection: &Connection,
) -> Result<Option<ThreadsTableColumns>, rusqlite::Error> {
    let mut statement = connection.prepare("PRAGMA table_info(threads)")?;
    let rows = statement.query_map([], |row| row.get::<usize, String>(1))?;
    let mut names = HashSet::new();
    for row in rows {
        let name = row?;
        names.insert(name);
    }
    if names.is_empty() {
        return Ok(None);
    }
    Ok(Some(ThreadsTableColumns {
        updated_at: names.contains("updated_at"),
        updated_at_ms: names.contains("updated_at_ms"),
        model_provider: names.contains("model_provider"),
        has_user_event: names.contains("has_user_event"),
        first_user_message: names.contains("first_user_message"),
        thread_source: names.contains("thread_source"),
    }))
}

fn build_threads_repair_where_clause(columns: ThreadsTableColumns) -> Option<String> {
    let mut predicates = Vec::new();
    if columns.model_provider {
        predicates.push("COALESCE(model_provider, '') <> ?1");
    }
    if columns.has_user_event && columns.first_user_message {
        predicates
            .push("(COALESCE(first_user_message, '') <> '' AND COALESCE(has_user_event, 0) <> 1)");
    }
    if columns.thread_source && columns.first_user_message {
        predicates
            .push("(COALESCE(first_user_message, '') <> '' AND COALESCE(thread_source, '') = '')");
    }
    if predicates.is_empty() {
        None
    } else {
        Some(predicates.join(" OR "))
    }
}

fn build_threads_repair_set_clause(columns: ThreadsTableColumns) -> String {
    let mut assignments = Vec::new();
    if columns.model_provider {
        assignments.push("model_provider = ?1");
    }
    if columns.has_user_event && columns.first_user_message {
        assignments.push(
            "has_user_event = CASE WHEN COALESCE(first_user_message, '') <> '' THEN 1 ELSE has_user_event END",
        );
    }
    if columns.thread_source && columns.first_user_message {
        assignments.push(
            "thread_source = CASE WHEN COALESCE(thread_source, '') = '' AND COALESCE(first_user_message, '') <> '' THEN 'user' ELSE thread_source END",
        );
    }
    assignments.join(", ")
}

fn format_sqlite_read_error(path: &Path, action: &str, error: &rusqlite::Error) -> String {
    format!("{} ({}): {}", action, path.display(), error)
}

fn format_sqlite_write_error(path: &Path, error: &rusqlite::Error) -> String {
    let message = error.to_string();
    let lowered = message.to_ascii_lowercase();
    if lowered.contains("database is locked") || lowered.contains("database busy") {
        return format!(
            "state_5.sqlite 当前被占用，请关闭 Codex / Codex App 后重试 ({}): {}",
            path.display(),
            message
        );
    }
    format!(
        "更新 SQLite 会话可见性失败 ({}): {}",
        path.display(),
        message
    )
}

fn rewrite_rollout_provider(change: &RolloutProviderChange) -> Result<(), String> {
    let original_modified_at =
        modules::codex_session_file_time::read_modified_time(&change.absolute_path);
    if let Some(updated_first_line) = change.updated_first_line.as_deref() {
        let bytes = fs::read(&change.absolute_path).map_err(|error| {
            format!(
                "读取 rollout 文件失败 ({}): {}",
                change.absolute_path.display(),
                error
            )
        })?;
        let (offset, separator) = detect_first_line_boundary(&bytes);
        let mut next_bytes = Vec::with_capacity(updated_first_line.len() + bytes.len());
        next_bytes.extend_from_slice(updated_first_line.as_bytes());
        next_bytes.extend_from_slice(separator.as_bytes());
        next_bytes.extend_from_slice(&bytes[offset..]);
        write_bytes_atomic(&change.absolute_path, &next_bytes)?;
    }
    modules::codex_session_file_time::restore_modified_time(
        &change.absolute_path,
        change.target_modified_at.or(original_modified_at),
    )
}

fn detect_first_line_boundary(bytes: &[u8]) -> (usize, &'static str) {
    for (index, byte) in bytes.iter().enumerate() {
        if *byte == b'\n' {
            if index > 0 && bytes[index - 1] == b'\r' {
                return (index + 1, "\r\n");
            }
            return (index + 1, "\n");
        }
    }
    (bytes.len(), "")
}

fn write_bytes_atomic(path: &Path, content: &[u8]) -> Result<(), String> {
    let parent = path
        .parent()
        .ok_or_else(|| format!("无法定位目标目录: {}", path.display()))?;
    fs::create_dir_all(parent)
        .map_err(|error| format!("创建目录失败 ({}): {}", parent.display(), error))?;

    let temp_path = parent.join(format!(
        ".{}.provider-repair.{}.{}",
        path.file_name()
            .and_then(|item| item.to_str())
            .unwrap_or("file"),
        std::process::id(),
        Utc::now().timestamp_nanos_opt().unwrap_or_default()
    ));
    fs::write(&temp_path, content)
        .map_err(|error| format!("写入临时文件失败 ({}): {}", temp_path.display(), error))?;
    if let Err(error) = fs::rename(&temp_path, path) {
        let _ = fs::remove_file(&temp_path);
        return Err(format!("替换文件失败 ({}): {}", path.display(), error));
    }
    Ok(())
}

fn sqlite_sidecar_paths(db_path: &Path) -> Vec<PathBuf> {
    let raw = db_path.to_string_lossy();
    vec![
        PathBuf::from(format!("{}-wal", raw)),
        PathBuf::from(format!("{}-shm", raw)),
    ]
}

fn remove_sqlite_sidecar_files(db_path: &Path) -> Result<(), String> {
    for path in sqlite_sidecar_paths(db_path) {
        match fs::remove_file(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!(
                    "清理 SQLite sidecar 文件失败 ({}): {}",
                    path.display(),
                    error
                ));
            }
        }
    }
    Ok(())
}

fn backup_sqlite_database(data_dir: &Path, backup_dir: &Path) -> Result<bool, String> {
    let db_path = data_dir.join(STATE_DB_FILE);
    if !db_path.exists() {
        return Ok(false);
    }

    let backup_db_path = backup_dir.join(STATE_DB_FILE);
    let connection = Connection::open(&db_path).map_err(|error| {
        format!(
            "打开 state_5.sqlite 以创建一致备份失败 ({}): {}",
            db_path.display(),
            error
        )
    })?;
    connection
        .busy_timeout(Duration::from_secs(3))
        .map_err(|error| {
            format!(
                "设置 SQLite 备份 busy_timeout 失败 ({}): {}",
                db_path.display(),
                error
            )
        })?;

    if backup_db_path.exists() {
        fs::remove_file(&backup_db_path).map_err(|error| {
            format!(
                "删除旧 state_5.sqlite 备份失败 ({}): {}",
                backup_db_path.display(),
                error
            )
        })?;
    }
    let backup_target = backup_db_path.to_string_lossy().to_string();
    connection
        .execute("VACUUM main INTO ?1", [backup_target.as_str()])
        .map_err(|error| {
            format!(
                "备份 state_5.sqlite 失败 ({} -> {}): {}",
                db_path.display(),
                backup_db_path.display(),
                error
            )
        })?;
    Ok(true)
}

fn restore_sqlite_database_from_backup(data_dir: &Path, backup_dir: &Path) -> Result<bool, String> {
    let backup_db_path = backup_dir.join(STATE_DB_FILE);
    if !backup_db_path.exists() {
        return Ok(false);
    }

    let target_db_path = data_dir.join(STATE_DB_FILE);
    fs::create_dir_all(data_dir).map_err(|error| {
        format!(
            "创建 state_5.sqlite 恢复目录失败 ({}): {}",
            data_dir.display(),
            error
        )
    })?;
    remove_sqlite_sidecar_files(&target_db_path)?;
    fs::copy(&backup_db_path, &target_db_path).map_err(|error| {
        format!(
            "恢复 state_5.sqlite 失败 ({} -> {}): {}",
            backup_db_path.display(),
            target_db_path.display(),
            error
        )
    })?;
    remove_sqlite_sidecar_files(&target_db_path)?;
    Ok(true)
}

fn backup_instance_files(
    data_dir: &Path,
    rollout_changes: &[RolloutProviderChange],
    include_sqlite: bool,
    include_session_index: bool,
    include_global_state: bool,
    instance_id: &str,
    target_provider: &str,
) -> Result<PathBuf, String> {
    let backup_dir_name = format!(
        "{}{}{}",
        SESSION_VISIBILITY_REPAIR_BACKUP_PREFIX,
        Utc::now().format("%Y%m%d-%H%M%S"),
        SESSION_VISIBILITY_REPAIR_BACKUP_SUFFIX
    );
    let backup_dir = data_dir.join(backup_dir_name);
    fs::create_dir_all(&backup_dir)
        .map_err(|error| format!("创建备份目录失败 ({}): {}", backup_dir.display(), error))?;

    let mut backed_up_files = Vec::new();
    let mut sqlite_backup_created = false;
    for change in rollout_changes {
        let target = backup_dir.join("files").join(&change.relative_path);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent).map_err(|error| {
                format!(
                    "创建 rollout 备份目录失败 ({}): {}",
                    parent.display(),
                    error
                )
            })?;
        }
        fs::copy(&change.absolute_path, &target).map_err(|error| {
            format!(
                "备份 rollout 文件失败 ({} -> {}): {}",
                change.absolute_path.display(),
                target.display(),
                error
            )
        })?;
        modules::codex_session_file_time::restore_modified_time(
            &target,
            modules::codex_session_file_time::read_modified_time(&change.absolute_path),
        )?;
        backed_up_files.push(change.relative_path.to_string_lossy().to_string());
    }

    if include_sqlite {
        sqlite_backup_created = backup_sqlite_database(data_dir, &backup_dir)?;
    }

    let mut global_state_backup_created = false;
    if include_global_state {
        let source = data_dir.join(GLOBAL_STATE_FILE);
        if source.exists() {
            let target = backup_dir.join("files").join(GLOBAL_STATE_FILE);
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent).map_err(|error| {
                    format!("创建全局状态备份目录失败 ({}): {}", parent.display(), error)
                })?;
            }
            fs::copy(&source, &target).map_err(|error| {
                format!(
                    "备份全局状态失败 ({} -> {}): {}",
                    source.display(),
                    target.display(),
                    error
                )
            })?;
            global_state_backup_created = true;
        }
    }

    let mut session_index_backup_created = false;
    if include_session_index {
        let source = data_dir.join(SESSION_INDEX_FILE);
        if source.exists() {
            let target = backup_dir.join("files").join(SESSION_INDEX_FILE);
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent).map_err(|error| {
                    format!(
                        "创建 session_index 备份目录失败 ({}): {}",
                        parent.display(),
                        error
                    )
                })?;
            }
            fs::copy(&source, &target).map_err(|error| {
                format!(
                    "备份 session_index.jsonl 失败 ({} -> {}): {}",
                    source.display(),
                    target.display(),
                    error
                )
            })?;
            session_index_backup_created = true;
        }
    }

    let manifest = json!({
        "instanceId": instance_id,
        "instanceRoot": data_dir,
        "targetProvider": target_provider,
        "createdAt": Utc::now().to_rfc3339(),
        "hasSqliteBackup": sqlite_backup_created,
        "hasSessionIndexBackup": session_index_backup_created,
        "hasGlobalStateBackup": global_state_backup_created,
        "rolloutFiles": backed_up_files,
    });
    fs::write(
        backup_dir.join("manifest.json"),
        format!(
            "{}\n",
            serde_json::to_string_pretty(&manifest)
                .map_err(|error| format!("序列化可见性修复备份清单失败: {}", error))?
        ),
    )
    .map_err(|error| {
        format!(
            "写入可见性修复备份清单失败 ({}): {}",
            backup_dir.display(),
            error
        )
    })?;

    Ok(backup_dir)
}

fn parse_session_visibility_repair_backup_timestamp(name: &str) -> Option<&str> {
    let timestamp = name
        .strip_prefix(SESSION_VISIBILITY_REPAIR_BACKUP_PREFIX)?
        .strip_suffix(SESSION_VISIBILITY_REPAIR_BACKUP_SUFFIX)?;
    if timestamp.len() != 15 {
        return None;
    }
    if !timestamp.chars().enumerate().all(|(index, value)| {
        if index == 8 {
            value == '-'
        } else {
            value.is_ascii_digit()
        }
    }) {
        return None;
    }
    Some(timestamp)
}

fn prune_session_visibility_repair_backups(instances: &[CodexSyncInstance]) {
    for instance in instances {
        if let Err(error) = prune_instance_session_visibility_repair_backups(&instance.data_dir) {
            modules::logger::log_warn(&format!(
                "清理 Codex 会话可见性修复旧备份失败 ({}): {}",
                instance.data_dir.display(),
                error
            ));
        }
    }
}

fn prune_instance_session_visibility_repair_backups(data_dir: &Path) -> Result<(), String> {
    let entries = match fs::read_dir(data_dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => {
            return Err(format!(
                "读取实例目录失败 ({}): {}",
                data_dir.display(),
                error
            ));
        }
    };
    let mut backups: Vec<(String, PathBuf)> = Vec::new();

    for entry in entries {
        let entry = entry
            .map_err(|error| format!("读取实例目录项失败 ({}): {}", data_dir.display(), error))?;
        let file_type = entry.file_type().map_err(|error| {
            format!(
                "读取实例目录项类型失败 ({}): {}",
                entry.path().display(),
                error
            )
        })?;
        if !file_type.is_dir() {
            continue;
        }

        let file_name = entry.file_name();
        let Some(file_name) = file_name.to_str() else {
            continue;
        };
        let Some(timestamp) = parse_session_visibility_repair_backup_timestamp(file_name) else {
            continue;
        };
        backups.push((timestamp.to_string(), entry.path()));
    }

    if backups.len() <= MAX_SESSION_VISIBILITY_REPAIR_BACKUPS {
        return Ok(());
    }

    backups.sort_by(|left, right| right.0.cmp(&left.0));
    for (_, path) in backups
        .into_iter()
        .skip(MAX_SESSION_VISIBILITY_REPAIR_BACKUPS)
    {
        fs::remove_dir_all(&path)
            .map_err(|error| format!("删除旧备份失败 ({}): {}", path.display(), error))?;
    }

    Ok(())
}

fn restore_instance_files_from_backup(
    data_dir: &Path,
    backup_dir: &Path,
    include_sqlite: bool,
    _include_global_state: bool,
) -> Result<(), String> {
    let files_root = backup_dir.join("files");
    if files_root.exists() {
        restore_directory_contents(&files_root, data_dir)?;
    }

    if include_sqlite {
        let _ = restore_sqlite_database_from_backup(data_dir, backup_dir)?;
    }

    Ok(())
}

fn restore_directory_contents(source_root: &Path, target_root: &Path) -> Result<(), String> {
    let entries = fs::read_dir(source_root)
        .map_err(|error| format!("读取备份目录失败 ({}): {}", source_root.display(), error))?;
    for entry in entries {
        let entry = entry.map_err(|error| {
            format!("读取备份目录项失败 ({}): {}", source_root.display(), error)
        })?;
        let source_path = entry.path();
        let file_type = entry.file_type().map_err(|error| {
            format!(
                "读取备份文件类型失败 ({}): {}",
                source_path.display(),
                error
            )
        })?;
        let relative = source_path
            .strip_prefix(source_root)
            .map_err(|_| format!("无法计算备份相对路径: {}", source_path.display()))?;
        let target_path = target_root.join(relative);

        if file_type.is_dir() {
            fs::create_dir_all(&target_path).map_err(|error| {
                format!("创建恢复目录失败 ({}): {}", target_path.display(), error)
            })?;
            restore_directory_contents(&source_path, &target_path)?;
            continue;
        }

        if let Some(parent) = target_path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("创建恢复父目录失败 ({}): {}", parent.display(), error))?;
        }
        fs::copy(&source_path, &target_path).map_err(|error| {
            format!(
                "恢复备份文件失败 ({} -> {}): {}",
                source_path.display(),
                target_path.display(),
                error
            )
        })?;
        modules::codex_session_file_time::restore_modified_time(
            &target_path,
            modules::codex_session_file_time::read_modified_time(&source_path),
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Duration, SystemTime, UNIX_EPOCH};

    fn make_temp_dir(prefix: &str) -> PathBuf {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time should be after unix epoch")
            .as_nanos();
        let base_dir =
            std::env::temp_dir().join(format!("{}-{}-{}", prefix, std::process::id(), unique));
        if base_dir.exists() {
            fs::remove_dir_all(&base_dir).expect("cleanup old temp dir");
        }
        fs::create_dir_all(&base_dir).expect("create temp dir");
        base_dir
    }

    #[test]
    fn rollout_repair_updates_provider_and_preserves_session_time() {
        let data_dir = make_temp_dir("codex-session-visibility-rollout-time-test");
        let rollout_dir = data_dir.join("sessions").join("2026").join("05").join("23");
        fs::create_dir_all(&rollout_dir).expect("create rollout dir");
        let rollout_path = rollout_dir.join("rollout-test.jsonl");
        fs::write(
            &rollout_path,
            "{\"type\":\"session_meta\",\"payload\":{\"id\":\"s1\",\"model_provider\":\"old\"}}\n{\"type\":\"event\",\"timestamp\":\"2024-01-01T00:00:00Z\"}\n",
        )
        .expect("write rollout");
        fs::write(
            data_dir.join(SESSION_INDEX_FILE),
            "{\"id\":\"s1\",\"thread_name\":\"Test\",\"updated_at\":\"2024-02-03T04:05:06Z\"}\n",
        )
        .expect("write session index");
        let polluted_modified_at = UNIX_EPOCH + Duration::from_secs(1_800_000_000);
        fs::File::open(&rollout_path)
            .expect("open rollout")
            .set_modified(polluted_modified_at)
            .expect("set polluted rollout mtime");

        let changes =
            collect_rollout_provider_changes(&data_dir, "relay").expect("collect rollout changes");
        assert_eq!(changes.len(), 1);

        repair_single_instance(&data_dir, "relay", &changes, false, false, false, false)
            .expect("repair rollout");

        let content = fs::read_to_string(&rollout_path).expect("read repaired rollout");
        assert!(content.contains("\"model_provider\":\"relay\""));
        assert_eq!(
            fs::metadata(&rollout_path)
                .expect("rollout metadata")
                .modified()
                .expect("rollout mtime"),
            UNIX_EPOCH + Duration::from_secs(1_706_933_106)
        );
        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }

    #[test]
    fn rollout_repair_restores_session_time_without_provider_change() {
        let data_dir = make_temp_dir("codex-session-visibility-mtime-only-test");
        let rollout_dir = data_dir.join("sessions").join("2026").join("05").join("23");
        fs::create_dir_all(&rollout_dir).expect("create rollout dir");
        let rollout_path = rollout_dir.join("rollout-test.jsonl");
        let rollout_content =
            "{\"type\":\"session_meta\",\"payload\":{\"id\":\"s1\",\"model_provider\":\"relay\"}}\n{\"type\":\"event\",\"timestamp\":\"2024-01-01T00:00:00Z\"}\n";
        fs::write(&rollout_path, rollout_content).expect("write rollout");
        let polluted_modified_at = UNIX_EPOCH + Duration::from_secs(1_800_000_000);
        fs::File::open(&rollout_path)
            .expect("open rollout")
            .set_modified(polluted_modified_at)
            .expect("set polluted rollout mtime");

        let changes =
            collect_rollout_provider_changes(&data_dir, "relay").expect("collect rollout changes");
        assert_eq!(changes.len(), 1);
        assert!(changes[0].updated_first_line.is_none());

        repair_single_instance(&data_dir, "relay", &changes, false, false, false, false)
            .expect("repair rollout time");

        assert_eq!(
            fs::read_to_string(&rollout_path).expect("read repaired rollout"),
            rollout_content
        );
        assert_eq!(
            fs::metadata(&rollout_path)
                .expect("rollout metadata")
                .modified()
                .expect("rollout mtime"),
            UNIX_EPOCH + Duration::from_secs(1_704_067_200)
        );
        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }

    #[test]
    fn rollout_repair_marks_interactive_session_meta_with_missing_thread_source() {
        let data_dir = make_temp_dir("codex-session-visibility-thread-source-test");
        let rollout_dir = data_dir.join("sessions").join("2026").join("05").join("23");
        fs::create_dir_all(&rollout_dir).expect("create rollout dir");
        let rollout_path = rollout_dir.join("rollout-test.jsonl");
        fs::write(
            &rollout_path,
            "{\"type\":\"session_meta\",\"payload\":{\"id\":\"s1\",\"source\":\"vscode\",\"model_provider\":\"relay\"}}\n{\"type\":\"event\",\"timestamp\":\"2024-01-01T00:00:00Z\"}\n",
        )
        .expect("write rollout");

        let changes =
            collect_rollout_provider_changes(&data_dir, "relay").expect("collect rollout changes");
        assert_eq!(changes.len(), 1);
        assert!(changes[0]
            .updated_first_line
            .as_deref()
            .expect("updated first line")
            .contains("\"thread_source\":\"user\""));

        repair_single_instance(&data_dir, "relay", &changes, false, false, false, false)
            .expect("repair rollout thread source");

        let content = fs::read_to_string(&rollout_path).expect("read repaired rollout");
        assert!(content.contains("\"thread_source\":\"user\""));
        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }

    #[test]
    fn sqlite_repair_marks_threads_with_first_user_message_visible() {
        let data_dir = make_temp_dir("codex-session-visibility-sqlite-test");
        let db_path = data_dir.join(STATE_DB_FILE);
        let connection = Connection::open(&db_path).expect("open sqlite");
        connection
            .execute(
                "CREATE TABLE threads (
                    id TEXT PRIMARY KEY,
                    model_provider TEXT,
                    has_user_event INTEGER,
                    first_user_message TEXT,
                    thread_source TEXT
                )",
                [],
            )
            .expect("create threads table");
        connection
            .execute(
                "INSERT INTO threads (id, model_provider, has_user_event, first_user_message, thread_source)
                 VALUES
                 ('matched-invisible', 'relay', 0, 'hello', ''),
                 ('old-invisible', 'old', 0, 'hi', NULL),
                 ('already-visible', 'relay', 1, 'visible', 'user'),
                 ('provider-only', '', 0, '', NULL)",
                [],
            )
            .expect("insert rows");
        drop(connection);

        let scan = count_sqlite_rows_to_update(&data_dir, "relay").expect("scan sqlite");
        assert_eq!(scan.rows_to_update, 3);
        assert!(!scan.skipped_unusable_database);

        let updated_rows = update_sqlite_provider(&data_dir, "relay").expect("update sqlite");
        assert_eq!(updated_rows, 3);

        let connection = Connection::open(&db_path).expect("reopen sqlite");
        let matched_invisible = connection
            .query_row(
                "SELECT model_provider, has_user_event, thread_source FROM threads WHERE id = 'matched-invisible'",
                [],
                |row| {
                    Ok((
                        row.get::<usize, String>(0)?,
                        row.get::<usize, i64>(1)?,
                        row.get::<usize, String>(2)?,
                    ))
                },
            )
            .expect("read matched row");
        assert_eq!(
            matched_invisible,
            ("relay".to_string(), 1, "user".to_string())
        );

        let old_invisible = connection
            .query_row(
                "SELECT model_provider, has_user_event, thread_source FROM threads WHERE id = 'old-invisible'",
                [],
                |row| {
                    Ok((
                        row.get::<usize, String>(0)?,
                        row.get::<usize, i64>(1)?,
                        row.get::<usize, String>(2)?,
                    ))
                },
            )
            .expect("read old row");
        assert_eq!(old_invisible, ("relay".to_string(), 1, "user".to_string()));

        let provider_only = connection
            .query_row(
                "SELECT model_provider, has_user_event FROM threads WHERE id = 'provider-only'",
                [],
                |row| Ok((row.get::<usize, String>(0)?, row.get::<usize, i64>(1)?)),
            )
            .expect("read provider-only row");
        assert_eq!(provider_only, ("relay".to_string(), 0));

        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }

    #[test]
    fn sqlite_repair_keeps_provider_only_schema_working() {
        let data_dir = make_temp_dir("codex-session-provider-only-sqlite-test");
        let db_path = data_dir.join(STATE_DB_FILE);
        let connection = Connection::open(&db_path).expect("open sqlite");
        connection
            .execute(
                "CREATE TABLE threads (id TEXT PRIMARY KEY, model_provider TEXT)",
                [],
            )
            .expect("create threads table");
        connection
            .execute(
                "INSERT INTO threads (id, model_provider) VALUES ('old', 'old'), ('same', 'relay')",
                [],
            )
            .expect("insert rows");
        drop(connection);

        let scan = count_sqlite_rows_to_update(&data_dir, "relay").expect("scan sqlite");
        assert_eq!(scan.rows_to_update, 1);
        let updated_rows = update_sqlite_provider(&data_dir, "relay").expect("update sqlite");
        assert_eq!(updated_rows, 1);

        let connection = Connection::open(&db_path).expect("reopen sqlite");
        let old_provider = connection
            .query_row(
                "SELECT model_provider FROM threads WHERE id = 'old'",
                [],
                |row| row.get::<usize, String>(0),
            )
            .expect("read old provider");
        assert_eq!(old_provider, "relay");

        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }

    #[test]
    fn sqlite_backup_restore_replaces_db_and_clears_sidecars() {
        let data_dir = make_temp_dir("codex-session-visibility-sqlite-backup-test");
        let db_path = data_dir.join(STATE_DB_FILE);
        let connection = Connection::open(&db_path).expect("open sqlite");
        connection
            .execute(
                "CREATE TABLE threads (id TEXT PRIMARY KEY, model_provider TEXT)",
                [],
            )
            .expect("create threads table");
        connection
            .execute(
                "INSERT INTO threads (id, model_provider) VALUES ('thread-1', 'old')",
                [],
            )
            .expect("insert old row");
        drop(connection);

        let backup_dir =
            backup_instance_files(&data_dir, &[], true, false, false, "default", "relay")
                .expect("backup db");

        let connection = Connection::open(&db_path).expect("reopen sqlite");
        connection
            .execute(
                "UPDATE threads SET model_provider = 'new' WHERE id = 'thread-1'",
                [],
            )
            .expect("mutate db after backup");
        drop(connection);
        for path in sqlite_sidecar_paths(&db_path) {
            fs::write(path, b"stale wal/shm").expect("write stale sidecar");
        }

        restore_instance_files_from_backup(&data_dir, &backup_dir, true, false)
            .expect("restore db");
        for path in sqlite_sidecar_paths(&db_path) {
            assert!(
                !path.exists(),
                "stale sidecar should be removed: {:?}",
                path
            );
        }

        let connection = Connection::open(&db_path).expect("open restored sqlite");
        let provider = connection
            .query_row(
                "SELECT model_provider FROM threads WHERE id = 'thread-1'",
                [],
                |row| row.get::<usize, String>(0),
            )
            .expect("read restored provider");
        assert_eq!(provider, "old");

        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }

    #[test]
    fn session_index_repair_rebuilds_visible_threads_at_tail() {
        let data_dir = make_temp_dir("codex-session-visibility-index-test");
        let db_path = data_dir.join(STATE_DB_FILE);
        let connection = Connection::open(&db_path).expect("open sqlite");
        connection
            .execute(
                "CREATE TABLE threads (
                    id TEXT PRIMARY KEY,
                    title TEXT,
                    updated_at INTEGER,
                    updated_at_ms INTEGER
                )",
                [],
            )
            .expect("create threads table");
        connection
            .execute(
                "INSERT INTO threads (id, title, updated_at, updated_at_ms) VALUES
                 ('indexed-thread', 'Indexed', 1_700_000_000, 1_700_000_000_123),
                 ('missing-thread', 'Missing chat', 1_800_000_000, 1_800_000_000_456)",
                [],
            )
            .expect("insert rows");
        drop(connection);

        fs::write(
            data_dir.join(SESSION_INDEX_FILE),
            "{\"id\":\"preserved-thread\",\"thread_name\":\"Preserved\",\"updated_at\":\"2024-01-01T00:00:00.0000000Z\"}\n{\"id\":\"indexed-thread\",\"thread_name\":\"Stale\",\"updated_at\":\"2024-01-01T00:00:00.0000000Z\"}\n",
        )
        .expect("write session index");

        let missing =
            count_missing_session_index_entries(&data_dir).expect("count missing index entries");
        assert_eq!(missing, 1);
        let drift = count_session_index_drift(&data_dir).expect("count index drift");
        assert_eq!(drift.missing_entries, 1);
        assert_eq!(drift.updated_entries, 1);

        let (added, updated) =
            reconcile_session_index_from_sqlite(&data_dir, false).expect("reconcile index");
        assert_eq!(added, 1);
        assert_eq!(updated, 1);

        let index_map = read_session_index_map(&data_dir).expect("read session index");
        assert!(index_map.contains_key("preserved-thread"));
        assert!(index_map.contains_key("missing-thread"));
        assert_eq!(
            index_map
                .get("missing-thread")
                .and_then(|entry| entry.get("thread_name"))
                .and_then(JsonValue::as_str),
            Some("Missing chat")
        );
        assert_eq!(
            index_map
                .get("missing-thread")
                .and_then(|entry| entry.get("updated_at"))
                .and_then(JsonValue::as_str),
            Some("2027-01-15T08:00:00.456000Z")
        );
        let lines = read_session_index_lines(&data_dir).expect("read rebuilt index");
        let ids = lines
            .iter()
            .map(|line| {
                serde_json::from_str::<JsonValue>(line)
                    .expect("valid index json")
                    .get("id")
                    .and_then(JsonValue::as_str)
                    .expect("id")
                    .to_string()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            ids,
            vec![
                "preserved-thread".to_string(),
                "indexed-thread".to_string(),
                "missing-thread".to_string(),
            ]
        );
        assert_eq!(
            count_missing_session_index_entries(&data_dir).expect("recount missing index entries"),
            0
        );
        assert!(!count_session_index_drift(&data_dir)
            .expect("recount index drift")
            .needs_repair());

        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }

    #[test]
    fn session_index_force_rebuild_refreshes_visible_thread_times() {
        let data_dir = make_temp_dir("codex-session-visibility-index-force-test");
        let db_path = data_dir.join(STATE_DB_FILE);
        let connection = Connection::open(&db_path).expect("open sqlite");
        connection
            .execute(
                "CREATE TABLE threads (
                    id TEXT PRIMARY KEY,
                    title TEXT,
                    updated_at INTEGER,
                    updated_at_ms INTEGER,
                    cwd TEXT,
                    archived INTEGER,
                    first_user_message TEXT,
                    thread_source TEXT
                )",
                [],
            )
            .expect("create threads table");
        connection
            .execute(
                "INSERT INTO threads (id, title, updated_at, updated_at_ms, cwd, archived, first_user_message, thread_source)
                 VALUES ('thread-1', 'Fresh title', 1_800_000_000, 1_800_000_000_123, '/tmp/project-a', 0, 'hello', 'user')",
                [],
            )
            .expect("insert row");
        drop(connection);

        fs::write(
            data_dir.join(SESSION_INDEX_FILE),
            "{\"id\":\"thread-1\",\"thread_name\":\"Stale title\",\"updated_at\":\"2024-01-01T00:00:00.000000Z\"}\n",
        )
        .expect("write stale session index");

        let (added, updated) =
            reconcile_session_index_from_sqlite(&data_dir, true).expect("force rebuild index");
        assert_eq!(added, 0);
        assert_eq!(updated, 1);

        let index_map = read_session_index_map(&data_dir).expect("read session index");
        let entry = index_map.get("thread-1").expect("thread index entry");
        assert_eq!(
            entry.get("thread_name").and_then(JsonValue::as_str),
            Some("Fresh title")
        );
        assert_eq!(
            entry.get("updated_at").and_then(JsonValue::as_str),
            Some("2027-01-15T08:00:00.123000Z")
        );

        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }

    #[test]
    fn global_state_repair_adds_thread_project_assignments_for_visible_threads() {
        let data_dir = make_temp_dir("codex-session-visibility-project-assignment-test");
        let db_path = data_dir.join(STATE_DB_FILE);
        let connection = Connection::open(&db_path).expect("open sqlite");
        connection
            .execute(
                "CREATE TABLE threads (
                    id TEXT PRIMARY KEY,
                    title TEXT,
                    updated_at INTEGER,
                    cwd TEXT,
                    archived INTEGER,
                    first_user_message TEXT,
                    thread_source TEXT
                )",
                [],
            )
            .expect("create threads table");
        connection
            .execute(
                "INSERT INTO threads (id, title, updated_at, cwd, archived, first_user_message, thread_source)
                 VALUES
                 ('visible-thread', 'Visible', 1_800_000_000, '/tmp/project-a', 0, 'hello', 'user'),
                 ('archived-thread', 'Archived', 1_800_000_001, '/tmp/project-b', 1, 'hello', 'user'),
                 ('system-thread', 'System', 1_800_000_002, '/tmp/project-c', 0, 'hello', 'system')",
                [],
            )
            .expect("insert rows");
        drop(connection);

        fs::write(
            data_dir.join(GLOBAL_STATE_FILE),
            "{\"project-order\":[],\"electron-saved-workspace-roots\":[]}\n",
        )
        .expect("write global state");

        let missing = count_missing_thread_project_assignments(&data_dir)
            .expect("count missing project assignments");
        assert_eq!(missing, 1);

        let updated =
            reconcile_thread_project_assignments(&data_dir).expect("reconcile project assignments");
        assert_eq!(updated, 1);

        let state = read_global_state(&data_dir).expect("read global state");
        let assignments = state
            .get(THREAD_PROJECT_ASSIGNMENTS_KEY)
            .and_then(JsonValue::as_object)
            .expect("project assignments");
        let assignment = assignments
            .get("visible-thread")
            .and_then(JsonValue::as_object)
            .expect("visible assignment");
        assert_eq!(
            assignment.get("projectKind").and_then(JsonValue::as_str),
            Some("local")
        );
        assert_eq!(
            assignment.get("projectId").and_then(JsonValue::as_str),
            Some("/tmp/project-a")
        );
        assert!(!assignments.contains_key("archived-thread"));
        assert!(!assignments.contains_key("system-thread"));
        assert_eq!(
            count_missing_thread_project_assignments(&data_dir)
                .expect("recount missing project assignments"),
            0
        );

        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }

    #[test]
    fn recent_window_repair_groups_nearby_project_threads_once() {
        let data_dir = make_temp_dir("codex-session-visibility-recent-window-test");
        let db_path = data_dir.join(STATE_DB_FILE);
        let connection = Connection::open(&db_path).expect("open sqlite");
        connection
            .execute(
                "CREATE TABLE threads (
                    id TEXT PRIMARY KEY,
                    title TEXT,
                    updated_at INTEGER,
                    updated_at_ms INTEGER,
                    cwd TEXT,
                    archived INTEGER,
                    first_user_message TEXT,
                    thread_source TEXT
                )",
                [],
            )
            .expect("create threads table");

        let base_ms = 1_800_000_000_000i64;
        for index in 0..60 {
            let cwd = if index == 40 {
                "/tmp/ctrl-agent".to_string()
            } else {
                format!("/tmp/project-{index:02}")
            };
            let id = if index == 40 {
                "ctrl-representative".to_string()
            } else {
                format!("project-{index:02}")
            };
            let updated_at_ms = base_ms - index * 1_000;
            connection
                .execute(
                    "INSERT INTO threads (id, title, updated_at, updated_at_ms, cwd, archived, first_user_message, thread_source)
                     VALUES (?1, ?2, ?3, ?4, ?5, 0, 'hello', 'user')",
                    params![
                        id,
                        format!("Thread {index}"),
                        updated_at_ms / 1_000,
                        updated_at_ms,
                        cwd
                    ],
                )
                .expect("insert representative");
        }
        for index in 0..5 {
            let updated_at_ms = base_ms - (60 + index as i64) * 1_000;
            connection
                .execute(
                    "INSERT INTO threads (id, title, updated_at, updated_at_ms, cwd, archived, first_user_message, thread_source)
                     VALUES (?1, ?2, ?3, ?4, '/tmp/ctrl-agent', 0, 'hello', 'user')",
                    params![
                        format!("ctrl-extra-{index}"),
                        format!("Ctrl extra {index}"),
                        updated_at_ms / 1_000,
                        updated_at_ms
                    ],
                )
                .expect("insert extra ctrl thread");
        }
        drop(connection);

        assert_eq!(
            count_recent_window_rows_to_rebalance(&data_dir).expect("count rebalance rows"),
            24
        );
        let updated = rebalance_recent_window_order(&data_dir).expect("rebalance recent window");
        assert_eq!(updated, 24);

        let rows = sorted_user_visible_thread_rows(&data_dir).expect("read sorted rows");
        let ctrl_positions = rows
            .iter()
            .enumerate()
            .filter_map(|(index, row)| {
                (row.cwd.as_deref() == Some("/tmp/ctrl-agent")).then_some(index + 1)
            })
            .collect::<Vec<_>>();
        assert_eq!(ctrl_positions, vec![41, 42, 43, 44, 45, 46]);
        assert_eq!(
            count_recent_window_rows_to_rebalance(&data_dir).expect("recount rebalance rows"),
            0
        );

        fs::remove_dir_all(&data_dir).expect("cleanup temp dir");
    }
}
