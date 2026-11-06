#!/bin/sh
# 增量蒸馏的一键入口: 提取新增的对话记录, 再渲染摘要. 已处理过的文件记在同目录 state.json (进仓库).
#
# 用法 (从任意目录): sh probes/Survey/scripts/handbook/run.sh <摘录与摘要的输出目录> [--since YYYY-MM-DD] [--session <会话 id>]
#   输出目录放仓库外 (如会话的 scratchpad); 摘录追加写, 摘要每次重写. 输出目录丢了而 state.json 还在时,
#   旧记录不会重提: 要全量重提就加 --reset 并换一个空目录 (见 extract.py 文件头).
# 对话记录的位置按 Claude Code 的约定由仓库路径推出: ~/.claude/projects/<仓库绝对路径里的 / 换成 ->;
#   后台任务输出在 ${TMPDIR 的 claude-<uid>}/<同上>/<会话>/tasks, 可用环境变量 HB_TASKS 另指 (冒号分隔).
set -e
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
out=${1:?用法: run.sh <输出目录> [--since 日期] [其他 extract.py 参数]}
shift
since=""
if [ "$1" = "--since" ]; then since=$2; shift 2; fi
slug=$(printf '%s' "$repo" | sed 's#[/.]#-#g')
root="$HOME/.claude/projects/$slug"
tasks_args=""
if [ -n "$HB_TASKS" ]; then
  for t in $(printf '%s' "$HB_TASKS" | tr ':' ' '); do tasks_args="$tasks_args --tasks $t"; done
else
  for t in /private/tmp/claude-$(id -u)/"$slug"/*/tasks /tmp/claude-$(id -u)/"$slug"/*/tasks; do
    [ -d "$t" ] && tasks_args="$tasks_args --tasks $t"
  done
fi
mkdir -p "$out/ex" "$out/digest"
python3 "$here/extract.py" --root "$root" --out "$out/ex" $tasks_args "$@"
if [ -n "$since" ]; then
  python3 "$here/digest.py" --ex "$out/ex" --out "$out/digest" --since "$since"
else
  python3 "$here/digest.py" --ex "$out/ex" --out "$out/digest"
fi
