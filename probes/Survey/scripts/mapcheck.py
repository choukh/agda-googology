# -*- coding: utf-8 -*-
# 导航完整性检查：入口、成果目录与接手纪要中的名字，及维护文档的本地链接。
#
# 用法 (任意目录): python3 probes/Survey/scripts/mapcheck.py
# 退出码: 0 未发现导航缺失，1 有缺失或定位错误；不认证数学、编译或当前路线。
#
# 判定:
#   路径 (含 / 或带扩展名, 可带 *): 依次对 probes/, probes/OCF/Align/, 仓库根解析.
#   模块名: probes/ 或 src/ 下有同名的 .lagda.md 或 .agda (probes 导入 src 的 OCF.BTBO).
#   其他都当定理名: 要在某个 Agda 代码块里有声明 (含 renaming 改出来的名字); 只被使用没有声明的, 算 "只有使用", 也报告.
#   表头有 "定理" 和 "文件" 两列的表: 定理列的每个名字必须声明在文件列写的文件之一里.
# 局限: 只认行首的声明形式 (签名, 定义, data, record, module); 不检查陈述, 也不检查文字说得对不对.
# 名字检查仍可能只匹配限定名末段或路径 basename；不能认证精确来源，须读声明核对。
import fnmatch, io, os, re, sys
from urllib.parse import unquote, urlsplit

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
PROBES = os.path.join(ROOT, 'probes')
MAPS = sys.argv[1:] or [os.path.join(PROBES, n) for n in
                       ('README.md', 'RESULTS.md', 'HANDOFF-2026-11-07.md')]
KEYWORDS = {'data', 'record', 'module', 'field', 'abstract', 'private', 'instance', 'mutual', 'postulate'}

paths, stems, code = [], {}, {}
for d, ds, fs in [w for top in (PROBES, os.path.join(ROOT, 'src')) for w in os.walk(top)]:
    ds[:] = [x for x in ds if x != '_build']
    for f in fs:
        p = os.path.join(d, f)
        if p.startswith(PROBES + os.sep):
            paths.append(os.path.relpath(p, PROBES))
        for ext in ('.lagda.md', '.agda'):
            if f.endswith(ext):
                stems.setdefault(f[:-len(ext)], []).append(p)
                text = io.open(p, encoding='utf-8', errors='replace').read()
                if ext == '.agda':
                    code[p] = text.split('\n')
                else:
                    lines, inside = [], False
                    for line in text.split('\n'):
                        if line.startswith('```'):
                            inside = line.startswith('```agda') and not inside
                        elif inside:
                            lines.append(line)
                    code[p] = lines

decl, used = {}, set()
for p, lines in code.items():
    for line in lines:
        for tok in re.split(r'[\s(){};"]+', line):
            used.add(tok)
            used.update(tok.split('.'))
        for h in re.findall(r'\bto\s+([^\s;)]+)', line) if 'renaming' in line else []:
            decl.setdefault(h, set()).add(p)
        words = line.split()
        while words and words[0] in KEYWORDS:
            words = words[1:]
        if not words or not (line[0].isspace() or line[0] not in '-{'):
            continue
        heads = []
        if ':' in words:                       # a b c : T
            heads = words[:words.index(':')]
        elif '=' in words or line.lstrip().split()[0] in KEYWORDS:
            heads = words[:1]
        for h in heads:
            decl.setdefault(h, set()).add(p)

def resolve_path(tok):
    tok = tok.rstrip('/')
    for base in ('', 'OCF/Align/'):
        for suffix in ('', '.lagda.md', '.agda'):
            if os.path.exists(os.path.join(PROBES, base + tok + suffix)):
                return True
    if os.path.exists(os.path.join(ROOT, tok)):
        return True
    if '*' in tok:
        return any(fnmatch.fnmatch(p, tok) or fnmatch.fnmatch(os.path.basename(p), tok + '*') for p in paths)
    return False

def resolve_base(tok):
    return any(os.path.basename(p) == tok for p in paths)

def is_path(tok):
    return '/' in tok or '*' in tok or re.search(r'\.(md|py|agda)$', tok) is not None

def module_files(tok):
    if tok in stems:
        return stems[tok]
    if '/' in tok:
        base = os.path.join(PROBES, tok)
        return [base + e for e in ('.lagda.md', '.agda') if os.path.exists(base + e)]
    return []

def check(tok):
    """None 表示找到, 否则返回问题."""
    if is_path(tok):
        return None if resolve_path(tok) or resolve_base(tok) else '找不到文件'
    if tok in stems or tok in decl:
        return None
    last = tok.split('.')[-1]
    if '.' in tok and last in decl:
        return None
    return '只有使用, 没有声明' if tok in used or last in used else '找不到'

def check_map(MAP):
    text = io.open(MAP, encoding='utf-8').read()
    body, fence = [], False
    for line in text.split('\n'):
        if line.startswith('```'):
            fence = not fence
        elif not fence:
            body.append(line)

    tokens = []
    for line in body:
        for t in re.findall(r'`([^`]+)`', line):
            if t not in tokens:
                tokens.append(t)

    bad = 0
    for t in tokens:
        why = check(t)
        if why:
            bad += 1
            print('缺失: `%s` (%s)' % (t, why))

    # 表里 "定理" 列的名字要声明在 "文件" 列的文件里
    header, rows = None, 0
    for line in body:
        if not line.startswith('|'):
            header = None
            continue
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        if header is None:
            header = cells
            continue
        if set(cells[0]) <= set('-') or '定理' not in header or '文件' not in header:
            continue
        names = re.findall(r'`([^`]+)`', cells[header.index('定理')])
        files = re.findall(r'`([^`]+)`', cells[header.index('文件')])
        if not names or not files:
            continue
        rows += 1
        where = [p for f in files for p in module_files(f)]
        for n in names:
            last = n.split('.')[-1]
            if not set(where) & decl.get(last, set()):
                bad += 1
                real = sorted(os.path.relpath(p, PROBES) for p in decl.get(last, set()))[:4]
                print('文件不对: `%s` 不在 %s; 声明在 %s' % (n, files, real))

    print('%s: 检查 %d 个名字, %d 行表格; 问题 %d 个' %
          (os.path.relpath(MAP, ROOT), len(tokens), rows, bad))
    return bad


def check_links(documents):
    """只查文件目标；不猜测数学含义，也不认证标题片段。"""
    bad, links = 0, 0
    for path in documents:
        text = io.open(path, encoding='utf-8').read()
        fence = False
        for line in text.splitlines():
            if line.startswith('```'):
                fence = not fence
            if fence:
                continue
            # 行内代码里的提议文字或链接示例不是导航；保留非空占位，
            # 以免漏掉 [`文件名`](实际目标) 这种合法链接。
            line = re.sub(r'(`+)(.*?)\1', 'CODE', line)
            for target in re.findall(r'(?<!!)\[[^\]\n]+\]\(([^)\n]+)\)', line):
                target = target.strip().strip('<>')
                url = urlsplit(target)
                if url.scheme or url.netloc or not url.path:
                    continue
                links += 1
                dest = os.path.normpath(os.path.join(os.path.dirname(path), unquote(url.path)))
                if not os.path.exists(dest):
                    bad += 1
                    print('断链: %s -> %s' % (os.path.relpath(path, ROOT), target))
    print('本地链接: %d 个目标; 问题 %d 个（不检查标题片段）' % (links, bad))
    return bad


bad = sum(check_map(path) for path in MAPS)
if not sys.argv[1:]:
    # 只检查这次维护的导航文档；不把全部历史正文强改成今天的表述。
    snapshots = [os.path.join(PROBES, 'Survey', n) for n in
                 ('Stage-2026-11-06.md', 'RouteReview.md', 'RouteReview2.md',
                  'ClosedTermReview.md', 'StallDiagnosis.md', 'SkeletonAudit.md', 'RouteSeal.md')]
    historical = snapshots + [os.path.join(PROBES, n) for n in
                              ('LOG.md', 'HANDOFF-2026-11-07.md')]
    documents = list(dict.fromkeys(MAPS + historical + [os.path.join(ROOT, 'README.md'),
                os.path.join(PROBES, 'Survey', 'ResearchHistory.md'),
                os.path.join(PROBES, 'Survey', 'EBOEndgame.lagda.md'),
                os.path.join(PROBES, 'Survey', 'EBOHandbook.md'),
                os.path.join(PROBES, 'Survey', 'EBOHandbook-proposals.md')]))
    bad += check_links(documents)
    for path in historical:
        if '<!-- historical-scope -->' not in io.open(path, encoding='utf-8').read():
            bad += 1
            print('缺历史作用域提示: %s' % os.path.relpath(path, ROOT))
    entry = io.open(os.path.join(PROBES, 'README.md'), encoding='utf-8').read()
    if not re.search(r'更新时间：\d{4}-\d{2}-\d{2}', entry) or 'id="current-state"' not in entry:
        bad += 1
        print('入口缺更新时间或当前状态锚点')
print('导航完整性问题合计 %d；不认证数学结论、编译状态或路线选择。' % bad)
sys.exit(1 if bad else 0)
