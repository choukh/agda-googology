# -*- coding: utf-8 -*-
# 地图检查: probes/README.md 里每个反引号里的文件名或定理名, 都要在 probes/ 下真的存在.
#
# 用法 (任意目录): python3 probes/Survey/scripts/mapcheck.py
# 退出码: 0 全部找到, 1 有缺失或文件不对.
#
# 判定:
#   路径 (含 / 或带扩展名, 可带 *): 依次对 probes/, probes/OCF/Align/, 仓库根解析.
#   模块名: probes/ 或 src/ 下有同名的 .lagda.md 或 .agda (probes 导入 src 的 OCF.BTBO).
#   其他都当定理名: 要在某个 Agda 代码块里有声明 (含 renaming 改出来的名字); 只被使用没有声明的, 算 "只有使用", 也报告.
#   表头有 "定理" 和 "文件" 两列的表: 定理列的每个名字必须声明在文件列写的文件之一里.
# 局限: 只认行首的声明形式 (签名, 定义, data, record, module); 不检查陈述, 也不检查文字说得对不对.
import fnmatch, io, os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
PROBES = os.path.join(ROOT, 'probes')
MAP = sys.argv[1] if len(sys.argv) > 1 else os.path.join(PROBES, 'README.md')   # 参数只用于反向测试
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

print('检查 %d 个名字, %d 行表格; 问题 %d 个' % (len(tokens), rows, bad))
sys.exit(1 if bad else 0)
