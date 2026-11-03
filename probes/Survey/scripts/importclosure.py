# -*- coding: utf-8 -*-
# 导入闭包审计: 打印一个模块的传递导入闭包, 闭包里出现记号或标签模块就失败. 见 AGENTS.md 的"审计".
#
# 用法 (任意目录):
#   python3 probes/Survey/scripts/importclosure.py <模块> [<模块> ...]
#   python3 probes/Survey/scripts/importclosure.py --only OCF.Free. --only OCF.BTBO <模块>
#   python3 probes/Survey/scripts/importclosure.py --verbatim probes/OCF/Free/Lab
# 退出码: 0 全部干净, 1 有模块碰到禁用表 (或 --only 之外的本地模块), 2 用法或找不到模块.
#
# 与 depslice.py 的区别: depslice 是定义级、语法级的近似, 看不见 Agda 求解的隐式参数.
# 这里只看模块导入, 粒度粗, 但闭包外的定义不可能被检查器用到, 所以结论是编译器保证的 (前提: 文件编译通过).
#
# --only P: 闭包内的本地模块 (probes/, src/ 下的) 必须以某个 P 开头.
# --verbatim D: 辅助检查. D 下每个代码行 (导入, 模块头, 选项除外) 须逐字出现在
#               probes/OCF/Align/ 或 src/ 的源文件里; 打印不是逐字的行. 只报告, 不影响退出码.
import io, os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
BASES = ('probes', 'src')

# 禁用表: 记号本身, 带标签的定理, 以及把记号搬上树的对齐文件.
DENY = [
    r'OCF\.Notation(\..*)?',
    r'OCF\.Align\.(EBO|Translate)',
    r'OCF\.Align\.(Correspond|Label|Standard|StandardOmega|SystemOmega|Stage2|Stage2Label)',
    r'OCF\.Align\.(GoodL|GoodLBase|Decouple|DecoupleBase|Omega2|Omega2Base|OmegaK|OmegaKBase)',
    r'OCF\.Align\.(OmegaExp|OmegaExpBase|OmegaSq|OmegaSqBase|NonTight|NonTightBase|TopDown)',
    r'OCF\.Align\.(Symbolic|Bachmann|Closure|Value)',
    r'OCF\.Align\.Uniform\w*(Label|Accept|Walk)',
    r'OCF\.Free\.(Bridge|Lab\..*)',
]
DENY_RE = re.compile('^(?:' + '|'.join(DENY) + ')$')
IMPORT_RE = re.compile(r'^\s*(?:open\s+)?import\s+([^\s;()]+)', re.M)


def path_of(mod):
    for base in BASES:
        for ext in ('.lagda.md', '.agda'):
            p = os.path.join(ROOT, base, *mod.split('.')) + ext
            if os.path.exists(p):
                return p
    return None


def code_of(path):
    text = io.open(path, encoding='utf-8').read()
    if path.endswith('.md'):
        text = '\n'.join(re.findall(r'^```agda[ \t]*\n(.*?)^```', text, re.S | re.M))
    text = re.sub(r'\{-(?!#).*?-\}', '', text, flags=re.S)
    return re.sub(r'(?m)(^|\s)--.*$', '', text)


def closure(root):
    """返回 {模块: 从根出发的导入路径}, 库模块也在内."""
    paths = {root: [root]}
    work = [root]
    while work:
        mod = work.pop()
        p = path_of(mod)
        if p is None:
            continue
        for dep in IMPORT_RE.findall(code_of(p)):
            if dep not in paths:
                paths[dep] = paths[mod] + [dep]
                work.append(dep)
    return paths


def audit(root, only):
    if path_of(root) is None:
        print('找不到模块', root)
        return 2
    paths = closure(root)
    local = sorted(m for m in paths if path_of(m))
    lib = [m for m in paths if not path_of(m)]
    bad = [m for m in local if DENY_RE.match(m)]
    outside = [m for m in local if only and not any(m.startswith(p) for p in only) and m not in bad]
    print('== %s: 闭包 %d 个模块 (本地 %d, 库 %d)' % (root, len(paths), len(local), len(lib)))
    for m in local:
        print('   ' + m)
    print('   禁用表命中: %d; --only 之外: %d' % (len(bad), len(outside)))
    for m in bad[:12] + outside[:12]:
        print('   ! ' + m + '  <-  ' + ' <- '.join(reversed(paths[m][:-1])))
    if len(bad) + len(outside) > 24:
        print('   ! ... 其余从略')
    if bad or outside:
        print('   FAIL')
        return 1
    print('   OK')
    return 0


def verbatim(target):
    corpus = set()
    for base in (os.path.join(ROOT, 'probes', 'OCF', 'Align'), os.path.join(ROOT, 'src')):
        for d, _, fs in os.walk(base):
            for f in fs:
                if f.endswith(('.lagda.md', '.agda')):
                    corpus.update(l.rstrip() for l in code_of(os.path.join(d, f)).split('\n'))
    files = []
    if os.path.isdir(target):
        files = sorted(os.path.join(target, f) for f in os.listdir(target) if f.endswith('.lagda.md'))
    else:
        files = [target]
    skip = re.compile(r'\s*(open\s+import|import|module OCF\.|\{-#)')
    total = same = 0
    for p in files:
        for l in code_of(p).split('\n'):
            s = l.rstrip()
            if not s.strip() or skip.match(s):
                continue
            total += 1
            if s in corpus:
                same += 1
            else:
                print('   非逐字 %s: %s' % (os.path.relpath(p, ROOT), s[:110]))
    print('== 逐字检查 %s: %d 行代码, %d 行逐字, %d 行不是' % (os.path.relpath(target, ROOT), total, same, total - same))


def main(argv):
    only = []
    roots = []
    i = 0
    while i < len(argv):
        if argv[i] == '--only' and i + 1 < len(argv):
            only.append(argv[i + 1])
            i += 2
        elif argv[i] == '--verbatim' and i + 1 < len(argv):
            verbatim(os.path.abspath(argv[i + 1]))
            i += 2
        else:
            roots.append(argv[i])
            i += 1
    code = 0
    for r in roots:
        code = max(code, audit(r, only))
    return code


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
