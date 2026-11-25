#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# 把 Survey.W4Rebase 依赖的留档附件抄成一个实验目录里的 .agda 模块:
# 先照 w5cand/materialize.py 抄出原 W4 的链与候选 W5 的链, 再加上 2026-11-25 这一轮的三组:
# 第十五次审查的 R15Mono, R15Steer; KQ 的八个模块; 候选 W6 的九个模块.
# 用法 (从仓库根):  python3 probes/Survey/scripts/w4rebase/materialize.py <实验目录>
# 然后:  agda --library-file=<库文件> -i src -i probes -i <实验目录> probes/Survey/W4Rebase.lagda.md +RTS -M6G -RTS
import importlib.util, os, shutil, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(HERE))))
A25 = os.path.join(ROOT, 'probes', 'Survey', 'Reports-2026-11-25', 'attachments')

EXTRA = [('RR15-', m) for m in ['R15Mono', 'R15Steer']]
EXTRA += [('KQ-', m) for m in ['KQBlock', 'KQOps', 'KQPath', 'KQFold', 'KQLev', 'KQRead', 'KQOut', 'KQOutNeg']]
EXTRA += [('W6-', m) for m in ['W6Block', 'W6Ops', 'W6Path', 'W6Loc', 'W6Fold', 'W6Shape', 'W6Trace', 'W6TraceZ', 'W6VsW5']]

def main():
    if len(sys.argv) != 2:
        sys.exit('用法: materialize.py <实验目录>')
    out = sys.argv[1]
    spec = importlib.util.spec_from_file_location('w5cand', os.path.join(os.path.dirname(HERE), 'w5cand', 'materialize.py'))
    base = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(base)
    base.main()
    for pre, m in EXTRA:
        shutil.copyfile(os.path.join(A25, pre + m + '.agda.txt'), os.path.join(out, m + '.agda'))
    print('另加 %d 个模块 -> %s' % (len(EXTRA), out))

if __name__ == '__main__':
    main()
