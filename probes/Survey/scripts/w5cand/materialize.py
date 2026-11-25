#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# 把候选改写 W5 (Survey.W5Candidate) 依赖的留档附件抄成一个实验目录里的 .agda 模块: 原 W4 的整条链加上候选的整条链, 两者并存.
# 用法 (从仓库根):  python3 probes/Survey/scripts/w5cand/materialize.py <实验目录>
# 然后:  agda --library-file=<库文件> -i src -i probes -i <实验目录> probes/Survey/W5Candidate.lagda.md +RTS -M6G -RTS
# pack.py 是生成候选链时用的改名脚本 (依赖候选定义的模块换成 W5…/K5…, 其余原名共享), 留作记录.
import os, shutil, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))))
A16 = os.path.join(ROOT, 'probes', 'Survey', 'Reports-2026-11-16', 'attachments')
A24 = os.path.join(ROOT, 'probes', 'Survey', 'Reports-2026-11-24', 'attachments')
A25 = os.path.join(ROOT, 'probes', 'Survey', 'Reports-2026-11-25', 'attachments')

SRC = {}
for m in ['W4Block', 'W4Ops', 'W4Path', 'W4Fold']:
    SRC[m] = (A16, 'B4W4-')
for m in ['WVOne', 'WVTwo']:
    SRC[m] = (A16, 'B5D-')
SRC['KMir'] = (A24, 'M0-')
SRC['KPow'] = (A24, 'M1-')
for m in ['KRel', 'KIface', 'KEmb', 'KEmbTr']:
    SRC[m] = (A24, 'M2v2-')
for m in ['KOpBase', 'KOpPow', 'KOpMain', 'KOpOp']:
    SRC[m] = (A24, 'M4b-')
for m in ['KBBase', 'KBAdd', 'KBRows', 'KBMain', 'KBRu', 'KBTop', 'KBAll']:
    SRC[m] = (A24, 'M3b-')
for m in ['KAsBase', 'KAsV3', 'KAsTw']:
    SRC[m] = (A24, 'M5-')
for m in ['KLowIface', 'KLow', 'KBtbo']:
    SRC[m] = (A24, '')
SRC['KLoc'] = (A24, 'KLoc-')
SRC['KLnNeg'] = (A24, 'KLn-')
SRC['KLpFin'] = (A24, 'KLp-')

def main():
    if len(sys.argv) != 2:
        sys.exit('用法: materialize.py <实验目录>')
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    n = 0
    for m, (d, pre) in sorted(SRC.items()):
        shutil.copyfile(os.path.join(d, pre + m + '.agda.txt'), os.path.join(out, m + '.agda'))
        n += 1
    for f in sorted(os.listdir(A25)):
        if f.startswith('W5-') and f.endswith('.agda.txt'):
            shutil.copyfile(os.path.join(A25, f), os.path.join(out, f[len('W5-'):-len('.txt')]))
            n += 1
    print('%d 个模块 -> %s' % (n, out))

if __name__ == '__main__':
    main()
