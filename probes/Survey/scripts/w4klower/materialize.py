#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# 把 W4 的 BTBO 下界 (Survey.W4CountableLower) 依赖的留档附件抄成一个实验目录里的 .agda 模块.
# 用法 (从仓库根):  python3 probes/Survey/scripts/w4klower/materialize.py <实验目录>
# 然后:  agda --library-file=<库文件> -i src -i probes -i <实验目录> probes/Survey/W4CountableLower.lagda.md +RTS -M6G -RTS
import os, shutil, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))))
A16 = os.path.join(ROOT, 'probes', 'Survey', 'Reports-2026-11-16', 'attachments')
A24 = os.path.join(ROOT, 'probes', 'Survey', 'Reports-2026-11-24', 'attachments')
A25 = os.path.join(ROOT, 'probes', 'Survey', 'Reports-2026-11-25', 'attachments')

# 模块名 -> (附件目录, 附件前缀)
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
# 越过 BTBO 的第一步 (2026-11-25): 真实运行的追踪与三个 KJ 模块.
for m in ['Audit2', 'KJLevel', 'KJRun', 'KJEbo']:
    SRC[m] = (A25, 'KJ-')

def main():
    if len(sys.argv) != 2:
        sys.exit('用法: materialize.py <实验目录>')
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    for m, (d, pre) in sorted(SRC.items()):
        shutil.copyfile(os.path.join(d, pre + m + '.agda.txt'), os.path.join(out, m + '.agda'))
    print('%d 个模块 -> %s' % (len(SRC), out))

if __name__ == '__main__':
    main()
