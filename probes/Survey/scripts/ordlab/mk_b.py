# -*- coding: utf-8 -*-
# 由 OrdLab{Base,Class,Rel,Psi,Eval,Top} 生成 OrdLabB{...}: 标签类对高度结构 HtB (LadderOrdTree) 抽象.
# 只替换名字: HtS → HtB, PxS → PxB, LadderInf* → LadderOrd*, OrdLab{...} → OrdLabB{...}. 用法: python3 mk_b.py [输出目录].
import re,os,sys,io
HERE=os.path.dirname(os.path.abspath(__file__))
A=os.path.abspath(os.path.join(HERE,'..','..','..','OCF','Align'))+'/'
OUT=(sys.argv[1].rstrip('/')+'/') if len(sys.argv)>1 else A
MODS='Base Class Rel Psi Eval Top'.split()
for m in MODS:
    s=io.open(A+'OrdLab%s.lagda.md'%m,encoding='utf-8').read()
    i=s.index('```agda'); head,body=s[:i],s[i:]
    body=re.sub(r'OCF\.Align\.OrdLab('+'|'.join(MODS)+r')\b',r'OCF.Align.OrdLabB\1',body)
    body=re.sub(r'OCF\.Align\.LadderInf','OCF.Align.LadderOrd',body)
    body=re.sub(r'\bHtS\b','HtB',body); body=re.sub(r'\bPxS\b','PxB',body)
    note='> **机械改写, 验收用.** 由 [OrdLab%s](OrdLab%s.lagda.md) 经 `Survey/scripts/ordlab/mk_b.py` 生成: 只把 `HtS`, `PxS`, `LadderInf*` 换成 `HtB`, `PxB`, `LadderOrd*`. 见 [OrdLab](OrdLab.lagda.md).\n\n'%(m,m)
    io.open(OUT+'OrdLabB%s.lagda.md'%m,'w',encoding='utf-8').write(note+'# OrdLabB%s\n\n'%m+body)
