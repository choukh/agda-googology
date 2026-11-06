#!/usr/bin/env python3
"""RsOwn 路的禁用构造扫描. 从仓库根运行: python3 probes/Survey/scripts/rsown/forbid.py
只扫描 ```agda 代码块; 打印每个文件的命中, 全部为 0 时退出码 0."""
import re, sys, pathlib

FILES = ["RsOwn", "RsOwnIf", "RsOwnSh", "RsOwnSW", "RsOwnBd", "RsOwnTm"]
PATS = [r"\bpostulate\b", r"\{!", r"(^|\s)\?(\s|$)", r"TERMINATING", r"NO_POSITIVITY_CHECK",
        r"trustMe", r"--cubical\b(?!-)", r"--with-K", r"[Ff]unext", r"\bFE₀\b", r"\bFEA\b"]

def blocks(text):
    out, on = [], False
    for ln in text.splitlines():
        if ln.strip().startswith("```agda"):
            on = True; continue
        if on and ln.strip().startswith("```"):
            on = False; continue
        if on:
            out.append(ln)
    return out

bad = 0
root = pathlib.Path("probes/OCF/Align")
for f in FILES:
    text = (root / f"{f}.lagda.md").read_text(encoding="utf-8")
    code = blocks(text)
    hits = [(i, ln) for i, ln in enumerate(code) for p in PATS if re.search(p, ln)]
    opt = [ln for ln in code if "OPTIONS" in ln]
    okopt = all(ln.strip() == "{-# OPTIONS --safe --without-K --lossy-unification #-}" for ln in opt) and len(opt) == 1
    print(f"{f}: {len(code)} 行代码, 命中 {len(hits)}, 选项行 {'正确' if okopt else '异常'}")
    for i, ln in hits:
        print("   ", ln)
    bad += len(hits) + (0 if okopt else 1)
sys.exit(1 if bad else 0)
