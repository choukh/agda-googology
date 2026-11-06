#!/usr/bin/env python3
"""Generate StrRel14SemJ / StrRel14NiJ / StrRel14KpJ from StrRel12Sem / StrRel12Ni / StrRel12Kp.

Usage (from repo root): python3 probes/Survey/scripts/strrel14/mk_semj.py .

The proofs are copied verbatim; only the state hypothesis changes: `R∀c` becomes the
invariant `J` of a record `I : Inv` (StrRel14If), `advRc`/`cvRc` become the record's
closure laws `⊕J`/`cvJ`, the two projections of `R∀c` go through `toR`, and
`HAW`/`SemW`/`haw↾` become `HAWJ`/`SemJ`/`haw↾J`.
"""
import re, sys, os

root = sys.argv[1] if len(sys.argv) > 1 else '.'
D = os.path.join(root, 'probes', 'OCF', 'Align')

def rd(n):
    with open(os.path.join(D, n), encoding='utf-8') as f:
        return f.read()

def wr(n, s):
    with open(os.path.join(D, n), 'w', encoding='utf-8') as f:
        f.write(s)

B = r'(?<![^\s(){};.@])'
E = r'(?![^\s(){};])'

def tok(s, a, b):
    return re.sub(B + re.escape(a) + E, b, s)

def body(src, start_marker):
    i = src.index(start_marker)
    return src[i:]

def common(s):
    s = s.replace('proj₂ hY', 'proj₂ (toR hY)')
    s = s.replace('proj₁ hY (tg', 'proj₁ (toR hY) (tg')
    for a, b in [('R∀c', 'J'), ('advRc', '⊕J'), ('cvRc', 'cvJ'), ('HAW', 'HAWJ'), ('SemW', 'SemJ'), ('haw↾', 'haw↾J')]:
        s = tok(s, a, b)
    return s

HEAD = '''# 结构关系, 第十四轮 ({n}): {title} (生成)

> 由 `probes/Survey/scripts/strrel14/mk_semj.py` 从 [{src}]({src}.lagda.md) 生成 (从仓库根运行 `python3 probes/Survey/scripts/strrel14/mk_semj.py .`, 逐字节可重生成). 入口 [StrRel14J](StrRel14J.lagda.md). 不读记号. 证明逐句不变, 只换状态前提: `R∀c` 换成不变量记录 `I : Inv` ([StrRel14If](StrRel14If.lagda.md)) 的 `J`, `advRc`/`cvRc` 换成记录的封闭律 `⊕J`/`cvJ`, `R∀c` 的两个分量经 `toR` 取, `HAW`/`SemW`/`haw↾` 换成 `HAWJ`/`SemJ`/`haw↾J`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{{-# OPTIONS --safe --without-K --lossy-unification #-}}
open import OCF.Align.HtFeedTree using (H; LgH)
open import OCF.Align.StrRel14If using (Inv)
module OCF.Align.{mod} (Λ : H) (lΛ : LgH Λ) (I : Inv Λ lΛ) where

open import OCF.Align.StrRel14If Λ lΛ using (module WithInv)
open WithInv I using (HAWJ; SemJ)
open Inv I using (J; toR; cvJ; ⊕J)
'''

# ---------- Sem ----------
sem = rd('StrRel12Sem.lagda.md')
imp_s = sem[sem.index('open import Data.Nat'):sem.index('module P = At')]
imp_s = imp_s.replace('open import OCF.Align.StrRel12Rel using', 'open import OCF.Align.StrRel12Rel using')
out = HEAD.format(n='一', title='与层无关的六条规则与两世界走法, 带不变量', src='StrRel12Sem', mod='StrRel14SemJ')
out += imp_s
out += 'open import OCF.Align.StrRel12Sem Λ lΛ using (Top; TC; OAc; R∀c)\n\n'
out += 'module P = At Λ lΛ\n'
out += 'open P using (Tg; tg; wm; tm; lm; tg↑; τ₀; St; Df; yc; d; z; cv; _⊕⟨_⟩_; Run; Rpt; Ig; Ig↾; LW; Walk; WRp; _⨾ᴰ_; nlᴰ; zeroD)\n'
out += '''
haw↾J : ∀ L {W W′ W₁ W₁′} {lW : Lg W} {lW′ : Lg W′} {p : W ⊲ W₁} {lW₁ : Lg W₁} {p′ : W′ ⊲ W₁′} {lW₁′ : Lg W₁′}
          {A₀ : Ig L W} {A₀′ : Ig L W′} → AP lW lW′ p lW₁ p′ lW₁′ → HAWJ L lW lW′ A₀ A₀′ → HAWJ L lW₁ lW₁′ (Ig↾ p A₀) (Ig↾ p′ A₀′)
haw↾J L {p = p} {p′ = p′} ap ha p₂ p₂′ l l′ cp = ha (⊲-tr p p₂) (⊲-tr p′ p₂′) l l′ (cp-tr ap cp)
```

'''
out += common(body(sem, '## 3 与层无关的六条规则'))
wr('StrRel14SemJ.lagda.md', out)

# ---------- Ni ----------
ni = rd('StrRel12Ni.lagda.md')
imp_n = ni[ni.index('open import Data.Nat'):ni.index('module P = At')]
imp_n = imp_n.replace(
    'open import OCF.Align.StrRel12Sem Λ lΛ using (TC; OAc; R∀c; cvRc; advRc; HAW; haw↾; SemW)',
    'open import OCF.Align.StrRel12Sem Λ lΛ using (TC; OAc; R∀c)\nopen import OCF.Align.StrRel14SemJ Λ lΛ I using (haw↾J)')
out = HEAD.format(n='二', title='同层节点规则 `niᴸ` 的可靠性, 带不变量', src='StrRel12Ni', mod='StrRel14NiJ')
out += imp_n + ni[ni.index('module P = At'):ni.index('## 1 节点规则的语义')]
out += common(body(ni, '## 1 节点规则的语义'))
wr('StrRel14NiJ.lagda.md', out)

# ---------- Kp ----------
kp = rd('StrRel12Kp.lagda.md')
imp_k = kp[kp.index('open import Data.Nat'):kp.index('module P = At')]
imp_k = imp_k.replace(
    'open import OCF.Align.StrRel12Sem Λ lΛ using (Top; TC; OAc; R∀c; cvRc; advRc; HAW; haw↾; SemW; module WalkR)',
    'open import OCF.Align.StrRel12Sem Λ lΛ using (Top; TC; OAc; R∀c)\nopen import OCF.Align.StrRel14SemJ Λ lΛ I using (haw↾J; module WalkR)')
out = HEAD.format(n='三', title='`nκ` 规则的可靠性, 带不变量', src='StrRel12Kp', mod='StrRel14KpJ')
out += imp_k + kp[kp.index('module P = At'):kp.index('## 1 不变量')]
out += common(body(kp, '## 1 不变量'))
wr('StrRel14KpJ.lagda.md', out)
print('ok')
