# 结构关系, 第十二轮 (七): 本族里 $\Omega_{\Omega^{\mathsf H}}$ 在两个世界之间不自相关 (否定)

> 不读记号. 入口 [StrRel12](StrRel12.lagda.md). `StrRel11Om.¬rel-Ω` 在本轮的关系族 (`StrRel12Rel.Rel`, 分支对取 `CP`) 里照样成立: 左边在世界 $0$, 右边在世界 $1$, `CP` 分支世界对 $(1,2)$ 上两个节点的坐标层是 `emb 1` 与 `emb 2`, 只有同层的 `niᴸ`, 所以不相关 (`¬ΩR`). 这说明入口的 `ΩR` 不能推广到 $\Omega$-极限层, 于是 `haAct` (外层动作 `Act` 的动作前提, 它在目标层 $t=\Omega^{\mathsf H}$ 上要 `Rel t (Ωd t {m}) (Ωd t {m′})`) 在 $\Lambda=\Omega^{\mathsf H}$ 时不能照入口的证法得到 (这一句是判断: 没有编译 "`HAW … Act Act` 不成立"). 范围: 只否定本族 (同层节点规则) 里的这一个相关.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel12Om where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (z≤; s≤; ≤-refl)
open import OCF.Align.HtFeedTree using (Ωd)
open import OCF.Align.HtFeedHt using (Ωᴴ)
open import OCF.Align.StrRel4Walk using (aS; aP)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel12Al using (CP)
open import OCF.Align.StrRel12Rel using (Rel; ⨾ᴸ; prᴸ; κᴸ)

one two : A
one = asuc azero
two = asuc one

-- 分支世界对 (1, 2): 对齐, 顶端可比, 自洽
cp12 : CP {V = azero} {V′ = one} tt tt (C.suc C.self) tt (C.suc C.self) tt
cp12 = (aP (aS C.self tt) z≤ ad , ad , refl , refl) , s≤ z≤ , tt , tt
  where
  ad : Adm azero one one two
  ad = one , ≤-refl one , ≤-refl two

¬ΩR : ¬ Rel Ωᴴ {azero} {one} tt tt (Ωd Ωᴴ) (Ωd Ωᴴ)
¬ΩR (⨾ᴸ _ (κᴸ h)) with h (C.suc C.self) (C.suc C.self) tt tt cp12
... | ()
¬ΩR (prᴸ ())
```
