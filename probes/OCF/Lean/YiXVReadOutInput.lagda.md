# YiXVReadOutInput
> 验收文件。档位：编译定理。全局实际树上界内的 Out 接口：同时记录参照合法性、底部读回界与全部带路径槽位。
> 从 YiXVSource*、YiCeilRead 与原 Level 的递归推广；未交节点行、外层 n≥2 读回界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadOutInput where
open import Data.Unit using (tt)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼; 1≼ψ⁰)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVZeroRead as Zero
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVLvlLiteral as Literal
import OCF.Lean.YiXVReadWorldInput as W
σ : ∀ {root x} → x P.≤ᵀ root → L.Simᴵ (T.lvl x) (T.lvl root)
σ P.here q = q
σ (P.below p) q = L.<ᴵ-trans q (Literal.step (P.raw p))
cap : ∀ {root x} → x P.≤ᵀ root → L.Ordᶜ (T.lvl root) → L.Ordᶜ (T.lvl x) → L.Ordᶜ (T.lvl root)
cap p Z X = L.add Z (σ p) X
record Out (root x : S.Tr S.zero) (within : x P.≤ᵀ root) (B : Fold.Base (J.ℓ x))
  (Z : L.Ordᶜ (T.lvl root)) (a : S.Tr (J.ℓ x)) (X : L.Ordᶜ (T.lvl x)) : Set where
  field
    good : A.Gd (cap within Z X)
    bot : Read.read (Fold.ψ⊥ (J.ℓ x) (T.εh x) (T.ρh x) B a) ≼ L.ψ⁰ (cap within Z X)
    slots : ∀ y (p : y P.≤ᵀ root) (v : J.ℓ y Path.≤ J.ℓ x) →
      U.UR y (Fold.ψs (J.ℓ x) (T.εh x) (T.ρh x) B (J.ℓ y) v
        (Fold.bs B (J.ℓ y) v) (Fold.ns B (J.ℓ y) v) a) (W.φ p (cap within Z X))
one : ∀ {root} (p : S.zero P.≤ᵀ root) Z → L.suc L.zero ≼ W.φ p Z
one p Z = ≼-trans (1≼ψ⁰ Z) (≅→≼ (L.≅-sym (Zero.same (W.pc p) (λ q → L.suc q) Z)))
model₀ : Out S.zero S.zero P.here (Fold.B₀ S.zero) (W.seed S.zero) S.zero (L.Ω L.zero)
Out.good model₀ = A.groundΩ
Out.bot model₀ = 1≼ψ⁰ (cap P.here (W.seed S.zero) (L.Ω L.zero))
Out.slots model₀ .S.zero P.here Path.self = one P.here _
Out.slots model₀ y (P.below ()) v
model₁₀ : Out (S.suc S.zero) S.zero (P.below P.root) (Fold.B₀ S.zero)
  (W.seed (S.suc S.zero)) S.zero (L.Ω L.zero)
Out.good model₁₀ = A.Layer.gs (A.Layer.gs A.Layer.gz)
Out.bot model₁₀ = 1≼ψ⁰ (cap (P.below P.root) (W.seed (S.suc S.zero)) (L.Ω L.zero))
Out.slots model₁₀ .(S.suc S.zero) P.here ()
Out.slots model₁₀ .S.zero (P.below P.root) Path.self = one (P.below P.root) _
Out.slots model₁₀ y (P.below (P.under-suc ())) v
```
