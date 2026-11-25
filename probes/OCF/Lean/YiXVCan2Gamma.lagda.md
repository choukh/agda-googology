# YiXV YiXVCan2Gamma
> 验收文件。编译定理：实际参照序列 γ 2 n 的每项有好树证据、后继界与累加一步界。
> 按 YiOverOps/YiXVRef2Add 的证明扩展，仅二层参照域；源树γ₂与整链上界仍未证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Gamma where
open import Data.Nat using (ℕ; zero; suc)
import OCF.Align.Level as L
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
open import OCF.Align.YiLvValBase using (γ)
open import OCF.Lean.YiXVCan2Core
import OCF.Lean.YiXVCan2Add as A
import OCF.Lean.YiXVCan2Psi as P
import OCF.Lean.YiXVCanTau as T

Γ : ℕ → F.T₂
Γ = γ 2

good : ∀ n → Gd (Γ n)
good zero = Gd-Ω₂
good (suc n) = P.good (good n)

base-inv : Le (L.suc F.Ω₂) (P.B O.Ω₁)
base-inv = pack (gs Gd-Ω₂) (P.goodB O.Gd-Ω) (aa₀
  (pack (gs Gd-Ω₂) (gl (P.good-iter Gd-Ω₂)) (lr 2 (A.plus Ω₂-refl P.pos-Ω))))

inv-Ω : Le (L.suc F.Ω₂) (P.Ψ F.Ω₂)
inv-Ω = pack (gs Gd-Ω₂) (P.good Gd-Ω₂) (aa₁ (λ z hz →
  trans base-inv (P.monoB (P.goodB O.Gd-Ω) (P.goodB (T.good (T.start-good hz))) (T.floor (T.start-floor hz)))))

inv : ∀ n → Le (L.suc (Γ n)) (Γ (suc n))
inv zero = inv-Ω
inv (suc n) = trans (P.strict (good (suc n))
  (trans P.pos-Ω (P.base (Γ n) (good (suc n))))) (P.mono (inv n))

next : ∀ n → Le (Γ n) (Γ (suc n))
next n = trans (pack (good n) (gs (good n)) (ws (refl (good n)))) (inv n)

step : ∀ {X} n → Le X (Γ n) → Le (X L.+ P.Ψ X) (Γ (suc (suc n)))
step n p = trans
  (pack (A.good (left p) (P.good (left p))) (P.good (gs (good n)))
    (lr 2 (A.plus (trans p (next n)) (P.mono p))))
  (P.mono (inv n))

sample : Gd (Γ 1)
sample = good 1
sample-step : Le (F.Ω₂ L.+ P.Ψ F.Ω₂) (Γ 2)
sample-step = step 0 Ω₂-refl
```
