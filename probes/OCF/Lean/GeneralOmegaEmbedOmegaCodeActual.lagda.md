# 全部原塔与Λ地板的实际运行嵌入

统一的Layer实例现在连到原floor、实际code和原run。跨up与分量注入
仍使用原函数，不替换成相似解释器；本篇只证明嵌入，不证明EBO值界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedOmegaCodeActual where
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (twL; ΛL)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.GeneralOmegaEmbedOmegaIf
open import OCF.Lean.GeneralOmegaEmbedOmegaLayer using (tower-layer; lambda-layer)
open import OCF.Lean.GeneralOmegaEmbedOmegaFloorRun using (floor)
open import OCF.Lean.GeneralOmegaEmbedOmegaCodeRun using (coded; sound)
open import OCF.Lean.GeneralOmegaEmbedIf using (Coded; cz; cs; cl; co)
open import OCF.Lean.GeneralOmegaEmbedGenerated using (up-right; branch-right)
open import OCF.Lean.GeneralOmegaEmbedRun using () renaming (sound to coded-sound)
open import OCF.Lean.FrozenWorldLift using (Same)
import OCF.Lean.GeneralOmegaConsumeRun as R

floor-same : ∀ {x y} (p : Layer x y) → Same (R.run x (flL x)) (R.run y (flL y))
floor-same p = sound p (floor p)
floor-up : ∀ {x} (p : Layer x x) →
  Same (R.run x (flL x)) (R.run (ls x) (up (flL x)))
floor-up p = coded-sound (up-right (coded p (floor p)))
floor-branch : ∀ {k g} e → Layer (g e) (g e) →
  Same (R.run (g e) (flL (g e)))
    (R.run (lΩ k g) (ι {IxL k} {FXL k g} (inj₂ e) (flL (g e))))
floor-branch e p = coded-sound (branch-right (coded p (floor p)))

sum-right : ∀ {x f n a b} → Coded x (f n) a b → Coded x (OCF.Lean.LHRecTy.ll f) a (ι n b)
sum-right cz = cz
sum-right (cs p) = cs (sum-right p)
sum-right (cl p) = cl (λ n → sum-right (p n))
sum-right (co p) = co (λ q → sum-right (p q))
floor-sum : ∀ f n → Layer (f n) (f n) →
  Same (R.run (f n) (flL (f n))) (R.run (OCF.Lean.LHRecTy.ll f) (ι n (flL (f n))))
floor-sum f n p = coded-sound (sum-right (coded p (floor p)))

tower-up : ∀ n → Same (R.run (twL n) (flL (twL n)))
  (R.run (ls (twL n)) (up (flL (twL n))))
tower-up n = floor-up (tower-layer n)
lambda-up : Same (R.run ΛL (flL ΛL)) (R.run (ls ΛL) (up (flL ΛL)))
lambda-up = floor-up lambda-layer
tower-in-lambda : ∀ n → Same (R.run (twL n) (flL (twL n)))
  (R.run ΛL (ι n (flL (twL n))))
tower-in-lambda n = floor-sum twL n (tower-layer n)
```

原全部twL与完整Λ有实际floor证，故这些字段前提非空。tower-in-lambda
是原单分量嵌入的完整运行等值，不据此删除原ΣF左前缀，也不把这条
嵌入定理读成实际EBO阶段覆盖或已验收ψ₀Λ。
