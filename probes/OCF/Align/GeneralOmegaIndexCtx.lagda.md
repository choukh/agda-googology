# 原指标Ω在实际外上下文中的捕获

put始终保留在源表达式外，不把put(a+b)改写成两个put的加法，也不
借Same过run。唯一坐标运输是Embedding已有的实际code-back等式。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaIndexCtx where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (ΩL; _⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL; ixK)
open import OCF.Lean.LHRecLeg using (ek; frC)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.GeneralOmegaEmbedContext using (Embedding; ctx; code-back; put)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.HigherIndexConsumePositive using (mul-partial)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenAbsorbNegUpper using (P; infl)
open import OCF.Align.GeneralOmegaConsumeValuePure using (positive)
open import OCF.Align.GeneralOmegaIndexIf using (θ)
open import OCF.Align.GeneralOmegaIndexRaise
open import OCF.Lean.GeneralOmegaCompletionIf using (Capture)
import OCF.Lean.GeneralOmegaCompletionRun as Complete

module Mapped {x y : LH} (j : Embedding x y) where
  prefix : ∀ A B C → run y (A ⊞ put j B) ≤ᵛ run y (A ⊞ put j (B ⊞ C))
  prefix A B hz = ≤-refl _
  prefix A B (hs C) = ≤l 0 (prefix A B C)
  prefix A B (hl f) = ≤l 0 (prefix A B (f 0))
  prefix A B (hΩ κ f) = ≤l 0 (prefix A B (f (frC (ctx j) κ (code y (ek (ctx j) κ) (hs hz)))))

  repeated : ∀ A B {C} → Raises C →
    Ops.repeat S⊥ (run y (A ⊞ put j B)) ≤ᵛ run y (A ⊞ put j (B ⊞ C))
  repeated A B (successor {a}) = repeat-mono (prefix A B a)
  repeated A B (limit n p) = ≤l n (repeated A B p)
  repeated A B (omega {κ} {g}) = l≤ (λ n → ≤l n (parts n))
    where
    H : Cd → Cd
    H d = run y (A ⊞ put j (B ⊞ g (frC (ctx j) κ (code y (ek (ctx j) κ) d))))
    parts : ∀ n → Ops.partial S⊥ (λ _ → run y (A ⊞ put j B)) n ≤ᵛ
      Ops.partial S⊥ (λ n → H (chain H n)) n
    parts zero = prefix A B _
    parts (suc n) = add-mono (parts n) (prefix A B _)

module Raised (k : LH) (g : HB (Lv k) → LH) {y}
  (j : Embedding (lΩ k g) y) (raising : ∀ e → Raises (flL (g e))) where
  affine : ∀ A a d → P (run y (A ⊞ put j (θ k g a))) d ≤ᵛ
    run y (A ⊞ put j (θ k g (a ⊞ pure (Lv k) d)))
  affine A a hz = ≤-refl _
  affine A a (hs d) = ≤-trans
    (l≤ (λ n → ≤l n (mul-partial (affine A a d) n)))
    (Mapped.repeated j A (θ k g (a ⊞ pure (Lv k) d))
      (raises-ι (inj₂ (a ⊞ pure (Lv k) d)) (raising (a ⊞ pure (Lv k) d))))
  affine A a (hl f) = l≤ (λ n → ≤l n (affine A a (f n)))

  H : HB (Lv y) → Cd → Cd
  H A d = run y (A ⊞ put j (θ k g
    (frC (ctx j) ixK (code y (ek (ctx j) ixK) d))))
  captures : ∀ A d → leg d ≤ᵛ H A d
  captures A d rewrite code-back j ixK d = ≤-trans
    (infl (run y (A ⊞ put j (θ k g (flL k))))
      (positive y (A ⊞ put j (θ k g (flL k)))) (leg d))
    (affine A (flL k) (leg d))
  captured : ∀ A → Capture (H A)
  captured A = record { on-chain = λ n → captures A (chain (H A) n) }
  stable : ∀ A → leg (run y (A ⊞ put j (flL (lΩ k g)))) ≤ᵛ
    run y (A ⊞ put j (flL (lΩ k g)))
  stable A = Complete.Result.upper (H A) (captured A)

module Successor (k y : LH) (j : Embedding (ΩL (ls k)) y) =
  Raised k (λ e → ΩL k ⊕L upL k e) j
    (λ e → floor-raises (plus-shape (Ω-shape k) (upL k e)))
module Index (k : LH) (g : HB (Lv k) → LH) (y : LH)
  (j : Embedding (ΩL (lΩ k g)) y) = Raised k (λ e → ΩL (g e)) j
    (λ e → floor-raises (Ω-shape (g e)))
```

两个实例直接覆盖原ΩL规则经任何已证code-compatible上下文嵌入的
完整Ω输出及任意外前缀，得到完成前后同值的上界方向。反向由现有
inflation给出。尚不覆盖put内部额外累计前缀，也不是EBO强度上界。
