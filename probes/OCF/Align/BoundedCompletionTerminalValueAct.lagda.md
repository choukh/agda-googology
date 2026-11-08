# 旧第二地板实际动作的值关系不变量

本篇只处理已接实际Old.TΩ2的act；没有假设任意高层折叠保持裸值序。
其单调、膨胀和实际全部坐标的证书均由VRel给出，再送原末段eval。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionTerminalValueAct where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Align.BoundedCompletionTerminalValueIf
open import OCF.Align.BoundedCompletionTerminalValueRun using (eval)
open import OCF.Align.BoundedCompletionTerminalValueClosure
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Align.BoundedNativeTerminalReady as T

one : HB U
one = hs hz
positive : ∀ a → VRel one (Old.act a)
positive hz = vs vz
positive (hs a) = vli 0 (positive a)
positive (hl f) = vli 0 (positive (f 0))
positive (hΩ (inj₁ ()) g)
positive (hΩ (inj₂ _) g) = vor (λ c → positive (g c))

act-mono : ∀ {a b} → VRel a b → VRel (Old.act a) (Old.act b)
act-mono {b = b} vz = positive b
act-mono (vs p) = repeat-rel (act-mono p)
act-mono (vr p) = vli 0 (act-mono p)
act-mono (vl p) = vl (λ n → act-mono (p n))
act-mono (vli n p) = vli n (act-mono p)
act-mono (vo p) = vo (λ q → act-mono (p q))
act-mono (vor p) = vor (λ c → act-mono (p c))

inflate : ∀ {a b} → VRel a b → VRel a (Old.act b)
inflate vz = vz
inflate {b = hs b} (vs p) = vli 1 (add-rel (inflate p) (positive b))
inflate (vr p) = vli 0 (inflate p)
inflate (vl p) = vl (λ n → inflate (p n))
inflate (vli n p) = vli n (inflate p)
inflate (vo p) = vo (λ q → inflate (p q))
inflate (vor p) = vor (λ c → inflate (p c))

old-coordinate-self : ∀ n → VRel (Old.Pure.ce n) (Old.Pure.ce n)
old-coordinate-self zero = floor-self
old-coordinate-self (suc n) =
  add-rel (old-coordinate-self n) (act-mono (old-coordinate-self n))

old-coordinate-output-lower : ∀ n {u v} → u ≤ᵛ v →
  T.fold u (Old.Pure.ce n) ≤ᵛ T.fold v (Old.act (Old.Pure.ce n))
old-coordinate-output-lower n uv = eval (inflate (old-coordinate-self n)) uv
```

最后两条针对真实旧地板的整条轨道，说明证书不止适用于空树或常值
分支。它们尚未将旧轨道与新规范族配对；该覆盖须另给值关系证据。
