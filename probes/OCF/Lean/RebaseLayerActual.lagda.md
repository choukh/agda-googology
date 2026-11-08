# 全有限原地板与实际生成族的采样自证

不要求任意raw输入自证；实例逐字采用已有floor与原act。
最低层双向连接旧Value，因而可交原terminal运行器消费。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerActual where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.RebaseLayerIf
open import OCF.Lean.RebaseLayerClosure
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
import OCF.Align.BoundedCompletionUniformIf as Old
import OCF.Align.BoundedCompletionUniformClosure as OldC
import OCF.Align.BoundedCompletionTerminalValueRun as Terminal
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Lean.RebaseCountableClosed as D

pure-up : ∀ {a b} → a ≤ᵛ b → Value hz (up a) (up b)
pure-up z≤ = vz
pure-up (s≤s p) = vs (pure-up p)
pure-up (≤s p) = vr (pure-up p)
pure-up (l≤ p) = vl (λ n → pure-up (p n))
pure-up (≤l n p) = vli n (pure-up p)
up-value : ∀ c {a b} → Value c a b → Value (hs c) (up a) (up b)
up-value c vz = vz
up-value c (vs p) = vs (up-value c p)
up-value c (vr p) = vr (up-value c p)
up-value c (vl p) = vl (λ n → up-value c (p n))
up-value c (vli n p) = vli n (up-value c p)
up-value c (vo p) = vo (λ x y xy → up-value c (p x y xy))
up-value c (vor p) = vor (λ e se → up-value c (p e se))
floor-self : ∀ n → Value (num n) (floor n) (floor n)
floor-self zero = vo (λ x y xy → pure-up xy)
floor-self (suc n) = vo (λ x y xy → up-value (num n) (proj₁ xy))

whole-self : ∀ n → Value (num 1) (Whole.Model.ce n) (Whole.Model.ce n)
whole-self zero = floor-self 1
whole-self (suc n) = add (whole-self n) (act-mono (whole-self n))
D-self : ∀ n → Value (num 1) (D.levels n) (D.levels n)
D-self zero = floor-self 1
D-self (suc n) = add (D-self n) (act-mono (D-self n))

zero-to-old : ∀ {a b} → Value hz a b → Old.Value hz a b
zero-to-old vz = Old.vz
zero-to-old (vs p) = Old.vs (zero-to-old p)
zero-to-old (vr p) = Old.vr (zero-to-old p)
zero-to-old (vl p) = Old.vl (λ n → zero-to-old (p n))
zero-to-old (vli n p) = Old.vli n (zero-to-old p)
zero-to-old (vo {κ = inj₁ ()} p)
zero-to-old (vo {κ = inj₂ _} p) = Old.vo (λ x y xy → zero-to-old (p x y xy))
zero-to-old (vor {κ = inj₁ ()} p)
zero-to-old (vor {κ = inj₂ _} p) = Old.vor (λ e → zero-to-old (p e tt))
old-to-zero : ∀ {a b} → Old.Value hz a b → Value hz a b
old-to-zero Old.vz = vz
old-to-zero (Old.vs p) = vs (old-to-zero p)
old-to-zero (Old.vr p) = vr (old-to-zero p)
old-to-zero (Old.vl p) = vl (λ n → old-to-zero (p n))
old-to-zero (Old.vli n p) = vli n (old-to-zero p)
old-to-zero (Old.vo {κ = inj₁ ()} p)
old-to-zero (Old.vo {κ = inj₂ _} p) = vo (λ x y xy → old-to-zero (p x y xy))
old-to-zero (Old.vor {κ = inj₁ ()} p)
old-to-zero (Old.vor {κ = inj₂ _} p) = vor (λ e se → old-to-zero (p e))

terminal : ∀ {a b x y} → Value hz a b → x ≤ᵛ y → T.fold x a ≤ᵛ T.fold y b
terminal p xy = Terminal.eval (OldC.value-zero (zero-to-old p)) xy
```

整Whole/D输入族已满足新关系自证，但高层at保持新关系还未证明。
最低层terminal定理不填补该缺口；高层仍必须联立证明采样坐标自证。
