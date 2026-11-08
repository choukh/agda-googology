# 同界有向结构模拟给出原位置方向

本篇是配对检验的正面结果，不是否定。H只测量原Cd构造形状：极限
外再加一层后继，因而每条非平凡第一位置在H值上严格变小。它不是
新的最终定义，不判定裸下标，也不给Γ或collapse的单调性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableHeightNegOrder where
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf
open import OCF.Lean.GeneralOmegaCountableSimCompletion using (self)
open import OCF.Lean.GeneralOmegaCountableObservePrefix using (position-value)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)

H : Cd → Cd
H hz = hz
H (hs a) = hs (H a)
H (hl f) = hs (hl (λ n → H (f n)))
H (hΩ () f)

sim-measure : ∀ {a b} → Sim hz a b → H a ≤ᵛ H b
sim-measure sz = z≤
sim-measure (ss p) = s≤s (sim-measure p)
sim-measure (sr p) = ≤s (sim-measure p)
sim-measure (sl p) = s≤s (l≤ (λ n → ≤l n (sim-measure (p n))))
sim-measure (sli n p) = ≤s (≤l n (sim-measure p))
sim-measure (so {κ = ()} p)
sim-measure (sor {κ = ()} p)

measure-position : ∀ {a b : Cd} → a ⊲ b → H a ⊲ H b
measure-position hself = hself
measure-position (hsuc p) = hsuc (measure-position p)
measure-position (hlim n p) = hsuc (hlim n (measure-position p))
measure-position (hLim {κ = ()} e p)

position-strict : ∀ {a b : Cd} → a ⊲ b → (a ≡ b) ⊎ (hs (H a) ≤ᵛ H b)
position-strict hself = inj₁ refl
position-strict (hsuc p) = inj₂ (s≤s (position-value (measure-position p)))
position-strict (hlim n p) = inj₂ (s≤s (≤l n (position-value (measure-position p))))
position-strict (hLim {κ = ()} e p)

orient : ∀ {a b : Cd} → Sim hz a b → b ⊲ a → a ⊲ b
orient {a} {b} s p with position-strict p
... | inj₁ e = subst (λ x → a ⊲ x) (sym e) hself
... | inj₂ strict = ⊥-elim (¬s≤ᵛ (H b) (≤-trans strict (sim-measure s)))

sim-to-position : ∀ {W a b : Cd} → LgB W → a ⊲ W → b ⊲ W → Sim hz a b → a ⊲ b
sim-to-position lW pa pb s with cmpB pa pb tt lW
... | inj₁ p = orient s p
... | inj₂ p = p

-- 合法非零公共界实例，及真实非有限共同界实例。
zero-to-one : hz ⊲ hs hz
zero-to-one = sim-to-position tt (hsuc hself) hself sz
omega-self : omega ⊲ omega
omega-self = sim-to-position omega-legal hself hself (self omega)
```

Sim的右极限选项只需进入H右极限的某一枝，再进入额外后继，故
sim-measure不需要任何极限左消去或原树正则性。sim-to-position保留
共同合法W的前提，只把已给方向还原为原路径。

此结果仍不等于HeightIf.capture：较小侧合法证是沿原pa从W取得，
而ObservePosition沿新a⊲b再从pb取得。它们的观察相容未在本篇证明；
也没有给两棵完成高度自动构造共同合法W。
