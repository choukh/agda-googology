# 实际访问路径给完整运行的值包含

Ω只调用已证原采样部分和包含；跨层只调用Coded完整反馈模拟。
左前缀使用原run自身已证的目标第一位置，未用高层源位置的单调性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaVisitRun where
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤s; ≤l; l≤)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (prefix-position)
import OCF.Lean.GeneralOmegaEmbedRun as C
import OCF.Lean.GeneralOmegaSampleRun as S
open import OCF.Lean.GeneralOmegaVisitIf

first-value : ∀ {a b : Cd} → a ⊲ b → a ≤ᵛ b
first-value hself = ≤-refl _
first-value (hsuc p) = ≤s (first-value p)
first-value (hlim n p) = ≤l n (first-value p)
first-value (hLim {κ = ()} e p)

sound : ∀ {a b} → Visit a b → value a ≤ᵛ value b
sound (here a) = ≤-refl _
sound (successor p) = ≤-trans (sound p) (≤l 0 (≤-refl _))
sound (natural n p) = ≤l n (sound p)
sound (sampled {x} {κ} {f} n p) = ≤-trans (sound p) (S.Node.sample-value x κ f n)
sound (prefix {x} {a} b p) = ≤-trans (sound p) (first-value (prefix-position x a b))
sound (embedded r p) = ≤-trans (sound p) (same-value (C.sound r))
sound (composed p q) = ≤-trans (sound p) (sound q)
sound (all-natural p) = l≤ (λ n → sound (p n))

below : ∀ {a b} {c : Cd} → c ≤ᵛ value a → Visit a b → c ≤ᵛ value b
below p q = ≤-trans p (sound q)
```

所有结论比较完整输出值。Visit没有证明每个合法源前驱可访问；前轮
NegUnvisited正说明不能加这种规则。用于γ验收时仍要构造真实路径，
并给参照到路径起点的值界，接口本身不填这个核心义务。
