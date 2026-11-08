# 原Γ实际生成域的树侧正则性接口

本接口不改变原Γ。Reg只描述树的遗传形状与极限值步进；它不替代
原LgB的字面第一位置合法性。只要求实际输出域满足Reg，不声称
所有布劳威尔树都满足它，故不能把严格View强加给全部对象。

Built直接读取原目标0观察器的三种输出规则：1、从0份起的重复列、
正输出的逐点极限。它不是记号语法，不进入原闭项的定义或合法证书。
后续必须证明实际observe落在此域，而不只是假定一个生成谓词。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularIf where
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.GeneralOmegaCountableObserveIf using (leftMul)
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ; stage)
open import OCF.Lean.GeneralOmegaCountableGammaOrderIf using (empty-limit)

Reg : Cd → Set
Reg hz = ⊤
Reg (hs a) = Reg a
Reg (hl f) = (∀ n → hs (f n) ≤ᵛ f (Data.Nat.suc n)) × (∀ n → Reg (f n))
Reg (hΩ () f)

data Built : Cd → Set where
  one : Built (hs hz)
  repeat : ∀ {a} → Built a → Built (hl (leftMul a))
  limit : ∀ {f} → (∀ n → Built (f n)) → Built (hl f)

record RegularConstruction : Set₁ where
  field
    built-observe : ∀ B lB pt a → Built (observe B lB hz pt a)
    complete-built : ∀ {a} → Built a → Reg (leg a)
    regular-Γ : ∀ c → Reg (Γ c)
    regular-stage : ∀ n → Reg (stage n)
    regular-height : ∀ n → Reg (leg (stage n))

-- 值律的输入对继续携带同一字面合法公共上界。
record RestrictedValueMonotone : Set where
  field
    monotone : ∀ {B a b : Cd} → LgB B → LgB a → LgB b →
      Reg a → Reg b → a ⊲ B → b ⊲ B → a ≤ᵛ b → Γ a ≤ᵛ Γ b

reg-zero : Reg hz
reg-zero = tt
reg-one : Reg (hs hz)
reg-one = tt
empty-not-regular : Reg empty-limit → ⊥
empty-not-regular r = ¬s≤ᵛ hz (proj₁ r 0)
```

Reg有实际零/后继实例，并确实排除旧零值空极限反例。排除这个
反例不说明RestrictedValueMonotone成立；此字段必须另行构造或
否定。RegularConstruction也须完整实例化原Γ及其全部实际阶段。
