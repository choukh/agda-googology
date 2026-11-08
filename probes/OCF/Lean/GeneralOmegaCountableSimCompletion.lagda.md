# 可数树有向结构模拟的完成闭包

这里比较的是Cd对象的结构，不判定裸下标，也不把Sim送过Γ。
原Sim没有任意ℕ左消去，因而可以逐构造运输完成：右选分量通过
原部分和中的右项吸收。结论给高度比较提供有证输入，但不自动
提供两棵完成高度的字面公共上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableSimCompletion where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf
open import OCF.Lean.GeneralOmegaCountableRegularCompareClosure using (add; right-add)

record CompletionSimulation : Set₁ where
  field
    lift-completion : ∀ {a b} → Sim hz a b → Sim hz (leg a) (leg b)
    from-position : ∀ {a b : Cd} → a ⊲ b → Sim hz (leg a) (leg b)
    inflation : ∀ a → Sim hz a (leg a)

self : ∀ (a : Cd) → Sim hz a a
self hz = sz
self (hs a) = ss (self a)
self (hl f) = sl (λ n → self (f n))
self (hΩ () f)

item : ∀ f n {a} → Sim hz a (f n) → Sim hz a (Σ₀ f n)
item f zero p = p
item f (suc n) p = right-add p (Σ₀ f n)
sums : ∀ f g → (∀ n → Sim hz (f n) (g n)) → ∀ n → Sim hz (Σ₀ f n) (Σ₀ g n)
sums f g p zero = p zero
sums f g p (suc n) = add (sums f g p n) (p (suc n))

lift-completion : ∀ {a b} → Sim hz a b → Sim hz (leg a) (leg b)
lift-completion sz = sz
lift-completion (ss p) = ss (lift-completion p)
lift-completion (sr p) = sr (lift-completion p)
lift-completion (sl {f} {g} p) = sl (sums (λ n → leg (f n)) (λ n → leg (g n))
  (λ n → lift-completion (p n)))
lift-completion (sli {f = f} n p) = sli n (item (λ k → leg (f k)) n (lift-completion p))
lift-completion (so {κ = ()} p)
lift-completion (sor {κ = ()} p)

position-sim : ∀ {a b : Cd} → a ⊲ b → Sim hz a b
position-sim {a} hself = self a
position-sim (hsuc p) = sr (position-sim p)
position-sim (hlim n p) = sli n (position-sim p)
position-sim (hLim {κ = ()} e p)
from-position : ∀ {a b : Cd} → a ⊲ b → Sim hz (leg a) (leg b)
from-position p = lift-completion (position-sim p)

inflation : ∀ a → Sim hz a (leg a)
inflation hz = sz
inflation (hs a) = ss (inflation a)
inflation (hl f) = sl (λ n → item (λ k → leg (f k)) n (inflation (f n)))
inflation (hΩ () f)

instance-completion : CompletionSimulation
instance-completion = record
  { lift-completion = lift-completion
  ; from-position = from-position
  ; inflation = inflation }
```

全部字段有实际实例，零、后继和任意ℕ树都由上面的结构递归覆盖。
from-position只交Sim证据，不声称leg a⊲leg b；它也不把不同源高度
的kind或低层坐标识别为相同，后者仍是异层观察比较的独立义务。
