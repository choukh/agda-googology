# YiXV：实际层号 2 折到层号 1
> 验收文件。编译定理：实际底 B2 上的 Ω 树折到第 1 层后，具有参照 ψ₁(Ω₂) 的模拟上界及字面起点证据。
> 复用 YiXVChain2.bounds、YiXVPlus 的加法闭包，逐项控制原回灌链的部分和；没有全体 pre 或外层链的上界。
> δ 是该实际非零目标折叠的输出；所有前提已由冻结模块实填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSlot2 where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiXVStart using (B2)
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVCarry as K
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVPlus as P
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVTwo as W
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
open import OCF.Lean.YiOverTwo using (Gd-γ; Inv-γ)
import OCF.Align.Level as L

module C = W.C
module A = S.Sim I.D1
module HC = H.Anchor I.D1
module PC = P.Closure I.D1

δ : Tr (suc zero)
δ = ψs (suc (suc zero)) tt tt B2 (suc zero) (ins self) K.γ₁
  (ns B2 (suc zero) (ins self)) (Ωt (suc (suc zero)))

rows : ℕ → Tr (suc zero)
rows n = C.c (suc n)

k : ℕ → ℕ
k n = C.ix (suc (suc n))

step : ∀ n → C.Γ n R.≤ₚ C.Γ (suc n)
step n = O.≤ψ₁ (Gd-γ n) (Inv-γ n)

grow3 : ∀ n → C.Γ n R.≤ₚ C.Γ (suc (suc (suc n)))
grow3 n = R.trans (step n) (R.trans (step (suc n)) (step (suc (suc n))))

absorb : ∀ n → (C.Γ n L.+ C.Γ n) R.≤ₚ C.Γ (suc (suc (suc n)))
absorb n = R.trans (O.+ₚ (O.reflₚ (Gd-γ n)) (step n))
  (R.trans (O.step-γ (Gd-γ n) (Inv-γ n) (O.reflₚ (Gd-γ n))) (step (suc (suc n))))

Sums : ℕ → Set
Sums n = Σ (A.U (cum rows n) (C.Γ (k n))) HC.Closed

sums : ∀ n → Sums n
sums zero = A.uw (Gd-γ (C.ix 1)) (proj₁ (C.bounds 1)) (grow3 (C.ix 1)) , proj₂ (C.bounds 1)
sums (suc n) =
  A.uw (O.Gd-+ (Gd-γ (k n)) (Gd-γ (k n)))
    (PC.plus-comp (Gd-γ (k n)) (proj₁ (sums n)) (Gd-γ (k n)) (proj₁ (C.bounds (suc (suc n)))))
    (absorb (k n)) ,
  HC.plus-closed (Gd-γ (k n)) (proj₁ (sums n)) (proj₂ (sums n))
    (Gd-γ (k n)) (proj₁ (C.bounds (suc (suc n)))) (proj₂ (C.bounds (suc (suc n))))

upper : A.U δ (L.ψ L.zero (λ r → r) (L.Ω (L.suc (L.suc L.zero))))
upper = A.ul (λ n → A.uw (Gd-γ (k n)) (proj₁ (sums n)) (R.≤l (k n) (step (k n))))

closed : HC.Closed upper
closed n = proj₂ (sums n)
```
