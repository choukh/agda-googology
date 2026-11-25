# 槽位链重建与原归约的对接
验收文件；编译定理：底、起点、回灌点与第 0 层输出逐字等于 `YiGIInst`、`YiFRStep` 的实际对象。
只核对重建对象，未给出相邻链点的值增长、`Tail` 或 `FirstMissing`。
树侧文件为 `YiSLStart`，不改主线定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSLCheck where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock using (Tr; tw)
open import OCF.Lean.YiRWPath using (_≤_)
import OCF.Lean.YiSLStart as S
import OCF.Lean.YiGIInst as G
import OCF.Lean.YiFRStep as F

base-eq : ∀ n i (u : i ≤ tw n) → S.baseᴱ n i u ≡ G.baseᴱ n i u
base-eq zero i u = refl
base-eq (suc n) i u = refl

beta-eq : ∀ n → S.betaᴱ n ≡ G.betaᴱ n
beta-eq zero = refl
beta-eq (suc n) = refl

feed-eq : (n : ℕ) (c : Tr (tw n)) → S.Step.feed n c ≡ F.Step.feed n c
feed-eq n c = refl

chain-eq : (n q : ℕ) → S.Step.chain n q ≡ F.Step.chain n q
chain-eq n q = refl

out-eq : (n q : ℕ) → S.Step.out n (S.Step.chain n q) ≡ F.Step.out n (F.Step.chain n q)
out-eq n q = refl
```
