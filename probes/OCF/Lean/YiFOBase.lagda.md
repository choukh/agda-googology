# 规范首链点与继承底中的缺格
验收文件，不读记号；编译目标是第 2、3 站实际首链点、其根槽位及继承底调用中的空格。
链与底照 YiFRStep/YiGIInst 的树侧表达式；feed 在出生处封装。源表、折叠、合法性均沿用原定义。
`not-full-base` 的域只含这些规范链点上的继承底调用；不等同于完整闭项的 FullTw，未判定是否丢值。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFOBase where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
import OCF.Lean.YiCWTable as CW
import OCF.Lean.YiMTHit as H
open import OCF.Lean.YiFOTrace using (Domain; FullOn)

FΛ : ℕ → Tr Λ
FΛ n = proj₁ (upz {s = sL} {h = tw} n (Ωt (tw n)))
pre : ℕ → Tr Λ
pre zero = zero
pre (suc n) = cum FΛ n
base : (n : ℕ) → Base (tw n)
base n i u = ψ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) i (inc n u) (Ωt i) (pre n)
module Run (n : ℕ) where
  k = tw n
  ℓ = tw (suc n)
  child : Tr k → L
  child c = k ⊕ ↑ k c
  g : Tr k → Tr ℓ
  g c = proj₁ (upz {s = sΩ k} {h = child} c (Ωt (child c)))
  opaque
    feed : Tr k → Tr k
    feed c = proj₁ (ψ ℓ (Ok-tw (suc n)) (rbᶻ ℓ) (base (suc n)) k (ink self)
      (base (suc n) k (ink self)) (g c))
    feed-eq : ∀ c → feed c ≡ proj₁ (ψ ℓ (Ok-tw (suc n)) (rbᶻ ℓ) (base (suc n)) k (ink self)
      (base (suc n) k (ink self)) (g c))
    feed-eq c = refl
    feed-positive : ∀ c → k ⊢ zero ◃ feed c
    feed-positive c = proj₂ (ψ ℓ (Ok-tw (suc n)) (rbᶻ ℓ) (base (suc n)) k (ink self)
      (base (suc n) k (ink self)) (g c))
  chain : ℕ → Tr k
  chain = iter feed zero
  chain-positive : ∀ q → k ⊢ zero ◃ chain (suc q)
  chain-positive q = feed-positive (chain q)

Missing : H.Site
Missing k h j c′ c m = m ≡ nothing
opaque
  unfolding Run.feed
  miss2 : proj₁ (rbᶻ (tw 2)) zero (Run.chain 1 1) ≡ nothing
  miss2 = refl
  miss3 : proj₁ (rbᶻ (tw 3)) zero (Run.chain 2 1) ≡ nothing
  miss3 = refl
  slot2 : Pos (Run.child 1 (Run.chain 1 1))
  slot2 = inj₁ (inj₁ tt)
  slot3 : Pos (Run.child 2 (Run.chain 2 1))
  slot3 = inj₁ (inj₁ tt)

BaseHit : H.Site → (n : ℕ) (c′ : Tr (tw n)) (i : L) → i ≤ Run.child n c′ → Set
BaseHit P n c′ i u = H.Hit P Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) (λ _ _ → ⊥)
  i (inc (suc n) (inc c′ u)) (Ωt i) ⊥ (pre (suc n))
base-miss2 : ∀ i u → BaseHit Missing 1 (Run.chain 1 1) i u
base-miss2 i u = miss2
base-miss3 : ∀ i u → BaseHit Missing 2 (Run.chain 2 1) i u
base-miss3 i u = miss3
root-base-miss2 : BaseHit Missing 1 (Run.chain 1 1)
  (at (Run.child 1 (Run.chain 1 1)) slot2) (posW (Run.child 1 (Run.chain 1 1)) slot2)
root-base-miss2 = base-miss2 (at (Run.child 1 (Run.chain 1 1)) slot2) (posW (Run.child 1 (Run.chain 1 1)) slot2)
root-base-miss3 : BaseHit Missing 2 (Run.chain 2 1)
  (at (Run.child 2 (Run.chain 2 1)) slot3) (posW (Run.child 2 (Run.chain 2 1)) slot3)
root-base-miss3 = base-miss3 (at (Run.child 2 (Run.chain 2 1)) slot3) (posW (Run.child 2 (Run.chain 2 1)) slot3)

BaseDomain : Domain
BaseDomain P = Σ ℕ λ n → Σ ℕ λ q → Σ L λ i →
  Σ (i ≤ Run.child n (Run.chain n q)) λ u → BaseHit P n (Run.chain n q) i u

not-full-base : FullOn BaseDomain → ⊥
not-full-base f = f (1 , 1 , at (Run.child 1 (Run.chain 1 1)) slot2 ,
  posW (Run.child 1 (Run.chain 1 1)) slot2 , root-base-miss2)
```
