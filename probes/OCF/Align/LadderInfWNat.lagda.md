> **机械克隆, 验收用.** 由 `LadderInfNat` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 实例 ℕ

> **判决: HOLDS (实例闭合).** 结论写在 [LadderInf](LadderInf.lagda.md). 高度结构的字段在 ℕ 上全部成立, 没有假设. `view`: $0$ 是根层, $n+1$ 是闭包. 这就是 [LadderNFTree](LadderNFTree.lagda.md) 的 `Ω̇` 的第 0 行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInfWNat where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.LadderInfBase
open import OCF.Align.LadderNFWTree using (_<ᴸ_; zero; suc; tr<; dn; z<s; s<s)
import OCF.Align.LadderNFWTree as NF

irrℕ : ∀ {m} → m <ᴸ m → ⊥
irrℕ {suc m} q = irrℕ (dn q)

triℕ : ∀ a b → Tri _<ᴸ_ a b
triℕ a b with NF.tri a b
... | NF.tlt p = tlt p
... | NF.teq e = teq e
... | NF.tgt p = tgt p

botℕ : ∀ i → (0 ≡ i) ⊎ (0 <ᴸ i)
botℕ zero = inj₁ refl
botℕ (suc i) = inj₂ (z<s i)

recℕ : ∀ {ℓ : Level} (X : ℕ → Set ℓ) (F : ∀ m → (∀ {n} → n <ᴸ m → X n) → X m) → ∀ m {n} → n <ᴸ m → X n
recℕ X F (suc m) zero    = F m (recℕ X F m)
recℕ X F (suc m) (suc q) = recℕ X F m q

recℕ-β : ∀ {ℓ : Level} (X : ℕ → Set ℓ) (F : ∀ m → (∀ {n} → n <ᴸ m → X n) → X m) → ∀ m {n} (q : n <ᴸ m) → recℕ X F m q ≡ F n (recℕ X F n)
recℕ-β X F (suc m) zero    = refl
recℕ-β X F (suc m) (suc q) = recℕ-β X F m q

viewℕ : ∀ m → View _<ᴸ_ 0 m
viewℕ zero    = base
viewℕ (suc m) = clos zero

assocℕ : ∀ {a b c d} (x : a <ᴸ b) (y : b <ᴸ c) (z : c <ᴸ d) → tr< (tr< x y) z ≡ tr< x (tr< y z)
assocℕ x y zero    = refl
assocℕ x y (suc z) = cong suc (assocℕ x y z)

stepℕ : ∀ {m F} {qs : ∀ i → F i <ᴸ m} → viewℕ m ≡ chain F qs → ∀ i → Σ (F i <ᴸ F (suc i)) λ r → (viewℕ (F (suc i)) ≡ clos r) × (qs i ≡ tr< r (qs (suc i)))
stepℕ {m = zero} ()
stepℕ {m = suc m} ()

HSℕ : HtS
HSℕ = record
  { Ht = ℕ
  ; _<ᴸ_ = _<ᴸ_
  ; h₀ = 0
  ; tr< = tr<
  ; irr = irrℕ
  ; no< = λ ()
  ; bot = botℕ
  ; tri = triℕ
  ; Rec = recℕ
  ; Rec-β = recℕ-β
  ; view = viewℕ
  ; tr-assoc = assocℕ
  ; view-step = stepℕ
  }
```
