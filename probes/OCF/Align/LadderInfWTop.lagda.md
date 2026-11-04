> **机械克隆, 验收用.** 由 `LadderInfTop` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 实例 ℕ∪{∞}

> **判决: HOLDS (实例闭合).** 结论写在 [LadderInf](LadderInf.lagda.md). 高度是 ℕ 加一个顶 ∞, 没有 ∞ 以上的高度, 所以 ∞ 不作节点的高度. `view ∞`: 链, 第 $i+1$ 项是 $\iota_{\downarrow\infty}(\dot\Omega_i\,0)$. 字段全部成立, 没有假设.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInfWTop where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.LadderInfBase
open import OCF.Align.LadderNFWTree using (_<ᴸ_; zero; suc; dn; z<s; s<s) renaming (tr< to trℕ)
import OCF.Align.LadderNFWTree as NF

data H : Set where
  fin : ℕ → H
  ∞   : H

infix 4 _<∞_
data _<∞_ : H → H → Set where
  fin : ∀ {n m} → n <ᴸ m → fin n <∞ fin m
  inf : ∀ n → fin n <∞ ∞

tr∞ : ∀ {a b c} → a <∞ b → b <∞ c → a <∞ c
tr∞ (fin x) (fin y) = fin (trℕ x y)
tr∞ (fin {n} x) (inf _) = inf n

irrℕ : ∀ {m} → m <ᴸ m → ⊥
irrℕ {suc m} q = irrℕ (dn q)

irr∞ : ∀ {m} → m <∞ m → ⊥
irr∞ (fin q) = irrℕ q

tri∞ : ∀ a b → Tri _<∞_ a b
tri∞ (fin a) (fin b) with NF.tri a b
... | NF.tlt p = tlt (fin p)
... | NF.teq refl = teq refl
... | NF.tgt p = tgt (fin p)
tri∞ (fin a) ∞ = tlt (inf a)
tri∞ ∞ (fin b) = tgt (inf b)
tri∞ ∞ ∞ = teq refl

bot∞ : ∀ i → (fin 0 ≡ i) ⊎ (fin 0 <∞ i)
bot∞ (fin zero) = inj₁ refl
bot∞ (fin (suc i)) = inj₂ (fin (z<s i))
bot∞ ∞ = inj₂ (inf 0)

-- 有限部分的递归是结构的
recF : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <∞ m → X n) → X m) → ∀ m {n} → n <∞ fin m → X n
recF X F (suc m) (fin zero)    = F (fin m) (recF X F m)
recF X F (suc m) (fin (suc q)) = recF X F m (fin q)

rec∞ : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <∞ m → X n) → X m) → ∀ m {n} → n <∞ m → X n
rec∞ X F (fin m) q = recF X F m q
rec∞ X F ∞ (inf n) = F (fin n) (recF X F n)

recF-β : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <∞ m → X n) → X m) → ∀ m {n} (q : n <∞ fin m) → recF X F m q ≡ F n (rec∞ X F n)
recF-β X F (suc m) (fin zero)    = refl
recF-β X F (suc m) (fin (suc q)) = recF-β X F m (fin q)

rec∞-β : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <∞ m → X n) → X m) → ∀ m {n} (q : n <∞ m) → rec∞ X F m q ≡ F n (rec∞ X F n)
rec∞-β X F (fin m) q = recF-β X F m q
rec∞-β X F ∞ (inf n) = refl

view∞ : ∀ m → View _<∞_ (fin 0) m
view∞ (fin zero)    = base
view∞ (fin (suc m)) = clos (fin zero)
view∞ ∞             = chain fin inf

assocℕ : ∀ {a b c d} (x : a <ᴸ b) (y : b <ᴸ c) (z : c <ᴸ d) → trℕ (trℕ x y) z ≡ trℕ x (trℕ y z)
assocℕ x y zero    = refl
assocℕ x y (suc z) = cong suc (assocℕ x y z)

assoc∞ : ∀ {a b c d} (x : a <∞ b) (y : b <∞ c) (z : c <∞ d) → tr∞ (tr∞ x y) z ≡ tr∞ x (tr∞ y z)
assoc∞ (fin x) (fin y) (fin z) = cong fin (assocℕ x y z)
assoc∞ (fin x) (fin y) (inf _) = refl

step∞ : ∀ {m F} {qs : ∀ i → F i <∞ m} → view∞ m ≡ chain F qs → ∀ i →
        Σ (F i <∞ F (suc i)) λ r → (view∞ (F (suc i)) ≡ clos r) × (qs i ≡ tr∞ r (qs (suc i)))
step∞ {m = fin zero} ()
step∞ {m = fin (suc m)} ()
step∞ {m = ∞} refl i = fin zero , refl , refl

HS∞ : HtS
HS∞ = record
  { Ht = H
  ; _<ᴸ_ = _<∞_
  ; h₀ = fin 0
  ; tr< = tr∞
  ; irr = irr∞
  ; no< = λ { (fin ()) }
  ; bot = bot∞
  ; tri = tri∞
  ; Rec = rec∞
  ; Rec-β = rec∞-β
  ; view = view∞
  ; tr-assoc = assoc∞
  ; view-step = step∞
  }
```
