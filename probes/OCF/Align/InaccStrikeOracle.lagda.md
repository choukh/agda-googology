# 降维打击的检验: 由树读出范数的总判决 `D★` (不含记号)

> 只看层号的总函数. `nrm` 从层号的前两个基本列项读出一个上界, 代替 `ver` 的固定采样 16; `toT` 把层号 `j` 读成第 `k` 层的树, 代替 `reify`. 它是候选, 而且**已被反驳**: 验收 [InaccStrikeAccept](InaccStrikeAccept.lagda.md) 的 `★-wrong-OO` 在标准形上给出错误判决. 保留它是为了记录这条路线试到哪里. 结论在 [InaccStrike](InaccStrike.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccStrikeOracle where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.InaccTreeBase

natL : ℕ → Lv
natL zero    = zero
natL (suc n) = suc (natL n)

natT′ : ∀ {k} → ℕ → Ordᴸ k
natT′ zero    = zero
natT′ (suc n) = suc (natT′ n)

nrm : Lv → ℕ
nrm zero       = 0
nrm (suc a)    = suc (nrm a)
nrm (lim f)    = suc (nrm (f 0) ⊔ nrm (f 1))
nrm (limᴼ k g) = suc (nrm k ⊔ nrm (g zero) ⊔ nrm (g (suc zero)))

andAll : ℕ → (ℕ → Bool) → Bool
andAll zero    t = true
andAll (suc m) t = t m ∧ andAll m t

sameᵈ : ℕ → Lv → Lv → Bool
sameᵈ d zero       zero         = true
sameᵈ d (suc a)    (suc b)      = sameᵈ d a b
sameᵈ d (lim f)    (lim h)      = andAll d (λ n → sameᵈ d (f n) (h n))
sameᵈ d (limᴼ k g) (limᴼ k′ g′) = sameᵈ d k k′ ∧ andAll d (λ n → sameᵈ d (g (natT′ n)) (g′ (natT′ n)))
sameᵈ d _          _            = false

same★ : Lv → Lv → Bool
same★ j i = sameᵈ (suc (suc (nrm j ⊔ nrm i))) j i

D★      : Oracle
toT     : ∀ k → Lv → Ordᴸ k
search★ : ℕ → ∀ j (h : ℕ → Lv) → Verdict j (lim h)
goS     : ∀ m j (h : ℕ → Lv) → Verdict j (h m) → Verdict j (lim h)
toTv    : ∀ k k′ (g : Ordᴸ k′ → Lv) → Verdict k′ k → Ordᴸ k
sucV    : ∀ j i → Bool → Verdict j (suc i)
sucW    : ∀ j i → Verdict j i → Verdict j (suc i)
omV     : ∀ j k (g : Ordᴸ k → Lv) → Bool → Verdict j (limᴼ k g)
omW     : ∀ j k (g : Ordᴸ k → Lv) → Verdict j k → Verdict j (limᴼ k g)
omX     : ∀ j k (g : Ordᴸ k → Lv) (x : Ordᴸ k) → Verdict j (g x) → Verdict j (limᴼ k g)

D★ j zero       = rise
D★ j (suc i)    = sucV j i (same★ j i)
D★ j (lim h)    = search★ (suc (suc (nrm j))) j h
D★ j (limᴼ k g) = omV j k g (same★ j k)

sucV j i true  = pen (inj₁ tt) (cast i j)
sucV j i false = sucW j i (D★ j i)
sucW j i (pen r b) = pen (inj₂ r) b
sucW j i rise      = rise

omV j k g true  = pen (inj₁ (inj₁ tt)) (cast k j)
omV j k g false = omW j k g (D★ j k)
omW j k g (pen r b) = pen (inj₁ (inj₂ r)) b
omW j k g rise      = omX j k g (suc (toT k j)) (D★ j (g (suc (toT k j))))
omX j k g x (pen r b) = pen (inj₂ (x , r)) b
omX j k g x rise      = rise

search★ zero    j h = rise
search★ (suc m) j h = goS m j h (D★ j (h m))
goS zero    j h (pen r b) = pen (zero , r) b
goS (suc m) j h (pen r b) = pen (suc m , r) b
goS zero    j h rise = rise
goS (suc m) j h rise = goS m j h (D★ j (h m))

toT k zero         = zero
toT k (suc a)      = suc (toT k a)
toT k (lim f)      = lim (λ n → toT k (f n))
toT k (limᴼ k′ g)  = toTv k k′ g (D★ k′ k)

toTv k k′ g (pen r b) = limᵢ r (λ y → toT k (g (b (outL k r y))))
toTv k k′ g rise      = lim (λ n → toT k k′ + toT k (g (natT′ n)))
```

## 否定: `D★` 只可能在 "基本列规整" 的层号上正确

`pad m` 先走 `m` 步 0 再走 ω: 它单调, 结构上严格高于每个有限数, 但 `nrm j` 不是它的模. 所以模不是层号自身的性质, 是层号类的性质: 全部 `Lv` 上由树读出的模不存在, 只能对某个规整类成立.

```agda
pad : ℕ → ℕ → Lv
pad zero    n       = natL n
pad (suc m) zero    = zero
pad (suc m) (suc n) = pad m n

D★-pad : D★ (natL 1) (lim (pad 10)) ≡ rise
D★-pad = refl

_ : natL 1 ≺ lim (pad 10)
_ = via (12 , inj₁ tt) (≅-refl _)
```
