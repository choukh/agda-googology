# 比较表: 与观察原则对照, 以及不能有的两种表

> 判决: 编译定理, 无前提, 不读记号. (1) 表的 "有没有条目" 不是 `YiAbsObs.Sep` 的观察: 指定孩子 `nat 2` 之外的孩子 `nat 3` 处也有条目 (`off-fails`), 所以 `branch→wdec`, `sep→wdec` 的 "别的孩子处为假" 这条前提在表上不成立. (2) 条目恰在对角线上的表弱判定孩子的字面相等 (`exact→wdec`, `sep→wdec` 的实例). (3) 不带 `Maybe` 的全表在塔第 1 项上不存在 (`no-total`): `ωᶜ` 与 `ωᵉ` 的层号之间两个方向都没有字面路径.
> 范围: (1) 说的是表这个数据, 不是折叠输出的头部; 折叠输出头部上的 `branch→wdec` 前提没有在这个块上陈述. 表的类型里没有孩子相等的证据, `viaE→dec` 的证据函数 `Maybe (c ≡ c′)` 不是它的实例 (读类型, 判断).
> 不否定什么: 可缺的表 `rb1`, `rbᶜ`, `rbᴴ` 都是闭项.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTBObs where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiTBRow
open import OCF.Lean.YiTBTab using (ωᶜ; ωᵉ; dbl)
open import OCF.Lean.YiAbsObs using (Sep; WDec; sep→wdec)
```

## 表的有无不是分离孩子的观察

```agda
isJ : {A : Set} → Maybe A → Bool
isJ (just _) = true
isJ nothing  = false

on-2 : isJ (tb (nat 2) (nat 2)) ≡ true
on-2 = refl

3≢2 : nat 2 ≡ nat 3 → ⊥
3≢2 ()

off-fails : ((c : Tr zero) → (nat 2 ≡ c → ⊥) → isJ (tb c (nat 2)) ≡ false) → ⊥
off-fails off with off (nat 3) 3≢2
... | ()
```

## 条目恰在对角线上的表弱判等

对任意下标类型与任意条目类型陈述; 前提在 `Tr zero` 上是否可满足没有证 (没有实例).

```agda
exact→wdec : {C : Set} {A : C → C → Set} (t : (c c′ : C) → Maybe (A c c′)) (c₀ : C)
  → isJ (t c₀ c₀) ≡ true → ((c : C) → (c₀ ≡ c → ⊥) → isJ (t c c₀) ≡ false)
  → (c : C) → WDec (c₀ ≡ c)
exact→wdec t c₀ on off = sep→wdec (record { f = λ c → isJ (t c c₀) ; on = on ; off = off })
```

## 全表不存在

`d`: 沿后继形状的孩子与 ℕ 极限形状的孩子 1 数层数. `noL`: ℕ 极限形状的层号没有通到有限后继链层号的路径.

```agda
d : L → ℕ
d zero            = 0
d (nd sS g)       = suc (d (g tt))
d (nd sL g)       = d (g 1)
d (nd (sΩ _) _)   = 0

NoLim : Tr zero → Set
NoLim zero      = ⊤
NoLim (suc x)   = NoLim x
NoLim (lim _ _) = ⊥

noL : ∀ {b g} (x : Tr zero) → NoLim x → Pth b (nd sL g) (h₁ x) → ⊥
noL zero      nl ()
noL (suc x)   nl (inc tt v) = noL x nl v
noL (suc x)   nl (inu vs)   = noL x nl (vs tt)
noL (lim f a) ()

module _ (fA fB : ℕ → Tr zero) (nlB : ∀ n → NoLim (fB n)) (ne : d (h₁ (fA 1)) ≡ d (h₁ (fB 1)) → ⊥) where
  noP : ∀ {b j ℓ} → Pth b j ℓ → j ≡ nd sL (λ n → h₁ (fA n)) → ℓ ≡ nd sL (λ n → h₁ (fB n)) → ⊥
  noP self      e₁   e₂   = ne (cong d {x = nd sL (λ n → h₁ (fA n))} {y = nd sL (λ n → h₁ (fB n))} (trans (sym e₁) e₂))
  noP (inc c v) refl refl = noL (fB c) (nlB c) v
  noP (inu vs)  refl refl = noL (fB 0) (nlB 0) (vs 0)
  noP (ink v)   e₁   ()

nlN : ∀ n → NoLim (nat n)
nlN zero    = tt
nlN (suc n) = nlN n

nlD : ∀ n → NoLim (dbl n)
nlD zero    = tt
nlD (suc n) = nlD n

1≢2 : _≡_ {A = ℕ} 1 2 → ⊥
1≢2 ()

2≢1 : _≡_ {A = ℕ} 2 1 → ⊥
2≢1 ()

no-ωᵉ≤ω : h₁ ωᵉ ≤ h₁ ωᶜ → ⊥
no-ωᵉ≤ω p = noP dbl nat nlN 2≢1 p refl refl

no-ω≤ωᵉ : h₁ ωᶜ ≤ h₁ ωᵉ → ⊥
no-ω≤ωᵉ p = noP nat dbl nlD 1≢2 p refl refl

no-total : ((c c′ : Tr zero) → (h₁ c′ ≤ h₁ c) ⊎ (h₁ c ≤ h₁ c′)) → ⊥
no-total t with t ωᶜ ωᵉ
... | inj₁ p = no-ωᵉ≤ω p
... | inj₂ p = no-ω≤ωᵉ p
```
