# 搬运在相等的层号上是结构拷贝 (互模拟)

非验收文件. 编译定理, 无前提. "值正确" 在这里指互模拟 `Sim`: 同一层上两棵树逐个构造子对应, 结点的位置与孩子的下标字面相同, 分支对互模拟的输入给出互模拟的输出 (照参照框架 `Level` 的 `lᵢ≅`, 是部分等价关系, 不要求函数外延).
`mv-sim`: 层号只含零, 后继, ℕ 极限 (`Sm`) 时, `x` 与 `y` 互模拟则 `mv a a x` 与 `y` 互模拟; `mv-subst`: 沿层号的相等 `e`, 搬运与 `subst` 互模拟. 第 0 层上互模拟自反 (`sim0`); `tw 2` 的分支层号与其位置的层号都是 `Sm` (`up0-sm`, `lev-sm`).
不否定: 一般层上 `Sim` 不自反 (分支函数未必尊重互模拟); Ω 结点层号上搬运不是拷贝.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZipSim where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev)
open import OCF.Lean.YiZipMove
```

## 1 只含零, 后继, ℕ 极限的层号; 互模拟

`SimAt a P K` 是第 `a` 层上的互模拟, 位置上的分支域与孩子层上的关系作参数 (只在负位置出现参数, 严格正); `Sim` 沿层号把参数取成低层的 `Sim`.

```agda
data Sm : LF → Set where
  z : Sm zero
  s : ∀ {k} → Sm k → Sm (suc k)
  l : ∀ {f} → (∀ n → Sm (f n)) → Sm (lim f)

module _ (a : LF) (P : (r : Pre a) → Lay.A (Lo a r) → Lay.A (Lo a r) → Set)
                  (K : (i : Kid a) → Lay.A (KS a i) → Lay.A (KS a i) → Set) where
  data SimAt : Raw a → Raw a → Set where
    z≈ : SimAt G.zero G.zero
    s≈ : ∀ {x y} → SimAt x y → SimAt (G.suc x) (G.suc y)
    l≈ : ∀ {f g} → (∀ n → SimAt (f n) (g n)) → SimAt (G.lim f) (G.lim g)
    c≈ : ∀ {r g g′} → (∀ η η′ → P r η η′ → SimAt (g η) (g′ η′)) → SimAt (G.lc r g) (G.lc r g′)
    e≈ : ∀ {i x y} → K i x y → SimAt (G.em i x) (G.em i y)
    t≈ : SimAt G.top G.top

Sim  : (a : LF) → Raw a → Raw a → Set
SimP : (a : LF) (r : Pre a) → Lay.A (Lo a r) → Lay.A (Lo a r) → Set
SimK : (a : LF) (i : Kid a) → Lay.A (KS a i) → Lay.A (KS a i) → Set

Sim a = SimAt a (SimP a) (SimK a)

SimP zero ()
SimP (suc k) (inj₁ _) = Sim k
SimP (suc k) (inj₂ r) = SimP k r
SimP (lim f) (n , r) = SimP (f n) r
SimP (lc k g) (η , _ , r) = SimP (g η) r

SimK zero ()
SimK (suc k) _ = Sim k
SimK (lim f) n = Sim (f n)
SimK (lc k g) (η , _) = Sim (g η)

sim0 : ∀ x → Sim zero x x
sim0 G.zero = z≈
sim0 (G.suc x) = s≈ (sim0 x)
sim0 (G.lim f) = l≈ (λ n → sim0 (f n))
sim0 G.top = t≈
```

## 2 搬运到自己是拷贝

`bk a r`: 位置 `r` 的分支域上的自搬运; `mvN-eq`: 同层时结点落回同一位置, 分支先经 `bk`.

```agda
bk : (a : LF) (r : Pre a) → Lay.A (Lo a r) → Lay.A (Lo a r)
bk zero ()
bk (suc k) (inj₁ _) = mv k k
bk (suc k) (inj₂ r) = bk k r
bk (lim f) (n , r) = bk (f n) r
bk (lc k g) (η , _ , r) = bk (g η) r

mvN-eq : ∀ {a} → Sm a → ∀ {M} (B : Bld M a) (r : Pre a) (h : Lay.A (Lo a r) → Raw M) →
  mvN a a B r h ≡ B r (λ η → h (bk a r η))
mvN-eq (s sk) B (inj₁ _) h = refl
mvN-eq (s sk) B (inj₂ r) h = mvN-eq sk (λ r′ → B (inj₂ r′)) r h
mvN-eq (l sf) B (n , r) h = mvN-eq (sf n) (λ r′ → B (n , r′)) r h

mv-sim : ∀ {a} → Sm a → ∀ {x y} → Sim a x y → Sim a (mv a a x) y
bk-sim : ∀ {a} → Sm a → (r : Pre a) → ∀ {η η′} → SimP a r η η′ → SimP a r (bk a r η) η′

mv-sim sa z≈ = z≈
mv-sim sa (s≈ p) = s≈ (mv-sim sa p)
mv-sim sa (l≈ p) = l≈ (λ n → mv-sim sa (p n))
mv-sim {a} sa (c≈ {r} {g} {g′} h) =
  subst (λ t → Sim a t (G.lc r g′)) (sym (mvN-eq sa G.lc r (λ η → mv a a (g η))))
    (c≈ (λ η η′ q → mv-sim sa (h (bk a r η) η′ (bk-sim sa r q))))
mv-sim (s sk) (e≈ p) = e≈ (mv-sim sk p)
mv-sim (l sf) (e≈ {i = n} p) = e≈ (mv-sim (sf n) p)
mv-sim sa t≈ = t≈

bk-sim (s sk) (inj₁ _) p = mv-sim sk p
bk-sim (s sk) (inj₂ r) p = bk-sim sk r p
bk-sim (l sf) (n , r) p = bk-sim (sf n) r p

mv-subst : ∀ {L j} (e : L ≡ j) → Sm L → ∀ {x y} → Sim L x y → Sim j (mv L j x) (subst Raw e y)
mv-subst refl sL p = mv-sim sL p
```

## 3 `tw 2` 里的层号

```agda
up0-sm : ∀ η → Sm (up zero η)
up0-sm G.zero = z
up0-sm (G.suc a) = s (up0-sm a)
up0-sm (G.lim f) = l (λ n → up0-sm (f n))
up0-sm (G.lc () g)
up0-sm (G.em () a)
up0-sm G.top = s z

lev-sm : ∀ {a} → Sm a → (r : Pre a) → Sm (lev a r)
lev-sm (s sk) (inj₁ _) = sk
lev-sm (s sk) (inj₂ r) = lev-sm sk r
lev-sm (l sf) (n , r) = lev-sm (sf n) r
```
