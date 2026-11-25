# YiLvNeg 第 5 项：累加归一 (极限处取部分和) 与第一位置

**判决：编译定理，正反各一。** `cum` 的输出不要证书就合法 (`cum-legal`)，所以层号 `read0 (cum η)` 的合法性由树算出 (`cum-level-legal`)。
它对一般的第一位置不单调 (`cum-not-monotone`，反例 `ω ⊲ lim (1, ω, ω, …)`)，`tw 3` 的分支换成 `Ω̂ (read0 (cum η))` 之后不过 `Legal` 的 `dir` 项 (`cum-tower-not-legal`)；
沿链的一步 `η ⊲ η + y` 它单调 (`cum-add-weak`, `chain-dir`)；不改树、只把链点取成 `c + cum v` 时守卫由树算出 (`norm-guard`, `tw3-chain-step`)。
只否定 "把树的分支换成归一后的读回" 这一种写法，不否定别的归一，也不否定只在链上归一的写法。入口 [YiLvIf](YiLvIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvNegCum where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiIrrFoldBase using (add-legal; add-cp)
open import OCF.Align.YiIrrNegLegal using (Ω̂-CP; Legal-tw)
open import OCF.Align.YiLvNegCompare using (branch₃)
```

## 1 定义与不要证书的合法性

照 BTBO 的 `cumsum`：`psum g 0 = g 0`，`psum g (n+1) = psum g n + suc (g (n+1))`。极限的相邻两项相差一次加法，
路径是 `x ⊲ x + y` (极限处取第 0 项)，不读任何证书。

```agda
psum : (ℕ → R) → ℕ → R
psum g zero = g zero
psum g (suc n) = psum g n +ʳ G.suc (g (suc n))

cum : R → R
cum G.zero = G.zero
cum (G.suc a) = G.suc (cum a)
cum (G.lim f) = G.lim (psum (λ n → cum (f n)))
cum (G.lc () c t g)
cum (G.em () a)
cum G.top = G.top

weak : ∀ x y → Cp zero x (x +ʳ y)
weak x G.zero = inj₁ refl
weak x (G.suc y) = inj₂ (weak x y)
weak x (G.lim f) = inj₂ (zero , weak x (f zero))
weak x (G.lc () c t g)
weak x (G.em () a)
weak x G.top = inj₂ (inj₁ refl)

psum-legal : ∀ (g : ℕ → R) → (∀ n → Lgl zero (g n)) → ∀ n → Lgl zero (psum g n)
psum-legal g lg zero = lg zero
psum-legal g lg (suc n) =
  add-legal (psum g n) (G.suc (g (suc n))) (psum-legal g lg n) (lg (suc n))

cum-legal : ∀ a → Lgl zero (cum a)
cum-legal G.zero = tt
cum-legal (G.suc a) = cum-legal a
cum-legal (G.lim f) =
  (λ n → weak (psum (λ k → cum (f k)) n) (G.suc (cum (f (suc n))))) ,
  psum-legal (λ k → cum (f k)) (λ k → cum-legal (f k))
cum-legal (G.lc () c t g)
cum-legal (G.em () a)
cum-legal G.top = tt

cum-level-legal : ∀ η → Legal (read0 (cum η))
cum-level-legal η = read0-legal (cum η) (cum-legal η)
```

## 2 反例：`ω ⊲ lim (1, ω, ω, …)`，归一后不再是第一位置

`cum ω` 是第 0 项为零的极限。`P y`：`y` 的第一位置上的极限，第 0 项都不是零。`cum (lim (1, ω, …))` 的部分和从 1 起步，
加法把第 0 项非零传下去，所以它满足 `P`；满足 `P` 的值的第一位置里没有第 0 项为零的极限。两个对象都合法 (`ω-lgl`, `b-lgl`)。

```agda
num : ℕ → R
num zero = G.zero
num (suc n) = G.suc (num n)

ω : R
ω = G.lim num

colˢ : ℕ → R
colˢ zero = one
colˢ (suc n) = ω

b : R
b = G.lim colˢ

ω-lgl : Lgl zero ω
ω-lgl = (λ n → inj₂ (inj₁ refl)) , num-lgl
  where
  num-lgl : ∀ n → Lgl zero (num n)
  num-lgl zero = tt
  num-lgl (suc n) = num-lgl n

b-lgl : Lgl zero b
b-lgl = step , lawful
  where
  step : ∀ n → Cp zero (colˢ n) (colˢ (suc n))
  step zero = inj₂ (1 , inj₁ refl)
  step (suc n) = inj₁ refl
  lawful : ∀ n → Lgl zero (colˢ n)
  lawful zero = tt
  lawful (suc n) = ω-lgl

ω-below-b : Cp zero ω b
ω-below-b = inj₂ (1 , inj₁ refl)

NZ : R → Set
NZ G.zero = ⊥
NZ (G.suc y) = ⊤
NZ (G.lim f) = ⊤
NZ (G.lc r c t g) = ⊤
NZ (G.em i T) = ⊤
NZ G.top = ⊤

P : R → Set
P G.zero = ⊤
P (G.suc y) = P y
P (G.lim f) = NZ (f zero) × (∀ k → P (f k))
P (G.lc () c t g)
P (G.em () T)
P G.top = ⊤

no-below : ∀ (w : ℕ → R) → (NZ (w zero) → ⊥) → ∀ y → P y → Cp zero (G.lim w) y → ⊥
no-below w z y py (inj₁ refl) = z (proj₁ py)
no-below w z (G.suc y) py (inj₂ p) = no-below w z y py p
no-below w z (G.lim f) (nz , pf) (inj₂ (k , p)) = no-below w z (f k) (pf k) p
no-below w z (G.lc () c t g) py (inj₂ p)
no-below w z (G.em () T) py (inj₂ p)
no-below w z G.top py (inj₂ ())

add-NZ : ∀ x y → NZ x → NZ (x +ʳ y)
add-NZ x G.zero nz = nz
add-NZ x (G.suc y) nz = tt
add-NZ x (G.lim f) nz = tt
add-NZ x (G.lc () c t g) nz
add-NZ x (G.em () T) nz
add-NZ x G.top nz = tt

add-P : ∀ x y → NZ x → P x → P (x +ʳ y)
add-P x G.zero nz px = px
add-P x (G.suc y) nz px = add-P x y nz px
add-P x (G.lim f) nz px = add-NZ x (f zero) nz , (λ k → add-P x (f k) nz px)
add-P x (G.lc () c t g) nz px
add-P x (G.em () T) nz px
add-P x G.top nz px = px

psum-P : ∀ (g : ℕ → R) → NZ (g zero) → P (g zero) → ∀ m → NZ (psum g m) × P (psum g m)
psum-P g nz p zero = nz , p
psum-P g nz p (suc m) =
  add-NZ (psum g m) (G.suc (g (suc m))) (proj₁ (psum-P g nz p m)) ,
  add-P (psum g m) (G.suc (g (suc m))) (proj₁ (psum-P g nz p m)) (proj₂ (psum-P g nz p m))

cum-b-P : P (cum b)
cum-b-P = tt , (λ m → proj₂ (psum-P (λ n → cum (colˢ n)) tt tt m))

cum-not-monotone : Cp zero (cum ω) (cum b) → ⊥
cum-not-monotone = no-below (psum (λ n → cum (num n))) (λ z → z) (cum b) cum-b-P

-- 对合法的值陈述, 前提由 ω, b 满足.
cum-mono-fails :
  (∀ x y → Lgl zero x → Lgl zero y → Cp zero x y → Cp zero (cum x) (cum y)) → ⊥
cum-mono-fails mono = cum-not-monotone (mono ω b ω-lgl b-lgl ω-below-b)
```

## 3 换了分支的 `tw 3` 不过 `dir`

同一个不变量搬到层号上：`Q` 说第一位置上的极限第 0 项都是 Ω 结点或极限 (不是 `Ω̂ 0 = 1`)。
`ω` 与 `b` 都是 `tw 3` 的带守卫坐标，守卫是闭的相关证明，对象在读回域内。

```agda
Big : LF → Set
Big zero = ⊥
Big (suc y) = ⊥
Big (lim f) = ⊤
Big (lc k c w b₀ t g) = ⊤

Q : LF → Set
Q zero = ⊤
Q (suc y) = Q y
Q (lim f) = Big (f zero) × (∀ k → Q (f k))
Q (lc k c w b₀ t g) = Q t

no-CP : ∀ (A : ℕ → LF) → (Big (A zero) → ⊥) → ∀ y → Q y → CP (lim A) y → ⊥
no-CP A z .(lim A) qy self = z (proj₁ qy)
no-CP A z (suc y) qy (suc p) = no-CP A z y qy p
no-CP A z (lim f) (bg , qf) (lim n p) = no-CP A z (f n) (qf n) p
no-CP A z (lc k c w b₀ t g) qy (fst p) = no-CP A z t qy p

Ω-Big : ∀ y → NZ y → Big (Ω̂ (read0 y))
Ω-Big (G.suc y) nz = tt
Ω-Big (G.lim f) nz = tt
Ω-Big (G.lc () c t g) nz
Ω-Big (G.em () T) nz
Ω-Big G.top nz = tt

Ω-Q : ∀ y → P y → Q (Ω̂ (read0 y))
Ω-Q G.zero py = tt
Ω-Q (G.suc y) py = Ω-Q y py
Ω-Q (G.lim f) (nz , pf) = Ω-Big (f zero) nz , (λ k → Ω-Q (f k) (pf k))
Ω-Q (G.lc () c t g) py
Ω-Q (G.em () T) py
Ω-Q G.top py = tt

branchᶜ : (η : R) → .(Gd zero raw1 η) → LF
branchᶜ η e = Ω̂ (read0 (cum η))

dir-fails : CP (Ω̂ (read0 (cum ω))) (Ω̂ (read0 (cum b))) → ⊥
dir-fails = no-CP (λ k → Ω̂ (read0 (psum (λ n → cum (num n)) k))) (λ z → z)
  (Ω̂ (read0 (cum b))) (Ω-Q (cum b) cum-b-P)

tw3ᶜ : LF
tw3ᶜ = lc zero raw1 tt tt (tw 2) branchᶜ

ω-guard : Gd zero raw1 ω
ω-guard = inj₂ (1 , inj₁ refl) , ω-lgl , raw0-Nested ω

b-guard : Gd zero raw1 b
b-guard = inj₂ (0 , inj₁ refl) , b-lgl , raw0-Nested b

cum-tower-not-legal : Legal tw3ᶜ → ⊥
cum-tower-not-legal L = dir-fails
  (proj₁ (proj₂ (proj₂ L)) ω ω-guard b b-guard (ω-below-b , b-lgl , raw0-Nested b))
```

## 4 沿链的一步单调

`η ⊲ η + y` 的路径在极限处只取第 0 项，而 `psum g 0 = g 0`，所以归一保持这条路径。
链的相邻两点正是这种关系，于是换了分支的树上，沿链的 `dir` 成立。

```agda
cum-add-weak : ∀ x y → Cp zero (cum x) (cum (x +ʳ y))
cum-add-weak x G.zero = inj₁ refl
cum-add-weak x (G.suc y) = inj₂ (cum-add-weak x y)
cum-add-weak x (G.lim f) = inj₂ (zero , cum-add-weak x (f zero))
cum-add-weak x (G.lc () c t g)
cum-add-weak x (G.em () T)
cum-add-weak x G.top = inj₂ (inj₁ refl)

chain-dir : ∀ η y → CP (Ω̂ (read0 (cum η))) (Ω̂ (read0 (cum (η +ʳ y))))
chain-dir η y = Ω̂-CP (read0-cp (cum (η +ʳ y)) (cum-add-weak η y))
```

## 5 不改树的用法：链点取 "下界加上归一后的累计"

树仍是 `tw 3`。结点的下界 `c`，累计的加数 `v ↦ v + y`，访问的坐标取 `c + cum v`。这样链点的守卫是由树与下界的合法性算出的相关数据：
路径是 `c ⊲ c + x`，合法性由加法与 §1 给出，不要折叠的输出合法 (`YiIrrFold` 的链在这一处调用 `ψ-legal`)。
相邻两支的第一位置由 `tw 3` 自己的 `dir` 给出。下界的合法性仍要一份相关的证明 (`tw 3` 的下界是字面的 1)。
这里只有守卫、路径与层号的合法性，没有折叠，没有值；它改了链的行 (`next-additive` 不再逐字成立)。

```agda
norm-guard : ∀ c → Lgl zero c → ∀ v → Gd zero c (c +ʳ cum v)
norm-guard c l₀ v =
  weak c (cum v) , add-legal c (cum v) l₀ (cum-legal v) , raw0-Nested (c +ʳ cum v)

norm-directed : ∀ c → Lgl zero c → ∀ v y → Gd zero (c +ʳ cum v) (c +ʳ cum (v +ʳ y))
norm-directed c l₀ v y =
  add-cp c (cum-add-weak v y) ,
  add-legal c (cum (v +ʳ y)) l₀ (cum-legal (v +ʳ y)) ,
  raw0-Nested (c +ʳ cum (v +ʳ y))

norm-level-legal : ∀ c → Lgl zero c → ∀ v → Legal (read0 (c +ʳ cum v))
norm-level-legal c l₀ v = read0-legal (c +ʳ cum v) (add-legal c (cum v) l₀ (cum-legal v))

tw3-chain-step : ∀ v y →
  CP (branch₃ (one +ʳ cum v) (norm-guard one tt v))
     (branch₃ (one +ʳ cum (v +ʳ y)) (norm-guard one tt (v +ʳ y)))
tw3-chain-step v y = proj₁ (proj₂ (proj₂ (Legal-tw 3)))
  (one +ʳ cum v) (norm-guard one tt v)
  (one +ʳ cum (v +ʳ y)) (norm-guard one tt (v +ʳ y)) (norm-directed one tt v y)
```
