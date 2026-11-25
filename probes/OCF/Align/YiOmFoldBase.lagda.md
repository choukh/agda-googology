# YiOmFold 底座：`Raw (tw 2)` 上的加法、ω 倍、主干片段

**档位：定义与编译定理，没有折叠。** 加法 `plusΩ` 对加数递归：三种孩子都逐槽位搬进 `tw 2` (分支的孩子用它自带的相关守卫)，这三行不改；
`x + top` 是**替代行** (`topᴬ`)：分支函数只拿到无关的守卫，取 "第一支加上坐标自己"。`Tr` 是对加法封闭的主干片段 (结点只在主干槽位上，没有分支的孩子)。
不否定别的写法；缺的那一行见 [YiOmFoldGap](YiOmFoldGap.lagda.md)。折叠在 [YiOmFold](YiOmFold.lagda.md)，接口 [YiOmIf](YiOmIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmFoldBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested)
open import OCF.Align.YiIrrIf using (R; read0)
open import OCF.Align.YiLvIf using (Plain; up0-plain)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br)
```

## 1 三种孩子的值域

孩子的位置在 `tw 2` 里的像：层号 0 的孩子没有位置；第一支 `suc zero` 的位置 `r` 是 `inj₂ (inj₁ r)`；第 `η` 支的位置 `r` 是 `br η e r`。
`Low`, `GdL`, `LglLow`, `NestedLow` 在这些像上与孩子里的定义性相等，所以 `YiLvFoldAdd.add` 可以原样用。

```agda
RΩ : Set
RΩ = Raw K₂ω

rplain : ∀ a → Plain (read0 a)
rplain a = up0-plain a (raw0-Nested a)

alg₁ : Alg (suc zero)
alg₁ = record
  { T = RΩ; sT = G.suc; lT = G.lim; nT = λ r → G.lc (inj₂ (inj₁ r))
  ; Dnᵀ = Dn K₂ω; Lgᵀ = Lgl K₂ω; Nsᵀ = Nested K₂ω; Psᵀ = Pos K₂ω
  ; dnS = λ p → p; dnL = λ n p → n , p; dnN = λ r c t g p → p
  ; lgS = λ l → l; lgL = λ st lf → st , lf
  ; lgN = λ r c t g tg dir lt lg → tg , dir , (λ η e e′ → refl) , lt , lg
  ; nsS = λ n → n; nsL = λ n → n
  ; nsN = λ r c t g l nl nt ng → l , nl , nt , ng
  ; psS = tt; psL = tt; psN = λ r c t g → tt }

alg₀ : Alg zero
alg₀ = shS alg₁

algᴮ : ∀ η → Gd zero raw1 η → Alg (read0 η)
algᴮ η e = record
  { T = RΩ; sT = G.suc; lT = G.lim; nT = λ r → G.lc (br η e r)
  ; Dnᵀ = Dn K₂ω; Lgᵀ = Lgl K₂ω; Nsᵀ = Nested K₂ω; Psᵀ = Pos K₂ω
  ; dnS = λ p → p; dnL = λ n p → n , p; dnN = λ r c t g p → p
  ; lgS = λ l → l; lgL = λ st lf → st , lf
  ; lgN = λ r c t g tg dir lt lg → tg , dir , (λ η e e′ → refl) , lt , lg
  ; nsS = λ n → n; nsL = λ n → n
  ; nsN = λ r c t g l nl nt ng → l , nl , nt , ng
  ; psS = tt; psL = tt; psN = λ r c t g → tt }
```

## 2 加法

`x + em …`：把孩子里的树逐槽位搬进来，分支的孩子 `em (η , e) T` 用树里那份相关的 `e`。
`x + top` (**替代行**)：根槽位上的结点，下界 1，第一支 `x + top₁` (第一支的 `top` 展开)，第 `η` 支是 "第一支加上坐标 `η` 自己"。
本该有的第 `η` 支是 `x + em (η , e) top`；它要相关的 `e`，并且搬进来以后各支的槽位互不相同 ([YiOmFoldGap](YiOmFoldGap.lagda.md))。

```agda
topᴬ : RΩ → RΩ
topᴬ x = G.lc root₂ raw1 (add (suc zero) alg₁ x G.top)
  (λ η e → add zero alg₀ (add (suc zero) alg₁ x G.top) η)

plusΩ : RΩ → RΩ → RΩ
plusΩ x G.zero = x
plusΩ x (G.suc a) = G.suc (plusΩ x a)
plusΩ x (G.lim f) = G.lim (λ n → plusΩ x (f n))
plusΩ x (G.lc r c t g) = G.lc r c (plusΩ x t) (λ η e → plusΩ x (g η e))
plusΩ x (G.em (inj₁ _) a) = add zero alg₀ x a
plusΩ x (G.em (inj₂ (inj₁ _)) a) = add (suc zero) alg₁ x a
plusΩ x (G.em (inj₂ (inj₂ (η , e))) a) = add (read0 η) (algᴮ η e) x a
plusΩ x G.top = topᴬ x
```

弱增长、保持第一位置、严格增长、合法性、嵌套证据。`a ⊲ top` 只有 `a = em₁ a′` 且 `a′ ≤ top₁` 一种，对上替代行的第一支。

```agda
plus-weak : ∀ x a → Cp K₂ω x (plusΩ x a)
plus-weak x G.zero = inj₁ refl
plus-weak x (G.suc a) = inj₂ (plus-weak x a)
plus-weak x (G.lim f) = inj₂ (zero , plus-weak x (f zero))
plus-weak x (G.lc r c t g) = inj₂ (plus-weak x t)
plus-weak x (G.em (inj₁ _) a) = add-weak zero alg₀ x a
plus-weak x (G.em (inj₂ (inj₁ _)) a) = add-weak (suc zero) alg₁ x a
plus-weak x (G.em (inj₂ (inj₂ (η , e))) a) = add-weak (read0 η) (algᴮ η e) x a
plus-weak x G.top = inj₂ (add-weak (suc zero) alg₁ x G.top)

plus-grow : ∀ x y → Pos K₂ω y → Dn K₂ω x (plusΩ x y)
plus-grow x (G.suc y) p = plus-weak x y
plus-grow x (G.lim f) p = zero , plus-weak x (f zero)
plus-grow x (G.lc r c t g) p = plus-weak x t
plus-grow x G.top p = add-weak (suc zero) alg₁ x G.top

plus-cp : ∀ x {a b} → Cp K₂ω a b → Cp K₂ω (plusΩ x a) (plusΩ x b)
plus-dn : ∀ x {a} b → Dn K₂ω a b → Dn K₂ω (plusΩ x a) (plusΩ x b)

plus-cp x (inj₁ refl) = inj₁ refl
plus-cp x {b = b} (inj₂ p) = inj₂ (plus-dn x b p)

plus-dn x (G.suc b) p = plus-cp x p
plus-dn x (G.lim f) (n , p) = n , plus-cp x p
plus-dn x (G.lc r c t g) p = plus-cp x p
plus-dn x {G.em (inj₁ _) a} (G.em (inj₁ _) T) p = add-dn zero tt alg₀ x T p
plus-dn x {G.em (inj₂ (inj₁ _)) a} (G.em (inj₂ (inj₁ _)) T) p =
  add-dn (suc zero) tt alg₁ x T p
plus-dn x {G.em (inj₂ (inj₂ (η , e))) a} (G.em (inj₂ (inj₂ .(η , e))) T) (refl , p) =
  add-dn (read0 η) (rplain η) (algᴮ η e) x T p
plus-dn x {G.em (inj₂ (inj₁ _)) a} G.top p = add-cp (suc zero) tt alg₁ x p

plus-lgl : ∀ x a → Lgl K₂ω x → Lgl K₂ω a → Lgl K₂ω (plusΩ x a)
plus-lgl x G.zero lx la = lx
plus-lgl x (G.suc a) lx la = plus-lgl x a lx la
plus-lgl x (G.lim f) lx (st , lf) =
  (λ n → plus-cp x (st n)) , (λ n → plus-lgl x (f n) lx (lf n))
plus-lgl x (G.lc r c t g) lx (tg , dir , irr , lt , lg) =
  (λ η e → plus-cp x (tg η e)) ,
  (λ η e η′ e′ q → plus-cp x (dir η e η′ e′ q)) ,
  (λ η e e′ → refl) ,
  plus-lgl x t lx lt ,
  (λ η e → plus-lgl x (g η e) lx (lg η e))
plus-lgl x (G.em (inj₁ _) a) lx la = add-lgl zero tt alg₀ x a lx la
plus-lgl x (G.em (inj₂ (inj₁ _)) a) lx la = add-lgl (suc zero) tt alg₁ x a lx la
plus-lgl x (G.em (inj₂ (inj₂ (η , e))) a) lx la =
  add-lgl (read0 η) (rplain η) (algᴮ η e) x a lx la
plus-lgl x G.top lx la =
  (λ η e → add-weak zero alg₀ (add (suc zero) alg₁ x G.top) η) ,
  (λ η e η′ e′ q → add-cp zero tt alg₀ (add (suc zero) alg₁ x G.top) (proj₁ q)) ,
  (λ η e e′ → refl) ,
  add-lgl (suc zero) tt alg₁ x G.top lx tt ,
  (λ η e → add-lgl zero tt alg₀ (add (suc zero) alg₁ x G.top) η
    (add-lgl (suc zero) tt alg₁ x G.top lx tt) (proj₁ (proj₂ e)))

plus-ns : ∀ x a → Nested K₂ω x → Nested K₂ω a → Nested K₂ω (plusΩ x a)
plus-ns x G.zero nx na = nx
plus-ns x (G.suc a) nx na = plus-ns x a nx na
plus-ns x (G.lim f) nx na = λ n → plus-ns x (f n) nx (na n)
plus-ns x (G.lc r c t g) nx (l , nl , nt , ng) =
  l , nl , plus-ns x t nx nt , (λ η e → plus-ns x (g η e) nx (ng η e))
plus-ns x (G.em (inj₁ _) a) nx na = add-ns zero alg₀ x a nx na
plus-ns x (G.em (inj₂ (inj₁ _)) a) nx na = add-ns (suc zero) alg₁ x a nx na
plus-ns x (G.em (inj₂ (inj₂ (η , e))) a) nx na = add-ns (read0 η) (algᴮ η e) x a nx na
plus-ns x G.top nx na =
  tt , tt , add-ns (suc zero) alg₁ x G.top nx tt ,
  (λ η e → add-ns zero alg₀ (add (suc zero) alg₁ x G.top) η
    (add-ns (suc zero) alg₁ x G.top nx tt) (proj₂ (proj₂ e)))
```

## 3 ω 倍

第 0 项取一份，与 `YiLvFoldAdd.copies` 同一个写法，加法换成 `plusΩ`。

```agda
copiesΩ : RΩ → ℕ → RΩ
copiesΩ y zero = y
copiesΩ y (suc n) = plusΩ y (copiesΩ y n)

successorΩ : RΩ → RΩ
successorΩ y = G.lim (copiesΩ y)

copiesΩ-step : ∀ y n → Cp K₂ω (copiesΩ y n) (copiesΩ y (suc n))
copiesΩ-step y zero = plus-weak y y
copiesΩ-step y (suc n) = plus-cp y (copiesΩ-step y n)

copiesΩ-legal : ∀ y → Lgl K₂ω y → ∀ n → Lgl K₂ω (copiesΩ y n)
copiesΩ-legal y ly zero = ly
copiesΩ-legal y ly (suc n) = plus-lgl y (copiesΩ y n) ly (copiesΩ-legal y ly n)

copiesΩ-nested : ∀ y → Nested K₂ω y → ∀ n → Nested K₂ω (copiesΩ y n)
copiesΩ-nested y ny zero = ny
copiesΩ-nested y ny (suc n) = plus-ns y (copiesΩ y n) ny (copiesΩ-nested y ny n)
```

## 4 主干片段

`Tr ξ`：结点只在主干的两个槽位上 (层号都是 0)，孩子只有层号 0 的与第一支的。分支槽位上的结点与分支的孩子不在里面。
`top` 在里面。加法、ω 倍对它封闭：两种主干孩子搬进来以后都是主干槽位上的结点。

```agda
Tr : RΩ → Set
Tr G.zero = ⊤
Tr (G.suc a) = Tr a
Tr (G.lim f) = ∀ n → Tr (f n)
Tr (G.lc (inj₁ (inj₁ _)) c t g) = Tr t × (∀ η (e : Gd zero c η) → Tr (g η e))
Tr (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) = Tr t × (∀ η (e : Gd zero c η) → Tr (g η e))
Tr (G.lc (inj₂ (inj₂ _)) c t g) = ⊥
Tr (G.em (inj₁ _) a) = ⊤
Tr (G.em (inj₂ (inj₁ _)) a) = ⊤
Tr (G.em (inj₂ (inj₂ _)) a) = ⊥
Tr G.top = ⊤

add₀-tr : ∀ x → Tr x → ∀ (a : R) → Tr (add zero alg₀ x a)
add₀-tr x tx G.zero = tx
add₀-tr x tx (G.suc a) = add₀-tr x tx a
add₀-tr x tx (G.lim f) = λ n → add₀-tr x tx (f n)
add₀-tr x tx G.top = tx

add₁-tr : ∀ x → Tr x → ∀ (a : Raw (suc zero)) → Tr (add (suc zero) alg₁ x a)
add₁-tr x tx G.zero = tx
add₁-tr x tx (G.suc a) = add₁-tr x tx a
add₁-tr x tx (G.lim f) = λ n → add₁-tr x tx (f n)
add₁-tr x tx (G.lc (inj₁ _) c t g) = add₁-tr x tx t , (λ η e → add₁-tr x tx (g η e))
add₁-tr x tx (G.em _ a) = add₀-tr x tx a
add₁-tr x tx G.top = add₀-tr x tx raw1 , (λ η e → add₀-tr x tx η)

plus-tr : ∀ x a → Tr x → Tr a → Tr (plusΩ x a)
plus-tr x G.zero tx ta = tx
plus-tr x (G.suc a) tx ta = plus-tr x a tx ta
plus-tr x (G.lim f) tx ta = λ n → plus-tr x (f n) tx (ta n)
plus-tr x (G.lc (inj₁ (inj₁ _)) c t g) tx (tt′ , tg) =
  plus-tr x t tx tt′ , (λ η e → plus-tr x (g η e) tx (tg η e))
plus-tr x (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) tx (tt′ , tg) =
  plus-tr x t tx tt′ , (λ η e → plus-tr x (g η e) tx (tg η e))
plus-tr x (G.em (inj₁ _) a) tx ta = add₀-tr x tx a
plus-tr x (G.em (inj₂ (inj₁ _)) a) tx ta = add₁-tr x tx a
plus-tr x G.top tx ta =
  add₁-tr x tx G.top , (λ η e → add₀-tr (add (suc zero) alg₁ x G.top) (add₁-tr x tx G.top) η)

copiesΩ-tr : ∀ y → Tr y → ∀ n → Tr (copiesΩ y n)
copiesΩ-tr y ty zero = ty
copiesΩ-tr y ty (suc n) = plus-tr y (copiesΩ y n) ty (copiesΩ-tr y ty n)
```
