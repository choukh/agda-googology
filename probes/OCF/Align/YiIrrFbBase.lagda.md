# YiIrrFb 底座：第 1 层的加法引理、定义域与 `Raw 1` 里的加法链

**档位：编译定理与定义，没有折叠。** 三样：`_+¹_` 保持第一位置、合法性与嵌套证据；定义域
`Dom x = Only01 x × Legal x × Seedᶠ x`，规范的 Ω₂ 在其中 (`dom-Ω₂`)；`Raw 1` 里的加法链 `Chain₁`，
链点的守卫无关，观察函数的目标层是参数 (回灌行取 0，`ψ₁` 自己的行取 1)。入口 [YiIrrFb](YiIrrFb.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFbBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrFoldSeed using (Seedᶠ; seed-Ω̂; seed-up)
open import OCF.Align.YiIrrNegLegal using (Legal-Ω̂; lgl→Legal)
open import OCF.Align.YiIrrFbRaw
open import OCF.Align.YiIrrFbIf
```

## 1 第 1 层的加法

`embed-*` 是加数为嵌入的第 0 层值的情形；`add-*¹` 对一般的加数。`add-weak¹` 不要前提；
严格增长 `grow¹` 只看加数的头：不是 `zero`，不是嵌入 (`Pos₁`)。`ψ₁` 的每一行的输出都是这样的头。

```agda
embed-cp : ∀ x {a b} → Cp zero a b → Cp L1 (embed-add x a) (embed-add x b)
embed-dn : ∀ x {a} b → Dn zero a b → Dn L1 (embed-add x a) (embed-add x b)
embed-cp x (inj₁ refl) = inj₁ refl
embed-cp x {b = b} (inj₂ p) = inj₂ (embed-dn x b p)
embed-dn x (G.suc b) p = embed-cp x p
embed-dn x (G.lim f) (n , p) = n , embed-cp x p
embed-dn x (G.lc () c t g) p
embed-dn x (G.em () T) p
embed-dn x G.top ()

embed-weak : ∀ x a → Cp L1 x (embed-add x a)
embed-weak x G.zero = inj₁ refl
embed-weak x (G.suc a) = inj₂ (embed-weak x a)
embed-weak x (G.lim f) = inj₂ (zero , embed-weak x (f zero))
embed-weak x (G.lc () c t g)
embed-weak x (G.em () T)
embed-weak x G.top = inj₂ (inj₁ refl)

embed-legal : ∀ x a → Lgl L1 x → Lgl zero a → Lgl L1 (embed-add x a)
embed-legal x G.zero lx la = lx
embed-legal x (G.suc a) lx la = embed-legal x a lx la
embed-legal x (G.lim f) lx (st , lf) =
  (λ n → embed-cp x (st n)) , (λ n → embed-legal x (f n) lx (lf n))
embed-legal x (G.lc () c t g) lx la
embed-legal x (G.em () T) lx la
embed-legal x G.top lx la = lx

embed-nested : ∀ x a → Nested L1 x → Nested L1 (embed-add x a)
embed-nested x G.zero nx = nx
embed-nested x (G.suc a) nx = embed-nested x a nx
embed-nested x (G.lim f) nx = λ n → embed-nested x (f n) nx
embed-nested x (G.lc () c t g) nx
embed-nested x (G.em () T) nx
embed-nested x G.top nx = nx

add-cp¹ : ∀ x {a b} → Cp L1 a b → Cp L1 (x +¹ a) (x +¹ b)
add-dn¹ : ∀ x {a} b → Dn L1 a b → Dn L1 (x +¹ a) (x +¹ b)
add-cp¹ x (inj₁ refl) = inj₁ refl
add-cp¹ x {b = b} (inj₂ p) = inj₂ (add-dn¹ x b p)
add-dn¹ x (G.suc b) p = add-cp¹ x p
add-dn¹ x (G.lim f) (n , p) = n , add-cp¹ x p
add-dn¹ x (G.lc r c t g) p = add-cp¹ x p
add-dn¹ x {G.em _ a} (G.em _ T) p = embed-dn x T p
add-dn¹ x {G.em _ a} G.top (inj₁ refl) = inj₁ refl
add-dn¹ x {G.em _ a} G.top (inj₂ ())

add-weak¹ : ∀ x y → Cp L1 x (x +¹ y)
add-weak¹ x G.zero = inj₁ refl
add-weak¹ x (G.suc y) = inj₂ (add-weak¹ x y)
add-weak¹ x (G.lim f) = inj₂ (zero , add-weak¹ x (f zero))
add-weak¹ x (G.lc r c t g) = inj₂ (add-weak¹ x t)
add-weak¹ x (G.em _ a) = embed-weak x a
add-weak¹ x G.top = inj₂ (inj₂ (inj₁ refl))

Pos₁ : R₁ → Set
Pos₁ G.zero = ⊥
Pos₁ (G.suc y) = ⊤
Pos₁ (G.lim f) = ⊤
Pos₁ (G.lc r c t g) = ⊤
Pos₁ (G.em i a) = ⊥
Pos₁ G.top = ⊤

grow¹ : ∀ x y → Pos₁ y → Dn L1 x (x +¹ y)
grow¹ x (G.suc y) p = add-weak¹ x y
grow¹ x (G.lim f) p = zero , add-weak¹ x (f zero)
grow¹ x (G.lc r c t g) p = add-weak¹ x t
grow¹ x G.top p = inj₂ (inj₁ refl)

add-legal¹ : ∀ x y → Lgl L1 x → Lgl L1 y → Lgl L1 (x +¹ y)
add-legal¹ x G.zero lx ly = lx
add-legal¹ x (G.suc y) lx ly = add-legal¹ x y lx ly
add-legal¹ x (G.lim f) lx (st , lf) =
  (λ n → add-cp¹ x (st n)) , (λ n → add-legal¹ x (f n) lx (lf n))
add-legal¹ x (G.lc r c t g) lx (tg , dir , irr , lt , lg) =
  (λ η e → add-cp¹ x (tg η e)) ,
  (λ η e η′ e′ q → add-cp¹ x (dir η e η′ e′ q)) ,
  (λ η e e′ → refl) ,
  add-legal¹ x t lx lt ,
  (λ η e → add-legal¹ x (g η e) lx (lg η e))
add-legal¹ x (G.em _ a) lx ly = embed-legal x a lx ly
add-legal¹ x G.top lx ly =
  (λ η e → embed-cp x (proj₁ e)) ,
  (λ η e η′ e′ q → embed-cp x (proj₁ q)) ,
  (λ η e e′ → refl) ,
  lx ,
  (λ η e → embed-legal x η lx (proj₁ (proj₂ e)))

add-nested¹ : ∀ x y → Nested L1 x → Nested L1 y → Nested L1 (x +¹ y)
add-nested¹ x G.zero nx ny = nx
add-nested¹ x (G.suc y) nx ny = add-nested¹ x y nx ny
add-nested¹ x (G.lim f) nx ny = λ n → add-nested¹ x (f n) nx (ny n)
add-nested¹ x (G.lc r c t g) nx (l , nl , nt , ng) =
  l , nl , add-nested¹ x t nx nt , (λ η e → add-nested¹ x (g η e) nx (ng η e))
add-nested¹ x (G.em _ a) nx ny = embed-nested x a nx
add-nested¹ x G.top nx ny = tt , tt , nx , (λ η e → embed-nested x η nx)

copies₁-step : ∀ y n → Cp L1 (copies₁ y n) (copies₁ y (suc n))
copies₁-step y zero = add-weak¹ y y
copies₁-step y (suc n) = add-cp¹ y (copies₁-step y n)

copies₁-legal : ∀ y → Lgl L1 y → ∀ n → Lgl L1 (copies₁ y n)
copies₁-legal y ly zero = ly
copies₁-legal y ly (suc n) =
  add-legal¹ y (copies₁ y n) ly (copies₁-legal y ly n)

copies₁-nested : ∀ y → Nested L1 y → ∀ n → Nested L1 (copies₁ y n)
copies₁-nested y ny zero = ny
copies₁-nested y ny (suc n) =
  add-nested¹ y (copies₁ y n) ny (copies₁-nested y ny n)
```

## 2 定义域

证书的第三项取 [YiIrrFoldSeed](YiIrrFoldSeed.lagda.md) 的 `Seedᶠ` (每个结点的下界合法与嵌套证据，相关的；
对层号、第一支、分支遗传)：保留行折叠第一支，输出结点的嵌套证据要相关的 `Lgl 0 c`，
所以这里用对第一支也遗传的那一个，不用 `Seed`。

```agda
Dom : LF → Set
Dom x = Only01 x × Legal x × Seedᶠ x

dom-pred : ∀ x → Dom (suc x) → Dom x
dom-pred x d = d

dom-at : ∀ f → Dom (lim f) → ∀ n → Dom (f n)
dom-at f (o , (st , l) , s) n = o n , l n , s n

module Node₀ (c : R) .(w : Lgl zero c) .(b : Nested zero c) (t : LF)
  (g : (η : R) → .(Gd zero c η) → LF) (d : Dom (lc zero c w b t g)) where

  first : Dom t
  first = proj₁ (proj₁ d) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₁ (proj₂ d)))))) ,
    proj₁ (proj₂ (proj₂ (proj₂ (proj₂ d))))

  branch : ∀ η (e : Gd zero c η) → Dom (g η e)
  branch η e = proj₂ (proj₁ d) η e ,
    proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₁ (proj₂ d)))))) η e ,
    proj₂ (proj₂ (proj₂ (proj₂ (proj₂ d)))) η e

  low : Lgl zero c × Nested zero c
  low = proj₁ (proj₂ (proj₂ (proj₂ d)))

  seed : Gd zero c c
  seed = inj₁ refl , low

  to-branch : ∀ η (e : Gd zero c η) → CP t (g η e)
  to-branch = proj₁ (proj₂ (proj₁ (proj₂ d)))

  directed : ∀ η (e : Gd zero c η) η′ (e′ : Gd zero c η′) → Gd zero η η′ →
    CP (g η e) (g η′ e′)
  directed = proj₁ (proj₂ (proj₂ (proj₁ (proj₂ d))))

module Node₁ (c : R₁) .(w : Lgl L1 c) .(b : Nested L1 c) (t : LF)
  (g : (η : R₁) → .(Gd L1 c η) → LF) (d : Dom (lc L1 c w b t g)) where

  branch : ∀ η (e : Gd L1 c η) → Dom (g η e)
  branch η e = proj₂ (proj₁ d) η e ,
    proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₁ (proj₂ d)))))) η e ,
    proj₂ (proj₂ (proj₂ (proj₂ (proj₂ d)))) η e

  seed : Gd L1 c c
  seed = inj₁ refl , proj₁ (proj₂ (proj₂ (proj₂ d)))

  to-branch : ∀ η (e : Gd L1 c η) → CP t (g η e)
  to-branch = proj₁ (proj₂ (proj₁ (proj₂ d)))

  directed : ∀ η (e : Gd L1 c η) η′ (e′ : Gd L1 c η′) → Gd L1 η η′ →
    CP (g η e) (g η′ e′)
  directed = proj₁ (proj₂ (proj₂ (proj₁ (proj₂ d))))
```

规范的 Ω₂ 在定义域里：它是层号 1 的结点，下界 `top`，第一支 Ω₁，分支是读回 `up 1 η`。
读回把 `Raw 1` 的结点读成层号 0 的结点，`em` 读成第 0 层的拷贝，`top` 读成 Ω₁，所以分支都在片段里。
合法性与起点证据来自已有的闭包定理 (`Legal-Ω̂`, `seed-Ω̂`)。

```agda
up0-only : ∀ a .(nb : Nested zero a) → Only01 (up zero a nb)
up0-only G.zero nb = tt
up0-only (G.suc a) nb = up0-only a nb
up0-only (G.lim f) nb = λ n → up0-only (f n) (nb n)
up0-only (G.lc () c t g) nb
up0-only (G.em () a) nb
up0-only G.top nb = tt

Ω₁-only01 : Only01 (tw 2)
Ω₁-only01 = tt , (λ η e → up0-only η (proj₂ (proj₂ e)))

up1-only : ∀ a .(nb : Nested L1 a) → Only01 (up L1 a nb)
up1-only G.zero nb = tt
up1-only (G.suc a) nb = up1-only a nb
up1-only (G.lim f) nb = λ n → up1-only (f n) (nb n)
up1-only (G.lc (inj₁ _) c t g) nb =
  up1-only t (proj₁ (proj₂ (proj₂ nb))) ,
  (λ η e → up1-only (g η e) (proj₂ (proj₂ (proj₂ nb)) η e))
up1-only (G.lc (inj₂ ()) c t g) nb
up1-only (G.em _ a) nb = up0-only a nb
up1-only G.top nb = Ω₁-only01

-- 第 1 层的读回域在定义域里: 合法且带嵌套证据的坐标, 读回后有证书.
up1-dom : ∀ a → Lgl L1 a → (nb : Nested L1 a) → Dom (up L1 a nb)
up1-dom a l nb = up1-only a nb , lgl→Legal L1 tt a nb l , seed-up L1 tt a nb

Ω₂-form : Ω₂ ≡ lc L1 G.top tt tt (tw 2) (λ η e → up L1 η (proj₂ (proj₂ e)))
Ω₂-form = refl

dom-Ω₂ : Dom Ω₂
dom-Ω₂ =
  (Ω₁-only01 , (λ η e → up1-only η (proj₂ (proj₂ e)))) ,
  Legal-Ω̂ (suc L1) tt ,
  seed-Ω̂ (suc L1) tt
```

## 3 `Raw 1` 里的加法链

`body` 是链点处目标层 1 的子折叠，链只由它推进。`lawful`, `nested` 只进下一点的守卫，是无关的模块参数；
`positive` 给增长，相关地用，它自己的守卫参数无关。`obs` 是在链点处被取极限的观察，目标层 `m` 任意 (显式参数：`Raw` 不是单射的头)。

```agda
module Chain₁ (c : R₁) (body : (η : R₁) → .(Gd L1 c η) → R₁)
  .(lawful : ∀ η (e : Gd L1 c η) → Lgl L1 (body η e))
  .(nested : ∀ η (e : Gd L1 c η) → Nested L1 (body η e))
  (positive : ∀ η .(e : Gd L1 c η) → Pos₁ (body η e)) where

  step : Pt L1 c → R₁
  step (pt η e) = body η e

  next : Pt L1 c → Pt L1 c
  next (pt η e) = pt (η +¹ body η e)
    (Cp-tr L1 (proj₁ e) (inj₂ (grow¹ η (body η e) (positive η e))) ,
     add-legal¹ η (body η e) (proj₁ (proj₂ e)) (lawful η e) ,
     add-nested¹ η (body η e) (proj₂ (proj₂ e)) (nested η e))

  grow : ∀ p → Dn L1 (at p) (at (next p))
  grow (pt η e) = grow¹ η (body η e) (positive η e)

  see : ∀ m (obs : (η : R₁) → .(Gd L1 c η) → Raw m) → Pt L1 c → Raw m
  see m obs (pt η e) = obs η e

  collapse : ∀ m (obs : (η : R₁) → .(Gd L1 c η) → Raw m) → Pt L1 c → Raw m
  collapse m obs p = G.lim (λ n → see m obs (iterate next p n))
```

证明里另造一列相关的守卫，坐标就是定义里那条链的坐标：起点用证书里的 `Lgl 1 c` 与 `Nested 1 c`，
下一点照 `next` 的无关分量重写。观察的合法性与沿守卫的位置保持给出极限的合法性。

```agda
module ChainLegal₁ (c : R₁) (body : (η : R₁) → .(Gd L1 c η) → R₁)
  (lawful : ∀ η (e : Gd L1 c η) → Lgl L1 (body η e))
  (nested : ∀ η (e : Gd L1 c η) → Nested L1 (body η e))
  (positive : ∀ η .(e : Gd L1 c η) → Pos₁ (body η e))
  (p₀ : Pt L1 c) (e₀ : Gd L1 c (at p₀)) where

  open Chain₁ c body lawful nested positive

  points : ℕ → Pt L1 c
  points = iterate next p₀

  guards : ∀ n → Gd L1 c (at (points n))
  guards zero = e₀
  guards (suc n) =
    Cp-tr L1 (proj₁ (guards n)) (inj₂ (grow (points n))) ,
    add-legal¹ (at (points n)) (step (points n))
      (proj₁ (proj₂ (guards n))) (lawful (at (points n)) (guards n)) ,
    add-nested¹ (at (points n)) (step (points n))
      (proj₂ (proj₂ (guards n))) (nested (at (points n)) (guards n))

  module _ (m : LF) (obs : (η : R₁) → .(Gd L1 c η) → Raw m) where

    collapse-legal :
      (∀ η (e : Gd L1 c η) → Lgl m (obs η e)) →
      (∀ η (e : Gd L1 c η) η′ (e′ : Gd L1 c η′) → Gd L1 η η′ →
        Cp m (obs η e) (obs η′ e′)) →
      Lgl m (collapse m obs p₀)
    collapse-legal obs-lawful obs-monotone =
      (λ n → obs-monotone (at (points n)) (guards n)
        (at (points (suc n))) (guards (suc n))
        (inj₂ (grow (points n)) , proj₂ (guards (suc n)))) ,
      (λ n → obs-lawful (at (points n)) (guards n))

    collapse-nested : (∀ η (e : Gd L1 c η) → Nested m (obs η e)) →
      Nested m (collapse m obs p₀)
    collapse-nested h n = h (at (points n)) (guards n)
```
