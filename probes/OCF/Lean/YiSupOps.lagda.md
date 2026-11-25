# 取尾部的上确界构造子 (原型): 运算

> 判决: 原型. 同 `YiRWOps`, 各运算补 `sup` 一行; Ω 形状层号上的 `Ωt` 改写成 `sup tt zero (λ c → Ωt (h c))` (规范的 Ω 树用新构造子).
> 上折 `Up` 在 `sup` 上是顶槽位的结点, 逐孩子上折.
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSupOps where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiSupBlock
```

## 一层之内

```agda
iter : {A : Set} → (A → A) → A → ℕ → A
iter f a zero    = a
iter f a (suc n) = f (iter f a n)

module _ {S : Sg} where
  T⁺ : Set
  T⁺ = Σ (T S) (Lt S zero)

  infixl 6 _+_
  mutual
    _+_ : T S → T S → T S
    x + zero       = x
    x + suc y      = suc (x + y)
    x + lim f a    = lim (λ n → x + f n) (λ n → +-mono x (a n))
    x + Ω p g      = Ω p (λ z → x + g z)
    x + up y c w e = up (x + y) c w e
    x + sup q y Y e = sup q (x + y) Y e

    +-mono : (c : T S) {a b : T S} → Lt S a b → Lt S (c + a) (c + b)
    +-mono c ◃s           = ◃s
    +-mono c (◃l n)       = ◃l n
    +-mono c ◃w           = ◃w
    +-mono c (◃u x k y e) = ◃u (c + x) k y e
    +-mono c (◃c x k d)   = ◃c (c + x) k d
    +-mono c (◃p q x Y e) = ◃p q (c + x) Y e
    +-mono c (◃t d e)     = ◃t (+-mono c d) (+-mono c e)

  lim⁺ : (F : ℕ → T⁺) → ((n : ℕ) → Lt S (proj₁ (F n)) (proj₁ (F (suc n)))) → T⁺
  lim⁺ F a = lim (λ n → proj₁ (F n)) a , ◃t (proj₂ (F zero)) (◃l zero)

  nextA : (b : T S) → Lt S zero b → (n : ℕ) → Lt S (iter (b +_) b n) (iter (b +_) b (suc n))
  nextA b nb zero    = +-mono b nb
  nextA b nb (suc n) = +-mono b (nextA b nb n)

  next⁺ : T⁺ → T⁺
  next⁺ (b , nb) = lim (iter (b +_) b) (nextA b nb) , ◃t nb (◃l zero)

  cum : (ℕ → T S) → ℕ → T S
  cum F zero    = F zero
  cum F (suc n) = cum F n + F (suc n)

  limc⁺ : (ℕ → T⁺) → T⁺
  limc⁺ F = lim (cum (λ n → proj₁ (F n))) (λ n → +-mono _ (proj₂ (F (suc n)))) , ◃t (proj₂ (F zero)) (◃l zero)

  Ω⁺ : (p : P S) → (B S p → T⁺) → T⁺
  Ω⁺ p G = Ω p (λ z → proj₁ (G z)) , ◃t (proj₂ (G (b₀ S p))) ◃w

  mutual
    zl : (x : T S) → (zero ≡ x) ⊎ Lt S zero x
    zl zero         = inj₁ refl
    zl (suc x)      = inj₂ (z◃ x ◃s)
    zl (lim f a)    = inj₂ (z◃ (f zero) (◃l zero))
    zl (Ω p g)      = inj₂ (z◃ (g (b₀ S p)) ◃w)
    zl (up x c y e) = inj₂ (z◃ x (◃u x c y e))
    zl (sup q x Y e) = inj₂ (z◃ x (◃p q x Y e))

    z◃ : (x : T S) {y : T S} → Lt S x y → Lt S zero y
    z◃ x d with zl x
    ... | inj₁ refl = d
    ... | inj₂ d′   = ◃t d′ d
```

## 各层的 Ω 树, 第 0 层的嵌入

`upz c y` 把孩子 c 的非零树嵌进本层 (左边是零). `Ωt ℓ` 是本层的 Ω_ℓ, 与 F2 的 `Ωt` 逐形状相同 (ℕ 极限一行写成部分和极限, 化简后与 F2 的 `cumΩ` 同项).

```agda
Tr⁺ : L → Set
Tr⁺ ℓ = T⁺ {Sig ℓ}

c₀ : (s : Sh) → Ch s
c₀ sS     = tt
c₀ sL     = zero
c₀ (sΩ k) = zero

upz : ∀ {s h} (c : Ch s) → Tr⁺ (h c) → Tr⁺ (nd s h)
upz c (y , e) = up zero c y e , ◃u zero c y e

Ωt : (ℓ : L) → Tr⁺ ℓ
Ωt zero          = suc zero , ◃s
Ωt (nd sS h)     = Ω⁺ (inj₂ (tt , inj₁ tt)) λ c → upz tt (suc c , z◃ c ◃s)
Ωt (nd sL g)     = limc⁺ λ n → upz n (Ωt (g n))
Ωt (nd (sΩ k) h) = sup tt zero (λ c → proj₁ (Ωt (h c))) (λ c → proj₂ (Ωt (h c))) , ◃p tt zero _ _

mutual
  ι : (j : L) → Tr zero → Tr j
  ι j zero      = zero
  ι j (suc x)   = suc (ι j x)
  ι j (lim f a) = lim (λ n → ι j (f n)) (λ n → ι-mono j (a n))

  ι-mono : (j : L) {a b : Tr zero} → zero ⊢ a ◃ b → j ⊢ ι j a ◃ ι j b
  ι-mono j ◃s       = ◃s
  ι-mono j (◃l n)   = ◃l n
  ι-mono j (◃t d e) = ◃t (ι-mono j d) (ι-mono j e)

infixl 6 _⊞_
_⊞_ : ∀ {j} → Tr⁺ j → Tr⁺ zero → Tr⁺ j
_⊞_ {j} (b , nb) (y , ny) = b + ι j y , ◃t nb (+-mono b (ι-mono j ny))
```

## 上折: 孩子层的树折进本层

下行链 `Dn`; 槽位沿链搬进 ℓ (`mv`), 分支类型逐字不变, 所以换型 `mvBr` 与第一分支 `mvFirst` 都是一行递归.

```agda
data Dn (ℓ : L) : L → Set where
  stop : Dn ℓ ℓ
  down : ∀ {s h} → Dn ℓ (nd s h) → (c : Ch s) → Dn ℓ (h c)

mv : ∀ {ℓ j} → Dn ℓ j → Pos j → Pos ℓ
mv stop       p = p
mv (down d c) p = mv d (inj₂ (c , inj₂ p))

mvBr : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) → Br ℓ (mv d p) → Br j p
mvBr stop       p z = z
mvBr (down d c) p z = mvBr d (inj₂ (c , inj₂ p)) z

mvFirst : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) → mvBr d p (fromBr ℓ (mv d p) zero) ≡ fromBr j p zero
mvFirst stop       p = refl
mvFirst (down d c) p = mvFirst d (inj₂ (c , inj₂ p))

mutual
  Up : ∀ {ℓ} (j : L) → Dn ℓ j → Tr⁺ ℓ → Tr j → Tr⁺ ℓ
  Up j        d b zero          = b
  Up j        d b (suc y)       = next⁺ (Up j d b y)
  Up j        d b (lim f a)     = lim⁺ (λ n → Up j d b (f n)) (λ n → Upm j d b (a n))
  Up j        d b (Ω p g)       = Ω⁺ (mv d p) (λ z → Up j d b (g (mvBr d p z)))
  Up (nd s h) d b (up y c y′ _) = Up (h c) (down d c) (Up (nd s h) d b y) y′
  Up (nd (sΩ k) h) d b (sup _ y Y _) = Ω⁺ (mv d (inj₁ (inj₁ tt))) λ z →
    Up (h (mvBr d (inj₁ (inj₁ tt)) z)) (down d (mvBr d (inj₁ (inj₁ tt)) z)) (Up (nd (sΩ k) h) d b y) (Y (mvBr d (inj₁ (inj₁ tt)) z))

  Upm : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr⁺ ℓ) {x y : Tr j}
      → j ⊢ x ◃ y → ℓ ⊢ proj₁ (Up j d b x) ◃ proj₁ (Up j d b y)
  Upm j d b ◃s     = ◃l zero
  Upm j d b (◃l n) = ◃l n
  Upm {ℓ} j d b (◃w {p = p} {g = g}) =
    subst (λ t → ℓ ⊢ proj₁ (Up j d b (g t)) ◃ proj₁ (Up j d b (Ω p g))) (mvFirst d p) ◃w
  Upm (nd s h) d b (◃u x c y e) = Upm (h c) (down d c) (Up (nd s h) d b x) e
  Upm (nd s h) d b (◃c x c r)   = Upm (h c) (down d c) (Up (nd s h) d b x) r
  Upm {ℓ} (nd (sΩ k) h) d b (◃p _ x Y e) =
    ◃t (Upm (h (mvBr d (inj₁ (inj₁ tt)) (fromBr ℓ (mv d (inj₁ (inj₁ tt))) zero)))
            (down d (mvBr d (inj₁ (inj₁ tt)) (fromBr ℓ (mv d (inj₁ (inj₁ tt))) zero)))
            (Up (nd (sΩ k) h) d b x) (e (mvBr d (inj₁ (inj₁ tt)) (fromBr ℓ (mv d (inj₁ (inj₁ tt))) zero)))) ◃w
  Upm j d b (◃t e f) = ◃t (Upm j d b e) (Upm j d b f)
```
