# 合法性进块: 运算

> 判决: 成品候选 (运算, 原型). 加法, `next`, 部分和的极限, 各层的 Ω 树, 第 0 层的嵌入 `ι`, 上折 `Up`; 每个运算与它的单调性 (必要时还有 "非零") 互递归, 因为造 ℕ 极限要交相邻项的步进.
> "保持合法" 不再是定理, 是这些运算的类型. `next`, `Up` 多收一个 "底非零" 的证明.
> 不否定什么. 折叠在 `YiLegFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLegOps where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)

open import OCF.Lean.YiLegBlock
```

## 一层之内的运算

```agda
iter : {A : Set} → (A → A) → A → ℕ → A
iter f a zero    = a
iter f a (suc n) = f (iter f a n)

module _ {S : Sg} where

  infixl 6 _+_
  mutual
    _+_ : T S → T S → T S
    x + zero       = x
    x + suc y      = suc (x + y)
    x + lim f a    = lim (λ n → x + f n) (λ n → +-mono x (a n))
    x + Ω p g      = Ω p (λ z → x + g z)
    x + up y c w e = up (x + y) c w e

    +-mono : (c : T S) {a b : T S} → Lt S a b → Lt S (c + a) (c + b)
    +-mono c ◃s           = ◃s
    +-mono c (◃l n)       = ◃l n
    +-mono c ◃w           = ◃w
    +-mono c (◃u x k y e) = ◃u (c + x) k y e
    +-mono c (◃c x k d)   = ◃c (c + x) k d
    +-mono c (◃t d e)     = ◃t (+-mono c d) (+-mono c e)

  nextA : (b : T S) → Lt S zero b → (n : ℕ) → Lt S (iter (b +_) b n) (iter (b +_) b (suc n))
  nextA b nz zero    = +-mono b nz
  nextA b nz (suc n) = +-mono b (nextA b nz n)

  next : (b : T S) → Lt S zero b → T S
  next b nz = lim (iter (b +_) b) (nextA b nz)

  cum : (ℕ → T S) → ℕ → T S
  cum F zero    = F zero
  cum F (suc n) = cum F n + F (suc n)

  limc : (F : ℕ → T S) → ((n : ℕ) → Lt S zero (F n)) → T S
  limc F nz = lim (cum F) (λ n → +-mono (cum F n) (nz (suc n)))

  zl : (x : T S) → (zero ≡ x) ⊎ Lt S zero x
  zl zero = inj₁ refl
  zl (suc x) with zl x
  ... | inj₁ refl = inj₂ ◃s
  ... | inj₂ d    = inj₂ (◃t d ◃s)
  zl (lim f a) with zl (f zero)
  ... | inj₁ e = inj₂ (subst (λ v → Lt S v (lim f a)) (sym e) (◃l zero))
  ... | inj₂ d = inj₂ (◃t d (◃l zero))
  zl (Ω p g) with zl (g (b₀ S p))
  ... | inj₁ e = inj₂ (subst (λ v → Lt S v (Ω p g)) (sym e) ◃w)
  ... | inj₂ d = inj₂ (◃t d ◃w)
  zl (up x c y e) with zl x
  ... | inj₁ refl = inj₂ (◃u zero c y e)
  ... | inj₂ d    = inj₂ (◃t d (◃u x c y e))

  z◃s : (x : T S) → Lt S zero (suc x)
  z◃s x with zl x
  ... | inj₁ refl = ◃s
  ... | inj₂ d    = ◃t d ◃s

  ¬◃z : {x : T S} → Lt S x zero → ⊥
  ¬◃z (◃t d e) = ¬◃z e
```

## 各层的 Ω 树与第 0 层的嵌入

```agda
mutual
  Ωt : (ℓ : L) → Tr ℓ
  cumΩ : (g : ℕ → L) → ℕ → Tr (lim g)
  Ωt-nz : (ℓ : L) → ℓ ⊢ zero ◃ Ωt ℓ

  cumΩ g zero    = up zero zero (Ωt (g zero)) (Ωt-nz (g zero))
  cumΩ g (suc n) = up (cumΩ g n) (suc n) (Ωt (g (suc n))) (Ωt-nz (g (suc n)))

  Ωt zero     = suc zero
  Ωt (suc a)  = Ω (inj₁ tt) (λ c → up zero tt (suc c) (z◃s c))
  Ωt (lim g)  = lim (cumΩ g) (λ n → ◃u (cumΩ g n) (suc n) (Ωt (g (suc n))) (Ωt-nz (g (suc n))))
  Ωt (Ωₗ k h) = Ω (inj₁ (inj₁ tt)) (λ c → up zero c (Ωt (h c)) (Ωt-nz (h c)))

  Ωt-nz zero     = ◃s
  Ωt-nz (suc a)  = ◃t (◃u zero tt (suc zero) (z◃s zero)) ◃w
  Ωt-nz (lim g)  = ◃t (◃u zero zero (Ωt (g zero)) (Ωt-nz (g zero))) (◃l zero)
  Ωt-nz (Ωₗ k h) = ◃t (◃u zero zero (Ωt (h zero)) (Ωt-nz (h zero))) ◃w

mutual
  ι : (j : L) → Tr zero → Tr j
  ι j zero      = zero
  ι j (suc x)   = suc (ι j x)
  ι j (lim f a) = lim (λ n → ι j (f n)) (λ n → ι-mono j (a n))
  ι j (Ω () _)
  ι j (up _ () _ _)

  ι-mono : (j : L) {a b : Tr zero} → zero ⊢ a ◃ b → j ⊢ ι j a ◃ ι j b
  ι-mono j ◃s       = ◃s
  ι-mono j (◃l n)   = ◃l n
  ι-mono j (◃w {p = ()})
  ι-mono j (◃u _ () _ _)
  ι-mono j (◃c _ () _)
  ι-mono j (◃t d e) = ◃t (ι-mono j d) (ι-mono j e)
```

## 上折: 孩子层的树折进本层

下行链 `Dn`, 槽位搬运 `mv` (分支类型不变), 与 `YiUpBlock` 同文. 搬运把第一分支送到第一分支 (`mvFirst`).

```agda
chP : (j : L) (c : Ch j) → Pos (chL j c) → Pos j
chP (suc a)  _ p = inj₂ p
chP (lim g)  n p = n , inj₂ p
chP (Ωₗ k h) c p = inj₂ (c , inj₂ p)

chBr : (j : L) (c : Ch j) (p : Pos (chL j c)) → Br j (chP j c p) → Br (chL j c) p
chBr (suc a)  _ p z = z
chBr (lim g)  n p z = z
chBr (Ωₗ k h) c p z = z

chFirst : (j : L) (c : Ch j) (p : Pos (chL j c)) → chBr j c p (br0 j (chP j c p)) ≡ br0 (chL j c) p
chFirst (suc a)  _ p = refl
chFirst (lim g)  n p = refl
chFirst (Ωₗ k h) c p = refl

data Dn (ℓ : L) : L → Set where
  stop : Dn ℓ ℓ
  down : ∀ {j} → Dn ℓ j → (c : Ch j) → Dn ℓ (chL j c)

mv : ∀ {ℓ j} → Dn ℓ j → Pos j → Pos ℓ
mv stop           p = p
mv (down {j} d c) p = mv d (chP j c p)

mvBr : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) → Br ℓ (mv d p) → Br j p
mvBr stop           p z = z
mvBr (down {j} d c) p z = chBr j c p (mvBr d (chP j c p) z)

mvFirst : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) → mvBr d p (br0 ℓ (mv d p)) ≡ br0 j p
mvFirst stop           p = refl
mvFirst (down {j} d c) p = trans (cong (chBr j c p) (mvFirst d (chP j c p))) (chFirst j c p)
```

上折与它的单调性, 非零互递归. 零的像是底 b; 结点保留, 槽位搬进 ℓ; 孩子里的 `up x c y` 沿链再下一层, 底是 x 的上折.

```agda
mutual
  Up : ∀ {ℓ} (j : L) → Dn ℓ j → (b : Tr ℓ) → ℓ ⊢ zero ◃ b → Tr j → Tr ℓ
  Up j        d b nb zero      = b
  Up j        d b nb (suc y)   = next (Up j d b nb y) (Up-nz j d b nb y)
  Up j        d b nb (lim f a) = lim (λ n → Up j d b nb (f n)) (λ n → Up-mono j d b nb (a n))
  Up j        d b nb (Ω p g)   = Ω (mv d p) (λ z → Up j d b nb (g (mvBr d p z)))
  Up (suc a)  d b nb (up y _ y′ _) = Up a (down d tt) (Up (suc a) d b nb y) (Up-nz (suc a) d b nb y) y′
  Up (lim g)  d b nb (up y n y′ _) = Up (g n) (down d n) (Up (lim g) d b nb y) (Up-nz (lim g) d b nb y) y′
  Up (Ωₗ k h) d b nb (up y c y′ _) = Up (h c) (down d c) (Up (Ωₗ k h) d b nb y) (Up-nz (Ωₗ k h) d b nb y) y′
  Up zero     d b nb (up y () _ _)

  Up-nz : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) (y : Tr j) → ℓ ⊢ zero ◃ Up j d b nb y
  Up-nz j        d b nb zero      = nb
  Up-nz j        d b nb (suc y)   = ◃t (Up-nz j d b nb y) (◃l zero)
  Up-nz j        d b nb (lim f a) = ◃t (Up-nz j d b nb (f zero)) (◃l zero)
  Up-nz {ℓ} j    d b nb (Ω p g)   = ◃t (Up-nz j d b nb (g (mvBr d p (br0 ℓ (mv d p))))) ◃w
  Up-nz (suc a)  d b nb (up y _ y′ _) = Up-nz a (down d tt) (Up (suc a) d b nb y) (Up-nz (suc a) d b nb y) y′
  Up-nz (lim g)  d b nb (up y n y′ _) = Up-nz (g n) (down d n) (Up (lim g) d b nb y) (Up-nz (lim g) d b nb y) y′
  Up-nz (Ωₗ k h) d b nb (up y c y′ _) = Up-nz (h c) (down d c) (Up (Ωₗ k h) d b nb y) (Up-nz (Ωₗ k h) d b nb y) y′
  Up-nz zero     d b nb (up y () _ _)

  Up-mono : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) {x y : Tr j}
          → j ⊢ x ◃ y → ℓ ⊢ Up j d b nb x ◃ Up j d b nb y
  Up-mono j d b nb ◃s     = ◃l zero
  Up-mono j d b nb (◃l n) = ◃l n
  Up-mono {ℓ} j d b nb (◃w {p = p} {g = g}) =
    subst (λ t → ℓ ⊢ Up j d b nb (g t) ◃ Ω (mv d p) (λ z → Up j d b nb (g (mvBr d p z)))) (mvFirst d p) ◃w
  Up-mono (suc a)  d b nb (◃u x _ y e) = Up-mono a (down d tt) (Up (suc a) d b nb x) (Up-nz (suc a) d b nb x) e
  Up-mono (lim g)  d b nb (◃u x n y e) = Up-mono (g n) (down d n) (Up (lim g) d b nb x) (Up-nz (lim g) d b nb x) e
  Up-mono (Ωₗ k h) d b nb (◃u x c y e) = Up-mono (h c) (down d c) (Up (Ωₗ k h) d b nb x) (Up-nz (Ωₗ k h) d b nb x) e
  Up-mono zero     d b nb (◃u x () y e)
  Up-mono (suc a)  d b nb (◃c x _ r) = Up-mono a (down d tt) (Up (suc a) d b nb x) (Up-nz (suc a) d b nb x) r
  Up-mono (lim g)  d b nb (◃c x n r) = Up-mono (g n) (down d n) (Up (lim g) d b nb x) (Up-nz (lim g) d b nb x) r
  Up-mono (Ωₗ k h) d b nb (◃c x c r) = Up-mono (h c) (down d c) (Up (Ωₗ k h) d b nb x) (Up-nz (Ωₗ k h) d b nb x) r
  Up-mono zero     d b nb (◃c x () r)
  Up-mono j d b nb (◃t e f) = ◃t (Up-mono j d b nb e) (Up-mono j d b nb f)
```

自身行用的一步上折, 按层号的形状写出 (孩子树的类型随之算出).

```agda
Upc : (ℓ : L) (c : Ch ℓ) (b : Tr ℓ) → ℓ ⊢ zero ◃ b → ChT ℓ c → Tr ℓ
Upc (suc a)  c b nb y = Up a (down stop c) b nb y
Upc (lim g)  n b nb y = Up (g n) (down stop n) b nb y
Upc (Ωₗ k h) c b nb y = Up (h c) (down stop c) b nb y

Upc-nz : (ℓ : L) (c : Ch ℓ) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) (y : ChT ℓ c) → ℓ ⊢ zero ◃ Upc ℓ c b nb y
Upc-nz (suc a)  c b nb y = Up-nz a (down stop c) b nb y
Upc-nz (lim g)  n b nb y = Up-nz (g n) (down stop n) b nb y
Upc-nz (Ωₗ k h) c b nb y = Up-nz (h c) (down stop c) b nb y

Upc-mono : (ℓ : L) (c : Ch ℓ) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) {y′ y : ChT ℓ c}
         → RCh ℓ c y′ y → ℓ ⊢ Upc ℓ c b nb y′ ◃ Upc ℓ c b nb y
Upc-mono (suc a)  c b nb r = Up-mono a (down stop c) b nb r
Upc-mono (lim g)  n b nb r = Up-mono (g n) (down stop n) b nb r
Upc-mono (Ωₗ k h) c b nb r = Up-mono (h c) (down stop c) b nb r

Upc-base : (ℓ : L) (c : Ch ℓ) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) (y : ChT ℓ c)
         → RCh ℓ c (chZ ℓ c) y → ℓ ⊢ b ◃ Upc ℓ c b nb y
Upc-base (suc a)  c b nb y e = Up-mono a (down stop c) b nb e
Upc-base (lim g)  n b nb y e = Up-mono (g n) (down stop n) b nb e
Upc-base (Ωₗ k h) c b nb y e = Up-mono (h c) (down stop c) b nb e
```
