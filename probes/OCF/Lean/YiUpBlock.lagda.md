# 上折: 孩子层的树折进本层

> 判决: 成品候选 (块的增量). 下行链 `Dn ℓ j` (从 ℓ 逐次取孩子到 j), 槽位沿链搬进 ℓ (`mv`, 分支类型不变, `mvBr` 每一情形都是恒等), 上折 `Up j d b : Tr j → Tr ℓ`.
> 上折: 零的像是底 b; 后继取 `next`; ℕ 极限逐项; 结点保留, 槽位搬进 ℓ, 分支继续上折; 孩子里的 `up x c y` 沿链再下一层, 底是 x 的上折.
> 不否定什么. 不比较孩子, 不读层号; 折叠在 `YiUpFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (next)
```

## 孩子的槽位是本层的槽位

```agda
chP : (j : L) (c : Ch j) → Pos (chL j c) → Pos j
chP (suc a)  _ p = inj₂ p
chP (lim g)  n p = n , inj₂ p
chP (Ωₗ k h) c p = inj₂ (c , inj₂ p)

chBr : (j : L) (c : Ch j) (p : Pos (chL j c)) → Br j (chP j c p) → Br (chL j c) p
chBr (suc a)  _ p z = z
chBr (lim g)  n p z = z
chBr (Ωₗ k h) c p z = z
```

## 下行链与槽位搬运

```agda
data Dn (ℓ : L) : L → Set where
  stop : Dn ℓ ℓ
  down : ∀ {j} → Dn ℓ j → (c : Ch j) → Dn ℓ (chL j c)

mv : ∀ {ℓ j} → Dn ℓ j → Pos j → Pos ℓ
mv stop       p = p
mv (down {j} d c) p = mv d (chP j c p)

mvBr : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) → Br ℓ (mv d p) → Br j p
mvBr stop       p z = z
mvBr (down {j} d c) p z = chBr j c p (mvBr d (chP j c p) z)
```

## 上折

对孩子层的树递归; `up` 的三行只是按层号的形状读出孩子树的类型.

```agda
Up : ∀ {ℓ} (j : L) → Dn ℓ j → Tr ℓ → Tr j → Tr ℓ
Up j        d b zero    = b
Up j        d b (suc y) = next (Up j d b y)
Up j        d b (lim f) = lim (λ n → Up j d b (f n))
Up j        d b (Ω p g) = Ω (mv d p) (λ z → Up j d b (g (mvBr d p z)))
Up (suc a)  d b (up y _ y′) = Up a (down d tt) (Up (suc a) d b y) y′
Up (lim g)  d b (up y n y′) = Up (g n) (down d n) (Up (lim g) d b y) y′
Up (Ωₗ k h) d b (up y c y′) = Up (h c) (down d c) (Up (Ωₗ k h) d b y) y′
Up zero     d b (up y () _)

Upc : (ℓ : L) (c : Ch ℓ) → Tr ℓ → ChT ℓ c → Tr ℓ
Upc ℓ c b y = Up (chL ℓ c) (down stop c) b (chT ℓ c y)
```
