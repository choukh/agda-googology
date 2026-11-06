# 可数层的对角, 第三轮 (三): `Lev` 种类在第 1 级进层; 缺的一块缩到 $k\ge1$

> 不含记号. 入口 [DiagK3](DiagK3.lagda.md).
>
> - **`lev₁`, `lev₂`** (定理): 在 `L′ 2` 的一个合法世界里, 第 1 级级顶 `λh 1` 下面有层, 其 $\Omega$-分支的种类是 `L′ 1` 的 `Lev` 种类 (`head₁`, `head₂`, `refl`). 坐标类型分别是 $H_0$ (`E₁`) 与 `HB S₁` (`E₂`). 所以 [DiagK3Zero](DiagK3Zero.lagda.md) 的投影到第 1 级就不再无损, `Lev` 种类的回灌从第 1 级起是真问题.
> - **`Fold₊`, `mkFd`** (定义): 第 0 级用 `DiagK3Zero.fold₀`, 只缺 $k\ge1$ 的级. `Tᴰ₊` 是条件于 `Fold₊` 的候选闭项, 合法 (`Lg-Tᴰ₊`), 其第 0 项就是 `t₀` (`t-zero`, `refl`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagK3One where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNStage using (L′; two; dW; dWLev)
open import OCF.Align.DiagKTop using (λh; towerL′; LevelFold; module Top)
open import OCF.Align.DiagK3Grow using (embL)
open import OCF.Align.DiagK3Zero using (fold₀; Lg-fold₀; lgdWLev; t₀; lλ₀)
```

## §1 最小世界合法, 一切 $k$

```agda
lgdW : ∀ k → LgW (L′ k) (dW k)
lgdW zero = tt
lgdW (suc k) true = lgdW k , tt
lgdW (suc k) false = lgdWLev (Ωtop (L′ k))
```

## §2 第 1 级级顶下的 `Lev` 种类

```agda
F₂ : Bool → KS
F₂ = two (step (L′ 1)) (Lev (Ωtop (L′ 1)))

ι₂ : HB (step (L′ 1)) → HB (L′ 2)
ι₂ = ι {F = F₂} true

-- L′ 1 里的两个 Lev 种类: 坐标 hs hz 与 hs (hs hz) 处的新种类
κ₁ κ₂ : K (L′ 1)
κ₁ = false , (hs hz , inj₂ tt)
κ₂ = false , (hs (hs hz) , inj₂ tt)

E₁ : E (L′ 1) κ₁ ≡ HB S₀
E₁ = refl

E₂ : E (L′ 1) κ₂ ≡ HB (step S₀)
E₂ = refl

y₁ : HB (L′ 1)
y₁ = hΩ κ₁ (λ _ → hz)

y₂ : HB (L′ 1)
y₂ = hΩ κ₂ (λ _ → hz)

lgy : ∀ κ → LgB {L′ 1} (hΩ κ (λ _ → hz))
lgy κ = (λ lw e e′ p → hself) , (λ c lc → tt)

wy : HB (L′ 1) → Wd (L′ 2)
wy y true = dW 1 , y
wy y false = dWLev (Ωtop (L′ 1))

lg-wy : ∀ κ → LgW (L′ 2) (wy (hΩ κ (λ _ → hz)))
lg-wy κ true = lgdW 1 , lgy κ
lg-wy κ false = lgdWLev (Ωtop (L′ 1))

lev₁ : ι₂ (up y₁) ⊲[ wy y₁ ] λh 1
lev₁ = hLim hself hself

lev₂ : ι₂ (up y₂) ⊲[ wy y₂ ] λh 1
lev₂ = hLim hself hself

-- 这两层的 Ω-分支的种类就是 L′ 1 的 Lev 种类 (经链分量)
head₁ : ι₂ (up y₁) ≡ hΩ (true , inj₁ κ₁) (λ _ → ι₂ (up hz))
head₁ = refl

head₂ : ι₂ (up y₂) ≡ hΩ (true , inj₁ κ₂) (λ _ → ι₂ (up hz))
head₂ = refl
```

## §3 缺的一块: 第 1 级起的折叠

```agda
record Fold₊ : Set where
  field
    foldₛ : ∀ k (Λ : HB (L′ (suc (suc k)))) → LgB Λ → A
    lgₛ   : ∀ k Λ (lΛ : LgB Λ) → Lg (foldₛ k Λ lΛ)
open Fold₊ public

mkFd : Fold₊ → LevelFold towerL′
mkFd F = record { fold = fd ; lg = lgd }
  where
  fd : ∀ k (Λ : HB (L′ (suc k))) → LgB Λ → A
  fd zero = fold₀
  fd (suc k) = foldₛ F k
  lgd : ∀ k Λ (lΛ : LgB Λ) → Lg (fd k Λ lΛ)
  lgd zero = Lg-fold₀
  lgd (suc k) = lgₛ F k

module _ (F : Fold₊) where
  open Top towerL′ (mkFd F) using (t; Tᴰ; Lg-Tᴰ; fgh)

  Tᴰ₊ : A
  Tᴰ₊ = Tᴰ

  Lg-Tᴰ₊ : Lg Tᴰ₊
  Lg-Tᴰ₊ = Lg-Tᴰ

  t-zero : t 0 ≡ t₀
  t-zero = refl
```

## §4 有损在哪里: 第二数类的增量进 `HB S₁` 的坐标, 不含新种类的节点

坐标是 `HB (step S₀)` 的那个 `Lev` 种类 (`κ₂`) 在只增长的世界里 ([DiagK3Grow](DiagK3Grow.lagda.md)) 得到的增量是 `embL (hs hz) h = up h`. 它**没有新种类 (`inj₂`) 的 $\Omega$-节点** (`noNew-emb`), 接上去也不会有新的 (`⊞-noNew`). 所以一步回灌永远跨不过新种类的一个 $\Omega$-极限; 忠实的回灌 (第 2 层的读回) 要跨. 这是 "只增长的世界对这一种类有损" 的形状证据 (定理); 它对读法的影响是判断.

```agda
NoNew : ∀ {S} → HB (step S) → Set
NoNew hz = ⊤
NoNew (hs x) = NoNew x
NoNew (hl f) = ∀ n → NoNew (f n)
NoNew (hΩ (inj₁ κ) g) = ∀ c → NoNew (g c)
NoNew (hΩ (inj₂ tt) g) = ⊥

up-noNew : ∀ {S} (h : HB S) → NoNew (up h)
up-noNew hz = tt
up-noNew (hs h) = up-noNew h
up-noNew (hl f) = λ n → up-noNew (f n)
up-noNew (hΩ κ g) = λ c → up-noNew (g c)

⊞-noNew : ∀ {S} (a b : HB (step S)) → NoNew a → NoNew b → NoNew (a ⊞ b)
⊞-noNew a hz na nb = na
⊞-noNew a (hs b) na nb = ⊞-noNew a b na nb
⊞-noNew a (hl f) na nb = λ n → ⊞-noNew a (f n) na (nb n)
⊞-noNew a (hΩ (inj₁ κ) g) na nb = λ c → ⊞-noNew a (g c) na (nb c)

-- 坐标 hs (hs hz) 处新种类的步进在 Lev (up (hs hz)) = step S₀ 里, 增量是 embL (hs hz) h
noNew-emb : ∀ h → NoNew {S₀} (embL {step S₀} (hs hz) h)
noNew-emb h = up-noNew h
