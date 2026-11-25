# YiKB 块: 层号带基底与下行路径的上确界结点

> 空白页独立样本 (只导入标准库). 层号 `L`: 零, 后继, 上确界结点 `sp b i g w` (基底 `b`, 下标 ℕ 或基底的一个位置, 孩子层号 `g x`, 字面下行路径 `w x : g x ↘ b`); 树 `T ℓ` 是一个泛型布劳威尔树, 位置, 分支域, 叶由 `ℓ` 递归算出.
> 做了什么: 归纳-递归的块, "树当层号" `lv`, 塔 `tw` 与 `Λ`. 合法性就是类型, 没有另设谓词.
> 不否定什么. 折叠在 [YiKBFold](YiKBFold.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKBBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
```

## 泛型树

`br p h` 是全值分支 (值落在整个类型里), `lf` 是叶. `Pk` 是不带 η 的对.

```agda
data Tr (P : Set) (D : P → Set) (F : Set) : Set where
  zero : Tr P D F
  suc  : Tr P D F → Tr P D F
  lim  : (ℕ → Tr P D F) → Tr P D F
  br   : (p : P) → (D p → Tr P D F) → Tr P D F
  lf   : F → Tr P D F

data Pk (A : Set) (B : A → Set) : Set where
  pk : (x : A) → B x → Pk A B

dom⁺ : {P : Set} → Set → (P → Set) → ⊤ ⊎ P → Set
dom⁺ X D (inj₁ _) = X
dom⁺ X D (inj₂ p) = D p
```

## 层号, 路径, 树

`ℓ ↘ a`: 从 `ℓ` 到 `a` 的字面下行路径. `ss`, `sb` 各退一层 (后继退到前驱, 上确界结点退到基底); `ch x` 落进上确界结点的第 `x` 个孩子. 路径只指定一个孩子, 不比较两个孩子.
上确界结点的树: 全值分支只开在基底及其位置上; 孩子里的内容是叶 `pk x t`, 整个待在孩子 `x` 的类型里. 后继层的叶是前驱层的树.

```agda
data L : Set
data _↘_ : L → L → Set
Pos : L → Set
Dom : (ℓ : L) → Pos ℓ → Set
Lf  : L → Set
Idx : L → Set
Ix  : (b : L) → Idx b → Set
T   : L → Set

data L where
  z  : L
  s  : L → L
  sp : (b : L) (i : Idx b) (g : Ix b i → L) (w : ∀ x → g x ↘ b) → L

data _↘_ where
  rf : ∀ {ℓ} → ℓ ↘ ℓ
  ss : ∀ {ℓ a} → ℓ ↘ a → s ℓ ↘ a
  sb : ∀ {b i g w a} → b ↘ a → sp b i g w ↘ a
  ch : ∀ {ℓ b i g w} x → ℓ ↘ g x → ℓ ↘ sp b i g w

T ℓ = Tr (Pos ℓ) (Dom ℓ) (Lf ℓ)

Pos z             = ⊥
Pos (s ℓ)         = ⊤ ⊎ Pos ℓ
Pos (sp b i g w)  = ⊤ ⊎ Pos b

Dom z            = λ ()
Dom (s ℓ)        = dom⁺ (T ℓ) (Dom ℓ)
Dom (sp b i g w) = dom⁺ (T b) (Dom b)

Lf z            = ⊥
Lf (s ℓ)        = T ℓ
Lf (sp b i g w) = Pk (Ix b i) (λ x → T (g x))

Idx b = ⊤ ⊎ (⊤ ⊎ Pos b)

Ix b (inj₁ _) = ℕ
Ix b (inj₂ q) = dom⁺ (T b) (Dom b) q
```

下标的三种: ℕ (ℕ 极限), 基底自己的树 (Ω 结点, 塔用这一种), 基底的一个低位置的树.

```agda
pattern iℕ   = inj₁ tt
pattern iΩ   = inj₂ (inj₁ tt)
pattern iP p = inj₂ (inj₂ p)
pattern top  = inj₁ tt
pattern low p = inj₂ p
```

## 沿后继链的嵌入

`a ≤ˢ b`: `b` 是 `a` 上若干次后继. 位置字面搬上去, 分支域不变.

```agda
data _≤ˢ_ (a : L) : L → Set where
  rf′ : a ≤ˢ a
  ss′ : ∀ {ℓ} → a ≤ˢ ℓ → a ≤ˢ s ℓ

lift : ∀ {a b} → a ≤ˢ b → Pos a → Pos b
lift rf′     p = p
lift (ss′ e) p = inj₂ (lift e p)

coe : ∀ {a b} (e : a ≤ˢ b) (p : Pos a) → Dom b (lift e p) → Dom a p
coe rf′     p x = x
coe (ss′ e) p x = coe e p x

pre : ∀ {a b} → s a ≤ˢ b → a ≤ˢ b
pre rf′     = ss′ rf′
pre (ss′ e) = ss′ (pre e)
```

## 树当层号

`lv e t` 读作 "`b` 加 `t`", 带一条回到 `b` 的路径 `lv↘`. 零, 后继, 极限, 分支逐构造子对应; 后继层的叶走进前驱层; 上确界结点的叶 `pk x t` 取孩子 `x` 上方的层号, 路径经 `ch x` 回来 (不要求它字面高于 `b`); 隔着后继的上确界叶粗略记作 `b`.

```agda
lv  : ∀ {a b} → a ≤ˢ b → T a → L
lv↘ : ∀ {a b} (e : a ≤ˢ b) (t : T a) → lv e t ↘ b

lv {b = b} e zero     = b
lv         e (suc t)  = s (lv e t)
lv {b = b} e (lim f)  = sp b iℕ (λ n → lv e (f n)) (λ n → lv↘ e (f n))
lv {b = b} e (br p h) = sp b (iP (lift e p)) (λ x → lv e (h (coe e p x))) (λ x → lv↘ e (h (coe e p x)))
lv {a = s a}          e       (lf t)        = lv (pre e) t
lv {a = sp _ _ g _}   rf′     (lf (pk x t)) = lv {b = g x} rf′ t
lv {a = sp _ _ _ _} {b} (ss′ e) (lf _)      = b

lv↘ e zero     = rf
lv↘ e (suc t)  = ss (lv↘ e t)
lv↘ e (lim f)  = sb rf
lv↘ e (br p h) = sb rf
lv↘ {a = s a}        e       (lf t)        = lv↘ (pre e) t
lv↘ {a = sp _ _ _ _} rf′     (lf (pk x t)) = ch x (lv↘ rf′ t)
lv↘ {a = sp _ _ _ _} (ss′ e) (lf _)        = rf

lev : ∀ {b} → T b → L
lev = lv rf′
```

## 塔与 Λ

`tw (n+1)` 是以 `tw n` 为基底与下标层的 Ω 结点, 孩子 `c` 的层号是 `lev c`. `Λ` 是 `tw` 的 ℕ 上确界.

```agda
tw : ℕ → L
tw zero    = z
tw (suc n) = sp (tw n) iΩ lev (lv↘ rf′)

tw↘ : ∀ n → tw n ↘ z
tw↘ zero    = rf
tw↘ (suc n) = sb (tw↘ n)

Λ : L
Λ = sp z iℕ tw tw↘
```
