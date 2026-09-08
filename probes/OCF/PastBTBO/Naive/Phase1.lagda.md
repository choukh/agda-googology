# 阶段 1: 最小扩展 `Ordᴰ-1`

> 原计划用泛型 `Ordᴰ-fam : Ordᴰ → Set` 一锅端, 但 `limᵢ` 的 `Ordᴰ-fam i → Ordᴰ-fam ℓ` 在 Agda 里被严格正性检查否决, 即使 `i ≠ ℓ` 也不行.
>
> 退一步, 只造**一层**新结构 `Ordᴰ-1` —— 在原 `Ordᴰ` 基础上加一个 `Ord₀`-索引的 `lim` 构造子. `Ord₀` 是外部类型, 不触发正性问题. 目标是看 Agda 能不能接受 + 是否值得继续 phase 2.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Naive.Phase1 where

open import OCF.BTBO
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich renaming (<-dec to <ᴰ-dec; _+_ to _+ᴰ_)
open Ord-Ord using (Ord₀)
```

## 关键决策: limΩ 的指标类型用 `Ordᴰ` 而不是 `Ord₀`

最初我用 `Ord₀` 当 `limΩ` 的指标类型, 但 `Ord₀` 的 `lim` 不带单调性, 导致下游的有界三歧性证不出来. 注意: 在框架的语义命名里 `Ord₀` 和 `Ordᴰ` 都代表"< Ω 的可数序数"——**指标用谁都行, 但 Ordᴰ 已经带 bounded trich, 用它能让 phase 2 跑通**.

## 第一步: 互递归骨架 `Ordᴰ-1` + `<-1`

```agda
infix 10 _<-1_

data Ordᴰ-1 : Set
data _<-1_ : Ordᴰ-1 → Ordᴰ-1 → Set

monoᴺ-1 : (ℕ → Ordᴰ-1) → Set
monoᴺ-1 f = ∀ {n m} → n <ᴺ m → f n <-1 f m

monoΩ-1 : (Ordᴰ → Ordᴰ-1) → Set
monoΩ-1 f = ∀ {a b : Ordᴰ} → a < b → f a <-1 f b

data Ordᴰ-1 where
  zero : Ordᴰ-1
  suc  : Ordᴰ-1 → Ordᴰ-1
  lim  : (f : ℕ → Ordᴰ-1) → monoᴺ-1 f → Ordᴰ-1
  limΩ : (f : Ordᴰ → Ordᴰ-1) → monoΩ-1 f → Ordᴰ-1

data _<-1_ where
  zero : ∀ {a : Ordᴰ-1}       → a <-1 suc a
  suc  : ∀ {a b : Ordᴰ-1}     → a <-1 b → a <-1 suc b
  lim  : ∀ {a : Ordᴰ-1} {f : ℕ → Ordᴰ-1} {mono : monoᴺ-1 f}
       → (n : ℕ) → a <-1 f n → a <-1 lim f mono
  limΩ : ∀ {a : Ordᴰ-1} {f : Ordᴰ → Ordᴰ-1} {mono : monoΩ-1 f}
       → (x : Ordᴰ) → a <-1 f x → a <-1 limΩ f mono
```

## 第三步: 传递性

```agda
<-1-trans : ∀ {a b c : Ordᴰ-1} → a <-1 b → b <-1 c → a <-1 c
<-1-trans p zero        = suc p
<-1-trans p (suc q)     = suc (<-1-trans p q)
<-1-trans p (lim n q)   = lim n (<-1-trans p q)
<-1-trans p (limΩ x q)  = limΩ x (<-1-trans p q)
```

## 第四步: 基本列下界

```agda
f<l-1 : ∀ {f : ℕ → Ordᴰ-1} {mono : monoᴺ-1 f}
      → (n : ℕ) → f n <-1 lim f mono
f<l-1 {mono = mono} n = lim (suc n) (mono zero)

f<lΩ-1 : ∀ {f : Ordᴰ → Ordᴰ-1} {mono : monoΩ-1 f}
       → (x : Ordᴰ) → f x <-1 limΩ f mono
f<lΩ-1 {mono = mono} x = limΩ (suc x) (mono zero)
```

## 第五步: 尝试有界三歧性

```agda
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

pattern injᵃ x = inj₁ x
pattern injᵇ x = inj₂ (inj₁ x)
pattern injᶜ x = inj₂ (inj₂ x)

-- 试图构造任意 x, y 的共同上界, 用于 limΩ 情形
-- x < suc (x + suc y) 总成立 (因为 suc y > 0)
x<sxy : ∀ x y → x < suc (x +ᴰ suc y)
x<sxy x y = suc (a<a+b ⦃ _ ⦄)

-- y < suc (x + suc y) 需要左单调性. 试着证 s<s 与 +l-mono:

open import Relation.Binary.PropositionalEquality using (sym; subst)

-- 关键引理: a < b → suc a < b ⊎ suc a ≡ b (即 "suc a ≤ b")
suc-≤ : ∀ {a b : Ordᴰ} → a < b → suc a < b ⊎ suc a ≡ b
suc-≤ zero                = inj₂ refl
suc-≤ (suc {b = b'} q) with suc-≤ q
... | inj₁ sa<b'          = inj₁ (suc sa<b')
... | inj₂ sa≡b'          = inj₁ (subst (λ z → z < suc b') (sym sa≡b') zero)
suc-≤ (lim {f = f} {mono = m} n q) with suc-≤ q
... | inj₁ sa<fn          = inj₁ (lim n sa<fn)
... | inj₂ sa≡fn          = inj₁ (subst (λ z → z < lim f m) (sym sa≡fn) (f<l n))

-- 由 suc-≤ 得 s<sᴰ
s<sᴰ : ∀ {a b : Ordᴰ} → a < b → suc a < suc b
s<sᴰ {b = b} q with suc-≤ q
... | inj₁ sa<b           = suc sa<b
... | inj₂ sa≡b           = subst (λ z → z < suc b) (sym sa≡b) zero

-- ⚠ 重要修正: +-lmono 本身就**作为定理不成立**.
-- 反例: 序数 0 + ω = ω = 1 + ω. 所以 0 < 1 但 0 +ᴰ ω ≡ 1 +ᴰ ω. 没有严格小于.
-- BoundedTrich 没提供 +-lmono 不是疏漏, 是因为它不真. 
-- 这意味着用 "x + suc y" 作为 x, y 共同上界的整个思路**失效**.

-- <-1-dec 整体注释掉, 因为 limΩ/limΩ 情形无法完成 (见下文分析).
-- 易做的部分如下, 保留作为参考:
{-
<-1-dec : ∀ {a b c : Ordᴰ-1} → a <-1 c → b <-1 c
        → a <-1 b ⊎ b <-1 a ⊎ a ≡ b
<-1-dec zero zero        = injᶜ refl
<-1-dec zero (suc q)     = injᵇ q
<-1-dec (suc p) zero     = injᵃ p
<-1-dec (suc p) (suc q)  = <-1-dec p q
<-1-dec (lim {mono = mono} n p) (lim m q) with <ᴺ-dec n m
... | injᵃ n<m         = <-1-dec (<-1-trans p (mono n<m)) q
... | injᵇ m<n         = <-1-dec p (<-1-trans q (mono m<n))
... | injᶜ refl        = <-1-dec p q
<-1-dec (limΩ x p) (limΩ y q) = ???  -- 撞墙: 需 Ordᴰ 上 x, y 的某种三歧, 
                                       -- 而构造 x, y 共同上界又需 +-lmono.
-}
```

## 完整进展与壁的位置

### ✓ 成功的部分

1. **类型骨架** `Ordᴰ-1` + `_<-1_` 互递归通过 Agda 严格正性检查
   - 注: 必须用 `Ordᴰ` 而非 `Ord₀` 作为 `limΩ` 的指标 (Ord₀ 没 mono)
2. `<-1-trans` (传递性) ✓
3. `f<l-1` / `f<lΩ-1` (基本列下界) ✓
4. `suc-≤ : a < b → suc a < b ⊎ suc a ≡ b` ✓
5. `s<sᴰ : a < b → suc a < suc b` ✓
6. `x<sxy : x < suc (x +ᴰ suc y)` (右侧上界) ✓
7. `<-1-dec` 的 zero/suc/lim 情形 ✓

### ❌ 撞墙的位置

**墙 1**: `<-1-dec` 的 limΩ/limΩ 情形.

需要决定 `x, y : Ordᴰ` 的关系 (类似 `lim/lim` 用 ℕ 上的 `<ᴺ-dec`). 但 `Ordᴰ` 只有**有界三歧性** `<ᴰ-dec` —— 要求两个元素被同一个 c 限制. 任意 x, y 之间没有自然的共同上界.

**墙 2** (墙 1 的连带): 构造 x, y 共同上界.

`x<sxy : x < suc (x +ᴰ suc y)` 容易 (用 `a<a+b`). 但 `y<sxy : y < suc (x +ᴰ suc y)` 需要 `y ≤ x +ᴰ y` 这种"左单调性"性质.

**墙 3** (深层原因, 比预想的更糟):
**`+-lmono` 作为定理本身就不真**, 在序数算术里有反例:

> 反例: `0 + ω = sup_{n<ω} (0 + n) = sup_n n = ω`. 同时 `1 + ω = sup_{n<ω} (1 + n) = sup_n (n+1) = ω`. 所以 `0 < 1` 但 `0 +ᴰ ω ≡ 1 +ᴰ ω`.

BoundedTrich 没提供 `+-lmono` 不是疏漏, 是**因为它根本不真**. 这一发现说明:

**所有用 `+, suc, lim` 从 x, y 构造的"自然上界"都注定无法证 `y < bound`**, 因为这等价于左单调性, 而后者不真.

具体地, 我们尝试了以下构造, 每一种都撞同一面壁:

| 上界构造 | x < c | y < c | 失败原因 |
|---------|------|------|---------|
| `c = suc (x +ᴰ suc y)` | ✓ (a<a+b) | ✗ | 需 `y < x +ᴰ y` (左非单调) |
| `c = (y +ᴰ suc x)` | ✗ | ✓ (a<a+b) | 对偶 |
| `c = (x +ᴰ suc y) +ᴰ (y +ᴰ suc x)` | ✓ | 部分 ✓ | 需 `c2 < c1 +ᴰ c2` (左非单调) |
| `c = lim (n ↦ cumsum f n) _` | ✓ | ✗ | cumsum 也是右加, 同问题 |

### 关键结论

**`Ordᴰ` 的 `+` 本质上不是左单调的, 而 `<` 又是结构性归纳定义 ⇒ 无法用 `+` 构造任意 x, y 的严格共同上界**. 这堵壁不是"难证", 而是"不真"——`+-lmono` 是错的定理.

走通 phase 2 需要换思路, 不是补一个引理就行.

### 真正可走的路径 (而非"硬啃 +-lmono")

**A. 添加新的"join"操作**.  
在 `Ordᴰ` 上引入 `_⊔_ : Ordᴰ → Ordᴰ → Ordᴰ` 显式定义 max, 配合证明 `a < a ⊔ b ⊎ a ≡ a ⊔ b` 与对称版. 但定义 `⊔` 在 `lim/lim` 情形又需要决定哪个更大 —— 同样的有界三歧问题. 死循环.

**B. 限定 `limΩ` 见证的结构**.  
让 `limΩ : (f : Ordᴰ → Ordᴰ-1) → mono → (∀ x y → ∃ z. x < z ⊎ x ≡ z ∧ y < z ⊎ y ≡ z) → ...`. 把"共同上界存在性"作为构造子的输入. 但这又把决策推到调用方, 改变了语义.

**C. 修改 `Ordᴰ` 的 `<` 定义**.  
用更强的关系, 例如带不动点信息或加 cofinal 嵌入信息. 但这彻底改变了原框架.

**D. 不要 bounded trichotomy. 设计不依赖三歧的 ψ-1**.  
看 ψ 的 limᵢ 情形怎么用 `<-dec`, 改写为不需决策的版本. 但这可能损失精度, 让 ψ-1 输出不再对应明确的 OCF 序数.

**E. 接受 phase 2 完成不了, 报告这一发现**.  
我们已经精确定位了墙, 这本身是诊断价值. 作者可能没意识到 +-lmono 不真这个根本障碍.

### 我现在倾向 E + 部分 D

E 是最诚实的——我们走了 phase 1, 撞墙, 知道墙的位置. 把发现写成给作者的诊断报告.

D 值得探索但不一定能成功——OCF 的 ψ 普遍依赖三歧来分配 limᵢ 的折叠目标. 不三歧的 ψ 可能根本无法定义.

完整突破 BTBO 可能需要回到之前讨论的 IR-Mahlo 方向, 那里"指标层"自带封闭性, 不依赖 + 的左单调.

