# Beyond BTBO: 一步一脚印的撞壁探索

> 目标: 不预设大方向, 只看"再往前走一步"会卡在哪里. 每条小路都尝试到撞墙为止, 把墙的位置精确定位.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Naive.Experiments where

open import OCF.BTBO
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open BoundedTrich hiding (_+_)
open Ord-Ord
```

## 实验 0: 基线 —— 框架实际跑出来是什么

> **历史脚注**: 本节最初记录的"`ψⁿ 1 = suc zero` 而非 `ω`"问题, 已在 BTBO.lagda.md 中通过把 `Ω zero` 从 `suc zero` 改为 `lim suc-iter` (即 Ord₀ 中的 ω) 修复. 现在 `ψⁿ 1 ≡ ω₀` 由 `refl` 直接成立, 链条与注释一致地落入 Buchholz ψ 量级.

但**核心结论仍然成立**: 整体收敛到何处, 在框架内**无形式化证明**, 只是作者的元层断言.

> 这是后续讨论的重要基线: 谈"BTBO = ψ(Ω_Ω)" 时, 等号意为"作者声称代表的序数", 不是 Agda 里证出的等式.

## 实验 A: "免费"变体 —— 用 `Ω + Ω` 代替 `Ω`

最朴素的"再往前一步"想法: 把迭代函数的 `Ω(ordᴰ α)` 改成 `Ω(ordᴰ α) + Ω(ordᴰ α)`, 期望对应到 `ψ(Ω_α · 2)`, 收敛到 ψ(Ω_Ω · 2) 量级.

```agda
g₁ : Ord₀ → Ord₀
g₁ α = ψ₀ (Ω (ordᴰ α) + Ω (ordᴰ α))

beyond-A : Ord₀
beyond-A = lim (iter g₁ zero)
```

**结果**: 类型检查通过. 但**这并未真正突破**:

1. `beyond-A : Ord₀`, 与 BTBO 同型. 框架没有 Ord₀ 上的 `<`, 所以无法在 Agda 里证明 `beyond-A > BTBO`.
2. 元层论证: 沿 BTBO 同样的"上确界即不动点"分析, `g₁` 的不动点对应 α = ψ_0(Ω_α + Ω_α) 的解. 这个不动点的具体值依赖 ψ_0 在 + 上的行为, 不一定大于 `α = ψ_0(Ω_α)` 的不动点.
3. 更深的问题: 即使元层上 `beyond-A` 名字叫"ψ(Ω_Ω · 2)", 该框架的 ψ 与标准 Buchholz ψ 并不相同 (见实验 0). 名字与实际行为之间存在鸿沟.

**结论**: A 不构成真正的进步. 它只是在 Ord₀ 内部生成了一个**或许**对应到更大序数的项, 但**无法在框架内证明它更大**. 这种"免费扩展"无穷多, 没有意义.

## 实验 B: 试图把 `ordᴰ` 推到 `ord-1`

`ordᴰ : Ord₀ → Ordᴰ` 是唯一的反向通道. 如果能造出 `ord-1 : Ord 1 → Ordᴰ`, 我们就能让 ψ 的输出 (高层 Ord) 直接当 Ω 的下标, 形式化地"往上一层".

```agda
-- 我们试图定义 (注释掉, 因为撞墙):
{-
ord-1 : Ord (suc zero) → Ordᴰ
ord-1 zero        = zero
ord-1 (suc a)     = suc (ord-1 a)
ord-1 (lim f)     = lim (cumsum (ord-1 ∘ f)) (cumsum-mono (ord-1 ∘ f))
ord-1 (limᵢ p f)  = ??? -- 撞墙
-}
```

**墙的精确位置**: `limᵢ p f` 中 `p : i < suc zero`. 由 Ordᴰ 的 `<` 定义, `i < suc zero` 只能由 `zero : i < suc i` (这里 i = zero) 给出, 即 `i = zero, p = zero`. 此时 `f : Ord< zero zero → Ord 1`, 即 `f : Ord₀ → Ord 1`.

这是**共尾度为 Ω 的基本列** (按 [BTBO.lagda.md:537](../../BTBO.lagda.md#L537) 的表格, Ord₀ 的上确界是 Ω). 要把它嵌入 Ordᴰ, 需要 Ordᴰ 支持 Ord₀-索引的 `lim` —— 但 Ordᴰ 的 `lim` 只接受 `ℕ → Ordᴰ`.

### "作弊"方案: 先折叠回 Ord₀

```agda
ord-1-cheat : Ord (suc zero) → Ordᴰ
ord-1-cheat a = ordᴰ (ψ₀ a)
```

**类型检查通过**, 但**没有新强度**: 我们只是把 Ord 1 → Ord 0 → Ordᴰ 走一遍, 而 Ord 1 → Ord 0 这一步就是已有的 ψ_0. `ord-1-cheat` 等价于走一次 ψ_0, 上确界仍然是 BTBO. 用 `ord-1-cheat` 替换 `ordᴰ` 重做 ψⁿ, 得到的"BTBO"和原版一样.

```agda
-- 验证 ord-1-cheat 用起来就是 ordᴰ ∘ ψ₀:
example-cheat : ∀ (a : Ord (suc zero)) → ord-1-cheat a ≡ ordᴰ (ψ₀ a)
example-cheat _ = refl
```

**结论**: B 的"作弊"方案不带来新强度. 真正的进步必须让 `limᵢ` 案例**不通过 ψ_0 折叠**就能嵌入 Ordᴰ-类的结构 —— 即 Ordᴰ 必须扩展.

## 实验 C: 给 Ord₀ 加上 `<` 序

要扩展 Ordᴰ 接受 Ord₀-索引的 `lim`, 第一步是让 `Ord₀ → Ordᴰ-类型` 的函数有**单调性**概念. 因此先给 Ord₀ 加 `<`:

```agda
infix 10 _<-Ord₀_
data _<-Ord₀_ : Ord₀ → Ord₀ → Set where
  zero : ∀ {a}     → a <-Ord₀ suc a
  suc  : ∀ {a b}   → a <-Ord₀ b → a <-Ord₀ suc b
  lim  : ∀ {a f}   → (n : ℕ) → a <-Ord₀ f n → a <-Ord₀ lim f
```

**类型检查通过**.

### 下一步: 有界三歧性

```agda
-- 我们试图证 (注释掉, 因为不可能):
{-
<-Ord₀-dec : ∀ {a b c : Ord₀} → a <-Ord₀ c → b <-Ord₀ c
           → a <-Ord₀ b ⊎ b <-Ord₀ a ⊎ a ≡ b
<-Ord₀-dec zero zero = inj₂ (inj₂ refl)
<-Ord₀-dec zero (suc q) = inj₂ (inj₁ q)
<-Ord₀-dec (suc p) zero = inj₁ p
<-Ord₀-dec (suc p) (suc q) = <-Ord₀-dec p q
<-Ord₀-dec (lim n p) (lim m q) = ??? -- 撞墙
-}
```

**墙的精确位置**: `a <-Ord₀ lim f` 与 `b <-Ord₀ lim f` 的见证分别是 `lim n p (p : a <-Ord₀ f n)` 和 `lim m q (q : b <-Ord₀ f m)`. 要决定 a vs b, 自然想法是用 ℕ 上的三歧性比较 n, m, 然后利用 `f` 的单调性把 `f n` 与 `f m` 的关系转给 a, b.

但 **Ord₀ 的 `lim f` 不携带 f 的单调性证明** ([BTBO.lagda.md:843](../../BTBO.lagda.md#L843)). f n 和 f m 之间可以是任意关系 (递增、递减、混乱). 没办法套用 Ordᴰ 的 `<-dec` 那一套 ([BTBO.lagda.md:704-707](../../BTBO.lagda.md#L704-L707)).

**这是第二面壁**: 即使补了 `<-Ord₀`, 有界三歧性也不可能成立, 因为 Ord₀ 的设计就是允许非单调基本列.

## 实验 D: 最小可行扩展轮廓

要真正绕过, 必须把 Ord ℓ 族**整族重做**, 在每个 `lim` 和 `limᵢ` 上都加上单调性证明. 这就需要互递归地定义 Ord-fam 与其 `<`:

```agda
-- 骨架 (注释掉, 仅供参考; 完整定义需 ~80 行, 加 <-trans/<-dec 再 ~120 行):
{-
mutual
  data Ordᴰ-fam : Ordᴰ → Set
  data _<-fam_  : ∀ {ℓ} → Ordᴰ-fam ℓ → Ordᴰ-fam ℓ → Set

  monoᴺ-fam : ∀ {ℓ} → (ℕ → Ordᴰ-fam ℓ) → Set
  monoᴺ-fam f = ∀ {n m} → n <ᴺ m → f n <-fam f m

  monoᵢ-fam : ∀ {ℓ i} → (p : i < ℓ) → (Ordᴰ-fam i → Ordᴰ-fam ℓ) → Set
  monoᵢ-fam {ℓ} p f = ∀ {a b} → a <-fam b → f a <-fam f b

  data Ordᴰ-fam where
    zero : ∀ {ℓ} → Ordᴰ-fam ℓ
    suc  : ∀ {ℓ} → Ordᴰ-fam ℓ → Ordᴰ-fam ℓ
    lim  : ∀ {ℓ} (f : ℕ → Ordᴰ-fam ℓ) → monoᴺ-fam f → Ordᴰ-fam ℓ
    limᵢ : ∀ {ℓ i} (p : i < ℓ) (f : Ordᴰ-fam i → Ordᴰ-fam ℓ) → monoᵢ-fam p f → Ordᴰ-fam ℓ

  data _<-fam_ where
    zero : ∀ {ℓ} {a : Ordᴰ-fam ℓ}     → a <-fam suc a
    suc  : ∀ {ℓ} {a b : Ordᴰ-fam ℓ}   → a <-fam b → a <-fam suc b
    lim  : ∀ {ℓ a f mono}             → (n : ℕ) → a <-fam f n → a <-fam (lim f mono)
    limᵢ : ∀ {ℓ i p a f mono}         → (x : Ordᴰ-fam i) → a <-fam f x → a <-fam (limᵢ p f mono)
-}
```

### 第三面壁: 有界三歧性的递归证明

即使骨架能让 Agda 接受, 接下来证 `<-fam-dec` 时, `limᵢ` 案例需要在见证类型 `Ordᴰ-fam i` 上做有界三歧. 这要求 i 层的 `<-fam-dec`. 由于 `i < ℓ`, 递归往下走, 似乎是良基的.

**但有个微妙问题**: `<-fam-dec` 要求"两个元素被同一个上界 c 限制". 当我们处理 `a <-fam limᵢ p f` 与 `b <-fam limᵢ p f` 时, 各自的见证 `x, y : Ordᴰ-fam i` **没有自然的共同上界** —— 不能直接用 i 层的 `<-fam-dec`.

可挽救方案: 由 f 的单调性, `f x, f y <-fam limᵢ p f mono` (这需要先证), 所以可以用 ℓ 层的 `<-fam-dec` 比较 f x 与 f y, 再用 mono 的"严格性" (mono ⇒ 单射) 把回拉到 x, y. 这一步**需要附加引理证明 mono 是严格 + 单射**, 涉及 codomain 反对称性, 不是直接套现有代码就行.

## 工程量估算 (诚实版)

| 组件 | LOC | 风险 |
|------|-----|------|
| `Ordᴰ-fam` 骨架 | ~80 | Agda 互递归终止检查 |
| `<-fam` 定义 | ~30 | 同上 |
| `<-trans-fam` | ~30 | 标准归纳, 低风险 |
| `<-fam-dec` (bounded trich) | ~80 | 严格单调性辅助引理, 中风险 |
| 单调性辅助引理 | ~50 | ⚠ 是难点 |
| `↑-fam`, `Ω-fam` | ~80 | 照搬现有代码改名 |
| cumsum 的 fam 版 | ~60 | 若需 `Ordᴰ-fam i` 索引, 需超穷加法 |
| `ψ<-fam`, `ψ₀-fam` | ~80 | |
| `ord-1` (真正的版本) | ~40 | 用 mono 输入再做嵌入 |
| `ψⁿ⁺` 与 `BTBO⁺` | ~30 | |
| **总计** | **~560** | 当前文件 1175 行的约 ½ |

主要风险点 (按风险高低):
1. **严格单调性引理** (mono 推出单射): 现有 `<-trans` 帮不上, 要从头证.
2. **互递归终止**: Agda 的 termination checker 对 mutual data + data 通常 OK, 但加上 mono 字段后可能需要 sized types 辅助.
3. **cumsum-fam 的超穷版**: 若 `limᵢ` 的 f 接 Ordᴰ-fam i, 而后续 ψ 输出需要单调化, 现有 ℕ-上的 cumsum 不够用, 要造 Ordᴰ-fam i 上的"超穷累积和".

## 结论: MVP 看清的事

1. **作者的"BTBO = ψ(Ω_Ω)"是元层断言, 不是 Agda 内的等式**. 早期 ψⁿ 值远小于注释命名 (实验 0).
2. **Ord₀ 内部不可形式化地比较两个项**, 所以"免费变体"等手段无法证明带来新强度 (实验 A).
3. **真正的撞壁是 Ord₀-索引基本列的嵌入**: Ord 1 → Ordᴰ 在 `limᵢ` 情形无解, 除非折叠回 Ord₀, 而折叠不带新强度 (实验 B).
4. **补 `<-Ord₀` 不够**, 因为 Ord₀ 的 `lim` 不带单调性, 三歧性无解 (实验 C).
5. **最小可行扩展**: 整个 Ord ℓ 族加上单调性证明, 估计 ~560 行新代码 (实验 D). 难点不在结构, 在严格单调性 + 超穷 cumsum.

## 建议的下一步

不一次到位写 560 行. 分三个小阶段, 每段独立可验证:

**阶段 1** (~110 行): 写 `Ordᴰ-fam` 骨架 + `<-fam` + `<-trans-fam`. 让 Agda 通过 termination check. 不证 `<-dec`. 这一步只是验证"互递归结构在 Agda 里成立".

**阶段 2** (~150 行): 证 `<-fam-dec` 和严格单调性引理. 这是核心难点; 通过这步才知道方案到底可不可行.

**阶段 3** (~300 行): 照搬现有代码到 fam 版本, 实现 Ω-fam、ψ-fam、新版 ordᴰ 与 BTBO⁺. 大部分是机械工作.

**关键决策点在阶段 2**: 如果 `<-fam-dec` 证不出来, 整个方案要重新设计 (可能要回到 IR-Mahlo 那条路). 阶段 1 的结果几乎没风险, 阶段 3 是体力活. 阶段 2 是赌注.

我推荐**先单独把阶段 1 跑通**, 再决定是否投入阶段 2. 这是最低成本的 go/no-go 测试.
