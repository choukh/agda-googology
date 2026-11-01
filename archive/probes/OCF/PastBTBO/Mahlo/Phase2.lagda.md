# Mahlo Phase 2: Sub reflection + `<ᴹ` + mono + bounded trichotomy 尝试

> Phase 1 骨架见 [Phase1.lagda.md](Phase1.lagda.md). 跨 Phase 综合诊断 → [FINDINGS.md](FINDINGS.md).
>
> 本文件独立 module 重建 Ordᴹ + Opᴹ + Sub + `<ᴹ` + `<ᴼ` + mono 互递归 (Phase 1 不含 mono 字段, Phase 2 升级需重声明), 逐步推进 Step 1-5: Sub reflection → `<ᴹ`+`<ᴼ` → mono → bounded trichotomy → ψ_M.
>
> **实测概要**: ✓ Step 1-3 通过, ⚠️ Step 4 在 mahlo 节点 4 子 case 中 3 个 blocked (退化为 partial `Maybe`-wrapped), ✗ Step 5 ψ_M 因 Step 4 partial 跳过. 与 [Naive/FINDINGS.md §5](../Naive/FINDINGS.md) `+-lmono` 死墙**结构同构**.
>
> **术语**: "Step N" 指本文件内 5 个子步 (1=Sub reflection, 2=`<ᴹ`+`<ᴼ`, 3=mono, 4=bounded trichotomy, 5=ψ_M). "Phase N" 指项目级阶段 (1=骨架, 2=本次 5-step 攻击, 3=Sub 内禀序). 两套编号互不重合.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Mahlo.Phase2 where

open import OCF.BTBO using (module Trich)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_) renaming (inj₁ to injᵃ; inj₂ to injᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
```

## Step 1 + 2 + 3 — 互递归 6 层骨架: Ordᴹ + Opᴹ + Sub + `<ᴹ` + `<ᴼ` + monoᴺ

Step 1 (Sub reflection) + Step 2 (`<ᴹ`, `<ᴼ`) + Step 3 (mono on lim) 合并为单一 forward-declaration + 定义块. mahlo 暂不加 monoSub (需 Sub 内禀序, 见 Step 3 实测).

```agda
infix 10 _<ᴹ_ _<ᴼ_

data Ordᴹ : Set
data Opᴹ  : Set
Sub : Ordᴹ → Set
data _<ᴹ_ : Ordᴹ → Ordᴹ → Set
data _<ᴼ_ : Opᴹ → Opᴹ → Set

monoᴺ : (ℕ → Ordᴹ) → Set
monoᴺ f = ∀ {n m : ℕ} → n <ᴺ m → f n <ᴹ f m

data Ordᴹ where
  zero  : Ordᴹ
  suc   : Ordᴹ → Ordᴹ
  lim   : (f : ℕ → Ordᴹ) → monoᴺ f → Ordᴹ
  mahlo : Opᴹ → (a : Ordᴹ) → (Sub a → Ordᴹ) → Ordᴹ

data Opᴹ where
  op : (c : Ordᴹ) → (Sub c → Opᴹ) → Opᴹ

Sub zero              = ⊥
Sub (suc _)           = ⊤
Sub (lim _ _)         = ℕ
Sub (mahlo _ a b)     = Σ (Sub a) (λ x → Sub (b x))
```

### Step 1 实测: Takahashi reflection 的 Brouwer-MLQ 形

`Sub (mahlo _ a b) = Σ (Sub a) (λ x → Sub (b x))` 是 Setzer Mahlo

    mahlo : ((a:U) → (T a → U) → U) → U

的 "T a × T(b applied to T a)" 闭合的 Brouwer-MLQ 化. 读法: mahlo 编码的 sub-universe 元素 = 一对 `(x : Sub a, y : Sub (b x))`.

注: `f : Opᴹ` 字段在此版本中**未参与** `Sub` 的反射定义. 完整 Takahashi 反射需要 `Opᴹ` 与 `Ordᴹ` 双向交互, 涉及更深的 mutual 结构. 当前 Σ-closure 是最小可行版.

```agda
data _<ᴹ_ where
  zero    : ∀ {a} → a <ᴹ suc a
  suc     : ∀ {a b} → a <ᴹ b → a <ᴹ suc b
  lim     : ∀ {a f} {mono : monoᴺ f} → (n : ℕ) → a <ᴹ f n → a <ᴹ lim f mono
  mahlo-a : ∀ {f a b x} → x <ᴹ a → x <ᴹ mahlo f a b
  mahlo-b : ∀ {f a b x} → (s : Sub a) → x <ᴹ b s → x <ᴹ mahlo f a b

data _<ᴼ_ where
  op-c : ∀ {c c' g g'} → c <ᴹ c' → op c g <ᴼ op c' g'
```

### Step 2 实测: `<ᴹ` 跨 mahlo 两条进路对应 Σ-反射

`mahlo f a b` 上的 `<ᴹ` 两个构造子 `mahlo-a` / `mahlo-b` 形状对应 Step 1 `Sub (mahlo _ a b) = Σ (Sub a) (Sub ∘ b)` 的两个分量. 任何小于 mahlo 的 x 必然或者 (a) 小于 mahlo 的 "code 头" a, 或者 (b) 小于某个 b-分支 `b s`. 这就是 Setzer Σ-closure 的**逆向反射**.

`<ᴼ` 只保留 op-c (头比较), 不展开 op 的 `Sub c → Opᴹ` 分支. 够用于未来 `mahlo` cross-Opᴹ 比较, 不过度复杂化.

### Step 3 实测: 为何 mahlo 暂未加 monoSub

完整 6 层互递归 (路线源 [FINDINGS.md §6](FINDINGS.md#6)) 应包括 `monoSub : (a : Ordᴹ) → (Sub a → Ordᴹ) → Set`. 实现障碍:

- `monoSub a b = ∀ {s s'} → s <ˢ s' → b s <ᴹ b s'` 需要 `Sub a` 上的 `<ˢ` 关系
- `<ˢ` 必须**按 a 的结构定义**:
  - `Sub zero = ⊥`: 无序
  - `Sub (suc _) = ⊤`: 单点平凡序
  - `Sub (lim _ _) = ℕ`: 用 `<ᴺ`
  - `Sub (mahlo _ a b) = Σ (Sub a) (Sub ∘ b)`: 递归字典序, 互递归向下
- 这会让互递归扩张到 7+ 层, 且 dictionary order 在 `Σ` 上的 mono 证明需要 `b` 自身的 mono — **循环依赖**

**决策**: Phase 2 不加 monoSub. mahlo 字段仍用 `b : Sub a → Ordᴹ` 无约束函数. Phase 3 之后再考虑独立的 Sub-内禀序模块.

## 传递性 `<ᴹ-trans`

仿 [Naive/Phase1.lagda.md L60-73](../Naive/Phase1.lagda.md). 结构归纳第二参数, mahlo 两条 case 平凡递归.

```agda
<ᴹ-trans : ∀ {a b c} → a <ᴹ b → b <ᴹ c → a <ᴹ c
<ᴹ-trans p zero          = suc p
<ᴹ-trans p (suc q)       = suc (<ᴹ-trans p q)
<ᴹ-trans p (lim n q)     = lim n (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-a q)   = mahlo-a (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-b s q) = mahlo-b s (<ᴹ-trans p q)
```

5 case 全部平凡递归, 与 BTBO `<-trans` 形式一致.

## Step 4 — 有界三歧性: 死墙的诞生

目标 (理想全函数版):

    <ᴹ-dec : ∀ {a b c} → a <ᴹ c → b <ᴹ c → a <ᴹ b ⊎ b <ᴹ a ⊎ a ≡ b

非 mahlo 情形 (zero/suc/lim) 平滑通过, 仿 BTBO `<-dec`. **mahlo 节点 4 个子 case (mahlo-a/mahlo-b 笛卡尔积) 触发结构性死墙**:

| sub-case | 类型展开 | 死墙根源 |
|----------|--------|----------|
| (mahlo-a p, mahlo-a q) | p : a <ᴹ a₀, q : b <ᴹ a₀ | ✓ 递归 `<ᴹ-dec p q` |
| (mahlo-a p, mahlo-b s q) | p : a <ᴹ a₀, q : b <ᴹ b₀ s | a₀ 与 b₀ s 之间无序关系 |
| (mahlo-b s p, mahlo-a q) | p : a <ᴹ b₀ s, q : b <ᴹ a₀ | 对称 |
| (mahlo-b s p, mahlo-b s' q) | p : a <ᴹ b₀ s, q : b <ᴹ b₀ s' | `Sub a₀` 无序 + `b₀` 无 mono |

### 与 Naive `+-lmono` 反例的同构

Naive Phase1 的死墙: `+-lmono : a < b → a + c < b + c` 不真. 反例 `0 + ω ≡ 1 + ω ∧ 0 < 1`. 后果: limΩ case 找不到自然共同上界.

Mahlo 节点的**对应反例**: 设 `b₀ : Sub a₀ → Ordᴹ` 非单射, 存在 `s ≠ s' : Sub a₀` 使 `b₀ s ≡ b₀ s'`. 此时 (mahlo-b s p, mahlo-b s' q) 在结构上不可区分, 但 `s, s'` 本身需要 `Sub a₀` 上的内禀序才能进一步分析 — 与 Step 3 monoSub 缺失**互锁**.

更深一层: 即使 `b₀` 单射, 跨 mahlo-a/mahlo-b 的 case 需要比较 `a₀` 与 `b₀ s` (两个独立的 Ordᴹ), 没有外部的"共同上界"提供. 类比 limΩ 的 `f a, f b : Ordᴰ-1` 跨 Ordᴰ-索引比较 — Naive 已经验证为不通.

### 缓解: Maybe-wrapped partial

由于 Agda `--safe` 拒绝不完整模式, 改写成**显式 partial**: 返回 `Maybe` 包装, mahlo 卡 case 返回 `nothing`.

```agda
Tri : Ordᴹ → Ordᴹ → Set
Tri a b = a <ᴹ b ⊎ b <ᴹ a ⊎ a ≡ b

-- partial bounded trichotomy: returns nothing on mahlo cross-cases
<ᴹ-dec? : ∀ {a b c} → a <ᴹ c → b <ᴹ c → Maybe (Tri a b)
<ᴹ-dec? zero zero        = just (injᵇ (injᵇ refl))
<ᴹ-dec? zero (suc q)     = just (injᵇ (injᵃ q))
<ᴹ-dec? (suc p) zero     = just (injᵃ p)
<ᴹ-dec? (suc p) (suc q)  = <ᴹ-dec? p q
<ᴹ-dec? {a} {b} (lim {mono = mono} n p) (lim m q) with <ᴺ-dec n m
... | injᵃ n<m         = <ᴹ-dec? (<ᴹ-trans p (mono n<m)) q
... | injᵇ (injᵃ m<n)  = <ᴹ-dec? p (<ᴹ-trans q (mono m<n))
... | injᵇ (injᵇ refl) = <ᴹ-dec? p q
<ᴹ-dec? (mahlo-a p)   (mahlo-a q)   = <ᴹ-dec? p q
-- BLOCKED: 下列 3 个 case 需要 Sub-内在序 + b-mono (Phase 3 todo)
<ᴹ-dec? (mahlo-a _)   (mahlo-b _ _) = nothing
<ᴹ-dec? (mahlo-b _ _) (mahlo-a _)   = nothing
<ᴹ-dec? (mahlo-b _ _) (mahlo-b _ _) = nothing
```

**Step 4 结论**: bounded trichotomy 在 mahlo 节点上**结构性卡死**, 与 Naive Phase1 `limΩ` case 的 `+-lmono` 死墙同构. 退回到 partial Maybe-wrapped 版本; 全函数化需 Phase 3 (Sub 内禀序 + mahlo 加 monoSub 字段).

## Step 5 — ψ_M collapser: 必然被阻断

ψ_M 仿 [Higher.agda L31-38](../../Higher.agda) `ψ<Ω`, 形为:

    ψ_M (mahlo … p f) with <ᴹ-dec? p (some upper bound)
    ... | just (injᵃ …) = limᵢ …
    ... | just (injᵇ …) = lfp …
    ... | nothing        = ???

`<ᴹ-dec?` 在 mahlo 输入上 3/4 几率 return `nothing` → `ψ_M` 在那些 case 上无法选择 limᵢ/lfp 分支. 用 Maybe-monad 把 `ψ_M : Ordᴹ → Maybe (Ord …)` 化亦无意义 — collapser 必须给出确定 Ord 值.

**结论**: ψ_M 至少要等 Phase 3 (Sub-序 + b-mono → 全函数 `<ᴹ-dec`) 后才有意义. 与 [Naive/FINDINGS.md §6 行 E](../Naive/FINDINGS.md) 同结论: Mahlo 的 ψ-collapser 需要在 trichotomy 死墙之上才有意义, 目前不可写.

## Phase 2 实测总结

| Step | 状态 | 备注 |
|------|------|------|
| 1. Sub reflection | ✓ | Σ-closure `Sub (mahlo _ a b) = Σ (Sub a) (Sub ∘ b)` |
| 2. `<ᴹ` + `<ᴼ` 互递归 | ✓ | mahlo-a / mahlo-b 双进路, `<ᴼ` 仅 op-c 头比较 |
| 3. mono 烤进 lim | ✓ (部分) | lim 带 monoᴺ; mahlo 未带 monoSub (Phase 3) |
| 4. bounded trichotomy | ⚠️ partial | non-mahlo 全通; mahlo 4 子 case 中 3 个 blocked, Maybe-wrapped |
| 5. ψ_M collapser | ✗ skip | trichotomy 未全通则不可写 |

### 修正路线估算 ([FINDINGS.md §6](FINDINGS.md#6))

原估: "Step 1-2 大概率通 (Takahashi 示范过). Step 3-4 是真正研究. Step 5 取决于 4."

实测修正:

- Step 1-3 通过 (与 Takahashi 示范一致).
- **Step 4 在 mahlo 节点上结构性卡死, 同 Naive `limΩ` 死墙**. 不是"难证而是不可证".
- Step 5 同步阻塞.

升级路径: 必须先做 Phase 3 (Sub 内禀序 + b mono). 这相当于把 Takahashi MLQ 扩成"index-ordered MLQ", 是 Takahashi 2024 paper 未做的部分.

### 与 Naive FINDINGS §6 的统一结论

| 死墙位置 | Naive 框架 | Mahlo 框架 | 同构关键 |
|---------|----------|----------|---------|
| 跨索引比较 | `limΩ f x` vs `limΩ f y` 跨 Ordᴰ x, y | `mahlo-b s` vs `mahlo-b s'` 跨 Sub a₀ s, s' | 索引类型无三歧 |
| 共同上界 | `x + suc y` 中 `+-lmono` 不真 | `b₀` 无 mono → 不存在自然桥接 | 函数空间内的单调性公理 |
| 修复路径 | 加 mono 到 Ordᴰ-1 的 limΩ + 改 ⊔ 算子 | 加 monoSub 到 mahlo + Sub 内禀序 | 烤入函数空间的内禀结构 |

两条路径都需要"在不可数索引空间上加内禀序+单调性", 这是 OCF Mahlo-级形式化的核心未解问题.

文件通过 `agda --safe --without-K --cubical-compatible` 编译. 无 postulate, 无 axiom.
