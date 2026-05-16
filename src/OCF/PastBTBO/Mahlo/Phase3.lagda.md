# Mahlo Phase 3: Sub 内禀序 + monoSub + strat 字段

> Phase 1 骨架: [Phase1.lagda.md](Phase1.lagda.md). Phase 2 ([Phase2.lagda.md](Phase2.lagda.md)) 在 mahlo 节点 trichotomy 3/4 卡死. Phase 3 目标: 加 `_<ˢ_` 内禀序 + `monoSub` 字段 (3a) + `strat : ∀ s → a <ᴹ b s` 字段 (3b), 落地 full `<ᴹ-dec`.
>
> 撞墙路线源: Phase 2 `<ᴹ-dec?` 4 mahlo 子 case 中 3 个 `nothing` (Sub 无内禀序 + b 无 mono).
>
> **实测概要**: ✓ 3a (Sub 内禀序 + monoSub) 通, ✓ 3b (strat 字段) 通, ✓ full `<ᴹ-dec` 4 子 case 全闭合. **代价: Mahlo 编码弱化为 stratified Σ-reflect, 强度 < 真 Setzer Mahlo, ≲ Higher.agda**. 详 §4.
>
> **术语**: "3a/3b" 指本文件内的两个攻击轮次, "Step N" 沿用 Phase 2 内 5-step 编号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Mahlo.Phase3 where

open import OCF.BTBO using (module Trich)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Data.Sum using (_⊎_) renaming (inj₁ to injᵃ; inj₂ to injᵇ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
```

## 互递归 8 层骨架: Ordᴹ + Opᴹ + Sub + `<ᴹ` + `<ᴼ` + `<ˢ` + monoᴺ + monoSub

Phase 2 6 层基础上, 新增 `_<ˢ_` (Sub 内禀序, IR-recursive on `a`) 与 `monoSub`. mahlo 字段从 3 个 (f/a/b) 升至 5 个 (+ monoSub + strat). monoSub/strat 一起把"任意 `Sub a → Ordᴹ`"窄化为"按 Sub 内禀序单调且与 `a` 分层".

```agda
infix 10 _<ᴹ_ _<ᴼ_ _<ˢ_

data Ordᴹ : Set
data Opᴹ  : Set
Sub : Ordᴹ → Set
data _<ᴹ_ : Ordᴹ → Ordᴹ → Set
data _<ᴼ_ : Opᴹ → Opᴹ → Set
_<ˢ_ : ∀ {a : Ordᴹ} → Sub a → Sub a → Set

monoᴺ : (ℕ → Ordᴹ) → Set
monoᴺ f = ∀ {n m : ℕ} → n <ᴺ m → f n <ᴹ f m

monoSub : (a : Ordᴹ) → (Sub a → Ordᴹ) → Set
monoSub a b = ∀ {s s' : Sub a} → s <ˢ s' → b s <ᴹ b s'

data Ordᴹ where
  zero  : Ordᴹ
  suc   : Ordᴹ → Ordᴹ
  lim   : (f : ℕ → Ordᴹ) → monoᴺ f → Ordᴹ
  mahlo : Opᴹ → (a : Ordᴹ) → (b : Sub a → Ordᴹ)
        → monoSub a b → (∀ s → a <ᴹ b s) → Ordᴹ

data Opᴹ where
  op : (c : Ordᴹ) → (Sub c → Opᴹ) → Opᴹ

Sub zero                = ⊥
Sub (suc _)             = ⊤
Sub (lim _ _)           = ℕ
Sub (mahlo _ a b _ _)   = Σ (Sub a) (λ x → Sub (b x))
```

### 3a 实测: IR 函数版 `<ˢ` 直接通过

Plan 风险 #1 (函数版 `<ˢ` 终止性) **未触发**. Phase 2 已有 `Sub (mahlo _ a b _ _) = Σ (Sub a) (Sub ∘ b)` 通过 IR scheme (其中 `Sub (b x)` 索引非结构子项), 同构论证下 `<ˢ` 也通过:

```agda
_<ˢ_ {a = zero}            ()  _
_<ˢ_ {a = suc _}           _   _   = ⊥
_<ˢ_ {a = lim _ _}         n   m   = n <ᴺ m
_<ˢ_ {a = mahlo _ a b _ _} (s , t) (s' , t') =
   (s <ˢ s') ⊎ Σ[ eq ∈ s ≡ s' ] (subst (Sub ∘ b) eq t <ˢ t')
```

`subst (Sub ∘ b) eq t : Sub (b s')` 把 `t : Sub (b s)` 沿 `eq : s ≡ s'` 同构搬到 `Sub (b s')`, 然后与 `t' : Sub (b s')` 同类型比较. **不需要 K**: subst 是 J 的特化, 在 `--without-K --cubical-compatible` 下合法.

Plan 备用方案 (data 版 `<ˢ` / `<ˢ` 出 mutual block) **未使用**. 函数版作为 IR scheme 的 Set-valued 一员被 Agda 8 层 mutual block 接受.

未单独证 `<ˢ-trans` (字典序传递性) — `<ᴹ-dec` 不依赖, 留待下游需要时再补.

```agda
data _<ᴹ_ where
  zero    : ∀ {a}                     → a <ᴹ suc a
  suc     : ∀ {a b}                   → a <ᴹ b → a <ᴹ suc b
  lim     : ∀ {a f} {mono : monoᴺ f} (n : ℕ)      → a <ᴹ f n → a <ᴹ lim f mono
  mahlo-a : ∀ {f a b} {m : monoSub a b} {σ : ∀ s → a <ᴹ b s} {x}
          → x <ᴹ a → x <ᴹ mahlo f a b m σ
  mahlo-b : ∀ {f a b} {m : monoSub a b} {σ : ∀ s → a <ᴹ b s} {x}
          → (s : Sub a) → x <ᴹ b s → x <ᴹ mahlo f a b m σ

data _<ᴼ_ where
  op-c : ∀ {c c' g g'} → c <ᴹ c' → op c g <ᴼ op c' g'
```

`σ` 是新的 strat 字段 (`∀ s → a <ᴹ b s`), `m` 是 monoSub 字段. `mahlo-a` / `mahlo-b` 构造子签名只多两个 implicit, 不影响递归结构.

## `<ᴹ-trans` (沿 Phase 2)

```agda
<ᴹ-trans : ∀ {a b c} → a <ᴹ b → b <ᴹ c → a <ᴹ c
<ᴹ-trans p zero          = suc p
<ᴹ-trans p (suc q)       = suc (<ᴹ-trans p q)
<ᴹ-trans p (lim n q)     = lim n (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-a q)   = mahlo-a (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-b s q) = mahlo-b s (<ᴹ-trans p q)
```

## `<ˢ-dec`: Sub 内禀序的无条件三歧

`Sub a` 在固定 a 下结构有限 (zero/suc/lim 分别给出 ⊥/⊤/ℕ; mahlo 给出 Σ 嵌套). 三歧无须 bound:

```agda
<ˢ-dec : ∀ {a} (s s' : Sub a) → s <ˢ s' ⊎ s' <ˢ s ⊎ s ≡ s'
<ˢ-dec {a = zero}            ()  _
<ˢ-dec {a = suc _}           tt  tt        = injᵇ (injᵇ refl)
<ˢ-dec {a = lim _ _}         n   m         with <ᴺ-dec n m
... | injᵃ n<m                         = injᵃ n<m
... | injᵇ (injᵃ m<n)                  = injᵇ (injᵃ m<n)
... | injᵇ (injᵇ refl)                 = injᵇ (injᵇ refl)
<ˢ-dec {a = mahlo _ a b _ _} (s , t) (s' , t') with <ˢ-dec s s'
... | injᵃ s<s'                        = injᵃ (injᵃ s<s')
... | injᵇ (injᵃ s'<s)                 = injᵇ (injᵃ (injᵃ s'<s))
... | injᵇ (injᵇ refl) with <ˢ-dec t t'
...   | injᵃ t<t'                      = injᵃ (injᵇ (refl , t<t'))
...   | injᵇ (injᵃ t'<t)               = injᵇ (injᵃ (injᵇ (refl , t'<t)))
...   | injᵇ (injᵇ refl)               = injᵇ (injᵇ refl)
```

**实测**: lex 序的无条件三歧 4 case 平凡通过. 关键利用: 在 `s ≡ s'` 分支 (Agda `with refl` 自动 unify), `subst (Sub ∘ b) refl t ≡ t` 定义性 reduce, 所以 `injᵇ (refl , t<t')` 中 `t<t'` 直接产生 `subst ... refl t <ˢ t' = t <ˢ t'`.

### 3a 单独效果 (理论复盘)

Phase 3 文件直接落地 3a+3b, 没有切单独 3a commit. 理论上 3a 单独可解锁的 case:

| sub-case | 3a 单独解锁? | 用何机制 |
|----------|-----------|---------|
| (mahlo-a, mahlo-a) | ✓ (Phase 2 已通) | 递归 |
| (mahlo-a, mahlo-b) | ✗ | 需 strat 桥接 a₀ ↔ b s |
| (mahlo-b, mahlo-a) | ✗ | 对称 |
| (mahlo-b s, mahlo-b s') | **✓ 新解锁** | `<ˢ-dec` + monoSub + `<ᴹ-trans` |

3a 单独把 4 case 中的 2 个闭合, cross-case (mahlo-a/mahlo-b) 仍卡死. 进度 1/4 → 2/4. Phase 2 报告 §4 的死墙诊断**精确预言此结果**.

## `<ᴹ-dec`: 完整有界三歧 (3a + 3b 全打)

仿 [BTBO.lagda.md:699-707](../../BTBO.lagda.md). 4 个 mahlo 子 case 全闭合:

```agda
<ᴹ-dec : ∀ {a b c} → a <ᴹ c → b <ᴹ c → a <ᴹ b ⊎ b <ᴹ a ⊎ a ≡ b
<ᴹ-dec zero zero        = injᵇ (injᵇ refl)
<ᴹ-dec zero (suc q)     = injᵇ (injᵃ q)
<ᴹ-dec (suc p) zero     = injᵃ p
<ᴹ-dec (suc p) (suc q)  = <ᴹ-dec p q
<ᴹ-dec (lim {mono = μ} n p) (lim k q) with <ᴺ-dec n k
... | injᵃ n<k         = <ᴹ-dec (<ᴹ-trans p (μ n<k)) q
... | injᵇ (injᵃ k<n)  = <ᴹ-dec p (<ᴹ-trans q (μ k<n))
... | injᵇ (injᵇ refl) = <ᴹ-dec p q
<ᴹ-dec (mahlo-a p)              (mahlo-a q)    = <ᴹ-dec p q
<ᴹ-dec (mahlo-a {σ = σ} p)      (mahlo-b s q)  = <ᴹ-dec (<ᴹ-trans p (σ s)) q
<ᴹ-dec (mahlo-b {σ = σ} s p)    (mahlo-a q)    = <ᴹ-dec p (<ᴹ-trans q (σ s))
<ᴹ-dec (mahlo-b {m = m} s p)    (mahlo-b s' q) with <ˢ-dec s s'
... | injᵃ s<s'        = <ᴹ-dec (<ᴹ-trans p (m s<s')) q
... | injᵇ (injᵃ s'<s) = <ᴹ-dec p (<ᴹ-trans q (m s'<s))
... | injᵇ (injᵇ refl) = <ᴹ-dec p q
```

四个 mahlo 子 case:

- `(mahlo-a, mahlo-a)`: 同 bound a. 递归.
- `(mahlo-a p, mahlo-b s q)`: p : a < a₀, strat (σ s) 给 a₀ <ᴹ b s, trans 给 a <ᴹ b s. 现 p', q 同 bound `b s`. 递归.
- `(mahlo-b s p, mahlo-a q)`: 对称.
- `(mahlo-b s p, mahlo-b s' q)`: `<ˢ-dec s s'` 三歧. mono (m) 给 b s ↔ b s' 的序, trans 把较低的 bound 抬到较高的 bound. 递归.

**终止性**: 每个递归 `<ᴹ-dec` 的输入证明从 `<ᴹ mahlo ...` 缩小到 `<ᴹ a` 或 `<ᴹ b s`, 是 `<ᴹ` 证明的结构子项, 通过 Agda termination checker.

## 3b strat 字段的语义代价

**`∀ s → a <ᴹ b s` 不是标准 Mahlo**. Setzer 1998 IR-Mahlo 的反射规则只要求 `b s` 是 sub-universe (对 `a` 闭合 reflection), **不要求 `a < b s`**. 真 Mahlo 模型中, `a` 与 `b s` 可以是相互独立的 inaccessibles, 没有线性序关系.

强制 `a < b s` 让 Mahlo 退化为类似 "Σ-veblen-stratified Mahlo" 的层次结构: 把所有 reflected sub-universes 串成 `a < b s₁ < b s₂ < ...` 的链. 这是 Mahlo 的弱版本:

- **Setzer 真 Mahlo**: M 是 Mahlo 基数, 对任意 closed unbounded class C, ∃ inaccessible κ ∈ C ∩ M. 涉及的 inaccessibles 无序约束.
- **本文件 stratified Mahlo**: M 上的 sub-universe 必须形成"linearly above a₀"的层次. 远小于 ψ(M_真).

**结论**: 本 Phase 3 编码不是真 Mahlo, 是 stratified Σ-reflect. 后续若要恢复 Setzer 强度, 必须找到替代 strat 的方案 — 此项是开放问题.

### strat 与 monoSub 的独立性

strat (`∀ s → a <ᴹ b s`) 与 monoSub (`s <ˢ s' → b s <ᴹ b s'`) 是两个独立约束:

- strat 单独不蕴含 mono. 不要求 `b` 单调.
- mono 单独不蕴含 strat. 不要求 `a` 在 `b` image 下.
- 二者合在一起把 `b : Sub a → Ordᴹ` 限定为"严格高于 a₀ 且单调"的 image.

数学上这把 mahlo 节点的 sub-universe 结构压扁成 ω₁-类型的链, 没有 reflection 的非平凡性. 但对 ordinal collapse 来说, 这层结构已足以驱动 ψ.

### 强度量级评估

原先粗估 "ψ((Ω_Ω)^ω) 量级" **过低**. (Ω_Ω)^ω 在 Buchholz 序数算术里只比 Ω_Ω 多一个 ω-指数, ψ((Ω_Ω)^ω) ≈ ψ(Ω_Ω · ω), 几乎贴着 ψ(Ω_Ω) 之上, 没有捕捉 mahlo 作为"BTBO 之上 +1 级结构层"的本质.

修正估算 (分单层与嵌套):

| 情形 | 索引结构 | 估算强度 |
|------|---------|---------|
| Phase 3 单层 mahlo (a, b 来自 BTBO 范围) | `Sub a` ≈ ℕ 或 Σ-of-ℕ, 都可数 cardinality, 平铺结构 | ≈ ψ((Ω_Ω)^ω) ~ ψ(Ω_Ω · ω) |
| Phase 3 嵌套 mahlo (a 自己是 mahlo, Σ-of-Σ-of-...) | 多层 Σ 名字空间, 仍可数但结构递归深 | 极限 ≈ ψ(Ω_(Ω+ω)) 量级, 上界 ≲ ψ(Ω_(Ω+1)) |
| 对比: Higher.agda OrdΩ + limₙ | `Ord ψᴰ(n)` (带 limᵢ 嵌套的 BTBO 全树作索引) | 实测 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))), 上界 ψ(Ω_(Ω+1)) ([Higher.agda:40](../../Higher.agda#L40)) |

### 与 Higher.agda 的精确对比

**两者都是"BTBO 之上 +1 级", 但增量方向不同**:

- **Higher.agda** 的增量在 *"index 的内部结构"*: `limₙ` 让 Brouwer 树以"另一棵 Brouwer 树"(`Ord ℓ`) 为索引. 索引集本身有 `limᵢ` 嵌套, 结构非常丰富.
- **Phase 3 mahlo** 的增量在 *"节点的外部结构"*: mahlo 节点带"sub-universe 名字集" `Sub a`. 但 `Sub a` 是 Σ-of-flat, **没有内部 limᵢ 嵌套**, 比 `Ord ℓ` 结构上更扁.

**Cardinality 等价, 结构非等价**. 两者都受可数 cofinality 限制, 但 Higher.agda 的 index 比 Phase 3 的 index 在 Brouwer 树意义下更复杂. 这意味着:

> **Phase 3 嵌套 mahlo 大概率不超过 Higher.agda**, 即两者都在 ψ(Ω_(Ω+1)) 下方挤, Phase 3 ≲ Higher.agda.

更精确的位次 (推测, 未严格证明):

    ψ(Ω_Ω) = BTBO
       < ψ(Ω_Ω · ω) ≈ ψ((Ω_Ω)^ω)
       ≲ Phase 3 单层 mahlo  ≈ ψ((Ω_Ω)^ω) 到 ψ((Ω_Ω)·ω²)
       ≲ Phase 3 嵌套 mahlo  ≈ ψ(Ω_(Ω+ω)) 上限
       ≲ Higher.agda (ggg 估算) = ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1)))
       < ψ(Ω_(Ω+1))   ← 共同硬上界
       < ψ(M_Setzer真)  ← 远在上方, 需 true reflection

**关键判断**: 即使 Phase 3 落地 ψ_M (Step 5), 它的输出**不会超过** Higher.agda 已有的 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) 太多. 原 plan 的"用强度换操作"的承诺**强度提升幅度有限**, 主要价值是在 mahlo 结构上证明了 trichotomy 可决, 而非真正抬高了 ordinal 量级.

### strat 字段是否值得?

如果 Phase 3 的强度实际**不超过** Higher.agda, 那么 strat 字段的"语义代价"是否值得?

| 路线 | 强度 | 操作性 | 代码复杂度 |
|------|------|--------|----------|
| Higher.agda (Ordᴰ + limₙ) | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) | full ψ<Ω | ~50 行 |
| Phase 3 (Ordᴹ + mahlo + strat) | ≲ Higher.agda | full <ᴹ-dec, ψ_M TODO | ~140 行 + 互递归 8 层 |
| Phase 3 不带 strat (Phase 3a only) | partial <ᴹ-dec, 实际不可定 ψ_M | — | — |
| Setzer 真 Mahlo | ψ(M) | trichotomy 在 Agda 中不可证 | — |

**警告**: Phase 3 用 8 层互递归 + strat 弱化换来的强度 (≲ Higher.agda), Higher.agda 已用更简单的方式达到了. 如果目标只是"超过 BTBO 一级", Higher.agda 已是更优解. Phase 3 的价值在于:

1. 探索 IR-Mahlo 的形式化路径 (结构性贡献, 不是强度贡献).
2. 准备未来 "true Mahlo without strat" 的研究铺垫 (Phase 4+).
3. 验证 monoSub + `<ˢ` 的 IR-recursive 定义可行 (Dybjer-Setzer scheme 的实证).

## Step 5 — ψ_M collapser (3b 解锁后)

(占位 — 仿 [Higher.agda L31-38](../../Higher.agda#L31-L38). 完整 ψ_M 见后续 Phase. 但**输出强度受上节限制**: 单层 ≈ ψ((Ω_Ω)^ω), 嵌套上限 ≈ ψ(Ω_(Ω+ω)), **大概率不超过 Higher.agda**.)

## Phase 3 进展表

| Step | 3a 状态 | 3b 状态 | 备注 |
|------|---------|---------|------|
| 1. Sub 反射 | ✓ (Phase 2) | ✓ | Σ-closure 不变 |
| 2. `<ᴹ` + `<ᴼ` | ✓ (Phase 2) | ✓ | 多 implicit `m`/`σ` pass-through |
| 3. `<ˢ` + monoSub | ✓ | ✓ | IR 函数版本 + lex 序 |
| 4. strat 字段 | n/a | ✓ | 弱化为 stratified Mahlo |
| 5. full `<ᴹ-dec` | partial (1/2 mahlo case) | ✓ | 4 子 case 全通 |
| 6. ψ_M | ✗ | TODO | 待 Phase 4+ |

## 与 Phase 2 / Naive 死墙的对照

| 维度 | Naive (`+-lmono` 不真) | Phase 2 (mahlo trichotomy 卡) | Phase 3 (本次) |
|------|----------------------|-----------------------------|----------------|
| 死墙位置 | `limΩ x, limΩ y` 跨 Ordᴰ 索引 | mahlo 4 子 case 中 3 卡 | **无 (4 子 case 全通)** |
| 函数空间约束 | `+-lmono` 不真 | `b : Sub a → Ordᴹ` 无 mono | **monoSub + strat 烤进 mahlo** |
| 索引空间约束 | `Ordᴰ` 上 `<` 无 join | `Sub a` 无内禀序 | **`<ˢ` 烤进 Sub** |
| 强度终点 | 卡 ψ(Ω_Ω) | partial, 不可定 ψ_M | ψ(stratified-Mahlo) (弱版本) |
| 数学忠实度 | — | Setzer 直译, 但 trichotomy 不全 | **强度妥协换全 trichotomy** |

**核心交换**: Phase 3 用"语义弱化 (strat 字段)"换"操作性全函数化". 这是研究级形式化中常见的 tradeoff — 自然语言/集合论的 Mahlo 太弱了无法构造性化, 必须妥协到可实现的子集.

Naive 死墙 (`+-lmono` 不真) 与 Phase 2 死墙 (mahlo cross-case) 在 Phase 3 都被烤进结构的约束 (mono / strat) 解决. **本质都是"在不可数索引空间上加内禀序+单调性"**, 是 OCF Mahlo 级形式化的核心研究方法.

## 文献定位

- **Setzer 1998**: 真 IR-Mahlo, 不含 strat. 强度高但 trichotomy 在 Agda 中不可决, 这是 strat 语义代价节提到的开放问题.
- **Takahashi 2024** ([arxiv 2402.15074](https://arxiv.org/abs/2402.15074)): MLQ-style 编码, 解决 Setzer 直译被 positivity 拒, 但**未处理 Sub 内禀序 + bounded trichotomy** (paper focus 在 type-theoretic 解释, 不需要 ordinal `<-dec`). 本 Phase 3 是 Takahashi 框架的延伸, **非 Takahashi paper 已做的部分**.
- **Rathjen 1991**: KPM 的 ψ-OCF 模板. 本 Phase 3 的 ψ_M 走 Rathjen 路线, 但因 strat 弱化, 输出落在子-Mahlo 量级.
- **Dybjer-Setzer 2003**: IR 框架. 本 Phase 3 的 `<ˢ` IR-recursive 定义 (与 Sub 同构) 是 Dybjer-Setzer IR scheme 的直接应用.

## Phase 4 候选升级路径

- **A. 去 strat 保 mono**: 退回 3a-only, 接受 cross-case 卡死, partial trichotomy. 强度高但操作弱.
- **B. 替代 strat**: 探索其他桥接 `a₀ ↔ b s` 的方式. 例如要求 Mahlo 节点带"reflection 见证元素" — 仍是研究问题.
- **C. 接受 stratified Mahlo**: 把 Phase 3 编码标识为"弱 Mahlo OCF", 继续走 ψ_M 路线获取 ψ(stratified-Mahlo) 级 ordinal. 工程上可走.

无 postulate, 无 `--unsafe`. 通过 Agda 2.8.0 + stdlib 2.3 + cubical 0.9 + `--safe --without-K --cubical-compatible --lossy-unification --hidden-argument-puns` 类型检查.
