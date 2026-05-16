# Mahlo Phase 2: Sub reflection + `<ᴹ` + mono + bounded trichotomy 尝试

> Phase 1 骨架见 [Phase1.lagda.md](Phase1.lagda.md). 五步路线见 [FINDINGS.md §6](FINDINGS.md#6-phase-2-路线-2000-3000-loc-估). 本文件独立 module 重建 Ordᴹ + Opᴹ + Sub + `<ᴹ` + `<ᴼ` + mono 互递归 (Phase 1 不含 mono 字段, Phase 2 升级需重声明), 逐步推进 Step 1-5.
>
> 撞墙记录见 [FINDINGS_Phase2.md](FINDINGS_Phase2.md) (Step 4 撞墙后新建).

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

## 互递归 6 层骨架: Ordᴹ + Opᴹ + Sub + `<ᴹ` + `<ᴼ` + monoᴺ

Step 1 (Sub reflection) + Step 2 (`<ᴹ`, `<ᴼ`) + Step 3 (mono on lim) 合并为一个 forward-declaration + 定义块. mahlo 暂不加 mono (Phase 3 todo: 需在 `Sub a` 上定义内在序后再加).

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

data _<ᴹ_ where
  zero    : ∀ {a} → a <ᴹ suc a
  suc     : ∀ {a b} → a <ᴹ b → a <ᴹ suc b
  lim     : ∀ {a f} {mono : monoᴺ f} → (n : ℕ) → a <ᴹ f n → a <ᴹ lim f mono
  mahlo-a : ∀ {f a b x} → x <ᴹ a → x <ᴹ mahlo f a b
  mahlo-b : ∀ {f a b x} → (s : Sub a) → x <ᴹ b s → x <ᴹ mahlo f a b

data _<ᴼ_ where
  op-c : ∀ {c c' g g'} → c <ᴹ c' → op c g <ᴼ op c' g'
```

注: `<ᴹ` 跨 mahlo 的两条进路 (mahlo-a / mahlo-b) 对应 Step 1 `Sub (mahlo _ a b) = Σ (Sub a) (Sub ∘ b)` 的两个分量 — 形状同步, 符合 Setzer Σ-closure 的反射结构.

## 传递性 `<ᴹ-trans`

仿 [Naive/Phase1.lagda.md:60–73](../Naive/Phase1.lagda.md). 结构归纳第二参数, mahlo 两条 case 平凡递归.

```agda
<ᴹ-trans : ∀ {a b c} → a <ᴹ b → b <ᴹ c → a <ᴹ c
<ᴹ-trans p zero          = suc p
<ᴹ-trans p (suc q)       = suc (<ᴹ-trans p q)
<ᴹ-trans p (lim n q)     = lim n (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-a q)   = mahlo-a (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-b s q) = mahlo-b s (<ᴹ-trans p q)
```

## Step 4 — 有界三歧性尝试 (撞墙记录)

仿 [Naive/Phase1.lagda.md:118–130](../Naive/Phase1.lagda.md) + [BTBO.lagda.md:699–707](../../BTBO.lagda.md). 目标 (伪代码, 实际 Agda 实现见下方 `<ᴹ-dec?`):

    <ᴹ-dec : ∀ {a b c} → a <ᴹ c → b <ᴹ c → a <ᴹ b ⊎ b <ᴹ a ⊎ a ≡ b

非 mahlo 情形 (zero/suc/lim) 平滑通过, 仿 BTBO `<-dec`. **mahlo 节点 4 个子 case (mahlo-a/mahlo-b 笛卡尔积) 触发结构性死墙**:

| sub-case | bound 提取 | 死墙根源 |
|----------|----------|----------|
| (mahlo-a p, mahlo-a q) | 都比 a 小 | ✓ 递归 |
| (mahlo-a p, mahlo-b s q) | 一个比 a, 一个比 b s | 需要 `a` 与 `b s` 的相对序 — `b : Sub a → Ordᴹ` 无 mono 约束 |
| (mahlo-b s p, mahlo-a q) | 对称 | 同上 |
| (mahlo-b s p, mahlo-b s' q) | 都是 b 分支, s/s' 不同 | 需 `Sub a` 上的内禀序 + `b` mono — Phase 3 todo |

类比 [Naive/FINDINGS.md §5](../Naive/FINDINGS.md) `+-lmono` 反例 (`0+ω≡1+ω ∧ 0<1`): 这里 Mahlo 节点上的对应反例形式为 `b s ≡ b s'` 但 `s ≠ s'` 的可能性 — 一旦 `b : Sub a → Ordᴹ` 非单射, Mahlo 节点的 sub-universe 元素无法被外部区分.

工作版本: 只覆盖 `(mahlo-a, mahlo-a)` 案例, 其余 3 个 mahlo 子 case 用 `BLOCKED-…` 占位 ⊥-eliminate 包裹宣告 (不放 postulate, 用 absurd-pattern-on-empty 表达 "此案需 Sub-序 + b-mono, Phase 3 再做").

由于 Agda `--safe` 拒绝不完整模式, 这里改写成**显式 partial**: 返回 `Maybe` 包装, mahlo 卡 case 返回 `nothing`.

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
-- BLOCKED: 下列 3 个 case 需要 Sub-内在序 + b-mono (Phase 3)
<ᴹ-dec? (mahlo-a _)   (mahlo-b _ _) = nothing
<ᴹ-dec? (mahlo-b _ _) (mahlo-a _)   = nothing
<ᴹ-dec? (mahlo-b _ _) (mahlo-b _ _) = nothing
```

**Step 4 结论**: bounded trichotomy 在 mahlo 节点上**结构性卡死**, 与 Naive Phase1 `limΩ` case 的 `+-lmono` 死墙同构. 退回到 partial Maybe-wrapped 版本; 全函数化需 Phase 3 (Sub 内禀序 + mahlo 加 monoSub 字段).

## Step 5 — ψ_M collapser (跳过)

Step 4 partial. ψ_M (仿 [Higher.agda:31–38](../../Higher.agda) `ψ<Ω`) 的关键 `with <ᴹ-dec` 三歧 fold 无法落地: mahlo 节点的 3 个 `nothing` 分支阻塞了 `ψ_M` 在 mahlo 输入上的递归. 即便用 Maybe-monad 把 `ψ_M : Ordᴹ → Maybe (Ord …)` 化, 输出的"Maybe Ord"在 Buchholz OCF 框架内**无意义**: collapser 需要给出确定的 Ord 值, 不能 nothing.

与 [Naive/FINDINGS.md §6 行 E](../Naive/FINDINGS.md) 同结论: Mahlo 的 ψ-collapser 需要在 trichotomy 死墙之上才有意义, 目前不可写. Phase 3 (Sub-序 + b-mono) 完成后再尝试.

## Phase 2 总结

| Step | 状态 | 备注 |
|------|------|------|
| 1. Sub reflection | ✓ | Σ-closure `Sub (mahlo _ a b) = Σ (Sub a) (Sub ∘ b)` |
| 2. `<ᴹ` + `<ᴼ` 互递归 | ✓ | mahlo-a / mahlo-b 双进路, `<ᴼ` 仅 op-c 头比较 |
| 3. mono 烤进 lim | ✓ (部分) | lim 带 monoᴺ; mahlo 未带 monoSub (Phase 3) |
| 4. bounded trichotomy | ⚠️ partial | non-mahlo 全通; mahlo 4 子 case 中 3 个 blocked, Maybe-wrapped |
| 5. ψ_M collapser | ✗ skip | trichotomy 未全通则不可写 |

文件通过 `agda --safe --without-K --cubical-compatible` 编译. 无 postulate, 无 axiom. 详细诊断 → [FINDINGS_Phase2.md](FINDINGS_Phase2.md).
