# SameV: 接口 (同值不同结构的坐标: 层号的搬运与跨层的值律)

> 不含记号. 构造一路 SameV, 否定一路 NegSameV 共用. 入口 [SameV](SameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValC*`, [ValXGoal](ValXGoal.lagda.md) (只用, 不改). 第 4 层: 只新增关系与定理, 不改树、折叠、合法性.
>
> **接口定稿 2026-11-06 21:03 (首次编译通过).** 定稿后只增不改.
>
> **问题.** [ValXObs](ValXObs.lagda.md) `floor-block`: 坐标 $1+\omega_1$ 与 $1+\omega_2$ 值相关、结构不同, 地板的分支 `gt` 落在无公共分量的两组种类里, 一切层反射的关系都比不了. 出路 (ValX 接手清单第 1 条) 是跨层比较: 把第 $c$ 层的高度比到第 $c'$ 层.
>
> **律的定义域: 为什么不是字面公共上界.** 同一棵合法的树的两个第一位置可比 (`cmpB`). 所以值相关而结构不同的两个层号**没有**合法的字面公共上界 (否定一路 `NegSameVSpine.no-common`, 对方已编译, 本路未复核). 律里的一对层号 $(m,m')$ 改带数据证据: 一个**层号搬运** `LvMor m m′` (§2). 它不是值关系的推导, 而是从 $m$ 的第一位置到 $m'$ 的第一位置的函数, 带字面的 $\lhd$ 证据; 每个层号**内部**的比较 (`cmpB`) 仍在各自的字面公共上界之下. 否定一路可挑战这一选择: 律里没有裸的跨层号比较, 但 `LvMor` 是否够用, 是待定的问题.
>
> **`LvMor` 的律** (全部字面): 位置的像 `im q ⊲ m′` (`im⊲`); 像只依赖位置不依赖证明 (`im-irr`; ℕ-极限的不同分量到达同一位置时像相同, 这是**协调性**); $0\mapsto0$ (`im-z`); 保第一位置 (`im-⊲`); 后继位置严格 (`im-s`); 真第一位置保持 (`im-pp`); 像不低于原来 (`im-le`, 第 0 层的值关系). 于是折叠的决定 (留 / 同层 / 在上) 在搬运下不变: 这是这个接口要的全部.
>
> **跨层关系** 是字段 `Le M` (§3): `M : LvMor m m′`, 左边第 $m$ 层, 右边第 $m'$ 层. 锚: 恒等搬运上包含同层关系 (`Le-id`); 第 0 层落到 `LeAt hz` (`Le-0`, 再经 `ValXTm.sound₀` 到 `TLRuleSpec._≤_`).
>
> §4 是目标陈述: `P2` 与 `P2L` (第 0 层, 不提 `LvMor`), `Goal₁` 的闭项形式, `TU` 对层号单调. 否定一路对 `P2` 本身、或对记录 `CrossV`, 都可以说话.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.SameVIf where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; TX; TU; TU1)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCIf I₁ using (toA; F)
open import OCF.Lean.ValXGoal using (kL; kR)
open import OCF.Align.CumReadCF using (asuc)
import OCF.Align.TLRuleSpec as TL
```

## §2 层号搬运

位置是 $t\lhd m$. `im q` 是位置 `q` 的像. 字段都带字面证据.

```agda
record LvMor (m m′ : Cd) : Set where
  field
    im     : ∀ {t} → t ⊲ m → Cd
    im⊲    : ∀ {t} (q : t ⊲ m) → im q ⊲ m′
    im-irr : ∀ {t} (q q′ : t ⊲ m) → im q ≡ im q′
    im-z   : ∀ (q : hz ⊲ m) → im q ≡ hz
    im-⊲   : ∀ {t u} (q : t ⊲ m) (r : u ⊲ m) → t ⊲ u → im q ⊲ im r
    im-s   : ∀ {j u} (q : j ⊲ m) (r : u ⊲ m) → hs j ⊲ u → hs (im q) ⊲ im r
    im-pp  : ∀ {t u} (q : t ⊲ m) (r : u ⊲ m) → Pp t u → Pp (im q) (im r)
    im-le  : ∀ {t} (q : t ⊲ m) → LeAt hz t (im q)
open LvMor public
```

限制到一个位置: 第一位置的传递给出 `res M q : LvMor t (im M q)`.

```agda
res : ∀ {m m′ t} (M : LvMor m m′) (q : t ⊲ m) → LvMor t (im M q)
res M q = record
  { im = λ r → im M (⊲ᴮ-tr r q)
  ; im⊲ = λ r → im-⊲ M (⊲ᴮ-tr r q) q r
  ; im-irr = λ r r′ → im-irr M _ _
  ; im-z = λ r → im-z M _
  ; im-⊲ = λ r s p → im-⊲ M _ _ p
  ; im-s = λ r s p → im-s M _ _ p
  ; im-pp = λ r s p → im-pp M _ _ p
  ; im-le = λ r → im-le M _ }
```

## §3 跨层的值律 (可数层号上的同底折叠)

`Bd M b b′`: 目标层上的一对界: 都值合法, 都在各自的地板之上, 跨层相关. `cross-mono`: 目标是位置 $t$ 与它的像 (不是公共目标), 输出在第 $t$ 层与第 $\mathrm{im}\,t$ 层, 关系沿限制 `res M q`.

```agda
record CrossV : Set₁ where
  field
    Le   : ∀ {m m′} → LvMor m m′ → H m → H m′ → Set
    idM  : ∀ m → LvMor m m
    Le-id : ∀ {m x y} → LeAt m x y → Le (idM m) x y
    Le-0  : ∀ (M : LvMor hz hz) {x y} → Le M x y → LeAt hz x y
    Le-z  : ∀ {m m′} (M : LvMor m m′) y → Le M hz y
    cross-mono : ∀ {m m′} (M : LvMor m m′) (lm : LgB m) (lm′ : LgB m′) {t} (q : t ⊲ m) {b b′ x y} →
                 MoAt t b → MoAt (im M q) b′ → LeAt t (top b⊥ t) b → LeAt (im M q) (top b⊥ (im M q)) b′ →
                 Le (res M q) b b′ → MoAt m x → MoAt m′ y → Le M x y →
                 Le (res M q) (F m lm t q b x) (F m′ lm′ (im M q) (im⊲ M q) b′ y)
```

## §4 目标陈述

`kL`, `kR`: [ValXGoal](ValXGoal.lagda.md) 的两族根分支. `P2`: ValXP1 的同名陈述 (这里不带 UIP 参数). `P2L`: 对 $k_L$ 的同样陈述. 两者都推出 `Hyp` 的情形 (`P1` 配合, 条件 UIP). `Goal`: 闭项. `TU-mono`: `TU` 对层号单调.

```agda
P2 P2L : Set
P2 = ∀ b₁ b₂ → LeAt hz b₁ b₂ → LeAt hz (kR b₁) (kR b₂)
P2L = ∀ b₁ b₂ → LeAt hz b₁ b₂ → LeAt hz (kL b₁) (kL b₂)

Goal : Set
Goal = asuc (toA TX) TL.≤ toA TU1

TU-mono : Set
TU-mono = ∀ m m′ (lm : LgB m) (lm′ : LgB m′) → LeAt hz m m′ → toA (TU m lm) TL.≤ toA (TU m′ lm′)
```
