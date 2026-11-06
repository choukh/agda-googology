# ValW (接口): 带 $W\le W'$ 证据的模拟应满足的律

**接口定稿 2026-11-05 23:43 (首次编译通过).**

> 不含记号. 入口 [ValW](ValW.lagda.md). 第 4 层: 只陈述关系与律, 不改树、折叠、合法性. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.
>
> 构造一路 ValW 与否定一路 NegValW 共用本文件; 定稿后只增不改.
>
> **对象.** 同一个一般折叠 [LeanTFold](LeanTFold.lagda.md) 的两个实例, 只差级回灌参数: `F₁ = Fold T bk Λ lΛ one⊲ fb₁` (左), `F₂ = … fb₂` (右). 主要的一对是 `fb₁` 一切有损 (闭项 `TL`), `fb₂` 按计划回灌 (闭项 `TF`). 回灌那一行 (`RKa`) 右边在升高的世界 $w_{n}\ge W$ 里跑分支, 所以从这一行往下, 两边在**不同的世界**里跑: 左边 $W_1$, 右边 $W_2$, 带证据 $W_1\le W_2$.
>
> **律的定义域 (公共上界都是字面的).**
>
> - 两个世界: 一切比较都带 `q : W₁ ≤ W₂`, 右边的世界就是公共上界. 分支在 "成对的更大世界" 上比: $W_1\le W_1'$, $W_2\le W_2'$, 并且 $W_1'\le W_2'$ (第三条证据也是字面给出的, 不比较两个裸世界).
> - 两个层: 关系允许左层 $L_1$ 与右层 $L_2$ 不同, 带证据 `e : L₁ ⊲[ W₂ ] L₂` (右层是字面上界; `hself` 是同层). 为什么要两个层: 闭包分支在世界 $W'$ 里过第 $g(\mathrm{top}\,\kappa\,W')$ 层 ($\Omega_L$ 的 $\Omega$-行), 右边世界更大, 走到的层更高.
> - 结点的 "保留/上升" 只在同一个目标层 $t$ 上, 两个目标世界 $m_1\le m_2$ 上比; 两个结点层 $k_1\lhd k_2$ 也带字面证据.
>
> 没有裸下标的比较律, 没有两个任意世界的比较.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
module OCF.Lean.ValWIf (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ)
  (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (fb₁ fb₂ : K T → FoldTy.Fb T Λ ⊎ ⊤) where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Lean.NegLeanLvVal using () renaming (_≤_ to _≤ᵥ_)
import OCF.Lean.LeanTFold as Fold
open Tree T
open FoldTy T Λ

module F₁ = Fold T bk Λ lΛ one⊲ fb₁
module F₂ = Fold T bk Λ lΛ one⊲ fb₂
```

## §1 结点的决定: 两个世界, 同层或两个层

`rkT` 在目标世界里比较结点层 $k$ 与目标层 $t$. 三种成对的结果: 都保留 (`kp`), 都上升 (`rs`), 左保留右上升 (`kr`). 第四种 (左上升右保留) 不列.

```agda
data RkR {k₁ k₂ t : HB L₀} {m₁ m₂ : Wd L₀} : F₁.Rk k₁ t m₁ → F₂.Rk k₂ t m₂ → Set where
  kp : ∀ {R₁ R₂} → RkR (F₁.keep R₁) (F₂.keep R₂)
  rs : RkR F₁.rise F₂.rise
  kr : ∀ {R₁} → RkR (F₁.keep R₁) F₂.rise

data RkSame {k t : HB L₀} {m₁ m₂ : Wd L₀} : F₁.Rk k t m₁ → F₂.Rk k t m₂ → Set where
  kp : ∀ {R₁ R₂} → RkSame (F₁.keep R₁) (F₂.keep R₂)
  rs : RkSame F₁.rise F₂.rise
```

**律 R1 (同层, 两个世界).** 同一个结点层 $k$, 同一个目标层 $t$, 目标世界 $m_1\le m_2$: 两边的决定一致.

```agda
RkAgree : Set
RkAgree = ∀ {k t m₁ m₂} → m₁ ≤ m₂ →
  (km₁ : k ⊲[ m₁ ] Λ) (tm₁ : t ⊲[ m₁ ] Λ) (lm₁ : LgW L₀ m₁) →
  (km₂ : k ⊲[ m₂ ] Λ) (tm₂ : t ⊲[ m₂ ] Λ) (lm₂ : LgW L₀ m₂) →
  RkSame (F₁.rkT km₁ tm₁ lm₁) (F₂.rkT km₂ tm₂ lm₂)
```

**律 R2 (两个层).** 结点层 $k_1\lhd k_2$ (右层是字面上界, 在 $m_2$ 里): 两边的决定是 `RkR` 的三种之一.

```agda
RkCross : Set
RkCross = ∀ {k₁ k₂ t m₁ m₂} → m₁ ≤ m₂ → k₁ ⊲[ m₂ ] k₂ →
  (km₁ : k₁ ⊲[ m₁ ] Λ) (tm₁ : t ⊲[ m₁ ] Λ) (lm₁ : LgW L₀ m₁) →
  (km₂ : k₂ ⊲[ m₂ ] Λ) (tm₂ : t ⊲[ m₂ ] Λ) (lm₂ : LgW L₀ m₂) →
  RkR (F₁.rkT km₁ tm₁ lm₁) (F₂.rkT km₂ tm₂ lm₂)
```

## §2 模拟关系的律

`Rx e q x y`: 左边第 $L_1$ 层、世界 $W_1$ 的数据 $x$ 被右边第 $L_2$ 层、世界 $W_2$ 的数据 $y$ 模拟. 律:

- **X1** (`x-sum`) 第 0 层读成值序: 相关的第 0 层数据, 起点 $b\le b'$, 则 `sum b x ≤ᵥ sum b′ y`.
- **X2** (`x-Ωd`) $\Omega_{t_1}$ 被 $\Omega_{t_2}$ 模拟 ($t_1\lhd t_2$ 或同层; 两个世界).
- **X3** (`x-Run`, 见 §3 的 `RunPres`) 折叠保持关系.

```agda
record SimW : Set₁ where
  field
    Rx    : ∀ {L₁ L₂ W₁ W₂} → L₁ ⊲[ W₂ ] L₂ → W₁ ≤ W₂ → D L₁ W₁ → D L₂ W₂ → Set
    x-sum : ∀ {W₁ W₂} (e : hz ⊲[ W₂ ] hz) (q : W₁ ≤ W₂) {x : D hz W₁} {y : D hz W₂} → Rx e q x y →
            ∀ {b b′} → b ≤ᵥ b′ → sum b x ≤ᵥ sum b′ y
    x-Ωd  : ∀ {t₁ t₂ W₁ W₂} (e : t₁ ⊲[ W₂ ] t₂) (q : W₁ ≤ W₂) → Rx e q (Ωd t₁) (Ωd t₂)
```

## §3 输出, 状态, 动作的关系; 折叠保持的陈述

输出 `Df` 在成对的目标上比: 目标层 $t_1\lhd t_2$ (或同层), 目标世界 $m_1\le m_2$. 状态只比累计输出 `d` (第 0, 1 层的 `z`, `z₁` 只喂新种类的回灌 `κc₁`; 判断: 最高层不含新种类 $\Omega$-结点时折叠不经过 `κc₁`). 动作在成对的更大世界上比.

```agda
module Goals (S : SimW) where
  open SimW S

  DfX : ∀ {W₁ W₂} → W₁ ≤ W₂ → Df W₁ → Df W₂ → Set
  DfX {W₁} {W₂} q Δ₁ Δ₂ =
    ∀ {t₁ t₂ m₁ m₂} (e : t₁ ⊲[ m₂ ] t₂) (qm : m₁ ≤ m₂) (T₁ : Tg W₁ t₁ m₁) (T₂ : Tg W₂ t₂ m₂) →
    Rx e qm (yc Δ₁ T₁) (yc Δ₂ T₂)

  StX : ∀ {W₁ W₂} → W₁ ≤ W₂ → St W₁ → St W₂ → Set
  StX q Y₁ Y₂ = DfX q (d Y₁) (d Y₂)

  IgX : ∀ {ly₁ ly₂ W₁ W₂} → ly₁ ⊲[ W₂ ] ly₂ → W₁ ≤ W₂ → Ig ly₁ W₁ → Ig ly₂ W₂ → Set
  IgX {ly₁} {ly₂} {W₁} {W₂} e q A₁ A₂ =
    ∀ {W₁′ W₂′} (p₁ : W₁ ≤ W₁′) (p₂ : W₂ ≤ W₂′) (q′ : W₁′ ≤ W₂′) (l₁ : LgW L₀ W₁′) (l₂ : LgW L₀ W₂′)
      {w₁ : D ly₁ W₁′} {w₂ : D ly₂ W₂′} → Rx (⊲ᴮ↑ p₂ e) q′ w₁ w₂ →
      {Y₁ : St W₁′} {Y₂ : St W₂′} → StX q′ Y₁ Y₂ → DfX q′ (A₁ p₁ l₁ w₁ Y₁) (A₂ p₂ l₂ w₂ Y₂)

  -- X3: 折叠保持关系 (两个层, 两个世界; 起点世界 W₀₁ ≤ W₀₂, 当前世界 W₁ ≤ W₂)
  RunPres : Set
  RunPres = ∀ {ly₁ ly₂ W₀₁ W₀₂ W₁ W₂} (ac₁ : AccY ly₁) (ac₂ : AccY ly₂)
    (e : ly₁ ⊲[ W₂ ] ly₂) (q : W₁ ≤ W₂) (q₀ : W₀₁ ≤ W₀₂) (e₀ : ly₁ ⊲[ W₀₂ ] ly₂)
    {x₁ : D ly₁ W₀₁} {x₂ : D ly₂ W₀₂} → Rx e₀ q₀ x₁ x₂ →
    (q₁ : W₀₁ ≤ W₁) (q₂ : W₀₂ ≤ W₂) (lW₁ : LgW L₀ W₁) (lW₂ : LgW L₀ W₂)
    (ll₁ : F₁.LW ly₁ W₁) (ll₂ : F₂.LW ly₂ W₂)
    {A₁ : Ig ly₁ W₁} {A₂ : Ig ly₂ W₂} → IgX e q A₁ A₂ →
    {w₁ : D ly₁ W₁} {w₂ : D ly₂ W₂} → Rx e q w₁ w₂ →
    {Y₁ : St W₁} {Y₂ : St W₂} → StX q Y₁ Y₂ →
    DfX q (F₁.Run ac₁ x₁ q₁ lW₁ ll₁ A₁ w₁ Y₁) (F₂.Run ac₂ x₂ q₂ lW₂ ll₂ A₂ w₂ Y₂)
```

## §4 回灌提高值: 目标的陈述

由 X1–X3 读到第 0 层 (同层 `hself`, 同一个基世界): 左边的第 0 层读数不超过右边的. 对主要的一对 (`TL`, `TF`) 这就是 `TL ≤ᵥ TF`; 实例的陈述写在入口 [ValW](ValW.lagda.md).

```agda
  Cross0 : Set
  Cross0 = ∀ {W} (ac₁ ac₂ : AccY Λ) {x₁ x₂ : D Λ W} → Rx hself (≤w-rf L₀) x₁ x₂ →
    (lW : LgW L₀ W) {A₁ A₂ : Ig Λ W} → IgX hself (≤w-rf L₀) A₁ A₂ →
    {Y₁ Y₂ : St W} → StX (≤w-rf L₀) Y₁ Y₂ →
    sum hz (yc (F₁.Run ac₁ x₁ (≤w-rf L₀) lW hself A₁ n0 Y₁) (F₁.τ₀ lW)) ≤ᵥ
    sum hz (yc (F₂.Run ac₂ x₂ (≤w-rf L₀) lW hself A₂ n0 Y₂) (F₂.τ₀ lW))
```
