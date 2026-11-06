# 相干的世界 (二): 带包含的塔的极限 `U⋆`

> 不含记号. 入口 [CohW](CohW.lagda.md). 把 [CohWTy](CohWTy.lagda.md) 的链极限用在 [HtTowerNStage](HtTowerNStage.lagda.md) 的塔 `L′` 上:
>
> - `L′ (k+1) = step (L′ k) ⊕ₖ Lev (Ωtop (L′ k))` 的世界是 `Bool` 上的族: `true` 分量是 `step (L′ k)` 的世界 $(w_k, \beta_k)$, `false` 分量是 `Lev` 部分的世界 $v_k$. 扩张数据 `XL k = HB (L′ k) × Wd (Lev (Ωtop (L′ k)))`, 粘合 `glL k w (β , v) = (true ↦ (w , β); false ↦ v)`.
> - **`U⋆ = colim chainL`**: 世界是 $A\times\prod_k \mathrm{XL}\,k$, 第 $k$ 级的世界是算出来的. 包含 `inclL` 的界双向都是恒等 (定义相等).
> - **`coh`**: 第 $k+1$ 级的世界投影到第 $k$ 级 (`proj₁ (pj (k+1) w true)`) 就是第 $k$ 级的世界, `refl`. 这是 `HtTowerN` 第一个障碍要的相干, 原话.
> - 定理: `kmU`/`wmU` (每一级 `L′ k` 进 `U⋆`), `needU`/`wmatchU` (每个 `step (L′ j)` 进 `U⋆`), **`tri`** (经 `L′ k` 的世界对应 `wmatch′` 再投影, 与直接投影相等, 对一切 $j<k$), `rcohL→`, `rcohL←` (跨级相干的实例), **`yes-wmatch`**: `no-wmatch` 的两个前提在 `U⋆` 上**同时**成立 (同一对种类的形状, 同一个世界对应).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohWL where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFNeed using (KMatch; km; to)
open import OCF.Align.HtTowerNStage using (_⊕ₖ_; two; L′; kmComp; kmStep; kmL; need′; WMatch; wm; bd→; bd←; wmatch′; K₀)
open import OCF.Align.CohWTy
```

## §1 链与极限

```agda
XL : ℕ → Set
XL k = HB (L′ k) × Wd (Lev (Ωtop (L′ k)))

glL : ∀ k → Wd (L′ k) → XL k → Wd (L′ (suc k))
glL k w x = λ { true → (w , proj₁ x) ; false → proj₂ x }

chainL : Chain
chainL = record { F = L′ ; X = XL ; gl = glL }

U⋆ : KS
U⋆ = colim chainL

pjL : ∀ k → Wd U⋆ → Wd (L′ k)
pjL k = pj chainL k
```

**相干** (`HtTowerN` 第一个障碍的原话): 第 $k+1$ 级的世界投影到第 $k$ 级, 等于第 $k$ 级的分量.

```agda
coh : ∀ k (w : Wd U⋆) → proj₁ (pjL (suc k) w true) ≡ pjL k w
coh k w = refl
```

**包含**: 第 $k$ 级的种类进第 $k+1$ 级的 `step` 分量的旧种类, 坐标恒等, 界双向是恒等.

```agda
kmLk : ∀ k → KMatch (L′ k) (L′ (suc k))
kmLk k = kmComp kmStep (kmL k)

inclL : Incl chainL
inclL = record { M = kmLk ; bdi→ = λ k e → e ; bdi← = λ k e → e }
```

## §2 每一级进 `U⋆`

```agda
kmU : ∀ k → KMatch (L′ k) U⋆
kmU = kmC chainL

wmU : ∀ k → WMatch (L′ k) U⋆ (kmU k)
wmU = wmC chainL

needU : ∀ j → KMatch (step (L′ j)) U⋆
needU j = kmComp (kmL j) (kmU (suc j))

wmatchU : ∀ j → WMatch (step (L′ j)) U⋆ (needU j)
wmatchU j = record { wm = λ w → pjL (suc j) w true ; bd→ = λ e → e ; bd← = λ e → e ; lgw = λ l → l (suc j) true }
```

**`tri`: 经有限级走与直接投影相同.** `HtTowerNStage.wmatch′ k j q` 把 `L′ k` 的世界投影到 `step (L′ j)`. 先投影到第 $k$ 级再用它, 等于直接投影到 `step (L′ j)`; 对一切 $j<k$, 证明对 $q$ 递归, 每一步是 `refl`.

```agda
tri : ∀ k j (q : j <ᴺ k) (w : Wd U⋆) → wm (wmatch′ k j q) (pjL k w) ≡ wm (wmatchU j) w
tri (suc j) j zero w = refl
tri (suc k) j (suc q) w = tri k j q w
```

**跨级相干的实例.** 第 $j$ 级的种类与它在第 $k$ 级的像界相同, 在同一个 `U⋆` 世界里.

```agda
rcohL→ : ∀ {j k} (q : Le j k) {κ c} {w : Wd U⋆} →
         Bd U⋆ (k , km (Mle inclL q) κ) (to (Mle inclL q) κ c) w → Bd U⋆ (j , κ) c w
rcohL→ = rcoh→ inclL

rcohL← : ∀ {j k} (q : Le j k) {κ c} {w : Wd U⋆} →
         Bd U⋆ (j , κ) c w → Bd U⋆ (k , km (Mle inclL q) κ) (to (Mle inclL q) κ c) w
rcohL← = rcoh← inclL
```

## §3 `no-wmatch` 的前提在 `U⋆` 上同时成立

`HtTowerNStage.no-wmatch` 的两个种类: `step (L′ 0)` 的新种类 (坐标 `H₀`), 与它在 `step (L′ 1)` 里的像. 在 `U⋆` 里它们是 `κ0⋆ = (1, (true, new))` 与 `κ1⋆ = (2, K₀)`, 都送到 `L′ 2` 的 `K₀`. `no-wmatch` 说 `U′` 上没有 `wm′` 同时满足下面两条; 在 `U⋆` 上 `wm′ = pjL 2` 两条都是恒等.

```agda
κ0⋆ κ1⋆ : K U⋆
κ0⋆ = 1 , (true , inj₂ tt)
κ1⋆ = 2 , K₀

yes-wmatch : Σ (Wd U⋆ → Wd (L′ 2)) (λ wm′ →
  (∀ {c w} → Bd U⋆ κ1⋆ c w → Bd (L′ 2) K₀ c (wm′ w)) ×
  (∀ {c w} → Bd (L′ 2) K₀ c (wm′ w) → Bd U⋆ κ0⋆ c w))
yes-wmatch = pjL 2 , (λ e → e) , (λ e → e)

-- 两个种类的界是同一个类型 (逐点, 不用外延)
same-bd : ∀ c w → Bd U⋆ κ0⋆ c w ≡ Bd U⋆ κ1⋆ c w
same-bd c w = refl
```
