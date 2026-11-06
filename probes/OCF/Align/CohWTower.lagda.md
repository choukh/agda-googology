# 相干的世界 (三): `U⋆` 里的塔与对角

> 不含记号. 入口 [CohW](CohW.lagda.md). 在 [CohWL](CohWL.lagda.md) 的 `U⋆` 里写塔, 照 [HtTowerU](HtTowerU.lagda.md) 的 `θ`:
>
> - 第 $k$ 个新种类 `ν⋆ k = (k+1, (true, new))`: `step (L′ k)` 的新种类, 坐标是 `HB (L′ k)`, 界是第 $k$ 份扩张数据 $\beta_k$, 第一位置是 `HB (L′ k)` 在投影世界 `pjL k w` 里的 `⊲` (定义相等).
> - `θ⋆ 0 = 0`, `θ⋆ (k+1) = hΩ (ν⋆ k) (c ↦ θ⋆ k ⊞ ιc k c)`: 接在 `θ⋆ k` 后面, 坐标经 `ιc k` 原样搬进 `U⋆`. 不经 `up` (坐标的种类就是第 $k$ 级的种类, 世界就是 `pjL k`).
> - 对角 **`Λ⋆ = hl θ⋆`**, 合法 **`Lg-Λ⋆`**: 一条对 $k$ 的一步定理 `Lg-θ⋆s` (用到的字段: 新种类的界与第一位置是 `HB (L′ k)` 在 `pjL k w` 里的, `ιc-⊲`, `⊞-⊲`), 不按级写, 合法性由形状给出.
> - 层的良基: `accB` 对一切种类结构 (`HtTowerFTree.accL` 的推广), 所以 `HB U⋆` 作层时折叠可以对层递归.
>
> 读法 (判断, 纸面, 沿用 `HtTowerU`, `HtTowerN` 的读法): `HB (L′ k)` 读 "下标低于 $\Lambda_k$"; `θ⋆ (k+1)` 读 $\Lambda_k$ 之上的第一个 $\Omega$; `Λ⋆` 读 $\Lambda=\sup_k\Lambda_k$, $x\mapsto\Omega_x$ 的第一个不动点. 都没有定理: 这里没有值, 没有折叠.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohWTower where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNStage using (L′; two)
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.CohWTy
open import OCF.Align.CohWL
import OCF.Align.HtFeedTree as F
open import OCF.Align.HtTowerU using (toB; toB-⊲; Lg-toB)
```

## §1 塔与对角

```agda
ν⋆ : ℕ → K U⋆
ν⋆ k = suc k , (true , inj₂ tt)

ι⋆ : ∀ k → HB (L′ k) → HB U⋆
ι⋆ = ιc chainL

θ⋆ : ℕ → HB U⋆
θ⋆ zero = hz
θ⋆ (suc k) = hΩ (ν⋆ k) (λ c → θ⋆ k ⊞ ι⋆ k c)

θ⋆-st : ∀ {w} k → θ⋆ k ⊲[ w ] θ⋆ (suc k)
θ⋆-st {w} k = hLim (botBd U⋆ (ν⋆ k) w) (⊞-fst (θ⋆ k) (ι⋆ k hz))

Λ⋆ : HB U⋆
Λ⋆ = hl θ⋆
```

**合法: 一条对 $k$ 的一步定理.** 新种类 `ν⋆ k` 在世界 $w$ 里的第一位置**就是** `HB (L′ k)` 在 `pjL k w` 里的 `⊲` (`colim` 的 `Pr`, `glL` 的 `true` 分量, `Step.Pr⁺`, 定义相等), 再用 `ιc-⊲`, `⊞-⊲`. 分支合法: `Lg-ιc`, `Lg-⊞`.

```agda
Lg-θ⋆s : ∀ k → LgB (θ⋆ k) → LgB (θ⋆ (suc k))
Lg-θ⋆s k lθ =
  (λ {w} lw e e′ p → ⊞-⊲ (θ⋆ k) (ιc-⊲ chainL {k} {w = w} p)) ,
  (λ c lc → Lg-⊞ (θ⋆ k) (ι⋆ k c) lθ (Lg-ιc chainL k c lc))

Lg-θ⋆ : ∀ k → LgB (θ⋆ k)
Lg-θ⋆ zero = tt
Lg-θ⋆ (suc k) = Lg-θ⋆s k (Lg-θ⋆ k)

Lg-Λ⋆ : LgB Λ⋆
Lg-Λ⋆ = (λ n → θ⋆-st n) , Lg-θ⋆

θ⋆⊲Λ⋆ : ∀ {w} k → θ⋆ k ⊲[ w ] Λ⋆
θ⋆⊲Λ⋆ k = hlim k hself
```

**旧高度.** `HtFeed`, `HtOut` 的合法高度经 `toB` 与第 0 级的嵌入是 `U⋆` 的合法高度; `HtTowerF`, `HtTowerN` 的层 `HB (step S₀)` 是 `L′ 1` 的 `true` 分量, 经 `ι⋆ 1` 进来 (`up₁`).

```agda
old⋆ : F.H → HB U⋆
old⋆ x = ι⋆ 0 (toB x)

Lg-old⋆ : ∀ x → F.LgH x → LgB (old⋆ x)
Lg-old⋆ x l = Lg-ιc chainL 0 (toB x) (Lg-toB x l)

-- step S₀ 的高度进 L′ 1 的 true 分量
up₁ : HB (step S₀) → HB (L′ 1)
up₁ = ι {F = two (step S₀) (Lev (Ωtop S₀))} true

Lg-up₁ : ∀ a → LgB a → LgB (up₁ a)
Lg-up₁ a l = Lg-ι true a l
```

## §2 层的良基, 对一切种类结构

`HtTowerFTree.StH`, `accL` 只对 `HB S₁`. 这里对一切 `S`: 层 $L$ 的节点种类 (后继, 第 $n$ 项, 界之下的坐标) 都在 $L$ 之下, 可达.

```agda
module _ {S : KS} where
  data StB (W : Wd S) (k : HB S) : HB S → Set where
    ss : ∀ {b} → k ⊲[ W ] b → StB W k (hs b)
    sl : ∀ {f} n → k ⊲[ W ] f n → StB W k (hl f)
    sL : ∀ {κ g c} → Bd S κ c W → k ⊲[ W ] g c → StB W k (hΩ κ g)

  data AccB (L : HB S) : Set where
    acc : (∀ {W k} → StB W k L → AccB k) → AccB L

  accB : ∀ L → AccB L
  accC : ∀ b {W a} → a ⊲[ W ] b → AccB a
  accB hz = acc (λ ())
  accB (hs b) = acc (λ { (ss P) → accC b P })
  accB (hl f) = acc (λ { (sl n P) → accC (f n) P })
  accB (hΩ κ g) = acc (λ { (sL e P) → accC (g _) P })
  accC a hself = accB a
  accC (hs b) (hsuc P) = accC b P
  accC (hl f) (hlim n P) = accC (f n) P
  accC (hΩ κ g) (hLim e P) = accC (g _) P

accΛ⋆ : AccB Λ⋆
accΛ⋆ = accB Λ⋆
```
