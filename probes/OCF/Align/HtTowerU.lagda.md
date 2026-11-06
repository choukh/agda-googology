# 高度的高度 (三): 塔

> 不含记号. 入口 [HtTower](HtTower.lagda.md). 只用 [HtTowerTy](HtTowerTy.lagda.md) 的三个构造 (`step`, `sup`, `Lev`) 与 [HtTowerCont](HtTowerCont.lagda.md) 的 `Ωtop`.
>
> 1. **逐级的塔** `Sn k = stepᵏ S₀`: 第 $k+1$ 级的新种类以第 $k$ 级的高度为坐标 (`HB (Sn (suc k))` 的分支取遍 `HB (Sn k)`). `Ωn k = Ωtop (Sn k)` 合法. 但在并 `sup ℕ Sn` 里, 各级的 `Ωn` 互相不是字面的第一位置 (`no-naive-diag`, [HtTowerNeg](HtTowerNeg.lagda.md)), 所以 ℕ-对角不能这样写.
> 2. **以高度为下标的塔** `L`: `L 0 = S₀`, `L (k+1) = Lev (Ωtop (L k))`: 下一级的种类结构是**上一级之上第一个 $\Omega$ 这个高度的 `Lev`**, 即一切低于它的级. 一个种类结构 `U = sup ℕ (step ∘ L)` 装下整座塔; 塔的高度 `θ k` 在 `U` 里一个接一个字面地是第一位置 (`θ-st`), 对角 `Λᵁ = hl θ` 合法 (`Lg-Λᵁ`). 合法性是一条对 $k$ 的一步定理 (`Lg-θ`), 不按级写.
>
> 读法 (判断, 纸面): `HB S₀` 的高度读 $<\Omega_2$; `θ 1` 读 $\Omega_2$; `HB (L k)` 读 "下标低于 $\Lambda_k$", $\Lambda_0=\Omega_2$, $\Lambda_{k+1}\approx\Omega_{\Lambda_k+1}$; `θ (k+1)` 读 $\approx\Lambda_k$ 之上的第一个 $\Omega$; `Λᵁ` 读 $\Lambda=\sup_k\Lambda_k$, 即 $x\mapsto\Omega_x$ 的第一个不动点. 都没有定理: 这里没有值, 也没有折叠 (见入口的第一个障碍).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerU where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
import OCF.Align.HtFeedTree as F
```

## §1 旧的高度是 `HB S₀` 的高度

`HtFeedTree.H` 逐构造子搬过来, 保第一位置, 保合法. 所以 `HtFeed`, `HtOut` 的一切高度都在这里 (经 `up`, `ι` 到下面的 `U`).

```agda
toB : F.H → HB S₀
toB F.hz = hz
toB (F.hs x) = hs (toB x)
toB (F.hl f) = hl (λ n → toB (f n))
toB (F.hΩ g) = hΩ tt (λ c → toB (g c))

toB-⊲ : ∀ {a b W} → a F.⊲[ W ] b → toB a ⊲[ W ] toB b
toB-⊲ F.hself = hself
toB-⊲ (F.hsuc p) = hsuc (toB-⊲ p)
toB-⊲ (F.hlim n p) = hlim n (toB-⊲ p)
toB-⊲ (F.hLim e p) = hLim e (toB-⊲ p)

Lg-toB : ∀ x → F.LgH x → LgB (toB x)
Lg-toB F.hz l = tt
Lg-toB (F.hs x) l = Lg-toB x l
Lg-toB (F.hl f) (st , l) = (λ {w} n → ⊲ᴮ↑ {S₀} (z⊲ w) (toB-⊲ (st n))) , (λ n → Lg-toB (f n) (l n))
Lg-toB (F.hΩ g) (mo , l) =
  (λ {w} lw e e′ p → ⊲ᴮ↑ {S₀} e′ (toB-⊲ (mo (lg⊲ e′ lw) p))) , (λ c lc → Lg-toB (g c) (l c lc))
```

## §2 逐级的塔

```agda
Sn : ℕ → KS
Sn zero = S₀
Sn (suc k) = step (Sn k)

-- 第 k+1 级之上的第一个 Ω: 新种类上的恒等分支
Ωn : ∀ k → HB (Sn (suc k))
Ωn k = Ωtop (Sn k)

Lg-Ωn : ∀ k → LgB (Ωn k)
Lg-Ωn k = Lg-Ωtop (Sn k)
```

## §3 以高度为下标的塔

`L (k+1)` 是高度 `Ωtop (L k)` 的 `Lev`: 它的种类是一切低于 "第 $L_k$ 级之上的第一个 $\Omega$" 的级. `U` 是 `step (L k)` 对一切 $k$ 的并: 第 $k$ 个分量的新种类 `(k , inj₂ tt)` 以 `HB (L k)` 为坐标.

```agda
L : ℕ → KS
L zero = S₀
L (suc k) = Lev (Ωtop (L k))

FU : ℕ → KS
FU k = step (L k)

U : KS
U = sup ℕ FU

ιU : ∀ k → HB (FU k) → HB U
ιU k = ι {ℕ} {FU} k

-- 第 k 个新种类
νk : ℕ → K U
νk k = k , inj₂ tt
```

**塔的高度.** `θ (k+1)` 是第 $k$ 个新种类上的 $\Omega$-极限, 第 $c$ 支是 `θ k` 接上坐标 $c$ (经 `up`, `ιU` 嵌入). 接在 `θ k` 后面, 所以 `θ k` 字面地是它的第一位置 (取最小坐标 $0$ 那一支), 在一切世界里.

```agda
θ : ℕ → HB U
θ zero = hz
θ (suc k) = hΩ (νk k) (λ c → θ k ⊞ ιU k (up c))

θ-st : ∀ {w} k → θ k ⊲[ w ] θ (suc k)
θ-st {w} k = hLim (botBd U (νk k) w) (⊞-fst (θ k) (ιU k (up hz)))

Λᵁ : HB U
Λᵁ = hl θ
```

**合法: 一条对 $k$ 的一步定理.** `θ k` 合法推出 `θ (k+1)` 合法. 单调: 第 $k$ 个新种类在世界 $w$ 里的第一位置就是 `HB (L k)` 在 `w k` 的旧分量里的 `⊲` (`Step.Pr⁺`, `sup` 的 `Pr`), `up-⊲`, `ι-⊲`, `⊞-⊲` 依次搬过去. 分支合法: `Lg-up`, `Lg-ι`, `Lg-⊞`. 用到的字段: `step` 的新种类 (界, 第一位置, 合法都是 `HB (L k)` 自己的), `sup` 的分量世界. 没有用到 `Lev` 的内部: **对任何 `L` 都成立**.

```agda
Lg-θs : ∀ k → LgB (θ k) → LgB (θ (suc k))
Lg-θs k lθ =
  (λ {w} lw e e′ p → ⊞-⊲ (θ k) (ι-⊲ {ℕ} {FU} {k} {w = w} (up-⊲ p))) ,
  (λ c lc → Lg-⊞ (θ k) (ιU k (up c)) lθ (Lg-ι k (up c) (Lg-up c lc)))

Lg-θ : ∀ k → LgB (θ k)
Lg-θ zero = tt
Lg-θ (suc k) = Lg-θs k (Lg-θ k)

Lg-Λᵁ : LgB Λᵁ
Lg-Λᵁ = (λ n → θ-st n) , Lg-θ
```

**塔与旧高度.** `HtFeed`, `HtOut` 的合法高度经 `toB`, `up`, `ιU 0` 是 `U` 里的合法高度.

```agda
old : F.H → HB U
old x = ιU 0 (up (toB x))

Lg-old : ∀ x → F.LgH x → LgB (old x)
Lg-old x l = Lg-ι 0 (up (toB x)) (Lg-up (toB x) (Lg-toB x l))
```
