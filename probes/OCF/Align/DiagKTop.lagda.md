# 可数层的对角 (四): 候选闭项的形状, 缺的一块写成类型

> 不含记号. 入口 [DiagK](DiagK.lagda.md). 目标 (作者 2026-11-05): $\psi_0\Lambda$ 的候选闭项. 本路的形状: 每一级 $k$ 一个闭项 $t_k : A$, 对角 $T=$ `Dg t` ([DiagKSum](DiagKSum.lagda.md)), 合法由部分和的形状给出.
>
> - **一族级与级顶** `Tower`: 种类结构 `Lvl k`, 合法高度 `top k : HB (Lvl k)`. 两个实例 (定义与合法是定理, 读法是判断):
>   - `towerL′`: `Lvl k = L′ (k+1)` ([HtTowerNStage](HtTowerNStage.lagda.md)), `top k = ι true (Ωtop (L′ k))`. 读法 $\Lambda_k$ ($\Lambda_0=\Omega_2$, $\Lambda_{k+1}\approx\Omega_{\Lambda_k+1}$, `HtTowerU` 的判断), 上确界读 $\Lambda$.
>   - `towerSn`: `Lvl k = Sn (k+1)`, `top k = Ωn k`. 读法 $\Omega_{k+2}$, 上确界读 $\Omega_\omega$.
> - **缺的一块** `LevelFold T`: 对一切 $k$, 一切 `Lvl k` 上的合法高度, 一个 $A$ 里的合法闭项. 读法要求 (判断): `fold k Λ` 读 $\psi_0(\Omega_\Lambda)$.
> - **候选闭项** `Top.Tᴰ`: $T=\mathrm{Dg}\,(k\mapsto \mathrm{fold}\,k\,(\mathrm{top}\,k))$, `Lg-Tᴰ` 对一切 `LevelFold` 是定理, `fgh`. 读法 (判断, **有条件**): 若 `fold` 读 $\psi_0(\Omega_\Lambda)$, 则 $t_k$ 读 $\psi_0(\Omega_{\Lambda_k})$, $T$ 读 $\sup_k\psi_0(\Omega_{\Lambda_k})=\psi_0(\Lambda)$ (部分和的值与上确界的关系见 `DiagKSum.Dg≈sup`, 其前提 "上确界加法封闭" 在这里是判断).
> - **合法性是盲的** (定理): 常值 $0$ 的 "折叠" (`dummy`) 也给出合法的 $T$ (`Lg-blind`). 所以 `Lg-Tᴰ` 只说形状, 读法全在 `fold` 上.
> - **已有的槽位** (定理): `towerSn` 的第 0 级 (`Sn 1`) 有现成的折叠 `fold₁` (`HtTowerFClosed.T⁺`), 它下面一级 `Sn 0` 有 `fold₀` (经 `fromB` 用 `HtFeedClosed.TΛ`); `towerSn` 第 $k\ge1$ 级没有. `towerL′` 的第 0 级是 `L′ 1`, 含 `Lev` 分量, **没有现成的折叠**; [DiagKLev](DiagKLev.lagda.md) 说 `HtTowerFFold` 那样恰好改一个分量的写法在这里要判定高度相等.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagKTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerU using (Sn; Ωn; Lg-Ωn)
open import OCF.Align.HtTowerNStage using (L′; two)
import OCF.Align.HtFeedTree as F
import OCF.Align.HtFeedClosed as FC
import OCF.Align.HtTowerFClosed as TC
open import OCF.Align.DiagKSum using (Dg; Lg-Dg; pre; pre-st; ord)
import OCF.Free.Level as FL
```

## §1 一族级与级顶

```agda
record Tower : Set₁ where
  field
    Lvl  : ℕ → KS
    top  : ∀ k → HB (Lvl k)
    ltop : ∀ k → LgB (top k)
open Tower public

λh : ∀ k → HB (L′ (suc k))
λh k = ι {F = two (step (L′ k)) (Lev (Ωtop (L′ k)))} true (Ωtop (L′ k))

Lg-λh : ∀ k → LgB (λh k)
Lg-λh k = Lg-ι {F = two (step (L′ k)) (Lev (Ωtop (L′ k)))} true (Ωtop (L′ k)) (Lg-Ωtop (L′ k))

towerL′ : Tower
towerL′ = record { Lvl = λ k → L′ (suc k) ; top = λh ; ltop = Lg-λh }

towerSn : Tower
towerSn = record { Lvl = λ k → Sn (suc k) ; top = Ωn ; ltop = Lg-Ωn }
```

## §2 缺的一块与候选闭项

```agda
record LevelFold (Tw : Tower) : Set where
  field
    fold : ∀ k (Λ : HB (Lvl Tw k)) → LgB Λ → A
    lg   : ∀ k Λ (lΛ : LgB Λ) → Lg (fold k Λ lΛ)
open LevelFold public

module Top (Tw : Tower) (Fd : LevelFold Tw) where
  t : ℕ → A
  t k = fold Fd k (top Tw k) (ltop Tw k)

  Tᴰ : A
  Tᴰ = Dg t

  Lg-Tᴰ : Lg Tᴰ
  Lg-Tᴰ = Lg-Dg t (λ k → lg Fd k (top Tw k) (ltop Tw k))

  t⊲ : ∀ k → pre t k ⊲ pre t (suc k)
  t⊲ = pre-st t

  fgh : ℕ → ℕ
  fgh = FL.FGH (ord Tᴰ)
```

**合法性是盲的.**

```agda
dummy : ∀ Tw → LevelFold Tw
dummy Tw = record { fold = λ _ _ _ → azero ; lg = λ _ _ _ → tt }

Lg-blind : ∀ Tw → Lg (Top.Tᴰ Tw (dummy Tw))
Lg-blind Tw = Top.Lg-Tᴰ Tw (dummy Tw)
```

## §3 已有的槽位: `towerSn` 的第 0, 1 级

第 0 级 `Sn 1 = step S₀` 就是 `HtTowerF` 的层; 再下一级 `HB S₀` 与 `HtFeedTree.H` 同形 (`fromB`). 两个现成的折叠都接受各自层上的一切合法高度.

```agda
fromB : HB S₀ → F.H
fromB hz = F.hz
fromB (hs x) = F.hs (fromB x)
fromB (hl f) = F.hl (λ n → fromB (f n))
fromB (hΩ tt g) = F.hΩ (λ c → fromB (g c))

fromB-⊲ : ∀ {a b w} → a ⊲[ w ] b → fromB a F.⊲[ w ] fromB b
fromB-⊲ hself = F.hself
fromB-⊲ (hsuc p) = F.hsuc (fromB-⊲ p)
fromB-⊲ (hlim n p) = F.hlim n (fromB-⊲ p)
fromB-⊲ (hLim e p) = F.hLim e (fromB-⊲ p)

Lg-fromB : ∀ x → LgB x → F.LgH (fromB x)
Lg-fromB hz l = tt
Lg-fromB (hs x) l = Lg-fromB x l
Lg-fromB (hl f) (st , l) = (λ n → fromB-⊲ (st {azero} n)) , (λ n → Lg-fromB (f n) (l n))
Lg-fromB (hΩ tt g) (mo , l) =
  (λ {c} {c′} lc′ p → fromB-⊲ (mo {c′} {c} {c′} lc′ p C.self p)) , (λ c lc → Lg-fromB (g c) (l c lc))

-- HB S₀ 上的折叠 (HtFeed)
fold₀ : (Λ : HB S₀) → LgB Λ → A
fold₀ Λ l = FC.TΛ (fromB Λ) (Lg-fromB Λ l)

Lg-fold₀ : ∀ Λ (l : LgB Λ) → Lg (fold₀ Λ l)
Lg-fold₀ Λ l = FC.Lg-TΛ (fromB Λ) (Lg-fromB Λ l)

-- HB (Sn 1) 上的折叠 (HtTowerF); Sn 1 = step S₀ 定义地就是 HtTowerFTree 的 S₁
fold₁ : (Λ : HB (Sn 1)) → LgB Λ → A
fold₁ Λ l = TC.T⁺ Λ l

Lg-fold₁ : ∀ Λ (l : LgB Λ) → Lg (fold₁ Λ l)
Lg-fold₁ Λ l = TC.Lg-T⁺ Λ l

-- towerSn 第 0 级的 t₀ 有现成的定义: ψ₀(Ω_{Ω₂}) 的读法 (判断)
t₀Sn : A
t₀Sn = fold₁ (Ωn 0) (Lg-Ωn 0)
```
