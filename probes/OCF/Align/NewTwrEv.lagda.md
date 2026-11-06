# 新塔 (三): 每站的下降, 值域是本站读回所在的类型

> 不含记号. 入口 [NewTwr](NewTwr.lagda.md), 接口 [NewTwrIf](NewTwrIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 `evN X : HB (step (Lev X))`.** 与 [GenFoldK](GenFoldK.lagda.md) 的 `evB X` 同一个求值 (层, 世界, 数据, 求到第 2 层的式子在本篇重写, 与 GenFold 的定义相等, 见 `NewTwrCmp`) (层 $L_X=2\boxplus\Omega_{\mathrm{top}}(\mathrm{Lev}\,X)$, 基世界, $\Omega_{L_X}$ 的数据, 一般折叠到第 2 层, `EvX.out₂`), 读回换成 [NewTwrRd](NewTwrRd.lagda.md) 的 `rdG`: **输出在 `HB (step (Lev X))`, 不在 `Ht`**. 合法由读回的形状给出 (`lg-evN`). 头是新种类的 $\Omega$-结点 (`evN-head`, `refl`, 对一切 $X$).
> - **§2 下降 `ρ b = hs (ρ′ b)`.** 层号是后继 $b=\mathrm{hs}\,X$ 时 `Lev b = step (Lev X)` (定义相等), $\rho'\,b=$ `evN X`; 不是后继时取 $0$ (新塔里不出现: 起点取 $2$, 之后每站层号的头都是后继, 构造文件 `NewTwrK.B-suc`). 外面包一个后继, 让下一站的层号的头仍是后继, 下一站仍走求值那一支 (定义相等, 不判定). `rdN : RdTower` (接口 §1).
>
> **下降只读层号.** 同 `GenFoldK.dnG`: `RdK` 给的是层号 $b$ 与它的合法; 求值的层与数据由 $b$ 决定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NewTwrEv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (module Tree; topStepG; accᴸ)
open import OCF.Align.GenFoldInst using (genLev; ldLev; flLev)
import OCF.Align.GenFoldRun as GR
import OCF.Align.NewTwrRd as NR
open import OCF.Align.NewTwrIf
```

## §1 第 $X$ 级之上一级的求值, 读回进 `HB (step (Lev X))`

层, 世界, 数据与 `GenFoldK` 的 `LX`, `W₀X`, `ΩX` 逐字相同 (这里重写一遍, 不导入 `GenFoldK`, 让闭项的导入闭包不经过读进 `Ht` 的 `GenFoldEv.evAt`, `GenFoldK.evB`; 逐项定义相等见 [NewTwrCmp](NewTwrCmp.lagda.md)). 求到第 2 层的式子同 `GenFoldEv.EvAt.out₂`.

```agda
two : ∀ {S : KS} → HB S
two = hs (hs hz)

LX : ∀ {S : KS} (X : HB S) → HB (step (Lev X))
LX X = two ⊞ Ωtop (Lev X)

lLX : ∀ {S : KS} (X : HB S) → LgB (LX X)
lLX X = Lg-⊞ two (Ωtop (Lev X)) tt (Lg-Ωtop (Lev X))

oLX : ∀ {S : KS} (X : HB S) {w} → hs hz ⊲[ w ] LX X
oLX X = ⊲ᴮ-tr (hsuc hself) (⊞-fst two (Ωtop (Lev X)))

eLX : ∀ {S : KS} (X : HB S) {w} → two ⊲[ w ] LX X
eLX X = ⊞-fst two (Ωtop (Lev X))

W₀X : ∀ {S : KS} (X : HB S) → Wd (step (Lev X))
W₀X X = w₀ (genLev X) , hz

lW₀X : ∀ {S : KS} (X : HB S) → LgW (step (Lev X)) (W₀X X)
lW₀X X = lw₀ (genLev X) , tt

ΩX : ∀ {S : KS} (X : HB S) → DK (Lev X) (LX X) (W₀X X)
ΩX X = Tree.Om.Ωd (Lev X) (topStepG (tpK (genLev X))) (LX X)

module EvN {S : KS} (X : HB S) where
  open Tree (Lev X)
  open GR (Lev X) (genLev X) (ldLev X) (flLev X) (LX X) (lLX X) (oLX X)
  open FoldTy (Lev X) (LX X) using (Ig; St; st; tg)

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0

  out₂ : ∀ {W} → LgW L₀ W → two ⊲[ W ] LX X → D (LX X) W → D two W
  out₂ {W} lW e D′ = yc (Run {W = W} accᴸ D′ ≤rf lW hself Act n0 Y₀) (tg ≤rf e lW)

out₂N : ∀ {S : KS} (X : HB S) → DK (Lev X) (hs (hs hz)) (W₀X X)
out₂N X = EvN.out₂ X (lW₀X X) (eLX X) (ΩX X)

evN : ∀ {S : KS} (X : HB S) → HB (step (Lev X))
evN X = NR.rdG (Lev X) (genLev X) (ldLev X) (lW₀X X) hz (out₂N X)

lg-evN : ∀ {S : KS} (X : HB S) → LgB (evN X)
lg-evN X = NR.Lg-rdG (Lev X) (genLev X) (ldLev X) (lW₀X X) hz (out₂N X) tt

-- 头是新种类 (坐标 HB (Lev X)) 的 Ω-结点
evN-head : ∀ {S : KS} (X : HB S) → Σ (HB (Lev X) → HB (step (Lev X))) (λ g → evN X ≡ hΩ (inj₂ tt) g)
evN-head X = _ , refl
```

## §2 下降

```agda
ρ′ : ∀ {S : KS} (b : HB S) → HB (Lev b)
ρ′ hz = hz
ρ′ (hs X) = evN X
ρ′ (hl f) = hz
ρ′ (hΩ κ g) = hz

lρ′ : ∀ {S : KS} (b : HB S) → LgB (ρ′ b)
lρ′ hz = tt
lρ′ (hs X) = lg-evN X
lρ′ (hl f) = tt
lρ′ (hΩ κ g) = tt

ρ : ∀ {K : KS} → RdK K
ρ b lb = hs (ρ′ b) , lρ′ b

rdN : RdTower
rdN s = ρ
```
