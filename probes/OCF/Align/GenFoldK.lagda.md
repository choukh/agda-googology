# 对一般种类结构的折叠 (六): 塔上的下降, 无条件闭项, 形状定理

> 不含记号. 入口 [GenFold](GenFold.lagda.md), 接口 [GenFoldIf](GenFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数.
>
> - **§1 每站一条的下降 `dnG`.** 站 $s$ 的层号是后继 $b=\mathrm{hs}\,X$ 时 (第 $s+1$ 站总是: `KcFoldTower.Shape.B-suc-shape`; 第 0 站 $b_0=1$ 也是), `Lev b = step (Lev X)` (定义相等), 于是取 $T=$ `Lev X`, 层 $L_X = 2\boxplus\mathrm{hs}(\Omega_{\mathrm{top}}(\mathrm{Lev}\,X))$, 在 `HB (step T)` 里求 $\Omega_{L_X}$ (`Ωd`) 到第 2 层, 读成 `Ht` (`GenFoldEv.EvAt`, `GenK` 由 `GenFoldInst.genLev X` 对 $X$ 结构递归给出). 层号不是后继时取截断版的常数. **下降只读层号 $b$** (`DnTower` 给的就是 $b$ 与它的合法), 不读输入: 输入要当层用必须合法, `DnK` 的函数对一切输入定义, 不带输入的合法 (判断: 要对输入用 "合法处恒等的夹法", 撞 `HtTotalNeg.no-clamp`). 塔在第 $s$ 站喂给下降的输入恒是读回 $\mathrm{rts}\,s=\mathrm{hs}(\mathrm{top}\,b)$, 它是 $b$ 的函数; 对 $b=\mathrm{hs}\,X$, $L_X = 2\boxplus\mathrm{rts}\,s$ (定义相等, `layer-rts`).
> - **§2 无条件闭项** `TG = KG.TΛ∞ω` (`KG = KD dnG dnL₀`), 证书 `Lg-TG`, FGH `fghG`; 只有有限站的 `TG∞`.
> - **§3 形状定理 (对一切 $s$, `refl`).** `Hs-ev`: 第 $s+1$ 站的回灌输出就是在层 $2\boxplus\mathrm{rts}(s+1)$ 上的求值 (`layer-rts`: 这个层就是 $2\boxplus$ 读回, 读回的新种类结点是层的头); `Hs-hl`: 它的头是 $\mathbb N$-极限 (折叠在第 2 层目标上走 "升" 的那一支, `RKi … rise`), 所以 **每一站都不是 $2$** (`not-dnC`, 对照 `NegDnFoldBlind.HsC`: 那个反模型每站都是 $2$).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenFoldK where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (Ht; H₀)
open import OCF.Align.GenFoldIf using (n1; nc; _⨾_)
open import OCF.Align.HtTowerFClosed using (ord)
open import OCF.Align.LvKtIf using (Kc)
open import OCF.Align.KcFoldIf using (DnK; DnTower)
open import OCF.Align.KcFoldTower using (module KD; module Shape; dn₀; dnL₀)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (module Tree; topStepG)
open import OCF.Align.GenFoldInst using (genLev; ldLev; flLev)
open import OCF.Align.GenFoldEv using (module EvAt)
```

## §1 每站一条的下降

```agda
two : ∀ {S : KS} → HB S
two = hs (hs hz)

-- 第 X 级之上一级的层: 2 ⊞ (读回的新种类结点)
LX : ∀ {S : KS} (X : HB S) → HB (step (Lev X))
LX X = two ⊞ Ωtop (Lev X)

lLX : ∀ {S : KS} (X : HB S) → LgB (LX X)
lLX X = Lg-⊞ two (Ωtop (Lev X)) tt (Lg-Ωtop (Lev X))

oLX : ∀ {S : KS} (X : HB S) {w} → hs hz ⊲[ w ] LX X
oLX X = ⊲ᴮ-tr (hsuc hself) (⊞-fst two (Ωtop (Lev X)))

eLX : ∀ {S : KS} (X : HB S) {w} → two ⊲[ w ] LX X
eLX X = ⊞-fst two (Ωtop (Lev X))

module EvX {S : KS} (X : HB S) = EvAt (Lev X) (genLev X) (ldLev X) (flLev X) (LX X) (lLX X) (oLX X)

-- 求值的世界: 基世界, 新种类的界取 0
W₀X : ∀ {S : KS} (X : HB S) → Wd (step (Lev X))
W₀X X = w₀ (genLev X) , hz

lW₀X : ∀ {S : KS} (X : HB S) → LgW (step (Lev X)) (W₀X X)
lW₀X X = lw₀ (genLev X) , tt

-- Ω_{L_X} 的数据 (Ω-行对一切种类一条)
ΩX : ∀ {S : KS} (X : HB S) → DK (Lev X) (LX X) (W₀X X)
ΩX X = Tree.Om.Ωd (Lev X) (topStepG (tpK (genLev X))) (LX X)

evB : ∀ {S : KS} (X : HB S) → Ht
evB X = EvX.evAt X (lW₀X X) (eLX X) (ΩX X)

lg-evB : ∀ {S : KS} (X : HB S) → LgB (evB X)
lg-evB X = EvX.lg-evAt X (lW₀X X) (eLX X) (ΩX X)

constD : ∀ {Q : KS} (h : Ht) → LgB h → DnK Q
constD h lh = (λ _ → h) , (λ _ _ → lh)

dnG : DnTower
dnG s hz lb = dn₀ s hz lb
dnG s (hs X) lb = constD (evB X) (lg-evB X)
dnG s (hl f) lb = dn₀ s (hl f) lb
dnG s (hΩ κ g) lb = dn₀ s (hΩ κ g) lb
```

## §2 无条件闭项

```agda
module KG = KD dnG dnL₀

TG : A
TG = KG.TΛ∞ω

Lg-TG : Lg TG
Lg-TG = KG.Lg-TΛ∞ω

fghG : ℕ → ℕ
fghG = FLv.FGH (ord TG)

TG∞ : A
TG∞ = KG.TΛ∞

Lg-TG∞ : Lg TG∞
Lg-TG∞ = KG.Lg-TΛ∞
```

## §3 形状定理

```agda
XG : ∀ s → HB (Kc (suc s))
XG s = Shape.X dnG dnL₀ s

-- 第 0 站: 层号 1 = hs hz, 在 Ht 上求 Ω_{2 ⊞ hs Ω₂}
Hs0-ev : KG.Hs 0 ≡ evB {S₀} hz
Hs0-ev = refl

-- 第 s+1 站: 回灌输出就是第 X s 级之上的求值
Hs-ev : ∀ s → KG.Hs (suc s) ≡ evB (XG s)
Hs-ev s = refl

-- 求值的层就是 2 ⊞ 读回 (读回的新种类结点是层的头)
layer-rts : ∀ s → hs (LX (XG s)) ≡ two ⊞ KG.rts (suc s)
layer-rts s = refl

rts-head : ∀ s → KG.rts (suc s) ≡ hs (hΩ (inj₂ tt) (up {Lev (XG s)}))
rts-head s = refl
```

**读回的新种类结点进了输出 (对一切级 $X$, `refl`).** $\Omega_{L_X}$ 的数据是 `n1 ⨾ nc (inj₂ tt) _ u` (`ΩX-head`): 层的头是读回的新种类 (`step (Lev X)` 的 `inj₂ tt`) 的 $\Omega$-结点, `Ωd` 的 $\Omega$-行给出这个种类的闭包结点. 折叠在第 2 层目标上**保留**它 (`out₂-kept`: 输出是 `a ⨾ nc (inj₂ tt) tt u′`), 读回 `rd₂` 把新种类的闭包读成 `Ht` 的 κH 的 $\Omega$-结点 (`evB-head`). 所以每一站的回灌输出的头是 κH 的 $\Omega$-结点, 它在折叠里只来自层头的那个新种类结点.

```agda
Br : (T : KS) → HB (step T) → Wd (step T) → Set
Br T L W = ∀ {W′} → _≤w_ (step T) W W′ → LgW (step T) W′ → DK T L W′

ΩX-head : ∀ {S : KS} (X : HB S) → Σ (Br (Lev X) (LX X) (W₀X X)) (λ u → ΩX X ≡ (n1 ⨾ nc (inj₂ tt) tt u))
ΩX-head X = _ , refl

out₂-kept : ∀ {S : KS} (X : HB S) →
  Σ (DK (Lev X) two (W₀X X)) (λ a → Σ (Br (Lev X) two (W₀X X)) (λ u → EvX.out₂ X (lW₀X X) (eLX X) (ΩX X) ≡ (a ⨾ nc (inj₂ tt) tt u)))
out₂-kept X = _ , _ , refl

evB-head : ∀ {S : KS} (X : HB S) → Σ (H₀ → Ht) (λ g → evB X ≡ hΩ (inj₂ tt) g)
evB-head X = _ , refl

Hs-head : ∀ s → Σ (H₀ → Ht) (λ g → KG.Hs s ≡ hΩ (inj₂ tt) g)
Hs-head zero = evB-head {S₀} hz
Hs-head (suc s) = evB-head (XG s)

hΩ≢hs : ∀ {g : H₀ → Ht} {x : Ht} → ¬ (hΩ (inj₂ tt) g ≡ hs x)
hΩ≢hs ()

-- 每一站都不是 2 (排除 NegDnFoldBlind.dnC, NegGenFold.dnGenC 那种每站输出 2 的下降)
not-dnC : ∀ s → ¬ (KG.Hs s ≡ hs (hs hz))
not-dnC s e with Hs-head s
... | g , q = hΩ≢hs (trans′ (sym′ q) e)
  where
  sym′ : ∀ {a b : Ht} → a ≡ b → b ≡ a
  sym′ refl = refl
  trans′ : ∀ {a b c : Ht} → a ≡ b → b ≡ c → a ≡ c
  trans′ refl q′ = q′
```
