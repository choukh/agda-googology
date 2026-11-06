# 骨架总审的编译实验: 封顶点的 `refl` 清单, 与绕过 `Ht` 的最终坍缩

> 不含记号. 配合 `probes/Survey/SkeletonAudit.md` (骨架总审). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 只读导入, 不改任何已有文件.
>
> 两部分:
>
> 1. **§1 封顶点的编译陈述 (全部 `refl`, 定理级的类型事实).** 骨架里从 `FamFold` 到 `GenFold` 的八个无条件闭项都是 `T⁺ h lh`, `h : Ht` (`fac-*`); 一般折叠的读回 `rd₂` 把旧种类的闭包结点读成当前世界的一支 (`nc-old-drop`), 把 `H₀` 坐标里的 $\Omega$-结点读成底坐标那一支 (`encH-bot`); 级顶在 $\Omega$-极限层号处只走底支 (`top-bot`); `step` 的新种类没有 A-回灌 (`fb-new-none`); 求值的世界是基世界, 新种类的界是 $0$ (`W₀X-base`); `GenFold` 的下降在层号是 ℕ-极限处取截断版的常数 (`dnG-hl-const`), 极限站的下降也是常数 (`TG-lim-const`).
> 2. **§2 绕过 `Ht` 的最终坍缩 (构造).** 一般折叠 (`GenFoldRun.Run`) 求到第 $0$ 层, 用 `GenFoldTree.Tree.sum` 直接读成 `A`, 不经 `rd₂` 与 `T⁺`: `Gen0.ev₀ : D L W → A`, 合法由形状给出 (`Lg-sum`). 由此每站一个闭项 `TX X : A` (层 `LX X` 在 `HB (step (Lev X))` 里, 对一切种类结构与一切层号 $X$ 一条定义), 塔上 `TXs s = TX (XG s)`, 极限站 `TXΛ = TX ΛB` (`ΛB : HB KΛc` 是 `GenFold` 塔的层号对角), 都合法, 都有 FGH. **这说明骨架总审的条件 C1 (最终坍缩的输入类型随站增长) 在类型上今天就能满足, 不需要新接口.** 它不说值: 求值的世界仍是基世界 (`W₀X-base`), 塔上的回灌仍只进层号; 读法是判断 (见总审 §3).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SkelDxGen where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht; H₀)
open import OCF.Align.HtTowerFClosed using (T⁺; ord)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (module Tree; accᴸ)
open import OCF.Align.GenFoldInst using (genLev; ldLev; flLev; genStep)
import OCF.Align.GenFoldRun as GR
import OCF.Align.GenFoldRd as GD
open import OCF.Align.GenFoldK using (LX; lLX; oLX; W₀X; lW₀X; ΩX; XG; module KG; TG; dnG)
open import OCF.Align.LvKtIf using (Kc; KΛc)
open import OCF.Align.KcFoldTop using () renaming (top to topLv)
open import OCF.Align.KcFoldTower using (dn₀; dnL₀)
import OCF.Align.KcFoldTower as KC
import OCF.Align.DnFoldK as DK
import OCF.Align.LvKtInst as KI
import OCF.Align.LvTopInst as TI
import OCF.Align.LvRdFold as RF
import OCF.Align.FamFoldAll as FA
import OCF.Align.LvOmClosed as OC
```

## §1 封顶点的编译陈述

### 八个闭项都经 `T⁺` 作用在 `Ht` 上

```agda
fac-TG : TG ≡ T⁺ KG.Λ∞ω KG.lΛ∞ω
fac-TG = refl

fac-TD : DK.TD ≡ T⁺ DK.KQ.Λ∞ω DK.KQ.lΛ∞ω
fac-TD = refl

fac-Tkc : KC.Tkc ≡ T⁺ KC.KU.Λ∞ω KC.KU.lΛ∞ω
fac-Tkc = refl

fac-Tkt : KI.Tkt ≡ T⁺ KI.TrKL.Λ∞ω KI.TrKL.lΛ∞ω
fac-Tkt = refl

fac-Ttr : TI.Ttr ≡ T⁺ TI.TrL.Λ∞ω TI.TrL.lΛ∞ω
fac-Ttr = refl

fac-T∞ω1 : RF.T∞ω1 ≡ T⁺ RF.Λω1 RF.lΛω1
fac-T∞ω1 = refl

fac-T∞ : FA.T∞ ≡ T⁺ FA.Λ∞ FA.lΛ∞
fac-T∞ = refl

fac-TΩ : OC.TΩ ≡ T⁺ OC.HΩd OC.lgHΩd
fac-TΩ = refl
```

### 读回与级顶的有损处

```agda
module _ (T : KS) (G : GenK T) (Ld : LgDn T) where
  open Tree T
  open GD T G Ld using (rd₂; encH)

  -- 旧种类的闭包结点: 只读当前世界的一支, Ω-极限被丢掉
  nc-old-drop : ∀ {W} (lW : LgW (step T) W) (b : Ht) (κ : K T)
                (u : ∀ {W′} → _≤w_ (step T) W W′ → LgW (step T) W′ → D (hs (hs hz)) W′) →
                rd₂ lW b (nc (inj₁ κ) tt u) ≡ rd₂ lW b (u ≤rf lW)
  nc-old-drop lW b κ u = refl

  -- H₀ 的坐标进新种类的界时, Ω-结点只取底坐标那一支
  encH-bot : ∀ (h : A → H₀) → encH (hΩ tt h) ≡ encH (h azero)
  encH-bot h = refl

-- 级顶在 Ω-极限层号处只走底支
top-bot : ∀ {𝕂 : KS} (κ : K 𝕂) (g : E 𝕂 κ → HB 𝕂) →
          topLv (hΩ κ g) ≡ ι {E 𝕂 κ} {λ x → Lev (g x)} (bot 𝕂 κ) (topLv (g (bot 𝕂 κ)))
top-bot κ g = refl

-- step 的新种类没有 A-回灌
fb-new-none : ∀ {T : KS} (G : GenK T) → fbA (genStep G) (inj₂ tt) ≡ inj₂ tt
fb-new-none G = refl

-- 求值的世界是基世界, 新种类的界是 0
W₀X-base : ∀ {S : KS} (X : HB S) → W₀X X ≡ (w₀ (genLev X) , hz)
W₀X-base X = refl

-- 层号是 ℕ-极限时 GenFold 的下降取截断版的常数; 极限站的下降也是常数
dnG-hl-const : ∀ s (f : ℕ → HB (Kc s)) (lb : LgB (hl f)) → dnG s (hl f) lb ≡ dn₀ s (hl f) lb
dnG-hl-const s f lb = refl

TG-lim-const : ∀ (b : HB KΛc) (lb : LgB b) (x : HB (Lev b)) → proj₁ (dnL₀ b lb) x ≡ KI.TrKL.Hω
TG-lim-const b lb x = refl
```

## §2 绕过 `Ht` 的最终坍缩: 一般折叠求到第 0 层, 读成 `A`

与 `GenFoldEv.EvAt` 同一个 `Run`, 目标换成第 $0$ 层 (`τ₀`), 读回换成 `sum` (第 $0$ 层没有闭包结点, `sum` 对一切数据有定义, 合法由 `Lg-sum` 给出).

```agda
module Gen0 (T : KS) (G : GenK T) (Ld : LgDn T) (fl : FbLg G)
  (L : HB (step T)) (lL : LgB L) (o : ∀ {w} → hs hz ⊲[ w ] L) where
  open Tree T
  open GR T G Ld fl L lL o
  open FoldTy T L using (Ig; St; st)

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0

  out₀ : ∀ {W} → LgW L₀ W → D L W → D hz W
  out₀ {W} lW X = yc (Run {W = W} accᴸ X ≤rf lW hself Act n0 Y₀) (τ₀ lW)

  ev₀ : ∀ {W} → LgW L₀ W → D L W → A
  ev₀ lW X = sum azero (n1 ⨾ out₀ lW X)

  lg-ev₀ : ∀ {W} (lW : LgW L₀ W) (X : D L W) → Lg (ev₀ lW X)
  lg-ev₀ lW X = Lg-sum azero (n1 ⨾ out₀ lW X) tt
```

每站一个闭项: 层 `LX X = 2 ⊞ Ωtop (Lev X)` (同 `GenFoldK`), 种类结构 `Lev X`, 对一切 `S` 与 `X` 一条.

```agda
TX : ∀ {S : KS} (X : HB S) → A
TX X = Gen0.ev₀ (Lev X) (genLev X) (ldLev X) (flLev X) (LX X) (lLX X) (oLX X) (lW₀X X) (ΩX X)

Lg-TX : ∀ {S : KS} (X : HB S) → Lg (TX X)
Lg-TX X = Gen0.lg-ev₀ (Lev X) (genLev X) (ldLev X) (flLev X) (LX X) (lLX X) (oLX X) (lW₀X X) (ΩX X)

-- 塔的第 s+1 站 (层号 X_s 在 HB (Kc (s+1)) 里, 随站换类型)
TXs : ℕ → A
TXs s = TX (XG s)

Lg-TXs : ∀ s → Lg (TXs s)
Lg-TXs s = Lg-TX (XG s)

fghXs : ℕ → ℕ → ℕ
fghXs s = FLv.FGH (ord (TXs s))

-- 极限站: 层号对角 ΛB : HB KΛc, 种类结构 Lev ΛB = sup ℕ (Lev ∘ Bᴧ)
TXΛ : A
TXΛ = TX KG.ΛB

Lg-TXΛ : Lg TXΛ
Lg-TXΛ = Lg-TX KG.ΛB

fghXΛ : ℕ → ℕ
fghXΛ = FLv.FGH (ord TXΛ)
```

**这不说明值.** `TX X` 的求值世界是基世界 (`W₀X-base`): `Lev X` 的种类的界都是底, 闭包结点的分支只在更大的世界里才有内容, 而折叠里升界的只有 `fbA` 有定义的种类 (`fb-new-none`, `genSupNo`). 所以 `TXs s` 随 $s$ 的增长是读法 (判断), 没有定理; 本文件只证明 "最终坍缩可以不经 `Ht`" 这一个类型事实.
