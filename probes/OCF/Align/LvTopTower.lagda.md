# 整座塔加对角 (一): 以 `FoldAt` 为模块参数的塔, 极限站, 对角, 闭项

> 不含记号. 入口 [LvTop](LvTop.lagda.md), 接口 [LvTopIf](LvTopIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 本篇的定理都以模块参数 (一个 `FoldAt` 实例与读法 `σ-of`) 为前提; 无条件的实例在 [LvTopInst](LvTopInst.lagda.md).
>
> - **§1 塔** `Tower CovS F σ-of b₀`: 第 $0$ 站的界 $B_0=b_0$ (有限级起; 截断版取 $b_0=0$, 全塔版的 $b_0$ 是参数). 第 $s+1$ 站在界 $B_s$ 的顶码 (`top`, 目标 $B_s$) 上折叠, 世界取全 $0$ (与 `LvRd` 的有限级从 `v₀` 起同), 得级顶的回灌输出 $H_s$ 与读回 $r_s$; 新界 $B_{s+1}=B_s\boxplus\sigma(H_s)$ (`LvRdWk.lvShapeδ` 的形状, 读法 $\sigma$ 与站号无关). 第 $s+1$ 站的码在新界之下就是 `κ s = cd (⊞-fst …)`, 目标是旧界 (`κ-tgt`, 同 `lvlδ`). 界, 合法性, 覆盖证据, 输出四者对 $s$ 同时递归.
> - **§2 极限站 (W1 的部分和与 `canon`)**: 极限界是部分和的 ℕ-极限 `Bω = hl psum` (`LvFbFac.FacPath.PSum`, 增量 $\sigma(H_s)$; `psum≡B`: 与塔的界逐站相等). 各站的码经 `NegLvRdWk.Canon.canon` 进极限 (`stageω`): 每个码沿它出生的那一站进极限, 相干 (`stageω-coh`) 且保目标 (`stageω-tgt`). 极限码 (界 `Bω` 的顶码) 的槽是各站读回 $r_s$ 从出生的那一站 (`ι s`, 并的第 $s$ 个分量) 直接进极限再取部分和 (`U`, `LvFbFac.Lim.Inc.U` 的形状), 合法由形状给出 (`lslotω`). 极限站在这个世界里再折叠一次, 得 `Hω` (`Lim` 子模块, 另一个 `FoldAt` 实例, 只要覆盖 `Bω`).
> - **§3 对角与闭项**: 各站级顶的回灌输出累加 `cum k = H₀ ⊞ … ⊞ H_k`, 对角 `Λ∞ = hl cum` (对照 `FamFoldAll.Λ∞`, `LvRdFold.ΛF`), 闭项 `TΛ∞ = T⁺ Λ∞ lΛ∞` 与 `fghΛ∞`; 加上极限站: `Λ∞ω = Λ∞ ⊞ Hω`, `TΛ∞ω`, `fghΛ∞ω` (对照 `LvRdFold.Λω1 = ΛF ⊞ Hω1`). 合法由形状给出: `Lg-TΛ∞`, `Lg-TΛ∞ω` 只用 `FoldAt` 的两条律 `lrt`, `lgH` 与 `Lg-⊞`, `⊞-fst`, `Lg-ι`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvTopTower where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺; ord)
open import OCF.Align.LvFbCode using (Code; RB; bH; bP; bL; bΩ; tgt; cd; cd-tgt)
open import OCF.Align.LvFbFac using (module FacPath)
open import OCF.Align.NegLvRdWk using (module Canon)
open import OCF.Align.LvTopIf
```

## §0 顶码, 全 0 的世界, 搬运

```agda
-- 界 b 的顶码: 停在界上, 目标就是 b (定义地)
top : ∀ b → Cod b
top b = bH , tt

w₀ : ∀ {b} → Wb b
w₀ k = hz

lw₀ : ∀ {b} → LgWb {b} w₀
lw₀ k = tt

-- 沿坐标的相等搬运槽 (对一个元素, 不对函数)
tpL : ∀ {t t′ : HB S₀} → t ≡ t′ → HB (Lev t) → HB (Lev t′)
tpL e x = subst (λ z → HB (Lev z)) e x

lg-tpL : ∀ {t t′ : HB S₀} (e : t ≡ t′) x → LgB x → LgB (tpL e x)
lg-tpL refl x l = l
```

## §1 塔

```agda
module Tower (CovS : HB S₀ → Set) (F : FoldAt CovS)
             (σ-of : Ht → HB S₀) (lσ : ∀ h → LgB (σ-of h))
             (b₀ : HB S₀) (lb₀ : LgB b₀)
             (cov0 : CovS b₀) (covS : ∀ t h → CovS t → CovS (t ⊞ σ-of h)) where
  open FoldAt F

  -- 第 s+1 站: 界 B s, 覆盖证据 cB s, 在顶码上折叠的输出 Hs s
  B   : ℕ → HB S₀
  lB  : ∀ s → LgB (B s)
  cB  : ∀ s → CovS (B s)
  Hs  : ℕ → Ht
  B zero = b₀
  B (suc s) = B s ⊞ σ-of (Hs s)
  lB zero = lb₀
  lB (suc s) = Lg-⊞ (B s) (σ-of (Hs s)) (lB s) (lσ (Hs s))
  cB zero = cov0
  cB (suc s) = covS (B s) (Hs s) (cB s)
  Hs s = H (lB s) (top (B s)) (cB s) w₀ lw₀

  lHs : ∀ s → LgB (Hs s)
  lHs s = lgH (lB s) (top (B s)) (cB s) w₀ lw₀

  -- 第 s+1 站的读回, 在第 B s 级
  rts : ∀ s → HB (Lev (B s))
  rts s = rt (lB s) (top (B s)) (cB s) w₀ lw₀

  lrts : ∀ s → LgB (rts s)
  lrts s = lrt (lB s) (top (B s)) (cB s) w₀ lw₀

  -- 增量: 第 s 站输出的读法 (与站号无关)
  σs : ℕ → HB S₀
  σs s = σ-of (Hs s)

  lσs : ∀ s → LgB (σs s)
  lσs s = lσ (Hs s)

  -- 第 s+1 站的码在新界之下, 目标是旧界 (lvlδ 的形状)
  κ : ∀ s → Cod (B (suc s))
  κ s = cd (⊞-fst {w = azero} (B s) (σs s))

  κ-tgt : ∀ s → tgt (κ s) ≡ B s
  κ-tgt s = cd-tgt (⊞-fst {w = azero} (B s) (σs s))

  -- 界逐站是第一位置 (一切 A-世界)
  B-fst : ∀ s {w} → B s ⊲[ w ] B (suc s)
  B-fst s = ⊞-fst (B s) (σs s)
```

## §2 极限站: W1 的部分和与 `canon`

```agda
  module PS = FacPath.PSum azero tt b₀ lb₀ σs lσs
  module CN = Canon azero tt b₀ lb₀ σs lσs
  open PS using (psum; lps)

  psum≡B : ∀ s → psum s ≡ B s
  psum≡B zero = refl
  psum≡B (suc s) = cong (_⊞ σs s) (psum≡B s)

  -- 极限界: 部分和的 ℕ-极限
  Bω : HB S₀
  Bω = hl psum

  lBω : LgB Bω
  lBω = PS.lB

  -- 各站的顶码 (部分和坐标里) 经 canon 进极限
  topP : ∀ s → CN.CS s
  topP s = bH , tt

  stageω : ∀ s → Cod Bω
  stageω s = CN.canon s (topP s)

  stageω-tgt : ∀ s → tgt (stageω s) ≡ B s
  stageω-tgt s = trans (CN.canon-tgt s (topP s)) (psum≡B s)

  -- 相干: 第 s 站的顶码先弱化到第 s+1 站再进极限, 与直接进极限相同
  stageω-coh : ∀ s → CN.canon (suc s) (CN.wkS s (topP s)) ≡ stageω s
  stageω-coh s = CN.canon-coh s (topP s)

  -- 各站读回搬到部分和坐标 (逐元素搬运, 不要外延)
  rtP : ∀ s → HB (Lev (psum s))
  rtP s = tpL (sym (psum≡B s)) (rts s)

  lrtP : ∀ s → LgB (rtP s)
  lrtP s = lg-tpL (sym (psum≡B s)) (rts s) (lrts s)

  -- W1: 第 s 站的读回从出生的那一站 (并的第 s 个分量) 直接进极限, 取部分和
  ιP : ∀ s → HB (Lev (psum s)) → HB (Lev Bω)
  ιP s = ι {F = λ n → Lev (psum n)} s

  U : ℕ → HB (Lev Bω)
  U zero = ιP zero (rtP zero)
  U (suc n) = U n ⊞ ιP (suc n) (rtP (suc n))

  lU : ∀ n → LgB (U n)
  lU zero = Lg-ι {F = λ n → Lev (psum n)} zero (rtP zero) (lrtP zero)
  lU (suc n) = Lg-⊞ (U n) (ιP (suc n) (rtP (suc n))) (lU n) (Lg-ι {F = λ n → Lev (psum n)} (suc n) (rtP (suc n)) (lrtP (suc n)))

  slotω : HB (Lev Bω)
  slotω = hl U

  lslotω : LgB slotω
  lslotω = (λ n → ⊞-fst (U n) (ιP (suc n) (rtP (suc n)))) , lU

  -- 极限界之下的世界: 极限码 (顶码) 的槽是 slotω, 其余为 0
  Wω : Wb Bω
  Wω (bH , v) = slotω
  Wω (bP r , v) = hz
  Wω (bL n r , v) = hz
  Wω (bΩ ra r , v) = hz

  lWω : LgWb Wω
  lWω (bH , v) = lslotω
  lWω (bP r , v) = tt
  lWω (bL n r , v) = tt
  lWω (bΩ ra r , v) = tt
```

## §3 对角与闭项

```agda
  cum : ℕ → Ht
  cum zero = Hs zero
  cum (suc k) = cum k ⊞ Hs (suc k)

  lcum : ∀ k → LgB (cum k)
  lcum zero = lHs zero
  lcum (suc k) = Lg-⊞ (cum k) (Hs (suc k)) (lcum k) (lHs (suc k))

  Λ∞ : Ht
  Λ∞ = hl cum

  lΛ∞ : LgB Λ∞
  lΛ∞ = (λ k → ⊞-fst (cum k) (Hs (suc k))) , lcum

  TΛ∞ : A
  TΛ∞ = T⁺ Λ∞ lΛ∞

  Lg-TΛ∞ : Lg TΛ∞
  Lg-TΛ∞ = Lg-T⁺ Λ∞ lΛ∞

  fghΛ∞ : ℕ → ℕ
  fghΛ∞ = FLv.FGH (ord TΛ∞)

  -- 极限站: 在极限界的顶码上, 世界 Wω, 再折叠一次 (另一个 FoldAt 实例, 只要覆盖 Bω)
  module Lim (CovL : HB S₀ → Set) (FL : FoldAt CovL) (covL : CovL Bω) where
    Hω : Ht
    Hω = FoldAt.H FL lBω (top Bω) covL Wω lWω

    lHω : LgB Hω
    lHω = FoldAt.lgH FL lBω (top Bω) covL Wω lWω

    Λ∞ω : Ht
    Λ∞ω = Λ∞ ⊞ Hω

    lΛ∞ω : LgB Λ∞ω
    lΛ∞ω = Lg-⊞ Λ∞ Hω lΛ∞ lHω

    TΛ∞ω : A
    TΛ∞ω = T⁺ Λ∞ω lΛ∞ω

    Lg-TΛ∞ω : Lg TΛ∞ω
    Lg-TΛ∞ω = Lg-T⁺ Λ∞ω lΛ∞ω

    fghΛ∞ω : ℕ → ℕ
    fghΛ∞ω = FLv.FGH (ord TΛ∞ω)
```

## §4 全塔: 一切码上的折叠

`FoldAll` 给出一切码上的折叠时, 覆盖证据都是 `tt`, 塔与极限站用同一个实例.

```agda
module Full (F : FoldAll) (σ-of : Ht → HB S₀) (lσ : ∀ h → LgB (σ-of h)) (b₀ : HB S₀) (lb₀ : LgB b₀) where
  open Tower (λ _ → ⊤) F σ-of lσ b₀ lb₀ tt (λ _ _ _ → tt) public
  open Lim (λ _ → ⊤) F tt public
```
