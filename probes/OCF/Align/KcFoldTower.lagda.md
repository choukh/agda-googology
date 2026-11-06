# 种类塔上的一级折叠 (二): 塔, 形状定理, 条件版 (只缺下降) 与无条件闭项

> 不含记号. 入口 [KcFold](KcFold.lagda.md), 接口 [KcFoldIf](KcFoldIf.lagda.md), 级顶 [KcFoldTop](KcFoldTop.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项与证书 (§4) 无模块参数.
>
> - **§1 条件版 `KD dn dnL`**: `LvKtTower.FullK (foldTower dn) (foldLim dnL) 1 tt`. 前提只剩**下降** (`DnTower`, `DnLim`, 接口 §3); 读回由级顶给出, 不是前提.
> - **§2 形状定理 (对一切下降, 对一切站, `refl`)**: 读回 `rts s = hs (top (B s))`; 第 $s+1$ 站层号 `B (s+1) = hs (emb (B s) ⊞ injL (B s) (top (B s)))` (头是后继); 第 $s+1$ 站的读回是 `hs (Ωtop (Lev X_s))`, 其中 $X_s$ = `emb (B s) ⊞ injL (B s) (top (B s))`, 即第 $B_{s+1}$ 级的新种类的 $\Omega$-结点, 坐标取遍第 $X_s$ 级的一切高度, 分支原样嵌入; 第 $s+2$ 站层号的头是种类 `(inj₂ (B (s+1)), inj₂ tt)` 的 $\Omega$-结点 (`B-new`), 它的坐标类型就是 `HB (Lev X_s)` (`coord-new`). **回灌输出只经下降看见读回** (`Hs-def`).
> - **§3 第 1 站 (s = 1)**: 起点 $b_0=1$. `B 1` 的头是种类 `(inj₂ 1, inj₂ tt)` 的 $\Omega$-结点 (同 `LvKtTest.t-cells` 的种类), 坐标取遍 `HB S₀` (`B1-shape`); 第 1 站的读回是第 $B_1$ 级的新种类结点, 对每个坐标 $y$ 那一支的级顶都是它的字面第一位置 (`s1-above`); `B 1` 不在 `foldFinK`, `foldωK` 的覆盖之内 (`no-covF1`, `no-covΩ1`).
> - **§4 无条件闭项**: 下降取截断版各站的输出 (常数, 不读读回). 闭项 `Tkc`, `Tkc∞`, 证书, FGH, 无模块参数. **各站输出与 `LvKtInst` 截断版逐站定义相等** (`Hs-trunc`, 对一切 $s$): 无条件闭项每站真回灌进层号的是整个读回, 进闭项的是 $0$ 个读回结点.
> - **§5 带世界版的实例** `ftW : FoldTowerW`, `flW : FoldLimKW` (接口 §4 的前提可满足, 读回含新种类结点); `bdecS₀ : BDecK S₀` (接口 §2 在底上的实例, 即 `LvOmLev.dec⊲`).
> - **§6 第一个障碍的编译陈述**: `ht-coords` (两种种类折叠的层 `Ht` 的坐标类型只有 `A` 与 `HB S₀`), 与 §2 的 `coord-new` 并读.
> - **§7 世界塔的实例** `wt₀`, `wtω` (接口 §6 的前提可满足; 不进闭项).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KcFoldTower where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.HtTowerFClosed using (ord)
open import OCF.Align.LvKtCode
open import OCF.Align.LvKtIf
open import OCF.Align.LvKtTower using (module FullK)
open import OCF.Align.LvKtInst using (finK; CovΩK; module TrK; module TrKL)
open import OCF.Align.LvOmLev using (dec⊲)
open import OCF.Align.KcFoldIf
open import OCF.Align.KcFoldTop
```

## §1 条件版: 只缺下降

```agda
module KD (dn : DnTower) (dnL : DnLim) = FullK (foldTower dn) (foldLim dnL) (hs hz) tt
```

## §2 形状定理 (对一切下降)

```agda
module Shape (dn : DnTower) (dnL : DnLim) where
  open KD dn dnL

  -- 读回是层号的级顶 (后加 1)
  rts-def : ∀ s → rts s ≡ hs (top (B s))
  rts-def s = refl

  -- 回灌输出只经下降看见读回
  Hs-def : ∀ s → Hs s ≡ proj₁ (dn s (B s) (lB s)) (hs (top (B s)))
  Hs-def s = refl

  -- 第 s 站之后的层号: 上一站层号接上整个读回; 头是后继
  X : ∀ s → HB (Kc (suc s))
  X s = emb (B s) ⊞ injL (B s) (top (B s))

  B-suc-shape : ∀ s → B (suc s) ≡ hs (X s)
  B-suc-shape s = refl

  -- 第 s+1 站的读回: 第 B (s+1) 级的新种类结点, 坐标取遍第 X s 级, 分支原样嵌入
  rts-suc : ∀ s → rts (suc s) ≡ hs (hΩ (inj₂ tt) (up {Lev (X s)}))
  rts-suc s = refl

  -- 第 s+2 站层号的头: 种类 (inj₂ (B (s+1)), inj₂ tt) 的 Ω-结点
  B-new : ∀ s → B (suc (suc s)) ≡
    hs (hΩ (inj₂ (B (suc s)) , inj₂ tt) (λ y → emb (B (suc s)) ⊞ injL (B (suc s)) (up {Lev (X s)} y)))
  B-new s = refl

  -- 它的坐标类型就是第 X s 级的高度
  coord-new : ∀ s → E (Kc (suc (suc s))) (inj₂ (B (suc s)) , inj₂ tt) ≡ HB (Lev (X s))
  coord-new s = refl

  -- 第 s+1 站的读回在第 X s 级的每个 (界之下的) 高度之上
  rts-above : ∀ s {w : Wd (Lev (X s))} {β : HB (Lev (X s))} (y : HB (Lev (X s))) →
              y ⊲[ w ] β → up y ⊲[ (w , β) ] top (B (suc s))
  rts-above s y e = top-above (X s) y e
```

## §3 第 1 站

```agda
module One (dn : DnTower) (dnL : DnLim) where
  open KD dn dnL

  -- 第 1 站层号: 头是种类 (inj₂ 1, inj₂ tt) 的 Ω-结点, 坐标取遍 HB S₀
  B1-shape : B 1 ≡ hs (hΩ (inj₂ (hs hz) , inj₂ tt) (λ y → hs hz ⊞ injL (hs hz) (up {S₀} y)))
  B1-shape = refl

  -- 第 1 站读回的新种类结点之下: 对坐标 y : HB S₀ 那一支的级顶 (注入第 y 个分量) 都是字面第一位置
  X₁ : HB (Kc 1)
  X₁ = hΩ (inj₂ (hs hz) , inj₂ tt) (λ y → hs hz ⊞ injL (hs hz) (up {S₀} y))

  comp : HB S₀ → HB (Kc 1)
  comp y = hs hz ⊞ injL (hs hz) (up {S₀} y)

  s1-above : ∀ (y : HB S₀) {w : Wd (Lev X₁)} {β : HB (Lev X₁)} →
             ι {HB S₀} {λ y′ → Lev (comp y′)} y (top (comp y)) ⊲[ w ] β →
             up (ι {HB S₀} {λ y′ → Lev (comp y′)} y (top (comp y))) ⊲[ (w , β) ] top (B 1)
  s1-above y e = top-above X₁ _ e

  -- 对每个坐标 y (不只底坐标 hz): 取界 β 为那一支的级顶本身 (合法: Lg-ι, Lg-top), 它就在读回之下
  s1-sees : ∀ (y : HB S₀) {w : Wd (Lev X₁)} →
            up (ι {HB S₀} {λ y′ → Lev (comp y′)} y (top (comp y))) ⊲[ (w , ι {HB S₀} {λ y′ → Lev (comp y′)} y (top (comp y))) ] top (B 1)
  s1-sees y = s1-above y hself

  s1-sees-lg : ∀ (y : HB S₀) → LgB (ι {HB S₀} {λ y′ → Lev (comp y′)} y (top (comp y)))
  s1-sees-lg y = Lg-ι {HB S₀} {λ y′ → Lev (comp y′)} y (top (comp y)) (Lg-top (comp y))

  -- 第 1 站的层号不在有限码与 ω 码的覆盖之内
  no-covF1 : ∀ n → ¬ (B 1 ≡ finK n)
  no-covF1 zero ()
  no-covF1 (suc zero) ()
  no-covF1 (suc (suc n)) ()

  no-covΩ1 : ¬ CovΩK (Kc 1) (ckc 1) (B 1)
  no-covΩ1 (f , () , _)
```

## §4 无条件闭项

下降取截断版 (`LvKtInst.TrK`, `TrKL`) 各站与极限站的输出: 对输入是常数. 这是 `DnTower`, `DnLim` 的实例 (所以 §1 的条件版不空真), 也是本篇唯一能无条件给出的下降.

```agda
dn₀ : DnTower
dn₀ s b lb = (λ _ → TrK.Hs s) , (λ _ _ → TrK.lHs s)

dnL₀ : DnLim
dnL₀ b lb = (λ _ → TrKL.Hω) , (λ _ _ → TrKL.lHω)

FT₀ : FoldTower
FT₀ = foldTower dn₀

FL₀ : FoldLimK
FL₀ = foldLim dnL₀

module KU = KD dn₀ dnL₀

-- 闭项 (有限站的对角加极限站), 证书, FGH: 无模块参数
Tkc : A
Tkc = KU.TΛ∞ω

Lg-Tkc : Lg Tkc
Lg-Tkc = KU.Lg-TΛ∞ω

fghKc : ℕ → ℕ
fghKc = FLv.FGH (ord Tkc)

-- 只有有限站的对角
Tkc∞ : A
Tkc∞ = KU.TΛ∞

Lg-Tkc∞ : Lg Tkc∞
Lg-Tkc∞ = KU.Lg-TΛ∞

-- 每站真回灌: 层号里是整个读回 (§2 对一切下降), 输出与截断版逐站定义相等
Hs-trunc : ∀ s → KU.Hs s ≡ TrK.Hs s
Hs-trunc s = refl

Hω-trunc : KU.Hω ≡ TrKL.Hω
Hω-trunc = refl
```

## §5 带世界版的实例与底上的可入判定

```agda
ftW : FoldTowerW
ftW s = foldTopW (Kc s) (ckc s) (λ a b lb → (λ _ → TrK.Hs s) , (λ _ _ → TrK.lHs s))

flW : FoldLimKW
flW = foldTopW KΛc ckΛ (λ a b lb → (λ _ → TrKL.Hω) , (λ _ _ → TrKL.lHω))

-- 带世界的读回: 外层世界 a 里, 码目标的级顶 (后加 1)
rtW-def : ∀ s {a b} (la : LgW (Kc s) a) (lb : LgB b) (c : Codes.Code (ckc s) a b) w (lw : LgWbKW (ckc s) w) →
          FoldAtKW.rtW (ftW s) la lb c tt w lw ≡ hs (topW a (Codes.tgt (ckc s) c))
rtW-def s la lb c w lw = refl

bdecS₀ : BDecK S₀
bdecS₀ e q l = dec⊲ e q l
```

## §6 第一个障碍的编译陈述

`Ht` (两种种类折叠的数据树的层所在的类型) 的种类的坐标类型只有 `A` 与 `HB S₀` (`ht-coords`). 第 2 站层号的头的坐标类型是 `HB (Lev (X 1))` (`Shape.coord-new 0` 的同类, 第 $X_1$ 级的高度). [判断] 所以第 2 站起的层号不能原样当 `Ht` 里的层, 下降要数据树的层推广到 `HB (step K)` (接口 `LayK`) 或另写 `HB (Lev c) → Ht` (接口 `DnK`). 本篇没有写这样的下降; 无条件闭项的下降是常数 (§4).

```agda
ht-coords : ∀ (κ : K (step S₀)) → (E (step S₀) κ ≡ A) ⊎ (E (step S₀) κ ≡ HB S₀)
ht-coords (inj₁ tt) = inj₁ refl
ht-coords (inj₂ tt) = inj₂ refl
```

## §7 世界塔的实例 (接口 §6 的前提可满足)

`wt₀`: 每站取码的基世界 `w0` (`code-botK` 的设置; `grow` 是自反). `wtω`: 第 0 站的外层世界取 $\omega$, 之后每站的 `inj₁ tt` 分量沿用上一站, 别的分量取基世界; 第 0 站在它里面看得见非底坐标 (`wtω-sees`). 本路的塔 (§1–§4) 不用世界塔: `LvKtTower.rtTop` 固定取 `w0`; 级顶读回也不读外层世界. 所以这两个实例只说明接口 §6 的前提可满足, 不进闭项.

```agda
wt₀ : WTower
wt₀ = record { aW = λ s → w0 (ckc s) ; laW = λ s → lw0 (ckc s) ; grow = λ s → ≤w-rf (Kc s) }

finA : ℕ → A
finA zero = azero
finA (suc n) = asuc (finA n)

lg-finA : ∀ n → Lg (finA n)
lg-finA zero = tt
lg-finA (suc n) = lg-finA n

ωA : A
ωA = alim finA

Lg-ωA : Lg ωA
Lg-ωA = (λ n → C.suc C.self) , lg-finA

aWω : ∀ s → Wd (Kc s)
aWω zero = ωA
aWω (suc s) (inj₁ tt) = aWω s
aWω (suc s) (inj₂ c) = w0 (cdLev c)

laWω : ∀ s → LgW (Kc s) (aWω s)
laWω zero = Lg-ωA
laWω (suc s) (inj₁ tt) = laWω s
laWω (suc s) (inj₂ c) = lw0 (cdLev c)

wtω : WTower
wtω = record { aW = aWω ; laW = laWω ; grow = λ s → ≤w-rf (Kc s) }

wtω-sees : Bd (Kc 0) tt (asuc azero) (WTower.aW wtω 0)
wtω-sees = C.lim 1 C.self
```
