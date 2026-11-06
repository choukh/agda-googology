# 新塔 (六): 最终坍缩与骨架总审的 `SkelDxGen.Gen0.ev₀` 是同一个式子

> 不含记号. 入口 [NewTwr](NewTwr.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 本篇只作对照 (导入骨架总审的实验文件, 它的导入闭包比闭项大), 不进闭项的导入闭包.
>
> 骨架总审 (`Survey/SkeletonAudit.md` §3) 独立写了 "一般折叠求到第 0 层, 用 `Tree.sum` 读成 `A`" 的 `Gen0.ev₀`. 本路的 `NewTwrColl.collG` 与它在同一个层 $1\boxplus h$, 同一个基世界, 同一份数据 $\Omega_{1\boxplus h}$ 上定义相等 (`coll≡ev₀`, `refl`, 对一切 $T$, $h$). 所以最终坍缩这一字段, 两边是同一个实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NewTwrCmp where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (module Tree; topStepG)
open import OCF.Align.NewTwrIf
open import OCF.Align.NewTwrColl using (collG; one⊞)
import OCF.Align.SkelDxGen as SK
import OCF.Align.GenFoldK as GK
import OCF.Align.GenFoldEv as GE
open import OCF.Align.NewTwrEv using (LX; W₀X; ΩX; out₂N; lW₀X; eLX)
open import OCF.Align.GenFoldInst using (genLev; ldLev; flLev)

coll≡ev₀ : ∀ {T : KS} (G : GenK T) (Ld : LgDn T) (fl : FbLg G) (h : HB (step T)) (lh : LgB h) →
  col (collG G Ld fl) h lh ≡
  SK.Gen0.ev₀ T G Ld fl (one⊞ h) (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h) {w₀ G , hz} (lw₀ G , tt)
    (Tree.Om.Ωd T (topStepG (tpK G)) (one⊞ h))
coll≡ev₀ G Ld fl h lh = refl
```

**求值与 GenFold 的同一个.** `NewTwrEv` 重写的层, 世界, 数据, 第 2 层的输出与 `GenFoldK`, `GenFoldEv` 的定义相等 (`refl`, 对一切 $X$). 所以本路每站的下降与 `GenFoldK.evB` 只差最后的读回 (`rdG` 读进 `HB (step (Lev X))`, `rd₂` 读进 `Ht`).

```agda
LX≡ : ∀ {S : KS} (X : HB S) → LX X ≡ GK.LX X
LX≡ X = refl

W₀X≡ : ∀ {S : KS} (X : HB S) → W₀X X ≡ GK.W₀X X
W₀X≡ X = refl

ΩX≡ : ∀ {S : KS} (X : HB S) → ΩX X ≡ GK.ΩX X
ΩX≡ X = refl

out₂≡ : ∀ {S : KS} (X : HB S) → out₂N X ≡ GK.EvX.out₂ X (GK.lW₀X X) (GK.eLX X) (GK.ΩX X)
out₂≡ X = refl
```
