# 原 Run 在共同界内的异层分派相容

只比较原 rkT 的结果，不把无证构造 rise 当作语义判据。
先为原比较程序补出结果证书：keep 携严格子位置，rise 携目标在节点层内的位置。
Shape 只在同一合法世界与原 Λ 的两条位置下转成层相等；不要求路径相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformGeneratedDispatch where
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (accL; Sk)
open import OCF.Align.EventReturnCodeIf using (Shape)
open import OCF.Align.EventReturnCodeBuild using (shape-self)
import OCF.Align.BoundedShapeEquality as E
import OCF.Align.GenFoldRun as Run

module Original (T : KS) (G : GenK T) (Ld : LgDn T) (fl : FbLg G)
  (Λ : HB (step T)) (lΛ : LgB Λ) (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) where
  module P = Run T G Ld fl Λ lΛ one⊲
  open P using (Rk; keep; rise; rkS; rkT)
  S : KS
  S = step T

  data Valid {k t : HB S} {W : Wd S} : Rk k t W → Set where
    kept : (r : StH W k t) → Valid (keep r)
    risen : t ⊲[ W ] k → Valid rise

  valid-S : ∀ {k t W} (p : k ⊲[ W ] t) → Valid (rkS p)
  valid-S hself = risen hself
  valid-S (hsuc p) = kept (ss p)
  valid-S (hlim n p) = kept (sl n p)
  valid-S (hLim e p) = kept (sL e p)

  valid-T : ∀ {k t W} (pk : k ⊲[ W ] Λ) (pt : t ⊲[ W ] Λ) (lw : LgW S W) →
    Valid (rkT pk pt lw)
  valid-T pk pt lw with cmpB pk pt lw lΛ
  ... | inj₁ p = risen p
  ... | inj₂ p = valid-S p

  data SameBranch {k k′ t : HB S} {W : Wd S} : Rk k t W → Rk k′ t W → Set where
    both-keep : ∀ r r′ → SameBranch (keep r) (keep r′)
    both-rise : SameBranch rise rise

  compatible : ∀ {k t W} {r s : Rk k t W} → Valid r → Valid s → SameBranch r s
  compatible (kept r) (kept s) = both-keep r s
  compatible (risen p) (risen q) = both-rise
  compatible {k} (kept r) (risen p) =
    ⊥-elim (E.no-child (accL k) (shape-self k) (Sk r p))
  compatible {k} (risen p) (kept r) =
    ⊥-elim (E.no-child (accL k) (shape-self k) (Sk r p))

  dispatch : ∀ {k k′ t W} (s : Shape k k′)
    (pk : k ⊲[ W ] Λ) (pk′ : k′ ⊲[ W ] Λ)
    (pt pt′ : t ⊲[ W ] Λ) (lw : LgW S W) →
    SameBranch (rkT pk pt lw) (rkT pk′ pt′ lw)
  dispatch s pk pk′ pt pt′ lw with E.bounded s pk pk′ lw lΛ
  ... | refl = compatible (valid-T pk pt lw) (valid-T pk′ pt′ lw)

  -- 原运行器的零节点和目标零总在当前 Λ 中，两个位置参数仍可独立。
  actual-zero : ∀ {W} (lw : LgW S W) (p q : hz ⊲[ W ] Λ) →
    SameBranch (rkT p p lw) (rkT q q lw)
  actual-zero lw p q = dispatch (shape-self hz) p q p q lw

  -- 实际节点 0 与非零目标 1；one⊲ 是原 Run 模块本来需要的界证。
  actual-low : ∀ {W} (lw : LgW S W) →
    SameBranch (rkT (z⊲ᴮ Λ) one⊲ lw) (rkT (⊲ᴮ-tr (hsuc hself) one⊲) one⊲ lw)
  actual-low lw = dispatch (shape-self hz) (z⊲ᴮ Λ) (⊲ᴮ-tr (hsuc hself) one⊲) one⊲ one⊲ lw
```

结论只同步真实 keep/rise 标签，未认同 keep 的 StH 证明，也未证明 Run 全部状态保持。
原共同界 Λ、合法世界和两侧节点位置不可删除；本篇没有跨历史自动补界。

以下直接用原 GenFoldInst 对所有 Lev x 的已填记录；不是假定接口有实例。
共同界取原一层源 1，仅用于校准真实 keep 的两条不同来源位置。
完整 dispatch 本身仍允许原 Run 的任意合法 Λ。

```agda
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.GenFoldInst using (genLev; ldLev; flLev)

module Actual {S₀ : KS} (x : HB S₀) where
  module D = Original (Lev x) (genLev x) (ldLev x) (flLev x) (hs hz) tt hself
  module P = D.P
  instance-low : D.SameBranch {W = w₀ (genLev x) , hz}
    (P.rkT (z⊲ᴮ (hs hz)) hself (lw₀ (genLev x) , tt))
    (P.rkT (⊲ᴮ-tr (hsuc hself) hself) hself (lw₀ (genLev x) , tt))
  instance-low = D.actual-low {W = w₀ (genLev x) , hz} (lw₀ (genLev x) , tt)
```
