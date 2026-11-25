# 正则性与全层覆盖的非空实例

这里只给编译过的非空实例，不把闭项测试当作全层保持。
Reg 的 Ω 保持另行检验；本篇不预设它。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRegInstances where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as A using (All)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁)
open import Data.Empty using (⊥)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiRTransport as R
open import OCF.Align.YiRCountable using (Small; small-zero; small-suc; small-lim; raw0-small)
open import OCF.Align.YiDispBase
open import OCF.Align.YiRegBase
open import OCF.Align.YiRegCover using (all-retained-reg)
import OCF.Align.YiRegZeroLimit as Z
import OCF.Align.YiGammaBase as H

nat-reg : ∀ n → Reg (V.natF n)
nat-reg zero = tt
nat-reg (suc n) = nat-reg n

ω-reg : Reg (F.lim V.natF)
ω-reg = nat-reg

Ω-reg : Reg (Y.tree R.ν)
Ω-reg = one e-first , tt , tt , (λ η e → small-reg (raw0-small η))

above-Ω : Y.Level
above-Ω = Y.suc (Y.suc R.ν)

above-Ω-reg : Reg (Y.tree above-Ω)
above-Ω-reg = Ω-reg

retained-above-Ω : RetainedDomain (Y.tree above-Ω) R.ν
retained-above-Ω = all-retained-reg above-Ω R.ν Ω-reg (structural (one e-suc))
  refl

known-env : List Y.Level
known-env = R.ν ∷ Y.zero ∷ Y.zero ∷ Y.zero ∷ Y.suc Y.zero ∷
  Y.zero ∷ Y.zero ∷ Y.zero ∷ Y.zero ∷ []

known-env-reg : All (λ x → Reg (Y.tree x)) known-env
known-env-reg = Ω-reg A.∷ tt A.∷ tt A.∷ tt A.∷ tt A.∷ tt A.∷ tt A.∷ tt A.∷ tt A.∷ A.[]

tower0-reg : Reg (Y.tree (Y.tower 0))
tower0-reg = tt

tower1-reg : Reg (Y.tree (Y.tower 1))
tower1-reg = tt

tower2-reg : Reg (Y.tree (Y.tower 2))
tower2-reg = Ω-reg

built-small : ∀ {η} → Z.TopBuilt η → Small (V.up Z.q η)
built-small Z.top-built = small-lim (λ _ → small-suc small-zero)
built-small (Z.suc-built p) = small-suc (built-small p)
built-small (Z.lim-built p) = small-lim (λ n → built-small (p n))

nonroot-reg : Reg Z.q × Reg (V.Ω̂ Z.q) ×
  (∀ η (e : F.Gd Z.q (V.cO Z.q) η) → Reg (V.up Z.q η))
nonroot-reg = Z.q-reg , small-reg (small-lim (λ _ → small-suc small-zero)) ,
  (λ η e → small-reg (built-small (Z.guard-built η (proj₂ e) (proj₁ e))))

raw-feedback-guard : F.Gd Z.x (V.cO Z.x) G.top
raw-feedback-guard = inj₁ refl , tt

no-reg-raw-feedback : Reg (V.up Z.x G.top) → ⊥
no-reg-raw-feedback = Z.no-reg-omega-x

no-reg-seed-x : Reg (Y.tree (H.read-point Z.x-level (H.seed Z.x-level))) → ⊥
no-reg-seed-x = Z.no-reg-omega-x
```

retained-above-Ω 在字段层 Ω 上量化全部合法 Raw Ω 坐标，已经超出第九轮的 Small 层。
它不依赖 Reg(Ω_Ω)，也不声称第一支／坐标读回本身保持 Reg。
known-env 是第八轮完整新历史的树列表，入口另与原 Enew 作类型核对。
没有交 Reg(Λ) 或全塔保持；本轮可满足性卡点必须单独报告。
nonroot-reg 进一步实填反例 Ωx 除根 Below 以外的全部 Reg 义务，
所以失败确在常零极限后的根位置，而非又塞进一个未检查的坏 Ω 子树。
no-reg-raw-feedback 只否定任意合法 guarded Raw 回读都保 Reg，
不是一个已构造的 ψ 输出或实际 γ 输出反例。
no-reg-seed-x 把同一反例接到已有结构 γ 种子算法；它不能为所有 Reg 层号给 Reg 种子。
