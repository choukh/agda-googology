# 非空输入与完整历史：种子已有包，保留支仍缺派发

本篇将上一篇实际路径的整个历史保留下来，既不把 [Ω,0] 当作完整 Env，
也不把“给了 InvD”当作已给可入 Raw 坐标。原当前树与 γ 种子均在第七轮
同一个码界包络下有 InvD；种子同时有 Point 的原 Gd 守卫。
包络没有宣称覆盖 γ 内部 Ω 基本列调用，这正是本轮要审查的缺口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGammaSeed where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as A using (All)
open import Data.Product.Base using (_,_; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
import OCF.Align.YiCtxFork as W
import OCF.Align.YiRTransport as R
open import OCF.Align.YiRCountable using (Small; small-suc)
open import OCF.Align.YiDBase
open import OCF.Align.YiSpineCommon using (Common)
open import OCF.Align.YiDActual
  using (ActualDemand; TargetName; seed-invD; no-small-demand; ν-nonzero;
         FiniteColumns; finite-columns; below-no-target; Ω-code)
open import OCF.Align.YiPrefixNames using (ω-code; ω-fs)
open import OCF.Align.YiSpineTrace using (Actual)
open import OCF.Align.EboLeanDef using (sucT; Ωt)
import OCF.Align.YiSpineNames as N
import OCF.Align.YiTargetHistory as H
import OCF.Align.YiGammaWitness as G
open import OCF.Align.YiGammaBase

Eold Enew : List Y.Level
Eold = Y.zero ∷ Y.zero ∷ Y.zero ∷ W.one ∷ Y.zero ∷ Y.zero ∷ Y.zero ∷ Y.zero ∷ []
Enew = R.ν ∷ Eold

history-named : map N.structure-model-read (H.Env G.r9) ≡ Eold
history-named = refl

β-name : N.Name G.β
β-name = N.no (N.ns (N.no (N.ns N.nz)))

β-tree : Y.tree (N.ι_L β-name) ≡ Y.tree R.gamma-source
β-tree = refl

seed-name : N.Name (Ωt Ω-code)
seed-name = N.no (N.no (N.ns N.nz))

seed-tree : Y.tree (N.ι_L seed-name) ≡ Y.tree R.seed-tree
seed-tree = refl

old-context : K.Ctx Eold
old-context = K.ctx W.one
  (V.suc V.self A.∷ V.suc V.self A.∷ V.suc V.self A.∷ V.self A.∷
   V.suc V.self A.∷ V.suc V.self A.∷ V.suc V.self A.∷ V.suc V.self A.∷ A.[])

new-context : K.Ctx Enew
new-context = K.ctx R.ν
  (V.self A.∷ V.fst (V.suc V.self) A.∷ V.fst (V.suc V.self) A.∷ V.fst (V.suc V.self) A.∷
   V.fst V.self A.∷ V.fst (V.suc V.self) A.∷ V.fst (V.suc V.self) A.∷
   V.fst (V.suc V.self) A.∷ V.fst (V.suc V.self) A.∷ A.[])

old-shape : All (λ u → u ≡ Y.zero ⊎ u ≡ W.one) Eold
old-shape = inj₁ refl A.∷ inj₁ refl A.∷ inj₁ refl A.∷ inj₂ refl A.∷
  inj₁ refl A.∷ inj₁ refl A.∷ inj₁ refl A.∷ inj₁ refl A.∷ A.[]

lookup : ∀ {P : Y.Level → Set} {E u} → All P E → u ∈ E → P u
lookup (p A.∷ ps) (here refl) = p
lookup (p A.∷ ps) (there q) = lookup ps q

no-one-name : ∀ {c} → TargetName R.ν (Y.tree W.one) c → ⊥
no-one-name ()

no-one-demand : ∀ {x} → ActualDemand R.ν x (Y.tree W.one) → ⊥
no-one-demand (c , u , bound , named , a) = no-one-name named

old-needed : ∀ t {k} (f : K.Field k (Y.tree t)) {u} → u ∈ Eold →
  ActualDemand R.ν (F.suc k) (Y.tree u) → Common (dispatch t f) u
old-needed t f p d with lookup old-shape p
... | inj₁ refl = zero-common (dispatch t f)
... | inj₂ refl = ⊥-elim (no-one-demand d)

source-invD : InvD (ActualDemand R.ν) Eold R.gamma-source
source-invD = demanded old-context (old-needed R.gamma-source)

entered-seed-invD : InvD (ActualDemand R.ν) Eold R.seed-tree
entered-seed-invD = enter-inv (Y.legal R.gamma-source) source-invD R.seed R.seed-guard

seed-history-invD : InvD (ActualDemand R.ν) Enew R.seed-tree
seed-history-invD = demanded new-context λ where
  f (here refl) d → needed seed-invD f (here refl) d
  f (there p) d → old-needed R.seed-tree f p d

gamma-seed : Certified (ActualDemand R.ν) Enew R.ν
gamma-seed = certify-seed R.ν seed-history-invD

seed-not-small : Small (Y.tree (read-point R.ν (coordinate gamma-seed))) → ⊥
seed-not-small ()

-- 标准ω的列，非第七轮的lim(n+1)。仍只逐项，不作函数外延。
b-columns : FiniteColumns W.b ω-code
b-columns = finite-columns refl (λ n → n , W.nat-read-agrees n , ω-fs n)

not-frozen-actual : Actual (sucT ω-code) Ω-code → ⊥
not-frozen-actual = below-no-target refl

no-kept-demand : ActualDemand R.ν (F.suc W.b) (Y.tree R.ν) → ⊥
no-kept-demand = no-small-demand R.ν ν-nonzero (small-suc R.b-small)
```

history-named 只读取已算出的0/1历史；没有使用 structure-model 的未指定正ψ填值。
source-invD 与 seed-history-invD 的需求范围仍显式是 ActualDemand Ω，
其中历史成员1没有该包络的需求，不能据此声称完整 γ 内部需求也被覆盖。
gamma-seed 证明当前 Raw Ω 中的不可数种子已有合法包与 InvD；缺的不是把任意
高层树回收到 Raw Ω 的总编码器，而是下一步保留分支按位置派发的定义。
not-frozen-actual／no-kept-demand 明确防止把那个 lt 分支误作旧 Actual 的坏对。
