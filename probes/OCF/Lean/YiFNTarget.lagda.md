# FirstMissing 目标的具体下界
验收文件；编译定理：目标不低于 ψ₀(Ω_{Ω_ω}) 与 ψ₀(Ω_{Ω+1}) 的参照树，原目标 HC 闭项实填。
只沿原目标的指定基本列路径取下界，不给实际回灌输出的记号上界，不判定 FirstMissing。
来源：路径工具改接 YiMXSamples.trace/Allω/walk/walk≼，值比较用 YiRefTw2.tree-≼；back-lower 照 YiExInst.tree-back 反向作结构递归。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFNTarget where
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiRefTw2 as R
import OCF.Lean.YiMXSamples as MX
import OCF.Lean.YiMonoExit as ME
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
open import OCF.Align.Value using (_≼_; z≼; s≼s; l≼; ≼l; ≼-trans)

target : E.T
target = E.fsn (Keel⁻.row keelᴱ 3) 1

walk : E.T → List ℕ → E.T
walk t ns = MX.trace ns t

PathOK : E.T → List ℕ → Set
PathOK t ns = MX.Allω ns t

get : ∀ t ns → PathOK t ns → E.HC t → E.HC (walk t ns)
get t ns = MX.walk ns {t = t}

get≤ : ∀ t ns (ok : PathOK t ns) (h : E.HC t) → R.Rt (get t ns ok h) ≼ R.Rt h
get≤ t ns = MX.walk≼ ns {t = t}

back-lower : ∀ {t} (h : SI.E.HC t) → ME.toL (ET.tree (XI.back h)) ≼ SI.E.tree h
back-lower (SI.E.h0 _) = z≼
back-lower (SI.E.h1 _ h) = s≼s (back-lower h)
back-lower (SI.E.hω _ hs) = l≼ (λ n → ≼l n (back-lower (hs n)))

walk-lower : ∀ t ns (ok : PathOK t ns) {u} → walk t ns ≡ u
  → (hu : E.HC u) (h : SI.E.HC t) → R.Rt hu ≼ SI.E.tree h
walk-lower t ns ok e hu h = ≼-trans
  (R.tree-≼ (sym e) hu (get t ns ok (XI.back h)))
  (≼-trans (get≤ t ns ok (XI.back h)) (back-lower h))

p00 p001 pplus : List ℕ
p00 = 0 ∷ 0 ∷ []
p001 = 0 ∷ 0 ∷ 1 ∷ []
pplus = 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []

ok00 : PathOK target p00
ok00 = refl , refl , tt
ok001 : PathOK target p001
ok001 = refl , refl , refl , tt
okplus : PathOK target pplus
okplus = refl , refl , refl , refl , refl , refl , refl , refl , tt

low : E.T
low = E.ψ [] (E.Ωt (E.Ωt (E.EBOψ 0))) ∷ []
shape00 : walk target p00 ≡ low
shape00 = refl
shape001 : walk target p001 ≡ E.EBOψ 2
shape001 = refl
shape-plus : walk target pplus ≡ R.t₊
shape-plus = refl

lower : (hl : E.HC low) (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
  → R.Rt hl ≼ SI.E.tree h
lower hl h = walk-lower target p00 ok00 shape00 hl h

lower-btbo : (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
  → R.Rt (ET.hc-tower 2) ≼ SI.E.tree h
lower-btbo h = walk-lower target p001 ok001 shape001 (ET.hc-tower 2) h

lower-plus : (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
  → R.Rt R.h₊ ≼ SI.E.tree h
lower-plus h = walk-lower target pplus okplus shape-plus R.h₊ h

opaque
  target-hc : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1)
  target-hc = SI.conv (R.hω-inv (ET.hc-tower 3) refl 1)

  low-hc : E.HC low
  low-hc = subst E.HC shape00 (get target p00 ok00 (XI.back target-hc))
```
