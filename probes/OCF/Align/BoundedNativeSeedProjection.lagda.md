# 种子世界沿实际原生路径的精确投影

不同目标副本任意给世界时相干会失败。这里所有副本由同一底世界v
生成；每个高秩界均为1。定理只沿已经给出的路径投影，不识别路径证据。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeSeedProjection where
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLeg using (pw; here; viaS; viaL)
open import OCF.Lean.BoundedContextRun using (path-context)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedNativeZeroWorld using (seed)
open import OCF.Align.BoundedNativeLegalWorld using (pw-compose)
import OCF.Align.BoundedNativeViewBase as Base

seed-project : ∀ {c t : Cd} (p : c ⊲ t) v →
  pw (path-context (ls lz) lz p) (seed t v) ≡ seed c v
seed-project hself v = refl
seed-project (hsuc p) v = trans
  (pw-compose (viaS here) (path-context (ls lz) lz p) _)
  (seed-project p v)
seed-project {t = hl f} (hlim n p) v = trans
  (pw-compose (viaL here n) (path-context (ls lz) lz p) _)
  (seed-project p v)

rank-project : ∀ {i t : Cd} (p : hs i ⊲ t) v →
  pw (path-context (ls lz) lz p) (seed t v) ≡ (seed i v , hs hz)
rank-project p v = seed-project p v

base-project : ∀ t v → Base.project t (seed t v) ≡ v
base-project hz v = refl
base-project (hs t) v = base-project t v
base-project (hl f) v = base-project (f 0) v

seed-order : ∀ t {v u} → _≤w_ (Native hz) v u →
  _≤w_ (Native t) (seed t v) (seed t u)
seed-order hz p = p
seed-order (hs t) p = seed-order t p , hself
seed-order (hl f) p = λ n → seed-order (f n) p
```

seed-project对所有可数高度成立；rank-project同时核对低层世界和种子
界。它不说原生运行器对任意目标世界保合法，也不把seed世界证书
直接等同原raw合法性。后续只能在明确给出的seed世界域内使用这些律。
