# 保留种类穿过一次后继的实际运输

直接对既有Ctx组合归纳，证明along在后继目标中成为旧种类，并逐坐标
核对fr。没有比较任意高度，也不把两条路径或函数判成相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionAlongSuccessor where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; ek; frC)
open import OCF.Lean.BoundedContextRun using (compose; path-context)
open import OCF.Align.BoundedDescentValueBridge using (Native; along; fr-along)

ek-step : ∀ {T S} (c : Ctx T S) κ →
  ek (compose (viaS here) c) κ ≡ inj₁ (ek c κ)
ek-step here κ = refl
ek-step (viaS c) κ = ek-step c (inj₁ κ)
ek-step (viaL c n) κ = ek-step c (n , κ)

fr-step : ∀ {T S} (c : Ctx T S) κ e →
  frC (compose (viaS here) c) κ e ≡
  frC c κ (subst (E (step T)) (ek-step c κ) e)
fr-step here κ e = refl
fr-step (viaS c) κ e = fr-step c (inj₁ κ) e
fr-step (viaL c n) κ e = fr-step c (n , κ) e

along-suc : ∀ {i t : Cd} (p : hs i ⊲ t) →
  along (hsuc p) ≡ inj₁ (along p)
along-suc p = ek-step (path-context (ls lz) lz p) (inj₂ tt)

fr-suc : ∀ {i t : Cd} (p : hs i ⊲ t) e →
  fr-along (hsuc p) e ≡
  fr-along p (subst (E (Native (hs t))) (along-suc p) e)
fr-suc p e = fr-step (path-context (ls lz) lz p) (inj₂ tt) e
```

条件p本身就是字面公共上界t中的位置。实际实例可取任意i、t=hs i、
p=hself；本定理并未要求所有高度之间能找到或判定这种位置。
