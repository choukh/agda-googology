# 原 FΩ 后继的全部源轨道与去 marker 观察

本篇锁定实际 FΩ(suc a)，a 为任意原层号。坐标是原 chainᵠ，
从 Ω̇ m a 起步，经过原 ψᵠ 回灌；没有改成另一个模型轨道。
全坐标都进入生成域，且原完整底观察可在每个实际分支去掉 marker。
这尚不是其与下降侧的整轨道耦合。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailRecoverySuccessor (S : HtB) where
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev; _⊔_; limA; wk)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.LadderOrdRel S
open import OCF.Align.TotalValueBuildRelatedGenIf S using (Gen)
open import OCF.Align.TotalValueBuildRelatedGenOps S using (chain-gen)
open import OCF.Align.TotalValueBuildRelatedGenPsi S using (psi-gen)
open import OCF.Align.TotalValueTailRecoveryMarker S using (successor-mark)

module At (m : Ht) (a : Ordᴵ) where
  callback : ∀ ξ ζ → Q m a ξ ζ → Q m (suc a) (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)
  callback ξ ζ z = qwk proj₁
    (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e))
    (omk zero z (ι zero z))

  clean : ∀ ξ ζ → Q m a ξ ζ → Q m (suc a) (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)
  clean ξ ζ z = qwk proj₁
    (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e)) (ι zero z)

  callback-gen : ∀ ξ ζ z → Gen m a z → Gen m (suc a) (callback ξ ζ z)
  callback-gen ξ ζ z gz = rwk (proj₁ gm) , proj₂ gm
    where gm = successor-mark m a z gz

  step : Q m a Fl (Z* (κ Fl)) → Q m a Fl (Z* (κ Fl))
  step z = qwk (λ v → v , (v , v)) (⇑ (cv* m))
    (ψᵠ zero (callback Fl (Z* (κ Fl)) z))

  step-gen : ∀ z → Gen m a z → Gen m a (step z)
  step-gen z gz = rwk (proj₁ gp) , proj₂ gp
    where gp = psi-gen zero (callback-gen Fl (Z* (κ Fl)) z gz)

  coordinates : ℕ → Q m a Fl (Z* (κ Fl))
  coordinates = chainᵠ (λ v → v) fc* step

  coordinates-gen : ∀ n → Gen m a (coordinates n)
  coordinates-gen = chain-gen (λ v → v) fc* step step-gen

  whole-clean : ∀ {w ℓ} (ok : Ok w) (e : Eh h₀ m w (κ Fl))
    (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) →
    ψ̄ᵠ ok e (Ω̇ m (suc a)) ev p ≡
    limA 0 (λ n → wk 0 (λ v → v , v)
      (ψ̄ᵠ ok (e⁺ m ok e) (clean Fl (Z* (κ Fl)) (coordinates n)))) ev p
  whole-clean ok e ev p = refl
```

全轨道已实填生成域，因而并非只给一条有条件的回调接口。
whole-clean 保留整个原极限与全部坐标，并非取首项。
剩余的确切值义务仍是源端原 ι(坐标) 与目标端原 ι↓(坐标)
在各自实际 ψ/Ψ 回灌下的比较。目标回灌也有生成域保持定理，
但两边分别有 Gen 不蕴含二者的关系；本篇没有如此推断。
