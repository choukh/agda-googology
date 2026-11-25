# 第 1 项的实际槽位最小检查
验收文件；编译定理：实际 c₁ 承载第 1 层的 Ω，下行指定槽位在第 1 层保留。
不把槽位保留当成 NextSlot 或零层第 1 项的证明；实际保留输出的归约见 YiC1Slot。
来源：底下界复用 YiTBFam.ψ-⊵，对象与指定下降路径复用 YiC0Local/YiC0Next。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC1Check where
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiC0Local as C
import OCF.Lean.YiC0Next as N
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiKSDesc as D
import OCF.Align.EboLeanDef as E
c₁-Ω : H.M 1 (E.Ωt (E.natT 1)) C.c₁
c₁-Ω = subst (H.M 1 (E.Ωt (E.natT 1)))
  (trans (sym UL.feed0) (sym C.c₁-eq))
  (H.m⊴N 1 (H.Mβ 0) (TF.ψ-⊵ (U.a B.zero) (proj₂ U.o₂ B.zero)
    (MT.rbᶻ (U.a B.zero)) (F.B₀ (U.a B.zero)) K.one
    (P.inu (λ _ → P.inc tt P.self)) (O.Ωt K.one) (proj₁ (O.Ωt (U.a B.zero)))))
pos¹ : ∀ {j ℓ} → D._⊑¹_ j ℓ → B.Pos j → B.Pos ℓ
pos¹ D.r¹ p = p
pos¹ (D.n¹ {s = s} d) p = inj₂ (O.c₀ s , inj₂ (pos¹ d p))
br¹ : ∀ {j ℓ} (d : D._⊑¹_ j ℓ) (p : B.Pos j) → B.Br j p → B.Br ℓ (pos¹ d p)
br¹ D.r¹ p z = z
br¹ (D.n¹ d) p z = br¹ d p z
first¹ : ∀ {j ℓ} (d : D._⊑¹_ j ℓ) (p : B.Pos j) → br¹ d p (B.fromBr j p B.zero) ≡ B.fromBr ℓ (pos¹ d p) B.zero
first¹ D.r¹ p = refl
first¹ (D.n¹ d) p = first¹ d p
p : B.Pos C.ℓ₁
p = pos¹ C.neck-path (inj₁ (inj₁ tt))
opaque
  unfolding C.neck-path C.c₁ U.Inner.feed U.Inner.g
  keep-check : F.kp C.ℓ₁ (proj₂ U.o₂ C.c₁) p N.w₁ ≡ just (K.q1 , br¹ C.neck-path (inj₁ (inj₁ tt)) , first¹ C.neck-path (inj₁ (inj₁ tt)))
  keep-check = refl
```
