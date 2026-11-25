# 两份 Ω₂ 的第 1 枝中，哪一个正层参数已经由实际反馈给出

第四层。把该参照的正输入逐项定位到真实第三塔的正槽；去掉第二层求值参数开头的 Ω₂ 时，整条零层链也由该塔支付。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadReturnPositive where

open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import WVOne using (T₀; read; 𝟏)
open import WVTwo using (T₁)
open import WSLevel using (Ω₁ᴸ)
open import WKShape using (lvl3)
open import YiLAB7Replay using (Ω₂ᴸ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
import B12Terminal as T
import B12ActualSlots as C
import B12Omega3Ref as R
import B13Target as P
import B14RefFixed as F
import B21RowDynamics as IX
import B21RowTheta as TH
import B24RRows as Row
import B24NScalar as S
import B24NStore as Store

anchor = Row.T Ω₁ᴸ
input = F.collapse anchor
raw : Row.y 1 L.≅ input
raw = F.pres (Row.from-live (L.Ω-refl _))

real : TH.Fits Store.Sem.target input
real d = B18RefModel.conv (B18RefRows.meaning d) (Store.positive d) raw
  where
  import B18RefModel
  import B18RefRows

target = Row.node 1
zero-return = L.ψ⁰ (P.co₁ input)
same : zero-return L.≅ S.bound
same = L.≅-trans (L.ψ⁰-≅ (P.co-pres (L.≅-trans (L.≅-sym raw) (Row.feed 1))))
  (L.l≅ (λ n → L.ψ⁰-≅ (P.co-pres (Row.regular 1 (arg n)))))
  where
  f = Row.kid 1
  g = λ x → L.ψ (L.suc L.zero) R.idσ (P.co₁ (f (L.tr⁻ L.z≅ x)))
  arg : ∀ n → L.tr⁻ L.z≅ (R.S.iter g 𝟏 n) L.≅ S.orbit n
  arg n = L.tr⁻-≅ L.z≅ (chain n)
    where
    chain = L.iter-R L._≅_ {G = g} {G′ = S.weak}
      (λ d → L.≅-sym (L.ψ⁰≅ψ {p = L.suc L.zero} {σ = R.idσ}
        (L.≅-sym (P.co-pres (Row.regular 1 (L.tr⁻-≅ L.z≅ d)))))) (L.s≅ L.z≅)

actual : ∀ (r : T.Run lvl3) (cv : C.Covered r) → zero-return ≼ read (T.value r)
actual r cv = ≼-trans {b = S.bound} (≅→≼ same) (S.At.value r cv)

stored : ∀ (r : T.Run lvl3) (cv : C.Covered r) → IX.Index (Store.At.index₂ r cv) Store.Sem.target
stored = Store.At.carried
```
