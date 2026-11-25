# 含 Ω 孩子的源上界证书与读法上界
验收文件；编译定理：实际 a(chain 1) 有 UpperChild 居民，chain 2/out(chain 1) 接回该孩子；所有 a d 满足 Light。
UpperChild 是保留完整层号坐标的候选关系，尚无折叠值出口；child-reading-ceiling 只界记号读法，不界 output。
来源：YiXUFirst 的 chain1-related/model 经 YiBRTw.↑-L/⊕-L 提升；读法界复用 YiNLCeiling，计算复用 YiCBActual/YiUTTwoLocal。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXWChild where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiCBActual as CB
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as Fold
import OCF.Lean.YiRWPath as Path
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiNLCeiling as N
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as EB
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiLegBlock as S
open import OCF.Lean.YiBRRel using (RelL; RelT; lz; lS; is)
import OCF.Lean.YiBRTw as T
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as Fam
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceEmbed as E
open import OCF.Lean.YiASIface using (s0; ss)
import OCF.Lean.YiXUFirst as X
import OCF.Align.Level as L

old-child : J.Tr 1 → S.L
old-child d = J.nat 2 S.⊕ (S.zero S.⊕ S.↑ (J.nat 1) (S.suc d))
child-related : ∀ {d d′} → RelT K.one (J.nat 1) d d′ → RelL (U.a d) (old-child d′)
child-related r = T.⊕-L (lS (lS lz)) (T.⊕-L lz (T.↑-L (lS lz) (is r)))
-- 此关系保留含 Ω 的完整坐标及源上界；尚无折叠值出口。
record UpperChild (ell : B.L) (X₁ : I.T 1) : Set where
  constructor upper-child
  field
    source : J.Tr 1
    coordinate : RelL ell (old-child source)
    model : Fam.U 1 source X₁

cap₁ : I.T 1
cap₁ = W.φ P.top (ss (ss s0)) (L.add (E.Ω 3) (λ q → q) (E.Ω 3 L.+ E.Ω 3))
actual : UpperChild (U.a (U.Inner.chain 1)) cap₁
actual = upper-child X.chain1-old (child-related X.chain1-related) X.chain1-model

chain2 : U.Inner.chain 2 ≡ proj₁ (TB.ψ (U.a (U.Inner.chain 1)) (proj₂ U.o₂ (U.Inner.chain 1))
  (MT.rbᶻ (U.a (U.Inner.chain 1))) (Fold.B₀ (U.a (U.Inner.chain 1))) K.one
  (Path.self Path.∙ proj₂ (proj₁ U.o₂) (U.Inner.chain 1)) (O.Ωt K.one)
  (proj₁ (O.Ωt (U.a (U.Inner.chain 1)))))
chain2 = CB.feed-child (U.Inner.chain 1)
out1 : U.Inner.out (U.Inner.chain 1) ≡ MT.ψ₀ᶻ (U.a (U.Inner.chain 1))
  (proj₂ U.o₂ (U.Inner.chain 1)) (proj₁ (O.Ωt (U.a (U.Inner.chain 1))))
out1 = UL.out-child (U.Inner.chain 1)

slots-one : N.Slots K.one
slots-one (Data.Sum.inj₁ ())
slots-one (Data.Sum.inj₂ (tt , Data.Sum.inj₁ tt)) = tt
slots-one (Data.Sum.inj₂ (tt , Data.Sum.inj₂ ()))
child-light : ∀ d → N.Light (U.a d)
child-light d = N.light-sum K.two (B.zero B.⊕ B.↑ K.one (B.suc d))
  (N.ln tt (λ _ → N.ln tt (λ _ → N.lz)))
  (N.light-sum B.zero (B.↑ K.one (B.suc d)) N.lz (N.light-up K.one slots-one (B.suc d)))
child-reading-ceiling : ∀ d {ν} → GR.Rd (U.a d) ν → ν EB.<ᵀ N.κ₂
child-reading-ceiling d = N.rd-light (U.a d) (child-light d)
```
