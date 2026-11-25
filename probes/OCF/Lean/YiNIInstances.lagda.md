# 两个指定请求的实填
验收文件，读记号；第 2 站使用的 tw 1 输出与 neck 均填入同一接口。
Law 的实填域只有 below 两个构造子；没有更大域的保持结论。
来源：值界复用 YiMTValue.btbo-tw1ᶻ、YiKCSem.sem0、YiC0Connect.neck-low。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNIInstances where
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (inj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiMTValue as V
import OCF.Lean.YiC0Reduce as R
import OCF.Lean.YiC0Connect as C
import OCF.Lean.YiNIDomain as D
open import OCF.Lean.YiCNDomain using (Cn; cz)
open import OCF.Lean.YiNIIface
import OCF.Align.EboLeanDef as E
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans)

station neck : D.Node
station = record
  { offset = B.zero
  ; readback = record { source = B.zero ; canonical = cz ; code = B.zero ; reads = refl }
  ; padding = 0 ; tail = λ d → d ; okay = P.Ok-tw 1 }
neck = record
  { offset = K.two
  ; readback = record { source = B.zero ; canonical = cz ; code = B.suc (B.suc B.zero) ; reads = refl }
  ; padding = 2 ; tail = B.suc ; okay = R.o-neck }

neck-read : GR.Rd (D.Node.layer neck) (E.Ωt (E.natT 1))
neck-read = GR.ca (inj₂ ([] , refl , GR.c0 refl , λ η c r →
  GR.rd-add K.two (D.zeros 2 (B.↑ B.zero (B.suc c)))
    (GR.rd-add B.zero (D.zeros 1 (B.↑ B.zero (B.suc c)))
      (GR.rd-add B.zero (B.↑ B.zero (B.suc c))
        (GR.rd-child B.sS (λ _ → B.↑ B.zero c) _ (LL.read0 r))))))

station-request neck-request : Request
station-request = record
  { node = station ; index = E.Ωt (E.natT 1) ; reads = LL.rdΩ ; nonempty = R.hc₀ }
neck-request = record
  { node = neck ; index = E.Ωt (E.natT 1) ; reads = neck-read ; nonempty = R.hc₀ }

-- perf: C-9，输运在变量上检查；不经非单射的读回头求解左值。
transport : (X : L.Ordᶜ L.zero) (x y : B.Tr B.zero) → x ≡ y
  → X ≼ K.readRW x → X ≼ K.readRW y
transport X x .x refl p = p

station-value : At.Value station-request
station-value = transport (RT.Rt R.hc₀) (MT.twᶻ 1) (D.output station)
  (sym (D.output-eq station))
  (K.lower⁰ (CS.sem0 (MT.twᶻ 1) V.btbo-tw1ᶻ) R.hc₀)

neck-output : D.output neck ≡ proj₁ R.neck-out
neck-output = trans (D.output-eq neck) (cong proj₁ (sym R.neck-out-eq))

neck-value : At.Value neck-request
neck-value = transport (RT.Rt R.hc₀) (proj₁ R.neck-out) (D.output neck) (sym neck-output) C.neck-low

data Known : Set where
  at-station at-neck : Known

known : Family
known = record { Member = Known ; request = λ { at-station → station-request ; at-neck → neck-request } }

known-law : Law known
known-law at-station = station-value
known-law at-neck = neck-value
```
