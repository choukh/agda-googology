# 含 Ω 孩子的带表对照折叠值出口
验收文件；编译定理：UpperChild 加 RelE 给折叠读回值上界，右端是带表对照块的折叠值，不是记号读法。
实际 chain 1 的 RelE 已填，故 out(chain 1) 接到该值；UpperChild 单独的全域出口未证，model 尚无该折叠的封顶律。
首阻点：YiXVSourceSem 只覆盖有限层原折叠，不能直接封顶此处的变层号带表折叠；全链、output 与里程碑均未判定。
来源：YiBRTw.⊕-E/↑-EO 构造实际证据，YiVTRel.A 搬运折叠，YiCOFinite.read-rel 给 K.readRW 出口；未改定义。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCOChild where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiXWChild as C
import OCF.Lean.YiXUFirst as X
import OCF.Lean.YiCOFinite as Fin
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as SO
import OCF.Lean.YiLegPath as SP
import OCF.Lean.YiLegFold as SF
import OCF.Lean.YiVTFold as VT
import OCF.Lean.YiVTRel as VR
import OCF.Lean.YiBROps as BO
import OCF.Lean.YiBRFold as BF
import OCF.Lean.YiBRTw as Tw
open import OCF.Lean.YiBRRel
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceSelfInput as D
open import OCF.Lean.YiLSRead using (read)
open import OCF.Align.Value using (_≼_)

rest : J.Tr 1 → S.L
rest d = S.zero S.⊕ S.↑ (J.nat 1) (S.suc d)
old-ev : ∀ d → SP.Ev (C.old-child d)
old-ev d = SP.Ev⊕ (J.nat 2) (rest d) (D.ev 2)
  (SP.EvO⊕ (J.nat 2) S.zero (S.↑ (J.nat 1) (S.suc d)) tt
    (SP.EvO↑ (J.nat 2) (J.nat 1) (D.ev 1) (SP.ins SP.self) (S.suc d)))
old-rt : ∀ d → SP.Rt (C.old-child d)
old-rt d = SP.Rt⊕ (J.nat 2) (rest d) (D.rt 2)
  (SP.RtP⊕ S.zero (S.↑ (J.nat 1) (S.suc d)) tt (SP.RtP↑ (J.nat 1) (D.rt 1) (S.suc d)))
child-E : ∀ {d d′} → RelT K.one (J.nat 1) d d′ →
  RelE (U.a d) (C.old-child d′) (proj₂ U.o₂ d) (old-ev d′) (old-rt d′)
-- perf: 非单射的 EvO/RtP 不能反推后继形状，显式给出全部坐标。
child-E {d} {d′} r = Tw.⊕-E {a = K.two} {a′ = J.nat 2}
  {b = B.zero B.⊕ B.↑ K.one (B.suc d)} {b′ = rest d′} (eS (eS ez))
  (Tw.⊕-EO {a = K.two} {a′ = J.nat 2} {b₁ = B.zero} {b₁′ = S.zero}
    {b₂ = B.↑ K.one (B.suc d)} {b₂′ = S.↑ (J.nat 1) (S.suc d′)} Tw.oz
    (Tw.↑-EO {a = K.two} {a′ = J.nat 2} {k = K.one} {k′ = J.nat 1}
      (eS ez) (wincS wself) {x = B.suc d} {x′ = S.suc d′} (is r)))

-- 这是附加 RelE 条件的值出口；不把 UpperChild.model 当成未证明的封顶律。
upper-child-fold-exit : ∀ {ell X₁} (c : C.UpperChild ell X₁) (o : P.Ok ell) →
  RelE ell (C.old-child (C.UpperChild.source c)) o
    (old-ev (C.UpperChild.source c)) (old-rt (C.UpperChild.source c)) →
  K.readRW (proj₁ (MT.ψ₀ᶻ ell o (proj₁ (O.Ωt ell)))) ≼
  read (VT.ψ⊥ (C.old-child (C.UpperChild.source c)) (old-ev (C.UpperChild.source c))
    (old-rt (C.UpperChild.source c)) (SF.B₀ (C.old-child (C.UpperChild.source c)))
    (SO.Ωt (C.old-child (C.UpperChild.source c))))
upper-child-fold-exit {ell} c o re = Fin.read-rel (proj₁
  (VR.A re (F.B₀ ell) (SF.B₀ (C.old-child (C.UpperChild.source c)))
    (BF.B₀-R (C.UpperChild.coordinate c)) (O.Ωt B.zero) (is iz) ds
    (BO.Ωt-R (C.UpperChild.coordinate c))))

out1-model-upper : K.readRW (proj₁ (U.Inner.out (U.Inner.chain 1))) ≼
  read (VT.ψ⊥ (C.old-child X.chain1-old) (old-ev X.chain1-old) (old-rt X.chain1-old)
    (SF.B₀ (C.old-child X.chain1-old)) (SO.Ωt (C.old-child X.chain1-old)))
out1-model-upper = subst (λ q → K.readRW (proj₁ q) ≼
  read (VT.ψ⊥ (C.old-child X.chain1-old) (old-ev X.chain1-old) (old-rt X.chain1-old)
    (SF.B₀ (C.old-child X.chain1-old)) (SO.Ωt (C.old-child X.chain1-old))))
  (sym (UL.out-child (U.Inner.chain 1))) (upper-child-fold-exit C.actual (proj₂ U.o₂ (U.Inner.chain 1)) (child-E X.chain1-related))
```
