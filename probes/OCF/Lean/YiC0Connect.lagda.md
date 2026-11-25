# 平移结点接回公共干净对象
验收文件；编译定理：指定 neck 的标准底输出不低于 BTBO，neck-low 实填 YiC0Reduce.NeckLow。
公共 YiUTTwo/YiUTTwoLocal 只读；没有更换底、表、路径或输出。
来源：相关性复用 YiMTRel.topΩ，值下界复用 YiC0Rows.btbo，记号出口复用 YiEXRow。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC0Connect where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiC0Local as C
import OCF.Lean.YiC0Reduce as R
import OCF.Lean.YiC0Pad as A
import OCF.Lean.YiC0Node as N
import OCF.Lean.YiLegBlock as L
import OCF.Lean.YiLegOps as L
import OCF.Lean.YiLegPath as L
import OCF.Lean.YiLegFold as L
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRTw using (∙V-R; wk-V; ⊕⊑-V; ◃→⊑-V)
open import OCF.Lean.YiBRLem using (E→L)
pad : B.Tr B.zero → B.L
pad d = K.two B.⊕ (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero d))
pad-w : (d : B.Tr B.zero) → P._≤_ B.zero (pad d)
pad-w d = P.inc tt (P.inc tt P.self) P.∙ P.lift K.two (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero d))
pad-W : ∀ {d d′} → RelT B.zero L.zero d d′ → RelW (pad-w d) (A.wh d′)
pad-W {d = B.zero} iz = wincS (wincS wself)
pad-W {d = B.suc d} (is r) = winuS (pad-W r)
pad-W {d = B.lim f a} (il (rf , ra)) = winuL (λ n → pad-W (rf n))
private
  zero-V : ∀ {j ℓ j′ ℓ′} {v : P._⊑_ j ℓ} {v′ : L._⊑_ j′ ℓ′}
    → RelV v v′ → RelV (P.⊕⊑ B.zero v) v′
  zero-V vself = vself
  zero-V (vincS r) = vincS (zero-V r)
  zero-V (vinuS r) = vinuS (zero-V r)
  zero-V (vincL n r) = vincL n (zero-V r)
  zero-V (vinuL r) = vinuL (λ n → zero-V (r n))
  zero-V (vincΩ rc r) = vincΩ rc (zero-V r)
  zero-V (vinuΩ r) = vinuΩ (λ c c′ rc → zero-V (r c c′ rc))
pad-V : ∀ {x y x′ y′} {d : B._⊢_◃_ B.zero x y} {d′ : L._⊢_◃_ L.zero x′ y′}
  → RelD B.zero L.zero d d′
  → RelV (P.⊕⊑ K.two (P.⊕⊑ B.zero (P.⊕⊑ B.zero (P.◃→⊑ B.zero d))))
    (L.⊕⊑ A.two₀ (L.◃→⊑ L.zero d′))
pad-V r = ⊕⊑-V (zero-V (zero-V (◃→⊑-V lz r)))
pad-o : (d : B.Tr B.zero) → P.Ok (pad d)
pad-o d = proj₂ (proj₂ R.o-neck d) tt
opaque
  unfolding C.neck-path C.c₁ U.Inner.feed U.Inner.g
  pad-E : ∀ {d d′} → RelT B.zero L.zero d d′
    → RelE (pad d) (A.h₁ d′) (pad-o d) (A.εh d′) (A.ρh d′)
  pad-E {d = B.zero} iz = eS (eS ez)
  pad-E {d = B.suc d} (is r) = eS (pad-E r)
  pad-E {d = B.lim f a} (il (rf , ra)) = eL (λ n → wk-V (pad-V (ra n))) (λ n → pad-E (rf n))
-- perf: C-24，实际证明的路径公式只展开一次；不把它换成一致零路径。
opaque
  unfolding C.neck-path C.c₁ U.Inner.feed U.Inner.g
  zero-route : (d : B.Tr B.zero) → proj₂ (proj₁ R.o-neck) d
    ≡ ((P.inc tt (P.inc tt P.self)) P.∙
       P.lift K.two (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero (B.suc d))))
  zero-route d = refl
route-R : ∀ d d′ → RelT B.zero L.zero d d′ → RelW (proj₂ (proj₁ R.o-neck) d) (N.wh d′)
route-R d d′ r = subst (λ w → RelW w (N.wh d′)) (sym (zero-route d)) (winuS (pad-W r))
node-E : RelE C.neck N.ΩN R.o-neck N.εN N.ρN
node-E = eΩ ez route-R (λ d d′ r → eS (pad-E r))
open import OCF.Lean.YiNRHit using (NoΩ)
import OCF.Lean.YiMTRel as MR
import OCF.Lean.YiBROps as BO
import OCF.Lean.YiBRFold as BF
import OCF.Lean.YiBRValue as BV
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiEXRow as XR
import OCF.Align.EboLeanTree as ET
import OCF.Align.YiBtValBT
import OCF.Lean.YiC0Rows as Rows
open import OCF.Align.Value using (_≼_; ≼-trans)
no-pad : ∀ d → NoΩ (pad d)
no-pad B.zero = λ _ _ → tt
no-pad (B.suc d) = λ _ → no-pad d
no-pad (B.lim f a) = λ n → no-pad (f n)
no-child : ∀ d → NoΩ (K.two B.⊕ (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero (B.suc d))))
no-child d = λ _ → no-pad d
output-R : RelT B.zero L.zero
  (proj₁ (MT.ψ₀ᶻ C.neck R.o-neck (proj₁ (O.Ωt C.neck)))) N.output
output-R = proj₁ (MR.topΩ node-E no-child (F.B₀ C.neck) (L.B₀ N.ΩN)
  (BF.B₀-R (E→L node-E)) (O.Ωt B.zero) (is iz) ds
  (λ z → MR.u0 z _ _) (BO.Ωt-R (E→L node-E)))
neck-btbo : OCF.Align.YiBtValBT.D.BTBOᴵ ≼ K.readRW (proj₁ R.neck-out)
neck-btbo = subst (λ z → OCF.Align.YiBtValBT.D.BTBOᴵ ≼ K.readRW (proj₁ z)) (sym R.neck-out-eq)
  (≼-trans (BV.up≼ output-R Rows.btbo)
    (CS.rr≼ (proj₁ (MT.ψ₀ᶻ C.neck R.o-neck (proj₁ (O.Ωt C.neck))))))
neck-low : R.NeckLow
neck-low = ≼-trans (RT.tree-≼ refl R.hc₀ (ET.hc-tower 2)) (≼-trans XR.row₂-btbo neck-btbo)
```
