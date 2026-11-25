# 换基实际 neck 的前提实例
验收文件；给 NoΩ 子层关系证明提供实际 RelE 与底关系实例，不宣称值界。
来源：YiC0Connect 的 pad-W、pad-V、pad-E、node-E 逐项搬用，仅换实际链点的证据来源。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBTPremise where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBSClean as U
import OCF.Lean.YiBTLocal as C
import OCF.Lean.YiBTLocal as R
import OCF.Lean.YiC0Local as Old
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
node-E : RelE Old.neck N.ΩN R.o-neck N.εN N.ρN
node-E = eΩ ez route-R (λ d d′ r → eS (pad-E r))
```
