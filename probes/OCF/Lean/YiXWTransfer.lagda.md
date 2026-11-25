# 含 Ω 实际孩子上的旧折叠上界搬运失败
验收文件；编译否定：a(chain 1) 上不存在最小表折叠 ≤ 原折叠的全路径全源树律；显式源树给严格反向值界。
只否定 Transfer 的全路径全源树接法；未证反例源树与路径出现在实际 out(chain 1) 的递归中，不判定 output 或里程碑。
来源：两行按 YiTBRow/YiRWFold 计算；读回加法沿 YiKidGen，反自升复用 YiNFO；neck 反例沿前三个可数头搬运，入口 no-chain1-transfer。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXWTransfer where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiC0Local as C
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; l≼; ≼l; ≼-refl; ≼-trans; ≅→≼) renaming (+-mono to plus-mono)
open import OCF.Lean.YiNFO using (s≼-irrefl)

-- 两个同文读回并非同一函数；沿 YiKidGen.read-+ᴿ 对 K.readRW 写出口。
read-plus : ∀ (a b : B.Tr B.zero) → K.readRW (a O.+ b) L.≅ (K.readRW a L.+ K.readRW b)
read-plus a B.zero = L.≅-refl⁰ (K.readRW a)
read-plus a (B.suc b) = L.s≅ (read-plus a b)
read-plus a (B.lim f _) = L.l≅ (λ n → read-plus a (f n))
read-iota : ∀ (a : B.Tr B.zero) → K.readRW (O.ι B.zero a) ≼ K.readRW a
read-iota B.zero = z≼
read-iota (B.suc a) = s≼s (read-iota a)
read-iota (B.lim f _) = l≼ (λ n → ≼l n (read-iota (f n)))

module Row (h : B.Tr B.zero → B.L) (o : P.Ok (B.nd (B.sΩ B.zero) h)) where
  ell = B.nd (B.sΩ B.zero) h
  w : B.zero P.≤ ell
  w = P.inc B.zero (P.z≤ (h B.zero))
  x : B.Tr ell
  x = B.up (B.suc B.zero) B.zero (B.suc B.zero) B.◃s
  new = TB.ψ ell o (MT.rbᶻ ell) (F.B₀ ell) B.zero w (O.Ωt B.zero) x
  old = F.ψ ell o (F.B₀ ell) B.zero w (O.Ωt B.zero) x
  new-row : new ≡ O.next⁺ (O.next⁺ (O.Ωt B.zero))
  new-row = refl
  old-row : old ≡ O.next⁺ (O.Ωt B.zero) O.⊞ O.next⁺ (O.Ωt B.zero)
  old-row = refl
  omega = proj₁ (O.next⁺ (O.Ωt B.zero))
  old-upper : K.readRW (proj₁ old) ≼ K.readRW (omega O.+ omega)
  old-upper = ≼-trans (≅→≼ (read-plus omega (O.ι B.zero omega)))
    (≼-trans (plus-mono (≼-refl (K.readRW omega)) (read-iota omega))
      (≅→≼ (L.≅-sym (read-plus omega omega))))
  strict : L.suc (K.readRW (proj₁ old)) ≼ K.readRW (proj₁ new)
  strict = ≼-trans (s≼s old-upper) (≼l 2 (≼l 0 (≼-refl _)))
  no-transfer : K.readRW (proj₁ new) ≼ K.readRW (proj₁ old) → ⊥
  no-transfer p = s≼-irrefl (K.readRW (proj₁ old)) (≼-trans strict p)

import OCF.Lean.YiUTTwo as U
open import Data.Product using (_,_) 
first-ok : ∀ ell → P.Ok ell → P.Ok (C.first ell)
first-ok B.zero o = o
first-ok (B.nd B.sS h) o = proj₂ o tt
first-ok (B.nd B.sL h) o = proj₂ o 0
first-ok (B.nd (B.sΩ k) h) o = proj₂ o B.zero
neck-ok : P.Ok C.neck
neck-ok = subst P.Ok C.neck-shape
  (first-ok (C.first (C.first C.ℓ₁))
    (first-ok (C.first C.ℓ₁) (first-ok C.ℓ₁ (proj₂ U.o₂ C.c₁))))
module AtNeck = Row
  (λ d → K.two B.⊕ (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero (B.suc d)))) neck-ok

Transfer : (ell : B.L) → P.Ok ell → Set
Transfer ell o = (w : B.zero P.≤ ell) (beta : O.Tr⁺ B.zero) (x : B.Tr ell) →
  K.readRW (proj₁ (TB.ψ ell o (MT.rbᶻ ell) (F.B₀ ell) B.zero w beta x)) ≼
  K.readRW (proj₁ (F.ψ ell o (F.B₀ ell) B.zero w beta x))
no-neck-transfer : Transfer C.neck neck-ok → ⊥
no-neck-transfer h = AtNeck.no-transfer (h AtNeck.w (O.Ωt B.zero) AtNeck.x)

record Bad (ell : B.L) (o : P.Ok ell) : Set where
  field
    path : B.zero P.≤ ell
    source : O.Tr⁺ ell
    smaller : L.suc (K.readRW (proj₁ (F.ψ ell o (F.B₀ ell) B.zero path (O.Ωt B.zero) (proj₁ source)))) ≼
      K.readRW (proj₁ (TB.ψ ell o (MT.rbᶻ ell) (F.B₀ ell) B.zero path (O.Ωt B.zero) (proj₁ source)))

neck-bad : Bad C.neck neck-ok
Bad.path neck-bad = AtNeck.w
Bad.source neck-bad = AtNeck.x , B.◃t B.◃s (B.◃u (B.suc B.zero) B.zero (B.suc B.zero) B.◃s)
Bad.smaller neck-bad = AtNeck.strict

bad-cast : ∀ {ell ell′} (eq : ell ≡ ell′) (o : P.Ok ell) → Bad ell′ (subst P.Ok eq o) → Bad ell o
bad-cast refl o b = b

data HeadC : B.L → Set where
  hs : ∀ {h} → HeadC (B.nd B.sS h)
  hl : ∀ {h} → HeadC (B.nd B.sL h)

lift-bad : ∀ ell (o : P.Ok ell) → HeadC ell → Bad (C.first ell) (first-ok ell o) → Bad ell o
Bad.path (lift-bad (B.nd B.sS h) o hs b) = P.inc tt (Bad.path b)
Bad.source (lift-bad (B.nd B.sS h) o hs b) = O.upz tt (Bad.source b)
Bad.smaller (lift-bad (B.nd B.sS h) o hs b) = Bad.smaller b
Bad.path (lift-bad (B.nd B.sL h) o hl b) = P.inc 0 (Bad.path b)
Bad.source (lift-bad (B.nd B.sL h) o hl b) = O.upz 0 (Bad.source b)
Bad.smaller (lift-bad (B.nd B.sL h) o hl b) = Bad.smaller b

head0 : HeadC C.ℓ₁
head0 = hs
opaque
  unfolding C.c₁ U.Inner.feed U.Inner.g
  head1 : HeadC (C.first C.ℓ₁)
  head1 = hl
  head2 : HeadC (C.first (C.first C.ℓ₁))
  head2 = hl

first1-ok = first-ok C.ℓ₁ (proj₂ U.o₂ C.c₁)
first2-ok = first-ok (C.first C.ℓ₁) first1-ok
first3-ok = first-ok (C.first (C.first C.ℓ₁)) first2-ok
actual-bad : Bad C.ℓ₁ (proj₂ U.o₂ C.c₁)
actual-bad = lift-bad C.ℓ₁ (proj₂ U.o₂ C.c₁) head0
  (lift-bad (C.first C.ℓ₁) first1-ok head1
    (lift-bad (C.first (C.first C.ℓ₁)) first2-ok head2
      (bad-cast C.neck-shape first3-ok neck-bad)))
no-actual-transfer : Transfer C.ℓ₁ (proj₂ U.o₂ C.c₁) → ⊥
no-actual-transfer h = s≼-irrefl _ (≼-trans (Bad.smaller actual-bad)
  (h (Bad.path actual-bad) (O.Ωt B.zero) (proj₁ (Bad.source actual-bad))))

no-chain1-transfer : Transfer (U.a (U.Inner.chain 1)) (proj₂ U.o₂ (U.Inner.chain 1)) → ⊥
no-chain1-transfer h = no-actual-transfer
  (subst (λ d → Transfer (U.a d) (proj₂ U.o₂ d)) (sym C.c₁-eq) h)
```
