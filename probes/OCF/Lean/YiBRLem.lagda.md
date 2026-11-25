# 新旧块的逐层关系: 槽位, 路径, 比较

> 编译定理 (验收用, 对一切相关的层号与槽位, 无前提): 槽位所在的层号与证据相关 (`at-L`, `E-at`), 换型与第一分支相关 (`fromBr-R`, `br0-R`), 槽位的路径相关 (`posW-R`), 推进与换回 (`psh-R`, `pshBr-R`), 路径的合成 (`∙-R`), ℕ 极限层号上两个孩子的比较相关 (`way-R`, 两边接路径的方式不同), 下行链的搬运 (`mv-R`, `mvBr-R`).
> 不否定什么. 关系的定义在 `YiBRRel`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBRLem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
open import OCF.Lean.YiBRRel
```

## 层号, 槽位, 换型

```agda
E→L : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → RelL ℓ ℓ′
E→L ez         = lz
E→L (eS re)    = lS (E→L re)
E→L (eL _ re)  = lL (λ n → E→L (re n))
E→L (eΩ rk rwc rc) = lΩ (E→L rk) (λ c c′ r → E→L ((rc c c′ r)))

mutual
  at-L : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → (p : Pos ℓ) (p′ : F.Pos ℓ′) → RelP ℓ ℓ′ p p′ → RelL (at ℓ p) (F.at ℓ′ p′)
  at-L lz         () _ _
  at-L (lS r)     (inj₁ ()) _ _
  at-L (lS r)     (inj₂ (c , t)) t′ rp = at⁼-L r t t′ rp
  at-L (lL r)     (inj₁ ()) _ _
  at-L (lL r)     (inj₂ (n , t)) .(n , _) (iσₙ rp) = at⁼-L (r n) t _ rp
  at-L (lΩ rk rh) (inj₁ t) .(inj₁ _) (i₁ rp) = at⁼-L rk t _ rp
  at-L (lΩ rk rh) (inj₂ (c , t)) .(inj₂ (_ , _)) (i₂ (iσ (rc , rp))) = at⁼-L (rh c _ rc) t _ rp

  at⁼-L : ∀ {a a′} → RelL a a′ → (t : Pos⁼ a) (t′ : F.Pos⁼ a′) → RelP⁼ a a′ t t′ → RelL (proj₁ (sl⁼ a t)) (F.at⁼ a′ t′)
  at⁼-L r (inj₁ _) .(inj₁ _) (i₁ _)  = r
  at⁼-L r (inj₂ p) .(inj₂ _) (i₂ rp) = at-L r p _ rp

mutual
  E-at : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (p : Pos ℓ) (p′ : F.Pos ℓ′) → RelP ℓ ℓ′ p p′
       → RelE (at ℓ p) (F.at ℓ′ p′) (Ok-at ℓ o p) (F.Ev-at ℓ′ ε p′) (F.Rt-at ℓ′ ρ p′)
  E-at ez         () _ _
  E-at (eS re)    (inj₁ ()) _ _
  E-at (eS re)    (inj₂ (c , t)) t′ rp = E-at⁼ re t t′ rp
  E-at (eL _ re)  (inj₁ ()) _ _
  E-at (eL _ re)  (inj₂ (n , t)) .(n , _) (iσₙ rp) = E-at⁼ (re n) t _ rp
  E-at (eΩ rk rwc rc) (inj₁ t) .(inj₁ _) (i₁ rp) = E-at⁼ rk t _ rp
  E-at (eΩ rk rwc rc) (inj₂ (c , t)) .(inj₂ (_ , _)) (i₂ (iσ (r , rp))) = E-at⁼ ((rc c _ r)) t _ rp

  E-at⁼ : ∀ {a a′ o ε ρ} → RelE a a′ o ε ρ → (t : Pos⁼ a) (t′ : F.Pos⁼ a′) → RelP⁼ a a′ t t′
        → RelE (proj₁ (sl⁼ a t)) (F.at⁼ a′ t′) (Ok-at⁼ a o t) (F.Ev-at⁼ a′ ε t′) (F.Rt-at⁼ a′ ρ t′)
  E-at⁼ re (inj₁ _) .(inj₁ _) (i₁ _)  = re
  E-at⁼ re (inj₂ p) .(inj₂ _) (i₂ rp) = E-at re p _ rp

mutual
  fromBr-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → (p : Pos ℓ) (p′ : F.Pos ℓ′) → RelP ℓ ℓ′ p p′
           → {x : Tr (at ℓ p)} {x′ : F.Tr (F.at ℓ′ p′)} → RelT (at ℓ p) (F.at ℓ′ p′) x x′
           → RelB ℓ ℓ′ p p′ (fromBr ℓ p x) (F.fromBr ℓ′ p′ x′)
  fromBr-R lz         () _ _
  fromBr-R (lS r)     (inj₁ ()) _ _
  fromBr-R (lS r)     (inj₂ (c , t)) t′ rp rx = fromBr⁼-R r t t′ rp rx
  fromBr-R (lL r)     (inj₁ ()) _ _
  fromBr-R (lL r)     (inj₂ (n , t)) .(n , _) (iσₙ rp) rx = fromBr⁼-R (r n) t _ rp rx
  fromBr-R (lΩ rk rh) (inj₁ t) .(inj₁ _) (i₁ rp) rx = fromBr⁼-R rk t _ rp rx
  fromBr-R (lΩ rk rh) (inj₂ (c , t)) .(inj₂ (_ , _)) (i₂ (iσ (rc , rp))) rx = fromBr⁼-R (rh c _ rc) t _ rp rx

  fromBr⁼-R : ∀ {a a′} → RelL a a′ → (t : Pos⁼ a) (t′ : F.Pos⁼ a′) → RelP⁼ a a′ t t′
            → {x : Tr (proj₁ (sl⁼ a t))} {x′ : F.Tr (F.at⁼ a′ t′)} → RelT (proj₁ (sl⁼ a t)) (F.at⁼ a′ t′) x x′
            → RelB⁼ a a′ t t′ (proj₂ (sl⁼ a t) x) (F.fromBr⁼ a′ t′ x′)
  fromBr⁼-R r (inj₁ _) .(inj₁ _) (i₁ _)  rx = rx
  fromBr⁼-R r (inj₂ p) .(inj₂ _) (i₂ rp) rx = fromBr-R r p _ rp rx

mutual
  br0-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → (p : Pos ℓ) (p′ : F.Pos ℓ′) → RelP ℓ ℓ′ p p′
        → RelB ℓ ℓ′ p p′ (fromBr ℓ p zero) (F.br0 ℓ′ p′)
  br0-R lz         () _ _
  br0-R (lS r)     (inj₁ ()) _ _
  br0-R (lS r)     (inj₂ (c , t)) t′ rp = br0⁼-R r t t′ rp
  br0-R (lL r)     (inj₁ ()) _ _
  br0-R (lL r)     (inj₂ (n , t)) .(n , _) (iσₙ rp) = br0⁼-R (r n) t _ rp
  br0-R (lΩ rk rh) (inj₁ t) .(inj₁ _) (i₁ rp) = br0⁼-R rk t _ rp
  br0-R (lΩ rk rh) (inj₂ (c , t)) .(inj₂ (_ , _)) (i₂ (iσ (rc , rp))) = br0⁼-R (rh c _ rc) t _ rp

  br0⁼-R : ∀ {a a′} → RelL a a′ → (t : Pos⁼ a) (t′ : F.Pos⁼ a′) → RelP⁼ a a′ t t′
         → RelB⁼ a a′ t t′ (proj₂ (sl⁼ a t) zero) (F.br0⁼ a′ t′)
  br0⁼-R r (inj₁ _) .(inj₁ _) (i₁ _)  = iz
  br0⁼-R r (inj₂ p) .(inj₂ _) (i₂ rp) = br0-R r p _ rp

mutual
  posW-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → (p : Pos ℓ) (p′ : F.Pos ℓ′) → RelP ℓ ℓ′ p p′ → RelW (posW ℓ p) (F.posW ℓ′ p′)
  posW-R lz         () _ _
  posW-R (lS r)     (inj₁ ()) _ _
  posW-R (lS r)     (inj₂ (c , t)) t′ rp = wincS (posW⁼-R r t t′ rp)
  posW-R (lL r)     (inj₁ ()) _ _
  posW-R (lL r)     (inj₂ (n , t)) .(n , _) (iσₙ rp) = wincL n (posW⁼-R (r n) t _ rp)
  posW-R (lΩ rk rh) (inj₁ t) .(inj₁ _) (i₁ rp) = wink (posW⁼-R rk t _ rp)
  posW-R (lΩ rk rh) (inj₂ (c , t)) .(inj₂ (_ , _)) (i₂ (iσ (rc , rp))) = wincΩ rc (posW⁼-R (rh c _ rc) t _ rp)

  posW⁼-R : ∀ {a a′} → RelL a a′ → (t : Pos⁼ a) (t′ : F.Pos⁼ a′) → RelP⁼ a a′ t t′ → RelW (posW⁼ a t) (F.posW⁼ a′ t′)
  posW⁼-R r (inj₁ _) .(inj₁ _) (i₁ _)  = wself
  posW⁼-R r (inj₂ p) .(inj₂ _) (i₂ rp) = posW-R r p _ rp
```

## 推进, 换回, 合成

```agda
psh-R : ∀ {k a k′ a′} {v : k ≤ a} {v′ : F._≤_ k′ a′} → RelW v v′
      → (t : Pos⁼ k) (t′ : F.Pos⁼ k′) → RelP⁼ k k′ t t′ → RelP⁼ a a′ (psh v t) (F.psh v′ t′)
psh-R wself         t t′ r = r
psh-R (wincS rv)    t t′ r = i₂ (psh-R rv t t′ r)
psh-R (winuS rv)    t t′ r = i₂ (psh-R rv t t′ r)
psh-R (wincL n rv)  t t′ r = i₂ (iσₙ (psh-R rv t t′ r))
psh-R (winuL rvs)   t t′ r = i₂ (iσₙ (psh-R (rvs zero) t t′ r))
psh-R (wincΩ rc rv) t t′ r = i₂ (i₂ (iσ (rc , psh-R rv t t′ r)))
psh-R (winuΩ rvs)   t t′ r = i₂ (i₂ (iσ (iz , psh-R (rvs zero F.zero iz) t t′ r)))
psh-R (wink rv)     t t′ r = i₂ (i₁ (psh-R rv t t′ r))

pshBr-R : ∀ {k a k′ a′} {v : k ≤ a} {v′ : F._≤_ k′ a′} → RelW v v′ → (t : Pos⁼ k) (t′ : F.Pos⁼ k′)
        → {z : Br⁼ a (psh v t)} {z′ : F.Br⁼ a′ (F.psh v′ t′)} → RelB⁼ a a′ (psh v t) (F.psh v′ t′) z z′
        → RelB⁼ k k′ t t′ (pshBr v t z) (F.pshBr v′ t′ z′)
pshBr-R wself         t t′ r = r
pshBr-R (wincS rv)    t t′ r = pshBr-R rv t t′ r
pshBr-R (winuS rv)    t t′ r = pshBr-R rv t t′ r
pshBr-R (wincL n rv)  t t′ r = pshBr-R rv t t′ r
pshBr-R (winuL rvs)   t t′ r = pshBr-R (rvs zero) t t′ r
pshBr-R (wincΩ rc rv) t t′ r = pshBr-R rv t t′ r
pshBr-R (winuΩ rvs)   t t′ r = pshBr-R (rvs zero F.zero iz) t t′ r
pshBr-R (wink rv)     t t′ r = pshBr-R rv t t′ r

∙-R : ∀ {i j ℓ i′ j′ ℓ′} {w : i ≤ j} {w′ : F._≤_ i′ j′} {v : j ≤ ℓ} {v′ : F._≤_ j′ ℓ′}
    → RelW w w′ → RelW v v′ → RelW (w ∙ v) (w′ F.∙ v′)
∙-R rw wself         = rw
∙-R rw (wincS rv)    = wincS (∙-R rw rv)
∙-R rw (winuS rv)    = winuS (∙-R rw rv)
∙-R rw (wincL n rv)  = wincL n (∙-R rw rv)
∙-R rw (winuL rvs)   = winuL (λ n → ∙-R rw (rvs n))
∙-R rw (wincΩ rc rv) = wincΩ rc (∙-R rw rv)
∙-R rw (winuΩ rvs)   = winuΩ (λ c c′ r → ∙-R rw (rvs c c′ r))
∙-R rw (wink rv)     = wink (∙-R rw rv)

idl-R : ∀ {j ℓ j′ ℓ′} {v : j ≤ ℓ} {v′ : F._≤_ j′ ℓ′} → RelW v v′ → RelW (self ∙ v) v′
idl-R wself         = wself
idl-R (wincS rv)    = wincS (idl-R rv)
idl-R (winuS rv)    = winuS (idl-R rv)
idl-R (wincL n rv)  = wincL n (idl-R rv)
idl-R (winuL rvs)   = winuL (λ n → idl-R (rvs n))
idl-R (wincΩ rc rv) = wincΩ rc (idl-R rv)
idl-R (winuΩ rvs)   = winuΩ (λ c c′ r → idl-R (rvs c c′ r))
idl-R (wink rv)     = wink (idl-R rv)
```

## ℕ 极限层号上两个孩子的比较

精简块由 `from0` 从第 0 项接起, F2 由 `rt` 从 m 接起; 两边的路径不是同一个项, 但相关.

```agda
data RelWay {g : ℕ → L} {g′ : ℕ → F.L} {m n : ℕ} : (g m ≤ g n) ⊎ (g n ≤ g m) → F.Way g′ m n → Set where
  rfwd : ∀ {u u′} → RelW u u′ → RelWay (inj₁ u) (F.fwd u′)
  rbwd : ∀ {u u′} → RelW u u′ → RelWay (inj₂ u) (F.bwd u′)

from0-R : ∀ {g g′} {r : (n : ℕ) → g n ≤ g (suc n)} {R : F.Adj g′} → ((n : ℕ) → RelW (r n) (R n))
        → (n : ℕ) → RelW (from0 g r (suc n)) (F.rt g′ R (F.z< n))
from0-R rr zero    = idl-R (rr zero)
from0-R rr (suc n) = ∙-R (from0-R rr n) (rr (suc n))

rt-s : ∀ {g′ : ℕ → F.L} (R : F.Adj g′) {m n : ℕ} (l : m F.<ₙ n)
     → F.rt g′ R (F.s< l) ≡ F.rt (λ i → g′ (suc i)) (λ i → R (suc i)) l
rt-s R F.here          = refl
rt-s R (F.nxt {n} l)   = cong (λ w → w F.∙ R (suc n)) (rt-s R l)

shift : ∀ {g g′} (R : F.Adj g′) {m n : ℕ} (c : F.Cmp m n) {X : (g (suc m) ≤ g (suc n)) ⊎ (g (suc n) ≤ g (suc m))}
      → RelWay {λ i → g (suc i)} {λ i → g′ (suc i)} {m} {n} X (F.way′ (λ i → g′ (suc i)) (λ i → R (suc i)) c)
      → RelWay {g} {g′} {suc m} {suc n} X (F.way′ g′ R (F.sC c))
shift R F.eq     (rbwd r) = rbwd r
shift R (F.lt l) (rfwd r) = rfwd (subst (RelW _) (sym (rt-s R l)) r)
shift R (F.gt l) (rbwd r) = rbwd (subst (RelW _) (sym (rt-s R l)) r)

way-R : ∀ {g g′} {r : (n : ℕ) → g n ≤ g (suc n)} {R : F.Adj g′} → ((n : ℕ) → RelW (r n) (R n))
      → (m n : ℕ) → RelWay (way g r m n) (F.way g′ R m n)
way-R rr zero    zero    = rbwd wself
way-R rr (suc m) zero    = rbwd (from0-R rr m)
way-R rr zero    (suc n) = rfwd (from0-R rr n)
way-R {g} {g′} {r} {R} rr (suc m) (suc n) = shift R (F.cmp m n) (way-R (λ i → rr (suc i)) m n)
```

## 下行链

```agda
data RelDn {ℓ : L} {ℓ′ : F.L} : {j : L} {j′ : F.L} → Dn ℓ j → F.Dn ℓ′ j′ → Set where
  dstop : RelDn stop F.stop
  ddown : ∀ {s h j′} {d : Dn ℓ (nd s h)} {d′ : F.Dn ℓ′ j′} {c : Ch s} {c′ : F.Ch j′}
        → RelL (nd s h) j′ → RelDn d d′ → RelC (nd s h) j′ c c′ → RelDn (down d c) (F.down d′ c′)

mv-R : ∀ {ℓ ℓ′ j j′} {d : Dn ℓ j} {d′ : F.Dn ℓ′ j′} → RelDn d d′
     → (p : Pos j) (p′ : F.Pos j′) → RelP j j′ p p′ → RelP ℓ ℓ′ (mv d p) (F.mv d′ p′)
mv-R dstop                p p′ rp = rp
mv-R (ddown (lS _) rd _)  p p′ rp = mv-R rd _ _ (i₂ rp)
mv-R (ddown (lL _) rd refl) p p′ rp = mv-R rd _ _ (iσₙ (i₂ rp))
mv-R (ddown (lΩ _ _) rd rc) p p′ rp = mv-R rd _ _ (i₂ (iσ (rc , i₂ rp)))

mvBr-R : ∀ {ℓ ℓ′ j j′} {d : Dn ℓ j} {d′ : F.Dn ℓ′ j′} → RelDn d d′ → (p : Pos j) (p′ : F.Pos j′)
       → {z : Br ℓ (mv d p)} {z′ : F.Br ℓ′ (F.mv d′ p′)} → RelB ℓ ℓ′ (mv d p) (F.mv d′ p′) z z′
       → RelB j j′ p p′ (mvBr d p z) (F.mvBr d′ p′ z′)
mvBr-R dstop                  p p′ r = r
mvBr-R (ddown (lS _) rd _)    p p′ r = mvBr-R rd _ _ r
mvBr-R (ddown (lL _) rd refl) p p′ r = mvBr-R rd _ _ r
mvBr-R (ddown (lΩ _ _) rd rc) p p′ r = mvBr-R rd _ _ r
```

## 推导经等式搬运

```agda
RelD-substˡ : ∀ {ℓ ℓ′} {A : Set} (X Y : A → Tr ℓ) {t₁ t₂ : A} (e : t₁ ≡ t₂) {d : ℓ ⊢ X t₁ ◃ Y t₁}
  {x′ y′ : F.Tr ℓ′} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′ → RelD ℓ ℓ′ (subst (λ t → ℓ ⊢ X t ◃ Y t) e d) d′
RelD-substˡ X Y refl r = r

RelD-substʳ : ∀ {ℓ ℓ′} {A : Set} (X Y : A → F.Tr ℓ′) {t₁ t₂ : A} (e : t₁ ≡ t₂) {d′ : F._⊢_◃_ ℓ′ (X t₁) (Y t₁)}
  {x y : Tr ℓ} {d : ℓ ⊢ x ◃ y} → RelD ℓ ℓ′ d d′ → RelD ℓ ℓ′ d (subst (λ t → F._⊢_◃_ ℓ′ (X t) (Y t)) e d′)
RelD-substʳ X Y refl r = r
```
