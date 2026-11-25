# 两条实际链的一切前缀：ActualMissing 与 Offset
不读记号；编译定理，无前提：`YiOFLocal.ActualMissing` 有居民（`actual`），从而 `YiTNLocal.Offset`（`offset`）与 `ChainAdvance 1`（`advance`）成立；源第 n 项不高于目标第 n 项（`prefix-all`）。
层号等式：`C.f n` 是数字 n+1（`f-nat`），`C.h n ≡ S2 (C.g n)`（`eh`），两侧相邻路径按等式是 `inc tt self`（`Hg`、`Hh`，`Hh` 在展开 `H.first` 后成立）；第 0 项用 `YiOFLocal.At.first`。
不否定什么；`YiTZLocal` 的 Cover（一切 n 的 ChainAdvance）未做，见回报。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPTAll where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; trans)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiTBRow using (nat)
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiOGState as St
import OCF.Lean.YiOGTransfer as X
import OCF.Lean.YiTNShape as H
import OCF.Lean.YiTNRow as R
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTNLocal as NL
import OCF.Lean.YiTYLocal as Y
open import OCF.Lean.YiRRRel using (N)
open import OCF.Lean.YiRRTwo using (le→n₀)
open import OCF.Lean.YiPTLadder using (S1; S2)
open import OCF.Lean.YiPTTow using (Tow; tz; ts; Adj)
open import OCF.Lean.YiPTChain using (module Chain)
```

## 层号等式与相邻路径

```agda
f : ℕ → Tr zero
f = C.f

a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)
a = nextA (proj₁ (Ωt zero)) (proj₂ (Ωt zero))

G : Tr zero → L
G x = zero ⊕ ↑ zero x

Rg : (x y : Tr zero) → zero ⊢ x ◃ y → G x ≤ G y
Rg x y p = wk (⊕⊑ zero (◃→⊑ zero p))

Rh : (x y : Tr zero) → zero ⊢ x ◃ y → R.shift x ≤ R.shift y
Rh x y p = wk (⊕⊑ T.two (⊕⊑ zero (⊕⊑ zero (◃→⊑ zero p))))

Hf : (n : ℕ) → _≡_ {A = Σ (Tr zero) (λ y → zero ⊢ f n ◃ y)} (f (suc n) , a n) (suc (f n) , ◃s)
Hf zero = refl
Hf (suc n) = cong (λ q → (proj₁ (Ωt zero) + proj₁ q , +-mono (proj₁ (Ωt zero)) (proj₂ q))) (Hf n)

f-nat : (n : ℕ) → f n ≡ nat (suc n)
f-nat zero = refl
f-nat (suc n) = trans (cong proj₁ (Hf n)) (cong suc (f-nat n))

Hg : Adj C.g (proj₁ C.og)
Hg i = cong (λ q → (G (proj₁ q) , Rg (f i) (proj₁ q) (proj₂ q))) (Hf i)

opaque
  unfolding H.first H.curve H.line
  Hh : Adj C.h (proj₁ St.oh)
  Hh i = cong (λ q → (R.shift (proj₁ q) , Rh (f i) (proj₁ q) (proj₂ q))) (Hf i)

shift-nat : (k : ℕ) → R.shift (nat k) ≡ S2 (G (nat k))
shift-nat zero = refl
shift-nat (suc k) = cong S1 (shift-nat k)

eh : (n : ℕ) → C.h n ≡ S2 (C.g n)
eh n = subst (λ x → R.shift x ≡ S2 (G x)) (sym (f-nat n)) (shift-nat (suc n))

towG : (k : ℕ) → Tow (G (nat k))
towG zero = tz
towG (suc k) = ts (towG k)

tg : (n : ℕ) → Tow (C.g n)
tg n = subst Tow (cong G (sym (f-nat n))) (towG (suc n))

inuTr : ∀ {X Y : L} (p : X ≡ Y) (w : zero ≤ X)
  → subst (zero ≤_) (cong S1 p) (inu {s = sS} {h = λ _ → X} (λ _ → w)) ≡ inu {s = sS} {h = λ _ → Y} (λ _ → subst (zero ≤_) p w)
inuTr refl w = refl

hwk : (k : ℕ) → subst (zero ≤_) (shift-nat k) (self ∙ z≤ (R.shift (nat k)))
    ≡ inu (λ _ → inu (λ _ → self ∙ lift zero (↑ zero (nat k))))
hwk zero = refl
hwk (suc k) = trans (inuTr (shift-nat k) (self ∙ z≤ (R.shift (nat k)))) (cong (λ w → inu (λ _ → w)) (hwk k))

hw : (x : Tr zero) (k : ℕ) (e : x ≡ nat k)
   → subst (zero ≤_) (subst (λ x → R.shift x ≡ S2 (G x)) (sym e) (shift-nat k)) (self ∙ z≤ (R.shift x))
   ≡ inu (λ _ → inu (λ _ → self ∙ lift zero (↑ zero x)))
hw .(nat k) k refl = hwk k

Hw : (n : ℕ) → subst (zero ≤_) (eh n) (C.wh n) ≡ inu (λ _ → inu (λ _ → C.wg n))
Hw n = hw (f n) (suc n) (f-nat n)
```

## 实例与出口

```agda
module I = Chain C.g C.h C.og St.oh Hg Hh eh tg C.wg C.wh Hw

opaque
  unfolding St.G.piece St.G.fold St.G.prefix St.G.part
  pS : (n : ℕ) → St.G.piece n ≡ I.Src.piece n
  pS n = refl

opaque
  unfolding St.T.piece St.T.fold St.T.prefix St.T.part
  pT : (n : ℕ) → St.T.piece n ≡ I.Tgt.piece n
  pT n = refl

h0 : N zero (proj₁ (I.Src.piece 0)) (proj₁ (I.Tgt.piece 0))
h0 = le→n₀ (X.v→r _ _ (subst₂ (λ x y → V.val zero (proj₁ x) V.≼ V.val zero (proj₁ y)) (pS 0) (pT 0) St.A.first))

prefix-all : (n : ℕ) → V.val zero (proj₁ (St.G.piece n)) V.≼ V.val zero (proj₁ (St.T.piece n))
prefix-all n = subst₂ (λ x y → V.val zero (proj₁ x) V.≼ V.val zero (proj₁ y)) (sym (pS n)) (sym (pT n)) (I.mainV h0 n)

cover : St.A.A.PrefixCover
cover n = n , prefix-all n

opaque
  unfolding H.first H.curve H.line
  actual : C.ActualMissing
  actual = cover

offset : NL.Offset
offset = C.from-actual actual

second : Y.Canonical.ChainAt 2 2
second = C.second-from-prefix actual

advance : Y.Canonical.ChainAdvance 1
advance = C.advance-from-prefix actual
```
