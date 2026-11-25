# 槽位标签作参数的全层关系与公共运算

> 验收文件 (读记号)。编译定理: 对任意槽位标签 `Lab` 写出关系族 `R` (槽位余尾 `Lab (at ℓ p)`); 取 `Lab = Lbl` 时与 `YiGLExact.Rˣ` 互相给出 (见 [YiXPExact](YiXPExact.lagda.md)); `YiGIRel.R` 的余尾 `Nu` 按槽位递归到 `Rd`, 本文不与它对接。
> 来源: `YiGTGen` 的运算, `YiLKSlot.low-from`, `YiSUIface` 的 `PrefixU`, `StepU′` 逐行搬来, 只把 `GR.Nu ℓ p` 换成 `Lab (at ℓ p)`; 证明不用 `Lab` 的任何性质。不改树、折叠、合法性; 不否定什么。各行在 [YiXPRows](YiXPRows.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.YiRWBlock using (L)
import OCF.Align.EboLeanDef as E
module OCF.Lean.YiXPRel (Lab : L → E.T → Set) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; sym; trans)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath using (Ok; _≤_; self; inc; inu; ink; emb; _∙_; posW)
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiLKIface using (feed; OK)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (Pen; cofK; fsTK)
import OCF.Lean.YiHCRel as H
```

## 关系

```agda
mutual
  R : (ℓ : L) → E.T → Tr ℓ → Set
  R zero = H.M⁰
  R (nd s h) = H.Mᴴ (Sig (nd s h)) (Low (nd s h)) (λ c → R (h c)) (λ p → Lab (at (nd s h) p))

  Low : (ℓ : L) (p : Pos ℓ) → E.T → Br ℓ p → Set
  Low (nd s h) (inj₂ (c , t)) = Low⁼ (h c) t
  Low (nd (sΩ k) h) (inj₁ t) = Low⁼ k t

  Low⁼ : (a : L) (t : Pos⁼ a) → E.T → Br⁼ a t → Set
  Low⁼ a (inj₁ _) = R a
  Low⁼ a (inj₂ p) = Low a p

module Gen (s : Sh) (h : Ch s → L) = H.Gen {Sig (nd s h)} {Low (nd s h)}
  {λ c → R (h c)} {λ p → Lab (at (nd s h) p)}
```

## 公共运算

```agda
weakᴿ : ∀ ℓ {t x y} → R ℓ t x → ℓ ⊢ x ◃ y → R ℓ t y
weakᴿ zero = H.mw
weakᴿ (nd s h) = H.mw

weakenᴿ : ∀ ℓ {t x y} → R ℓ t x → x ⊴ y → R ℓ t y
weakenᴿ ℓ m ⊴r = m
weakenᴿ ℓ m (⊴◃ d) = weakᴿ ℓ m d

closeᴿ : ∀ ℓ {s t x} → s ≤ᵀ t → R ℓ t x → R ℓ s x
closeᴿ zero = H.mc
closeᴿ (nd s h) = H.mc

limᴿ : ∀ ℓ {t x} → E.cof t ≡ E.cω → (∀ n → R ℓ (E.fsn t n) x) → R ℓ t x
limᴿ zero = H.mL
limᴿ (nd s h) = H.mL

nextᴿ : ∀ ℓ {t p} (β : Tr⁺ ℓ) → E.cof t ≡ E.cω
  → (∀ n → E.fsn t n ≡ replicate n p)
  → R ℓ (p ∷ []) (proj₁ β) → R ℓ t (proj₁ (next⁺ β))
nextᴿ zero = H.G⁰.m-next
nextᴿ (nd s h) = Gen.m-next s h

cumᴿ : ∀ ℓ {t} (F : ℕ → Tr⁺ ℓ) (n : ℕ)
  → R ℓ t (proj₁ (F n)) → R ℓ t (proj₁ (limc⁺ F))
cumᴿ zero = H.G⁰.m-cum
cumᴿ (nd s h) = Gen.m-cum s h

zlᴿ : ∀ ℓ {S : Sg} (F : T S → Tr ℓ)
  → (∀ {x y} → Lt S x y → ℓ ⊢ F x ◃ F y)
  → ∀ {t} → R ℓ t (F zero) → ∀ x → R ℓ t (F x)
zlᴿ zero = H.G⁰.m-zl
zlᴿ (nd s h) = Gen.m-zl s h

nodeᴿ : ∀ ℓ (p : Pos ℓ) {t κ} {g : Br ℓ p → Tr ℓ}
  → E.cof t ≡ E.cΩ κ → Lab (at ℓ p) κ
  → (∀ η c → Low ℓ p η c → R ℓ (E.fsT t η) (g c))
  → R ℓ t (Ω p g)
nodeᴿ zero ()
nodeᴿ (nd s h) p = H.mΩ

emb-pres : ∀ ℓ (o : Ok ℓ) {k} (w : k ≤ ℓ) (y : Tr⁺ k) {a}
  → R k a (proj₁ y) → R ℓ a (proj₁ (emb ℓ o w y))
emb-pres ℓ o self y m = m
emb-pres (nd s h) o (inc c w) y m = H.mU H.mz (emb-pres (h c) (proj₂ o c) w y m)
emb-pres (nd s h) o (inu ws) y m = H.mU H.mz
  (emb-pres (h (c₀ s)) (proj₂ o (c₀ s)) (ws (c₀ s)) y m)
emb-pres (nd (sΩ k) h) o (ink w) y m = H.mU H.mz
  (emb-pres (h zero) (proj₂ o zero) (w ∙ proj₂ (proj₁ o) zero) y m)

nextψ : ∀ ℓ ν t a → E.cof a ≡ E.c1 → (β : Tr⁺ ℓ)
  → R ℓ (E.ψ ν (t ++ E.pred a) ∷ []) (proj₁ β)
  → R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (next⁺ β))
nextψ ℓ ν t a e β m = nextᴿ ℓ β (cofψ1 ν (t ++ a) (cof++1 t a e))
  (λ n → trans (fsnψ1 ν (t ++ a) n (cof++1 t a e))
    (cong (λ z → replicate n (E.ψ ν z)) (pred++ t a e))) m

limψ : ∀ ℓ ν t a → E.cof a ≡ E.cω → (x : Tr ℓ)
  → (∀ n → R ℓ (E.ψ ν (t ++ E.fsn a n) ∷ []) x)
  → R ℓ (E.ψ ν (t ++ a) ∷ []) x
limψ ℓ ν t a e x m = limᴿ ℓ (cofψω ν (t ++ a) (cof++ω t a e))
  (λ n → subst (λ z → R ℓ z x)
    (sym (trans (fsnψω ν (t ++ a) n (cof++ω t a e))
      (cong (λ z → E.ψ ν z ∷ []) (fsn++ t a n e)))) (m n))

nodeψ : ∀ ℓ ν t a (p : Pos ℓ) {κ} {g : Br ℓ p → Tr ℓ}
  → E.cof a ≡ E.cΩ κ → Pen (E.cmpᵀ (E.sucT κ) ν) → Lab (at ℓ p) κ
  → (∀ η c → Low ℓ p η c → R ℓ (E.ψ ν (t ++ E.fsT a η) ∷ []) (g c))
  → R ℓ (E.ψ ν (t ++ a) ∷ []) (Ω p g)
nodeψ ℓ ν t a p e pen nu m = nodeᴿ ℓ p (cofK ν (t ++ a) pen (cof++Ω t a e)) nu
  (λ η c l → subst (λ z → R ℓ z _)
    (sym (trans (fsTK ν (t ++ a) η pen (cof++Ω t a e))
      (cong (λ z → E.ψ ν z ∷ []) (fsT++ t a η e)))) (m η c l))
```

## 槽位换型, 前缀与步进

```agda
mutual
  low-from : ∀ ℓ (p : Pos ℓ) {η} {x : Tr (at ℓ p)}
    → R (at ℓ p) η x → Low ℓ p η (fromBr ℓ p x)
  low-from (nd s h) (inj₂ (c , q)) m = low-from⁼ (h c) q m
  low-from (nd (sΩ k) h) (inj₁ q) m = low-from⁼ k q m

  low-from⁼ : ∀ a (q : Pos⁼ a) {η} {x : Tr (proj₁ (sl⁼ a q))}
    → R (proj₁ (sl⁼ a q)) η x → Low⁼ a q η (proj₂ (sl⁼ a q) x)
  low-from⁼ a (inj₁ _) m = m
  low-from⁼ a (inj₂ p) m = low-from a p m

PrefixU : ∀ {ℓ} → Base ℓ → E.T → Set
PrefixU {ℓ} B t = (p : Pos ℓ) (ν : E.T) → Lab (at ℓ p) ν
  → R (at ℓ p) (E.ψ ν t ∷ []) (proj₁ (B (at ℓ p) (posW ℓ p)))

StepU′ : L → Set
StepU′ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t
  → (a : E.T) (p : Pos ℓ) (ν : E.T) → Lab (at ℓ p) ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) (n : ℕ) (c : Br ℓ p)
  → Low ℓ p (E.γT (t ++ a) ν n) c
  → R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)
```
