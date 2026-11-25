# 新块的 View：部分良基与对象步进
> 成品候选。来源：`YiLPWf`，旧层号的三种分支合并为 `nd s h`；零无前驱复用 `YiRWCheck.¬◃z`。
> 编译定理 `parts⊆`、`wf`、`vrec`、`objStep`：View 的部分可良基递归，ℕ 极限相邻项沿对象自身的第一位置步进。
> `Pt` 包含额外部分用于证明良基；不改树、折叠或合法性，不作强度验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVWWf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (zl)
open import OCF.Lean.YiRWCheck using (¬◃z)
open import OCF.Lean.YiVWVal
open import OCF.Lean.YiVWView
open import OCF.Align.BrwViewDef using (vz; vs; vl; vΩ)

Part : ∀ {ℓ v} → VW ℓ v → Tr ℓ → Set
Part (vz _)           t = ⊥
Part (vs y _ _)       t = t ≡ y
Part (vl f _ _ _)     t = Σ ℕ λ n → t ≡ f n
Part {ℓ} (vΩ p g _ _) t = Σ (Br ℓ p) λ z → t ≡ g z

data Pt : (ℓ : L) → Tr ℓ → Tr ℓ → Set where
  ps : ∀ {ℓ x} → Pt ℓ x (suc x)
  pl : ∀ {ℓ f a} (n : ℕ) → Pt ℓ (f n) (lim f a)
  pw : ∀ {ℓ p g} (z : Br ℓ p) → Pt ℓ (g z) (Ω p g)
  pz : ∀ {ℓ x c y e t} → Pt ℓ t x → Pt ℓ t (up x c y e)
  pu : ∀ {ℓ x c y e y′} → Pt (chL ℓ c) y′ (chT ℓ c y) → Pt ℓ (upz ℓ c x y′) (up x c y e)

part-reidx : ∀ {ℓ} {w w′ : V ℓ} (e : w′ ≈ w) (u : VW ℓ w) {t : Tr ℓ} → Part (reidx e u) t → Part u t
part-reidx e (vz _)       q = q
part-reidx e (vs _ _ _)   q = q
part-reidx e (vl _ _ _ _) q = q
part-reidx e (vΩ _ _ _ _) q = q

part-mapUp : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (vx : VW ℓ (val ℓ x)) {v : V (chL ℓ c)}
  (w : VW (chL ℓ c) v) {t : Tr ℓ} → Part (mapUp ℓ c x vx w) t
  → Part vx t ⊎ Σ (Tr (chL ℓ c)) λ y′ → Part w y′ × (t ≡ upz ℓ c x y′)
part-mapUp ℓ c x vx (vz e)       q          = inj₁ (part-reidx _ vx q)
part-mapUp ℓ c x vx (vs y _ _)   refl       = inj₂ (y , refl , refl)
part-mapUp ℓ c x vx (vl f _ _ _) (n , refl) = inj₂ (f n , (n , refl) , refl)
part-mapUp ℓ c x vx (vΩ p g _ _) (z , refl) = inj₂ (g (chBr ℓ c p z) , (chBr ℓ c p z , refl) , refl)

parts⊆ : (ℓ : L) (x : Tr ℓ) {t : Tr ℓ} → Part (view ℓ x) t → Pt ℓ t x
parts⊆ ℓ zero      ()
parts⊆ ℓ (suc x)   refl       = ps
parts⊆ ℓ (lim f a) (n , refl) = pl n
parts⊆ ℓ (Ω p g)   (z , refl) = pw z
parts⊆ zero (up x () y e) q
parts⊆ (nd s h) (up x c y e) q with part-mapUp (nd s h) c x (view (nd s h) x) (view (h c) y) q
... | inj₁ q′               = pz (parts⊆ (nd s h) x q′)
... | inj₂ (y′ , q′ , refl) = pu (parts⊆ (h c) y q′)


data Acc (ℓ : L) (x : Tr ℓ) : Set where
  acc : (∀ {t} → Pt ℓ t x → Acc ℓ t) → Acc ℓ x

mutual
  accUp : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) → Acc ℓ x → (y : Tr (chL ℓ c)) (d : chL ℓ c ⊢ zero ◃ y)
        → Acc (chL ℓ c) y → Acc ℓ (up x c (chT⁻ ℓ c y) (conv₀ ℓ c d))
  accUp ℓ c x (acc ax) y d (acc ay) = acc λ where
    (pz q)             → ax q
    (pu {y′ = y′} q) → accUpz ℓ c x (acc ax) y′ (ay (subst (Pt (chL ℓ c) y′) (chT-β ℓ c y) q))

  accUpz : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) → Acc ℓ x → (y : Tr (chL ℓ c)) → Acc (chL ℓ c) y
         → Acc ℓ (upz ℓ c x y)
  accUpz ℓ c x ax y ay with zl y
  ... | inj₁ _ = ax
  ... | inj₂ d = accUp ℓ c x ax y d ay

wf : (ℓ : L) (x : Tr ℓ) → Acc ℓ x
wf ℓ zero      = acc λ ()
wf ℓ (suc x)   = acc λ where ps → wf ℓ x
wf ℓ (lim f a) = acc λ where (pl n) → wf ℓ (f n)
wf ℓ (Ω p g)   = acc λ where (pw z) → wf ℓ (g z)
wf zero     (up x () y e)
wf (nd s h) (up x c y e) = accUp (nd s h) c x (wf (nd s h) x) y e (wf (h c) y)

vrec : (ℓ : L) (P : Tr ℓ → Set)
     → ((x : Tr ℓ) → ((t : Tr ℓ) → Part (view ℓ x) t → P t) → P x)
     → (x : Tr ℓ) → P x
vrec ℓ P step x = go x (wf ℓ x)
  where
  go : (x : Tr ℓ) → Acc ℓ x → P x
  go x (acc ax) = step x (λ t q → go t (ax (parts⊆ ℓ x q)))

ObjStep : ∀ {ℓ v} → VW ℓ v → Set
ObjStep {ℓ} (vl f _ _ _) = (n : ℕ) → ℓ ⊢ f n ◃ f (suc n)
ObjStep (vz _)           = ⊤
ObjStep (vs _ _ _)       = ⊤
ObjStep (vΩ _ _ _ _)     = ⊤

upz-step : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (a b : Tr (chL ℓ c)) → chL ℓ c ⊢ a ◃ b
         → ℓ ⊢ upz ℓ c x a ◃ upz ℓ c x b
upz-step ℓ c x a b d with zl a | zl b
... | inj₁ refl | inj₁ refl = ⊥-elim (¬◃z d)
... | inj₁ refl | inj₂ db   = ◃u x c (chT⁻ ℓ c b) (conv₀ ℓ c db)
... | inj₂ da   | inj₁ refl = ⊥-elim (¬◃z d)
... | inj₂ da   | inj₂ db   = ◃c x c (conv ℓ c d)

os-reidx : ∀ {ℓ} {w w′ : V ℓ} (e : w′ ≈ w) (u : VW ℓ w) → ObjStep u → ObjStep (reidx e u)
os-reidx e (vz _)       o = o
os-reidx e (vs _ _ _)   o = o
os-reidx e (vl _ _ _ _) o = o
os-reidx e (vΩ _ _ _ _) o = o

os-mapUp : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (vx : VW ℓ (val ℓ x)) {v : V (chL ℓ c)}
  (w : VW (chL ℓ c) v) → ObjStep vx → ObjStep w → ObjStep (mapUp ℓ c x vx w)
os-mapUp ℓ c x vx (vz e)       ox ow = os-reidx _ vx ox
os-mapUp ℓ c x vx (vs _ _ _)   ox ow = tt
os-mapUp ℓ c x vx (vl f _ _ _) ox ow = λ n → upz-step ℓ c x (f n) (f (suc n)) (ow n)
os-mapUp ℓ c x vx (vΩ _ _ _ _) ox ow = tt

objStep : (ℓ : L) (x : Tr ℓ) → ObjStep (view ℓ x)
objStep ℓ zero      = tt
objStep ℓ (suc x)   = tt
objStep ℓ (lim f a) = a
objStep ℓ (Ω p g)   = tt
objStep zero (up x () y e)
objStep (nd s h) (up x c y e) = os-mapUp (nd s h) c x (view (nd s h) x) (view (h c) y) (objStep (nd s h) x) (objStep (h c) y)
```
