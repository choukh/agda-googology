# 内部 View: 部分良基, 对象层的步进

> 判决: 成品候选. 编译定理: View 的部分都在 "部分" 关系 `Pt` 里 (`parts⊆`), `Pt` 在每层良基 (`wf`, 无前提), 所以沿 View 可以像布劳威尔树一样递归 (`vrec`);
> View 的 ℕ 极限的相邻项在树自己的第一位置序 `_⊢_◃_` 里也步进 (`objStep`, 无前提).
> 不否定什么. `Pt` 比 View 的部分多 (含 x 的部分), 只用于良基.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiViewWf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃u; ◃c; ◃t; Leg; zl)
open import OCF.Lean.YiUpBlock using (chP; chBr)
open import OCF.Lean.YiViewVal
open import OCF.Lean.YiViewInst
open import OCF.Align.BrwViewDef using (vz; vs; vl; vΩ)
```

## 部分

`Part w t`: t 是 View w 的一个部分 (Ω 极限取一切坐标). `Pt ℓ t x`: 树上的部分关系.

```agda
Part : ∀ {ℓ v} → VW ℓ v → Tr ℓ → Set
Part (vz _)               t = ⊥
Part (vs y _ _)           t = t ≡ y
Part (vl f _ _ _)         t = Σ ℕ λ n → t ≡ f n
Part {ℓ} (vΩ p g _ _)     t = Σ (Br ℓ p) λ z → t ≡ g z

data Pt : (ℓ : L) → Tr ℓ → Tr ℓ → Set where
  ps : ∀ {ℓ x} → Pt ℓ x (suc x)
  pl : ∀ {ℓ f} (n : ℕ) → Pt ℓ (f n) (lim f)
  pw : ∀ {ℓ p g} (z : Br ℓ p) → Pt ℓ (g z) (Ω p g)
  pz : ∀ {ℓ x c y t} → Pt ℓ t x → Pt ℓ t (up x c y)
  pu : ∀ {ℓ x c y y′} → Pt (chL ℓ c) y′ (chT ℓ c y) → Pt ℓ (upz ℓ c x y′) (up x c y)

part-reidx : ∀ {ℓ} {w w′ : V ℓ} (e : w′ ≈ w) (u : VW ℓ w) {t : Tr ℓ} → Part (reidx e u) t → Part u t
part-reidx e (vz _)       q = q
part-reidx e (vs _ _ _)   q = q
part-reidx e (vl _ _ _ _) q = q
part-reidx e (vΩ _ _ _ _) q = q

part-mapUp : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (hx : Leg ℓ x) (vx : VW ℓ (val ℓ x)) {v : V (chL ℓ c)}
  (w : VW (chL ℓ c) v) {t : Tr ℓ} → Part (mapUp ℓ c x hx vx w) t
  → Part vx t ⊎ Σ (Tr (chL ℓ c)) λ y′ → Part w y′ × (t ≡ upz ℓ c x y′)
part-mapUp ℓ c x hx vx (vz e)       q              = inj₁ (part-reidx _ vx q)
part-mapUp ℓ c x hx vx (vs y _ _)   refl           = inj₂ (y , refl , refl)
part-mapUp ℓ c x hx vx (vl f _ _ _) (n , refl)     = inj₂ (f n , (n , refl) , refl)
part-mapUp ℓ c x hx vx (vΩ p g _ _) (z , refl)     = inj₂ (g (chBr ℓ c p z) , (chBr ℓ c p z , refl) , refl)
```

View 的部分都在 `Pt` 里.

```agda
parts⊆ : (ℓ : L) (x : Tr ℓ) (h : Leg ℓ x) {t : Tr ℓ} → Part (view ℓ x h) t → Pt ℓ t x
parts⊆ ℓ zero    h ()
parts⊆ ℓ (suc x) h refl       = ps
parts⊆ ℓ (lim f) h (n , refl) = pl n
parts⊆ ℓ (Ω p g) h (z , refl) = pw z
parts⊆ zero (up x () y) h q
parts⊆ (suc a) (up x c y) (hx , hy , _) q
  with part-mapUp (suc a) c x hx (view (suc a) x hx) (view a y hy) q
... | inj₁ q′              = pz (parts⊆ (suc a) x hx q′)
... | inj₂ (y′ , q′ , refl) = pu (parts⊆ a y hy q′)
parts⊆ (lim g) (up x n y) (hx , hy , _) q
  with part-mapUp (lim g) n x hx (view (lim g) x hx) (view (g n) y hy) q
... | inj₁ q′              = pz (parts⊆ (lim g) x hx q′)
... | inj₂ (y′ , q′ , refl) = pu (parts⊆ (g n) y hy q′)
parts⊆ (Ωₗ k h) (up x c y) (hx , hy , _) q
  with part-mapUp (Ωₗ k h) c x hx (view (Ωₗ k h) x hx) (view (h c) y hy) q
... | inj₁ q′              = pz (parts⊆ (Ωₗ k h) x hx q′)
... | inj₂ (y′ , q′ , refl) = pu (parts⊆ (h c) y hy q′)
```

## 良基

```agda
data Acc (ℓ : L) (x : Tr ℓ) : Set where
  acc : (∀ {t} → Pt ℓ t x → Acc ℓ t) → Acc ℓ x

chT-β : (ℓ : L) (c : Ch ℓ) (y : Tr (chL ℓ c)) → chT ℓ c (chT⁻ ℓ c y) ≡ y
chT-β zero     () y
chT-β (suc a)  c y = refl
chT-β (lim g)  n y = refl
chT-β (Ωₗ k h) c y = refl

mutual
  accUp : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) → Acc ℓ x → (y : Tr (chL ℓ c)) → Acc (chL ℓ c) y
        → Acc ℓ (up x c (chT⁻ ℓ c y))
  accUp ℓ c x (acc ax) y (acc ay) = acc λ where
    (pz d)             → ax d
    (pu {y′ = y′} d) → accUpz ℓ c x (acc ax) y′ (ay (subst (Pt (chL ℓ c) y′) (chT-β ℓ c y) d))

  accUpz : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) → Acc ℓ x → (y : Tr (chL ℓ c)) → Acc (chL ℓ c) y
         → Acc ℓ (upz ℓ c x y)
  accUpz ℓ c x ax zero         ay = ax
  accUpz ℓ c x ax y@(suc _)    ay = accUp ℓ c x ax y ay
  accUpz ℓ c x ax y@(lim _)    ay = accUp ℓ c x ax y ay
  accUpz ℓ c x ax y@(Ω _ _)    ay = accUp ℓ c x ax y ay
  accUpz ℓ c x ax y@(up _ _ _) ay = accUp ℓ c x ax y ay

wf : (ℓ : L) (x : Tr ℓ) → Acc ℓ x
wf ℓ zero    = acc λ ()
wf ℓ (suc x) = acc λ where ps → wf ℓ x
wf ℓ (lim f) = acc λ where (pl n) → wf ℓ (f n)
wf ℓ (Ω p g) = acc λ where (pw z) → wf ℓ (g z)
wf zero     (up x () y)
wf (suc a)  (up x c y) = accUp (suc a) c x (wf (suc a) x) y (wf a y)
wf (lim g)  (up x n y) = accUp (lim g) n x (wf (lim g) x) y (wf (g n) y)
wf (Ωₗ k h) (up x c y) = accUp (Ωₗ k h) c x (wf (Ωₗ k h) x) y (wf (h c) y)
```

沿 View 递归: 只要对每个合法对象, 由它的合法部分上的值给出它的值.

```agda
vrec : (ℓ : L) (P : Tr ℓ → Set)
     → ((x : Tr ℓ) (h : Leg ℓ x) → ((t : Tr ℓ) → Part (view ℓ x h) t → Leg ℓ t → P t) → P x)
     → (x : Tr ℓ) → Leg ℓ x → P x
vrec ℓ P step x h = go x h (wf ℓ x)
  where
  go : (x : Tr ℓ) → Leg ℓ x → Acc ℓ x → P x
  go x h (acc ax) = step x h (λ t q ht → go t ht (ax (parts⊆ ℓ x h q)))
```

## 对象层的步进

```agda
ObjStep : ∀ {ℓ v} → VW ℓ v → Set
ObjStep {ℓ} (vl f _ _ _) = (n : ℕ) → ℓ ⊢ f n ◃ f (suc n)
ObjStep (vz _)           = ⊤
ObjStep (vs _ _ _)       = ⊤
ObjStep (vΩ _ _ _ _)     = ⊤

¬◃zero : ∀ {j} {a : Tr j} → j ⊢ a ◃ zero → ⊥
¬◃zero (◃t d e) = ¬◃zero e

upz-nz : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c)) → chL ℓ c ⊢ zero ◃ y
       → upz ℓ c x y ≡ up x c (chT⁻ ℓ c y)
upz-nz ℓ c x zero       d = ⊥-elim (¬◃zero d)
upz-nz ℓ c x (suc _)    d = refl
upz-nz ℓ c x (lim _)    d = refl
upz-nz ℓ c x (Ω _ _)    d = refl
upz-nz ℓ c x (up _ _ _) d = refl

conv◃ : (ℓ : L) (c : Ch ℓ) {a b : Tr (chL ℓ c)} → chL ℓ c ⊢ a ◃ b
      → chL ℓ c ⊢ chT ℓ c (chT⁻ ℓ c a) ◃ chT ℓ c (chT⁻ ℓ c b)
conv◃ zero     () d
conv◃ (suc a)  c d = d
conv◃ (lim g)  n d = d
conv◃ (Ωₗ k h) c d = d

upz-step : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (a b : Tr (chL ℓ c)) → Leg (chL ℓ c) a → chL ℓ c ⊢ a ◃ b
         → ℓ ⊢ upz ℓ c x a ◃ upz ℓ c x b
upz-step ℓ c x a b ha d with zl a ha
... | inj₁ refl = subst (λ t → ℓ ⊢ x ◃ t) (sym (upz-nz ℓ c x b d)) (◃u (nz◃ ℓ c b d))
... | inj₂ da   = subst₂ (λ s t → ℓ ⊢ s ◃ t) (sym (upz-nz ℓ c x a da)) (sym (upz-nz ℓ c x b (◃t da d)))
                    (◃c (conv◃ ℓ c d))

os-reidx : ∀ {ℓ} {w w′ : V ℓ} (e : w′ ≈ w) (u : VW ℓ w) → ObjStep u → ObjStep (reidx e u)
os-reidx e (vz _)       o = o
os-reidx e (vs _ _ _)   o = o
os-reidx e (vl _ _ _ _) o = o
os-reidx e (vΩ _ _ _ _) o = o

os-mapUp : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (hx : Leg ℓ x) (vx : VW ℓ (val ℓ x)) {v : V (chL ℓ c)}
  (w : VW (chL ℓ c) v) → ObjStep vx → ObjStep w → ObjStep (mapUp ℓ c x hx vx w)
os-mapUp ℓ c x hx vx (vz e)        ox ow = os-reidx _ vx ox
os-mapUp ℓ c x hx vx (vs _ _ _)    ox ow = tt
os-mapUp ℓ c x hx vx (vl f hf _ _) ox ow = λ n → upz-step ℓ c x (f n) (f (suc n)) (hf n) (ow n)
os-mapUp ℓ c x hx vx (vΩ _ _ _ _)  ox ow = tt

objStep : (ℓ : L) (x : Tr ℓ) (h : Leg ℓ x) → ObjStep (view ℓ x h)
objStep ℓ zero    h          = tt
objStep ℓ (suc x) h          = tt
objStep ℓ (lim f) (hf , adj) = adj
objStep ℓ (Ω p g) h          = tt
objStep zero (up x () y) h
objStep (suc a)  (up x c y) (hx , hy , _) =
  os-mapUp (suc a) c x hx (view (suc a) x hx) (view a y hy) (objStep (suc a) x hx) (objStep a y hy)
objStep (lim g)  (up x n y) (hx , hy , _) =
  os-mapUp (lim g) n x hx (view (lim g) x hx) (view (g n) y hy) (objStep (lim g) x hx) (objStep (g n) y hy)
objStep (Ωₗ k h) (up x c y) (hx , hy , _) =
  os-mapUp (Ωₗ k h) c x hx (view (Ωₗ k h) x hx) (view (h c) y hy) (objStep (Ωₗ k h) x hx) (objStep (h c) y hy)
```
