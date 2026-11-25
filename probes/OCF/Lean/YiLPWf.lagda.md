# 合法块的 View: 部分良基, 对象层的步进

> 判决: 成品候选. 编译定理, 无前提: View 的部分都在部分关系 `Pt` 里 (`parts⊆`), `Pt` 在每层良基 (`wf`), 所以沿 View 可以像布劳威尔树一样递归 (`vrec`); View 的 ℕ 极限的相邻项在树自己的第一位置序里也步进 (`objStep`).
> 与 `YiViewWf` 同文, 合法性一律是 `⊤`; `upz` 的两种情形由 `zl` 分开.
> 不否定什么. `Pt` 比 View 的部分多 (含 x 的部分), 只用于良基.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPWf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (zl; ¬◃z; chP; chBr)
open import OCF.Lean.YiLPVal
open import OCF.Lean.YiLPView
open import OCF.Align.BrwViewDef using (vz; vs; vl; vΩ)
```

## 部分

```agda
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

part-mapUp : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (vx : VW ℓ (val ℓ x)) {v : V (chL ℓ c)}
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
parts⊆ (suc a) (up x c y e) q with part-mapUp (suc a) c x (view (suc a) x) (view a y) q
... | inj₁ q′               = pz (parts⊆ (suc a) x q′)
... | inj₂ (y′ , q′ , refl) = pu (parts⊆ a y q′)
parts⊆ (lim g) (up x n y e) q with part-mapUp (lim g) n x (view (lim g) x) (view (g n) y) q
... | inj₁ q′               = pz (parts⊆ (lim g) x q′)
... | inj₂ (y′ , q′ , refl) = pu (parts⊆ (g n) y q′)
parts⊆ (Ωₗ k h) (up x c y e) q with part-mapUp (Ωₗ k h) c x (view (Ωₗ k h) x) (view (h c) y) q
... | inj₁ q′               = pz (parts⊆ (Ωₗ k h) x q′)
... | inj₂ (y′ , q′ , refl) = pu (parts⊆ (h c) y q′)
```

## 良基

```agda
data Acc (ℓ : L) (x : Tr ℓ) : Set where
  acc : (∀ {t} → Pt ℓ t x → Acc ℓ t) → Acc ℓ x

mutual
  accUp : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) → Acc ℓ x → (y : Tr (chL ℓ c)) (d : chL ℓ c ⊢ zero ◃ y)
        → Acc (chL ℓ c) y → Acc ℓ (up x c (chT⁻ ℓ c y) (conv₀ ℓ c d))
  accUp ℓ c x (acc ax) y d (acc ay) = acc λ where
    (pz q)             → ax q
    (pu {y′ = y′} q) → accUpz ℓ c x (acc ax) y′ (ay (subst (Pt (chL ℓ c) y′) (chT-β ℓ c y) q))

  accUpz : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) → Acc ℓ x → (y : Tr (chL ℓ c)) → Acc (chL ℓ c) y
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
wf (suc a)  (up x c y e) = accUp (suc a) c x (wf (suc a) x) y e (wf a y)
wf (lim g)  (up x n y e) = accUp (lim g) n x (wf (lim g) x) y e (wf (g n) y)
wf (Ωₗ k h) (up x c y e) = accUp (Ωₗ k h) c x (wf (Ωₗ k h) x) y e (wf (h c) y)
```

沿 View 递归: 只要对每个对象, 由它的部分上的值给出它的值.

```agda
vrec : (ℓ : L) (P : Tr ℓ → Set)
     → ((x : Tr ℓ) → ((t : Tr ℓ) → Part (view ℓ x) t → P t) → P x)
     → (x : Tr ℓ) → P x
vrec ℓ P step x = go x (wf ℓ x)
  where
  go : (x : Tr ℓ) → Acc ℓ x → P x
  go x (acc ax) = step x (λ t q → go t (ax (parts⊆ ℓ x q)))
```

## 对象层的步进

```agda
ObjStep : ∀ {ℓ v} → VW ℓ v → Set
ObjStep {ℓ} (vl f _ _ _) = (n : ℕ) → ℓ ⊢ f n ◃ f (suc n)
ObjStep (vz _)           = ⊤
ObjStep (vs _ _ _)       = ⊤
ObjStep (vΩ _ _ _ _)     = ⊤

upz-step : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (a b : Tr (chL ℓ c)) → chL ℓ c ⊢ a ◃ b
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

os-mapUp : (ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (vx : VW ℓ (val ℓ x)) {v : V (chL ℓ c)}
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
objStep (suc a)  (up x c y e) = os-mapUp (suc a) c x (view (suc a) x) (view a y) (objStep (suc a) x) (objStep a y)
objStep (lim g)  (up x n y e) = os-mapUp (lim g) n x (view (lim g) x) (view (g n) y) (objStep (lim g) x) (objStep (g n) y)
objStep (Ωₗ k h) (up x c y e) = os-mapUp (Ωₗ k h) c x (view (Ωₗ k h) x) (view (h c) y) (objStep (Ωₗ k h) x) (objStep (h c) y)
```
