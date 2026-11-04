> **机械克隆, 验收用.** 把 `LadderLabZGoodLBase`, `LadderLabZDecoupleBase`, `LadderLabZPrefix` 里类型提到 `NF₁` 的几个定义搬到新的 `NF₁` 上, 代码逐字. `Survey/scripts/embvv/mk_world.py`. 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVLZExtra where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)
import OCF.Align.EBO as E
open E using (T; PT; c0; c1; cω; cΩ; cof; cofA; cofψ0; cofψ₊; fsn; fsT; cmpᵀ; lt; eq; gt; sucT; Ωt; natT; _<ᵀ_; hd<; tl<; lv<; ar<; []<) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt; rep<)
open import OCF.Align.Stage2 using (ctx)
open import OCF.Align.Symbolic using (X₂ᵗ)
open import OCF.Align.Standard using (Ctbl; c[]; c∷; Ctbl-pred; []≤) renaming (d₀ to d₀ᴰ)
open import OCF.Align.Closure using (lt→<ᴾ; eq→≡ᴾ; <ᵀ-trans)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Align.LadderLabZGoodLBase using (ctbl-hd; ctbl-one)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; n[]; n∷; nψ; NF₁-fsn; fsT-mono₁; γ-mono₁; γ′-NF; diag₁-desc-NF; walkD; Vis₁; vh; vd; vs; vt)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ; γP)
open import OCF.Align.LadderLabZPrefix using (toX₂)

fs-mono₁ : ∀ {u} → NF₁ u → cof u ≡ cω → ∀ n → fsn u n <ᵀ fsn u (suc n)
fs-monoL : ∀ {w ws} → NF₁ (w ∷ ws) → ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω →
           ∀ n → fsn (Ωt (w ∷ ws)) n <ᵀ fsn (Ωt (w ∷ ws)) (suc n)
fs-monoA : ∀ {w y ys} → NF₁ (y ∷ ys) → ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω →
           ∀ n → fsn (ψᵗ w (y ∷ ys) ∷ []) n <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) (suc n)

fs-mono₁ n[] () n
fs-mono₁ (n∷ nx (n∷ ny nys hy) hx) e n = tl< (fs-mono₁ (n∷ ny nys hy) e n)
fs-mono₁ (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () n
fs-mono₁ (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e n = fs-monoL nw (cof (w ∷ ws)) refl e n
fs-mono₁ (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e n = fs-monoA na (cof (y ∷ ys)) refl e n

fs-monoL nw c0 ke () n
fs-monoL nw c1 ke () n
fs-monoL {w} {ws} nw cω ke e n =
  subst₂ _<ᵀ_ (sym (E.fsn0-eq w ws n ke)) (sym (E.fsn0-eq w ws (suc n) ke)) (hd< (lv< (fs-mono₁ nw ke n)))
fs-monoL nw (cΩ μ) ke () n

fs-monoA nb c0 ke e n = ⊥-elim (cof-ne _ _ ke)
fs-monoA {w} {y} {ys} nb c1 ke e n =
  subst₂ _<ᵀ_ (sym (fs-rep w y ys ke n)) (sym (fs-rep w y ys ke (suc n))) (rep< _ n)
fs-monoA {w} {y} {ys} nb cω ke e n =
  subst₂ _<ᵀ_ (sym (fs-ω w y ys ke n)) (sym (fs-ω w y ys ke (suc n))) (hd< (ar< (fs-mono₁ nb ke n)))
fs-monoA {w} {y} {ys} nb (cΩ ν) ke e n = go (cmpᵀ (sucT ν) w) refl e
  where
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω →
       fsn (ψᵗ w (y ∷ ys) ∷ []) n <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) (suc n)
  go lt em ()
  go eq em ()
  go gt em _ = subst₂ _<ᵀ_ (sym (fs-gt w y ys ν ke em n)) (sym (fs-gt w y ys ν ke em (suc n)))
                      (hd< (ar< (fsT-mono₁ nb ke (γ-mono₁ nb ke n))))

Ctbl-ω : ∀ {u} → NF₁ u → cof u ≡ cω → Ctbl (fsn u 1) → Ctbl u
Ctbl-ω n[] () c
Ctbl-ω (n∷ nx (n∷ ny nys hy) hx) e (c∷ ct) = c∷ (Ctbl-ω (n∷ ny nys hy) e ct)
Ctbl-ω (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () c
Ctbl-ω (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e c = go (cof (w ∷ ws)) refl e c
  where
  go : ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω → Ctbl (fsn (Ωt (w ∷ ws)) 1) → Ctbl (Ωt (w ∷ ws))
  go c0 ke () c
  go c1 ke () c
  go (cΩ μ) ke () c
  go cω ke _ c with subst (_<ᵀ_ (fsn (w ∷ ws) 0)) (ctbl-hd (subst Ctbl (E.fsn0-eq w ws 1 ke) c)) (fs-mono₁ nw ke 0)
  ... | ()
Ctbl-ω (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e c = go (cof (y ∷ ys)) refl e c
  where
  go : ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω → Ctbl (fsn (ψᵗ w (y ∷ ys) ∷ []) 1) → Ctbl (ψᵗ w (y ∷ ys) ∷ [])
  go c0 ke _ c = ⊥-elim (cof-ne y ys ke)
  go c1 ke _ c = ctbl-one (ctbl-hd (subst Ctbl (fs-rep w y ys ke 1) c))
  go cω ke _ c = ctbl-one (ctbl-hd (subst Ctbl (fs-ω w y ys ke 1) c))
  go (cΩ ν) ke e′ c = gc′ (cmpᵀ (sucT ν) w) refl e′
    where
    gc′ : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω → Ctbl (ψᵗ w (y ∷ ys) ∷ [])
    gc′ lt em ()
    gc′ eq em ()
    gc′ gt em _ = ctbl-one (ctbl-hd (subst Ctbl (fs-gt w y ys ν ke em 1) c))

tailVis : ∀ {y e xs u} → TailOf (ψᵗ y e ∷ xs) u → Vis₁ [] e u
tailVis th = vt (vh ([]≤ _))
tailVis (ts t) = vt (tailVis t)

occVis : ∀ {y e xs t} → Occ (ψᵗ y e ∷ xs) t → Vis₁ [] e t
occVis oh     = vs ([]≤ _) (vh ([]≤ _))
occVis (od o) = vd ([]≤ _) (occVis o)
occVis (os o) = vs ([]≤ _) (occVis o)
occVis (oτ t) = vs ([]≤ _) (tailVis t)
occVis (ot o) = vt (occVis o)


tl<₁ : ∀ {x ts} → NF₁ (x ∷ ts) → ts <ᵀ x ∷ ts
tl<₁ (n∷ _ n[] _) = []<
tl<₁ {x} (n∷ _ (n∷ {x = y} ny nys hy) (inj₁ e)) = hd< (lt→<ᴾ y x e)
tl<₁ {x} (n∷ _ (n∷ {x = y} ny nys hy) (inj₂ e)) with eq→≡ᴾ y x e
... | refl = tl< (tl<₁ (n∷ ny nys hy))

occ< : ∀ {x t} → NF₁ t → Ctbl t → Occ x t → Ctbl x → x <ᵀ t
occ< nt (c∷ ct) oh cx = []<
occ< (n∷ (nψ _ _ na g) _ _) (c∷ ct) (od o) c[]      = []<
occ< (n∷ (nψ _ _ na g) _ _) (c∷ ct) (od o) (c∷ cx)  = hd< (ar< (g (occVis o)))
occ< nt (c∷ ct) (os ()) cx
occ< nt (c∷ ct) (oτ ()) cx
occ< (n∷ nx nts h) (c∷ ct) (ot o) cx = <ᵀ-trans (occ< nts ct o cx) (tl<₁ (n∷ nx nts h))

nf1 : NF₁ (natT 1)
nf1 = γ′-NF 0

nfγ : ∀ {y ys} → NF₁ (ctx (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cΩ []) → ∀ m → NF₁ (ctx (fsT (y ∷ ys) (γP (y ∷ ys) m)))
nfγ {y} {ys} nu c m = subst NF₁ (fs-gt [] ΩΩ (y ∷ ys) [] c refl m) (NF₁-fsn nu (cong (E.cofA []) c) m)

nfω : ∀ {y ys} → NF₁ (ctx (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cω) → ∀ m → NF₁ (ctx (fsn (y ∷ ys) m))
nfω {y} {ys} nu c m = subst NF₁ (fs-ω [] ΩΩ (y ∷ ys) c m) (NF₁-fsn nu (cong (E.cofA []) c) m)

X₂-NF : NF₁ X₂ᵗ
X₂-NF = diag₁-desc-NF (walkD d₀ᴰ toX₂ (refl , refl , refl , refl , refl , refl , tt))
```
