# 全部 $\theta$ 的证书: 有限模式与 $\theta=3$ (底座)

> 底座, 不含记号. 结论写在 [InaccTheta](InaccTheta.lagda.md). 目标是自然数的模式 `fin` 对**任何** `S`, 任何层号都 `OK`: `finD` 是语义正确的 (`fin-cv`). 所以节点层是自然数的层号 (`FinAt`) 全部无条件. `Cert` 是目标 1 的证书定理, `F 3` 是它的实例.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.InaccThetaFin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; fin; upM; verdict; chM; natL; isN; finD; asN)
open import OCF.Align.InaccFloorBase using (Aℓ)
open import OCF.Align.InaccThetaObs using (BL; b0; b1)
open import OCF.Align.InaccThetaClose using (module Close)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; zero; suc; lim)

module Fin (S : Sib) (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) (B₀ : Ordᴸ zero → Set) (a⊆b : ∀ x → Aℓ ℓ zero x → B₀ x) where
  open Close S ℓ one B₀ a⊆b public

  isN-nn : ∀ n {j} → natL n ≈ᴮ j → isN j n ≡ nothing → ⊥
  isN-nn zero z≈ ()
  isN-nn (suc n) (s≈ {b = j} e) eq with isN j n | isN-nn n e
  isN-nn (suc n) (s≈ {b = _} e) () | just refl | _
  ... | nothing | k = k refl

  fin-cv : ∀ j n → CV (finD j n)
  fin-cv j zero = cvr (λ ())
  fin-cv j (suc n) with isN j n in eq
  ... | just refl = cvp (inj₁ tt) refl tt
  ... | nothing with finD j n | fin-cv j n
  ...   | _ | cvp r e a = cvp (inj₂ r) e a
  ...   | _ | cvr k = cvr λ { (inj₁ _) _ q → isN-nn n q eq ; (inj₂ r) d q → k r d q }

  okF : ∀ k {i} n (e : i ≡ natL n) → OK k (fin n e)
  okF zero       n refl = tt
  okF (suc k)    n refl = (λ r d → fin-cv _ n) , okF k n refl
  okF (lim f)    n refl = (λ r d → fin-cv _ n) , (λ m → okF (f m) n refl)
  okF (limᴼ k g) n refl = (λ r d → fin-cv _ n) , (λ x _ → okF (g x) n refl)

  asN-nat : ∀ n → asN (natL n) ≡ just (n , refl)
  asN-nat zero    = refl
  asN-nat (suc n) rewrite asN-nat n = refl

  asN-no : ∀ j n → j ≡ natL n → asN j ≡ nothing → ⊥
  asN-no _ n refl eq with () ← trans (sym (asN-nat n)) eq

  okCh : ∀ k r n → at k r ≡ natL n → OK k (chM k r)
  okCh k r n e with asN (at k r) in eq
  ... | just (m , e′) = okF k m e′
  ... | nothing = ⊥-elim (asN-no _ n e eq)

  zt-nat : ∀ n → Zt (natL (suc n))
  zt-nat n = go n , zpI where
    go : ∀ n → Σ (Pre (natL (suc n))) λ r → AdmB (natL (suc n)) r × at (natL (suc n)) r ≡ zero
    go zero    = inj₁ tt , tt , refl
    go (suc n) with go n
    ... | r , d , e = inj₂ r , d , e

  ch-fin : ∀ k r n → at k r ≡ natL n → ChOK k r
  ch-fin k r zero    e = inj₁ e
  ch-fin k r (suc n) e = inj₂ (okCh k r (suc n) e , subst Zt (sym e) (zt-nat n))
```

## §1 节点层都是自然数的层号

`FinAt` 只看全部原始路径. 它包括 $n$, $\omega$, 以及分支值都是这种层号的 `limᴼ`. 这个类里 `S` 从来不被问到: 所有链的目标都是自然数, `chM` 走 `fin`.

```agda
  FinAt : Lv → Set
  FinAt i = ∀ r → Σ ℕ λ n → at i r ≡ natL n

  lvt-fin : ∀ i → FinAt i → LvT i
  lvt-fin zero       h = tt
  lvt-fin (suc k)    h =
    (λ r _ → ch-fin (suc k) r (proj₁ (h r)) (proj₂ (h r))) , lvt-fin k (λ r → h (inj₂ r))
  lvt-fin (lim f)    h =
    (λ r _ → ch-fin (lim f) r (proj₁ (h r)) (proj₂ (h r))) , (λ n → lvt-fin (f n) (λ r → h (n , r)))
  lvt-fin (limᴼ k g) h =
    (λ r _ → ch-fin (limᴼ k g) r (proj₁ (h r)) (proj₂ (h r))) ,
    lvt-fin k (λ r → h (inj₁ (inj₂ r))) ,
    (λ x _ → lvt-fin (g x) (λ r → h (inj₂ (x , r))))

  fin-nat : ∀ n → FinAt (natL n)
  fin-nat (suc n) (inj₁ _) = n , refl
  fin-nat (suc n) (inj₂ r) = fin-nat n r

  lvr-nat : ∀ n → LvR (natL n)
  lvr-nat zero    = tt
  lvr-nat (suc n) = lvr-nat n

  glv-nat : ∀ n → GLv (natL n)
  glv-nat zero    = tt
  glv-nat (suc n) = glv-nat n

  lvp-nat : ∀ n → LvP (natL n)
  lvp-nat n = t→g _ (lvt-fin (natL n) (fin-nat n)) , lvr-nat n , glv-nat n
```

## §2 证书定理

```agda
  Ti₁ : Ti (natL 1)
  Ti₁ = lvt-fin (natL 1) (fin-nat 1) , zt-nat 0 , tt

  GΩ₁ : GoodT (natL 1) (Ω (natL 1))
  GΩ₁ = Good-Ω (natL 1) (lvp-nat 1)

  Good-F : ∀ θ → LvP θ → GoodT (natL 1) (F θ)
  Good-F θ p@(g , r , _) = Good-ψ (fin 1 refl) (okF θ 1 refl) Ti₁ GΩ₁ (Good-Ω θ p) (Ω-self θ g r)

  Cert : ∀ θ → LvP θ → WFᴬ (toLv (F θ))
  Cert θ p = wf b1 (Good-F θ p)

  cmp-F : ∀ θ → LvP θ → (p q : Pre (toLv (F θ))) → Adm _ p → Adm _ q → Tri (at (toLv (F θ)) p) (at (toLv (F θ)) q)
  cmp-F θ h = <-decᴬ (toLv (F θ)) (Cert θ h)

  -- θ = 3, 以及一切自然数
  Cert-n : ∀ n → WFᴬ (toLv (F (natL n)))
  Cert-n n = Cert (natL n) (lvp-nat n)

  Cert₃ : WFᴬ (toLv (F (natL 3)))
  Cert₃ = Cert-n 3

  -- θ = ω
  Ωω : Lv
  Ωω = lim natL
```
