# 分层的 $\approx$: 好层号的闭包 (底座)

> 底座, 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). 由 [LevelKLvP](LevelKLvP.lagda.md) 改写. `lvp-cx`: 参数层全低且 `Cx` 的层号, 只要 `LvG` 就是好层号, 这里低层可以含 `limᴼ`. `Cert-top`: 字面目标的证书.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStratLvP where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; limᵢ; up; Ω; toLv; Sim; ι; _∘σ_)
open import OCF.Align.InaccFloorTree using (Sib; Mode; bel)
open import OCF.Align.LvStratBase using (Stage)
open import OCF.Align.LvStratFin using (module Fin)

module LvPs (S : Sib) (St : Stage) where
  open Fin S St public

  lvp-o : ∀ {k} {g : Ordᴸ k → Lv} → LvP (limᴼ k g) → ∀ x → A k x → LvP (g x)
  lvp-o {k} (lg , lr , _ , vg , _) x a =
    proj₂ (proj₂ lg) x (A⊆B k x a) , proj₁ (proj₂ lr) x (A⊆B k x a) , vg x (inj₁ a)

  Ω-path : ∀ θ′ (q : Pre θ′) → Adm θ′ q → WFᴬ θ′ → Lo θ′ → LvP θ′ → ∀ κ → LvP (suc κ) → κ ≈ᴮ at θ′ q → Ω (suc κ) ⊑ᵒ Ω θ′
  Ω-path (suc k) (inj₁ _) d w l (lg , lr , _) κ (lk , rk , _) e = ≃→⊑ᵒ (Ω≃ (s≈ e) lk lg rk)
  Ω-path (suc k) (inj₂ q) d w l ((_ , lt) , lr , v) κ pκ e =
    limᵢ-r tt (up-r (suc k) tt (Ω-path k q d w l (t→g k lt , lr , v) κ pκ e))
  Ω-path (lim f) (n , q) d (_ , w) l (lg , lr , v , _) κ pκ e =
    lim-r n (up-r (lim f) tt (Ω-path (f n) q d (w n) (l n) (lg n , lr n , v n) κ pκ e))
  Ω-path (limᴼ j g) q d w@(dir , par , her) l p κ pκ e with branchᴬ {k = j} {g = g} par q d
  ... | x , ax , viaᴬ q′ d′ e′ =
    limᵢ-r₀ tt (proj₁ l) x ax
      (up-r (limᴼ j g) (A⊆B j x ax) (Ω-path (g x) q′ d′ (her x ax) (proj₂ l x ax) (lvp-o p x ax) κ pκ (≈ᴮ-trans e e′)))

  Ω-mono : ∀ θ θ′ → WFᴬ θ → WFᴬ θ′ → Lo θ → Lo θ′ → LvP θ → LvP θ′ → θ ⊑ᴬ θ′ → Ω θ ⊑ᵒ Ω θ′
  Ω-mono zero θ′ w w′ l l′ p p′ σ = Ω0 θ′
  Ω-mono (suc κ) θ′ w w′ l l′ p p′ σ with σ (inj₁ tt) tt
  ... | viaᴬ q d e = Ω-path θ′ q d w′ l′ p′ κ p e
  Ω-mono (lim h) θ′ (_ , w) w′ l l′ (lg , lr , v , _) p′ σ =
    lim-l (λ n → up-l (lim h) tt (Ω-mono (h n) θ′ (w n) w′ (l n) l′ (lg n , lr n , v n) p′ (λ r d → σ (n , r) d)))
  Ω-mono (limᴼ j g) θ′ (_ , _ , her) w′ l l′ p p′ σ =
    limᵢ-l (Ω-self θ′ (proj₁ p′) (proj₁ (proj₂ p′))) tt (proj₁ l)
      (λ z az → up-l (limᴼ j g) (A⊆B j z az)
                  (Ω-mono (g z) θ′ (her z az) w′ (proj₂ l z az) l′ (lvp-o p z az) p′ (λ r d → σ (inj₂ (z , r)) (az , d))))
      (λ _ → zy (σ (inj₁ (inj₁ tt)) tt))
    where
    zy : j ≺ᴬ θ′ → j ≺ᴬ toLv (Ω θ′)
    zy (viaᴬ q d e) = ≺ᴬ-respˡ e (path→Ω θ′ q d)

  lvg-low : ∀ j → Lw j → LvG j
  lvg-low j l = t→g j (low→lvt j l)

  lvp-low : ∀ j → Lw j → LvP j
  lvp-cx : ∀ a → Lo a → Cx a → LvG a → LvP a

  lvp-low j l = lvp-cx j (low-lo j l) (low-cx j l) (lvg-low j l)

  lvp-cx zero l c g = tt , tt , tt
  lvp-cx (suc k) l c g =
    let _ , r , v = lvp-cx k l c (t→g k (proj₂ g)) in g , r , v
  lvp-cx (lim f) l c g =
    let P = λ n → lvp-cx (f n) (l n) (cxL c n) (g n)
    in g , (λ n → proj₁ (proj₂ (P n))) , (λ n → proj₂ (proj₂ (P n))) ,
       (λ n → Ω-mono (f n) (f (suc n)) (proj₂ (proj₁ c) n) (proj₂ (proj₁ c) (suc n)) (l n) (l (suc n)) (P n) (P (suc n))
                (proj₁ (proj₁ c) n))
  lvp-cx (limᴼ k h) (lk , lh) c g =
    let P = λ z (az : A k z) → lvp-cx (h z) (lh z az) (cxB c z az) (proj₂ (proj₂ g) z (A⊆B k z az))
        bl = lw→bl lk
    in g ,
       lvr-rp (limᴼ k h) (lk , lh) (proj₁ (proj₂ c)) ,
       proj₂ (proj₂ (lvp-low k lk)) ,
       (λ z d → proj₂ (proj₂ (P z (Gi→A k lk d)))) ,
       (λ z z′ d d′ p →
          let az = Gi→A k lk d ; az′ = Gi→A k lk d′ in
          Ω-mono (h z) (h z′) (proj₁ (cxB c z az)) (proj₁ (cxB c z′ az′)) (lh z az) (lh z′ az′) (P z az) (P z′ az′)
            (proj₂ (proj₂ (proj₂ c)) z z′ az az′ (p (idO {b = bl} {b′ = bl})))) ,
       (λ _ → par-Ω (proj₁ (proj₂ (proj₁ c))))
    where
    par-Ω : (Σ (Ordᴸ k) λ x₀ → A k x₀ × k ≺ᴬ h x₀ × k ⊑ᴬ h x₀) → Σ (Ordᴸ k) λ x₀ → A k x₀ × k ≺ᴬ toLv (Ω (h x₀))
    par-Ω (x₀ , ax , viaᴬ q dq e , _) = x₀ , ax , ≺ᴬ-respˡ e (path→Ω (h x₀) q dq)

  -- 字面目标: 任何 `BL` 的目标, 含 `limᴼ` 的也行
  Cert-top : ∀ {θ L} (m : Mode θ L) → BL L → Ti L → LvP L → OK θ m → LvP θ → WFᴬ (toLv (ψᵖ m (Ω θ)))
  Cert-top {θ} {L} m b ti pL ok p@(g , r , _) = wf b (Good-ψ m ok ti (Good-Ω L pL) (Good-Ω θ p) (Ω-self θ g r))

  -- `bel`: 树层在目标之下, 判决不被问到
  okB : ∀ k {i} (σ : Sim k i) → SD σ → OK k (bel σ)
  okB zero σ s = tt
  okB (suc k) σ s = (λ r d → cvp (proj₁ (σ r)) (proj₂ (σ r)) (s r d)) , okB k (_∘σ_ {b = suc k} σ (ι (suc k) tt)) (sd∘ι (suc k) tt σ s tt)
  okB (lim f) σ s =
    (λ r d → cvp (proj₁ (σ r)) (proj₂ (σ r)) (s r d)) , (λ n → okB (f n) (_∘σ_ {b = lim f} σ (ι (lim f) n)) (sd∘ι (lim f) n σ s tt))
  okB (limᴼ k g) σ s =
    (λ r d → cvp (proj₁ (σ r)) (proj₂ (σ r)) (s r d)) , (λ x b → okB (g x) (_∘σ_ {b = limᴼ k g} σ (ι (limᴼ k g) x)) (sd∘ι (limᴼ k g) x σ s b))
```
