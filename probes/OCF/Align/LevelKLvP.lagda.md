# 证书与阶段无关: 好层号的闭包 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). `Ω-mono`: 参数层全低的两个层号, `⊑ᴬ` 给 $\Omega$ 的观测单调. 这是 [InaccThetaMono](InaccThetaMono.lagda.md) 的 `Ω-mono` 去掉 "只有 `limᴼ 0`" 的版本. `lvp-cx`: 参数层全低且 `Cx` 的层号, 只要 `LvG` 就是好层号. 所以 `limᴼ k` ($k$ 低) 现在可以作下标. 这里只剩 `LvG` 问判决, 而 `LvG` 的分支只在地板上: 这就是 `no-Ω₂` 的前提改变的地方.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKLvP where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; limᵢ; up; Ω; toLv)
open import OCF.Align.InaccFloorTree using (Sib)
open import OCF.Align.LevelKBase using (NoO; Stage)
open import OCF.Align.LevelKFin using (module Fin)

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
      (up-r (limᴼ j g) (A⊆B j x ax) (Ω-path (g x) q′ d′ (her x ax) (proj₂ l x) (lvp-o p x ax) κ pκ (≈ᴮ-trans e e′)))

  Ω-mono : ∀ θ θ′ → WFᴬ θ → WFᴬ θ′ → Lo θ → Lo θ′ → LvP θ → LvP θ′ → θ ⊑ᴬ θ′ → Ω θ ⊑ᵒ Ω θ′
  Ω-mono zero θ′ w w′ l l′ p p′ σ = Ω0 θ′
  Ω-mono (suc κ) θ′ w w′ l l′ p p′ σ with σ (inj₁ tt) tt
  ... | viaᴬ q d e = Ω-path θ′ q d w′ l′ p′ κ p e
  Ω-mono (lim h) θ′ (_ , w) w′ l l′ (lg , lr , v , _) p′ σ =
    lim-l (λ n → up-l (lim h) tt (Ω-mono (h n) θ′ (w n) w′ (l n) l′ (lg n , lr n , v n) p′ (λ r d → σ (n , r) d)))
  Ω-mono (limᴼ j g) θ′ (_ , _ , her) w′ l l′ p p′ σ =
    limᵢ-l tt (proj₁ l)
      (λ z az → up-l (limᴼ j g) (A⊆B j z az)
                  (Ω-mono (g z) θ′ (her z az) w′ (proj₂ l z) l′ (lvp-o p z az) p′ (λ r d → σ (inj₂ (z , r)) (az , d))))
      (λ _ → zy (σ (inj₁ (inj₁ tt)) tt))
    where
    zy : j ≺ᴬ θ′ → j ≺ᴬ toLv (Ω θ′)
    zy (viaᴬ q d e) = ≺ᴬ-respˡ e (path→Ω θ′ q d)

  -- 参数层全低: Rp 给 LvR
  lvr-rp : ∀ a → Lo a → Rp a → LvR a
  lvr-rp zero l r = tt
  lvr-rp (suc k) l r = lvr-rp k l r
  lvr-rp (lim f) l r = λ n → lvr-rp (f n) (l n) (r n)
  lvr-rp (limᴼ k g) (lk , lg) (rb , rr) =
    lvr-noo k (low-noo k lk) ,
    (λ x b → lvr-rp (g x) (lg x) (rb x b)) ,
    (λ z z′ bz bz′ → λ { (inj₁ e) → rr z z′ bz bz′ (b≃ (lw→bl lk) (lw→bl lk) e)
                        ; (inj₂ (_ , _ , t)) → rr z z′ bz bz′ t })

  lvg-low : ∀ j → Lw j → LvG j
  lvg-low j l = t→g j (low→lvt j l)

  lvp-low : ∀ j → Lw j → LvP j
  glv-low : ∀ j → Lw j → GLv j

  lvp-low j l = lvg-low j l , lvr-noo j (low-noo j l) , glv-low j l

  glv-low zero l = tt
  glv-low (suc j) l = glv-low j (low-at (suc j) l (inj₁ tt))
  glv-low (lim f) l =
    (λ n → glv-low (f n) (low-lim f n l)) ,
    (λ n → let ln  = low-lim f n l
               ln′ = low-lim f (suc n) l
           in Ω-mono (f n) (f (suc n)) (low-wf _ ln) (low-wf _ ln′) (lo-par ln) (lo-par ln′) (lvp-low _ ln) (lvp-low _ ln′)
                (proj₁ (low-wf (lim f) l) n))
  glv-low (limᴼ j g) l with low-noo _ l
  ... | ()

  lvp-cx : ∀ a → Lo a → Cx a → LvG a → LvP a
  lvp-cx zero l c g = tt , tt , tt
  lvp-cx (suc k) l c g =
    let _ , r , v = lvp-cx k l c (t→g k (proj₂ g)) in g , r , v
  lvp-cx (lim f) l c g =
    let P = λ n → lvp-cx (f n) (l n) (cxL c n) (g n)
    in g , (λ n → proj₁ (proj₂ (P n))) , (λ n → proj₂ (proj₂ (P n))) ,
       (λ n → Ω-mono (f n) (f (suc n)) (proj₂ (proj₁ c) n) (proj₂ (proj₁ c) (suc n)) (l n) (l (suc n)) (P n) (P (suc n))
                (proj₁ (proj₁ c) n))
  lvp-cx (limᴼ k h) (lk , lh) c g =
    let P = λ z (az : A k z) → lvp-cx (h z) (lh z) (cxB c z az) (proj₂ (proj₂ g) z (A⊆B k z az))
        bl = lw→bl lk
    in g ,
       lvr-rp (limᴼ k h) (lk , lh) (proj₁ (proj₂ c)) ,
       glv-low k lk ,
       (λ z d → proj₂ (proj₂ (P z (Gi→A k lk d)))) ,
       (λ z z′ d d′ p →
          let az = Gi→A k lk d ; az′ = Gi→A k lk d′ in
          Ω-mono (h z) (h z′) (proj₁ (cxB c z az)) (proj₁ (cxB c z′ az′)) (lh z) (lh z′) (P z az) (P z′ az′)
            (proj₂ (proj₂ (proj₂ c)) z z′ az az′ (p (idO {b = bl} {b′ = bl}))))
```
