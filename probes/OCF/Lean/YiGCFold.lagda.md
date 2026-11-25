# NoΩ 源层上的 Level 折叠主引理
验收文件；精确对应下的沿帧 MS 与第 1 层 lower。
来源：YiLSFold.M.MS/Mdef/chainS，复用 YiFPFrames 的执行、换目标与 YiGCSlots 的保留规格。
结论仍是 Level 关系；到 EboLean.M 的窄桥不在本模块中假设完成。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGCFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.YiRWBlock renaming (L to LF)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath hiding (psh; wk; emb)
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiNRHit using (NoΩ)
open import OCF.Lean.YiFPFrames
open import OCF.Lean.YiGCFrames
open import OCF.Lean.YiGCCorr
open import OCF.Lean.YiGCRel
open import OCF.Lean.YiGCSlots
open import OCF.Lean.YiKCStep using (OKB; ⊴-trans)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiLeanValRel using (TRC)
import OCF.Lean.YiTBRow as TB
import OCF.Align.Level as L
open L using (_<ᴵ_)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using () renaming (iter to iterᴸ)
foldV : (a : LF) → Ok a → TB.Rb a → Base a → (j : LF) → j ≤ a → Tr⁺ j → Tr a → Tr j
foldV a o r B j w β x = proj₁ (TB.ψ a o r B j w β x)
UpV : ∀ {j} (a : LF) → Dn j a → Tr⁺ j → Tr a → Tr j
UpV a d b x = proj₁ (Up a d b x)
run-nz : ∀ {j a} (st : St j a) x → j ⊢ zero ◃ run st x
run-nz st x = proj₂ (run⁺ st x)
run-ss : ∀ {j a} (st : St j a) {k} {X : L.Ordᶜ k} {y : Tr a}
  → Rel j X (run st y) → Rel j (L.lim (iterᴸ (X L.+_) L.zero)) (run st (suc y))
run-ss {j} (fo (o , r , B) w β) {y = y} h = Add.nextL j (SlOf j) (proj₂ (TB.ψ _ o r B j w β y)) h
run-ss {j} {a} (uf d b) {y = y} h = Add.nextL j (SlOf j) (proj₂ (Up a d b y)) h
ok-cfg : ∀ {j a} (st : St j a) → OKst st → {C′ : Cfg a} → cfgOf st ≡ just C′ → OKB (proj₂ (proj₂ C′))
ok-cfg (fo C w β) ok refl = ok
J′ : (a : LF) → ∀ {j} {d : Dc a j} → Ctx a d → ∀ {k} → L.Ordᶜ k → Tr j → Set
J′ a = Sim.J a (SlOf a)
Wch : ∀ {i′ K′} (q : i′ <ᴵ K′) (f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′) → ℕ → L.Ordᶜ i′
Wch {i′} q f′ = iterᴸ (λ x → L.ψ q (λ r → r) (f′ (L.into (L.<→◃ q) x))) (L.Ω i′)
Dref : ∀ {i′ K′ L⁺ i} (p₀ : i <ᴵ L⁺) (σ : L.Simᴵ K′ L⁺) (q : i′ <ᴵ K′) (f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′) → L.Ordᶜ i
Dref p₀ σ q f′ = L.lim (λ n → L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (Wch q f′ n))))
Vch : ∀ {a} (C : Cfg a) (p : Pos a) (g : Br a p → Tr a) → ℕ → Br a p
Vch {a} (o , r , B) p g = iter (λ z → fromBr a p (foldV a o r B (at a p) (posW a p) (B (at a p) (posW a p)) (g z))) (fromBr a p zero)
module M {ℓ : LF} (f : NoΩ ℓ) (C₀ : Cfg ℓ) (ok : OKB (proj₂ (proj₂ C₀))) where

  top : ∀ {j} → j ≤ ℓ → St j ℓ
  top w = can C₀ w

  ReC : ∀ {jd} {d : Dc ℓ jd} → Ctx ℓ d → Cfg jd → Set
  ReC {jd} Γ C′ = ∀ {j₁} (w₁ : j₁ ≤ jd) → Σ (j₁ ≤ ℓ) (λ w₂ → stOf f (top w₂) Γ ≡ can C′ w₁)

  top-zr : ∀ {j} (w : j ≤ ℓ) {i} → Corr i j → (y : Tr ℓ) → Rel j (L.Ω i) (run (top w) y)
  top-zr {j} w ci y = Rel-⊴ (START (noΩW w f) ci) (⊴-trans (ok j w) (run-⊵ (top w) y))

  mutual
    MS : ∀ {j} (w : j ≤ ℓ) {jd} {d : Dc ℓ jd} {Γ : Ctx ℓ d} (s : St j jd) → s ≡ stOf f (top w) Γ
       → ∀ {k} {X : L.Ordᶜ k} {y : Tr jd} → J′ ℓ Γ X y
       → ∀ {L⁺ i} (p₀ : i <ᴵ L⁺) → Corr i j → (σ : L.Simᴵ k L⁺) → Rel j (L.ψ p₀ σ X) (run s y)
    MS {j} w s eq (zr {y = y}) p₀ ci σ =
      subst (λ s → Rel j (L.Ω _) (run s y)) (sym eq) (top-zr w ci y)
    MS {j} w s eq (pop {Γ = Γ₀} {t = t} {c = c} {y = y} r) p₀ ci σ =
      subst (λ s → Rel j _ (run s y)) (sym (trans eq (stOf-snoc f (top w) Γ₀ t c)))
        (Rel-⊴ (MS w (stOf f (top w) Γ₀) refl r p₀ ci σ) (nxt-⊵ (noΩD f Γ₀) (stOf f (top w) Γ₀) t c y))
    MS w s eq (ss r) p₀ ci σ = run-ss s (MS w s eq r p₀ ci σ)
    MS w s eq (wk r e) p₀ ci σ = wk (MS w s eq r p₀ ci σ) (run-mono s e)
    MS w s eq (ll h) p₀ ci σ = ll (λ n → MS w s eq (h n) p₀ ci σ)
    MS {j} w {jd} {Γ = Γ} (uf d b) eq (nodeR {q = q} {f = f′} {p = p} {g = g} lv h) p₀ ci σ
      with L.<ᴵ-dec (σ q) p₀
    ... | injᵃ (L.via e r) =
      nodeR (subst (Corr _) (sym (at-mv d p)) (Corr-≅ (L.≅ᴵ-sym e) lv))
        (λ y₀ c′ sl →
          subst (λ u → Rel j (L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (L.tr⁻ e u)))) (UpV jd d b (g (mvBr d p c′))))
            (sym (L.out-into (L.<→◃ r) y₀))
            (MS w (uf d b) eq
              (h (L.tr⁻ e y₀) (mvBr d p c′) (toSl ℓ _ p (mvRel d p (TRC.tr⁻ᴿ (trP j (mv d p)) e sl))))
              p₀ ci σ))
    ... | injᵇ x = ⊥-elim (L.clash₁ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _)
        (POS (noΩW w f) (mv d p) (subst (Corr _) (sym (at-mv d p)) lv) ci) x)
    ... | injᶜ x = ⊥-elim (L.clash₂ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _)
        (POS (noΩW w f) (mv d p) (subst (Corr _) (sym (at-mv d p)) lv) ci) x)
    MS {j} w {jd} {Γ = Γ} (fo (ε′ , ρ′ , B′) w′ β) eq (nodeR {q = q} {f = f′} {p = p} {g = g} lv h) p₀ ci σ
      with L.<ᴵ-dec (σ q) p₀
    ... | injᵃ (L.via e r) =
      nodeCase (noΩD f Γ) ε′ p w′
        (λ z → TB.ψ jd ε′ ρ′ B′ j w′ β (g z))
        (λ z → fromBr jd p (foldV jd ε′ ρ′ B′ (at jd p) (posW jd p) (B′ (at jd p) (posW jd p)) (g z)))
        (λ T → Rel j (L.limᵢ r (λ u → L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) u)))))) T)
        (λ q′ cv kf → nodeR (subst (Corr _) (sym (Kept.lev kf)) (Corr-≅ (L.≅ᴵ-sym e) lv))
          (λ y₀ c′ sl →
            subst (λ u → Rel j (L.ψ p₀ σ (f′ (L.into (L.<→◃ q) (L.tr⁻ e u))))
                               (foldV jd ε′ ρ′ B′ j w′ β (g (cv c′))))
              (sym (L.out-into (L.<→◃ r) y₀))
              (MS w (fo (ε′ , ρ′ , B′) w′ β) eq
                (h (L.tr⁻ e y₀) (cv c′) (toSl ℓ _ p (Kept.conv kf (TRC.tr⁻ᴿ (trP j q′) e sl))))
                p₀ ci σ)))
        (λ df → ⊥-elim (df lv ci (L.via e r)))
    ... | injᵇ x =
      nodeCase (noΩD f Γ) ε′ p w′
        (λ z → TB.ψ jd ε′ ρ′ B′ j w′ β (g z))
        (λ z → fromBr jd p (foldV jd ε′ ρ′ B′ (at jd p) (posW jd p) (B′ (at jd p) (posW jd p)) (g z))) (λ T → Rel j (Dref p₀ σ q f′) T)
        (λ q′ cv kf → ⊥-elim (L.clash₁ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _) (Kept.below kf lv ci) x))
        (λ _ → Mdef w Γ (ε′ , ρ′ , B′) w′ β eq lv h p₀ ci σ)
    ... | injᶜ x =
      nodeCase (noΩD f Γ) ε′ p w′
        (λ z → TB.ψ jd ε′ ρ′ B′ j w′ β (g z))
        (λ z → fromBr jd p (foldV jd ε′ ρ′ B′ (at jd p) (posW jd p) (B′ (at jd p) (posW jd p)) (g z))) (λ T → Rel j (Dref p₀ σ q f′) T)
        (λ q′ cv kf → ⊥-elim (L.clash₂ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _) (Kept.below kf lv ci) x))
        (λ _ → Mdef w Γ (ε′ , ρ′ , B′) w′ β eq lv h p₀ ci σ)
    MS w s eq (ur r) p₀ ci σ = MS w s eq r p₀ ci (λ q → σ (L.suc q))
    MS w s eq (ul n r) p₀ ci σ = MS w s eq r p₀ ci (λ q → σ (L.lim n q))
    MS {j} w s eq (psh {j = jp} {Γ = Γ₀} {t = t} {c = c} {y = y} {e = e} r) p₀ ci σ =
      subst (λ s → Rel j _ (run s (up t c y e))) (sym eq)
        (subst (Rel j _) (sym (run-up (noΩD f Γ₀) (stOf f (top w) Γ₀) t c y e))
          (subst (λ s → Rel j _ (run s (asChild jp c y))) (stOf-snoc f (top w) Γ₀ t c)
            (MS w (stOf f (top w) (snocC Γ₀ t c)) refl r p₀ ci σ)))

    Mdef : ∀ {j} (w : j ≤ ℓ) {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) (C′ : Cfg jd) (w′ : j ≤ jd)
      (β : Tr⁺ j)
      → fo C′ w′ β ≡ stOf f (top w) Γ
      → ∀ {i′ K′} {q : i′ <ᴵ K′} {f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′} {p : Pos jd} {g : Br jd p → Tr jd}
      → Corr i′ (at jd p)
      → (∀ (y₀ : L.Ordᶜ i′) (c : Br jd p) → SlOf ℓ d p y₀ c → J′ ℓ Γ (f′ (L.into (L.<→◃ q) y₀)) (g c))
      → ∀ {L⁺ i} (p₀ : i <ᴵ L⁺) → Corr i j → (σ : L.Simᴵ K′ L⁺)
      → Rel j (Dref p₀ σ q f′)
          (proj₁ (limc⁺ (λ n → run⁺ (fo C′ w′ β) (g (Vch C′ p g n)))))
    Mdef {j} w {jd} Γ C′ w′ β eq {q = q} {f′ = f′} {p = p} {g = g} lv h p₀ ci σ =
      ll (λ n → Add.inCum j (SlOf j) (λ m → run (fo C′ w′ β) (g (Vch C′ p g m)))
                  (λ m → run-nz (fo C′ w′ β) (g (Vch C′ p g m))) (suc n)
        (MS w (fo C′ w′ β) eq
          (h (Wch q f′ n) (Vch C′ p g (suc n))
             (toSl ℓ _ p (chainS Γ C′
               (g-fo (good-stOf f Γ) C₀ w _ (cong cfgOf (sym eq)))
               (ok-cfg (stOf f (top w) Γ) (ok-stOf f (top w) ok Γ) (cong cfgOf (sym eq)))
               lv h n)))
          p₀ ci σ))

    chainS : ∀ {jd} {d : Dc ℓ jd} (Γ : Ctx ℓ d) (C′ : Cfg jd) → ReC Γ C′ → OKB (proj₂ (proj₂ C′))
      → ∀ {i′ K′} {q : i′ <ᴵ K′} {f′ : L.U i′ (L.<→◃ q) → L.Ordᶜ K′} {p : Pos jd} {g : Br jd p → Tr jd}
      → Corr i′ (at jd p)
      → (∀ (y₀ : L.Ordᶜ i′) (c : Br jd p) → SlOf ℓ d p y₀ c → J′ ℓ Γ (f′ (L.into (L.<→◃ q) y₀)) (g c))
      → ∀ n → RelP jd p (Wch q f′ n) (Vch C′ p g (suc n))
    chainS {jd} Γ (ε′ , ρ′ , B′) rc okC {p = p} {g = g} lv h zero =
      relFrom jd p (Rel-⊴ (START (noΩ-at (noΩD f Γ) p) lv)
        (⊴-trans (okC (at jd p) (posW jd p))
                 (ψ-⊵ jd ε′ ρ′ B′ (at jd p) (posW jd p) _ (g (fromBr jd p zero)))))
    chainS {jd} Γ (ε′ , ρ′ , B′) rc okC {q = q} {f′ = f′} {p = p} {g = g} lv h (suc n) =
      relFrom jd p (MS (proj₁ (rc (posW jd p))) (can (ε′ , ρ′ , B′) (posW jd p)) (sym (proj₂ (rc (posW jd p))))
        (h (Wch q f′ n) (Vch (ε′ , ρ′ , B′) p g (suc n)) (toSl ℓ _ p (chainS Γ (ε′ , ρ′ , B′) rc okC lv h n)))
        q lv (λ r → r))


lower : ∀ {a κ j i} (ns : NoΩ a) (C : Cfg a) → OKB (proj₂ (proj₂ C))
  → Corr κ a → (w : j ≤ a) → Corr i j → (p : i L.<ᴵ L.suc κ)
  → Rel j (L.ψ p (λ q → L.suc q) (L.Ω κ)) (run (can C w) (proj₁ (Ωt a)))
lower ns C ok c w ci p = M.MS ns C ok w (can C w) refl (START ns c) p ci (λ q → L.suc q)

import OCF.Lean.YiKVRel as K
lower-one : ∀ {a κ} (ns : NoΩ a) (C : Cfg a) → OKB (proj₂ (proj₂ C))
  → Corr κ a → (w : K.one ≤ a) → (p : L.natᴵ 1 L.<ᴵ L.suc κ)
  → Rel K.one (L.ψ p (λ q → L.suc q) (L.Ω κ)) (run (can C w) (proj₁ (Ωt a)))
lower-one ns C ok c w p = lower ns C ok c w (cs cz) p

import OCF.Align.Value as V
lower-zero : ∀ {a κ} (ns : NoΩ a) (C : Cfg a) → OKB (proj₂ (proj₂ C))
  → Corr κ a → (p : L.zero L.<ᴵ L.suc κ)
  → L.ψ p (λ q → L.suc q) (L.Ω κ) V.≼ K.readRW (run (can C (z≤ a)) (proj₁ (Ωt a)))
lower-zero ns C ok c p = r→≼ (lower ns C ok c (z≤ _) cz p)
```
