# 统一形 (五): 嵌入、层间搬运、尾巴与 $\Omega_{\Omega+\eta}$ 的标签

> 接 [Uniform5Close](Uniform5Close.lagda.md), [Uniform4Tail](Uniform4Tail.lagda.md). 结论先说:
>
> 1. `Ld-ι`: 嵌入 $r:a\triangleleft b$ 保持标签.
> 2. `tlA`/`tlV`/`tl₊`/`tlH`/`tlΩ`/`tlT`: 与 Uniform4Tail 逐行相同, 模块参数 `c : Ordᴵ`.
> 3. **`LdΩ̇ : Lab Y θ → NF₁ θ → α ≅ᴵ toLevel Y hY → Ld α m (Ω̇ α) (Ωt (μ θ))`: 对一切带标签的可数树, 对 $Y$ 递归**. $\theta=0$ 是闭包 ($\Omega_\Omega$), 后继只用 `Ld-ι` 与 $\Omega_{\Omega+\theta}[\zeta]=\zeta$, 极限 $\Omega_{\Omega+\theta}[n]=\Omega_{\Omega+\theta[n]}$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5Tail where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Decouple using (Idx; lvI; Lab0[])
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.OmegaExpBase using (OccΣ; cofΣ; predΣ)
open import OCF.Align.GoodLBase
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3Hon
open import OCF.Align.Uniform3Depth2Class
open import OCF.Align.Uniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.Uniform3Depth2Fold using (Zc₀; Zc₀-of)
open import OCF.Align.Uniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr)
open import OCF.Align.Uniform5Head
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.Uniform4Two
open import OCF.Align.Uniform5Class
open import OCF.Align.Uniform5Close
```

## §1 嵌入

```agda
out-intoU : ∀ {c k} (r : k ◃ c) {ξ} (z : O k ξ) → outU r (intoU r z) ≡ z
out-intoU zero      z = refl
out-intoU (suc r)   z = out-intoU r z
out-intoU (self n)  z = refl
out-intoU (lim n r) z = out-intoU r z

Ld-ι : ∀ {c d m φ} (q : c ◃ d) {x : O c φ} {u} → Ld c m x u → Ld d m (ι q x) u
Ld-ι q lz = lz
Ld-ι q (ls cc F l) = ls cc F (Ld-ι q l)
Ld-ι q (ll cc h) = ll cc (λ n → Ld-ι q (h n))
Ld-ι q (li cc I e hP hI) = li cc I e (λ η x l s v → Ld-ι q (hP η x l s v)) (λ η x i → Ld-ι q (hI η x i))
Ld-ι q (lĉ cc K h₀ hk) = lĉ cc K (Ld-ι q h₀) (λ k → Ld-ι q (hk k))
Ld-ι q (lŝ cc I b ob h₀ hg) = lŝ cc I b ob (Ld-ι q h₀) (λ θ Y hY lY nθ lt e → Ld-ι q (hg θ Y hY lY nθ lt e))
Ld-ι q (lclo F cc h₀ hg) = lclo F cc (Ld-ι q h₀) (λ θ Y hY lY nθ lt → Ld-ι q (hg θ Y hY lY nθ lt))
Ld-ι q (lwk l) = lwk (Ld-ι q l)
Ld-ι {d = d} q (lΩ {ps = ps} {y} {ys} {r = r} {h = h} cc I e f) =
  lΩ {r = <◃ r q} cc I e
     (λ {m′} v ξ z θ l → subst (λ w → Ld d m′ (ι q (h ξ (intoU (<→◃ r) w))) (ps ++ fsT (y ∷ ys) θ)) (sym (out-intoU (<→◃ (<◃ r q)) z))
                               (Ld-ι q (f v ξ z θ (intoL (<→◃ r) (outL (<→◃ (<◃ r q)) l)))))
```

## §2 尾巴

```agda
Zu : Mode → Ordᴵ → Flr → Set
Zu m zero      φ = ∀ u → FlU m φ u
Zu m (suc _)   φ = ⊤
Zu m (lim _ _) φ = ⊤

Zu-flo : ∀ m k → Zu m k (flo k)
Zu-flo hon zero u ()
Zu-flo (wkm c) zero u ()
Zu-flo m (suc k) = tt
Zu-flo m (lim f s) = tt

Zu-of : ∀ {m k φ} → Zc₀ k φ → Zu m k φ
Zu-of {m = hon} {k = zero} f u k with f k
... | inj₁ e = inj₁ e
... | inj₂ e = inj₂ (inj₁ e)
Zu-of {m = wkm c} {k = zero} f u k with f k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ e = inj₂ (inj₁ e)
Zu-of {k = suc _} f = tt
Zu-of {k = lim _ _} f = tt

FP→U : ∀ {c φ} → FP c φ → ∀ u → FlU (wkm c) φ u
FP→U f u k with f k
... | inj₁ g = inj₁ g
... | inj₂ e = inj₂ (inj₁ e)

FH→U : ∀ {m φ z u v vs} → z ≡ ψᵗ u v ∷ vs → FH φ z → FlU m φ z
FH→U {m = hon} refl f k with f k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ (I , kw)) = inj₂ (inj₂ (_ , I , kw , oh))
FH→U {m = wkm c} refl f k with f k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ (I , kw)) = inj₂ (inj₂ (_ , I , kw , oh))

module _ {c : Ordᴵ} where
  tlA : ∀ {m φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → (∀ u → FlU m φ u) → Lab0ᴸ t y → Ld c m (tl φ cv t) y
  tlA {y = []} fp (lz cc) = lz
  tlA {y = y ∷ ys} fp (lz cc) = ⊥-elim (cof-ne y ys cc)
  tlA {y = []} fp (ls () l)
  tlA {y = y ∷ ys} fp (ls cc l) = ls {ps = []} cc (fp _) (tlA fp l)
  tlA {y = []} fp (ll () h)
  tlA {y = y ∷ ys} fp (ll cc h) = ll {ps = []} cc (λ n → tlA fp (h n))
  tlA {y = []} fp (lŝ₀ () K h₀ hk)
  tlA {y = y ∷ ys} fp (lŝ₀ cc K h₀ hk) = lĉ {ps = []} cc K (tlA fp h₀) (λ k → tlA fp (hk k))
  tlA {y = []} fp (lĉ () K h₀ hk)
  tlA {y = y ∷ ys} fp (lĉ cc K h₀ hk) = lĉ {ps = []} cc K (tlA fp h₀) (λ k → tlA fp (hk k))

  tlV : ∀ {i k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP i φ → LvOK i k → LabL t y → Ld c (wkm i) (tl φ cv t) y
  tl₊ : ∀ {i k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP i φ → LvOK i k → LabL₊ k Ll t y → Ld c (wkm i) (tl φ cv t) y

  tlV {k = zero}    fp lv at = tlA (FP→U fp) (atomL at)
  tlV {k = suc _}   fp lv h  = tl₊ fp lv h
  tlV {k = lim _ _} fp lv h  = tl₊ fp lv h

  tl₊ {y = []} fp lv (gz cc) = lz
  tl₊ {y = y ∷ ys} fp lv (gz cc) = ⊥-elim (cof-ne y ys cc)
  tl₊ {y = []} fp lv (gs () l)
  tl₊ {y = y ∷ ys} fp lv (gs cc l) = ls {ps = []} cc (FP→U fp _) (tl₊ fp lv l)
  tl₊ {y = []} fp lv (gl () h)
  tl₊ {y = y ∷ ys} fp lv (gl cc h) = ll {ps = []} cc (λ n → tl₊ fp lv (h n))
  tl₊ {k = suc k′} fp lv (gu {r = zero} h) = lwk (tlV {φ = flo k′} {cv = cvFlo k′} (FP-flo lv) (LvOK-pred lv) h)
  tl₊ {k = lim f s} fp lv (gu {r = self n} h) = lwk (tlV {φ = flo (f n)} {cv = cvFlo (f n)} (FP-flo′ (LvOK-self lv n)) (LvOK-self lv n) h)
  tl₊ {y = []} fp lv (gi () I ej h)
  tl₊ {y = y ∷ ys} fp lv (gi {q = q} cc I ej h) =
    li {ps = []} cc I ej (λ η x l s v → Ld-cv v (tl₊ fp lv (h η x (→Ll (<→◃ q) l))))
       (λ η x i → tl₊ fp lv (h η x (→Ll (<→◃ q) (proj₁ i))))
  tl₊ {y = []} fp lv (gĉ () K h₀ hk)
  tl₊ {y = y ∷ ys} fp lv (gĉ cc K h₀ hk) = lĉ {ps = []} cc K (tl₊ fp lv h₀) (λ k → tl₊ fp lv (hk k))
  tl₊ {k = zero} fp lv (gŝ () cc Iw bw ob h₀ hg)
  tl₊ {k = suc _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  tl₊ {k = suc _} {y = y ∷ ys} fp lv (gŝ kk cc Iw bw ob h₀ hg) =
    lŝ {ps = []} cc Iw bw ob (tl₊ fp lv h₀) (λ θ Y hY lY nθ lt e → tl₊ fp lv (hg θ Y hY lY nθ lt e))
  tl₊ {k = lim _ _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  tl₊ {k = lim _ _} {y = y ∷ ys} fp lv (gŝ kk cc Iw bw ob h₀ hg) =
    lŝ {ps = []} cc Iw bw ob (tl₊ fp lv h₀) (λ θ Y hY lY nθ lt e → tl₊ fp lv (hg θ Y hY lY nθ lt e))

  tlH : ∀ {m k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FH φ y → Hn t y → LabL₊ k Ll t y → Ld c m (tl φ cv t) y
  tlΩ : ∀ {m θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {k} → k ≅ᴵ toLevel Y hY → ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} → Zu m k φ →
        Ld c m (tl φ cv (Ωˢ k)) (Ωt θ)
  tlT : ∀ {m j} {x : Ordˢ j} {η} → InpW j η x → Ld c m (tl (flo j) (cvFlo j) x) η

  tlT {m} {j = zero}    (l , ch) = tlA (Zu-flo m zero) (atomL l)
  tlT {j = suc _}   (l , ch) = tlH (proj₂ (ch refl)) (proj₁ (ch refl)) l
  tlT {j = lim _ _} (l , ch) = tlH (proj₂ (ch refl)) (proj₁ (ch refl)) l

  tlH fp (hΩ refl (Y , hY , lY , nY) e) l = tlΩ Y hY lY nY e (Zu-of (Zc₀-of (Y , hY , lY , nY) e fp))
  tlH {y = []} fp hz (gz cc) = lz
  tlH {y = y ∷ ys} fp hz (gz cc) = ⊥-elim (cof-ne y ys cc)
  tlH {y = []} fp (hs () n) l
  tlH {y = y@(ψᵗ _ _) ∷ ys} fp (hs nb n) (gs cc l) =
    ls {ps = []} cc (FH→U (proj₂ (proj₂ (pred-Pr nb cc))) (FH-pred nb cc fp)) (tlH (FH-pred nb cc fp) n l)
  tlH {y = []} fp (hl () n) l
  tlH {y = y ∷ ys} fp (hl nb n) (gl cc h) = ll {ps = []} cc (λ m → tlH (FH-fsn nb fp m) (n m) (h m))
  tlH {y = []} fp (hi () n) l
  tlH {y = y ∷ ys} fp (hi {q = q} nb n) (gi cc I ej h) =
    li {ps = []} cc I ej (λ η x l s v → tlH (FH-fsT nb fp η) (n η x l) (h η x (→Ll (<→◃ q) l)))
       (λ η x i → tlH (FH-fsT nb fp η) (n η x (proj₁ i)) (h η x (→Ll (<→◃ q) (proj₁ i))))
  tlH {y = []} fp (hĉ () cw K g₀ n₀ gk nk) l
  tlH {y = y ∷ ys} fp (hĉ nb cw K g₀ n₀ gk nk) l = lĉ {ps = []} cw K (tlH (FH-fsn nb fp 0) n₀ g₀) (λ k → tlH (FH-fsn nb fp (suc k)) (nk k) (gk k))
  tlH {k = zero} fp (hŝ nb n₀ nk) (gŝ () cc Iw bw ob h₀ hg)
  tlH {k = suc _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg)
  tlH {k = suc _} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ kk cc Iw bw ob h₀ hg) =
    lŝ {ps = []} cc Iw bw ob (tlH (FH-fsT nb fp (natT 1)) n₀ h₀) (λ θ Y hY lY nθ lt e → tlH (FH-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e))
  tlH {k = lim _ _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg)
  tlH {k = lim _ _} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ kk cc Iw bw ob h₀ hg) =
    lŝ {ps = []} cc Iw bw ob (tlH (FH-fsT nb fp (natT 1)) n₀ h₀) (λ θ Y hY lY nθ lt e → tlH (FH-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e))

  tlΩ {θ = []} Ord₊.zero hY l nθ z≅ zc = tlA zc (atomL (LabL-Ω Ord₊.zero hY l nθ z≅))
  tlΩ {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ zc with Lab0[] l
  ... | ()
  tlΩ (Ord₊.suc Y) hY (l0 cc ()) nθ (s≅ e) zc
  tlΩ (Ord₊.suc Y) hY (lω cc () h) nθ (s≅ e) zc
  tlΩ {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) zc
  tlΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc j} (s≅ e) {φ} {cv} zc =
    li {ps = []} {y = ψᵗ (w ∷ ws) []} {ys = []} (cong (E.cofψ0 (w ∷ ws)) c₁) (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e
       (λ η x lx {i} s v → re (sym (fsTΩ c₁ η)) (lwk (tlV {φ = flo j} {cv = cvFlo j} (FP-flo′ (inj₁ (⊑ᴵ-trans (≺→⊑ s) (⊑-suc i)))) (inj₁ (⊑ᴵ-trans (≺→⊑ s) (⊑-suc i))) lx)))
       (λ η x ix → re (sym (fsTΩ c₁ η)) (lwk (tlT ix)))
  tlΩ (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) zc
  tlΩ (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) zc
  tlΩ {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) zc
  tlΩ {m = m} {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {k = lim f s} (l≅ ee) {φ} {cv} zc =
    ll {ps = []} {y = ψᵗ (w ∷ ws) []} {ys = []} (cong (E.cofψ0 (w ∷ ws)) c₁)
       (λ n → re (sym (E.fsn0-eq w ws n c₁))
                 (lwk (tlΩ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) {flo (f n)} {cvFlo (f n)} (Zu-flo m (f n)))))
  tlΩ (Ord₊.limᵢ () f) hY l nθ e zc
  tlΩ (Ord₊.up () x) hY l nθ e zc
```

## §3 $\Omega_{\Omega+\eta}$ 的标签

```agda
ZuK : ∀ m k → Zu m k (fz ⊔ fk k)
ZuK hon zero u (inr ink) = inj₁ z≅
ZuK (wkm c) zero u (inr ink) = inj₁ (inj₁ (inj₁ z≅))
ZuK m (suc k) = tt
ZuK m (lim f s) = tt

Fw-Ω̂ : ∀ m → Fw m (fz ⊔ fk zero) [] ΩΩ []
Fw-Ω̂ hon (inr ink) = inj₁ z≅
Fw-Ω̂ (wkm c) (inr ink) = inj₁ (inj₁ (inj₁ z≅))

LdΩ̇ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {α} → α ≅ᴵ toLevel Y hY → ∀ m → Ld α m (Ω̇ α) (Ωt (μ θ))
LdΩ̇ {θ = []} Ord₊.zero hY l nθ z≅ m =
  lclo {ps = []} {y = ΩΩ} {ys = []} (Fw-Ω̂ m) refl
       (tlΩ one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _) {fz ⊔ fk zero} {proj₂} tt)
       (λ θ Y hY lY nθ lt → tlΩ Y hY lY nθ (≅ᴵ-refl _) {fz ⊔ fk (toLevel Y hY)} {λ e q → proj₂ e (suc q)} (ZuK m (toLevel Y hY)))
LdΩ̇ {θ = w ∷ ws} Ord₊.zero hY l nθ z≅ m with Lab0[] l
... | ()
LdΩ̇ (Ord₊.suc Y) hY (l0 cc ()) nθ (s≅ e) m
LdΩ̇ (Ord₊.suc Y) hY (lω cc () h) nθ (s≅ e) m
LdΩ̇ {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) m
LdΩ̇ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {suc j} (s≅ e) m =
  lΩ {ps = []} {y = ψᵗ (μ (w ∷ ws)) []} {ys = []} (cong (E.cofψ0 (μ (w ∷ ws))) c₁) (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e
     (λ v ξ z θ l′ → lwk (re (sym (fsTΩ {Ωp} {w ∷ ws} c₁ θ)) (Ld-ι zero l′)))
LdΩ̇ (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) m
LdΩ̇ (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) m
LdΩ̇ {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) m
LdΩ̇ {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {lim f s} (l≅ ee) m =
  ll {ps = []} {y = ψᵗ (μ (w ∷ ws)) []} {ys = []} (cong (E.cofψ0 (μ (w ∷ ws))) c₁)
     (λ n → re (sym (E.fsn0-eq Ωp (w ∷ ws) n c₁))
               (Ld-ι (self n) (LdΩ̇ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) m)))

LdΩ̇ᴵ : ∀ {ν α} (I : Idx ν) → α ≅ᴵ lvI I → ∀ m → Ld α m (Ω̇ α) (Ωt (μ ν))
LdΩ̇ᴵ (Y , hY , lY , nY) e m = LdΩ̇ Y hY lY nY e m
```
