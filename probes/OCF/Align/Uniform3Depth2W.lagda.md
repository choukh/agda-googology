# 统一形 (三): 一切深度 (二) $W$ 部分

> 接 [Uniform3Depth2Class](Uniform3Depth2Class.lagda.md). 把 Uniform3Hon §5 与 Uniform3Full §5 搬到一般深度 $d+1$. 除后继行外每一行都是一行: 一个 `Wd` 的行引理, 前缀是 $\zeta$. 后继行落到深度 $d$: `limWd` + `copyW`, 也就是 Uniform3Plus1 说的 "后继行变成帧的副本". **$d$ 在证明里不出现**, 只是模块参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform3Depth2W where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; Ωˢ; intoˢ; toZ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Decouple using (Idx; lvI; Lab0[])
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaExpBase using (OccΣ; repW; ωW)
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base
open import OCF.Align.Uniform3Depth1 using (c1Ω; cωΩ; cΩΩ; penΩ)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3Hon
open import OCF.Align.Uniform3Full using (FHc; FH→FHc; FHc-fsn; FHc-fsT; FHc-pred; pred-Pr; flo≼; Zc; Zc-of; Zc-flo)
open import OCF.Align.Uniform3Depth2Class
```

## §1 地板

```agda
FP→FLΩ : ∀ {c φ ζ} → FP c φ → FLΩ[ c ] φ ζ
FP→FLΩ f k with f k
... | inj₁ g = inj₁ g
... | inj₂ e1 with wit1 e1
...   | w , Iw , kw , o = inj₂ (w , Iw , kw , λ b → o _)

FHc→FLΩ : ∀ {c φ ζ z u v vs} → z ≡ ψᵗ u v ∷ vs → FHc c φ z → FLΩ[ c ] φ (ζ ++ z)
FHc→FLΩ {ζ = ζ} {u = u} {v} {vs} refl f k with f k
... | inj₁ g = inj₁ g
... | inj₂ (inj₁ e1) with wit1 e1
...   | w , Iw , kw , o = inj₂ (w , Iw , kw , λ b → o _)
FHc→FLΩ {ζ = ζ} {u = u} {v} {vs} refl f k | inj₂ (inj₂ (I , kw)) =
  inj₂ (u , I , kw , λ b → subst (λ w → Occ u (ψᵗ Ωᵗ w ∷ [])) (sym (++-assoc ζ (ψᵗ u v ∷ vs) b)) (od (OccΣ ζ oh)))
```

## §2 层号条件下的折叠: `WV`

```agda
module WGd (d : ℕ) {flE} {E : A (suc d) flE} {ζ : T} (c : Ordᴵ) (FE : FLΩ[ c ] flE ζ) (WE : Wd c (suc d) E ζ) where

  sucWg : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {a : Ordˢ k} {y ys} → cof (y ∷ ys) ≡ c1 →
         FLΩ[ c ] φ (ζ ++ pred (y ∷ ys)) → Wd c (suc d) (fold (suc d) φ cv E a) (ζ ++ pred (y ∷ ys)) →
         Wd c (suc d) (fold (suc d) φ cv E (Ord₊ˢ.suc a)) (ζ ++ (y ∷ ys))
  sucWg {φ = φ} {cv} {a} {y} {ys} cc Fφ IH {c′} u {fl} {Q} {ρ} Fl hQ =
    limWd d {ps = ρ} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA d Q (fold (suc d) φ cv E a) m} (c1Ω ζ cc)
          (λ m → subst (λ v → Wd c′ d (repA d Q (fold (suc d) φ cv E a) m) (ρ ++ v)) (sym (repW Ωᵗ ζ y ys cc m))
                       (copyW d Fl (FLΩ-up u (FLΩ-⊔ (FLΩ-ext _ FE) Fφ)) hQ (W-up (suc d) u IH) m))

  WA : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → FP c φ → Lab0ᴸ t y → Wd c (suc d) (fold (suc d) φ cv E t) (ζ ++ y)
  WV : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP c φ → LvOK c k → LabL t y → Wd c (suc d) (fold (suc d) φ cv E t) (ζ ++ y)
  W₊ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP c φ → LvOK c k → LabL₊ k Ll t y →
       Wd c (suc d) (fold (suc d) φ cv E t) (ζ ++ y)

  WA {y = []} fp (lz cc) = subst (Wd c (suc d) _) (sym (++-identityʳ ζ)) (wkW (suc d) proj₁ WE)
  WA {y = y ∷ ys} fp (lz cc) = ⊥-elim (cof-ne y ys cc)
  WA {y = []} fp (ls () l)
  WA {y = y ∷ ys} fp (ls cc l) = sucWg cc (FP→FLΩ fp) (WA fp l)
  WA {y = []} fp (ll () h)
  WA {φ = φ} {cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (ll cc h) =
    limWd (suc d) {ps = ζ} {y = y} {ys = ys} {F = λ n → fold (suc d) φ cv E (G n)} cc (λ n → WA fp (h n))
  WA {y = []} fp (lŝ₀ () K h₀ hk)
  WA {y = y ∷ ys} fp (lŝ₀ cc K h₀ hk) = ĉWd (suc d) {ps = ζ} {y = y} {ys = ys} cc K (WA fp h₀) (λ k → WA fp (hk k))
  WA {y = []} fp (lĉ () K h₀ hk)
  WA {y = y ∷ ys} fp (lĉ cc K h₀ hk) = ĉWd (suc d) {ps = ζ} {y = y} {ys = ys} cc K (WA fp h₀) (λ k → WA fp (hk k))

  WV {k = zero}    fp lv at = WA fp (atomL at)
  WV {k = suc _}   fp lv h  = W₊ fp lv h
  WV {k = lim _ _} fp lv h  = W₊ fp lv h

  W₊ {y = []} fp lv (gz cc) = subst (Wd c (suc d) _) (sym (++-identityʳ ζ)) (wkW (suc d) proj₁ WE)
  W₊ {y = y ∷ ys} fp lv (gz cc) = ⊥-elim (cof-ne y ys cc)
  W₊ {y = []} fp lv (gs () l)
  W₊ {y = y ∷ ys} fp lv (gs cc l) = sucWg cc (FP→FLΩ fp) (W₊ fp lv l)
  W₊ {y = []} fp lv (gl () h)
  W₊ {φ = φ} {cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp lv (gl cc h) =
    limWd (suc d) {ps = ζ} {y = y} {ys = ys} {F = λ n → fold (suc d) φ cv E (G n)} cc (λ n → W₊ fp lv (h n))
  W₊ {k = suc k′} fp lv (gu {r = zero} h) =
    wkW (suc d) _ (WV {φ = flo k′} {cv = cvFlo k′} (FP-flo lv) (LvOK-pred lv) h)
  W₊ {k = lim f s} fp lv (gu {r = self n} h) =
    wkW (suc d) _ (WV {φ = flo (f n)} {cv = cvFlo (f n)} (FP-flo′ (LvOK-self lv n)) (LvOK-self lv n) h)
  W₊ {y = []} fp lv (gi () I ej h)
  W₊ {φ = φ} {cv} {y = y ∷ ys} fp lv (gi {q = q} {f = f} cc I ej h) =
    limᵢWs (suc d) {ps = ζ} {y = y} {ys = ys} {ac = λ ev → cv (proj₂ ev) q} {H = λ x → fold (suc d) φ cv E (f (intoˢ (<→◃ q) x))}
           cc I ej (λ η x l → W₊ fp lv (h η x (→Ll (<→◃ q) l)))
  W₊ {y = []} fp lv (gĉ () K h₀ hk)
  W₊ {y = y ∷ ys} fp lv (gĉ cc K h₀ hk) = ĉWd (suc d) {ps = ζ} {y = y} {ys = ys} cc K (W₊ fp lv h₀) (λ k → W₊ fp lv (hk k))
  W₊ {k = zero} fp lv (gŝ () cc Iw bw ob h₀ hg)
  W₊ {k = suc _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  W₊ {k = suc _} {y = y ∷ ys} fp lv (gŝ kk cc Iw bw ob h₀ hg) =
    ŝWd (suc d) {ps = ζ} {y = y} {ys = ys} cc Iw bw (λ θ → OccΣ ζ (ob θ)) (W₊ fp lv h₀) (λ θ Y hY lY nθ lt e → W₊ fp lv (hg θ Y hY lY nθ lt e))
  W₊ {k = lim _ _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  W₊ {k = lim _ _} {y = y ∷ ys} fp lv (gŝ kk cc Iw bw ob h₀ hg) =
    ŝWd (suc d) {ps = ζ} {y = y} {ys = ys} cc Iw bw (λ θ → OccΣ ζ (ob θ)) (W₊ fp lv h₀) (λ θ Y hY lY nθ lt e → W₊ fp lv (hg θ Y hY lY nθ lt e))
```

## §3 诚实的尾巴: `WH`, `WΩ`

与 Uniform3Full §5 同一递归: `WΩ` 到 `WTail` 层号严格下降, `WH` 到 `WΩ` 层号不变, `WH` 到 `WH` 在 `Hn` 上结构下降. 变化只有穿透行: 帧 $E$ 与输入栈经 `W-up` 抬到 $i$.

```agda
fsTΩ : ∀ {w ws} → cof (w ∷ ws) ≡ c1 → ∀ η → fsT (Ωt (w ∷ ws)) η ≡ η
fsTΩ {w} {ws} c₁ η = fsT-c1 (w ∷ ws) (cof (w ∷ ws)) c₁ η

CH : (j : Ordᴵ) → T → Ordˢ j → Set
CH j η x = kd j ≡ false → Hn x η × FH (flo j) η

InpW : (j : Ordᴵ) → T → Ordˢ j → Set
InpW j η x = LabL x η × CH j η x

FHν : ∀ {ν v j} (I : Idx ν) → j ≅ᴵ lvI I → FH (flo j) (ψᵗ ν v ∷ [])
FHν I e k = inj₂ (inj₂ (I , flo≼ e k))

module WHd (d : ℕ) {flE} {E : A (suc d) flE} {ζ : T} (c : Ordᴵ) (FE : FLΩ[ c ] flE ζ) (WE : Wd c (suc d) E ζ) where
  open WGd d c FE WE

  WH : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FHc c φ y → Hn t y → LabL₊ k Ll t y → Wd c (suc d) (fold (suc d) φ cv E t) (ζ ++ y)
  WΩ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {k} → k ≅ᴵ toLevel Y hY → ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} → Zc c k φ →
       Wd c (suc d) (fold (suc d) φ cv E (Ωˢ k)) (ζ ++ Ωt θ)
  WTail : ∀ {j} {x : Ordˢ j} {η} → InpW j η x → Wd c (suc d) (fold (suc d) (flo j) (cvFlo j) E x) (ζ ++ η)

  WTail {j = zero}    (l , ch) = WV FP-fz (inj₂ lw0) l
  WTail {j = suc _}   (l , ch) = WH (FH→FHc (proj₂ (ch refl))) (proj₁ (ch refl)) l
  WTail {j = lim _ _} (l , ch) = WH (FH→FHc (proj₂ (ch refl))) (proj₁ (ch refl)) l

  WH fp (hΩ {w = w} refl (Y , hY , lY , nY) e) l = WΩ Y hY lY nY e (Zc-of (Y , hY , lY , nY) e fp)
  WH {y = []} fp hz (gz cc) = subst (Wd c (suc d) _) (sym (++-identityʳ ζ)) (wkW (suc d) proj₁ WE)
  WH {y = y ∷ ys} fp hz (gz cc) = ⊥-elim (cof-ne y ys cc)
  WH {y = []} fp (hs () n) l
  WH {y = y@(ψᵗ _ _) ∷ ys} fp (hs nb n) (gs cc l) =
    sucWg cc (FHc→FLΩ (proj₂ (proj₂ (pred-Pr nb cc))) (FHc-pred nb cc fp)) (WH (FHc-pred nb cc fp) n l)
  WH {y = []} fp (hl () n) l
  WH {φ = φ} {cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (hl nb n) (gl cc h) =
    limWd (suc d) {ps = ζ} {y = y} {ys = ys} {F = λ m → fold (suc d) φ cv E (G m)} cc (λ m → WH (FHc-fsn nb fp m) (n m) (h m))
  WH {y = []} fp (hi () n) l
  WH {φ = φ} {cv} {y = y ∷ ys} fp (hi {q = q} {f = f} nb n) (gi cc I ej h) =
    limᵢWs (suc d) {ps = ζ} {y = y} {ys = ys} {ac = λ ev → cv (proj₂ ev) q} {H = λ x → fold (suc d) φ cv E (f (intoˢ (<→◃ q) x))}
           cc I ej (λ η x l → WH (FHc-fsT nb fp η) (n η x l) (h η x (→Ll (<→◃ q) l)))
  WH {y = []} fp (hĉ () cw K g₀ n₀ gk nk) l
  WH {y = y ∷ ys} fp (hĉ nb cw K g₀ n₀ gk nk) l =
    ĉWd (suc d) {ps = ζ} {y = y} {ys = ys} cw K (WH (FHc-fsn nb fp 0) n₀ g₀) (λ k → WH (FHc-fsn nb fp (suc k)) (nk k) (gk k))
  WH {k = zero} fp (hŝ nb n₀ nk) (gŝ () cc Iw bw ob h₀ hg)
  WH {k = suc _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg)
  WH {k = suc _} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ kk cc Iw bw ob h₀ hg) =
    ŝWd (suc d) {ps = ζ} {y = y} {ys = ys} cc Iw bw (λ θ → OccΣ ζ (ob θ)) (WH (FHc-fsT nb fp (natT 1)) n₀ h₀)
        (λ θ Y hY lY nθ lt e → WH (FHc-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e))
  WH {k = lim _ _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg)
  WH {k = lim _ _} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ kk cc Iw bw ob h₀ hg) =
    ŝWd (suc d) {ps = ζ} {y = y} {ys = ys} cc Iw bw (λ θ → OccΣ ζ (ob θ)) (WH (FHc-fsT nb fp (natT 1)) n₀ h₀)
        (λ θ Y hY lY nθ lt e → WH (FHc-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e))

  WΩ {θ = []} Ord₊.zero hY l nθ z≅ zc = WV zc (inj₂ lw0) (LabL-Ω Ord₊.zero hY l nθ z≅)
  WΩ {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ zc with Lab0[] l
  ... | ()
  WΩ (Ord₊.suc Y) hY (l0 cc ()) nθ (s≅ e) zc
  WΩ (Ord₊.suc Y) hY (lω cc () h) nθ (s≅ e) zc
  WΩ {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) zc
  WΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc j} (s≅ e) {φ} {cv} zc =
    limᵢWd (suc d) {ps = ζ} {y = ψᵗ θ []} {ys = []} {ac = λ ev → cv (proj₂ ev) zero}
           {H = λ x → fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))} cΩθ I e
           (InpW j) i₀ hClose hPen hOut
    where
    θ : T
    θ = w ∷ ws
    cΩθ : cof (Ωt θ) ≡ cΩ (pred θ)
    cΩθ = cong (E.cofψ0 θ) c₁
    I : Idx (pred θ)
    I = Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁
    i₀ : InpW j (Ωt (pred θ)) (Ωˢ j)
    i₀ = LabL-Ω Y (hs⁻ hY) (Lab-≅ e′ l) (NF₁-pred nθ c₁) e , λ _ → hΩ refl I e , FHν I e
    hClose : ∀ {v x′} → kd j ≡ false → Out x′ (ψᵗ (pred θ) v ∷ []) → InpW j (ψᵗ (pred θ) v ∷ []) x′
    hClose kj o = frL₊ kj (proj₁ o) , λ _ → proj₂ o , FHν I e
    hPen : ∀ η x → LabL x η → ∀ {i} → j ≺ᴵ i → Up c i →
           Wd i (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))) (ζ ++ fsT (Ωt θ) η)
    hPen η x lx {i} s ui =
      subst (λ v → Wd i (suc d) _ (ζ ++ v)) (sym (fsTΩ c₁ η))
            (wkW (suc d) _ (WGd.WV d i (FLΩ-up ui FE) (W-up (suc d) ui WE) {φ = flo j} {cv = cvFlo j} (FP-flo′ lvᵢ) lvᵢ lx))
      where
      lvᵢ : LvOK i j
      lvᵢ = inj₁ (⊑ᴵ-trans (≺→⊑ s) (⊑-suc i))
    hOut : ∀ {η x} → InpW j η x → Wd c (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))) (ζ ++ fsT (Ωt θ) η)
    hOut {η} {x} ix = subst (λ v → Wd c (suc d) _ (ζ ++ v)) (sym (fsTΩ c₁ η)) (wkW (suc d) _ (WTail ix))
  WΩ (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) zc
  WΩ (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) zc
  WΩ {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) zc
  WΩ {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {k = lim f s} (l≅ ee) {φ} {cv} zc =
    limWd (suc d) {ps = ζ} {y = ψᵗ (w ∷ ws) []} {ys = []} {F = λ n → fold (suc d) φ cv E (Ord₊ˢ.up (self n) (Ωˢ (f n)))} (cong (E.cofψ0 (w ∷ ws)) c₁)
          (λ n → subst (λ u → Wd c (suc d) _ (ζ ++ u)) (sym (E.fsn0-eq w ws n c₁))
                       (wkW (suc d) _ (WΩ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) {flo (f n)} {cvFlo (f n)} (Zc-flo (f n)))))
  WΩ (Ord₊.limᵢ () f) hY l nθ e zc
  WΩ (Ord₊.up () x) hY l nθ e zc
```
