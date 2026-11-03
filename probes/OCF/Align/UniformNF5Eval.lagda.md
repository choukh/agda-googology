# 层号参数化的无符号闭包定理 (九): 求值定理

> 由 [UniformNF4Eval](UniformNF4Eval.lagda.md) 经脚本移植到 `Ordᴵ` 层号, 只删 `lΩ` (取 `Ω̇G _`).
>
> 接 [UniformNF5Psi](UniformNF5Psi.lagda.md). 结论先说:
>
> 1. **`Ev.T̄ : Gᵀ c 𝓖 x → Good true 𝓖′ (ψ̄ x ev p)`, 只要 $O\in\mathcal G'$ 推出 `top O ev p` ∈ $\mathcal G$, $O\in$ `VisT i`.** 这是 [UniformNF3D1F](UniformNF3D1F.lagda.md) 的 `FF` 在树上的形式, 证明同形. `oΩ` 的行用 `Psi` 走链.
> 2. **`gclo` 的行取 `Bd`.** 界 $\sqsubseteq$ 层号由 `ubd` 得到: 目标由 `readT`, 地板由 `dt`/`dg`. 这是全文唯一读 `ev` 的地方. 分支的守卫就是 `𝓖ᵍ` 在 `top` 处的值.
> 3. **`T̄₀`: 目标 0 给 `Goodᴺ`.**
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF5Eval where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; tr⁻ˢ)
open import OCF.Align.UniformNF3Eq using (≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅; Ωˢ-≅; Ωˢ-refl; self-tr⁻ˢ; tr⁻ˢ-≅; ≅-tr⁻ˢ; ⊑ᴵ-≅ʳ; ≅ᴵ→⊑ᴵ; addˢ-≅)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; cloA; bound; Top; Bd; Fc; ubd; evF; iF; FM; FB; liftEv; limᵢA)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr)
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.Uniform4Two
open RestrO
open import OCF.Align.UniformNF5Base
open import OCF.Align.UniformNF5Rules
open import OCF.Align.UniformNF5Strict
open import OCF.Align.UniformNF5Class
open import OCF.Align.UniformNF5ClassF
open import OCF.Align.UniformNF5Good
open import OCF.Align.UniformNF5Add
open import OCF.Align.UniformNF5Psi
```

## §1 目标类 `VisT` 的封闭性

与 UniformNF3D1F §2 相同, 没有前缀.

```agda
VT : ∀ i → Cl i
VT = VisT

toV : ∀ {i} {O : Obs i} → NZ i → VT i O → Vis (suc i) O
toV {i = suc _}   nz v = v
toV {i = lim _ _} nz v = v

frV : ∀ {i} {O : Obs i} → NZ i → Vis (suc i) O → VT i O
frV {i = suc _}   nz v = v
frV {i = lim _ _} nz v = v

cxT : ∀ i {O : Obs i} → VT i O → Ctx O
cxT zero refl = tt
cxT (suc _) v = cx v
cxT (lim _ _) v = cx v

clT : ∀ {i} {a : Ordˢ i} → a ≅ˢ a → Ωˢ i ⊑ᴱ a → NZ i → ∀ {O C″} → VT i O → FlOver a O C″ → VT i C″
clT {i} {a} ea fa nz v f′ = frV nz (vis (cxo f′)
  (λ {b} h t et fl G →
  ⊑ᴵ-trans (cp (toV nz v) h a ea (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ h) fa) (proj₁ (flw f′ t et G)))
           (toLevel-⊑ (forceᴺ-HS _ _) (forceᴺ-HS _ G) (proj₂ (flw f′ t et G)))))

cgT : ∀ {i} {C C′ : Obs i} → Ctx C → C ≈ᵒ C′ → VT i C′ → VT i C
cgT {i = zero} c₀ o refl = ≈-id o
cgT {i = suc _} c₀ o v = Vis-≈ c₀ o v
cgT {i = lim _ _} c₀ o v = Vis-≈ c₀ o v

hoT : ∀ {i} {a : Ordˢ i} {O : Obs i} → a ≅ˢ a → Ωˢ i ⊑ᴱ a → VT i O → Hon i a O
hoT {i = zero} ea fa v G = z⊑
hoT {i = suc j} {a} ea fa v G = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (cp v (via (≅ᴵ-refl (suc j)) zero) a ea (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fa) G)
hoT {i = lim f s} {a} ea fa v G = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (cp v (via (≅ᴵ-refl (lim f s)) zero) a ea (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fa) G)

readT : ∀ {i} {O : Obs i} (t : Ordˢ i) → VT i O → t ≅ˢ t → Ωˢ i ⊑ᴱ t → (G : Goodᴺ (toZ (run O t))) → suc i ⊑ᴵ lvG G
readT {i = zero} t refl et fi G = read1 idO tt t et (⊑ᴱ-trans (Ω1ᴱ zero) fi) G
readT {i = suc j} t v et fi G = cp v (via (≅ᴵ-refl (suc j)) zero) t et (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fi) G
readT {i = lim f s} t v et fi G = cp v (via (≅ᴵ-refl (lim f s)) zero) t et (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fi) G

hselfT : ∀ i {𝓐 : Cl i} {a : Ordˢ i} → a ≅ˢ a → 𝟏 ⊑ᴱ a → (NZ i → ∀ {O} → 𝓐 O → FlOver a O (addo O a (λ q → q)) → 𝓐 (addo O a (λ q → q))) → (∀ {O} → 𝓐 O → Ctx O) → Wit i 𝓐 → Hk i 𝓐 a (λ q → q) 𝓐
hselfT zero ea oa cl cxA z = z
hselfT (suc j) {a = a} ea oa cl cxA z {O} h = cl tt h (flo-over (afl ea oa tt , cxA h) (λ t et G → add-rᴱ {a = a} {a′ = a} {σ = λ q → q} t ea et (ctx-refl O (cxA h)) G))
hselfT (lim f s) {a = a} ea oa cl cxA z {O} h = cl tt h (flo-over (afl ea oa tt , cxA h) (λ t et G → add-rᴱ {a = a} {a′ = a} {σ = λ q → q} t ea et (ctx-refl O (cxA h)) G))

inpVis : ∀ {c φ} j {𝓖₀ : ClT c φ} (W : Cx c φ → Obs j) → (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → ∀ {D} → Inp j (W ⟪ 𝓖₀ ⟫) D → Vis j D
inpVis zero W Wv refl = vis tt (λ { (via _ ()) })
inpVis (suc j) W Wv (x , C , c , o) = Vis-≈ x o (Vis-mono ≺-suc (Wv c))
inpVis (lim f s) W Wv (x , C , c , o) = Vis-≈ x o (Vis-mono ≺-suc (Wv c))

visD : ∀ {c φ} j {𝓖₀ : ClT c φ} (W : Cx c φ → Obs j) → (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → ∀ {D′} → Inp j (W ⟪ 𝓖₀ ⟫) D′ → VT j D′
visD zero W Wv d = d
visD (suc j) W Wv (x , C , c , o) = Vis-≈ x o (Wv c)
visD (lim f s) W Wv (x , C , c , o) = Vis-≈ x o (Wv c)

witI : ∀ j {𝓓 : Cl j} → Wit j (Inp j 𝓓)
witI zero = refl
witI (suc _) = tt
witI (lim _ _) = tt

vΩ : ∀ i → Good true (VT i) (Ωˢ i)
vΩ zero = Good-mono (λ { refl → vis tt (λ { (via _ ()) }) }) (Ωg zero)
vΩ (suc i) = Good-mono (λ v → Vis-mono ≺-suc v) (Ωg (suc i))
vΩ (lim f s) = Good-mono (λ v → Vis-mono ≺-suc v) (Ωg (lim f s))
```

## §2 `T̄`

```agda
module EvalM (Ω̇G : ∀ t → Gᵀ t {Fl} 𝓥 (Ω̇ t)) where
  open PsiM Ω̇G

  ZT : ∀ {c φ ℓ} j {ev : Ev ℓ φ} → j <ᴵ ℓ → ClT c φ → Set
  ZT zero {ev} ac 𝓖₀ = 𝓖₀ (top idO ev ac)
  ZT (suc _) ac 𝓖₀ = ⊤
  ZT (lim _ _) ac 𝓖₀ = ⊤

  incE′ : ∀ {c φ ℓ} j {ev : Ev ℓ φ} {ac : j <ᴵ ℓ} (𝓖₀ : ClT c φ) (W : Cx c φ → Obs j) →
          (∀ {C C′} → 𝓖₀ C → AboveV j C′ (W C) → 𝓖₀ C′) → ZT j {ev = ev} ac 𝓖₀ →
          ∀ {C} → (Σ _ λ D → Inp j (W ⟪ 𝓖₀ ⟫) D × (C ≡ top D ev ac)) → 𝓖₀ C
  incE′ zero 𝓖₀ W St zv (D , refl , refl) = zv
  incE′ (suc j) {ev} {ac} 𝓖₀ W St zv (D , (x , C , c , o) , refl) =
    St c (aboveV x (λ t rt → let et′ = R→≈ rt ev ac ev ac (≅ᴵ-refl _) in ψ̄ t ev ac , et′ , F0ᵀ rt , run-≅ o et′))
  incE′ (lim f s) {ev} {ac} 𝓖₀ W St zv (D , (x , C , c , o) , refl) =
    St c (aboveV x (λ t rt → let et′ = R→≈ rt ev ac ev ac (≅ᴵ-refl _) in ψ̄ t ev ac , et′ , F0ᵀ rt , run-≅ o et′))

  mkZ : ∀ {c φ j i ℓ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} {ac : j <ᴵ ℓ} {𝓖′ : Cl i} {𝓖₀ : ClT c φ} → (i ≺ᴵ j ⊎ j ≅ᴵ i) → Wit i 𝓖′ →
        (∀ {O} → 𝓖′ O → 𝓖₀ (top O ev p)) → (∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ C′ → 𝓖₀ C) → ZT j {ev = ev} ac 𝓖₀
  mkZ {j = zero} (inj₁ (via e ())) w m cg
  mkZ {j = zero} {i = zero} (inj₂ z≅) wi m cg = cg tt (top idO) (m wi)
  mkZ {j = suc _} cc w m cg = tt
  mkZ {j = lim _ _} cc w m cg = tt

  T̄ : ∀ {c φ i ℓ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} {𝓖 : ClT c φ} {𝓖′ : Cl i} {x : O c φ} →
      (∀ {O} → 𝓖′ O → 𝓖 (top O ev p)) → (∀ {O} → 𝓖′ O → VT i O) → Wit i 𝓖′ → Gᵀ c 𝓖 x → Good true 𝓖′ (ψ̄ x ev p)
  chT : ∀ {c φ j i ℓ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} {𝓖 : ClT c φ} {𝓖′ : Cl i} {ac : ∀ {L₁} → Ev L₁ φ → j <ᴵ L₁} {f : Ordˢ j → O c φ} →
        (∀ {O} → 𝓖′ O → 𝓖 (top O ev p)) → (∀ {O} → 𝓖′ O → VT i O) → Wit i 𝓖′ → (i ≺ᴵ j ⊎ j ≅ᴵ i) →
        (𝓖₀ : ClT c φ) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Cx c φ → Obs j) →
        (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ runᶜ C (f u)) →
        (∀ (𝓔 : ClT c φ) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z → Good true (Inp j (W ⟪ 𝓔 ⟫)) z → Gᵀ c 𝓔 (f z)) →
        (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) →
        (∀ {C C′} → 𝓖₀ C → AboveV j C′ (W C) → 𝓖₀ C′) →
        (∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ C′ → 𝓖₀ C) →
        (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f z ⊑ᵗ f z′) →
        (∀ {z z′} → z ≅ˢ z′ → Rᵒ c c (f z) (f z′)) →
        Good true 𝓖′ (Ord₊ˢ.lim (λ m → ψ̄ (f (iter (λ w → ψ̄ (f w) ev (ac ev)) (Ωˢ j) m)) ev p))

  T̄ H H₂ w g0 = Good-mono H₂ (vΩ _)
  T̄ {i = i} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (gs {a = a} 𝓚 v g clk cgk ho) =
    bl (λ n → Good-mono (λ c → H₂ c , v (H c)) (proj₁ (AddM.iterA gv ew oa proj₁′ cgh clh hoh (hselfT i {𝓐 = ℋ} ew oa clh′ proj₁′ wℋ) n))) (rule4ᵒ ew)
    where
    ℋ : Cl i
    ℋ O = VT i O × 𝓚 (top O ev p)
    wℋ : Wit i ℋ
    wℋ = wit-map i (λ c → H₂ c , v (H c)) w
    ra = G→R g
    wv = ψ̄ a ev p
    ew : wv ≅ˢ wv
    ew = R→≈ ra ev p ev p (≅ᴵ-refl i)
    fw : Ωˢ i ⊑ᴱ wv
    fw = F0ᵀ ra
    oa : 𝟏 ⊑ᴱ wv
    oa = ⊑ᴱ-trans (Ω1ᴱ i) fw
    gv : Good true ℋ wv
    gv = T̄ {𝓖 = 𝓚} {𝓖′ = ℋ} proj₂ proj₁ wℋ g
    proj₁′ : ∀ {O} → ℋ O → Ctx O
    proj₁′ (t , c) = cxT i t
    cgh : ∀ {C C′} → Ctx C → C ≈ᵒ C′ → ℋ C′ → ℋ C
    cgh c₀ o (t , c) = cgT c₀ o t , cgk c₀ (top o) c
    clh : NZ i → ∀ {O C″} → ℋ O → FlOver wv O C″ → ℋ C″
    clh nz (t , c) f′ = clT ew fw nz t f′ , clk c (flo-overᵀ (cxo f′) (λ u ru G → flw f′ (ψ̄ u ev p) (R→≈ ru ev p ev p (≅ᴵ-refl i)) G))
    clh′ : NZ i → ∀ {O} → ℋ O → FlOver wv O (addo O wv (λ q → q)) → ℋ (addo O wv (λ q → q))
    clh′ nz h f′ = clh nz h f′
    hoh : ∀ {C} → ℋ C → Hon i wv C
    hoh h = hoT ew fw (proj₁ h)
  T̄ H H₂ w (gl f st) = bl (λ n → T̄ H H₂ w (f n)) (λ n → ψ̄-congᵒ (st n))
  T̄ {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (gŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) =
    bŝ (λ η O → 𝓑 η (top O ev p)) Bc (T̄ H H₂ w g₀)
       (λ η e w′ → T̄ {𝓖 = λ C → 𝓖 C × 𝓑 η C} {𝓖′ = λ O → 𝓖′ O × 𝓑 η (top O ev p)} (λ (c , b) → H c , b) (λ c → H₂ (proj₁ c)) w′ (gg η e))
       (R→≈ et ev p ev p (≅ᴵ-refl _)) (λ η e η′ e′ d → R→≈ (eg η e η′ e′ d) ev p ev p (≅ᴵ-refl _))
       (λ η e → ψ̄-congᵒ (m η e)) (λ η e η′ e′ h → ψ̄-congᵒ (mm η e η′ e′ h))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  T̄ H H₂ w (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
    bĉ ys hy dy G₀ l₀ Gg lE (T̄ H H₂ w go) (λ k → T̄ H H₂ w (gO k)) (ψ̄-congᵒ mo) (λ k → ψ̄-congᵒ (mO k))
  T̄ {ev = ev} {p = p} H H₂ w (gw {le = le} 𝓖₁ inc g) = T̄ {ev = le ev} {p = p} {𝓖 = 𝓖₁} (λ c → inc (H c)) H₂ w g
  T̄ {c = c} {φ = φ ⊔ fk zero} {i = i} {ℓ = ℓ} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (gclo {t = t} {g = g} 𝓖ᵗ inc₁ 𝓖ᵍ Bcᵍ gt gg rt rg m mm dt dg ch₀ chS) =
    bŝ 𝓑
       (λ {η} {η′} {O} eq (x , b) → x , λ e′ → Bcᵍ eq x (top (ctx-refl O x)) (b (⊑ᴵ-≅ʳ e′ (≅ᴵ-sym eq))))
       (T̄ (λ c₁ → inc₁ (H c₁)) H₂ w gt)
       (λ η e w′ → T̄ {ev = evη η e} {p = tg η e} {𝓖 = 𝓖ᵍ η} {𝓖′ = λ O → 𝓖′ O × 𝓑 η O} (λ (c₁ , (x , b)) → b e) (λ c₁ → H₂ (proj₁ c₁)) w′ (gg η))
       (R→≈ rt ev p ev p (≅ᴵ-refl i))
       (λ η e η′ e′ d → R→≈ (rg η η′ d) (evη η e) (tg η e) (evη η′ e′) (tg η′ e′) (≅ᴵ-refl i))
       (λ η e → ψ̄-congᵒ (m η (one⊑η η e)))
       (λ η e η′ e′ u → ψ̄-congᵒ (mm η η′ (one⊑η η e) u))
       (λ {O} c₁ G → bd⊑ G (readT _ (H₂ c₁) (R→≈ rt ev p ev p (≅ᴵ-refl i)) (F0ᵀ rt) G) (dt (inc₁ (H c₁)) G))
       (λ {O} η e c₁ (x , b) G → bd⊑ G (readT _ (H₂ c₁) (R→≈ (rg η η (≅ᴵ-refl η)) (evη η e) (tg η e) (evη η e) (tg η e) (≅ᴵ-refl i)) (F0ᵀ (rg η η (≅ᴵ-refl η))) G) (dg η (b e) G))
       (λ {O} c₁ G → cxT i (H₂ c₁) , λ e → ch₀ (inc₁ (H c₁)) G (cxT i (H₂ c₁)) (top (ctx-refl O (cxT i (H₂ c₁)))))
       (λ {O} η e c₁ (x , b) G → x , λ e′ → chS η (b e) G x (top (ctx-refl O x)))
    where
    B : Top i ℓ (φ ⊔ fk zero)
    B = bound (φ ⊔ fk zero) ev p
    Lη : ∀ η → Bd B ⊑ᴵ η → Ordᴵ
    Lη η e = Mlev (Fc B) (suc η) (FB B e)
    evη : ∀ η (e : Bd B ⊑ᴵ η) → Ev (Lη η e) (φ ⊔ fk η)
    evη η e = liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)
    tg : ∀ η (e : Bd B ⊑ᴵ η) → i <ᴵ Lη η e
    tg η e = lim 0 (iF B)
    𝓑 : Ordᴵ → Cl i
    𝓑 η O = Ctx O × (∀ (e : Bd B ⊑ᴵ η) → 𝓖ᵍ η (top O (evη η e) (tg η e)))
    one⊑η : ∀ η → Bd B ⊑ᴵ η → suc zero ⊑ᴵ η
    one⊑η η e = ⊑ᴵ-trans (s⊑ z≅ (proj₂ (evF B) zero)) (⊑ᴵ-trans (FM B) e)
    bd⊑ : ∀ {O : Obs i} {X : Ordˢ i} (G : Goodᴺ (toZ (run O X))) → suc i ⊑ᴵ lvG G → (∀ {K} (k : InF K φ) → Dem (lvG G) k) → Bd B ⊑ᴵ lvG G
    bd⊑ G (s⊑ e q) dm = ubd B (via e q) (λ { (inl k) → dm k ; (inr ink) → inj₂ z≅ })
  T̄ {c = c} {φ = φ} {i = i} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ wi (gi {j = j} {ac = ac} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) with <ᴵ-dec (ac ev) p
  ... | injᵃ (via e r) =
    bi (λ O → 𝓖₀ (top O ev p) × VT i O) (λ c₁ → inc₀ (H c₁) , H₂ c₁) (λ O → tr⁻o (W (top O ev p)) e)
       (λ {O} (c₁ , v) u eu → subst (λ y → run (W (top O ev p)) (tr⁻ˢ e u) ≅ˢ run O (ψ̄ (f (tr⁻ˢ e y)) ev p)) (sym (out-intoˢ (<→◃ r) u))
           (Wf c₁ (tr⁻ˢ e u) (self-tr⁻ˢ e eu)))
       (λ 𝓔′ inc″ z ez g → subst (λ y → Good true 𝓔′ (ψ̄ (f (tr⁻ˢ e y)) ev p)) (sym (out-intoˢ (<→◃ r) z))
           (T̄ {𝓖 = 𝓔₀ 𝓔′} {𝓖′ = 𝓔′} (λ c₁ → _ , c₁ , refl) (λ c₁ → proj₂ (inc″ c₁)) (wit-nz i (NZ-of r))
              (hb (𝓔₀ 𝓔′) (λ { (O , c₁ , refl) → proj₁ (inc″ c₁) }) (tr⁻ˢ e z) (self-tr⁻ˢ e ez)
                  (Bb e (W ⟪ 𝓔₀ 𝓔′ ⟫) ((λ O → tr⁻o (W (top O ev p)) e) ⟨ 𝓔′ ⟩)
                      (λ { (x , _ , (O , c₁ , refl) , o) → x , x , O , c₁ , tr⁻o o }) ez (Gd→Good (<→◃ r) g)))))
       (λ {O} (c₁ , v) → vis (cx (Wv c₁))
           (λ {b′} h t et fl G →
           cp (Wv c₁) (≺ᴵ-respʳ h (s≅ (≅ᴵ-sym e))) (tr⁻ˢ e t) (self-tr⁻ˢ e et) (λ ex₀ h₀ → fl-tr⁻ e ex₀ (fl ex₀ h₀)) G))
       (λ {O} {C″} (c₁ , v) (above cx′ wrap) →
          St c₁ (aboveV cx′ (λ t rt →
            let t′ = ψ̄ t ev p
                et′ = R→≈ rt ev p ev p (≅ᴵ-refl i)
                u = proj₁ (wrap t′ et′)
                eu = proj₁ (proj₂ (wrap t′ et′))
                fu = proj₁ (proj₂ (proj₂ (wrap t′ et′)))
                d = proj₂ (proj₂ (proj₂ (wrap t′ et′)))
            in tr⁻ˢ e u , self-tr⁻ˢ e eu , fl-tr⁻ e (Ωˢ-refl j) (⊑ᴱ-trans (≅→⊑ᴱ (Ωˢ-≅ e)) fu) , d)) ,
          frV (NZ-of r) (vis cx′
            (λ {b′} h t et fl G →
            let u = proj₁ (wrap t et)
                eu = proj₁ (proj₂ (wrap t et))
                d = proj₂ (proj₂ (proj₂ (wrap t et)))
                d₂ = Wf c₁ (tr⁻ˢ e u) (self-tr⁻ˢ e eu)
                ey = rf (self-tr⁻ˢ e eu)
            in pull (≅ˢ-trans d d₂)
                    (cp (toV (NZ-of r) v) h _ (R→≈ ey ev p ev p (≅ᴵ-refl i))
                        (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ h) (F0ᵀ ey))) G)))
       (λ c₀ o (c₁ , v) → cg c₀ (top o) c₁ , cgT c₀ o v)
       (λ {z} {z′} h₀ → subst₂ (λ y y′ → ψ̄ (f (tr⁻ˢ e y)) ev p ⊑ᵒ ψ̄ (f (tr⁻ˢ e y′)) ev p)
            (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (ψ̄-congᵒ (hm (tr⁻-cong h₀))))
    where
    𝓔₀ : Cl i → ClT c φ
    𝓔₀ 𝓔′ C = Σ _ λ O → 𝓔′ O × (C ≡ top O ev p)
  ... | injᵇ cc = chT {ac = ac} H H₂ wi (inj₁ cc) 𝓖₀ inc₀ W Wf hb Wv St cg hm rf
  ... | injᶜ cc = chT {ac = ac} H H₂ wi (inj₂ cc) 𝓖₀ inc₀ W Wf hb Wv St cg hm rf
  T̄ {c = c} {φ = φ} {i = i} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ wi (gΩ {m = m} {fe = fe} {r = r} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
    bl (λ n → T̄ {ev = ev , ev} {p = p} {𝓖 = 𝓖₀ φ} {𝓖′ = 𝓖′} (λ {O} c₁ → inc₀ φ (H c₁) (cxT i (H₂ c₁)) (top (ctx-refl O (cxT i (H₂ c₁))))) H₂ wi
                   (hb 𝓖₀ (λ ξ c₁ → c₁) φ (zt n) (G→R (zG n)) (intoG (<→◃ r) (zG n))))
       (λ n → ψ̄-congᵒ (hm (zm n)))
    where
    f : O m φ → O m φ
    f z = owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))
    zt : ℕ → O m φ
    zt = chainᵒ fe f
    𝓖₆ : ClT m (Fl ⊔ (φ ⊔ φ))
    𝓖₆ E = 𝓥 E × 𝓖₀ φ (pψ r E)
    zG : ∀ n → Gᵀ m (W φ ⟪ 𝓖₀ φ ⟫ᵀ) (zt n)
    zG zero = gw 𝓥 (λ {D} (x , _) → Ctx-wkC D x) (Ω̇G _)
    zG (suc n) =
      gw 𝓖₆ (λ {D} (x , C , c₁ , o) → Ctx-wkC D x , St φ c₁ (aboveΩ (Ctx-wkC D x) (λ t₁ rt →
             owk (λ v → fe v , (v , v)) (ψᵒ r t₁) , rwk (R-ψ r r (≅ᴵ-refl _) rt) , (λ _ h₁ → wk-rᵀ (P0ᵀ {q = r} rt h₁)) ,
             subst (λ v₁ → v₁ ≅ˢ runᶜ (W φ C) (owk (λ v → fe v , (v , v)) (ψᵒ r t₁))) (sym (run-wkC (λ v → fe v , (v , v)) D (ψᵒ r t₁))) (runᶜ-≅ o (rwk (R-ψ r r (≅ᴵ-refl _) rt))))))
         (Psi r {𝓖 = 𝓖₆} {𝓧 = 𝓖₀ φ} proj₂ proj₁ (hb 𝓖₀ (λ ξ c₁ → c₁) φ (zt n) (G→R (zG n)) (intoG (<→◃ r) (zG n))))
    zm : ∀ n → zt n ⊑ᵗ zt (suc n)
    zm zero = wk-rᵗ (⊑ᵀ→ᵗ (rwk (RΩ̇ (≅ᴵ-refl m))) (P0ᵀ {q = r} (rf φ φ (∼ᶠ-refl φ) (zt 0) (zt 0) (G→R (zG 0))) (wk-lᵀ (R→⊑ᵀ (RΩ̇ (≅ᴵ-refl m))))))
    zm (suc n) = wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = r} (hm (zm n))))

  chT {c = c} {φ = φ} {j = j} {i = i} {ℓ = ℓ} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} {ac = ac₀} {f = f} H H₂ wi cc 𝓖₀ inc₀ W Wf hb Wv St cg hm rf =
    bl (λ n → T̄ H H₂ wi
          (hb 𝓖 inc₀ (zt n) (csim n) (Good-mono (inp-map j (λ { (x , C , c₁ , o) → x , C , inc₀ c₁ , o })) (chG n))))
       (λ n → ψ̄-congᵒ (hm (chst n)))
    where
    ac : j <ᴵ ℓ
    ac = ac₀ ev
    zt : ℕ → Ordˢ j
    zt = iter (λ w → ψ̄ (f w) ev ac) (Ωˢ j)
    csim : ∀ n → zt n ≅ˢ zt n
    csim zero = Ωˢ-refl j
    csim (suc n) = R→≈ (rf (csim n)) ev ac ev ac (≅ᴵ-refl j)
    chst : ∀ n → zt n ⊑ᵒ zt (suc n)
    chst zero = ⊑ᴱ→ᵒ (Ωˢ-refl j) (F0ᵀ (rf (Ωˢ-refl j)))
    chst (suc n) = ψ̄-congᵒ (hm (chst n))
    𝓔₂ : ClT c φ
    𝓔₂ C′ = Σ _ λ D → Inp j (W ⟪ 𝓖₀ ⟫) D × (C′ ≡ top D ev ac)
    incE : ∀ {C} → 𝓔₂ C → 𝓖₀ C
    incE = incE′ j {ev = ev} {ac = ac} 𝓖₀ W St (mkZ {p = p} cc wi (λ c₁ → inc₀ (H c₁)) cg)
    chG : ∀ n → Good true (Inp j (W ⟪ 𝓖₀ ⟫)) (zt n)
    chG zero = Good-mono (inpVis j W Wv) (Ωg j)
    chG (suc n) = T̄ {ev = ev} {p = ac} {𝓖 = 𝓔₂} {𝓖′ = Inp j (W ⟪ 𝓖₀ ⟫)} (λ d → _ , d , refl) (visD j W Wv) (witI j {W ⟪ 𝓖₀ ⟫})
          (hb 𝓔₂ incE (zt n) (csim n) (Good-mono (inp-map j (λ { (x , C , e′ , o) → x , C , incE e′ , o })) (chG n)))
```
