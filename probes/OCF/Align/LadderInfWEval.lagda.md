> **机械克隆, 验收用.** 由 `LadderInfEval` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 求值定理

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFEval](LadderNFEval.lagda.md) 生成, 下面的说明是原文件的. `EvalM.T̄ : Gq g m c 𝓖 x → Good true 𝓖′ (ψ̄ᵠ ok e x ev p)`, 只要 $O\in\mathcal G'$ 推出 `top O …` ∈ $\mathcal G$, $O\in$ `VT i`. 与 `OCF.Free.Eval` 同形. `gcl`: 高度 $n$ 的闭包, 目标是可数的, 界只读地板 (`bd⊑`). `gΩ↓`: 走 `Ψ` 的链. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfWEval (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Align.LadderNFWEq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅)
open import OCF.Align.LadderNFWFloor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Align.LadderNFWForce using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Align.LadderNFWFT using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderInfWTree 𝕊
open import OCF.Align.LadderInfWRel 𝕊
open import OCF.Align.LadderInfWCx 𝕊
open import OCF.Align.LadderInfWRules 𝕊
open import OCF.Align.LadderInfWRules2 𝕊
open import OCF.Align.LadderInfWRules3 𝕊
open import OCF.Align.LadderInfWStrict 𝕊
open import OCF.Align.LadderInfWStrict2 𝕊
open import OCF.Align.LadderInfWClass 𝕊
open import OCF.Align.LadderInfWClassF 𝕊
open import OCF.Align.LadderInfWGood 𝕊
open import OCF.Align.LadderInfWVis 𝕊
open import OCF.Align.LadderInfWIota 𝕊
open import OCF.Align.LadderInfWAdd 𝕊
open import OCF.Align.LadderInfWTr 𝕊
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.LadderInfWPsi 𝕊
open import OCF.Align.LadderInfWRead 𝕊
open import OCF.Align.LadderNFWFloor using (bound; Top; Bd; Fc; ubd; evF; iF; FM; FB; liftEv; bound-≅)
open import OCF.Align.LadderNFWAux using (Mlev)
open import OCF.Align.LadderNFWEq using (⊑ᴵ-≅ʳ; ⊑ᴵ-≅ˡ)
open import OCF.Align.LadderInfWPsiH 𝕊
-- (同上)
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.LadderNFWEq using (≅ᴵ→⊑ᴵ; self-trˢ; self-tr⁻ˢ; ≅-tr⁻ˢ; tr⁻ˢ-≅; Ωˢ-≅; Ωˢ-refl; addˢ-≅)
open Ord-Ord using (iter)
open RestrQ
```

## §1 目标类 `VisT` 的封闭性

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

inpVis : ∀ {m c φ χ} j {𝓖₀ : ClT m c φ χ} (W : Cx m c φ χ → Obs j) → (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → ∀ {D} → Inp j (W ⟪ 𝓖₀ ⟫) D → Vis j D
inpVis zero W Wv refl = vis tt (λ { (via _ ()) })
inpVis (suc j) W Wv (x , C , c , o) = Vis-≈ x o (Vis-mono ≺-suc (Wv c))
inpVis (lim f s) W Wv (x , C , c , o) = Vis-≈ x o (Vis-mono ≺-suc (Wv c))

visD : ∀ {m c φ χ} j {𝓖₀ : ClT m c φ χ} (W : Cx m c φ χ → Obs j) → (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → ∀ {D′} → Inp j (W ⟪ 𝓖₀ ⟫) D′ → VT j D′
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
module EvalM (Ω̇G : ∀ g m k → Gq (inp g) m k (KQ (inp g) k) (Ω̇ m k)) where
  open PsiM Ω̇G
  open PsiHM Ω̇G

  ZT : ∀ {m c φ χ ℓ w} j {ev : Ev ℓ φ} → j <ᴵ ℓ → (ok : Ok w) → Eh h₀ m w χ → ClT m c φ χ → Set
  ZT zero {ev} ac ok e 𝓖₀ = 𝓖₀ (top idO ev ac ok e)
  ZT (suc _) ac ok e 𝓖₀ = ⊤
  ZT (lim _ _) ac ok e 𝓖₀ = ⊤

  incE′ : ∀ {m c φ χ ℓ w} j {ev : Ev ℓ φ} {ac : j <ᴵ ℓ} {ok : Ok w} {e : Eh h₀ m w χ} (𝓖₀ : ClT m c φ χ) (W : Cx m c φ χ → Obs j) →
          (∀ {C C′} → 𝓖₀ C → AboveV j C′ (W C) → Nd C′ → 𝓖₀ C′) → ZT j {ev = ev} ac ok e 𝓖₀ →
          ∀ {C} → (Σ _ λ D → Inp j (W ⟪ 𝓖₀ ⟫) D × (C ≡ top D ev ac ok e)) → 𝓖₀ C
  incE′ zero 𝓖₀ W St zv (D , refl , refl) = zv
  incE′ (suc j) {ev} {ac} {ok} {e} 𝓖₀ W St zv (D , (x , C , c , o) , refl) =
    St c (aboveV x (λ t rt → let et′ = R→≈ᵠ rt ok e ok e ev ac ev ac (≅ᴵ-refl _) in ψ̄ᵠ ok e t ev ac , et′ , F0ᵀ rt , run-≅ o et′)) tt
  incE′ (lim f s) {ev} {ac} {ok} {e} 𝓖₀ W St zv (D , (x , C , c , o) , refl) =
    St c (aboveV x (λ t rt → let et′ = R→≈ᵠ rt ok e ok e ev ac ev ac (≅ᴵ-refl _) in ψ̄ᵠ ok e t ev ac , et′ , F0ᵀ rt , run-≅ o et′)) tt

  mkZ : ∀ {m c φ χ j i ℓ w} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} {ac : j <ᴵ ℓ} {ok : Ok w} {e : Eh h₀ m w χ} {𝓖′ : Cl i} {𝓖₀ : ClT m c φ χ} → (i ≺ᴵ j ⊎ j ≅ᴵ i) → Wit i 𝓖′ →
        (∀ {O} → 𝓖′ O → 𝓖₀ (top O ev p ok e)) → (∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ C′ → 𝓖₀ C) → ZT j {ev = ev} ac ok e 𝓖₀
  mkZ {j = zero} (inj₁ (via e ())) w m cg
  mkZ {j = zero} {i = zero} (inj₂ z≅) wi m cg = cg tt (top idO) (m wi)
  mkZ {j = suc _} cc w m cg = tt
  mkZ {j = lim _ _} cc w m cg = tt

  T̄ : ∀ {g m c φ χ i ℓ w} {ok : Ok w} {e : Eh h₀ m w χ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} {𝓖 : ClT m c φ χ} {𝓖′ : Cl i} {x : Q m c φ χ} →
      (∀ {O} → 𝓖′ O → 𝓖 (top O ev p ok e)) → (∀ {O} → 𝓖′ O → VT i O) → Wit i 𝓖′ → Gq g m c 𝓖 x → Good true 𝓖′ (ψ̄ᵠ ok e x ev p)
  chT : ∀ {g m c φ χ j i ℓ w} {ok : Ok w} {e : Eh h₀ m w χ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} {𝓖 : ClT m c φ χ} {𝓖′ : Cl i} {ac : ∀ {L₁} → Ev L₁ φ → j <ᴵ L₁} {f : Ordˢ j → Q m c φ χ} →
        (∀ {O} → 𝓖′ O → 𝓖 (top O ev p ok e)) → (∀ {O} → 𝓖′ O → VT i O) → Wit i 𝓖′ → (i ≺ᴵ j ⊎ j ≅ᴵ i) →
        (𝓖₀ : ClT m c φ χ) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Cx m c φ χ → Obs j) →
        (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ runᶜ C (f u)) →
        (∀ (𝓔 : ClT m c φ χ) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z → Good true (Inp j (W ⟪ 𝓔 ⟫)) z → Gq g m c 𝓔 (f z)) →
        (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) →
        (∀ {C C′} → 𝓖₀ C → AboveV j C′ (W C) → Nd C′ → 𝓖₀ C′) →
        (∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ C′ → 𝓖₀ C) →
        (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f z ⊑ᵗ f z′) →
        (∀ {z z′} → z ≅ˢ z′ → Rq m c c (f z) (f z′)) →
        Good true 𝓖′ (Ord₊ˢ.lim (λ n → ψ̄ᵠ ok e (f (iter (λ w₁ → ψ̄ᵠ ok e (f w₁) ev (ac ev)) (Ωˢ j) n)) ev p))

  T̄ H H₂ w g0 = Good-mono H₂ (vΩ _)
  T̄ {i = i} {ok = ok} {e = e} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (gs {a = a} 𝓚 v k clk cgk ho hq) =
    bl (λ n → Good-mono (λ c → H₂ c , v (H c)) (proj₁ (AddM.iterA gv ew oa proj₁′ cgh clh hoh (hselfT i {𝓐 = ℋ} ew oa clh′ proj₁′ wℋ) n))) (rule4ᵒ ew)
    where
    ℋ : Cl i
    ℋ O = VT i O × 𝓚 (top O ev p ok e)
    wℋ : Wit i ℋ
    wℋ = wit-map i (λ c → H₂ c , v (H c)) w
    ra = G→R k
    wv = ψ̄ᵠ ok e a ev p
    ew : wv ≅ˢ wv
    ew = R→≈ᵠ ra ok e ok e ev p ev p (≅ᴵ-refl i)
    fw : Ωˢ i ⊑ᴱ wv
    fw = F0ᵀ ra
    oa : 𝟏 ⊑ᴱ wv
    oa = ⊑ᴱ-trans (Ω1ᴱ i) fw
    gv : Good true ℋ wv
    gv = T̄ {𝓖 = 𝓚} {𝓖′ = ℋ} proj₂ proj₁ wℋ k
    proj₁′ : ∀ {O} → ℋ O → Ctx O
    proj₁′ (t , c) = cxT i t
    cgh : ∀ {C C′} → Ctx C → C ≈ᵒ C′ → ℋ C′ → ℋ C
    cgh c₀ o (t , c) = cgT c₀ o t , cgk c₀ (top o) c
    clh : NZ i → ∀ {O C″} → ℋ O → FlOver wv O C″ → ℋ C″
    clh nz (t , c) f′ = clT ew fw nz t f′ , clk c (flo-overᵀ (cxo f′) (λ u ru G → flw f′ (ψ̄ᵠ ok e u ev p) (R→≈ᵠ ru ok e ok e ev p ev p (≅ᴵ-refl i)) G)) (ndg _ tt)
    clh′ : NZ i → ∀ {O} → ℋ O → FlOver wv O (addo O wv (λ q → q)) → ℋ (addo O wv (λ q → q))
    clh′ nz h f′ = clh nz h f′
    hoh : ∀ {C} → ℋ C → Hon i wv C
    hoh h = hoT ew fw (proj₁ h)
  T̄ H H₂ w (gl f st) = bl (λ n → T̄ H H₂ w (f n)) (λ n → ψ̄-congᵒ (st n))
  T̄ {ok = ok} {e = e} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (gŝ 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) =
    bŝ (λ η O → 𝓑 η (top O ev p ok e)) Bc (T̄ H H₂ w g₀′)
       (λ η d w′ → T̄ {𝓖 = λ C → 𝓖 C × 𝓑 η C} {𝓖′ = λ O → 𝓖′ O × 𝓑 η (top O ev p ok e)} (λ (c , b) → H c , b) (λ c → H₂ (proj₁ c)) w′ (gg η d))
       (R→≈ᵠ et ok e ok e ev p ev p (≅ᴵ-refl _)) (λ η d η′ d′ d₂ → R→≈ᵠ (eg η d η′ d′ d₂) ok e ok e ev p ev p (≅ᴵ-refl _))
       (λ η d → ψ̄-congᵒ (m₁ η d)) (λ η d η′ d′ h → ψ̄-congᵒ (mm η d η′ d′ h))
       (λ c G → d₀ (H c) G) (λ η d c b G → dE η d (H c) b G) (λ c G → ch₀ (H c) G) (λ η d c b G → chS η d (H c) b G)
  T̄ H H₂ w (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
    bĉ ys hy dy G₀ l₀ Gg lE (T̄ H H₂ w go) (λ k → T̄ H H₂ w (gO k)) (ψ̄-congᵒ mo) (λ k → ψ̄-congᵒ (mO k))
  T̄ {ok = ok} {e = e} {ev = ev} {p = p} H H₂ w (gw {le = le} {lc = lc} 𝓖₁ inc k) = T̄ {ok = ok} {e = λ i h r → lc i r (e i h r)} {ev = le ev} {p = p} {𝓖 = 𝓖₁} (λ c → inc (H c)) H₂ w k
  T̄ {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (gm zc rz₁ gx) = T̄ {𝓖 = λ C → 𝓖 C × Nd C} {𝓖′ = 𝓖′} (λ c → H c , tt) H₂ w gx
  T̄ {m = m} {c = c} {φ = φ ⊔ fk zero} {χ = χ} {i = i} {ℓ = ℓ} {ok = ok} {e = e} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (gclo {t = t} {h = g} 𝓖ᵗ inc₁ cgᵗ 𝓖ᵍ Bcᵍ gt gg rt rg m₁ mm dt dg ch₀ chS) =
    bŝ 𝓑
       (λ {η} {η′} {O} eq (x , b) → x , λ e′ → Bcᵍ eq x (top (ctx-refl O x)) (b (⊑ᴵ-≅ʳ e′ (≅ᴵ-sym eq))))
       (T̄ (λ c₁ → inc₁ (H c₁)) H₂ w gt)
       (λ η e₁ w′ → T̄ {ok = ok} {e = e} {ev = evη φ B η e₁} {p = tg η e₁} {𝓖 = 𝓖ᵍ η} {𝓖′ = λ O → 𝓖′ O × 𝓑 η O} (λ (c₁ , (x , b)) → b e₁) (λ c₁ → H₂ (proj₁ c₁)) w′ (gg η))
       (R→≈ᵠ rt ok e ok e ev p ev p (≅ᴵ-refl i))
       (λ η e₁ η′ e′ d → R→≈ᵠ (rg η η′ d) ok e ok e (evη φ B η e₁) (tg η e₁) (evη φ B η′ e′) (tg η′ e′) (≅ᴵ-refl i))
       (λ η e₁ → ψ̄-congᵒ (m₁ η (one⊑B B e₁)))
       (λ η e₁ η′ e′ u → ψ̄-congᵒ (mm η η′ (one⊑B B e₁) u))
       (λ {O} c₁ G → bd⊑ B (readT _ (H₂ c₁) (R→≈ᵠ rt ok e ok e ev p ev p (≅ᴵ-refl i)) (F0ᵀ rt) G) (dt (inc₁ (H c₁)) G))
       (λ {O} η e₁ c₁ (x , b) G → bd⊑ B (readT _ (H₂ c₁) (R→≈ᵠ (rg η η (≅ᴵ-refl η)) ok e ok e (evη φ B η e₁) (tg η e₁) (evη φ B η e₁) (tg η e₁) (≅ᴵ-refl i)) (F0ᵀ (rg η η (≅ᴵ-refl η))) G) (dg η (b e₁) G))
       (λ {O} c₁ G → cxT i (H₂ c₁) , λ e₁ → ch₀ (inc₁ (H c₁)) G (cxT i (H₂ c₁)) (top (ctx-refl O (cxT i (H₂ c₁)))))
       (λ {O} η e₁ c₁ (x , b) G → x , λ e′ → chS η (b e₁) G x (top (ctx-refl O x)))
    where
    B : Top i ℓ (φ ⊔ fk zero)
    B = bound (φ ⊔ fk zero) ev p
    Lη : ∀ η → Bd B ⊑ᴵ η → Ordᴵ
    Lη η e₁ = Mlev (Fc B) (suc η) (FB B e₁)
    tg : ∀ η (e₁ : Bd B ⊑ᴵ η) → i <ᴵ Lη η e₁
    tg η e₁ = lim 0 (iF B)
    𝓑 : Ordᴵ → Cl i
    𝓑 η O = Ctx O × (∀ (e₁ : Bd B ⊑ᴵ η) → 𝓖ᵍ η (top O (evη φ B η e₁) (tg η e₁) ok e))
  T̄ {m = m} {c = c} {φ = φ} {χ = χ} {i = i} {ℓ = ℓ} {w = w} {ok = ok} {e = e} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ wi (gcl {n = n} {q = q} {ψ = ψ} {s = s} {t = t} {h = g} 𝓖ᵗ inc₁ 𝓖ᵍ Bcᵍ gt gg rt rg m₁ mm dt dg ch₀ chS) =
    bŝ 𝓑
       (λ {η} {η′} {O} eq (x , b) → x , λ d′ → Bcᵍ eq x (top (ctx-refl O x)) (b (⊑ᴵ-≅ʳ d′ (≅ᴵ-sym eq))))
       (T̄ (λ c₁ → inc₁ (H c₁)) H₂ wi gt)
       (λ η d w′ → T̄ {ok = ok′ η d} {e = e′ η d} {ev = ev} {p = p} {𝓖 = 𝓖ᵍ η} {𝓖′ = λ O → 𝓖′ O × 𝓑 η O} (λ (c₁ , (x , b)) → b d) (λ c₁ → H₂ (proj₁ c₁)) w′ (gg η))
       (R→≈ᵠ rt ok e ok e ev p ev p (≅ᴵ-refl i))
       (λ η d η′ d′ d₂ → R→≈ᵠ (rg η η′ d₂) (ok′ η d) (e′ η d) (ok′ η′ d′) (e′ η′ d′) ev p ev p (≅ᴵ-refl i))
       (λ η d → ψ̄-congᵒ (m₁ η (one⊑B B d)))
       (λ η d η′ d′ u → ψ̄-congᵒ (mm η η′ (one⊑B B d) u))
       (λ {O} c₁ G → bd⊑ B (read1 O (cxT i (H₂ c₁)) _ (R→≈ᵠ rt ok e ok e ev p ev p (≅ᴵ-refl i)) (⊑ᴱ-trans (Ω1ᴱ i) (F0ᵀ rt)) G) (dt (inc₁ (H c₁)) G))
       (λ {O} η d c₁ (x , b) G → bd⊑ B (read1 O x _ (R→≈ᵠ (rg η η (≅ᴵ-refl η)) (ok′ η d) (e′ η d) (ok′ η d) (e′ η d) ev p ev p (≅ᴵ-refl i)) (⊑ᴱ-trans (Ω1ᴱ i) (F0ᵀ (rg η η (≅ᴵ-refl η)))) G) (dg η (b d) G))
       (λ {O} c₁ G → cxT i (H₂ c₁) , λ d → ch₀ (inc₁ (H c₁)) G (cxT i (H₂ c₁)) (top (ctx-refl O (cxT i (H₂ c₁)))))
       (λ {O} η d c₁ (x , b) G → x , λ d′ → chS η (b d) G x (top (ctx-refl O x)))
    where
    B = bound (ψ ⊔ fk zero) (s (e n (Hi-0 n) q)) (zr ok n)
    Lw : ∀ η → Bd B ⊑ᴵ η → Ht → Ordᴵ
    Lw η d = upd w n (Mlev (Fc B) (suc η) (FB B d))
    ok′ : ∀ η (d : Bd B ⊑ᴵ η) → Ok (Lw η d)
    ok′ η d = upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))
    e′ : ∀ η (d : Bd B ⊑ᴵ η) → Eh h₀ m (Lw η d) (upd χ n (ψ ⊔ fk η))
    e′ η d i₁ h r = upd-ev n i₁ w χ (evη ψ B η d) (e i₁ h r)
    𝓑 : Ordᴵ → Cl i
    𝓑 η O = Ctx O × (∀ (d : Bd B ⊑ᴵ η) → 𝓖ᵍ η (top O ev p (ok′ η d) (e′ η d)))
  T̄ {m = m} {c = c} {φ = φ} {χ = χ} {i = i} {ok = ok} {e = e} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ wi (gi {j = j} {ac = ac} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) with <ᴵ-dec (ac ev) p
  ... | injᵃ (via e₁ r) =
    bi (λ O → 𝓖₀ (top O ev p ok e) × VT i O) (λ c₁ → inc₀ (H c₁) , H₂ c₁) (λ O → tr⁻o (W (top O ev p ok e)) e₁)
       (λ {O} (c₁ , v) u eu → subst (λ y → run (W (top O ev p ok e)) (tr⁻ˢ e₁ u) ≅ˢ run O (ψ̄ᵠ ok e (f (tr⁻ˢ e₁ y)) ev p)) (sym (out-intoˢ (<→◃ r) u))
           (Wf c₁ (tr⁻ˢ e₁ u) (self-tr⁻ˢ e₁ eu)))
       (λ 𝓔′ inc″ z ez gz → subst (λ y → Good true 𝓔′ (ψ̄ᵠ ok e (f (tr⁻ˢ e₁ y)) ev p)) (sym (out-intoˢ (<→◃ r) z))
           (T̄ {𝓖 = 𝓔₀ 𝓔′} {𝓖′ = 𝓔′} (λ c₁ → _ , c₁ , refl) (λ c₁ → proj₂ (inc″ c₁)) (wit-nz i (NZ-of r))
              (hb (𝓔₀ 𝓔′) (λ { (O , c₁ , refl) → proj₁ (inc″ c₁) }) (tr⁻ˢ e₁ z) (self-tr⁻ˢ e₁ ez)
                  (Bb e₁ (W ⟪ 𝓔₀ 𝓔′ ⟫) ((λ O → tr⁻o (W (top O ev p ok e)) e₁) ⟨ 𝓔′ ⟩)
                      (λ { (x , _ , (O , c₁ , refl) , o) → x , x , O , c₁ , tr⁻o o }) ez (Gd→Good (<→◃ r) gz)))))
       (λ {O} (c₁ , v) → vis (cx (Wv c₁))
           (λ {b′} h t et fl G →
           cp (Wv c₁) (≺ᴵ-respʳ h (s≅ (≅ᴵ-sym e₁))) (tr⁻ˢ e₁ t) (self-tr⁻ˢ e₁ et) (λ ex₀ h₀ → fl-tr⁻ e₁ ex₀ (fl ex₀ h₀)) G))
       (λ {O} {C″} (c₁ , v) (above cx′ wrap) →
          St c₁ (aboveV cx′ (λ t rt →
            let t′ = ψ̄ᵠ ok e t ev p
                et′ = R→≈ᵠ rt ok e ok e ev p ev p (≅ᴵ-refl i)
                u = proj₁ (wrap t′ et′)
                eu = proj₁ (proj₂ (wrap t′ et′))
                fu = proj₁ (proj₂ (proj₂ (wrap t′ et′)))
                d = proj₂ (proj₂ (proj₂ (wrap t′ et′)))
            in tr⁻ˢ e₁ u , self-tr⁻ˢ e₁ eu , fl-tr⁻ e₁ (Ωˢ-refl j) (⊑ᴱ-trans (≅→⊑ᴱ (Ωˢ-≅ e₁)) fu) , d)) (ndg _ tt) ,
          frV (NZ-of r) (vis cx′
            (λ {b′} h t et fl G →
            let u = proj₁ (wrap t et)
                eu = proj₁ (proj₂ (wrap t et))
                d = proj₂ (proj₂ (proj₂ (wrap t et)))
                d₂ = Wf c₁ (tr⁻ˢ e₁ u) (self-tr⁻ˢ e₁ eu)
                ey = rf (self-tr⁻ˢ e₁ eu)
            in pull (≅ˢ-trans d d₂)
                    (cp (toV (NZ-of r) v) h _ (R→≈ᵠ ey ok e ok e ev p ev p (≅ᴵ-refl i))
                        (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ h) (F0ᵀ ey))) G)))
       (λ c₀ o (c₁ , v) → cg c₀ (top o) c₁ , cgT c₀ o v)
       (λ {z} {z′} h₀ → subst₂ (λ y y′ → ψ̄ᵠ ok e (f (tr⁻ˢ e₁ y)) ev p ⊑ᵒ ψ̄ᵠ ok e (f (tr⁻ˢ e₁ y′)) ev p)
            (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (ψ̄-congᵒ (hm (tr⁻-cong h₀))))
    where
    𝓔₀ : Cl i → ClT m c φ χ
    𝓔₀ 𝓔′ C = Σ _ λ O → 𝓔′ O × (C ≡ top O ev p ok e)
  ... | injᵇ cc = chT {ac = ac} H H₂ wi (inj₁ cc) 𝓖₀ inc₀ W Wf hb Wv (λ c₁ a₁ n₁ → St c₁ a₁ (ndg _ n₁)) cg hm rf
  ... | injᶜ cc = chT {ac = ac} H H₂ wi (inj₂ cc) 𝓖₀ inc₀ W Wf hb Wv (λ c₁ a₁ n₁ → St c₁ a₁ (ndg _ n₁)) cg hm rf
  T̄ {g} {m} {φ = φ} {χ = χ} {i = i} {ok = ok} {e = e} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ wi (gΩ↓ {n = n} {k = k₁} {q = q} {fe = fe} {ac = ac} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
    bl (λ i₁ → T̄ {ok = ok} {e = e⁺ n ok e} {ev = ev , ev} {p = p} {𝓖 = 𝓖₀ φ Z₁} {𝓖′ = 𝓖′} (λ {O} c₁ → inc₀ φ Z₁ (H c₁) (cxT i (H₂ c₁)) (top (ctx-refl O (cxT i (H₂ c₁))))) H₂ wi
                   (hb 𝓖₀ (λ ξ ζ c₁ → c₁) φ Z₁ (zt i₁) (G→R (zG i₁)) (intoGV q (zG i₁))))
       (λ i₁ → ψ̄-congᵒ (hm (zm i₁)))
    where
    Z₁ = Z* χ
    E₁ = e⁺ n ok (e↓ e)
    P₁ = ac (e↓ e n (inj₁ refl) q)
    f : Q n k₁ φ Z₁ → Q n k₁ φ Z₁
    f z = qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok E₁ P₁ (h φ Z₁ (intoV q z)))
    zt : ℕ → Q n k₁ φ Z₁
    zt = chainᵠ fe fc* f
    𝓖₆ : ClT n k₁ (Fl ⊔ (φ ⊔ φ)) (Z* (lo n Z₁ ∪ χ))
    𝓖₆ E = VisQT k₁ E × 𝓖₀ φ Z₁ (pΨ q ok E₁ P₁ E)
    zG : ∀ i₁ → Gq g₂ n k₁ (W φ Z₁ ⟪ 𝓖₀ φ Z₁ ⟫ᵀ) (zt i₁)
    zG zero = gw (KQ g₂ k₁) (λ {D} (x , C , c₁ , o) → vQ (Kl-wk₂ {le = fe} {lc = fc*} (VisQT-≈ x o (Wv φ Z₁ c₁)))) (Ω̇G g₂ n k₁)
    zG (suc i₁) =
      gw 𝓖₆ (λ {D} (x , C , c₁ , o) → Kl-wk₂ {le = λ v → fe v , (v , v)} {lc = ⇑ (cv* n)} (VisQT-≈ x o (Wv φ Z₁ c₁)) , St φ Z₁ c₁ (aboveΩ (Ctx-wkC D x) (λ t₁ rt →
             qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok E₁ P₁ t₁) , rwk (R-Ψ q ok E₁ P₁ ok E₁ P₁ (≅ᴵ-refl _) rt) , (λ _ h₁ → wk-rᵀ (H0ᵀ rt h₁)) ,
             subst (λ v₁ → v₁ ≅ˢ runᶜ (W φ Z₁ C) (qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok E₁ P₁ t₁))) (sym (run-wkC (λ v → fe v , (v , v)) (⇑ (cv* n)) D (Ψ q ok E₁ P₁ t₁))) (runᶜ-≅ o (rwk (R-Ψ q ok E₁ P₁ ok E₁ P₁ (≅ᴵ-refl _) rt))))) (ndg _ tt))
         (PsiH q ok E₁ P₁ {𝓖 = 𝓖₆} {𝓧 = 𝓖₀ φ Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) φ Z₁ (zt i₁) (G→R (zG i₁)) (intoGV q (zG i₁))))
    zm : ∀ i₁ → zt i₁ ⊑ᵗ zt (suc i₁)
    zm zero = wk-rᵗ (⊑ᵀ→ᵗ (rwk (RΩ̇ n (≅ᴵ-refl k₁))) (H0ᵀ (rf φ φ Z₁ Z₁ (∼ᶠ-refl φ) (Sim∼-refl Z₁) (zt 0) (zt 0) (G→R (zG 0))) (wk-lᵀ (R→⊑ᵀ (RΩ̇ n (≅ᴵ-refl k₁))))))
    zm (suc i₁) = wk-lᵗ (wk-rᵗ (Ψ-congᵗ (hm (zm i₁))))
  T̄ {g} {m} {φ = φ} {χ = χ} {i = i} {ok = ok} {e = e} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ wi (gΩ {k = k₁} {fe = fe} {r = r} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
    bl (λ i₁ → T̄ {ok = ok} {e = e⁺ m ok e} {ev = ev , ev} {p = p} {𝓖 = 𝓖₀ φ Z₁} {𝓖′ = 𝓖′} (λ {O} c₁ → inc₀ φ Z₁ (H c₁) (cxT i (H₂ c₁)) (top (ctx-refl O (cxT i (H₂ c₁))))) H₂ wi
                   (hb 𝓖₀ (λ ξ ζ c₁ → c₁) φ Z₁ (zt i₁) (G→R (zG i₁)) (intoG (<→◃ r) (zG i₁))))
       (λ i₁ → ψ̄-congᵒ (hm (zm i₁)))
    where
    Z₁ = Z* χ
    f : Q m k₁ φ Z₁ → Q m k₁ φ Z₁
    f z = qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ Z₁ (intoU (<→◃ r) z)))
    zt : ℕ → Q m k₁ φ Z₁
    zt = chainᵠ fe fc* f
    𝓖₆ : ClT m k₁ (Fl ⊔ (φ ⊔ φ)) (Z* (lo m Z₁ ∪ χ))
    𝓖₆ E = KlT g k₁ E × 𝓖₀ φ Z₁ (pψ r E)
    zG : ∀ i₁ → Gq (inp g) m k₁ (W φ Z₁ ⟪ 𝓖₀ φ Z₁ ⟫ᵀ) (zt i₁)
    zG zero = gw (KQ (inp g) k₁) (λ {D} (x , C , c₁ , o) → K→Q g (Kl-wk g {le = fe} {lc = fc*} (KlT-≈ g x o (Wv φ Z₁ c₁)))) (Ω̇G g m k₁)
    zG (suc i₁) =
      gw 𝓖₆ (λ {D} (x , C , c₁ , o) → Kl-wk g {le = λ v → fe v , (v , v)} {lc = ⇑ (cv* m)} (KlT-≈ g x o (Wv φ Z₁ c₁)) , St φ Z₁ c₁ (aboveΩ (Ctx-wkC D x) (λ t₁ rt →
             qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r t₁) , rwk (R-ψᵠ r r (≅ᴵ-refl _) rt) , (λ _ h₁ → wk-rᵀ (P0ᵀ {q = r} rt h₁)) ,
             subst (λ v₁ → v₁ ≅ˢ runᶜ (W φ Z₁ C) (qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r t₁))) (sym (run-wkC (λ v → fe v , (v , v)) (⇑ (cv* m)) D (ψᵠ r t₁))) (runᶜ-≅ o (rwk (R-ψᵠ r r (≅ᴵ-refl _) rt))))) (ndg _ tt))
         (Psi r {𝓖 = 𝓖₆} {𝓧 = 𝓖₀ φ Z₁} proj₂ proj₁ (hb 𝓖₀ (λ ξ ζ c₁ → c₁) φ Z₁ (zt i₁) (G→R (zG i₁)) (intoG (<→◃ r) (zG i₁))))
    zm : ∀ i₁ → zt i₁ ⊑ᵗ zt (suc i₁)
    zm zero = wk-rᵗ (⊑ᵀ→ᵗ (rwk (RΩ̇ m (≅ᴵ-refl k₁))) (P0ᵀ {q = r} (rf φ φ Z₁ Z₁ (∼ᶠ-refl φ) (Sim∼-refl Z₁) (zt 0) (zt 0) (G→R (zG 0))) (wk-lᵀ (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl k₁))))))
    zm (suc i₁) = wk-lᵗ (wk-rᵗ (ψ-congᵗ {q = r} (hm (zm i₁))))

  chT {m = m} {c = c} {φ = φ} {χ = χ} {j = j} {i = i} {ℓ = ℓ} {ok = ok} {e = e} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} {ac = ac₀} {f = f} H H₂ wi cc 𝓖₀ inc₀ W Wf hb Wv St cg hm rf =
    bl (λ n → T̄ H H₂ wi
          (hb 𝓖 inc₀ (zt n) (csim n) (Good-mono (inp-map j (λ { (x , C , c₁ , o) → x , C , inc₀ c₁ , o })) (chG n))))
       (λ n → ψ̄-congᵒ (hm (chst n)))
    where
    ac : j <ᴵ ℓ
    ac = ac₀ ev
    zt : ℕ → Ordˢ j
    zt = iter (λ w₁ → ψ̄ᵠ ok e (f w₁) ev ac) (Ωˢ j)
    csim : ∀ n → zt n ≅ˢ zt n
    csim zero = Ωˢ-refl j
    csim (suc n) = R→≈ᵠ (rf (csim n)) ok e ok e ev ac ev ac (≅ᴵ-refl j)
    chst : ∀ n → zt n ⊑ᵒ zt (suc n)
    chst zero = ⊑ᴱ→ᵒ (Ωˢ-refl j) (F0ᵀ (rf (Ωˢ-refl j)))
    chst (suc n) = ψ̄-congᵒ (hm (chst n))
    𝓔₂ : ClT m c φ χ
    𝓔₂ C′ = Σ _ λ D → Inp j (W ⟪ 𝓖₀ ⟫) D × (C′ ≡ top D ev ac ok e)
    incE : ∀ {C} → 𝓔₂ C → 𝓖₀ C
    incE = incE′ j {ev = ev} {ac = ac} {ok = ok} {e = e} 𝓖₀ W St (mkZ {p = p} cc wi (λ c₁ → inc₀ (H c₁)) cg)
    chG : ∀ n → Good true (Inp j (W ⟪ 𝓖₀ ⟫)) (zt n)
    chG zero = Good-mono (inpVis j W Wv) (Ωg j)
    chG (suc n) = T̄ {ok = ok} {e = e} {ev = ev} {p = ac} {𝓖 = 𝓔₂} {𝓖′ = Inp j (W ⟪ 𝓖₀ ⟫)} (λ d → _ , d , refl) (visD j W Wv) (witI j {W ⟪ 𝓖₀ ⟫})
          (hb 𝓔₂ incE (zt n) (csim n) (Good-mono (inp-map j (λ { (x , C , e′ , o) → x , C , incE e′ , o })) (chG n)))
```
