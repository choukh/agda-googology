# 一切深度: 诚实好树的克隆

> 由 [UniformNF3D3CF](UniformNF3D3CF.lagda.md) 经脚本克隆到 [UniformNF3D3O](UniformNF3D3O.lagda.md) 的 `Obs`, 内容不变. 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3CF where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Align.UniformNF3Eq using (⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅; Ωˢ-≅; Ωˢ-refl;
  self-tr⁻ˢ; tr⁻ˢ-≅; ≅-tr⁻ˢ; ĉ-refl₀; ĉ-reflg; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; addˢ-≅)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; Run; flo; cvFlo; toFlo; fold; Ω̂A; ∅ᴿ; chainA)
open import OCF.Align.UniformNF3Eq using (_≈ᴿ_; fold-≅0)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3D3O using (Obs; idO; fo; addo; tro; tr⁻o; run; _≈ᵒ_; ≈ᵒ-reflˡ; ≈ᵒ-reflʳ; run-≅)
open import OCF.Align.UniformNF3D3N using (Goodᴺ-tr; _⊑ᵒ_; tr⁻-cong; fold-cong; add-cong; rule4ᵒ; B1)
open import OCF.Align.UniformNF3D3G using (_⊑ᴱ_; Ctx; ctx-refl; PFl; AFl; afl; 𝟏; ⊑ᴱ-≅ʳ; ⊑ᴱ-trans; ≅→⊑ᴱ; up-rᴱ; lim-rᴱ; add-floorᴱ; add-rᴱ; add-congᴱ; B1ᴱ; Ω1ᴱ; fold-congᴱ; ŝ-rᴱ; suc-fold)
open import OCF.Align.UniformNF3D3C
```

## §1 第 0 层闭包的链

```agda
module Ch0 {s} {𝓖 : Cl zero} {c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} (𝓑 : Ordᴵ → Cl zero) (i : 𝓖 idO)
           (g0 : Good s 𝓖 t₀) (gg : ∀ η e → (𝓖 ∧ 𝓑 η) idO → Good s (𝓖 ∧ 𝓑 η) (g η e))
           (m : ∀ η e → t₀ ⊑ᵒ g η e) (mm : ∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′)
           (d₀ : ∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (run C t₀))) → c ⊑ᴵ lvG G)
           (dE : ∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (run C (g η e)))) → c ⊑ᴵ lvG G)
           (ch₀ : ∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (run C t₀))) → 𝓑 (lvG G) C)
           (chS : ∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (run C (g η e)))) → 𝓑 (lvG G) C) where
  G₀ : Goodᴺ (toZ t₀)
  G₀ = Good→N i g0
  P  : ℕ → Pt₀ c (λ η → 𝓑 η idO)
  Gk : ∀ k → Goodᴺ (toZ (g (toLevel (Yp (P k)) (hp (P k))) (dp (P k))))
  P zero    = pt (forceᴺ _ G₀) (forceᴺ-HS _ G₀) (d₀ i G₀) (ch₀ i G₀)
  P (suc k) = pt (forceᴺ _ (Gk k)) (forceᴺ-HS _ (Gk k)) (dE _ (dp (P k)) i (bp (P k)) (Gk k)) (chS _ (dp (P k)) i (bp (P k)) (Gk k))
  Gk k = Good→N (i , bp (P k)) (gg _ (dp (P k)) (i , bp (P k)))

  ys : ℕ → Ordᶜ zero
  ys k = Yp (P k)
  hy : ∀ k → HS (ys k)
  hy k = hp (P k)
  dy : ∀ k → c ⊑ᴵ toLevel (ys k) (hy k)
  dy k = dp (P k)

  Ymono : ∀ k → ys k ⊑⁰ ys (suc k)
  Ymono zero    = m _ (dy 0) idO G₀ (Gk 0)
  Ymono (suc k) = mm _ (dy k) _ (dy (suc k)) (toLevel-⊑ (hy k) (hy (suc k)) (Ymono k)) idO (Gk k) (Gk (suc k))

  lmono : ∀ k → toLevel (ys k) (hy k) ⊑ᴵ toLevel (ys (suc k)) (hy (suc k))
  lmono k = toLevel-⊑ (hy k) (hy (suc k)) (Ymono k)
```

## §2 加法

`Add`: $a$ 在类 `𝓐` 里好, `𝓐` 对 "压在 $a$ 之上" 封闭 (`clA`). 右项 $y$ 的上下文是 `addo O a σ`. 类 `𝓐₁` 是 `𝓐` 的任意子类. 第 0 层的右项只读 `idO`. `b1` 变成 `bs`, 这是后继的唯一来源.

```agda
Hk : ∀ {ℓ} (k : Ordᴵ) → Cl ℓ → (a : Ordˢ ℓ) → Simᴵ k ℓ → Cl k → Set
Hk zero      𝓐₁ a σ 𝓧 = 𝓧 idO
Hk (suc k)   𝓐₁ a σ 𝓧 = ∀ {O} → 𝓐₁ O → 𝓧 (addo O a σ)
Hk (lim f s) 𝓐₁ a σ 𝓧 = ∀ {O} → 𝓐₁ O → 𝓧 (addo O a σ)

inp-map : ∀ j {𝓕 𝓕′ : Cl j} → (∀ {D} → 𝓕 D → 𝓕′ D) → ∀ {D} → Inp j 𝓕 D → Inp j 𝓕′ D
inp-map zero      h x = x
inp-map (suc _)   h x = h x
inp-map (lim _ _) h x = h x

Gd-conv : ∀ {i ℓ ℓ′ s 𝓖} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordˢ i} → Gd s i r 𝓖 (intoˢ r x) → Gd s i r′ 𝓖 (intoˢ r′ x)
Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)

NZ-of : ∀ {j ℓ} → j <ᴵ ℓ → NZ ℓ
NZ-of {ℓ = suc _}   _ = tt
NZ-of {ℓ = lim _ _} _ = tt
NZ-of {ℓ = zero} ()

module AddM {ℓ} {𝓐 : Cl ℓ} {a : Ordˢ ℓ} (ga : Good true 𝓐 a) (ea : a ≅ˢ a) (oa : 𝟏 ⊑ᴱ a)
            (cxA : ∀ {O} → 𝓐 O → Ctx O)
            (cgA : ∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓐 C′ → 𝓐 C)
            (clA : NZ ℓ → ∀ {O C″} → 𝓐 O → FlOver a O C″ → 𝓐 C″)
            (hoA : ∀ {C} → 𝓐 C → Hon ℓ a C) where

  fl-add : ∀ {k} (σ : Simᴵ k ℓ) {O : Obs ℓ} {C″} {b : Ordˢ k} → Ctx O → b ≅ˢ b → FlOver (addˢ a σ b) O C″ → FlOver a O C″
  fl-add σ {O} {b = b} cO eb (flo-over cc fl) = flo-over cc (λ t et G →
    proj₁ (add-rᴱ {a = a} {a′ = a} {σ = σ} b ea eb (ctx-refl O cO) (proj₁ (fl t et G))) ,
    ⊑-trans (proj₂ (add-rᴱ {a = a} {a′ = a} {σ = σ} b ea eb (ctx-refl O cO) (proj₁ (fl t et G)))) (proj₂ (fl t et G)))

  hdn : ∀ {k k₀} (r : k ◃₁ k₀) {σ : Simᴵ k₀ ℓ} {𝓐₁ : Cl ℓ} {𝓧 : Cl k₀} → (∀ {O} → 𝓐₁ O → 𝓐 O) → (∀ {O} → 𝓐₁ O → 𝓧 (addo O a σ)) → Hk k 𝓐₁ a (λ q → σ (τ₁ r q)) (Dn r 𝓧)
  hdn {k = zero}    r inc H = refl
  hdn {k = suc _}   r {σ} inc H {O} c = (afl ea oa , cxA (inc c)) , addo O a σ , H c , addo (ctx-refl O (cxA (inc c))) (≅ᴵ-refl _) ea
  hdn {k = lim _ _} r {σ} inc H {O} c = (afl ea oa , cxA (inc c)) , addo O a σ , H c , addo (ctx-refl O (cxA (inc c))) (≅ᴵ-refl _) ea

  iterA-placeholder : ⊤
  iterA-placeholder = tt

  hoB : ∀ {k} {σ : Simᴵ k ℓ} {b : Ordˢ k} {C} → b ≅ˢ b → 𝓐 C → Hon ℓ (addˢ a σ b) C
  hoB {σ = σ} {b = b} {C = C} eb c G = ⊑ᴵ-trans (hoA c (proj₁ L)) (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))
    where L = add-rᴱ {σ = σ} b ea eb (ctx-refl C (cxA c)) G

  Add : ∀ {k} {σ : Simᴵ k ℓ} {𝓐₁ : Cl ℓ} {𝓧 : Cl k} {y : Ordˢ k} → (∀ {O} → 𝓐₁ O → 𝓐 O) → Hk k 𝓐₁ a σ 𝓧 → Good true 𝓧 y → y ≅ˢ y → Good true 𝓐₁ (addˢ a σ y)
  Add inc H bz ey = Good-mono inc ga
  Add inc H (b1 lz) ey = bs 𝓐 inc ea ga clA (λ nz → cgA) hoA
  Add {k = zero} {σ = σ} inc H (bs {a = b} 𝓚 v eb g clk cgk ho) ey =
    bs 𝓐 inc (addˢ-≅ (≅ᴵ-refl _) ea eb) (Add {σ = σ} (λ c → c) (v H) g eb) (λ nz c f′ → clA nz c (fl-add σ (cxA c) eb f′)) (λ nz → cgA) (λ c → hoB {σ = σ} eb c)
  Add {k = suc _} {σ = σ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (bs {a = b} 𝓚 v eb g clk cgk ho) ey =
    bs (λ O → 𝓐 O × 𝓚 (addo O a σ)) (λ c → inc c , v (H c)) (addˢ-≅ (≅ᴵ-refl _) ea eb)
       (Add {σ = σ} {𝓐₁ = λ O → 𝓐 O × 𝓚 (addo O a σ)} {𝓧 = 𝓚} proj₁ proj₂ g eb)
       (λ nz {O} {C″} (c , c₁) f′ → clA nz c (fl-add σ (cxA c) eb f′) ,
          clk tt {addo O a σ} {addo C″ a σ} c₁ (flo-over (afl ea oa , cxo f′) (λ t et G → flw f′ (addˢ a σ t) (addˢ-≅ (≅ᴵ-refl _) ea et) G)))
       (λ nz c₀ o (c , c₁) → cgA c₀ o c , cgk tt (afl ea oa , c₀) (addo o (≅ᴵ-refl _) ea) c₁) (λ (c , c₁) → hoB {σ = σ} eb c)
  Add {k = lim _ _} {σ = σ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (bs {a = b} 𝓚 v eb g clk cgk ho) ey =
    bs (λ O → 𝓐 O × 𝓚 (addo O a σ)) (λ c → inc c , v (H c)) (addˢ-≅ (≅ᴵ-refl _) ea eb)
       (Add {σ = σ} {𝓐₁ = λ O → 𝓐 O × 𝓚 (addo O a σ)} {𝓧 = 𝓚} proj₁ proj₂ g eb)
       (λ nz {O} {C″} (c , c₁) f′ → clA nz c (fl-add σ (cxA c) eb f′) ,
          clk tt {addo O a σ} {addo C″ a σ} c₁ (flo-over (afl ea oa , cxo f′) (λ t et G → flw f′ (addˢ a σ t) (addˢ-≅ (≅ᴵ-refl _) ea et) G)))
       (λ nz c₀ o (c , c₁) → cgA c₀ o c , cgk tt (afl ea oa , c₀) (addo o (≅ᴵ-refl _) ea) c₁) (λ (c , c₁) → hoB {σ = σ} eb c)
  Add {σ = σ} inc H (bl hg st) ey = bl (λ n → Add {σ = σ} inc H (hg n) (l-invˢ ey n)) (λ n → add-cong (≅ᴵ-refl _) ea (st n))
  Add {k = suc _} {σ = σ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ey = bi
    (λ O → 𝓐 O × 𝓖₀ (addo O a σ)) (λ c → inc c , inc₀ (H c)) (λ O → W (addo O a σ))
    (λ {O} (c , c₀) u eu → subst (λ w → run (W (addo O a σ)) u ≅ˢ run O (addˢ a σ (f (intoˢ (<→◃ q) w)))) (sym (out-intoˢ (<→◃ (σ q)) u)) (Wf c₀ u eu))
    (λ 𝓔′ inc″ z ez g → subst (λ y → Good true 𝓔′ (addˢ a σ (f (intoˢ (<→◃ q) y)))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (Add {σ = σ} {𝓐₁ = 𝓔′} {𝓧 = λ D → Σ _ λ O → 𝓔′ O × (D ≡ addo O a σ)} (λ c → proj₁ (inc″ c)) (λ {O} c → O , c , refl)
          (hb (λ D → Σ _ λ O → 𝓔′ O × (D ≡ addo O a σ)) (λ { (O , c , refl) → proj₂ (inc″ c) }) z ez
              (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , C , (O , c , refl) , o) → x , O , c , o })) (Gd→Good (<→◃ (σ q)) g))))
          (i-respˢ ey ez)))
    (λ (c , c₀) → Wv c₀)
    (λ {O} {C″} (c , c₀) (above cx′ wrap) →
       clA (NZ-of (σ q)) c (flo-over cx′ (λ t et G →
         let u  = proj₁ (wrap t et)
             eu = proj₁ (proj₂ (wrap t et))
             d  = ≅ˢ-trans (proj₂ (proj₂ (proj₂ (wrap t et)))) (Wf c₀ u eu)
             H₂ = Goodᴺ-tr (toZ-≅ d) G
             A  = add-rᴱ {a = a} {a′ = a} {σ = σ} (f (intoˢ (<→◃ q) u)) ea (i-respˢ ey eu) (ctx-refl O (cxA c)) H₂
         in proj₁ A , ⊑-trans (proj₂ A) (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) H₂ G)))) ,
       St c₀ (above (afl ea oa , cx′) (λ t et → wrap (addˢ a σ t) (addˢ-≅ (≅ᴵ-refl _) ea et))))
    (λ c₀ o (c , cc) → cgA c₀ o c , cg (afl ea oa , c₀) (addo o (≅ᴵ-refl _) ea) cc)
    (λ {z} {z′} h → subst₂ (λ w w′ → addˢ a σ (f (intoˢ (<→◃ q) w)) ⊑ᵒ addˢ a σ (f (intoˢ (<→◃ q) w′)))
         (sym (out-intoˢ (<→◃ (σ q)) z)) (sym (out-intoˢ (<→◃ (σ q)) z′)) (add-cong (≅ᴵ-refl _) ea (hm h)))
  Add {k = lim _ _} {σ = σ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ey = bi
    (λ O → 𝓐 O × 𝓖₀ (addo O a σ)) (λ c → inc c , inc₀ (H c)) (λ O → W (addo O a σ))
    (λ {O} (c , c₀) u eu → subst (λ w → run (W (addo O a σ)) u ≅ˢ run O (addˢ a σ (f (intoˢ (<→◃ q) w)))) (sym (out-intoˢ (<→◃ (σ q)) u)) (Wf c₀ u eu))
    (λ 𝓔′ inc″ z ez g → subst (λ y → Good true 𝓔′ (addˢ a σ (f (intoˢ (<→◃ q) y)))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (Add {σ = σ} {𝓐₁ = 𝓔′} {𝓧 = λ D → Σ _ λ O → 𝓔′ O × (D ≡ addo O a σ)} (λ c → proj₁ (inc″ c)) (λ {O} c → O , c , refl)
          (hb (λ D → Σ _ λ O → 𝓔′ O × (D ≡ addo O a σ)) (λ { (O , c , refl) → proj₂ (inc″ c) }) z ez
              (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , C , (O , c , refl) , o) → x , O , c , o })) (Gd→Good (<→◃ (σ q)) g))))
          (i-respˢ ey ez)))
    (λ (c , c₀) → Wv c₀)
    (λ {O} {C″} (c , c₀) (above cx′ wrap) →
       clA (NZ-of (σ q)) c (flo-over cx′ (λ t et G →
         let u  = proj₁ (wrap t et)
             eu = proj₁ (proj₂ (wrap t et))
             d  = ≅ˢ-trans (proj₂ (proj₂ (proj₂ (wrap t et)))) (Wf c₀ u eu)
             H₂ = Goodᴺ-tr (toZ-≅ d) G
             A  = add-rᴱ {a = a} {a′ = a} {σ = σ} (f (intoˢ (<→◃ q) u)) ea (i-respˢ ey eu) (ctx-refl O (cxA c)) H₂
         in proj₁ A , ⊑-trans (proj₂ A) (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) H₂ G)))) ,
       St c₀ (above (afl ea oa , cx′) (λ t et → wrap (addˢ a σ t) (addˢ-≅ (≅ᴵ-refl _) ea et))))
    (λ c₀ o (c , cc) → cgA c₀ o c , cg (afl ea oa , c₀) (addo o (≅ᴵ-refl _) ea) cc)
    (λ {z} {z′} h → subst₂ (λ w w′ → addˢ a σ (f (intoˢ (<→◃ q) w)) ⊑ᵒ addˢ a σ (f (intoˢ (<→◃ q) w′)))
         (sym (out-intoˢ (<→◃ (σ q)) z)) (sym (out-intoˢ (<→◃ (σ q)) z′)) (add-cong (≅ᴵ-refl _) ea (hm h)))
  Add {k = zero} inc H (bi {p = ()} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ey
  Add {k = suc k′} {σ = σ} inc H (bu {r = zero} g) ey = Add {σ = λ q → σ (suc q)} inc (hdn zero inc H) g (u-reflˢ zero ey)
  Add {k = lim _ _} {σ = σ} inc H (bu {r = self n} g) ey = Add {σ = λ q → σ (lim n q)} inc (hdn (self n) inc H) g (u-reflˢ (self n) ey)
  Add {k = suc _} {σ = σ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ey =
    bŝ (λ η O → 𝓑 η (addo O a σ)) Bc (Add {σ = σ} inc H g0 et)
       (λ η e w → Add {σ = σ} {𝓧 = 𝓧 ∧ 𝓑 η} (λ c → inc (proj₁ c)) (λ (c , b) → H c , b)
          (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
       (addˢ-≅ (≅ᴵ-refl _) ea et) (λ η e η′ e′ eη → addˢ-≅ (≅ᴵ-refl _) ea (eg η e η′ e′ eη))
       (λ η e → add-cong (≅ᴵ-refl _) ea (m η e)) (λ η e η′ e′ h → add-cong (≅ᴵ-refl _) ea (mm η e η′ e′ h))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  Add {k = lim _ _} {σ = σ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ey =
    bŝ (λ η O → 𝓑 η (addo O a σ)) Bc (Add {σ = σ} inc H g0 et)
       (λ η e w → Add {σ = σ} {𝓧 = 𝓧 ∧ 𝓑 η} (λ c → inc (proj₁ c)) (λ (c , b) → H c , b)
          (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
       (addˢ-≅ (≅ᴵ-refl _) ea et) (λ η e η′ e′ eη → addˢ-≅ (≅ᴵ-refl _) ea (eg η e η′ e′ eη))
       (λ η e → add-cong (≅ᴵ-refl _) ea (m η e)) (λ η e η′ e′ h → add-cong (≅ᴵ-refl _) ea (mm η e η′ e′ h))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  Add {k = zero} {σ = σ} {𝓐₁ = 𝓐₁} {𝓧 = 𝓧} inc H (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ey =
    bĉ C.ys C.hy C.dy C.G₀ (≅-refl⁰ _) C.Gk (λ k → ≅-refl⁰ _)
       (Add {σ = σ} inc H g0 et)
       (λ k → Add {σ = σ} {𝓧 = 𝓧 ∧ 𝓑 _} inc (H , bp (C.P k)) (gg _ (C.dy k) (H , bp (C.P k))) (eg _ _ _ _ (≅ᴵ-refl _)))
       (add-cong (≅ᴵ-refl _) ea (m _ _)) (λ k → add-cong (≅ᴵ-refl _) ea (mm _ _ _ _ (C.lmono k)))
    where module C = Ch0 𝓑 H g0 gg m mm d₀ dE ch₀ chS
  Add {σ = σ} inc H (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ey =
    bĉ ys hy dy G₀ l₀ Gg lE (Add {σ = σ} inc H go (ĉ-refl₀ ey)) (λ k → Add {σ = σ} inc H (gO k) (ĉ-reflg ey _ _))
       (add-cong (≅ᴵ-refl _) ea mo) (λ k → add-cong (≅ᴵ-refl _) ea (mO k))

  iterA : Hk ℓ 𝓐 a (λ q → q) 𝓐 → ∀ n → Good true 𝓐 (iter (a +ˢ_) Ord₊ˢ.zero n) × (iter (a +ˢ_) Ord₊ˢ.zero n ≅ˢ iter (a +ˢ_) Ord₊ˢ.zero n)
  iterA Hs zero    = bz , z≅
  iterA Hs (suc n) = Add {σ = λ q → q} (λ c → c) Hs (proj₁ (iterA Hs n)) (proj₂ (iterA Hs n)) , addˢ-≅ (≅ᴵ-refl _) ea (proj₂ (iterA Hs n))
```
