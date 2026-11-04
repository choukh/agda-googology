> **机械克隆, 验收用.** 由 `OrdLabZGoodLBase` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZGoodLBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZUniform using (Uniform)
open import OCF.Align.OrdLabZSymbolic using (Mlev; σ1)
open import OCF.Align.EmbVVOZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; fΩ̂; ψᴾ; trˢ; tr⁻ˢ; z<suc; H₊; _~_; empty~; H1-pen; H1-fsT; Restrˢ; resˢ; res⁻ˢ)
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω; fsT-c1; γᴱ; diag-fs)
open import OCF.Align.OrdLabZBachmann using (fs-gt; rep<; pen→<; gt→≤; clash; cofA≢c1)
open import OCF.Align.OrdLabZClosure using (lt→<; Pen; fsT₊-pen′)
open import OCF.Align.Standard using (Ctbl; c[]; c∷; Ctbl-pred; Ctbl-fsn; cofψ0≢c1)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; NFᴾ₁; n[]; n∷; nψ; NF₁-pred; NF₁-fsn; γ-mono₁; fsT-mono₁; γ′-NF)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.EmbVVLZExtra using (occ<)
open import OCF.Align.OrdLabZStage2 using (ctx; Lab-+; Lab-uniq; ≺→⊑)
open import OCF.Align.OrdLabZLabel using (BTBO-label; γ-label)
open import OCF.Align.EmbVVOZUniformS
open import OCF.Align.EmbVVOZStage2Label using (chain0; chain1; chain1-≅; t₀pop; gpop; Lab-oc; one⁰)
open import OCF.Align.EmbVVOZDecoupleBase using (fold1; pen1; ΩΩ; γP; 1<ctx; nfγ; nfω; ŝ-reflg; force-subst)
open import OCF.Align.EmbVVOZDecouple using (Idx; lvI; Ilt; Ieq; Lab0[]; kdI; kdI′; gtν; kdI[]; cofP; fold0; pen0)
open import OCF.Align.LadderLabZGoodLBase public using (Ctbl-c1; ctbl-hd; ctbl-one)
open import OCF.Align.EmbVVLZExtra public using (Ctbl-ω; fs-monoA; fs-monoL; fs-mono₁; nf1)
```

```agda
open Ord-Ord using (iter)
open Restrˢ
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt;
              []<; hd<; tl<; lv<; ar<; cofA; cofψ0; cofψ₊) renaming (ψ to ψᵗ)
```

## §1 `Goodᴸ`: 链点带标签的证书

```agda
record Ptᴸ (c : Ordᴵ) (γ : ℕ → T) (m : ℕ) : Set where
  constructor ptᴸ
  field
    x  : Ordᶜ zero
    hx : HS x
    lx : Lab x (γ m)
    dx : c ⊑ᴵ toLevel x hx

lvᴸ : ∀ {c γ m} → Ptᴸ c γ m → Ordᴵ
lvᴸ p = toLevel (Ptᴸ.x p) (Ptᴸ.hx p)

ptsᴸ : ∀ {c γ} (x₀ : Ordᶜ zero) (h₀ : HS x₀) → Lab x₀ (γ 0) → c ⊑ᴵ toLevel x₀ h₀ →
       (F : ∀ m Y (hY : HS Y) → Lab Y (γ m) → c ⊑ᴵ toLevel Y hY → Ordᶜ zero) →
       (hF : ∀ m Y hY lY e → HS (F m Y hY lY e)) →
       (∀ m Y hY lY e → Lab (F m Y hY lY e) (γ (suc m))) →
       (∀ m Y hY lY e → c ⊑ᴵ toLevel (F m Y hY lY e) (hF m Y hY lY e)) → ∀ k → Ptᴸ c γ k
ptsᴸ x₀ h₀ l₀ d₀ F hF lF dF zero    = ptᴸ x₀ h₀ l₀ d₀
ptsᴸ x₀ h₀ l₀ d₀ F hF lF dF (suc k) =
  ptᴸ (F k (Ptᴸ.x p) (Ptᴸ.hx p) (Ptᴸ.lx p) (Ptᴸ.dx p)) (hF k (Ptᴸ.x p) (Ptᴸ.hx p) (Ptᴸ.lx p) (Ptᴸ.dx p))
      (lF k (Ptᴸ.x p) (Ptᴸ.hx p) (Ptᴸ.lx p) (Ptᴸ.dx p)) (dF k (Ptᴸ.x p) (Ptᴸ.hx p) (Ptᴸ.lx p) (Ptᴸ.dx p))
  where p = ptsᴸ x₀ h₀ l₀ d₀ F hF lF dF k

outsᴸ : Ordᶜ zero → (ℕ → Ordᶜ zero) → ℕ → Ordᶜ zero
outsᴸ O₀ O zero    = O₀
outsᴸ O₀ O (suc k) = O k

outsᴸ-HS : ∀ {O₀ O} → HS O₀ → (∀ k → HS (O k)) → ∀ n → HS (outsᴸ O₀ O n)
outsᴸ-HS h₀ h zero    = h₀
outsᴸ-HS h₀ h (suc k) = h k

outsᴸ-step : ∀ {O₀ O} → O₀ ⊑⁰ O 0 → (∀ k → O k ⊑⁰ O (suc k)) → ∀ n → outsᴸ O₀ O n ⊑⁰ outsᴸ O₀ O (suc n)
outsᴸ-step m₀ m zero    = m₀
outsᴸ-step m₀ m (suc k) = m k
```

```agda
data Goodᴸ : Z → Set
forceᴸ    : (x : Z) → Goodᴸ x → Ordᶜ zero
forceᴸ-HS : (x : Z) (G : Goodᴸ x) → HS (forceᴸ x G)

data Goodᴸ where
  gz : Goodᴸ Z.zero
  gs : ∀ {x} → Goodᴸ x → Goodᴸ (Z.suc x)
  gl : ∀ {f : ℕ → Z} (G : ∀ n → Goodᴸ (f n)) →
       (∀ n → forceᴸ (f n) (G n) ⊑⁰ forceᴸ (f (suc n)) (G (suc n))) → Goodᴸ (Z.lim f)
  gc : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} (γ : ℕ → T)
       (G₀ : Goodᴸ t₀) (l₀ : Lab (forceᴸ t₀ G₀) (γ 0)) (d₀ : c ⊑ᴵ toLevel (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀))
       (Gg : ∀ m Y (hY : HS Y) → Lab Y (γ m) → (e : c ⊑ᴵ toLevel Y hY) → Goodᴸ (g (toLevel Y hY) e))
       (lE : ∀ m Y hY lY e → Lab (forceᴸ _ (Gg m Y hY lY e)) (γ (suc m)))
       (dE : ∀ m Y hY lY e → c ⊑ᴵ toLevel (forceᴸ _ (Gg m Y hY lY e)) (forceᴸ-HS _ (Gg m Y hY lY e)))
       (Go₀ : Goodᴸ o₀) →
       let P = ptsᴸ (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀) l₀ d₀ (λ m Y hY lY e → forceᴸ _ (Gg m Y hY lY e))
                    (λ m Y hY lY e → forceᴸ-HS _ (Gg m Y hY lY e)) lE dE in
       (Go : ∀ k → Goodᴸ (o (lvᴸ (P k)) (Ptᴸ.dx (P k)))) →
       forceᴸ o₀ Go₀ ⊑⁰ forceᴸ _ (Go 0) →
       (∀ k → forceᴸ _ (Go k) ⊑⁰ forceᴸ _ (Go (suc k))) →
       Goodᴸ (ĉᴸ c t₀ g o₀ o)

forceᴸ Z.zero    gz        = zero
forceᴸ (Z.suc x) (gs G)    = suc (forceᴸ x G)
forceᴸ (Z.lim f) (gl G st) = lim (λ n → forceᴸ (f n) (G n))
forceᴸ (ĉᴸ c t₀ g o₀ o) (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) = lim (outsᴸ (forceᴸ o₀ Go₀) (λ k → forceᴸ _ (Go k)))

forceᴸ-HS Z.zero    gz        = hz
forceᴸ-HS (Z.suc x) (gs G)    = hs (forceᴸ-HS x G)
forceᴸ-HS (Z.lim f) (gl G st) = hl (λ n → forceᴸ-HS (f n) (G n)) st
forceᴸ-HS (ĉᴸ c t₀ g o₀ o) (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) =
  hl (outsᴸ-HS (forceᴸ-HS o₀ Go₀) (λ k → forceᴸ-HS _ (Go k))) (outsᴸ-step mo₀ mo)
```

```agda
record CCᴸ (c : Ordᴵ) (t₀ : Z) (g : (η : Ordᴵ) → c ⊑ᴵ η → Z) : Set where
  constructor ccᴸ
  field
    γ  : ℕ → T
    G₀ : Goodᴸ t₀
    l₀ : Lab (forceᴸ t₀ G₀) (γ 0)
    d₀ : c ⊑ᴵ toLevel (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀)
    Gg : ∀ m Y (hY : HS Y) → Lab Y (γ m) → (e : c ⊑ᴵ toLevel Y hY) → Goodᴸ (g (toLevel Y hY) e)
    lE : ∀ m Y hY lY e → Lab (forceᴸ _ (Gg m Y hY lY e)) (γ (suc m))
    dE : ∀ m Y hY lY e → c ⊑ᴵ toLevel (forceᴸ _ (Gg m Y hY lY e)) (forceᴸ-HS _ (Gg m Y hY lY e))

ptK : ∀ {c t₀ g} (K : CCᴸ c t₀ g) k → Ptᴸ c (CCᴸ.γ K) k
ptK K = ptsᴸ (forceᴸ _ (CCᴸ.G₀ K)) (forceᴸ-HS _ (CCᴸ.G₀ K)) (CCᴸ.l₀ K) (CCᴸ.d₀ K)
             (λ m Y hY lY e → forceᴸ _ (CCᴸ.Gg K m Y hY lY e)) (λ m Y hY lY e → forceᴸ-HS _ (CCᴸ.Gg K m Y hY lY e))
             (CCᴸ.lE K) (CCᴸ.dE K)

lvK : ∀ {c t₀ g} → CCᴸ c t₀ g → ℕ → Ordᴵ
lvK K k = lvᴸ (ptK K k)

dxK : ∀ {c t₀ g} (K : CCᴸ c t₀ g) k → c ⊑ᴵ lvK K k
dxK K k = Ptᴸ.dx (ptK K k)
```

## §2 计值与证书无关, 证书沿 `≅ᶻ` 搬运

```agda
module _ {c c′ : Ordᴵ} {γ γ′ : ℕ → T} {x₀ x₀′ : Ordᶜ zero} {h₀ : HS x₀} {h₀′ : HS x₀′}
         {l₀ : Lab x₀ (γ 0)} {l₀′ : Lab x₀′ (γ′ 0)} {d₀ : c ⊑ᴵ toLevel x₀ h₀} {d₀′ : c′ ⊑ᴵ toLevel x₀′ h₀′}
         {F : ∀ m Y (hY : HS Y) → Lab Y (γ m) → c ⊑ᴵ toLevel Y hY → Ordᶜ zero}
         {F′ : ∀ m Y (hY : HS Y) → Lab Y (γ′ m) → c′ ⊑ᴵ toLevel Y hY → Ordᶜ zero}
         {hF : ∀ m Y hY lY e → HS (F m Y hY lY e)} {hF′ : ∀ m Y hY lY e → HS (F′ m Y hY lY e)}
         {lF : ∀ m Y hY lY e → Lab (F m Y hY lY e) (γ (suc m))} {lF′ : ∀ m Y hY lY e → Lab (F′ m Y hY lY e) (γ′ (suc m))}
         {dF : ∀ m Y hY lY e → c ⊑ᴵ toLevel (F m Y hY lY e) (hF m Y hY lY e)}
         {dF′ : ∀ m Y hY lY e → c′ ⊑ᴵ toLevel (F′ m Y hY lY e) (hF′ m Y hY lY e)} where
  pts-≅ : x₀ ≅ x₀′ →
          (∀ m Y hY lY e Y′ hY′ lY′ e′ → toLevel Y hY ≅ᴵ toLevel Y′ hY′ → F m Y hY lY e ≅ F′ m Y′ hY′ lY′ e′) →
          ∀ k → Ptᴸ.x (ptsᴸ x₀ h₀ l₀ d₀ F hF lF dF k) ≅ Ptᴸ.x (ptsᴸ x₀′ h₀′ l₀′ d₀′ F′ hF′ lF′ dF′ k)
  pts-≅ e₀ eF zero    = e₀
  pts-≅ e₀ eF (suc k) = eF k _ _ _ _ _ _ _ _ (toLevel-≅ _ _ (pts-≅ e₀ eF k))

outs-≅ᴸ : ∀ {O₀ O₀′ O O′} → O₀ ≅ O₀′ → (∀ k → O k ≅ O′ k) → ∀ n → outsᴸ O₀ O n ≅ outsᴸ O₀′ O′ n
outs-≅ᴸ e₀ e zero    = e₀
outs-≅ᴸ e₀ e (suc k) = e k

forceᴸ-≅ : ∀ {x y} → x ≅ᶻ y → (G : Goodᴸ x) (G′ : Goodᴸ y) → forceᴸ x G ≅ forceᴸ y G′
forceᴸ-≅ zᶻ     gz gz = z≅
forceᴸ-≅ (sᶻ d) (gs G) (gs G′) = s≅ (forceᴸ-≅ d G G′)
forceᴸ-≅ (lᶻ h) (gl G _) (gl G′ _) = l≅ (λ n → forceᴸ-≅ (h n) (G n) (G′ n))
forceᴸ-≅ (ĉᶻ ec dt dg dp dO) (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (gc γ′ G₀′ l₀′ d₀′ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′) =
  l≅ (outs-≅ᴸ (forceᴸ-≅ dp Go₀ Go₀′)
              (λ k → forceᴸ-≅ (dO _ _ _ _ (toLevel-≅ _ _ (pts-≅ (forceᴸ-≅ dt G₀ G₀′)
                        (λ m Y hY lY e Y′ hY′ lY′ e′ eq → forceᴸ-≅ (dg _ e _ e′ eq) (Gg m Y hY lY e) (Gg′ m Y′ hY′ lY′ e′)) k)))
                        (Go k) (Go′ k)))
```

```agda
Goodᴸ-tr : ∀ {x y} → x ≅ᶻ y → Goodᴸ x → Goodᴸ y
Goodᴸ-tr zᶻ     gz     = gz
Goodᴸ-tr (sᶻ d) (gs G) = gs (Goodᴸ-tr d G)
Goodᴸ-tr (lᶻ h) (gl G st) = gl (λ n → Goodᴸ-tr (h n) (G n))
  (λ n → ⊑-trans (≅→⊑ (≅-sym (forceᴸ-≅ (h n) (G n) (Goodᴸ-tr (h n) (G n)))))
         (⊑-trans (st n) (≅→⊑ (forceᴸ-≅ (h (suc n)) (G (suc n)) (Goodᴸ-tr (h (suc n)) (G (suc n)))))))
Goodᴸ-tr {y = ĉᴸ c′ t₀′ g′ o₀′ o′} (ĉᶻ {c = c} {t₀ = t₀} {o₀ = o₀} {g = g} {o = o} ec dt dg dp dO)
         (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) =
  gc γ G₀′ l₀′ d₀′ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′
  where
  cv : ∀ {η} → c′ ⊑ᴵ η → c ⊑ᴵ η
  cv = ⊑ᴵ-≅ˡ (≅ᴵ-sym ec)
  G₀′ : Goodᴸ t₀′
  G₀′ = Goodᴸ-tr dt G₀
  ft : forceᴸ t₀ G₀ ≅ forceᴸ t₀′ G₀′
  ft = forceᴸ-≅ dt G₀ G₀′
  l₀′ : Lab (forceᴸ t₀′ G₀′) (γ 0)
  l₀′ = Lab-≅ (≅-sym ft) l₀
  d₀′ : c′ ⊑ᴵ toLevel (forceᴸ t₀′ G₀′) (forceᴸ-HS t₀′ G₀′)
  d₀′ = ⊑ᴵ-≅ˡ ec (⊑ᴵ-≅ʳ d₀ (toLevel-≅ _ _ ft))
  Gg′ : ∀ m Y (hY : HS Y) → Lab Y (γ m) → (e : c′ ⊑ᴵ toLevel Y hY) → Goodᴸ (g′ (toLevel Y hY) e)
  Gg′ m Y hY lY e = Goodᴸ-tr (dg _ (cv e) _ e (≅ᴵ-refl _)) (Gg m Y hY lY (cv e))
  fg : ∀ m Y (hY : HS Y) (lY : Lab Y (γ m)) (e : c′ ⊑ᴵ toLevel Y hY) →
       forceᴸ _ (Gg m Y hY lY (cv e)) ≅ forceᴸ _ (Gg′ m Y hY lY e)
  fg m Y hY lY e = forceᴸ-≅ (dg _ (cv e) _ e (≅ᴵ-refl _)) (Gg m Y hY lY (cv e)) (Gg′ m Y hY lY e)
  lE′ : ∀ m Y hY lY e → Lab (forceᴸ _ (Gg′ m Y hY lY e)) (γ (suc m))
  lE′ m Y hY lY e = Lab-≅ (≅-sym (fg m Y hY lY e)) (lE m Y hY lY (cv e))
  dE′ : ∀ m Y hY lY e → c′ ⊑ᴵ toLevel (forceᴸ _ (Gg′ m Y hY lY e)) (forceᴸ-HS _ (Gg′ m Y hY lY e))
  dE′ m Y hY lY e = ⊑ᴵ-≅ˡ ec (⊑ᴵ-≅ʳ (dE m Y hY lY (cv e)) (toLevel-≅ _ _ (fg m Y hY lY e)))
  Go₀′ : Goodᴸ o₀′
  Go₀′ = Goodᴸ-tr dp Go₀
  P : ∀ k → Ptᴸ c γ k
  P = ptsᴸ (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀) l₀ d₀ (λ m Y hY lY e → forceᴸ _ (Gg m Y hY lY e))
           (λ m Y hY lY e → forceᴸ-HS _ (Gg m Y hY lY e)) lE dE
  P′ : ∀ k → Ptᴸ c′ γ k
  P′ = ptsᴸ (forceᴸ t₀′ G₀′) (forceᴸ-HS t₀′ G₀′) l₀′ d₀′ (λ m Y hY lY e → forceᴸ _ (Gg′ m Y hY lY e))
            (λ m Y hY lY e → forceᴸ-HS _ (Gg′ m Y hY lY e)) lE′ dE′
  eP : ∀ k → lvᴸ (P k) ≅ᴵ lvᴸ (P′ k)
  eP k = toLevel-≅ _ _ (Lab-uniq (Ptᴸ.lx (P k)) (Ptᴸ.lx (P′ k)))
  dOk : ∀ k → o (lvᴸ (P k)) (Ptᴸ.dx (P k)) ≅ᶻ o′ (lvᴸ (P′ k)) (Ptᴸ.dx (P′ k))
  dOk k = dO _ _ _ _ (eP k)
  Go′ : ∀ k → Goodᴸ (o′ (lvᴸ (P′ k)) (Ptᴸ.dx (P′ k)))
  Go′ k = Goodᴸ-tr (dOk k) (Go k)
  fo : ∀ k → forceᴸ _ (Go k) ≅ forceᴸ _ (Go′ k)
  fo k = forceᴸ-≅ (dOk k) (Go k) (Go′ k)
  fo₀ : forceᴸ o₀ Go₀ ≅ forceᴸ o₀′ Go₀′
  fo₀ = forceᴸ-≅ dp Go₀ Go₀′
  mo₀′ : forceᴸ o₀′ Go₀′ ⊑⁰ forceᴸ _ (Go′ 0)
  mo₀′ = ⊑-trans (≅→⊑ (≅-sym fo₀)) (⊑-trans mo₀ (≅→⊑ (fo 0)))
  mo′ : ∀ k → forceᴸ _ (Go′ k) ⊑⁰ forceᴸ _ (Go′ (suc k))
  mo′ k = ⊑-trans (≅→⊑ (≅-sym (fo k))) (⊑-trans (mo k) (≅→⊑ (fo (suc k))))
```

## §3 记号侧: `fs-mono₁`

```agda
Lab→Ctbl : ∀ {Y t} → Lab Y t → NF₁ t → Ctbl t
Lab→Ctbl {t = []} (l0 c e) nt = c[]
Lab→Ctbl {t = x ∷ xs} (l0 c e) nt = ⊥-elim (cof-ne x xs c)
Lab→Ctbl {t = t} (l1 c e l) nt = Ctbl-c1 t c (Lab→Ctbl l (NF₁-pred nt c))
Lab→Ctbl (lω c e h) nt = Ctbl-ω nt c (Lab→Ctbl (h 1) (NF₁-fsn nt c 1))

Idx-Ctbl : ∀ {ν} → Idx ν → Ctbl ν
Idx-Ctbl (Y , hY , lY , nY) = Lab→Ctbl lY nY
```

```agda
mono-lab : ∀ {u X Y} → NF₁ u → (c : cof u ≡ cω) → ∀ n → Lab X (fsn u n) → Lab Y (fsn u (suc n)) → X ⊑⁰ Y
mono-lab nu c n lX lY = ≺→⊑ (Lab-oc lY (NF₁-fsn nu c (suc n)) lX (NF₁-fsn nu c n) (fs-mono₁ nu c n))

lab0 : Lab Ord₊.zero []
lab0 = l0 refl z≅

one⊑lab : ∀ {Y t} (hY : HS Y) → Lab Y t → NF₁ t → [] <ᵀ t → suc zero ⊑ᴵ toLevel Y hY
one⊑lab hY lY nt p = s⊑′ (toLevel-≺ hz hY (Lab-oc lY nt lab0 n[] p))
```

## §5 两个构造器, 原子与第 0 层的结构标签

```agda
outsLab : ∀ {O₀ O t} → Lab O₀ (fsn t 0) → (∀ k → Lab (O k) (fsn t (suc k))) → ∀ n → Lab (outsᴸ O₀ O n) (fsn t n)
outsLab l₀ lk zero    = l₀
outsLab l₀ lk (suc k) = lk k

limᴸ : ∀ {u} {f : ℕ → Z} → NF₁ u → cof u ≡ cω → (Gs : ∀ n → Goodᴸ (f n)) → (∀ n → Lab (forceᴸ _ (Gs n)) (fsn u n)) →
       Σ (Goodᴸ (Z.lim f)) λ G → Lab (forceᴸ _ G) u
limᴸ nu c Gs lab = gl Gs (λ n → mono-lab nu c n (lab n) (lab (suc n))) , lω c (l≅ (λ n → ≅-refl⁰ _)) lab

ĉᴸ-mk : ∀ {u c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} → NF₁ u → cof u ≡ cω → (K : CCᴸ c t₀ g) →
        (Go₀ : Goodᴸ o₀) → Lab (forceᴸ _ Go₀) (fsn u 0) →
        (Go : ∀ k → Goodᴸ (o (lvK K k) (dxK K k))) → (∀ k → Lab (forceᴸ _ (Go k)) (fsn u (suc k))) →
        Σ (Goodᴸ (ĉᴸ c t₀ g o₀ o)) λ G → Lab (forceᴸ _ G) u
ĉᴸ-mk nu c K Go₀ l₀ Go lk =
  gc (CCᴸ.γ K) (CCᴸ.G₀ K) (CCᴸ.l₀ K) (CCᴸ.d₀ K) (CCᴸ.Gg K) (CCᴸ.lE K) (CCᴸ.dE K) Go₀ Go
     (mono-lab nu c 0 l₀ (lk 0)) (λ k → mono-lab nu c (suc k) (lk k) (lk (suc k))) ,
  lω c (l≅ (λ n → ≅-refl⁰ _)) (outsLab l₀ lk)
```

```agda
Atomᴸ : Ordˢ zero → T → Set
Atomᴸ x θ = (x ≅ˢ x) × Σ (Goodᴸ (toZ x)) (λ G → Lab (forceᴸ (toZ x) G) θ)

Atomᴸ-≅ : ∀ {x y : Ordˢ zero} {θ} → Atomᴸ x θ → y ≅ˢ x → Atomᴸ y θ
Atomᴸ-≅ (ex , G , l) d = ≅ˢ-reflˡ d , Goodᴸ-tr (toZ-≅ (≅ˢ-sym d)) G , Lab-≅ (forceᴸ-≅ (toZ-≅ d) _ G) l

data Lab0ᴸ : Ordˢ zero → T → Set where
  lz  : ∀ {t} → cof t ≡ c0 → Lab0ᴸ Ord₊ˢ.zero t
  ls  : ∀ {t y} → cof t ≡ c1 → Lab0ᴸ y (pred t) → Lab0ᴸ (Ord₊ˢ.suc y) t
  ll  : ∀ {t} {F : ℕ → Ordˢ zero} → cof t ≡ cω → (∀ n → Lab0ᴸ (F n) (fsn t n)) → Lab0ᴸ (Ord₊ˢ.lim F) t
  lŝ₀ : ∀ {t c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} → cof t ≡ cω →
        (K : CCᴸ c (toZ t₀) (λ η e → toZ (g η e))) → Lab0ᴸ t₀ (fsn t 0) →
        (∀ k → Lab0ᴸ (g (lvK K k) (dxK K k)) (fsn t (suc k))) → Lab0ᴸ (Ord₊ˢ.ŝ {ℓ = zero} c t₀ g) t
  lĉ  : ∀ {t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ zero} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} → cof t ≡ cω →
        (K : CCᴸ c t₀ g) → Lab0ᴸ o₀ (fsn t 0) → (∀ k → Lab0ᴸ (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
        Lab0ᴸ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t

atomL : ∀ {x : Ordˢ zero} {θ} → Atomᴸ x θ → Lab0ᴸ x θ
atomL {x = Ord₊ˢ.zero} (ex , gz , l0 c e) = lz c
atomL {x = Ord₊ˢ.zero} (ex , gz , l1 c () l)
atomL {x = Ord₊ˢ.zero} (ex , gz , lω c () h)
atomL {x = Ord₊ˢ.suc x} (ex , gs G , l0 c ())
atomL {x = Ord₊ˢ.suc x} (ex , gs G , l1 c (s≅ e) l) = ls c (atomL (s-invˢ ex , G , Lab-≅ e l))
atomL {x = Ord₊ˢ.suc x} (ex , gs G , lω c () h)
atomL {x = Ord₊ˢ.lim f} (ex , gl G st , l0 c ())
atomL {x = Ord₊ˢ.lim f} (ex , gl G st , l1 c () l)
atomL {x = Ord₊ˢ.lim f} (ex , gl G st , lω c (l≅ k) h) = ll c (λ n → atomL (l-invˢ ex n , G n , Lab-≅ (k n) (h n)))
atomL {x = Ord₊ˢ.limᵢ () f} at
atomL {x = Ord₊ˢ.up () x} at
atomL {x = Ord₊ˢ.ŝ c t₀ g} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , l0 c′ ())
atomL {x = Ord₊ˢ.ŝ c t₀ g} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , l1 c′ () l)
atomL {x = Ord₊ˢ.ŝ c t₀ g} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , lω cw (l≅ k) h) =
  lŝ₀ cw (ccᴸ γ G₀ l₀ d₀ Gg lE dE) (atomL (ŝ-refl₀ ex , Go₀ , Lab-≅ (k 0) (h 0)))
      (λ m → atomL (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _) , Go m , Lab-≅ (k (suc m)) (h (suc m))))
atomL {x = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , l0 c′ ())
atomL {x = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , l1 c′ () l)
atomL {x = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} (ex , gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo , lω cw (l≅ k) h) =
  lĉ cw (ccᴸ γ G₀ l₀ d₀ Gg lE dE) (atomL (ĉ-refl₀ ex , Go₀ , Lab-≅ (k 0) (h 0)))
     (λ m → atomL (ĉ-reflg ex _ _ , Go m , Lab-≅ (k (suc m)) (h (suc m))))
```

## §6 第 0 层的和与规则 4

```agda
addᴸ : ∀ {a b : Ordˢ zero} {x ys} (Ga : Goodᴸ (toZ a)) → Lab (forceᴸ _ Ga) (x ∷ []) →
       (Gb : Goodᴸ (toZ b)) → Lab (forceᴸ _ Gb) ys → NF₁ (x ∷ ys) →
       Σ (Goodᴸ (toZ (a +ˢ b))) λ G → Lab (forceᴸ _ G) (x ∷ ys)
addᴸ {b = Ord₊ˢ.zero} {ys = []} Ga la gz lb nf = Ga , la
addᴸ {b = Ord₊ˢ.zero} {ys = y ∷ ys} Ga la gz (l0 c e) nf = ⊥-elim (cof-ne y ys c)
addᴸ {b = Ord₊ˢ.zero} {ys = y ∷ ys} Ga la gz (l1 c () l) nf
addᴸ {b = Ord₊ˢ.zero} {ys = y ∷ ys} Ga la gz (lω c () h) nf
addᴸ {b = Ord₊ˢ.suc b} Ga la (gs Gb) (l0 c ()) nf
addᴸ {b = Ord₊ˢ.suc b} {ys = []} Ga la (gs Gb) (l1 () e l) nf
addᴸ {b = Ord₊ˢ.suc b} {ys = y ∷ ys} Ga la (gs Gb) (l1 c (s≅ e) l) nf =
  gs (proj₁ Rb) , l1 c (s≅ (≅-refl⁰ _)) (proj₂ Rb)
  where Rb = addᴸ Ga la Gb (Lab-≅ e l) (NF₁-pred nf c)
addᴸ {b = Ord₊ˢ.suc b} Ga la (gs Gb) (lω c () h) nf
addᴸ {b = Ord₊ˢ.lim f} Ga la (gl Gb st) (l0 c ()) nf
addᴸ {b = Ord₊ˢ.lim f} Ga la (gl Gb st) (l1 c () l) nf
addᴸ {b = Ord₊ˢ.lim f} {ys = []} Ga la (gl Gb st) (lω () e h) nf
addᴸ {b = Ord₊ˢ.lim f} {ys = y ∷ ys} Ga la (gl Gb st) (lω c (l≅ k) h) nf =
  limᴸ nf c (λ n → proj₁ (addᴸ Ga la (Gb n) (Lab-≅ (k n) (h n)) (NF₁-fsn nf c n)))
            (λ n → proj₂ (addᴸ Ga la (Gb n) (Lab-≅ (k n) (h n)) (NF₁-fsn nf c n)))
addᴸ {b = Ord₊ˢ.limᵢ () f} Ga la Gb lb nf
addᴸ {b = Ord₊ˢ.up () x} Ga la Gb lb nf
addᴸ {b = Ord₊ˢ.ŝ c t₀ g} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (l0 c′ ()) nf
addᴸ {b = Ord₊ˢ.ŝ c t₀ g} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (l1 c′ () l) nf
addᴸ {b = Ord₊ˢ.ŝ c t₀ g} {ys = []} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (lω () e h) nf
addᴸ {b = Ord₊ˢ.ŝ c t₀ g} {ys = y ∷ ys} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (lω cw (l≅ k) h) nf =
  ĉᴸ-mk nf cw (ccᴸ γ G₀ l₀ d₀ Gg lE dE)
        (proj₁ (addᴸ Ga la Go₀ (Lab-≅ (k 0) (h 0)) (NF₁-fsn nf cw 0)))
        (proj₂ (addᴸ Ga la Go₀ (Lab-≅ (k 0) (h 0)) (NF₁-fsn nf cw 0)))
        (λ m → proj₁ (addᴸ Ga la (Go m) (Lab-≅ (k (suc m)) (h (suc m))) (NF₁-fsn nf cw (suc m))))
        (λ m → proj₂ (addᴸ Ga la (Go m) (Lab-≅ (k (suc m)) (h (suc m))) (NF₁-fsn nf cw (suc m))))
addᴸ {b = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (l0 c′ ()) nf
addᴸ {b = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (l1 c′ () l) nf
addᴸ {b = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} {ys = []} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (lω () e h) nf
addᴸ {b = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} {ys = y ∷ ys} Ga la (gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) (lω cw (l≅ k) h) nf =
  ĉᴸ-mk nf cw (ccᴸ γ G₀ l₀ d₀ Gg lE dE)
        (proj₁ (addᴸ Ga la Go₀ (Lab-≅ (k 0) (h 0)) (NF₁-fsn nf cw 0)))
        (proj₂ (addᴸ Ga la Go₀ (Lab-≅ (k 0) (h 0)) (NF₁-fsn nf cw 0)))
        (λ m → proj₁ (addᴸ Ga la (Go m) (Lab-≅ (k (suc m)) (h (suc m))) (NF₁-fsn nf cw (suc m))))
        (λ m → proj₂ (addᴸ Ga la (Go m) (Lab-≅ (k (suc m)) (h (suc m))) (NF₁-fsn nf cw (suc m))))

repᴸ : ∀ {P : Ordˢ zero} {x} (GP : Goodᴸ (toZ P)) → Lab (forceᴸ _ GP) (x ∷ []) → (∀ n → NF₁ (replicate n x)) →
       ∀ n → Σ (Goodᴸ (toZ (iter (P +ˢ_) Ord₊ˢ.zero n))) λ G → Lab (forceᴸ _ G) (replicate n x)
repᴸ GP lP nf zero    = gz , l0 refl z≅
repᴸ GP lP nf (suc n) = addᴸ GP lP (proj₁ (repᴸ GP lP nf n)) (proj₂ (repᴸ GP lP nf n)) (nf (suc n))
```

## §8 全层级的关系式标签 `LabL`

```agda
module _ (ℓ : Ordᴵ) (L< : (j : Ordᴵ) (r : j ◃ ℓ) → Uˢ j r → T → Set) where
  data LabL₊ : Ordˢ ℓ → T → Set where
    gz : ∀ {t} → cof t ≡ c0 → LabL₊ Ord₊ˢ.zero t
    gs : ∀ {t y} → cof t ≡ c1 → LabL₊ y (pred t) → LabL₊ (Ord₊ˢ.suc y) t
    gl : ∀ {t} {F : ℕ → Ordˢ ℓ} → cof t ≡ cω → (∀ n → LabL₊ (F n) (fsn t n)) → LabL₊ (Ord₊ˢ.lim F) t
    gu : ∀ {t k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → L< k (◃₁→◃ r) x t → LabL₊ (Ord₊ˢ.up r x) t
    gi : ∀ {t ν j} {q : j <ᴵ ℓ} {f : Uˢ j (<→◃ q) → Ordˢ ℓ} → cof t ≡ cΩ ν → (I : Idx ν) → j ≅ᴵ lvI I →
         (∀ η (x : Ordˢ j) → L< j (<→◃ q) (intoˢ (<→◃ q) x) η → LabL₊ (f (intoˢ (<→◃ q) x)) (fsT t η)) →
         LabL₊ (Ord₊ˢ.limᵢ q f) t
    gĉ : ∀ {t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → cof t ≡ cω →
         (K : CCᴸ c t₀ g) → LabL₊ o₀ (fsn t 0) →
         (∀ k → LabL₊ (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
         LabL₊ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t
    gŝ : ∀ {t c w} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → kd ℓ ≡ false → cof t ≡ cΩ [] →
         (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → (∀ θ → Occ w (fsT t θ)) →
         LabL₊ t₀ (fsT t (natT 1)) →
         (∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) →
          LabL₊ (g (toLevel Y hY) e) (fsT t θ)) →
         LabL₊ (Ord₊ˢ.ŝ c t₀ g) t

LvL : (i : Ordᴵ) → ((j : Ordᴵ) (r : j ◃ i) → Uˢ j r → T → Set) → Ordˢ i → T → Set
LvL zero      L x t = Atomᴸ x t
LvL (suc i)   L x t = LabL₊ (suc i) L x t
LvL (lim f s) L x t = LabL₊ (lim f s) L x t

Ll : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → T → Set
Ll i zero         x t = LvL i Ll x t
Ll i (suc r)      x t = Ll i r x t
Ll _ (self {f} n) x t = LvL (f n) Ll x t
Ll i (lim n r)    x t = Ll i r x t

LabL : ∀ {ℓ} → Ordˢ ℓ → T → Set
LabL {ℓ} x t = LvL ℓ Ll x t

Ll→ : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → Ll i r (intoˢ r x) t → LabL x t
Ll→ zero      h = h
Ll→ (suc r)   h = Ll→ r h
Ll→ (self n)  h = h
Ll→ (lim n r) h = Ll→ r h

→Ll : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → LabL x t → Ll i r (intoˢ r x) t
→Ll zero      h = h
→Ll (suc r)   h = →Ll r h
→Ll (self n)  h = h
→Ll (lim n r) h = →Ll r h

toL₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabL x t → LabL₊ i Ll x t
toL₊ {i = zero}    () h
toL₊ {i = suc _}   k h = h
toL₊ {i = lim _ _} k h = h

frL₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabL₊ i Ll x t → LabL x t
frL₊ {i = zero}    () h
frL₊ {i = suc _}   k h = h
frL₊ {i = lim _ _} k h = h
```

## §9 搬运与 $\Omega$

```agda
LabL-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabL x t → LabL (trˢ e x) t
LabL-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabL x t → LabL (tr⁻ˢ e x) t
LabL-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {t} → LabL u t → LabL (backˢ (resˢ q e) u) t
LabL-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {t} → LabL u t → LabL (backˢ (res⁻ˢ q e) u) t
L-tr  : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabL₊ a Ll x t → LabL₊ b Ll (trˢ e x) t
L-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabL₊ b Ll x t → LabL₊ a Ll (tr⁻ˢ e x) t

LabL-tr z≅ at = Atomᴸ-≅ at (trˢ-≅ z≅ (proj₁ at))
LabL-tr (s≅ e) h = L-tr (s≅ e) h
LabL-tr (l≅ k) h = L-tr (l≅ k) h
LabL-tr⁻ z≅ at = Atomᴸ-≅ at (tr⁻ˢ-≅ z≅ (proj₁ at))
LabL-tr⁻ (s≅ e) h = L-tr⁻ (s≅ e) h
LabL-tr⁻ (l≅ k) h = L-tr⁻ (l≅ k) h

L-tr e (gz c)   = gz c
L-tr e (gs c h) = gs c (L-tr e h)
L-tr e (gl c h) = gl c (λ n → L-tr e (h n))
L-tr (s≅ e) (gu {r = zero} h)   = gu (LabL-tr e h)
L-tr (l≅ k) (gu {r = self n} h) = gu (LabL-tr (k n) h)
L-tr e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej)
     (λ η x l → subst (λ v → LabL₊ _ Ll (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) x))
                      (L-tr e (h η (backˢ (resˢ q e) x) (→Ll (<→◃ q) (LabL-back q e (Ll→ (<→◃ (ltˢ (resˢ q e))) l))))))
L-tr e (gĉ c K h₀ hk) = gĉ c K (L-tr e h₀) (λ k → L-tr e (hk k))
L-tr e (gŝ kk c Ib bb ob h₀ hg) = gŝ (trans (sym (kd-≅ e)) kk) c Ib bb ob (L-tr e h₀) (λ θ Y hY lY nθ lt d → L-tr e (hg θ Y hY lY nθ lt d))

L-tr⁻ e (gz c)   = gz c
L-tr⁻ e (gs c h) = gs c (L-tr⁻ e h)
L-tr⁻ e (gl c h) = gl c (λ n → L-tr⁻ e (h n))
L-tr⁻ (s≅ e) (gu {r = zero} h)   = gu (LabL-tr⁻ e h)
L-tr⁻ (l≅ k) (gu {r = self n} h) = gu (LabL-tr⁻ (k n) h)
L-tr⁻ e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej)
     (λ η x l → subst (λ v → LabL₊ _ Ll (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) x))
                      (L-tr⁻ e (h η (backˢ (res⁻ˢ q e) x) (→Ll (<→◃ q) (LabL-back⁻ q e (Ll→ (<→◃ (ltˢ (res⁻ˢ q e))) l))))))
L-tr⁻ e (gĉ c K h₀ hk) = gĉ c K (L-tr⁻ e h₀) (λ k → L-tr⁻ e (hk k))
L-tr⁻ e (gŝ kk c Ib bb ob h₀ hg) = gŝ (trans (kd-≅ e) kk) c Ib bb ob (L-tr⁻ e h₀) (λ θ Y hY lY nθ lt d → L-tr⁻ e (hg θ Y hY lY nθ lt d))

LabL-back zero      (s≅ e) h = LabL-tr⁻ e h
LabL-back (suc q)   (s≅ e) h = LabL-back q e h
LabL-back (lim n q) (l≅ k) h = LabL-back q (k n) h

LabL-back⁻ zero      (s≅ e) h = LabL-tr e h
LabL-back⁻ (suc q)   (s≅ e) h = LabL-back⁻ q e h
LabL-back⁻ (lim n q) (l≅ k) h = LabL-back⁻ q (k n) h
```

```agda
LabL-Ω : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {a} → a ≅ᴵ toLevel Y hY → LabL (Ωˢ a) (Ωt θ)
LabL-Ω {θ = []} Ord₊.zero hY l nθ z≅ = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
LabL-Ω {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ with Lab0[] l
... | ()
LabL-Ω {θ = θ} (Ord₊.suc Y) hY (l0 c ()) nθ (s≅ e)
LabL-Ω {θ = θ} (Ord₊.suc Y) hY (lω c () h) nθ (s≅ e)
LabL-Ω {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e)
LabL-Ω {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c (s≅ e′) l) nθ (s≅ e) =
  gi (cong (E.cofψ0 (w ∷ ws)) c) (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c) e
     (λ η x lx → gu (subst (LabL x) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) c η)) lx))
LabL-Ω {θ = θ} (Ord₊.lim F) hY (l0 c ()) nθ (l≅ k)
LabL-Ω {θ = θ} (Ord₊.lim F) hY (l1 c () l) nθ (l≅ k)
LabL-Ω {θ = []} (Ord₊.lim F) hY (lω () (l≅ k′) h) nθ (l≅ k)
LabL-Ω {θ = w ∷ ws} (Ord₊.lim F) hY (lω c (l≅ k′) h) nθ (l≅ k) =
  gl (cong (E.cofψ0 (w ∷ ws)) c)
     (λ n → gu (subst (LabL _) (sym (E.fsn0-eq w ws n c))
                      (LabL-Ω (F n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c n) (k n))))
LabL-Ω (Ord₊.limᵢ () f) hY l nθ e
LabL-Ω (Ord₊.up () x) hY l nθ e
```

## §10 不带前缀的 $\psi_w$

```agda
LSumA : ∀ {ℓ} {a : Ordˢ ℓ} {σ : Simᴵ zero ℓ} {b : Ordˢ zero} {x ys} → LabL₊ ℓ Ll a (x ∷ []) → Lab0ᴸ b ys →
        LabL₊ ℓ Ll (addˢ a σ b) (x ∷ ys)
LSumA {ys = []} la (lz c) = la
LSumA {ys = y ∷ ys} la (lz c) = ⊥-elim (cof-ne y ys c)
LSumA {ys = []} la (ls () l)
LSumA {ys = y ∷ ys} la (ls c l) = gs c (LSumA la l)
LSumA {ys = []} la (ll () h)
LSumA {ys = y ∷ ys} la (ll c h) = gl c (λ n → LSumA la (h n))
LSumA {ys = []} la (lŝ₀ () K h₀ hk)
LSumA {ys = y ∷ ys} la (lŝ₀ c K h₀ hk) = gĉ c K (LSumA la h₀) (λ m → LSumA la (hk m))
LSumA {ys = []} la (lĉ () K h₀ hk)
LSumA {ys = y ∷ ys} la (lĉ c K h₀ hk) = gĉ c K (LSumA la h₀) (λ m → LSumA la (hk m))

LSum  : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabL₊ ℓ Ll a (x ∷ []) → LabL b ys →
        LabL₊ ℓ Ll (addˢ a σ b) (x ∷ ys)
LSum₊ : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabL₊ ℓ Ll a (x ∷ []) → LabL₊ k Ll b ys →
        LabL₊ ℓ Ll (addˢ a σ b) (x ∷ ys)
LSum {k = zero} kl la at = LSumA la (atomL at)
LSum {k = suc _} kl la h = LSum₊ kl la h
LSum {k = lim _ _} kl la h = LSum₊ kl la h
LSum₊ {ys = []} kl la (gz c) = la
LSum₊ {ys = y ∷ ys} kl la (gz c) = ⊥-elim (cof-ne y ys c)
LSum₊ {ys = []} kl la (gs () h)
LSum₊ {ys = y ∷ ys} kl la (gs c h) = gs c (LSum₊ kl la h)
LSum₊ {ys = []} kl la (gl () h)
LSum₊ {ys = y ∷ ys} kl la (gl c h) = gl c (λ n → LSum₊ kl la (h n))
LSum₊ {σ = σ} kl la (gu {r = zero} h) = LSum {σ = λ q → σ (suc q)} kl la h
LSum₊ {σ = σ} kl la (gu {r = self n} h) = LSum {σ = λ q → σ (lim n q)} kl la h
LSum₊ {ys = []} kl la (gi () I ej h)
LSum₊ {a = a} {σ = σ} {x = x} {ys = y ∷ ys} kl la (gi {q = q} {f = f} c I ej h) =
  gi c I ej (λ η w l → subst (λ v → LabL₊ _ Ll (addˢ a σ (f (intoˢ (<→◃ q) v))) (x ∷ fsT (y ∷ ys) η))
                             (sym (out-intoˢ (<→◃ (σ q)) w))
                             (LSum₊ kl la (h η w (→Ll (<→◃ q) (Ll→ (<→◃ (σ q)) l)))))
LSum₊ {ys = []} kl la (gĉ () K h₀ hk)
LSum₊ {ys = y ∷ ys} kl la (gĉ c K h₀ hk) = gĉ c K (LSum₊ kl la h₀) (λ m → LSum₊ kl la (hk m))
LSum₊ {k = zero} kl la (gŝ () c Ib bb ob h₀ hg)
LSum₊ {k = suc _} {ys = []} kl la (gŝ kk () Ib bb ob h₀ hg)
LSum₊ {k = suc _} {ys = y ∷ ys} kl la (gŝ kk c Ib bb ob h₀ hg) =
  gŝ kl c Ib bb (λ θ → ot (ob θ)) (LSum₊ kl la h₀) (λ θ Y hY lY nθ lt e → LSum₊ kl la (hg θ Y hY lY nθ lt e))
LSum₊ {k = lim _ _} {ys = []} kl la (gŝ kk () Ib bb ob h₀ hg)
LSum₊ {k = lim _ _} {ys = y ∷ ys} kl la (gŝ kk c Ib bb ob h₀ hg) =
  gŝ kl c Ib bb (λ θ → ot (ob θ)) (LSum₊ kl la h₀) (λ θ Y hY lY nθ lt e → LSum₊ kl la (hg θ Y hY lY nθ lt e))

LRep : ∀ {ℓ} {P : Ordˢ ℓ} {x} → kd ℓ ≡ false → LabL₊ ℓ Ll P (x ∷ []) → ∀ n →
       LabL₊ ℓ Ll (iter (P +ˢ_) Ord₊ˢ.zero n) (replicate n x)
LRep kl lP zero    = gz refl
LRep kl lP (suc n) = LSum₊ kl lP (LRep kl lP n)
```

## §11 带前缀的 $\psi_w$, 目标 $w\ne0$

```agda
lab1 : Lab one⁰ (natT 1)
lab1 = l1 refl (s≅ z≅) (l0 refl z≅)
```

## §12 带前缀的 $\psi_0$, 任意层的尾巴: 证书与标签一起

```agda
I0 : Idx []
I0 = Ord₊.zero , hz , l0 refl z≅ , n[]

z≺I : ∀ {ν j} → (I : Idx ν) → j ≅ᴵ lvI I → (ν ≡ [] → ⊥) → zero ≺ᴵ j
z≺I {ν = []}    I ej ne = ⊥-elim (ne refl)
z≺I {ν = v ∷ vs} I ej ne = ≺ᴵ-respʳ (Ilt I0 I []<) (≅ᴵ-sym ej)
```

## §13 结论与边界
