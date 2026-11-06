# EboLeanTau: 可数 EBO 标准形的良基, 沿 τ 拉回 Setzer 的突出集

> **记号侧验收工作**, 读记号 (EBO 的项与标准形) 与 Setzer 1998 的记号 OT_I, 不进成品.
>
> **结论 (编译过的定理, 无前提).** `wfNF′ : NF t → Ctbl t → AccNF t`: 可数 EBO 标准形上 $<^\mathsf T$ 良基 (量词限于标准且可数的项). 同 [WfTauNF](WfTauNF.lagda.md) 的 `wfNF`, 换了两处:
>
> 1. **不经 Setzer 的 Theorem 4.41, 不要 Γ-迭代.** 原路线用 `Acc-endpt 1`: OT_I 端点 $\psi_{\Omega_1}(\Omega_{I+1})$ 以下全部可达, 证明要突出类 $W_i$ (`Main`) 与 $\mathbb W\cap I\cong W(\mathbb W)\cap I$ (`Gamma`, `Gamma2`, 即 I 层的 Γ-迭代). 这里直接对 EBO 标准形结构归纳证 $\tau t\in\mathbb W$ (`𝕎τ`, §3): $\mathbb W$ (一切突出集的并) 对 $0$, $1$, $+$, $\Omega$, $\psi$ 封闭 (Setzer Lemma 4.29, 4.31 (a)), 而 τ 的像只用这些构造, 没有 $I$ 与 $\psi_I$. 再由 Lemma 4.21 (c) ($\mathbb W\cap\Omega_1$ 上的超限归纳) 得可达. 于是 OT_I 的 `Main` (208 行), `Gamma` (238), `Gamma2` (25), 以及 Lemma 4.31 (b) 的 $\psi_I$ 部分都不需要.
> 2. **τ 保标准形对归纳的 `NF` 证** (§2), 不经 bot 的 Bool 谓词.
>
> 端点也更简单: 可数项 $<\Omega_1$ 在 EBO 一侧是句法事实, τ 保序送到 Setzer 的 $\Omega_1$ (`ctbl<Ω₁`), 不要 `τ≺I` 与端点 `endpt`.
>
> τ 与 `τ-mono`, `τ≺I` 逐字取自 [WfScoutTau](WfScoutTau.lagda.md); `Gnil`, `Gτ`, τ-NF 的侧条件取自 WfTauNF, 改成对 `NF` 与 `InG` 证. Setzer 一侧导入 [EboLean/OT](EboLean/OT/) (归档 `Mahlo.Inacc` 的拷贝, 见 [EboLean](EboLean.lagda.md) §2). `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLeanTau where

open import Level using (0ℓ)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<; sucT)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLeanBase
  using (NF; NFP; n[]; n∷; nψ; HdLe; _≤ᵀ_; _≤ᴾ_; dec≤; ≤-<; sub≤; idx<; <ᵀ-trans;
         InG; InGP; gp; gtl; gh; gw; gc; GB; Ctbl; c[]; c∷; nfp-u; nfp-a; nf-ψ)

open import OCF.Align.EboLean.OT.Syntax using (Tm; PTm; Reg; zer; _▹_; ⟨_⟩; phi; psi; Om; I; ΩR; one;
  eqT; eqP; toList; NZ; isZero; isFi; isFiT; Ω₁)
open import OCF.Align.EboLean.OT.Order using (lt; le; _≺_; lt!)
open import OCF.Align.EboLean.OT.Closure using (isOT; isOTP; OT; ot!; G; GP; allLt)
open import OCF.Align.EboLean.OT.Arith using (app; _+_; Ω; plus)
open import OCF.Align.EboLean.OT.BoolLemmas using (∨-true; ∨-introˡ; ∨-introʳ; ∧-intro; ∧-true; if-true; if-false;
  eqP-refl; eqR-refl; eqT-sound; eqT-refl)
open import OCF.Align.EboLean.OT.OrderProps using (ltLx; lt-list)
open import OCF.Align.EboLean.OT.Unfold using (lt-unfold≠)
open import OCF.Align.EboLean.OT.Linear using (AT-all; lin″; ≺⇒eqT-false; goL)
open import OCF.Align.EboLean.OT.Trans using (lt-trans)
open import OCF.Align.EboLean.OT.Lex using (fromL; toList-fromL; fromL-NZ; ltLx-sing⁻; ≺-▹; +1-least′; +one;
  one≺P; ≺-sing-▹; lt-zer; leˡ; leʳ)
open import OCF.Align.EboLean.OT.FactsImpl using (facts)
open import OCF.Align.EboLean.OT.WO.Facts using (module OTFacts)
open OTFacts facts using (+-OT; plus-OT; plus-Car; ≺plus; Car-closed-+1)
open import OCF.Align.EboLean.OT.WO.Base using (Prog₁)
open import OCF.Align.EboLean.OT.WO.Closed2 facts using (OT-one; uc-+; uc-app)
open import OCF.Align.EboLean.OT.WO.Dist facts using (Ag-Prog₁)
open import OCF.Align.EboLean.OT.WO.Union facts using (𝕎; Ag𝕎; 𝕎-UC; 𝕎-plus; 𝕎-ψ; 𝕎⊆OT)
open import OCF.Align.EboLean.OT.WO.Lemma431 facts using (𝕎-Ω; one∈𝕎; 0∈𝕎; x+1-view)
```

## §1 τ 与严格保序 (取自 WfScoutTau)

$\tau(\mathbf 1)=\varphi'_00$, $\tau(\psi_u(0))=\Omega'_{\tau u}$ ($u\ne0$), $\tau(\psi_u(a))=\psi_{\Omega'_{\tau u+1}}(\tau a)$ ($a\ne0$), 和逐项.

```agda
φ1 : PTm
φ1 = phi zer zer

τL : E.T → List PTm
τP : E.PT → PTm
τ  : E.T → Tm
τ t = fromL (τL t)
τL [] = []
τL (x ∷ xs) = τP x ∷ τL xs
τP (E.ψ u (y ∷ ys)) = psi (ΩR (τ u ▹ φ1)) (τ (y ∷ ys))
τP (E.ψ [] []) = φ1
τP (E.ψ (w ∷ ws) []) = Om (τ (w ∷ ws))

lt-τ : ∀ s t → lt (τ s) (τ t) ≡ ltLx (τL s) (τL t)
lt-τ s t = trans (lt-list (τ s) (τ t)) (subst (λ z → ltLx z (toList (τ t)) ≡ ltLx (τL s) (τL t)) (sym (toList-fromL (τL s)))
                                         (cong (ltLx (τL s)) (toList-fromL (τL t))))

notle : ∀ s t → lt s t ≡ true → le t s ≡ false
notle s t h = trans (lin″ s t (AT-all s t)) (cong not h)

Ωlt : ∀ a c → lt a c ≡ true → lt ⟨ Om a ⟩ ⟨ Om c ⟩ ≡ true
Ωlt a c h = trans (lt-unfold≠ (Om a) (Om c) (≺⇒eqT-false a c (AT-all a c) h)) h

Ωle : ∀ a c → le a c ≡ true → le ⟨ Om a ⟩ ⟨ Om c ⟩ ≡ true
Ωle a c h with ∨-true h
... | inj₁ l = leˡ ⟨ Om a ⟩ ⟨ Om c ⟩ (Ωlt a c l)
... | inj₂ e = leʳ ⟨ Om a ⟩ ⟨ Om c ⟩ e

s1≤ : ∀ x y → lt x y ≡ true → le (x ▹ φ1) y ≡ true
s1≤ x y h = subst (λ z → le z y ≡ true) (+one x) (+1-least′ x y h)

le-lt : ∀ a b c → le a b ≡ true → lt b c ≡ true → lt a c ≡ true
le-lt a b c h g with ∨-true h
... | inj₁ l = lt-trans a b c l g
... | inj₂ e = subst (λ z → lt z c ≡ true) (sym (eqT-sound a b e)) g

s1< : ∀ x y → lt x y ≡ true → lt (x ▹ φ1) (y ▹ φ1) ≡ true
s1< x y h = le-lt (x ▹ φ1) y (y ▹ φ1) (s1≤ x y h) (≺-▹ y φ1)

eqT-ne : ∀ a c → lt a c ≡ true → eqT a c ≡ false
eqT-ne a c h = ≺⇒eqT-false a c (AT-all a c) h

τ-lt  : ∀ {s t} → s <ᵀ t → lt (τ s) (τ t) ≡ true
mono  : ∀ {s t} → s <ᵀ t → ltLx (τL s) (τL t) ≡ true
monoP : ∀ {x y} → x <ᴾ y → lt ⟨ τP x ⟩ ⟨ τP y ⟩ ≡ true

τ-lt {s} {t} q = trans (lt-τ s t) (mono q)

mono []< = refl
mono (hd< {x} {y} {xs} {ys} p) = ltLx-sing⁻ (τP x) (τL xs) (τP y) (τL ys) (monoP p)
mono (tl< {x} q) = trans (if-true (eqP-refl (τP x))) (mono q)

monoP {E.ψ [] []} {E.ψ (w ∷ ws) []} (lv< []<) = one≺P (Om (τ (w ∷ ws))) refl
monoP {E.ψ [] []} {E.ψ (w ∷ ws) (y ∷ ys)} (lv< []<) = one≺P (psi (ΩR (τ (w ∷ ws) ▹ φ1)) (τ (y ∷ ys))) refl
monoP {E.ψ (u ∷ us) []} {E.ψ (v ∷ vs) []} (lv< q) = Ωlt (τ (u ∷ us)) (τ (v ∷ vs)) (τ-lt q)
monoP {E.ψ (u ∷ us) []} {E.ψ v (y ∷ ys)} (lv< q) =
  trans (lt-unfold≠ (Om U) (psi (ΩR (V ▹ φ1)) (τ (y ∷ ys))) refl)
        (cong not (notle ⟨ Om U ⟩ ⟨ Om (V ▹ φ1) ⟩ (Ωlt U (V ▹ φ1) (lt-trans U V (V ▹ φ1) (τ-lt q) (≺-▹ V φ1)))))
  where U = τ (u ∷ us); V = τ v
monoP {E.ψ u (a ∷ as)} {E.ψ (v ∷ vs) []} (lv< q) =
  trans (lt-unfold≠ (psi (ΩR (τ u ▹ φ1)) (τ (a ∷ as))) (Om (τ (v ∷ vs))) refl)
        (Ωle (τ u ▹ φ1) (τ (v ∷ vs)) (s1≤ (τ u) (τ (v ∷ vs)) (τ-lt q)))
monoP {E.ψ u (a ∷ as)} {E.ψ v (y ∷ ys)} (lv< q) =
  trans (lt-unfold≠ (psi π A) (psi κ B) e)
        (∨-introʳ {x = eqT (τ u ▹ φ1) (τ v ▹ φ1) ∧ lt A B} (∨-introˡ (Ωlt (τ u ▹ φ1) (τ v ▹ φ1) (s1< (τ u) (τ v) (τ-lt q)))))
  where
    π = ΩR (τ u ▹ φ1); κ = ΩR (τ v ▹ φ1); A = τ (a ∷ as); B = τ (y ∷ ys)
    e : eqP (psi π A) (psi κ B) ≡ false
    e = cong (λ z → (z ∧ eqP φ1 φ1) ∧ eqT A B) (eqT-ne (τ u) (τ v) (τ-lt q))
monoP {E.ψ [] []} {E.ψ [] (y ∷ ys)} (ar< q) = one≺P (psi (ΩR (zer ▹ φ1)) (τ (y ∷ ys))) refl
monoP {E.ψ (u ∷ us) []} {E.ψ _ (y ∷ ys)} (ar< q) =
  trans (lt-unfold≠ (Om U) (psi (ΩR (U ▹ φ1)) (τ (y ∷ ys))) refl)
        (cong not (notle ⟨ Om U ⟩ ⟨ Om (U ▹ φ1) ⟩ (Ωlt U (U ▹ φ1) (≺-▹ U φ1))))
  where U = τ (u ∷ us)
monoP {E.ψ u (a ∷ as)} {E.ψ _ (y ∷ ys)} (ar< q) =
  trans (lt-unfold≠ (psi π A) (psi π B) e) (∨-introˡ (∧-intro (eqR-refl π) (τ-lt q)))
  where
    π = ΩR (τ u ▹ φ1); A = τ (a ∷ as); B = τ (y ∷ ys)
    e : eqP (psi π A) (psi π B) ≡ false
    e = trans (cong (λ z → z ∧ eqT A B) (eqR-refl π)) (eqT-ne A B (τ-lt q))

τ-mono : ∀ {s t} → s <ᵀ t → τ s ≺ τ t
τ-mono q = lt! (τ-lt q)
```

一切 τ-像 $\prec I$ (`τ≺I`): Lemma 4.31 (a) 的 Ω-封闭要这个前提.

```agda
τ≺I  : ∀ t → lt (τ t) ⟨ I ⟩ ≡ true
τP≺I : ∀ x → lt ⟨ τP x ⟩ ⟨ I ⟩ ≡ true
s1≺I : ∀ u → lt (τ u ▹ φ1) ⟨ I ⟩ ≡ true
τ≺I [] = lt-zer zer I
τ≺I (x ∷ xs) = trans (lt-list (τ (x ∷ xs)) ⟨ I ⟩)
  (trans (cong (λ z → ltLx z (I ∷ [])) (toList-fromL (τL (x ∷ xs)))) (ltLx-sing⁻ (τP x) (τL xs) I [] (τP≺I x)))
τP≺I (E.ψ [] []) = one≺P I refl
τP≺I (E.ψ (w ∷ ws) []) = trans (lt-unfold≠ (Om (τ (w ∷ ws))) I refl) (τ≺I (w ∷ ws))
τP≺I (E.ψ u (y ∷ ys)) =
  trans (lt-unfold≠ (psi (ΩR (τ u ▹ φ1)) (τ (y ∷ ys))) I refl)
        (leˡ ⟨ Om (τ u ▹ φ1) ⟩ ⟨ I ⟩ (trans (lt-unfold≠ (Om (τ u ▹ φ1)) I refl) (s1≺I u)))
s1≺I [] = one≺P I refl
s1≺I (w ∷ ws) = ≺-sing-▹ (τ (w ∷ ws)) φ1 I (fromL-NZ (τP w) (τL ws)) (τ≺I (w ∷ ws))
```

## §2 τ 保标准形 (对 `NF`)

门槛: τ 把下标 $X$ 送到正则基数 $\pi_X=\Omega'_{\tau X+1}$; $\pi_X\preceq'\Omega'_{\tau w+1}$ 恰当 $X\le w$.

```agda
πX : E.T → Reg
πX X = ΩR (τ X ▹ φ1)

ΩS : E.T → Tm
ΩS X = ⟨ Om (τ X ▹ φ1) ⟩

leΩ : ∀ X w → X ≤ᵀ w → le (ΩS X) (ΩS w) ≡ true
leΩ X w (inj₁ p)    = leˡ (ΩS X) (ΩS w) (Ωlt (τ X ▹ φ1) (τ w ▹ φ1) (s1< (τ X) (τ w) (τ-lt p)))
leΩ X w (inj₂ refl) = leʳ (ΩS X) (ΩS X) (eqT-refl (ΩS X))

nleΩ : ∀ X w → w <ᵀ X → le (ΩS X) (ΩS w) ≡ false
nleΩ X w p = notle (ΩS w) (ΩS X) (Ωlt (τ w ▹ φ1) (τ X ▹ φ1) (s1< (τ w) (τ X) (τ-lt p)))

∧₁ : ∀ {x y} → x ∧ y ≡ true → x ≡ true
∧₁ h = proj₁ (∧-true h)

Gs : Reg → List PTm → List Tm
Gs ρ [] = []
Gs ρ (p ∷ ps) = GP ρ p ++ Gs ρ ps

G-goL : ∀ ρ a ps → G ρ (goL a ps) ≡ G ρ a ++ Gs ρ ps
G-goL ρ a [] = sym (++-identityʳ (G ρ a))
G-goL ρ a (p ∷ ps) = trans (G-goL ρ (a ▹ p) ps) (++-assoc (G ρ a) (GP ρ p) (Gs ρ ps))

G-τ∷ : ∀ ρ x xs → G ρ (τ (x ∷ xs)) ≡ GP ρ (τP x) ++ G ρ (τ xs)
G-τ∷ ρ x xs = trans (G-goL ρ zer (τP x ∷ τL xs)) (cong (GP ρ (τP x) ++_) (sym (G-goL ρ zer (τL xs))))

all++ : ∀ xs ys b → allLt xs b ≡ true → allLt ys b ≡ true → allLt (xs ++ ys) b ≡ true
all++ [] ys b _ h = h
all++ (x ∷ xs) ys b h g = ∧-intro (∧₁ h) (all++ xs ys b (proj₂ (∧-true h)) g)

allLt≡ : ∀ {L L′} b → L ≡ L′ → allLt L′ b ≡ true → allLt L b ≡ true
allLt≡ b e h = subst (λ L → allLt L b ≡ true) (sym e) h
```

(G5): $w$ 标准且首项下标 $<X$ 时 $G_{\pi_X}(\tau w)=\emptyset$. 降序把首项的条件传给每一项.

```agda
HdLt : E.T → E.T → Set
HdLt X [] = ⊤
HdLt X (E.ψ v b ∷ _) = v <ᵀ X

hdLt : ∀ X W → W <ᵀ X → HdLt X W
hdLt X [] _ = tt
hdLt X (E.ψ v a ∷ vs) p = <ᵀ-trans (idx< v a vs) p

hd-desc : ∀ {X v b} ws → HdLe (E.ψ v b) ws → v <ᵀ X → HdLt X ws
hd-desc [] _ _ = tt
hd-desc (E.ψ v′ b′ ∷ ws) h p = ≤-< (sub≤ h) p

Gnil  : ∀ X W → NF W → HdLt X W → G (πX X) (τ W) ≡ []
GPnil : ∀ X v b → NFP (E.ψ v b) → v <ᵀ X → GP (πX X) (τP (E.ψ v b)) ≡ []
Gnil X [] _ _ = refl
Gnil X (E.ψ v b ∷ ws) (n∷ pv h nws) p =
  trans (G-τ∷ (πX X) (E.ψ v b) ws) (cong₂ _++_ (GPnil X v b pv p) (Gnil X ws nws (hd-desc ws h p)))
GPnil X [] [] _ _ = refl
GPnil X (w ∷ ws) [] (nψ nu _ _) h = Gnil X (w ∷ ws) nu (hdLt X (w ∷ ws) h)
GPnil X v (c ∷ cs) _ h = if-false (nleΩ X v h)
```

$G$ 条件经 τ: $Y$ 标准, $G_X(Y)<Z$ ⟹ $G_{\pi_X}(\tau Y)\prec'\tau Z$.

```agda
Gτ  : ∀ X Y Z → NF Y → GB X Y Z → allLt (G (πX X) (τ Y)) (τ Z) ≡ true
GτP : ∀ X v b Z → NFP (E.ψ v b) → (∀ {z} → InGP X z (E.ψ v b) → z <ᵀ Z) →
      allLt (GP (πX X) (τP (E.ψ v b))) (τ Z) ≡ true
Gτ X [] Z _ _ = refl
Gτ X (E.ψ v b ∷ ys) Z (n∷ pv _ nys) g = allLt≡ (τ Z) (G-τ∷ (πX X) (E.ψ v b) ys)
  (all++ _ _ (τ Z) (GτP X v b Z pv (λ i → g (gp i))) (Gτ X ys Z nys (λ i → g (gtl i))))
GτP X [] [] Z _ _ = refl
GτP X (w ∷ ws) [] Z (nψ nu _ _) g with dec≤ X (w ∷ ws)
... | inj₁ l = Gτ X (w ∷ ws) Z nu (λ i → g (gw l i))
... | inj₂ p = allLt≡ (τ Z) (Gnil X (w ∷ ws) nu (hdLt X (w ∷ ws) p)) refl
GτP X v (c ∷ cs) Z (nψ nv nb _) g with dec≤ X v
... | inj₁ l = allLt≡ (τ Z) (if-true (leΩ X v l))
  (∧-intro (τ-lt (g (gh l)))
    (all++ _ _ (τ Z) (all++ _ [] (τ Z) (Gτ X v Z nv (λ i → g (gw l i))) refl) (Gτ X (c ∷ cs) Z nb (λ i → g (gc l i)))))
... | inj₂ p = allLt≡ (τ Z) (if-false (nleΩ X v p)) refl
```

侧条件 (τ 的像没有 $I$, $\psi_I$) 与主定理.

```agda
fiP : ∀ w → isFi (τP w) ≡ false
fiP (E.ψ [] []) = refl
fiP (E.ψ (_ ∷ _) []) = refl
fiP (E.ψ u (_ ∷ _)) = refl

fi-goL2 : ∀ a q p ps → isFiT (goL (a ▹ q ▹ p) ps) ≡ false
fi-goL2 a q p [] = refl
fi-goL2 a q p (r ∷ rs) = fi-goL2 (a ▹ q) p r rs

fi-τ : ∀ w ws → isFiT (τ (w ∷ ws)) ≡ false
fi-τ w [] = fiP w
fi-τ w (v ∷ vs) = fi-goL2 zer (τP w) (τP v) (τL vs)

zero-goL : ∀ a p ps → isZero (goL (a ▹ p) ps) ≡ false
zero-goL a p [] = refl
zero-goL a p (r ∷ rs) = zero-goL (a ▹ p) r rs

fi1 : ∀ s → isFiT (s ▹ φ1) ≡ false
fi1 zer = refl
fi1 (a ▹ p) = refl

le1 : ∀ p → le ⟨ φ1 ⟩ ⟨ p ⟩ ≡ true
le1 p = go (eqP φ1 p) refl where
  go : ∀ b → eqP φ1 p ≡ b → le ⟨ φ1 ⟩ ⟨ p ⟩ ≡ true
  go true  e = leʳ ⟨ φ1 ⟩ ⟨ p ⟩ e
  go false e = leˡ ⟨ φ1 ⟩ ⟨ p ⟩ (one≺P p e)

snoc1 : ∀ s → isOT s ≡ true → isOT (s ▹ φ1) ≡ true
snoc1 zer _ = refl
snoc1 (a ▹ p) h = ∧-intro h (le1 p)

desc-le : ∀ {x y} → y ≤ᴾ x → le ⟨ τP y ⟩ ⟨ τP x ⟩ ≡ true
desc-le {x} {y} (inj₁ p)    = leˡ ⟨ τP y ⟩ ⟨ τP x ⟩ (monoP p)
desc-le {x} {y} (inj₂ refl) = leʳ ⟨ τP y ⟩ ⟨ τP y ⟩ (eqT-refl ⟨ τP y ⟩)

τ-NFᵇ  : ∀ {t} → NF t → isOT (τ t) ≡ true
τP-NF  : ∀ {x} → NFP x → isOTP (τP x) ≡ true
nf-sum : ∀ a x xs → isOT (a ▹ τP x) ≡ true → HdLe x xs → NF xs → isOT (goL (a ▹ τP x) (τL xs)) ≡ true

τ-NFᵇ n[] = refl
τ-NFᵇ (n∷ {x} {xs} px h nxs) = nf-sum zer x xs (τP-NF px) h nxs

nf-sum a x [] h _ _ = h
nf-sum a x (y ∷ ys) h d (n∷ py hy nys) =
  nf-sum (a ▹ τP x) y ys (∧-intro h (∧-intro (τP-NF py) (desc-le d))) hy nys

τP-NF {E.ψ [] []} _ = refl
τP-NF {E.ψ (w ∷ ws) []} (nψ nu _ _) =
  ∧-intro (τ-NFᵇ nu) (∧-intro (cong not (fi-τ w ws)) (cong not (zero-goL zer (τP w) (τL ws))))
τP-NF {E.ψ u (y ∷ ys)} (nψ nu na g) =
  ∧-intro (τ-NFᵇ na)
    (∧-intro (∧-intro (snoc1 (τ u) (τ-NFᵇ nu)) (∧-intro (cong not (fi1 (τ u))) refl))
             (Gτ u (y ∷ ys) (y ∷ ys) na g))

τ-NF : ∀ {t} → NF t → OT (τ t)
τ-NF n = ot! (τ-NFᵇ n)
```

## §3 τ 的像在 $\mathbb W$ 里

$\mathbb W$ 对 $+1$ 与 $\Omega$: $c\in\mathbb W\Rightarrow\Omega'_{c+1}\in\mathbb W$ (`𝕎Ωs`), 由 Lemma 4.29 的 `uc-+` (界取 $c^+\in\mathbb W$) 与 Lemma 4.31 (a). 和: `uc-app`, 界取 $\Omega'_{\tau v+1}$, $v$ 是首项下标; τ 保序给出 $\tau(\psi_v(b)+\cdots)\prec\Omega'_{\tau v+1}$.

```agda
+1≡ : ∀ c → OT c → c + one ≡ c ▹ φ1
+1≡ c oc with x+1-view c oc
... | inj₁ (refl , e) = e
... | inj₂ (_ , e)    = e

Ω1≡ : ∀ s → Ω (s ▹ φ1) ≡ ⟨ Om (s ▹ φ1) ⟩
Ω1≡ zer     = refl
Ω1≡ (a ▹ p) = refl

𝕎Ωs : ∀ v → 𝕎 (τ v) → 𝕎 ⟨ Om (τ v ▹ φ1) ⟩
𝕎Ωs v w = subst 𝕎 (Ω1≡ (τ v)) (𝕎-Ω w₁ (lt! (s1≺I v)))
  where
    oc = 𝕎⊆OT w
    w₁ : 𝕎 (τ v ▹ φ1)
    w₁ = subst 𝕎 (+1≡ (τ v) oc)
           (uc-+ 𝕎-UC oc OT-one (+-OT oc OT-one)
                 (plus (τ v) , 𝕎-plus w , Car-closed-+1 (plus-Car oc) (plus-OT oc) oc (≺plus oc)) w (one∈𝕎 w))

app-goL : ∀ a b ps → app a (goL b ps) ≡ goL (app a b) ps
app-goL a b [] = refl
app-goL a b (p ∷ ps) = app-goL a (b ▹ p) ps

goL-snoc : ∀ a ps p → goL a (ps ++ p ∷ []) ≡ goL a ps ▹ p
goL-snoc a [] p = refl
goL-snoc a (q ∷ qs) p = goL-snoc (a ▹ q) qs p

τL-++ : ∀ s t → τL (s ++ t) ≡ τL s ++ τL t
τL-++ [] t = refl
τL-++ (x ∷ s) t = cong (τP x ∷_) (τL-++ s t)

τ-suc : ∀ v → τ (sucT v) ≡ τ v ▹ φ1
τ-suc v = trans (cong fromL (τL-++ v (E.𝟏 ∷ []))) (goL-snoc zer (τL v) φ1)

τΩs : ∀ v → τ (E.Ωs v) ≡ ⟨ Om (τ v ▹ φ1) ⟩
τΩs []       = refl
τΩs (x ∷ xs) = cong (λ z → ⟨ Om z ⟩) (τ-suc (x ∷ xs))

𝕎τ  : ∀ {t} → NF t → 𝕎 (τ t)
𝕎τP : ∀ {x} → NFP x → 𝕎 ⟨ τP x ⟩
𝕎τ n[] = 0∈𝕎
𝕎τ (n∷ px _ n[]) = 𝕎τP px
𝕎τ {E.ψ v b ∷ y ∷ ys} nt@(n∷ px _ nys) =
  subst 𝕎 (sym e) (uc-app 𝕎-UC {y = X} {z = Y} (fromL-NZ (τP y) (τL ys)) (subst OT e (τ-NF nt)) bnd (𝕎τP px) (𝕎τ nys))
  where
    X = ⟨ τP (E.ψ v b) ⟩
    Y = τ (y ∷ ys)
    e : τ (E.ψ v b ∷ y ∷ ys) ≡ app X Y
    e = sym (app-goL X zer (τL (y ∷ ys)))
    bnd : Σ Tm (λ c → 𝕎 c × app X Y ≺ c)
    bnd = ⟨ Om (τ v ▹ φ1) ⟩ , 𝕎Ωs v (𝕎τ (nfp-u px))
        , subst (λ z → app ⟨ τP (E.ψ v b) ⟩ (τ (y ∷ ys)) ≺ z) (τΩs v)
                (subst (λ z → z ≺ τ (E.Ωs v)) e (τ-mono (hd< (lv< (<-sucT v)))))
𝕎τP {E.ψ [] []} _ = one∈𝕎 0∈𝕎
𝕎τP {E.ψ (w ∷ ws) []} (nψ nu _ _) =
  subst 𝕎 (trans (if-false (zero-goL zer (τP w) (τL ws))) (if-false (fi-τ w ws))) (𝕎-Ω (𝕎τ nu) (lt! (τ≺I (w ∷ ws))))
𝕎τP {E.ψ v (y ∷ ys)} p@(nψ nu na g) = 𝕎-ψ (𝕎Ωs v (𝕎τ nu)) (𝕎τ na) (τ-NF (nf-ψ nu na g))
```

## §4 可达性

`Acc` 是 Setzer 的可达性 (分支限于 OT, 同归档 `WO/Main` §5). $\mathbb W$ 是突出集 (`Ag𝕎`), Lemma 4.21 (c) (`Ag-Prog₁`) 给 $\mathbb W\cap\Omega_1$ 上的超限归纳. 拉回: $b<^\mathsf T t$, $b$ 标准可数 ⟹ $\tau b\prec\tau t$, $\tau b\in\mathrm{OT}$.

```agda
data Acc (y : Tm) : Set where
  acc : (∀ {z} → OT z → z ≺ y → Acc z) → Acc y

Prog₁-Acc : Prog₁ Acc
Prog₁-Acc (ox , x≺Ω₁) ih = acc (λ oz z≺x → ih ((oz , OTFacts.≺-trans facts z≺x x≺Ω₁) , oz , z≺x))

ctbl< : ∀ {t} → Ctbl t → t <ᵀ E.Ωs []
ctbl< c[]    = []<
ctbl< (c∷ _) = hd< (lv< []<)

accτ : ∀ {t} → NF t → Ctbl t → Acc (τ t)
accτ n c = Ag-Prog₁ Ag𝕎 Prog₁-Acc (𝕎τ n , τ-NF n , τ-mono (ctbl< c))

data AccNF (t : E.T) : Set where
  accNF : (∀ {b} → NF b → Ctbl b → b <ᵀ t → AccNF b) → AccNF t

goNF : ∀ {t} → Acc (τ t) → AccNF t
goNF (acc rs) = accNF (λ nb _ b<t → goNF (rs (τ-NF nb) (τ-mono b<t)))

wfNF′ : ∀ {t} → NF t → Ctbl t → AccNF t
wfNF′ n c = goNF (accτ n c)
```
