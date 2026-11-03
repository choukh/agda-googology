# 一切深度 (六): 折叠定理, 对一切深度

> 接 [UniformNF3D3R](UniformNF3D3R.lagda.md). 由 [UniformNF3D2H](UniformNF3D2H.lagda.md) 经脚本克隆. 结论先说:
>
> 1. **`FF1.FF₁`: 帧 $X$ 在世界 $w$ 上好, 则对 $w$ 里的一切点, 尾巴好推出折叠好.** 任意深度, 同一个证明. 深度只是模块的隐式参数, 证明不对它归纳.
> 2. **点是 `Pack`:** 基点 `Base`, 带世界的脊, `SG`, 世界的成员. 只有后继行换点 (`Row.outR`); 其余各行是第 0 层 `FF` 的克隆.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3H where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; tr⁻ˢ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᴵ→⊑ᴵ; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅; Ωˢ-≅; Ωˢ-refl;
  self-tr⁻ˢ; tr⁻ˢ-≅; ≅-tr⁻ˢ; ĉ-refl₀; ĉ-reflg; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; addˢ-≅)
open import OCF.Align.Uniform3Base using (InF; Dem; repA; Flr; fz; fk; _⊔_; Ev; Run; flo; cvFlo; toFlo; fold; Ω̂A; ∅ᴿ; chainA)
open import OCF.Align.UniformNF3Eq using (_≈ᴿ_; fold-≅0)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3D3O using (_≈U_; _≈S_; Fr; Sp; sf; fold1; Obs; idO; fo; fo1; addo; tro; tr⁻o; run; _≈ᵒ_; ≈ᵒ-reflˡ; ≈ᵒ-reflʳ; run-≅)
open import OCF.Align.UniformNF3D3N using (fold1-cong; Goodᴺ-tr; _⊑ᵒ_; tr⁻-cong; fold-cong; add-cong; rule4ᵒ; B1)
open import OCF.Align.UniformNF3D3G using (B1₁ᴱ; FlU; SF; SF≈; FFl; ffl; F≅; fold1-congᴱ; _⊑ᴱ_; Ctx; ctx-refl; PFl; pfl; AFl; afl; 𝟏; ⊑ᴱ-≅ʳ; ⊑ᴱ-trans; ≅→⊑ᴱ; add-rᴱ; B1ᴱ; Ω1ᴱ; suc-fold)
open import OCF.Align.UniformNF3D3C
open import OCF.Align.UniformNF3D3CF
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.UniformNF3D3F using (FL; Pd; VF; ⊑ᴱ→ᵒ)
open import OCF.Align.UniformNF3D3S using (cxV; demUp; mapV; putV; PCg)
open import OCF.Align.UniformNF3D3W
open import OCF.Align.UniformNF3D3R using (module Row)
```

## §1 辅助

```agda
module Aux {d flE} {E : Fr (suc d) flE} (fE : FFl E) (b : Base) {Q : Sp (suc d)} (pf : SF Q)
           (flQ : ∀ {i ℓ} (ev : Ev ℓ (sf Q ⊔ flE)) (p : i <ᴵ ℓ) → 𝓕b b (E Q ev p)) where
  open Cls b public
  rE : E ≈U E
  rE = FFl.rE fE
  rQ : Q ≈S Q
  rQ = SF≈ pf

  leF : ∀ {k i ℓ} (ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))) (p : i <ᴵ ℓ) (t : Ordˢ k) → t ≅ˢ t → E Q (proj₁ ev , proj₁ (proj₂ ev)) p ⊑ᴱ fold1 (flo k) (cvFlo k) E t Q ev p
  leF {k = k} ev p t et = B1₁ᴱ {φ = flo k} {E = E} {Q = Q} {cv = cvFlo k} {ev = ev} {p = p} (≅→⊑ᴱ (rE rQ _ p _ p (≅ᴵ-refl _))) t et

  flw1 : ∀ {k i ℓ} {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} (y : Ordˢ k) → y ≅ˢ y → Ωˢ i ⊑ᴱ fold1 (flo k) (cvFlo k) E y Q ev p
  flw1 {ev = ev} {p = p} y ey = ⊑ᴱ-trans (PFl.f0 (FFl.pE fE pf) (proj₁ ev , proj₁ (proj₂ ev)) p) (leF ev p y ey)

  one1 : ∀ {k i ℓ} {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} (y : Ordˢ k) → y ≅ˢ y → 𝟏 ⊑ᴱ fold1 (flo k) (cvFlo k) E y Q ev p
  one1 {i = i} {ev = ev} {p = p} y ey = ⊑ᴱ-trans (Ω1ᴱ i) (flw1 {ev = ev} {p = p} y ey)

  lfo1 : ∀ {i} {O : Obs i} → VF 𝓟 i O → ∀ {k ℓ} {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} → Ab (fo1 {k = k} O E Q ev p)
  lfo1 {i} {O} v {ev = ev} {p = p} = i , O , _ , flQ (proj₁ ev , proj₁ (proj₂ ev)) p , cxT i v , pT i v , λ t et G → leF ev p t et (ctx-refl O (cxT i v)) G

  chain1-≅ : ∀ {k j ℓ} {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
             Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
             ∀ n → chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) Q) ev n ≅ˢ
                   chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) Q) ev n
  chain1-≅ {j = j} e zero = Ωˢ-refl j
  chain1-≅ {ev = ev} {q = q} e (suc n) = F≅ {ev = ev} {ev′ = ev} rE rQ (i-respˢ e (chain1-≅ {ev = ev} e n)) _ _ (≅ᴵ-refl _)

  chain1-st : ∀ {k j ℓ} {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
              Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
              (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
              ∀ n → chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) Q) ev n ⊑ᵒ
                    chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) Q) ev (suc n)
  chain1-st {k = k} {j = j} {ev = ev} {q = q} {f = f} e hm zero =
    ⊑ᴱ→ᵒ (Ωˢ-refl j) (flw1 {ev = ev} {p = cvFlo k (proj₂ (proj₂ ev)) q} (f (intoˢ (<→◃ q) (Ωˢ j))) (i-respˢ e (Ωˢ-refl j)))
  chain1-st {ev = ev} e hm (suc n) = fold1-cong rE rQ (hm (chain1-st {ev = ev} e hm n))

  ZT1 : ∀ {k ℓ} j {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} → j <ᴵ ℓ → Cl k → Set
  ZT1 zero {ev} ac 𝓖₀ = 𝓖₀ (fo1 idO E Q ev ac)
  ZT1 (suc _) ac 𝓖₀ = ⊤
  ZT1 (lim _ _) ac 𝓖₀ = ⊤

  incE1 : ∀ {k ℓ} j {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} {ac : j <ᴵ ℓ} (𝓖₀ : Cl k) (W : Obs k → Obs j) →
          (∀ {C C′} → 𝓖₀ C → Above j C′ (W C) → 𝓖₀ C′) → (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) → ZT1 j {ev = ev} ac 𝓖₀ →
          ∀ {C} → (Σ _ λ D → Inp j (W ⟨ 𝓖₀ ⟩) D × (C ≡ fo1 D E Q ev ac)) → 𝓖₀ C
  incE1 zero 𝓖₀ W St cg zv (D , refl , refl) = zv
  incE1 (suc j) {ev} {ac} 𝓖₀ W St cg zv (D , (x , C , c , o) , refl) =
    St c (above (fE , pf , x) (λ t et → let et′ = F≅ {ev = ev} {ev′ = ev} rE rQ et ac ac (≅ᴵ-refl _) in
      _ , et′ , flw1 {ev = ev} {p = ac} t et , run-≅ o et′))
  incE1 (lim f s) {ev} {ac} 𝓖₀ W St cg zv (D , (x , C , c , o) , refl) =
    St c (above (fE , pf , x) (λ t et → let et′ = F≅ {ev = ev} {ev′ = ev} rE rQ et ac ac (≅ᴵ-refl _) in
      _ , et′ , flw1 {ev = ev} {p = ac} t et , run-≅ o et′))

  mkZ1 : ∀ {k j i ℓ} {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} {ac : j <ᴵ ℓ} {𝓖′ : Cl i} {𝓖₀ : Cl k} → (i ≺ᴵ j ⊎ j ≅ᴵ i) → Wit i 𝓖′ → (∀ {O} → 𝓖′ O → VF 𝓟 i O) →
         (∀ {O} → 𝓖′ O → 𝓖₀ (fo1 O E Q ev p)) → (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) → ZT1 j {ev = ev} ac 𝓖₀
  mkZ1 {j = zero} (inj₁ (via e ())) w H₂ m cg
  mkZ1 {j = zero} {i = zero} (inj₂ z≅) wi H₂ m cg = cg (fE , pf , tt) (fo1 idO rE rQ) (m wi)
  mkZ1 {j = suc _} cc w H₂ m cg = tt
  mkZ1 {j = lim _ _} cc w H₂ m cg = tt

```

## §2 `FF₁`

```agda
module FF1 {d flE} {E : Fr (suc d) flE} {wE : Wld (suc d)} (rX : RF (suc d) wE E) where
  fE : FFl E
  fE = fX rX
  rE′ : E ≈U E
  rE′ = FFl.rE fE

  record Pack : Set₂ where
    constructor pk
    field
      bS  : Base
      wS  : WSp (suc d)
      sgS : SG bS wS
      weS : wE bS wS
  open Pack public

  QS : Pack → Sp (suc d)
  QS S = er (wS S)

  𝓟S : Pack → Pd
  𝓟S S = 𝓟b (bS S)

  pfS : (S : Pack) → SF (QS S)
  pfS S = sfW (wS S)

  flS : (S : Pack) → ∀ {i ℓ} (ev : Ev ℓ (sf (QS S) ⊔ flE)) (p : i <ᴵ ℓ) → 𝓕b (bS S) (E (QS S) ev p)
  flS S = RFP.flX rX (bS S) (wS S) (sgS S) (weS S)

  module A′ (S : Pack) = Aux fE (bS S) {Q = QS S} (pfS S) (flS S)

  Hf₁ : (Q : Sp (suc d)) (k : Ordᴵ) {i ℓ : Ordᴵ} → Ev ℓ (sf Q ⊔ (flE ⊔ flo k)) → i <ᴵ ℓ → Cl k → Cl i → Set
  Hf₁ Q zero      ev p 𝓖 𝓖′ = 𝓖 idO
  Hf₁ Q (suc k)   ev p 𝓖 𝓖′ = ∀ {O} → 𝓖′ O → 𝓖 (fo1 O E Q ev p)
  Hf₁ Q (lim f s) ev p 𝓖 𝓖′ = ∀ {O} → 𝓖′ O → 𝓖 (fo1 O E Q ev p)

  hdnF1 : (S : Pack) {k k₀ i ℓ : Ordᴵ} (r : k ◃₁ k₀) {ev : Ev ℓ (sf (QS S) ⊔ (flE ⊔ flo k₀))} {ev₂ : Ev ℓ (sf (QS S) ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} {𝓖 : Cl k₀} {𝓖′ : Cl i} →
          (∀ {O} → 𝓖′ O → 𝓖 (fo1 O E (QS S) ev p)) → (∀ {O} → 𝓖′ O → VF (𝓟S S) i O) → Hf₁ (QS S) k ev₂ p (Dn r 𝓖) 𝓖′
  hdnF1 S {k = zero} r H H₂ = refl
  hdnF1 S {k = suc _} {i = i} r {ev = ev} {p = p} H H₂ {O} c = (fE , pfS S , cxV i (H₂ c)) , fo1 O E _ ev p , H c , fo1 (ctx-refl O (cxV i (H₂ c))) rE′ (SF≈ (pfS S))
  hdnF1 S {k = lim _ _} {i = i} r {ev = ev} {p = p} H H₂ {O} c = (fE , pfS S , cxV i (H₂ c)) , fo1 O E _ ev p , H c , fo1 (ctx-refl O (cxV i (H₂ c))) rE′ (SF≈ (pfS S))

  rowOut : (S : Pack) {k : Ordᴵ} {i ℓ : Ordᴵ} {ev : Ev ℓ (sf (QS S) ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} {𝓖′ : Cl i} →
           (∀ {O} → 𝓖′ O → VF (𝓟S S) i O) → Wit i 𝓖′ → {a : Ordˢ k} → a ≅ˢ a → (𝓚 : Cl k) →
           (∀ {O} → 𝓖′ O → 𝓚 (fo1 O E (QS S) ev p)) →
           (∀ {O C″} → 𝓚 O → FlOver a O C″ → 𝓚 C″) →
           (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓚 C′ → 𝓚 C) →
           (∀ {C} → 𝓚 C → Hon k a C) →
           (∀ b (s : WSp (suc d)) → SG b s → wE b s → ∀ {j ℓ₁} {ev₁ : Ev ℓ₁ (sf (er s) ⊔ (flE ⊔ flo k))} {p₁ : j <ᴵ ℓ₁} {𝓖₂ : Cl j} →
                 (∀ {O} → 𝓖₂ O → 𝓚 (fo1 O E (er s) ev₁ p₁)) → (∀ {O} → 𝓖₂ O → VF (𝓟b b) j O) → Wit j 𝓖₂ →
                 Good true 𝓖₂ (fold1 (flo k) (cvFlo k) E a (er s) ev₁ p₁)) →
           Good true 𝓖′ (fold1 (flo k) (cvFlo k) E (Ord₊ˢ.suc a) (QS S) ev p)
  rowOut S {ev = ev} {p = p} H₂ w ea 𝓚 Kc clk cgk ho ih =
    Row.outR rX (bS S) {fl = proj₁ (wS S)} {P = proj₁ (proj₂ (wS S))} {w = proj₁ (proj₂ (proj₂ (wS S)))} {rP = proj₁ (proj₂ (proj₂ (proj₂ (wS S))))} {s₀ = proj₂ (proj₂ (proj₂ (proj₂ (wS S))))}
      (sgS S) (weS S) {ev = ev} {p = p} H₂ w ea 𝓚 Kc clk cgk ho ih

  FF₁ : (S : Pack) {k i ℓ : Ordᴵ} {ev : Ev ℓ (sf (QS S) ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} {𝓖 : Cl k} {𝓖′ : Cl i} {x : Ordˢ k} →
        Hf₁ (QS S) k ev p 𝓖 𝓖′ → (∀ {O} → 𝓖′ O → VF (𝓟S S) i O) → Wit i 𝓖′ → Good true 𝓖 x → x ≅ˢ x → Good true 𝓖′ (fold1 (flo k) (cvFlo k) E x (QS S) ev p)
  Fk₁ : (S : Pack) {k i ℓ : Ordᴵ} {ev : Ev ℓ (sf (QS S) ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} → NZ k → ∀ {𝓖₁ : Cl k} {𝓖₂ : Cl i} {x : Ordˢ k} →
        (∀ {O} → 𝓖₂ O → 𝓖₁ (fo1 O E (QS S) ev p)) → (∀ {O} → 𝓖₂ O → VF (𝓟S S) i O) → Wit i 𝓖₂ → Good true 𝓖₁ x → x ≅ˢ x → Good true 𝓖₂ (fold1 (flo k) (cvFlo k) E x (QS S) ev p)
  passF₁ : (S : Pack) {k j i ℓ : Ordᴵ} {ev : Ev ℓ (sf (QS S) ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} {𝓖 : Cl k} {𝓖′ : Cl i} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (∀ {O} → 𝓖′ O → 𝓖 (fo1 O E (QS S) ev p)) → (∀ {O} → 𝓖′ O → VF (𝓟S S) i O) → Wit i 𝓖′ →
        ∀ {b} (e : j ≅ᴵ b) (r : b <ᴵ i) → (𝓖₀ : Cl k) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Obs k → Obs j) →
        (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ run C (f (intoˢ (<→◃ q) u))) →
        (∀ (𝓔 : Cl k) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd true j (<→◃ q) (Inp j (W ⟨ 𝓔 ⟩)) (intoˢ (<→◃ q) z) → Good true 𝓔 (f (intoˢ (<→◃ q) z))) →
        (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → (∀ {C} → 𝓖₀ C → A′.Ab S (W C)) → (∀ {C C′} → 𝓖₀ C → Above j C′ (W C) → 𝓖₀ C′) →
        (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) →
        (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
        Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
        Good true 𝓖′ (Ord₊ˢ.limᵢ r (λ y → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))) (QS S) ev p))
  chF₁ : (S : Pack) {k j i ℓ : Ordᴵ} {ev : Ev ℓ (sf (QS S) ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} {𝓖 : Cl k} {𝓖′ : Cl i} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (∀ {O} → 𝓖′ O → 𝓖 (fo1 O E (QS S) ev p)) → (∀ {O} → 𝓖′ O → VF (𝓟S S) i O) → Wit i 𝓖′ →
        (i ≺ᴵ j ⊎ j ≅ᴵ i) → (𝓖₀ : Cl k) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Obs k → Obs j) →
        (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ run C (f (intoˢ (<→◃ q) u))) →
        (∀ (𝓔 : Cl k) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd true j (<→◃ q) (Inp j (W ⟨ 𝓔 ⟩)) (intoˢ (<→◃ q) z) → Good true 𝓔 (f (intoˢ (<→◃ q) z))) →
        (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → (∀ {C} → 𝓖₀ C → A′.Ab S (W C)) → (∀ {C C′} → 𝓖₀ C → Above j C′ (W C) → 𝓖₀ C′) →
        (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) →
        (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
        Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
        Good true 𝓖′ (Ord₊ˢ.lim (λ n → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) (chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) (QS S)) ev n))) (QS S) ev p))

  FF₁ S {i = i} {ev = ev} {p = p} H H₂ w bz ex = Good-mono H₂ (vX rX (bS S) (wS S) (sgS S) (weS S) (proj₁ ev , proj₁ (proj₂ ev)) p (wit-map i H₂ w))
  FF₁ S {k = zero} {ev = ev} {p = p} H H₂ w (b1 z≅) ex = rowOut S {ev = ev} {p = p} H₂ w z≅ (λ _ → ⊤) (λ _ → tt) (λ _ _ → tt) (λ _ _ _ → tt) (λ _ G → z⊑) (λ b₁ s₁ sg₁ we₁ {ev₁ = ev₁} {p₁ = p₁} {𝓖₂ = 𝓖₂} _ H₂′ w′ → FF₁ (pk b₁ s₁ sg₁ we₁) {ev = ev₁} {p = p₁} {𝓖 = isId} {𝓖′ = 𝓖₂} refl H₂′ w′ bz z≅)
  FF₁ S {k = suc _} H H₂ w (b1 ()) ex
  FF₁ S {k = lim _ _} H H₂ w (b1 ()) ex
  FF₁ S {k = zero} {ev = ev} {p = p} H H₂ w (bs {a = b} 𝓚 v eb g clk cgk ho) ex = rowOut S {ev = ev} {p = p} H₂ w eb (λ _ → ⊤) (λ _ → tt) (λ _ _ → tt) (λ _ _ _ → tt) (λ _ G → z⊑) (λ b₁ s₁ sg₁ we₁ {ev₁ = ev₁} {p₁ = p₁} {𝓖₂ = 𝓖₂} _ H₂′ w′ → FF₁ (pk b₁ s₁ sg₁ we₁) {ev = ev₁} {p = p₁} {𝓖 = 𝓚} {𝓖′ = 𝓖₂} (v H) H₂′ w′ g eb)
  FF₁ S {k = suc _} {ev = ev} {p = p} H H₂ w (bs {a = b} 𝓚 v eb g clk cgk ho) ex = rowOut S {ev = ev} {p = p} H₂ w eb 𝓚 (λ c → v (H c)) (clk tt) (cgk tt) ho (λ b₁ s₁ sg₁ we₁ {ev₁ = ev₁} {p₁ = p₁} {𝓖₂ = 𝓖₂} K H₂′ w′ → FF₁ (pk b₁ s₁ sg₁ we₁) {ev = ev₁} {p = p₁} {𝓖 = 𝓚} {𝓖′ = 𝓖₂} K H₂′ w′ g eb)
  FF₁ S {k = lim _ _} {ev = ev} {p = p} H H₂ w (bs {a = b} 𝓚 v eb g clk cgk ho) ex = rowOut S {ev = ev} {p = p} H₂ w eb 𝓚 (λ c → v (H c)) (clk tt) (cgk tt) ho (λ b₁ s₁ sg₁ we₁ {ev₁ = ev₁} {p₁ = p₁} {𝓖₂ = 𝓖₂} K H₂′ w′ → FF₁ (pk b₁ s₁ sg₁ we₁) {ev = ev₁} {p = p₁} {𝓖 = 𝓚} {𝓖′ = 𝓖₂} K H₂′ w′ g eb)
  FF₁ S {k = suc k′} {ev = ev} {p = p} H H₂ w (bu {r = zero} g) ex =
    FF₁ S {k = k′} {ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo k′ (λ q → cvFlo (suc k′) (proj₂ (proj₂ ev)) (suc q)))} {p = p} (hdnF1 S zero {ev = ev} {p = p} H H₂) H₂ w g (u-reflˢ zero ex)
  FF₁ S {k = lim f s} {ev = ev} {p = p} H H₂ w (bu {r = self n} g) ex =
    FF₁ S {k = f n} {ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo (f n) (λ q → cvFlo (lim f s) (proj₂ (proj₂ ev)) (lim n q)))} {p = p} (hdnF1 S (self n) {ev = ev} {p = p} H H₂) H₂ w g (u-reflˢ (self n) ex)
  FF₁ S {ev = ev} {p = p} H H₂ w (bl hg st) ex = bl (λ n → FF₁ S {ev = ev} {p = p} H H₂ w (hg n) (l-invˢ ex n)) (λ n → fold1-cong rE′ (SF≈ (pfS S)) (st n))
  FF₁ S {ev = ev} {p = p} H H₂ w (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
    bĉ ys hy dy G₀ l₀ Gg lE (FF₁ S {ev = ev} {p = p} H H₂ w go (ĉ-refl₀ ex)) (λ k → FF₁ S {ev = ev} {p = p} H H₂ w (gO k) (ĉ-reflg ex _ _)) (fold1-cong rE′ (SF≈ (pfS S)) mo) (λ k → fold1-cong rE′ (SF≈ (pfS S)) (mO k))
  FF₁ S {k = zero} {ev = ev} {p = p} H H₂ w (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
    bĉ C.ys C.hy C.dy C.G₀ (≅-refl⁰ _) C.Gk (λ k → ≅-refl⁰ _)
       (FF₁ S {ev = ev} {p = p} H H₂ w g0 et)
       (λ n → FF₁ S {ev = ev} {p = p} (H , bp (C.P n)) H₂ w (gg _ (C.dy n) (H , bp (C.P n))) (eg _ _ _ _ (≅ᴵ-refl _)))
       (fold1-cong rE′ (SF≈ (pfS S)) (m _ _)) (λ n → fold1-cong rE′ (SF≈ (pfS S)) (mm _ _ _ _ (C.lmono n)))
    where module C = Ch0 𝓑 H g0 gg m mm d₀ dE ch₀ chS
  FF₁ S {k = suc _} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
    bŝ (λ η O → 𝓑 η (fo1 O E (QS S) ev p)) Bc (FF₁ S {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w g0 et)
       (λ η e w′ → FF₁ S {ev = ev} {p = p} {𝓖 = 𝓖 ∧ 𝓑 η} {𝓖′ = 𝓖′ ∧ (λ O → 𝓑 η (fo1 O E (QS S) ev p))} (λ (c , b) → H c , b) (λ c → H₂ (proj₁ c)) w′
           (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
       (F≅ {ev = ev} {ev′ = ev} rE′ (SF≈ (pfS S)) et p p (≅ᴵ-refl _)) (λ η e η′ e′ eη → F≅ {ev = ev} {ev′ = ev} rE′ (SF≈ (pfS S)) (eg η e η′ e′ eη) p p (≅ᴵ-refl _))
       (λ η e → fold1-cong rE′ (SF≈ (pfS S)) (m η e)) (λ η e η′ e′ h → fold1-cong rE′ (SF≈ (pfS S)) (mm η e η′ e′ h))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  FF₁ S {k = lim _ _} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
    bŝ (λ η O → 𝓑 η (fo1 O E (QS S) ev p)) Bc (FF₁ S {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w g0 et)
       (λ η e w′ → FF₁ S {ev = ev} {p = p} {𝓖 = 𝓖 ∧ 𝓑 η} {𝓖′ = 𝓖′ ∧ (λ O → 𝓑 η (fo1 O E (QS S) ev p))} (λ (c , b) → H c , b) (λ c → H₂ (proj₁ c)) w′
           (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
       (F≅ {ev = ev} {ev′ = ev} rE′ (SF≈ (pfS S)) et p p (≅ᴵ-refl _)) (λ η e η′ e′ eη → F≅ {ev = ev} {ev′ = ev} rE′ (SF≈ (pfS S)) (eg η e η′ e′ eη) p p (≅ᴵ-refl _))
       (λ η e → fold1-cong rE′ (SF≈ (pfS S)) (m η e)) (λ η e η′ e′ h → fold1-cong rE′ (SF≈ (pfS S)) (mm η e η′ e′ h))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  FF₁ S {k = zero} H H₂ w (bi {p = ()} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ex
  FF₁ S {k = suc k′} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ex with <ᴵ-dec (cvFlo (suc k′) (proj₂ (proj₂ ev)) q) p
  ... | injᵃ (via e r) = passF₁ S {ev = ev} {p = p} {𝓖 = 𝓖 ∧ A′.Ab S} {𝓖′ = 𝓖′} (λ c → H c , A′.lfo1 S (H₂ c)) H₂ w e r (𝓖₀ ∧ A′.Ab S) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → A′.loW S ex (Wf c) l) (λ (c , l) A′ → St c A′ , A′.abAbove S A′ (A′.loW S ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , A′.abCg S o l) hm ex
  ... | injᵇ c = chF₁ S {ev = ev} {p = p} {𝓖 = 𝓖 ∧ A′.Ab S} {𝓖′ = 𝓖′} (λ c′ → H c′ , A′.lfo1 S (H₂ c′)) H₂ w (inj₁ c) (𝓖₀ ∧ A′.Ab S) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → A′.loW S ex (Wf c) l) (λ (c , l) A′ → St c A′ , A′.abAbove S A′ (A′.loW S ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , A′.abCg S o l) hm ex
  ... | injᶜ c = chF₁ S {ev = ev} {p = p} {𝓖 = 𝓖 ∧ A′.Ab S} {𝓖′ = 𝓖′} (λ c′ → H c′ , A′.lfo1 S (H₂ c′)) H₂ w (inj₂ c) (𝓖₀ ∧ A′.Ab S) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → A′.loW S ex (Wf c) l) (λ (c , l) A′ → St c A′ , A′.abAbove S A′ (A′.loW S ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , A′.abCg S o l) hm ex
  FF₁ S {k = lim f₀ s₀} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ex with <ᴵ-dec (cvFlo (lim f₀ s₀) (proj₂ (proj₂ ev)) q) p
  ... | injᵃ (via e r) = passF₁ S {ev = ev} {p = p} {𝓖 = 𝓖 ∧ A′.Ab S} {𝓖′ = 𝓖′} (λ c → H c , A′.lfo1 S (H₂ c)) H₂ w e r (𝓖₀ ∧ A′.Ab S) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → A′.loW S ex (Wf c) l) (λ (c , l) A′ → St c A′ , A′.abAbove S A′ (A′.loW S ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , A′.abCg S o l) hm ex
  ... | injᵇ c = chF₁ S {ev = ev} {p = p} {𝓖 = 𝓖 ∧ A′.Ab S} {𝓖′ = 𝓖′} (λ c′ → H c′ , A′.lfo1 S (H₂ c′)) H₂ w (inj₁ c) (𝓖₀ ∧ A′.Ab S) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → A′.loW S ex (Wf c) l) (λ (c , l) A′ → St c A′ , A′.abAbove S A′ (A′.loW S ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , A′.abCg S o l) hm ex
  ... | injᶜ c = chF₁ S {ev = ev} {p = p} {𝓖 = 𝓖 ∧ A′.Ab S} {𝓖′ = 𝓖′} (λ c′ → H c′ , A′.lfo1 S (H₂ c′)) H₂ w (inj₂ c) (𝓖₀ ∧ A′.Ab S) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → A′.loW S ex (Wf c) l) (λ (c , l) A′ → St c A′ , A′.abAbove S A′ (A′.loW S ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , A′.abCg S o l) hm ex

  Fk₁ S {k = suc _} {ev = ev} {p = p} nk H H₂ w g ex = FF₁ S {ev = ev} {p = p} H H₂ w g ex
  Fk₁ S {k = lim _ _} {ev = ev} {p = p} nk H H₂ w g ex = FF₁ S {ev = ev} {p = p} H H₂ w g ex

  passF₁ S {k = k} {j = j} {i = i} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} {q = q} {f = f} H H₂ wi {b} e r 𝓖₀ inc₀ W Wf hb Wv lW St cg hm ex =
    bi (λ O → 𝓖₀ (fo1 O E (QS S) ev p) × VF (𝓟S S) i O) (λ c → inc₀ (H c) , H₂ c) (λ O → tr⁻o (W (fo1 O E (QS S) ev p)) e)
       (λ {O} (c , v) u eu → subst (λ y → run (W (fo1 O E (QS S) ev p)) (tr⁻ˢ e u) ≅ˢ run O (fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) (tr⁻ˢ e y))) (QS S) ev p)) (sym (out-intoˢ (<→◃ r) u))
           (Wf c (tr⁻ˢ e u) (self-tr⁻ˢ e eu)))
       (λ 𝓔′ inc″ z ez g → subst (λ y → Good true 𝓔′ (fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) (tr⁻ˢ e y))) (QS S) ev p)) (sym (out-intoˢ (<→◃ r) z))
           (Fb (λ c → _ , c , refl) (λ c → proj₂ (inc″ c)) (wit-nz i (NZ-of r))
              (hb (λ C → Σ _ λ O → 𝓔′ O × (C ≡ fo1 O E (QS S) ev p)) (λ { (O , c , refl) → proj₁ (inc″ c) }) (tr⁻ˢ e z) (self-tr⁻ˢ e ez)
                  (Good→Gd (<→◃ q) (Bb e (W ⟨ (λ C → Σ _ λ O → 𝓔′ O × (C ≡ fo1 O E (QS S) ev p)) ⟩) ((λ O → tr⁻o (W (fo1 O E (QS S) ev p)) e) ⟨ 𝓔′ ⟩)
                      (λ { (x , _ , (O , c , refl) , o) → x , x , O , c , tr⁻o o }) ez (Gd→Good (<→◃ r) g))))
              (i-respˢ ex (self-tr⁻ˢ e ez))))
       (λ {O} (c , v) → vis (cx (Wv c))
           (λ nz s es os G → tw (Wv c) (NZ-e e nz) (tr⁻ˢ e s) (self-tr⁻ˢ e es) (fl-tr⁻ e (s≅ z≅ z≅) os) G)
           (λ {b′} h t et fl G →
           cp (Wv c) (≺ᴵ-respʳ h (s≅ (≅ᴵ-sym e))) (tr⁻ˢ e t) (self-tr⁻ˢ e et) (λ ex₀ h₀ → fl-tr⁻ e ex₀ (fl ex₀ h₀)) G))
       (λ {O} {C″} (c , v) (above cx′ wrap) →
          St c (above (fE , pfS S , cx′) (λ t et →
            let t′ = fold1 (flo k) (cvFlo k) E t (QS S) ev p
                et′ = F≅ {ev = ev} {ev′ = ev} rE rQ et p p (≅ᴵ-refl i)
                u = proj₁ (wrap t′ et′)
                eu = proj₁ (proj₂ (wrap t′ et′))
                fu = proj₁ (proj₂ (proj₂ (wrap t′ et′)))
                d = proj₂ (proj₂ (proj₂ (wrap t′ et′)))
            in tr⁻ˢ e u , self-tr⁻ˢ e eu , fl-tr⁻ e (Ωˢ-refl j) (⊑ᴱ-trans (≅→⊑ᴱ (Ωˢ-≅ e)) fu) , d)) ,
          frV (NZ-of r) (vis cx′
            (λ nz t et os G →
              let u = proj₁ (wrap t et)
                  eu = proj₁ (proj₂ (wrap t et))
                  d = proj₂ (proj₂ (proj₂ (wrap t et)))
                  d₂ = Wf c (tr⁻ˢ e u) (self-tr⁻ˢ e eu)
                  ey = i-respˢ ex (self-tr⁻ˢ e eu)
              in ≺-≅tw (≅ˢ-trans d d₂) (tw (toV (NZ-of r) v) (NZ-of r) _ (F≅ {ev = ev} {ev′ = ev} rE rQ ey p p (≅ᴵ-refl i)) (one1 {ev = ev} {p = p} _ ey)) G)
            (λ {b′} h t et fl G →
            let u = proj₁ (wrap t et)
                eu = proj₁ (proj₂ (wrap t et))
                d = proj₂ (proj₂ (proj₂ (wrap t et)))
                d₂ = Wf c (tr⁻ˢ e u) (self-tr⁻ˢ e eu)
                ey = i-respˢ ex (self-tr⁻ˢ e eu)
            in pull (≅ˢ-trans d d₂)
                    (cp (toV (NZ-of r) v) h _ (F≅ {ev = ev} {ev′ = ev} rE rQ ey p p (≅ᴵ-refl i))
                        (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ h) (flw1 {ev = ev} {p = p} _ ey))) G))
            (ab→𝓟 cx′ (abAbove (above cx′ wrap) (abTr⁻ {e = e} (lW c)))))
       (λ c₀ o (c , v) → cg (fE , pfS S , c₀) (fo1 o rE rQ) c , cgT c₀ o v)
       (λ {z} {z′} h₀ → subst₂ (λ y y′ → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) (tr⁻ˢ e y))) (QS S) ev p ⊑ᵒ fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) (tr⁻ˢ e y′))) (QS S) ev p)
            (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold1-cong rE rQ (hm (tr⁻-cong h₀))))
    where
    open A′ S
    Fb : ∀ {𝓖₁ : Cl k} {𝓖₂ : Cl i} {x} → (∀ {O} → 𝓖₂ O → 𝓖₁ (fo1 O E (QS S) ev p)) → (∀ {O} → 𝓖₂ O → VF (𝓟S S) i O) → Wit i 𝓖₂ → Good true 𝓖₁ x → x ≅ˢ x → Good true 𝓖₂ (fold1 (flo k) (cvFlo k) E x (QS S) ev p)
    Fb = Fk₁ S {ev = ev} {p = p} (NZ-of q)

  chF₁ S {k} {j} {i} {ℓ} {ev} {p} {𝓖} {𝓖′} {q} {f} H H₂ wi cc 𝓖₀ inc₀ W Wf hb Wv lW St cg hm ex =
    bl (λ n → Fb H H₂ wi
          (hb 𝓖 inc₀ (chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) (QS S)) ev n) (csim n)
              (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , C , c , o) → x , C , inc₀ c , o })) (chG n))))
          (i-respˢ ex (csim n)))
       (λ n → fold1-cong rE rQ (hm (chain1-st {ev = ev} ex hm n)))
    where
    open A′ S
    Fb : ∀ {i′} {p′ : i′ <ᴵ ℓ} {𝓖₁ : Cl k} {𝓖₂ : Cl i′} {x} → (∀ {O} → 𝓖₂ O → 𝓖₁ (fo1 O E (QS S) ev p′)) → (∀ {O} → 𝓖₂ O → VF (𝓟S S) i′ O) → Wit i′ 𝓖₂ → Good true 𝓖₁ x → x ≅ˢ x → Good true 𝓖₂ (fold1 (flo k) (cvFlo k) E x (QS S) ev p′)
    Fb {p′ = p′} = Fk₁ S {ev = ev} {p = p′} (NZ-of q)
    ac : j <ᴵ ℓ
    ac = cvFlo k (proj₂ (proj₂ ev)) q
    csim : ∀ n → (chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) (QS S)) ev n) ≅ˢ (chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) (QS S)) ev n)
    csim = chain1-≅ {ev = ev} ex
    𝓔₂ : Cl k
    𝓔₂ C′ = Σ _ λ D → Inp j (W ⟨ 𝓖₀ ⟩) D × (C′ ≡ fo1 D E (QS S) ev ac)
    chG : ∀ n → Good true (Inp j (W ⟨ 𝓖₀ ⟩)) (chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) (QS S)) ev n)
    chG zero = Good-mono (inpVis j W Wv) (Ωg j)
    chG (suc n) = Fb (λ d → _ , d , refl) (visD j W Wv lW (witJ cc wi H₂)) (witI j {W ⟨ 𝓖₀ ⟩})
          (hb 𝓔₂ (incE) (chainA (λ ev′ → cvFlo k (proj₂ (proj₂ ev′)) q) (λ x → fold1 (flo k) (cvFlo k) E (f (intoˢ (<→◃ q) x)) (QS S)) ev n) (csim n)
              (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , C , e′ , o) → x , C , incE e′ , o })) (chG n))))
          (i-respˢ ex (csim n))
      where
      incE : ∀ {C} → 𝓔₂ C → 𝓖₀ C
      incE = incE1 j {ev = ev} {ac = ac} 𝓖₀ W St cg (mkZ1 cc wi H₂ (λ c → inc₀ (H c)) cg)
```
