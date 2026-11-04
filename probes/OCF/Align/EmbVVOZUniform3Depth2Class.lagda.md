> **机械克隆, 验收用.** 由 `OrdLabZUniform3Depth2Class` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZUniform3Depth2Class where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Align.OrdLabZLevel
open import OCF.Align.EmbVVOZPrefix using (Z; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.EmbVVOZDecouple using (Idx; lvI)
open import OCF.Align.EmbVVOZGoodLBase
open import OCF.Align.EmbVVOZOmegaExpBase using (OccΣ; repW; ωW; πw)
open import OCF.Align.EmbVVOZUniformS
open import OCF.Align.EmbVVOZUniform3Base
open import OCF.Align.EmbVVOZUniform3Depth1 using (cωΩ; cΩΩ; penΩ; wkL0)
open import OCF.Align.EmbVVOZUniform3Rel
open import OCF.Align.EmbVVOZUniform3SqABase
open import OCF.Align.EmbVVOZUniform3SqA using (Up0; LW0→LW)
open import OCF.Align.EmbVVOZUniform3Hon
open import OCF.Align.EmbVVOZUniform3Full using (FlrLab[]-up; LWʰ-up; limᵢ0ᴾ; GRH; GA0ʰ)
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
open GRᴬ
```

## §1 地板

```agda
FLΩ[_] : Ordᴵ → Flr → T → Set
FLΩ[ c ] φ ζ = ∀ {K} (k : InF K φ) → IgnK c k ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × (∀ b → Occ w (ψᵗ Ωᵗ (ζ ++ b) ∷ []))

FL : Ordᴵ → ℕ → Flr → T → Set
FL c zero    φ π = FlrLab[ c ] φ π
FL c (suc d) φ ζ = FLΩ[ c ] φ ζ

FLΩ→[] : ∀ {c φ ζ} → FlrLabΩ φ ζ → FLΩ[ c ] φ ζ
FLΩ→[] F k with F k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ w = inj₂ w

FLΩ-up : ∀ {c c′ φ ζ} → Up c c′ → FLΩ[ c ] φ ζ → FLΩ[ c′ ] φ ζ
FLΩ-up u F k with F k
... | inj₁ (inj₁ (inj₁ e0)) = inj₁ (inj₁ (inj₁ e0))
... | inj₁ (inj₁ (inj₂ kc)) = inj₁ (inj₁ (inj₂ (≼-trans kc u)))
... | inj₁ (inj₂ (b , le)) = inj₁ (inj₂ (b , ⊑ᴵ-trans le (sB u)))
... | inj₂ w = inj₂ w

FL-up : ∀ d {c c′ φ ζ} → Up c c′ → FL c d φ ζ → FL c′ d φ ζ
FL-up zero    = FlrLab[]-up
FL-up (suc d) = FLΩ-up
```

## §2 类 `Wd`

```agda
Wd : Ordᴵ → ∀ d {φ} → A d φ → T → Set
Wd c zero    R u = LWʰ[ c ] R u
Wd c (suc d) X ζ = ∀ {c′} → Up c c′ → ∀ {fl} {Q : A d fl} {ρ} → FL c′ d fl ρ → Wd c′ d Q ρ → Wd c′ d (X Q) (ρ ++ ψΩᵗ ζ)

≼-refl : ∀ i → i ≼ i
≼-refl i = inj₂ (≅ᴵ-refl i)

W-up : ∀ d {c c′ φ} {X : A d φ} {u} → Up c c′ → Wd c d X u → Wd c′ d X u
W-up zero    u h = LWʰ-up u h
W-up (suc d) u h u′ = h (≼-trans u u′)

wkW : ∀ d {c φ ψ} {X : A d φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → Wd c d X u → Wd c d (wk d le X) u
wkW zero    le h = wkLWʰ le h
wkW (suc d) le h u F hQ = wkW d _ (h u F hQ)

-- 帧的应用, 目标不变
```

## §3 $W$ 的行引理

```agda
limWd : ∀ d {c φ ps y ys} {F : ℕ → A d φ} → cof (y ∷ ys) ≡ cω → (∀ n → Wd c d (F n) (ps ++ fsn (y ∷ ys) n)) → Wd c d (limA d F) (ps ++ (y ∷ ys))
limWd zero {ps = ps} {y} {ys} {F} cc h = limWʰ {ps = ps} {y = y} {ys = ys} {F = F} cc h
limWd (suc d) {ps = ps} {y} {ys} {F} cc h {c′} u {Q = Q} {ρ} Fl hQ =
  limWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {F = λ m → F m Q} (cωΩ ps cc)
       (λ m → subst (λ v → Wd c′ d (F m Q) (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cc m)) (h m u Fl hQ))

ĉWd : ∀ d {c φ c₀ t₀} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {ps y ys} {O₀ : A d φ} {O : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} →
     cof (y ∷ ys) ≡ cω → (K : CCᴸ c₀ t₀ g) → Wd c d O₀ (ps ++ fsn (y ∷ ys) 0) →
     (∀ k → Wd c d (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) → Wd c d (ĉA d c₀ t₀ g O₀ O) (ps ++ (y ∷ ys))
ĉWd zero {ps = ps} {y} {ys} {O₀} {O} cw K h₀ hk = ĉWʰ {ps = ps} {y = y} {ys = ys} {O₀ = O₀} {O = O} cw K h₀ hk
ĉWd (suc d) {ps = ps} {y} {ys} {O₀} {O} cw K h₀ hk {c′} u {Q = Q} {ρ} Fl hQ =
  ĉWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {O₀ = O₀ Q} {O = λ η e → O η e Q} (cωΩ ps cw) K
     (subst (λ v → Wd c′ d (O₀ Q) (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cw 0)) (h₀ u Fl hQ))
     (λ k → subst (λ v → Wd c′ d _ (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cw (suc k))) (hk k u Fl hQ))

Ob↑ : ∀ {w ps y ys} ρ → cof (y ∷ ys) ≡ cΩ [] → Ob w ps y ys → Ob w ρ (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) []
Ob↑ {w} {ps} ρ cs ob θ = subst (λ u → Occ w (ρ ++ u)) (sym (penΩ ps cs I0 θ)) (OccΣ ρ (od (ob θ)))

ŝWd : ∀ d {c φ c₀ w′ ps y ys} {T₀ : A d φ} {G : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} →
     cof (y ∷ ys) ≡ cΩ [] → (Iw′ : Idx w′) → c₀ ⊑ᴵ suc (lvI Iw′) → Ob w′ ps y ys → Wd c d T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
     (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → Wd c d (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
     Wd c d (ŝA d c₀ T₀ G) (ps ++ (y ∷ ys))
ŝWd zero {ps = ps} {y} {ys} {T₀} {G} cs Iw′ bw ob h₀ hg = ŝWʰ {ps = ps} {y = y} {ys = ys} {T₀ = T₀} {G = G} cs Iw′ bw ob h₀ hg
ŝWd (suc d) {ps = ps} {y} {ys} {T₀} {G} cs Iw′ bw ob h₀ hg {c′} u {Q = Q} {ρ} Fl hQ =
  ŝWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {T₀ = T₀ Q} {G = λ η e → G η e Q} (cΩΩ ps cs I0) Iw′ bw (Ob↑ ρ cs ob)
     (subst (λ v → Wd c′ d (T₀ Q) (ρ ++ v)) (sym (penΩ ps cs I0 (natT 1))) (h₀ u Fl hQ))
     (λ θ Y hY lY nθ lt e → subst (λ v → Wd c′ d _ (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (hg θ Y hY lY nθ lt e u Fl hQ))

FWd : Ordᴵ → ℕ → Flr → T → PT → T → Set
FWd c zero    φ ps y ys = FW[ c ] (φ ⊔ fk zero) ps y ys
FWd c (suc d) φ ps y ys = ∀ {c′} → Up c c′ → ∀ {fl ρ} → FL c′ d fl ρ → FWd c′ d (fl ⊔ φ) ρ (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) []

cloWd : ∀ d {c φ ps y ys} {t : A d (φ ⊔ fk zero)} {g : (η : Ordᴵ) → A d (φ ⊔ fk η)} → FWd c d φ ps y ys → cof (y ∷ ys) ≡ cΩ [] →
       Wd c d t (ps ++ fsT (y ∷ ys) (natT 1)) →
       (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → Wd c d (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
       Wd c d (cloA d t g) (ps ++ (y ∷ ys))
cloWd zero {ps = ps} {y} {ys} {t} {g} fw cs h₀ hg = cloWʰ {ps = ps} {y = y} {ys = ys} {t = t} {g = g} fw cs h₀ hg
cloWd (suc d) {ps = ps} {y} {ys} {t} {g} fw cs h₀ hg {c′} u {fl} {Q} {ρ} Fl hQ =
  wkW d _ (cloWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} (fw u Fl) (cΩΩ ps cs I0)
    (subst (λ v → Wd c′ d _ (ρ ++ v)) (sym (penΩ ps cs I0 (natT 1))) (wkW d _ (h₀ u Fl hQ)))
    (λ θ Y hY lY nθ lt → subst (λ v → Wd c′ d _ (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (wkW d _ (hg θ Y hY lY nθ lt u Fl hQ))))
```

```agda
limᵢWd : ∀ d {c φ j ν ps y ys} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → A d φ} →
         cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (Inp : T → Ordˢ j → Set) → Inp (Ωt ν) (Ωˢ j) →
         (∀ {v x′} → kd j ≡ false → Out x′ (ψᵗ ν v ∷ []) → Inp (ψᵗ ν v ∷ []) x′) →
         (∀ η x → LabL x η → ∀ {i} → j ≺ᴵ i → Up c i → Wd i d (H x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ {η x} → Inp η x → Wd c d (H x) (ps ++ fsT (y ∷ ys) η)) →
         Wd c d (limᵢA d ac H) (ps ++ (y ∷ ys))
limᵢWd zero {ps = ps} {y} {ys} {ac} {H} cc Iν ej Inp i₀ hClose hPen hOut =
  limᵢWᴾ {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} cc Iν ej Inp i₀
    (λ η x l {i} ev p Iw ei ki u s → hPen η x l s u ev p Iw ei ki (≼-refl i))
    (λ ix kj uj ev → hClose kj (hOut ix ev (ac ev) Iν ej kj uj))
    hOut
limᵢWd (suc d) {ps = ps} {y} {ys} {ac} {H} cc Iν ej Inp i₀ hClose hPen hOut {c′} u {fl} {Q} {ρ} Fl hQ =
  limᵢWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {ac = λ ev → ac (proj₂ ev)} {H = λ x → H x Q}
         (cΩΩ ps cc Iν) Iν ej Inp i₀ hClose
         (λ η x l {i} s ui → subst (λ v → Wd i d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η))
                                   (hPen η x l s (≼-trans u ui) (≼-refl i) (FL-up d ui Fl) (W-up d ui hQ)))
         (λ {η} {x} ix → subst (λ v → Wd c′ d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (hOut ix u Fl hQ))

-- 普通形: 一切带标签的输入都好
```

## §4 互模拟 `Rd`

```agda
Rd : ∀ d {φ ψ} → A d φ → A d ψ → Set
Rd zero    R R′ = R ≈ᴬ R′
Rd (suc d) X X′ = ∀ {fl fl′} {Q : A d fl} {Q′ : A d fl′} → fl ∼ᶠ fl′ → Rd d Q Q′ → Rd d (X Q) (X′ Q′)

wkRd : ∀ d {φ φ′ ψ ψ′} {X : A d φ} {X′ : A d φ′} (le : ∀ {L} → Ev L ψ → Ev L φ) (le′ : ∀ {L} → Ev L ψ′ → Ev L φ′) →
       Rd d X X′ → Rd d (wk d le X) (wk d le′ X′)
wkRd zero    le le′ h = wkRᴬ le le′ h
wkRd (suc d) le le′ h s H = wkRd d _ _ (h s H)

limRd : ∀ d {φ ψ} {F : ℕ → A d φ} {G : ℕ → A d ψ} → (∀ n → Rd d (F n) (G n)) → Rd d (limA d F) (limA d G)
limRd zero    h = limRᴬ h
limRd (suc d) h s H = limRd d (λ n → h n s H)

limᵢRd : ∀ d {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L}
         {H : Ordˢ j → A d φ} {H′ : Ordˢ j′ → A d ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ᴬ y → Rd d (H x) (H′ y)) → Rd d (limᵢA d ac H) (limᵢA d ac′ H′)
limᵢRd zero    {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h = limᵢRᴬ {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h
limᵢRd (suc d) {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h {Q = Q} {Q′ = Q′} s H₀ =
  limᵢRd d {ac = λ ev → ac (proj₂ ev)} {ac′ = λ ev → ac′ (proj₂ ev)} {H = λ x → H x Q} {H′ = λ x → H′ x Q′} e (λ x y dd → h x y dd s H₀)

ĉRd : ∀ d {φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
      {O₀ : A d φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → A d φ} {O₀′ : A d ψ} {O′ : (η : Ordᴵ) → c′ ⊑ᴵ η → A d ψ} →
      c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
      Rd d O₀ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Rd d (O η e) (O′ η′ e′)) → Rd d (ĉA d c t₀ g O₀ O) (ĉA d c′ t₀′ g′ O₀′ O′)
ĉRd zero    ec dt dg h₀ h = ĉRᴬ ec dt dg h₀ h
ĉRd (suc d) ec dt dg h₀ h s H = ĉRd d ec dt dg (h₀ s H) (λ η e η′ e′ eη → h η e η′ e′ eη s H)

ŝRd : ∀ d {φ ψ c c′} {T₀ : A d φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → A d φ} {T₀′ : A d ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → A d ψ} →
      c ≅ᴵ c′ → Rd d T₀ T₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Rd d (G η e) (G′ η′ e′)) → Rd d (ŝA d c T₀ G) (ŝA d c′ T₀′ G′)
ŝRd zero    ec h₀ h = ŝRᴬ ec h₀ h
ŝRd (suc d) ec h₀ h s H = ŝRd d ec (h₀ s H) (λ η e η′ e′ eη → h η e η′ e′ eη s H)

cloRd : ∀ d {φ φ′} {t : A d (φ ⊔ fk zero)} {g : (η : Ordᴵ) → A d (φ ⊔ fk η)}
        {t′ : A d (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → A d (φ′ ⊔ fk η)} → φ ∼ᶠ φ′ →
        Rd d t t′ → (∀ η η′ → η ≅ᴵ η′ → Rd d (g η) (g′ η′)) → Rd d (cloA d t g) (cloA d t′ g′)
cloRd zero    {t = t} {g = g} {t′ = t′} {g′ = g′} s ht hg = cloRᴬ {t = t} {g = g} {t′ = t′} {g′ = g′} s ht hg
cloRd (suc d) sφ ht hg s H =
  wkRd d _ _ (cloRd d (⊔∼ s sφ) (wkRd d _ _ (ht s H)) (λ η η′ eη → wkRd d _ _ (hg η η′ eη s H)))
```

## §5 全类 `Gc` 与 `Od`

```agda
FLg : ℕ → Flr → T → Set
FLg zero    φ π = FlrLab φ π
FLg (suc d) φ ζ = FlrLabΩ φ ζ

FLg→FL : ∀ d {c φ ζ} → FLg d φ ζ → FL c d φ ζ
FLg→FL zero    = FlrLab→[]
FLg→FL (suc d) = FLΩ→[]

Od : ∀ d {φ} → A d φ → T → Set
Hd : ∀ d {φ} → A d φ → T → Set
Gc : ∀ d {φ} → A d φ → T → Set

Od zero    R u = L0 R u
Od (suc d) X ζ = ∀ {fl} {Q : A d fl} {ρ} → Gc d Q ρ → Od d (X Q) (ρ ++ ψΩᵗ ζ)

Hd zero    R u = GRH R u
Hd (suc d) X ζ = (∀ {c} → Wd c (suc d) X ζ) × Od (suc d) X ζ × Rd (suc d) X X

Gc d {φ} X u = FLg d φ u × Hd d X u

LWʰ-z : ∀ {c φ} {R : Run φ} {u} → LWʰ[ zero ] R u → LWʰ[ c ] R u
LWʰ-z h ev p Iw ei ki _ = h ev p Iw ei ki (Up0 Iw ei ki)

H→W : ∀ d {c φ} {X : A d φ} {u} → Hd d X u → Wd c d X u
H→W zero    (_ , h) = LWʰ-z h
H→W (suc d) h = proj₁ h

H→O : ∀ d {φ} {X : A d φ} {u} → Hd d X u → Od d X u
H→O zero    (g , _) = g0ᴬ g
H→O (suc d) h = proj₁ (proj₂ h)

H→R : ∀ d {φ} {X : A d φ} {u} → Hd d X u → Rd d X X
H→R zero    (g , _) = gRᴬ g
H→R (suc d) h = proj₂ (proj₂ h)

G→FL : ∀ d {c φ} {X : A d φ} {u} → Gc d X u → FL c d φ u
G→FL d G = FLg→FL d (proj₁ G)

G→W : ∀ d {c φ} {X : A d φ} {u} → Gc d X u → Wd c d X u
G→W d G = H→W d (proj₂ G)

wkO : ∀ d {φ ψ} {X : A d φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → Od d X u → Od d (wk d le X) u
wkO zero    {X = X} le h = wkL0 {R = X} le h
wkO (suc d) le h G = wkO d _ (h G)
```

## §6 $O$ 的行引理

```agda
limOd : ∀ d {φ ps y ys} {F : ℕ → A d φ} → cof (y ∷ ys) ≡ cω → (∀ n → Od d (F n) (ps ++ fsn (y ∷ ys) n)) → Od d (limA d F) (ps ++ (y ∷ ys))
limOd zero {ps = ps} {y} {ys} {F} cc h = lim0 {ps = ps} {y = y} {ys = ys} {F = F} cc h
limOd (suc d) {ps = ps} {y} {ys} {F} cc h {Q = Q} {ρ} G =
  limOd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {F = λ m → F m Q} (cωΩ ps cc)
        (λ m → subst (λ v → Od d (F m Q) (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cc m)) (h m G))

ĉOd : ∀ d {φ c₀ t₀} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {ps y ys} {O₀ : A d φ} {O : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} →
      cof (y ∷ ys) ≡ cω → (K : CCᴸ c₀ t₀ g) → Od d O₀ (ps ++ fsn (y ∷ ys) 0) →
      (∀ k → Od d (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) → Od d (ĉA d c₀ t₀ g O₀ O) (ps ++ (y ∷ ys))
ĉOd zero {ps = ps} {y} {ys} {O₀} {O} cw K h₀ hk = ĉ0 {ps = ps} {y = y} {ys = ys} {O₀ = O₀} {O = O} cw K h₀ hk
ĉOd (suc d) {ps = ps} {y} {ys} {O₀} {O} cw K h₀ hk {Q = Q} {ρ} G =
  ĉOd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {O₀ = O₀ Q} {O = λ η e → O η e Q} (cωΩ ps cw) K
      (subst (λ v → Od d (O₀ Q) (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cw 0)) (h₀ G))
      (λ k → subst (λ v → Od d _ (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cw (suc k))) (hk k G))

ŝOd : ∀ d {φ c₀ w′ ps y ys} {T₀ : A d φ} {G : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} →
      cof (y ∷ ys) ≡ cΩ [] → (Iw′ : Idx w′) → c₀ ⊑ᴵ suc (lvI Iw′) → Ob w′ ps y ys → Od d T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
      (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → Od d (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
      Od d (ŝA d c₀ T₀ G) (ps ++ (y ∷ ys))
ŝOd zero {ps = ps} {y} {ys} {T₀} {G} cs Iw′ bw ob h₀ hg = ŝ0 {ps = ps} {y = y} {ys = ys} {T₀ = T₀} {G = G} cs Iw′ bw ob h₀ hg
ŝOd (suc d) {ps = ps} {y} {ys} {T₀} {G} cs Iw′ bw ob h₀ hg {Q = Q} {ρ} GQ =
  ŝOd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {T₀ = T₀ Q} {G = λ η e → G η e Q} (cΩΩ ps cs I0) Iw′ bw (Ob↑ ρ cs ob)
      (subst (λ v → Od d (T₀ Q) (ρ ++ v)) (sym (penΩ ps cs I0 (natT 1))) (h₀ GQ))
      (λ θ Y hY lY nθ lt e → subst (λ v → Od d _ (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (hg θ Y hY lY nθ lt e GQ))

FWo : ℕ → Flr → T → PT → T → Set
FWo zero    φ ps y ys = FW (φ ⊔ fk zero) ps y ys
FWo (suc d) φ ps y ys = ∀ {fl ρ} → FLg d fl ρ → FWo d (fl ⊔ φ) ρ (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) []

cloOd : ∀ d {φ ps y ys} {t : A d (φ ⊔ fk zero)} {g : (η : Ordᴵ) → A d (φ ⊔ fk η)} → FWo d φ ps y ys → cof (y ∷ ys) ≡ cΩ [] →
        Od d t (ps ++ fsT (y ∷ ys) (natT 1)) →
        (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → Od d (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
        Od d (cloA d t g) (ps ++ (y ∷ ys))
cloOd zero {ps = ps} {y} {ys} {t} {g} fw cs h₀ hg = clo0 {ps = ps} {y = y} {ys = ys} {t = t} {g = g} fw cs h₀ hg
cloOd (suc d) {ps = ps} {y} {ys} {t} {g} fw cs h₀ hg {fl} {Q} {ρ} G =
  wkO d _ (cloOd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} (fw (proj₁ G)) (cΩΩ ps cs I0)
    (subst (λ v → Od d _ (ρ ++ v)) (sym (penΩ ps cs I0 (natT 1))) (wkO d _ (h₀ G)))
    (λ θ Y hY lY nθ lt → subst (λ v → Od d _ (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (wkO d _ (hg θ Y hY lY nθ lt G))))

limᵢOᴬ : ∀ d {φ j ν ps y ys} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → A d φ} →
         cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (∀ η x → LabL x η → Wd zero d (H x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ η x → LabL x η → x ≅ᴬ x → Od d (H x) (ps ++ fsT (y ∷ ys) η) × Rd d (H x) (H x)) →
         Od d (limᵢA d ac H) (ps ++ (y ∷ ys))
limᵢOᴬ zero {ps = ps} {y} {ys} {ac} {H} cc Iν ej hW h0 =
  limᵢ0ᴬ {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} cc Iν ej (λ η x l → LW0→LW (LWʰ→ (hW η x l))) h0
limᵢOᴬ (suc d) {ps = ps} {y} {ys} {ac} {H} cc Iν ej hW h0 {fl} {Q} {ρ} G =
  limᵢOᴬ d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {ac = λ ev → ac (proj₂ ev)} {H = λ x → H x Q}
         (cΩΩ ps cc Iν) Iν ej
         (λ η x l → subst (λ v → Wd zero d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (hW η x l (≼-refl zero) (G→FL d G) (G→W d G)))
         (λ η x l xx → subst (λ v → Od d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (proj₁ (h0 η x l xx) G) ,
                       proj₂ (h0 η x l xx) (∼ᶠ-refl fl) (H→R d (proj₂ G)))

limᵢOᴾ : ∀ d {φ j ν ps y ys} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → A d φ} →
         kd j ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (Inp : T → Ordˢ j → Set) → Inp (Ωt ν) (Ωˢ j) →
         (∀ {v x′} → Out x′ (ψᵗ ν v ∷ []) → x′ ≅ᴬ x′ → Inp (ψᵗ ν v ∷ []) x′) →
         (∀ {η x} → Inp η x → Wd j d (H x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ {η x} → Inp η x → Rd d (H x) (H x)) →
         (∀ {η x} → Inp η x → Od d (H x) (ps ++ fsT (y ∷ ys) η)) →
         Od d (limᵢA d ac H) (ps ++ (y ∷ ys))
limᵢOᴾ zero {j = j} {ps = ps} {y} {ys} {ac} {H} kj cc Iν ej Inp i₀ hClose hW hR hO =
  limᵢ0ᴾ {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} kj cc Iν ej Inp i₀
    (λ ix ev → hClose (hW ix ev (ac ev) Iν ej kj (≼-refl j)) (hR ix ev (ac ev) ev (ac ev) (≅ᴵ-refl j))) hO
limᵢOᴾ (suc d) {j = j} {ps = ps} {y} {ys} {ac} {H} kj cc Iν ej Inp i₀ hClose hW hR hO {fl} {Q} {ρ} G =
  limᵢOᴾ d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {ac = λ ev → ac (proj₂ ev)} {H = λ x → H x Q}
         kj (cΩΩ ps cc Iν) Iν ej Inp i₀ hClose
         (λ {η} {x} ix → subst (λ v → Wd j d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (hW ix (≼-refl j) (G→FL d G) (G→W d G)))
         (λ ix → hR ix (∼ᶠ-refl fl) (H→R d (proj₂ G)))
         (λ {η} {x} ix → subst (λ v → Od d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (hO ix G))
```
