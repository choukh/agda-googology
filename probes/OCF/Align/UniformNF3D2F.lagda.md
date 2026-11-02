# 抽象类族上的折叠定理 (一): `FF`

> 接 [UniformNF3D1F](UniformNF3D1F.lagda.md), 证明同形, 只把类族换成抽象的. 结论先说:
>
> 1. **`VF 𝓟 i = VisT i ∧ 𝓟`, $\mathcal P$ 只要两条封闭性:** 相似 (`pCg`) 与 "压在 $a$ 之上, $a\sqsupseteq Q$" (`pOv`, 跨层). 第 0 层也一样: `idO` 要满足 $\mathcal P$, 否则那个目标的类就是空的.
> 2. **吸收者 `Ab C`: 存在 $O\in\mathcal P$, 使 $C$ 下的一切值 $\sqsupseteq O$ 下 $Q$ 的值.** 折叠给出它 (`lfo`), 它沿语义搬运 (`abSem`), 它给出 $\mathcal P$ (`ab→𝓟`). `LoD` 没有了.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D2F where

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
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; Run; flo; cvFlo; toFlo; fold; Ω̂A; ∅ᴿ; chainA)
open import OCF.Align.UniformNF3Eq using (_≈₁_; _≈ᴿ_; fold-≅0)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3D1O using (Obs; idO; fo; addo; tro; tr⁻o; run; _≈ᵒ_; ≈ᵒ-reflˡ; ≈ᵒ-reflʳ; run-≅)
open import OCF.Align.UniformNF3D1N using (Goodᴺ-tr; _⊑ᵒ_; tr⁻-cong; fold-cong; add-cong; rule4ᵒ; B1)
open import OCF.Align.UniformNF3D1G using (_⊑ᴱ_; Ctx; ctx-refl; PFl; pfl; AFl; afl; 𝟏; ⊑ᴱ-≅ʳ; ⊑ᴱ-trans; ≅→⊑ᴱ; add-rᴱ; B1ᴱ; Ω1ᴱ; suc-fold)
open import OCF.Align.UniformNF3D1C
open import OCF.Align.UniformNF3D1CF
open import OCF.Align.Stage2Label using (one⁰)
```

## §1 辅助

`⊑ᴱ→ᵒ`: `⊑ᵒ` 由 `⊑ᴱ` 与计值无关性得出. `chain-≅`, `chain-st`: 链 (Goodᴺ 版). `toV`/`frV`: 非零目标的 `VT`.

```agda
⊑ᴱ→ᵒ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ x → x ⊑ᴱ y → x ⊑ᵒ y
⊑ᴱ→ᵒ ex h o G G′ = ⊑-trans (≅→⊑ (forceᴺ-≅ (toZ-≅ (run-≅ (≈ᵒ-reflˡ o) ex)) G (proj₁ (h o G′)))) (proj₂ (h o G′))

NZ-≺ : ∀ {i j} → i ≺ᴵ j → NZ j
NZ-≺ {j = suc _}   _ = tt
NZ-≺ {j = lim _ _} _ = tt
NZ-≺ {j = zero} (via e ())

module ChainM {fl} {Q : Run fl} (pf : PFl Q) where
  rQ : Q ≈ᴿ Q
  rQ = PFl.rP pf

  chain-≅ : ∀ {φ k j ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
            Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
            ∀ n → chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n ≅ˢ
                  chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n
  chain-≅ {j = j} e zero = Ωˢ-refl j
  chain-≅ {φ = φ} {cv = cv} {ev = ev} {q = q} e (suc n) =
    fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ (i-respˢ e (chain-≅ {φ = φ} {cv = cv} {ev = ev} e n)) ev _ ev _ (≅ᴵ-refl _)

  chain-st : ∀ {φ k j ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
             Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
             (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
             ∀ n → chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n ⊑ᵒ
                   chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev (suc n)
  chain-st {φ = φ} {j = j} {cv = cv} {ev = ev} {q = q} {f = f} e hm zero =
    ⊑ᴱ→ᵒ (Ωˢ-refl j) (B1ᴱ {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} {x = Ωˢ j} rQ (PFl.f0 pf (proj₁ ev) (cv (proj₂ ev) q))
          (f (intoˢ (<→◃ q) (Ωˢ j))) (i-respˢ e (Ωˢ-refl j)))
  chain-st {φ = φ} {cv = cv} {ev = ev} e hm (suc n) = fold-cong rQ (hm (chain-st {φ = φ} {cv = cv} {ev = ev} e hm n))
```

## §2 折叠定理

`F`: 尾巴在类 `𝓖` 里好, 则折叠输出在任意满足下面条件的类 `𝓖′` 里好: `O ∈ 𝓖′` 推出 `fo φ O Q cv ev p ∈ 𝓖` (第 0 层尾巴: `𝓖 idO`), 且 `O ∈ VT i`. 这是阶段无关的: `Q` 只经 `PFl` 与值 `vQ` 进入.

```agda
Hf : ∀ {fl} (Q : Run fl) (φ : Flr) (k : Ordᴵ) {i ℓ} → (∀ {L} → Ev L φ → Simᴵ k L) → Ev ℓ (fl ⊔ φ) → i <ᴵ ℓ → Cl k → Cl i → Set
Hf Q φ zero      cv ev p 𝓖 𝓖′ = 𝓖 idO
Hf Q φ (suc k)   cv ev p 𝓖 𝓖′ = ∀ {O} → 𝓖′ O → 𝓖 (fo φ O Q cv ev p)
Hf Q φ (lim f s) cv ev p 𝓖 𝓖′ = ∀ {O} → 𝓖′ O → 𝓖 (fo φ O Q cv ev p)



FL : ∀ {i j} → Ordˢ i → Obs i → Obs j → Set
FL {j = j} a O C = (t : Ordˢ j) → t ≅ˢ t → (G : Goodᴺ (toZ (run C t))) → Σ (Goodᴺ (toZ (run O a))) λ H → forceᴺ _ H ⊑ forceᴺ _ G

Pd : Set₁
Pd = ∀ {i} → Obs i → Set

VF : Pd → ∀ i → Cl i
VF 𝓟 zero      = λ O → isId O × 𝓟 O
VF 𝓟 (suc i)   = λ O → Vis (suc (suc i)) O × 𝓟 O
VF 𝓟 (lim f s) = λ O → Vis (suc (lim f s)) O × 𝓟 O

module FoldQ (𝓟 : Pd) (pCg : ∀ {i} {C C′ : Obs i} → Ctx C → C ≈ᵒ C′ → 𝓟 C′ → 𝓟 C) {fl} (Q : Run fl) (pf : PFl Q)
             (pOv : ∀ {i j ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) {a : Ordˢ i} {O : Obs i} {C″ : Obs j} → Q ev p ⊑ᴱ a → Ctx O → 𝓟 O → Ctx C″ → FL a O C″ → 𝓟 C″)
             (vQ : ∀ {i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → Wit i (VF 𝓟 i) → Good true (VF 𝓟 i) (Q ev p)) where
  open ChainM pf

  toV : ∀ {i} {O : Obs i} → NZ i → VF 𝓟 i O → Vis (suc i) O
  toV {i = suc _}   nz v = proj₁ v
  toV {i = lim _ _} nz v = proj₁ v

  frV : ∀ {i} {O : Obs i} → NZ i → Vis (suc i) O → 𝓟 O → VF 𝓟 i O
  frV {i = suc _}   nz v l = v , l
  frV {i = lim _ _} nz v l = v , l

  cxT : ∀ i {O : Obs i} → VF 𝓟 i O → Ctx O
  cxT zero (refl , _) = tt
  cxT (suc _) v = cx (proj₁ v)
  cxT (lim _ _) v = cx (proj₁ v)

  pT : ∀ i {O : Obs i} → VF 𝓟 i O → 𝓟 O
  pT zero v = proj₂ v
  pT (suc _) v = proj₂ v
  pT (lim _ _) v = proj₂ v

  Ab : ∀ {k} → Obs k → Set
  Ab C = Σ Ordᴵ λ i → Σ (Obs i) λ O → Σ Ordᴵ λ ℓ → Σ (Ev ℓ fl) λ ev → Σ (i <ᴵ ℓ) λ p → Ctx O × 𝓟 O × FL (Q ev p) O C

  abSem : ∀ {k k′} {A′ : Obs k} {B : Obs k′} → (∀ t → t ≅ˢ t → Σ (Ordˢ k′) λ u → (u ≅ˢ u) × (run A′ t ≅ˢ run B u)) → Ab B → Ab A′
  abSem h (i , O , ℓ , ev , p , c , π , fl′) = i , O , ℓ , ev , p , c , π , λ t et G →
    let d = toZ-≅ (proj₂ (proj₂ (h t et)))
        G′ = Goodᴺ-tr d G
        R = fl′ (proj₁ (h t et)) (proj₁ (proj₂ (h t et))) G′
    in proj₁ R , ⊑-trans (proj₂ R) (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym d) G′ G))

  abCg : ∀ {k} {C C′ : Obs k} → C ≈ᵒ C′ → Ab C′ → Ab C
  abCg o = abSem (λ s es → s , es , run-≅ o es)

  abAbove : ∀ {j ℓ} {C′ : Obs ℓ} {D′ : Obs j} → Above j C′ D′ → Ab D′ → Ab C′
  abAbove (above _ wrap) = abSem (λ t et → proj₁ (wrap t et) , proj₁ (proj₂ (wrap t et)) , proj₂ (proj₂ (proj₂ (wrap t et))))

  abTr⁻ : ∀ {a b} {X : Obs a} {e : a ≅ᴵ b} → Ab X → Ab (tr⁻o X e)
  abTr⁻ {e = e} (i , O , ℓ , ev , p , c , π , fl′) = i , O , ℓ , ev , p , c , π , λ s es G → fl′ (tr⁻ˢ e s) (self-tr⁻ˢ e es) G

  ab→𝓟 : ∀ {k} {C : Obs k} → Ctx C → Ab C → 𝓟 C
  ab→𝓟 x (i , O , ℓ , ev , p , c , π , fl′) = pOv ev p (≅→⊑ᴱ (PFl.rP pf ev p ev p (≅ᴵ-refl i))) c π x fl′

  lfo : ∀ {i} {O : Obs i} → VF 𝓟 i O → ∀ {φ k ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} → Ab (fo φ O Q cv ev p)
  lfo {i} {O} v {φ} {cv = cv} {ev = ev} {p = p} = i , O , _ , proj₁ ev , p , cxT i v , pT i v , λ s es G →
    B1ᴱ {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} {x = Q (proj₁ ev) p} (PFl.rP pf) (≅→⊑ᴱ (PFl.rP pf (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i))) s es (ctx-refl O (cxT i v)) G

  VT : ∀ i → Cl i
  VT = VF 𝓟

  flw-fold : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} (y : Ordˢ k) → y ≅ˢ y → Ωˢ i ⊑ᴱ fold 0 φ cv Q y ev p
  flw-fold {φ = φ} {cv = cv} {ev = ev} {p = p} y ey = B1ᴱ {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} rQ (PFl.f0 pf (proj₁ ev) p) y ey

  one-fold : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} (y : Ordˢ k) → y ≅ˢ y → 𝟏 ⊑ᴱ fold 0 φ cv Q y ev p
  one-fold {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} y ey =
    B1ᴱ {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} rQ (⊑ᴱ-trans (Ω1ᴱ i) (PFl.f0 pf (proj₁ ev) p)) y ey

  -- VT i 对 "压在一个地板 ⊒ Ω_i 的 a 之上" 封闭
  clT : ∀ {i ℓ₀} {ev₀ : Ev ℓ₀ fl} {p₀ : i <ᴵ ℓ₀} {a : Ordˢ i} → Q ev₀ p₀ ⊑ᴱ a → a ≅ˢ a → Ωˢ i ⊑ᴱ a → (𝟏 ⊑ᴱ a) → NZ i → ∀ {O C″} → VT i O → FlOver a O C″ → VT i C″
  clT {i} {ev₀ = ev₀} {p₀ = p₀} {a} qa ea fa oa nz v f′ = frV nz (vis (cxo f′)
    (λ nz₂ t et os G → proj₂ (flw f′ t et G) (tw (toV nz v) nz₂ a ea oa (proj₁ (flw f′ t et G))))
    (λ {b} h t et fl G →
    ⊑ᴵ-trans (cp (toV nz v) h a ea (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ h) fa) (proj₁ (flw f′ t et G)))
             (toLevel-⊑ (forceᴺ-HS _ _) (forceᴺ-HS _ G) (proj₂ (flw f′ t et G)))))
    (pOv ev₀ p₀ qa (cxT i v) (pT i v) (cxo f′) (flw f′))

  cgT : ∀ {i} {C C′ : Obs i} → Ctx C → C ≈ᵒ C′ → VT i C′ → VT i C
  cgT {i = zero} c₀ o (refl , t) = ≈-id o , pCg c₀ o t
  cgT {i = suc _} c₀ o v = Vis-≈ c₀ o (proj₁ v) , pCg c₀ o (proj₂ v)
  cgT {i = lim _ _} c₀ o v = Vis-≈ c₀ o (proj₁ v) , pCg c₀ o (proj₂ v)

  hselfT : ∀ i {ℓ₀} {ev₀ : Ev ℓ₀ fl} {p₀ : i <ᴵ ℓ₀} {a : Ordˢ i} → Q ev₀ p₀ ⊑ᴱ a → Wit i (VT i) → a ≅ˢ a → (𝟏 ⊑ᴱ a) → Ωˢ i ⊑ᴱ a → Hk i (VT i) a (λ q → q) (VT i)
  hselfT zero      qa wv ea oa fa = wv
  hselfT (suc j)   qa wv ea oa fa {O} v = clT qa ea fa oa tt v (flo-over (afl ea oa , cx (proj₁ v)) (λ t et G → add-rᴱ {a = _} {a′ = _} {σ = λ q → q} t ea et (ctx-refl O (cx (proj₁ v))) G))
  hselfT (lim f s) qa wv ea oa fa {O} v = clT qa ea fa oa tt v (flo-over (afl ea oa , cx (proj₁ v)) (λ t et G → add-rᴱ {a = _} {a′ = _} {σ = λ q → q} t ea et (ctx-refl O (cx (proj₁ v))) G))


  inpVis : ∀ {k} j {𝓖₀ : Cl k} (W : Obs k → Obs j) → (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → ∀ {D} → Inp j (W ⟨ 𝓖₀ ⟩) D → Vis j D
  inpVis zero W Wv refl = vis tt (λ ()) (λ { (via _ ()) })
  inpVis (suc j) W Wv (x , C , c , o) = Vis-≈ x o (Vis-mono ≺-suc (Wv c))
  inpVis (lim f s) W Wv (x , C , c , o) = Vis-≈ x o (Vis-mono ≺-suc (Wv c))

  visD : ∀ {k} j {𝓖₀ : Cl k} (W : Obs k → Obs j) → (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → (∀ {C} → 𝓖₀ C → Ab (W C)) → Wit j (VT j) → ∀ {D′} → Inp j (W ⟨ 𝓖₀ ⟩) D′ → VT j D′
  visD zero W Wv lW wj refl = wj
  visD (suc j) W Wv lW wj (x , C , c , o) = Vis-≈ x o (Wv c) , ab→𝓟 x (abCg o (lW c))
  visD (lim f s) W Wv lW wj (x , C , c , o) = Vis-≈ x o (Wv c) , ab→𝓟 x (abCg o (lW c))

  loW : ∀ {k j} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {C : Obs k} {W′ : Obs j} →
        Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → (∀ u → u ≅ˢ u → run W′ u ≅ˢ run C (f (intoˢ (<→◃ q) u))) → Ab C → Ab W′
  loW ex wf = abSem (λ u eu → _ , i-respˢ ex eu , wf u eu)

  witJ : ∀ {i j} {𝓖′ : Cl i} → (i ≺ᴵ j ⊎ j ≅ᴵ i) → Wit i 𝓖′ → (∀ {O} → 𝓖′ O → VT i O) → Wit j (VT j)
  witJ {j = zero} (inj₁ (via e ())) w H₂
  witJ {i = zero} {j = zero} (inj₂ z≅) w H₂ = H₂ w
  witJ {j = suc _} cc w H₂ = tt
  witJ {j = lim _ _} cc w H₂ = tt

  hoT : ∀ {i} {a : Ordˢ i} {O : Obs i} → a ≅ˢ a → Ωˢ i ⊑ᴱ a → VT i O → Hon i a O
  hoT {i = zero} ea fa v G = z⊑
  hoT {i = suc j} {a} ea fa v G = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (cp (proj₁ v) (via (≅ᴵ-refl (suc j)) zero) a ea (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fa) G)
  hoT {i = lim f s} {a} ea fa v G = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (cp (proj₁ v) (via (≅ᴵ-refl (lim f s)) zero) a ea (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fa) G)

  witI : ∀ j {𝓓 : Cl j} → Wit j (Inp j 𝓓)
  witI zero = refl
  witI (suc _) = tt
  witI (lim _ _) = tt

  ZT : ∀ {φ k ℓ} j {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} → j <ᴵ ℓ → Cl k → Set
  ZT {φ} zero {cv} {ev} ac 𝓖₀ = 𝓖₀ (fo φ idO Q cv ev ac)
  ZT (suc _) ac 𝓖₀ = ⊤
  ZT (lim _ _) ac 𝓖₀ = ⊤

  incE′ : ∀ {φ k ℓ} j {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {ac : j <ᴵ ℓ} (𝓖₀ : Cl k) (W : Obs k → Obs j) →
          (∀ {C C′} → 𝓖₀ C → Above j C′ (W C) → 𝓖₀ C′) → (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) → ZT j {cv = cv} {ev = ev} ac 𝓖₀ →
          ∀ {C} → (Σ _ λ D → Inp j (W ⟨ 𝓖₀ ⟩) D × (C ≡ fo φ D Q cv ev ac)) → 𝓖₀ C
  incE′ zero 𝓖₀ W St cg zv (D , refl , refl) = zv
  incE′ {φ} (suc j) {cv} {ev} {ac} 𝓖₀ W St cg zv (D , (x , C , c , o) , refl) =
    St c (above (pf , x) (λ t et → let et′ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ et ev ac ev ac (≅ᴵ-refl _) in
      fold 0 φ cv Q t ev ac , et′ , flw-fold {φ = φ} {cv = cv} {ev = ev} {p = ac} t et , run-≅ o et′))
  incE′ {φ} (lim f s) {cv} {ev} {ac} 𝓖₀ W St cg zv (D , (x , C , c , o) , refl) =
    St c (above (pf , x) (λ t et → let et′ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ et ev ac ev ac (≅ᴵ-refl _) in
      fold 0 φ cv Q t ev ac , et′ , flw-fold {φ = φ} {cv = cv} {ev = ev} {p = ac} t et , run-≅ o et′))

  mkZ : ∀ {φ k j i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {ac : j <ᴵ ℓ} {𝓖′ : Cl i} {𝓖₀ : Cl k} → (i ≺ᴵ j ⊎ j ≅ᴵ i) → Wit i 𝓖′ → (∀ {O} → 𝓖′ O → VT i O) →
        (∀ {O} → 𝓖′ O → 𝓖₀ (fo φ O Q cv ev p)) → (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) → ZT j {cv = cv} {ev = ev} ac 𝓖₀
  mkZ {j = zero} (inj₁ (via e ())) w H₂ m cg
  mkZ {φ} {j = zero} {i = zero} {cv = cv} {ev = ev} {p = p} {𝓖₀ = 𝓖₀} (inj₂ z≅) wi H₂ m cg = cg (pf , tt) (fo idO rQ) (m wi)
  mkZ {j = suc _} cc w H₂ m cg = tt
  mkZ {j = lim _ _} cc w H₂ m cg = tt

  mkHs : ∀ i {𝓐 : Cl i} {a : Ordˢ i} → (NZ i → ∀ {O} → 𝓐 O → 𝓐 (addo O a (λ q → q))) → Wit i 𝓐 → Hk i 𝓐 a (λ q → q) 𝓐
  mkHs zero s z = z
  mkHs (suc _) s z = s tt
  mkHs (lim _ _) s z = s tt


  hdnF : ∀ {φ φ₂ k k₀ i ℓ} (r : k ◃₁ k₀) {cv₂ : ∀ {L} → Ev L φ₂ → Simᴵ k L} {cv : ∀ {L} → Ev L φ → Simᴵ k₀ L} {ev : Ev ℓ (fl ⊔ φ)} {ev₂ : Ev ℓ (fl ⊔ φ₂)} {p : i <ᴵ ℓ} {𝓖 : Cl k₀} {𝓖′ : Cl i} →
         (∀ {O} → 𝓖′ O → 𝓖 (fo φ O Q cv ev p)) → (∀ {O} → 𝓖′ O → VT i O) → Hf Q φ₂ k cv₂ ev₂ p (Dn r 𝓖) 𝓖′
  hdnF {k = zero} r H H₂ = refl
  hdnF {φ = φ} {k = suc _} {i = i} r {cv = cv} {ev = ev} {p = p} H H₂ {O} c = (pf , cxT i (H₂ c)) , fo φ O Q cv ev p , H c , fo (ctx-refl O (cxT i (H₂ c))) rQ
  hdnF {φ = φ} {k = lim _ _} {i = i} r {cv = cv} {ev = ev} {p = p} H H₂ {O} c = (pf , cxT i (H₂ c)) , fo φ O Q cv ev p , H c , fo (ctx-refl O (cxT i (H₂ c))) rQ


  FF : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {𝓖 : Cl k} {𝓖′ : Cl i} {x : Ordˢ k} →
      Hf Q φ k cv ev p 𝓖 𝓖′ → (∀ {O} → 𝓖′ O → VT i O) → Wit i 𝓖′ → Good true 𝓖 x → x ≅ˢ x → Good true 𝓖′ (fold 0 φ cv Q x ev p)
  Fk : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} → NZ k → ∀ {𝓖₁ : Cl k} {𝓖₂ : Cl i} {x : Ordˢ k} →
      (∀ {O} → 𝓖₂ O → 𝓖₁ (fo φ O Q cv ev p)) → (∀ {O} → 𝓖₂ O → VT i O) → Wit i 𝓖₂ → Good true 𝓖₁ x → x ≅ˢ x → Good true 𝓖₂ (fold 0 φ cv Q x ev p)
  bsF : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {𝓖 : Cl k} {𝓖′ : Cl i} {b : Ordˢ k} → NZ k →
        (∀ {O} → 𝓖′ O → 𝓖 (fo φ O Q cv ev p)) → (∀ {O} → 𝓖′ O → VT i O) → Wit i 𝓖′ → (𝓚 : Cl k) → (∀ {C} → 𝓖 C → 𝓚 C) → b ≅ˢ b → Good true 𝓚 b →
        (∀ {O C″} → 𝓚 O → FlOver b O C″ → 𝓚 C″) → (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓚 C′ → 𝓚 C) →
        Good true 𝓖′ (fold 0 φ cv Q (Ord₊ˢ.suc b) ev p)
  passF : ∀ {φ k j i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {𝓖 : Cl k} {𝓖′ : Cl i} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (∀ {O} → 𝓖′ O → 𝓖 (fo φ O Q cv ev p)) → (∀ {O} → 𝓖′ O → VT i O) → Wit i 𝓖′ →
        ∀ {b} (e : j ≅ᴵ b) (r : b <ᴵ i) → (𝓖₀ : Cl k) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Obs k → Obs j) →
        (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ run C (f (intoˢ (<→◃ q) u))) →
        (∀ (𝓔 : Cl k) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd true j (<→◃ q) (Inp j (W ⟨ 𝓔 ⟩)) (intoˢ (<→◃ q) z) → Good true 𝓔 (f (intoˢ (<→◃ q) z))) →
        (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → (∀ {C} → 𝓖₀ C → Ab (W C)) → (∀ {C C′} → 𝓖₀ C → Above j C′ (W C) → 𝓖₀ C′) →
        (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) →
        (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
        Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
        Good true 𝓖′ (Ord₊ˢ.limᵢ r (λ y → fold 0 φ cv Q (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))) ev p))
  chF : ∀ {φ k j i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {𝓖 : Cl k} {𝓖′ : Cl i} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (∀ {O} → 𝓖′ O → 𝓖 (fo φ O Q cv ev p)) → (∀ {O} → 𝓖′ O → VT i O) → Wit i 𝓖′ →
        (i ≺ᴵ j ⊎ j ≅ᴵ i) → (𝓖₀ : Cl k) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Obs k → Obs j) →
        (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ run C (f (intoˢ (<→◃ q) u))) →
        (∀ (𝓔 : Cl k) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd true j (<→◃ q) (Inp j (W ⟨ 𝓔 ⟩)) (intoˢ (<→◃ q) z) → Good true 𝓔 (f (intoˢ (<→◃ q) z))) →
        (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) → (∀ {C} → 𝓖₀ C → Ab (W C)) → (∀ {C C′} → 𝓖₀ C → Above j C′ (W C) → 𝓖₀ C′) →
        (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) →
        (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
        Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
        Good true 𝓖′ (Ord₊ˢ.lim (λ n → fold 0 φ cv Q (f (intoˢ (<→◃ q) (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n))) ev p))

  FF {i = i} {ev = ev} {p = p} H H₂ w bz ex = Good-mono H₂ (vQ (proj₁ ev) p (wit-map i H₂ w))
  FF {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} H H₂ w (b1 lz) ex =
    bl (λ n → Good-mono H₂ (proj₁ (AddM.iterA gv ev₁ one₁ (cxT i) cgT (clT q₁ ev₁ fv one₁) (hoT ev₁ fv) (hselfT i q₁ (wit-map i H₂ w) ev₁ one₁ fv) n))) (rule4ᵒ ev₁)
    where
    gv  = vQ (proj₁ ev) p (wit-map i H₂ w)
    ev₁ = PFl.rP pf (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i)
    fv  = PFl.f0 pf (proj₁ ev) p
    q₁ : Q (proj₁ ev) p ⊑ᴱ Q (proj₁ ev) p
    q₁ = ≅→⊑ᴱ ev₁
    one₁ : 𝟏 ⊑ᴱ Q (proj₁ ev) p
    one₁ = ⊑ᴱ-trans (Ω1ᴱ i) fv
  FF {φ = φ} {cv = cv} {ev = ev} {p = p} H H₂ w (bl hg st) ex = bl (λ n → FF {φ = φ} {cv = cv} {ev = ev} {p = p} H H₂ w (hg n) (l-invˢ ex n)) (λ n → fold-cong rQ (st n))
  FF {k = suc k′} {cv = cv} {ev = ev} {p = p} H H₂ w (bu {r = zero} g) ex =
    FF {φ = flo k′} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))} {p = p} (hdnF zero {cv₂ = cvFlo k′} {cv = cv} {ev = ev} {p = p} H H₂) H₂ w g (u-reflˢ zero ex)
  FF {φ = φ} {k = lim f _} {cv = cv} {ev = ev} {p = p} H H₂ w (bu {r = self n} g) ex =
    FF {φ = flo (f n)} {cv = cvFlo (f n)} {ev = proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))} {p = p} (hdnF (self n) {cv₂ = cvFlo (f n)} {cv = cv} {ev = ev} {p = p} H H₂) H₂ w g (u-reflˢ (self n) ex)
  FF {φ = φ} {cv = cv} {ev = ev} {p = p} H H₂ w (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
    bĉ ys hy dy G₀ l₀ Gg lE (FF {φ = φ} {cv = cv} {ev = ev} {p = p} H H₂ w go (ĉ-refl₀ ex)) (λ k → FF {φ = φ} {cv = cv} {ev = ev} {p = p} H H₂ w (gO k) (ĉ-reflg ex _ _)) (fold-cong rQ mo) (λ k → fold-cong rQ (mO k))
  FF {φ = φ} {k = zero} {cv = cv} {ev = ev} {p = p} H H₂ w (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
    bĉ C.ys C.hy C.dy C.G₀ (≅-refl⁰ _) C.Gk (λ k → ≅-refl⁰ _)
       (FF {φ = φ} {cv = cv} {ev = ev} {p = p} H H₂ w g0 et)
       (λ n → FF {φ = φ} {cv = cv} {ev = ev} {p = p} (H , bp (C.P n)) H₂ w (gg _ (C.dy n) (H , bp (C.P n))) (eg _ _ _ _ (≅ᴵ-refl _)))
       (fold-cong rQ (m _ _)) (λ n → fold-cong rQ (mm _ _ _ _ (C.lmono n)))
    where module C = Ch0 𝓑 H g0 gg m mm d₀ dE ch₀ chS
  FF {k = zero} H H₂ w (bi {p = ()} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ex
  FF {φ = φ} {k = suc _} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
    bŝ (λ η O → 𝓑 η (fo φ O Q cv ev p)) Bc (FF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w g0 et)
       (λ η e w′ → FF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖 ∧ 𝓑 η} {𝓖′ = 𝓖′ ∧ (λ O → 𝓑 η (fo φ O Q cv ev p))} (λ (c , b) → H c , b) (λ c → H₂ (proj₁ c)) w′
           (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ et ev p ev p (≅ᴵ-refl _)) (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rQ (m η e)) (λ η e η′ e′ h → fold-cong rQ (mm η e η′ e′ h))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  FF {φ = φ} {k = suc _} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = passF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖 ∧ Ab} {𝓖′ = 𝓖′} (λ c → H c , lfo (H₂ c)) H₂ w e r (𝓖₀ ∧ Ab) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → loW ex (Wf c) l) (λ (c , l) A → St c A , abAbove A (loW ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , abCg o l) hm ex
  ... | injᵇ c = chF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖 ∧ Ab} {𝓖′ = 𝓖′} (λ c′ → H c′ , lfo (H₂ c′)) H₂ w (inj₁ c) (𝓖₀ ∧ Ab) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → loW ex (Wf c) l) (λ (c , l) A → St c A , abAbove A (loW ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , abCg o l) hm ex
  ... | injᶜ c = chF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖 ∧ Ab} {𝓖′ = 𝓖′} (λ c′ → H c′ , lfo (H₂ c′)) H₂ w (inj₂ c) (𝓖₀ ∧ Ab) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → loW ex (Wf c) l) (λ (c , l) A → St c A , abAbove A (loW ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , abCg o l) hm ex
  FF {φ = φ} {k = lim _ _} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
    bŝ (λ η O → 𝓑 η (fo φ O Q cv ev p)) Bc (FF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w g0 et)
       (λ η e w′ → FF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖 ∧ 𝓑 η} {𝓖′ = 𝓖′ ∧ (λ O → 𝓑 η (fo φ O Q cv ev p))} (λ (c , b) → H c , b) (λ c → H₂ (proj₁ c)) w′
           (gg η e tt) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ et ev p ev p (≅ᴵ-refl _)) (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rQ (m η e)) (λ η e η′ e′ h → fold-cong rQ (mm η e η′ e′ h))
       (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
  FF {φ = φ} {k = lim _ _} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} H H₂ w (bi {j = j} {p = q} {f = f} 𝓖₀ inc₀ W Wf hb Wv St cg hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = passF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖 ∧ Ab} {𝓖′ = 𝓖′} (λ c → H c , lfo (H₂ c)) H₂ w e r (𝓖₀ ∧ Ab) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → loW ex (Wf c) l) (λ (c , l) A → St c A , abAbove A (loW ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , abCg o l) hm ex
  ... | injᵇ c = chF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖 ∧ Ab} {𝓖′ = 𝓖′} (λ c′ → H c′ , lfo (H₂ c′)) H₂ w (inj₁ c) (𝓖₀ ∧ Ab) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → loW ex (Wf c) l) (λ (c , l) A → St c A , abAbove A (loW ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , abCg o l) hm ex
  ... | injᶜ c = chF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖 ∧ Ab} {𝓖′ = 𝓖′} (λ c′ → H c′ , lfo (H₂ c′)) H₂ w (inj₂ c) (𝓖₀ ∧ Ab) (λ (c , l) → inc₀ c , l) W (λ (c , l) → Wf c) (λ 𝓔 inc″ → hb 𝓔 (λ c′ → proj₁ (inc″ c′))) (λ (c , l) → Wv c) (λ (c , l) → loW ex (Wf c) l) (λ (c , l) A → St c A , abAbove A (loW ex (Wf c) l)) (λ c₀ o (c , l) → cg c₀ o c , abCg o l) hm ex
  FF {φ = φ} {k = zero} {i = i} {cv = cv} {ev = ev} {p = p} H H₂ w (bs {a = b} 𝓚 v eb g clk cgk ho) ex =
    bl (λ n → Good-mono H₂ (proj₁ (AddM.iterA gw ew oa (cxT i) cgT (clT qw ew fw oa) (hoT ew fw) (hselfT i qw (wit-map i H₂ w) ew oa fw) n))) (rule4ᵒ ew)
    where
    gw = FF {φ = φ} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓚} {𝓖′ = VT i} (v H) (λ t → t) (wit-map i H₂ w) g eb
    ew = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ eb ev p ev p (≅ᴵ-refl i)
    fw = flw-fold {φ = φ} {cv = cv} {ev = ev} {p = p} b eb
    qw : Q (proj₁ ev) p ⊑ᴱ fold 0 φ cv Q b ev p
    qw = B1ᴱ {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} {x = Q (proj₁ ev) p} rQ (≅→⊑ᴱ (rQ (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i))) b eb
    oa : 𝟏 ⊑ᴱ fold 0 φ cv Q b ev p
    oa = one-fold {φ = φ} {cv = cv} {ev = ev} {p = p} b eb
  FF {φ = φ} {k = suc _} {cv = cv} {ev = ev} {p = p} H H₂ w (bs 𝓚 v eb g clk cgk ho) ex = bsF {φ = φ} {cv = cv} {ev = ev} {p = p} tt H H₂ w 𝓚 v eb g (clk tt) (cgk tt)
  FF {φ = φ} {k = lim _ _} {cv = cv} {ev = ev} {p = p} H H₂ w (bs 𝓚 v eb g clk cgk ho) ex = bsF {φ = φ} {cv = cv} {ev = ev} {p = p} tt H H₂ w 𝓚 v eb g (clk tt) (cgk tt)

  passF {φ} {k = k} {j = j} {i = i} {cv = cv} {ev = ev} {p = p} {𝓖 = 𝓖} {𝓖′ = 𝓖′} {q = q} {f = f} H H₂ wi {b} e r 𝓖₀ inc₀ W Wf hb Wv lW St cg hm ex =
    bi (λ O → 𝓖₀ (fo φ O Q cv ev p) × VT i O) (λ c → inc₀ (H c) , H₂ c) (λ O → tr⁻o (W (fo φ O Q cv ev p)) e)
       (λ {O} (c , v) u eu → subst (λ y → run (W (fo φ O Q cv ev p)) (tr⁻ˢ e u) ≅ˢ run O (fold 0 φ cv Q (f (intoˢ (<→◃ q) (tr⁻ˢ e y))) ev p)) (sym (out-intoˢ (<→◃ r) u))
           (Wf c (tr⁻ˢ e u) (self-tr⁻ˢ e eu)))
       (λ 𝓔′ inc″ z ez g → subst (λ y → Good true 𝓔′ (fold 0 φ cv Q (f (intoˢ (<→◃ q) (tr⁻ˢ e y))) ev p)) (sym (out-intoˢ (<→◃ r) z))
           (Fb (λ c → _ , c , refl) (λ c → proj₂ (inc″ c)) (wit-nz i (NZ-of r))
              (hb (λ C → Σ _ λ O → 𝓔′ O × (C ≡ fo φ O Q cv ev p)) (λ { (O , c , refl) → proj₁ (inc″ c) }) (tr⁻ˢ e z) (self-tr⁻ˢ e ez)
                  (Good→Gd (<→◃ q) (Bb e (W ⟨ (λ C → Σ _ λ O → 𝓔′ O × (C ≡ fo φ O Q cv ev p)) ⟩) ((λ O → tr⁻o (W (fo φ O Q cv ev p)) e) ⟨ 𝓔′ ⟩)
                      (λ { (x , _ , (O , c , refl) , o) → x , x , O , c , tr⁻o o }) ez (Gd→Good (<→◃ r) g))))
              (i-respˢ ex (self-tr⁻ˢ e ez))))
       (λ {O} (c , v) → vis (cx (Wv c))
           (λ nz s es os G → tw (Wv c) (NZ-e e nz) (tr⁻ˢ e s) (self-tr⁻ˢ e es) (fl-tr⁻ e (s≅ z≅ z≅) os) G)
           (λ {b′} h t et fl G →
           cp (Wv c) (≺ᴵ-respʳ h (s≅ (≅ᴵ-sym e))) (tr⁻ˢ e t) (self-tr⁻ˢ e et) (λ ex₀ h₀ → fl-tr⁻ e ex₀ (fl ex₀ h₀)) G))
       (λ {O} {C″} (c , v) (above cx′ wrap) →
          St c (above (pf , cx′) (λ t et →
            let t′ = fold 0 φ cv Q t ev p
                et′ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ et ev p ev p (≅ᴵ-refl i)
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
              in ≺-≅tw (≅ˢ-trans d d₂) (tw (toV (NZ-of r) v) (NZ-of r) _ (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ ey ev p ev p (≅ᴵ-refl i)) (one-fold {φ = φ} {cv = cv} {ev = ev} {p = p} _ ey)) G)
            (λ {b′} h t et fl G →
            let u = proj₁ (wrap t et)
                eu = proj₁ (proj₂ (wrap t et))
                d = proj₂ (proj₂ (proj₂ (wrap t et)))
                d₂ = Wf c (tr⁻ˢ e u) (self-tr⁻ˢ e eu)
                ey = i-respˢ ex (self-tr⁻ˢ e eu)
            in pull (≅ˢ-trans d d₂)
                    (cp (toV (NZ-of r) v) h _ (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ ey ev p ev p (≅ᴵ-refl i))
                        (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ h) (flw-fold {φ = φ} {cv = cv} {ev = ev} {p = p} _ ey))) G))
            (ab→𝓟 cx′ (abAbove (above cx′ wrap) (abTr⁻ {e = e} (lW c)))))
       (λ c₀ o (c , v) → cg (pf , c₀) (fo o rQ) c , cgT c₀ o v)
       (λ {z} {z′} h₀ → subst₂ (λ y y′ → fold 0 φ cv Q (f (intoˢ (<→◃ q) (tr⁻ˢ e y))) ev p ⊑ᵒ fold 0 φ cv Q (f (intoˢ (<→◃ q) (tr⁻ˢ e y′))) ev p)
            (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong rQ (hm (tr⁻-cong h₀))))
    where
    Fb : ∀ {𝓖₁ : Cl k} {𝓖₂ : Cl i} {x} → (∀ {O} → 𝓖₂ O → 𝓖₁ (fo φ O Q cv ev p)) → (∀ {O} → 𝓖₂ O → VT i O) → Wit i 𝓖₂ → Good true 𝓖₁ x → x ≅ˢ x → Good true 𝓖₂ (fold 0 φ cv Q x ev p)
    Fb = Fk {φ = φ} {cv = cv} {ev = ev} {p = p} (NZ-of q)

  chF {φ} {k} {j} {i} {ℓ} {cv} {ev} {p} {𝓖} {𝓖′} {q} {f} H H₂ wi cc 𝓖₀ inc₀ W Wf hb Wv lW St cg hm ex =
    bl (λ n → Fb H H₂ wi
          (hb 𝓖 inc₀ (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n) (csim n)
              (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , C , c , o) → x , C , inc₀ c , o })) (chG n))))
          (i-respˢ ex (csim n)))
       (λ n → fold-cong rQ (hm (chain-st {φ = φ} {cv = cv} {ev = ev} ex hm n)))
    where
    Fb : ∀ {i′} {p′ : i′ <ᴵ ℓ} {𝓖₁ : Cl k} {𝓖₂ : Cl i′} {x} → (∀ {O} → 𝓖₂ O → 𝓖₁ (fo φ O Q cv ev p′)) → (∀ {O} → 𝓖₂ O → VT i′ O) → Wit i′ 𝓖₂ → Good true 𝓖₁ x → x ≅ˢ x → Good true 𝓖₂ (fold 0 φ cv Q x ev p′)
    Fb {p′ = p′} = Fk {φ = φ} {cv = cv} {ev = ev} {p = p′} (NZ-of q)
    ac : j <ᴵ ℓ
    ac = cv (proj₂ ev) q
    csim : ∀ n → (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n) ≅ˢ (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n)
    csim = chain-≅ {φ = φ} {cv = cv} {ev = ev} ex
    𝓔₂ : Cl k
    𝓔₂ C′ = Σ _ λ D → Inp j (W ⟨ 𝓖₀ ⟩) D × (C′ ≡ fo φ D Q cv ev ac)
    chG : ∀ n → Good true (Inp j (W ⟨ 𝓖₀ ⟩)) (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n)
    chG zero = Good-mono (inpVis j W Wv) (Ωg j)
    chG (suc n) = Fb (λ d → _ , d , refl) (visD j W Wv lW (witJ cc wi H₂)) (witI j {W ⟨ 𝓖₀ ⟩})
          (hb 𝓔₂ (incE) (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv Q (f (intoˢ (<→◃ q) x))) ev n) (csim n)
              (Good→Gd (<→◃ q) (Good-mono (inp-map j (λ { (x , C , e′ , o) → x , C , incE e′ , o })) (chG n))))
          (i-respˢ ex (csim n))
      where
      incE : ∀ {C} → 𝓔₂ C → 𝓖₀ C
      incE = incE′ {φ = φ} j {cv = cv} {ev = ev} {ac = ac} 𝓖₀ W St cg (mkZ cc wi H₂ (λ c → inc₀ (H c)) cg)

  Fk {φ = φ} {k = suc _} {cv = cv} {ev = ev} {p = p} nk H H₂ w g ex = FF {φ = φ} {cv = cv} {ev = ev} {p = p} H H₂ w g ex
  Fk {φ = φ} {k = lim _ _} {cv = cv} {ev = ev} {p = p} nk H H₂ w g ex = FF {φ = φ} {cv = cv} {ev = ev} {p = p} H H₂ w g ex

  bsF {φ} {suc k′} {i} {ℓ} {cv} {ev} {p} {𝓖} {𝓖′} {b} nk H H₂ wi 𝓚 v₁ eb g clk cgk = 
    bl (λ n → Good-mono (λ c → v₁ (H c) , H₂ c) (proj₁ (AddM.iterA gw ew oa cxh cgh clh (λ h → hoT ew fw (proj₂ h)) (mkHs i {𝓐 = ℋ} (λ nz h → clh nz h (fla h)) (wit-map i (λ c → v₁ (H c) , H₂ c) wi)) n))) (rule4ᵒ ew)
    where
    C₁ : ∀ O → Obs _
    C₁ O = fo φ O Q cv ev p
    ℋ : Cl i
    ℋ O = 𝓚 (C₁ O) × VT i O
    wv : Ordˢ i
    wv = fold 0 φ cv Q b ev p
    ew : wv ≅ˢ wv
    ew = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ eb ev p ev p (≅ᴵ-refl i)
    fw : Ωˢ i ⊑ᴱ wv
    fw = flw-fold {φ = φ} {cv = cv} {ev = ev} {p = p} b eb
    qw : Q (proj₁ ev) p ⊑ᴱ fold 0 φ cv Q b ev p
    qw = B1ᴱ {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} {x = Q (proj₁ ev) p} rQ (≅→⊑ᴱ (rQ (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i))) b eb
    oa : 𝟏 ⊑ᴱ wv
    oa = one-fold {φ = φ} {cv = cv} {ev = ev} {p = p} b eb
    gw : Good true ℋ wv
    gw = Fk {φ = φ} {cv = cv} {ev = ev} {p = p} nk {𝓖₁ = 𝓚} {𝓖₂ = ℋ} proj₁ proj₂ (wit-map i (λ c → v₁ (H c) , H₂ c) wi) g eb
    cxh : ∀ {O} → ℋ O → Ctx O
    cxh (c , t) = cxT i t
    cgh : ∀ {C C′} → Ctx C → C ≈ᵒ C′ → ℋ C′ → ℋ C
    cgh c₀′ o (c , t) = cgk (pf , c₀′) (fo o rQ) c , cgT c₀′ o t
    clh : NZ i → ∀ {O C″} → ℋ O → FlOver wv O C″ → ℋ C″
    clh nzi (c , t) f′ = clk c (flo-over (pf , cxo f′) (λ u eu G → flw f′ (fold 0 φ cv Q u ev p)
        (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ eu ev p ev p (≅ᴵ-refl i)) G)) , clT qw ew fw oa nzi t f′
    fla : ∀ {O} → ℋ O → FlOver wv O (addo O wv (λ q → q))
    fla {O} h = flo-over (afl ew oa , cxh h) (λ t et G → add-rᴱ {a = wv} {a′ = wv} {σ = λ q → q} t ew et (ctx-refl O (cxh h)) G)

  bsF {φ} {lim f₀ s₀} {i} {ℓ} {cv} {ev} {p} {𝓖} {𝓖′} {b} nk H H₂ wi 𝓚 v₁ eb g clk cgk = 
    bl (λ n → Good-mono (λ c → v₁ (H c) , H₂ c) (proj₁ (AddM.iterA gw ew oa cxh cgh clh (λ h → hoT ew fw (proj₂ h)) (mkHs i {𝓐 = ℋ} (λ nz h → clh nz h (fla h)) (wit-map i (λ c → v₁ (H c) , H₂ c) wi)) n))) (rule4ᵒ ew)
    where
    C₁ : ∀ O → Obs _
    C₁ O = fo φ O Q cv ev p
    ℋ : Cl i
    ℋ O = 𝓚 (C₁ O) × VT i O
    wv : Ordˢ i
    wv = fold 0 φ cv Q b ev p
    ew : wv ≅ˢ wv
    ew = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ eb ev p ev p (≅ᴵ-refl i)
    fw : Ωˢ i ⊑ᴱ wv
    fw = flw-fold {φ = φ} {cv = cv} {ev = ev} {p = p} b eb
    qw : Q (proj₁ ev) p ⊑ᴱ fold 0 φ cv Q b ev p
    qw = B1ᴱ {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} {x = Q (proj₁ ev) p} rQ (≅→⊑ᴱ (rQ (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i))) b eb
    oa : 𝟏 ⊑ᴱ wv
    oa = one-fold {φ = φ} {cv = cv} {ev = ev} {p = p} b eb
    gw : Good true ℋ wv
    gw = Fk {φ = φ} {cv = cv} {ev = ev} {p = p} nk {𝓖₁ = 𝓚} {𝓖₂ = ℋ} proj₁ proj₂ (wit-map i (λ c → v₁ (H c) , H₂ c) wi) g eb
    cxh : ∀ {O} → ℋ O → Ctx O
    cxh (c , t) = cxT i t
    cgh : ∀ {C C′} → Ctx C → C ≈ᵒ C′ → ℋ C′ → ℋ C
    cgh c₀′ o (c , t) = cgk (pf , c₀′) (fo o rQ) c , cgT c₀′ o t
    clh : NZ i → ∀ {O C″} → ℋ O → FlOver wv O C″ → ℋ C″
    clh nzi (c , t) f′ = clk c (flo-over (pf , cxo f′) (λ u eu G → flw f′ (fold 0 φ cv Q u ev p)
        (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = Q} {P′ = Q} rQ eu ev p ev p (≅ᴵ-refl i)) G)) , clT qw ew fw oa nzi t f′
    fla : ∀ {O} → ℋ O → FlOver wv O (addo O wv (λ q → q))
    fla {O} h = flo-over (afl ew oa , cxh h) (λ t et G → add-rᴱ {a = wv} {a′ = wv} {σ = λ q → q} t ew et (ctx-refl O (cxh h)) G)

```
