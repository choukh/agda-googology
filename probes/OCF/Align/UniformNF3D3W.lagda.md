# 一切深度 (四): 世界

> 接 [UniformNF3D3G](UniformNF3D3G.lagda.md), [UniformNF3D3F](UniformNF3D3F.lagda.md). 结论先说:
>
> 1. **`Base`: 一个点的类族 $\mathcal P$ 与地板集 $\mathcal F$, 带封闭性 `cl`: "压在 $a\in\mathcal F$ 之上" 不出 $\mathcal P$.** 地板集的作用: 帧副本 $F_b\,P$ 上的类族 "$\mathcal P\wedge$ `fo1 O X (P,s) ∈ 𝓚`" 只对 $a\sqsupseteq F_b\,P\,s$ 封闭, 不对 $a\sqsupseteq$ 底封闭. 所以闭包的门槛必须是点的一部分.
> 2. **`WSp d`: 带世界的脊.** 脊的每一格带一个帧 $P$, 它的世界 $w$, 与 "$P$ 在 $w$ 上好" 的证明 `RF`. **`SG`: 脊在一个点上好**, 每一格有自己的上方点 $b'$, $\mathcal P\subseteq\mathcal P'$, $b'\in w$. 世界与 `SG` 都在 `Set₁`, 带世界的脊在 `Set₂`, **宇宙不随深度增长**.
> 3. **`RF d w X`: 帧在世界上好.** 五条: 地板 `fX`, 值 `vX`, 需求 `dT`, 地板集 `flX`, Kripke 单调 `upX`. `Rais`: 抬高一个点: 类族变小, 新脊的头值压在 $X\,s$ 之上, 且在新地板集里. 这就是带标签路线 `Wd` 的 $\forall c'\succeq c$ 的树侧形式: 那里的世界是目标层, 这里的世界是点.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3W where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Level using (Lift; lift)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Uˢ; Ordˢ; intoˢ; toZ; Ωˢ; tr⁻ˢ)
open import OCF.Align.UniformNF3Eq using (_≅ˢ_; ≅ᶻ-sym; toZ-≅; self-tr⁻ˢ; i-respˢ; z≅; ≅ˢ-sym; ≅ˢ-trans)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; Run; InF; Dem)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3D3O using (Fr; Sp; sf; Obs; idO; fo1; tr⁻o; run; _≈ᵒ_; run-≅; ≈ᵒ-reflˡ)
open import OCF.Align.UniformNF3D3N using (Goodᴺ-tr)
open import OCF.Align.UniformNF3D3G using (_⊑ᴱ_; Ctx; ctx-refl; FlU; SF; 𝟏; ⊑ᴱ-trans; ≅→⊑ᴱ)
open import OCF.Align.UniformNF3D3C
open import OCF.Align.UniformNF3D3CF
open import OCF.Align.UniformNF3D3F using (FL; Pd; VF)
open import OCF.Align.UniformNF3D3S using (PCg; cxV)
```

## §1 点、脊与好

```agda
FlP : Set₁
FlP = ∀ {i} → Ordˢ i → Set

record Base : Set₁ where
  constructor base
  field
    𝓟b  : Pd
    pCb : PCg 𝓟b
    𝓕b  : FlP
    uF  : ∀ {i} {a a′ : Ordˢ i} → 𝓕b a → a ⊑ᴱ a′ → 𝓕b a′
    cl  : ∀ {i j} {a : Ordˢ i} {O : Obs i} {C″ : Obs j} → 𝓕b a → Ctx O → 𝓟b O → Ctx C″ → FL a O C″ → 𝓟b C″
open Base public

_⊂ᵇ_ : Base → Base → Set
b ⊂ᵇ b′ = ∀ {j} {O : Obs j} → 𝓟b b O → 𝓟b b′ O

record RFP {d φ} (WS : Set₂) (er : WS → Sp d) (Sg : Base → WS → Set₁) (Rs : Base → WS → Base → WS → Set) (w : Base → WS → Set₁) (X : Fr d φ) : Set₂ where
  constructor rfp
  field
    fX  : FlU d X
    vX  : ∀ b (s : WS) → Sg b s → w b s → ∀ {i ℓ} (ev : Ev ℓ (sf (er s) ⊔ φ)) (p : i <ᴵ ℓ) → Wit i (VF (𝓟b b) i) → Good true (VF (𝓟b b) i) (X (er s) ev p)
    dT  : ∀ b (s : WS) → Sg b s → w b s → ∀ {i ℓ} {O : Obs i} → Ctx O → 𝓟b b O → (ev : Ev ℓ (sf (er s) ⊔ φ)) (p : i <ᴵ ℓ) (G : Goodᴺ (toZ (run O (X (er s) ev p)))) → ∀ {K} (q : InF K (sf (er s) ⊔ φ)) → Dem (lvG G) q
    flX : ∀ b (s : WS) → Sg b s → w b s → ∀ {i ℓ} (ev : Ev ℓ (sf (er s) ⊔ φ)) (p : i <ᴵ ℓ) → 𝓕b b (X (er s) ev p)
    upX : ∀ b (s : WS) b′ (s′ : WS) → Sg b s → w b s → Sg b′ s′ → Rs b s b′ s′ → w b′ s′
open RFP public

mutual
  WSp : ℕ → Set₂
  WSp zero    = Lift _ ⊤
  WSp (suc d) = Σ Flr λ fl → Σ (Fr d fl) λ P → Σ (Base → WSp d → Set₁) λ w → RF d w P × WSp d

  er : ∀ {d : ℕ} → WSp d → Sp d
  er {d = zero}  _ = tt
  er {d = suc d} (fl , P , w , r , s) = fl , P , er s

  SG : ∀ {d : ℕ} → Base → WSp d → Set₁
  SG {d = zero}  b s = Lift _ ⊤
  SG {d = suc d} b (fl , P , w , r , s) = Σ Base λ b′ → (b ⊂ᵇ b′) × (w b′ s × SG b′ s)

  Rais : ∀ (d : ℕ) {φ} → Fr d φ → Base → WSp d → Base → WSp d → Set
  Rais zero X b s b′ s′ = ⊥
  Rais (suc d) {φ} X b s b′ (fl′ , P′ , w′ , r′ , t′) =
    (b′ ⊂ᵇ b) ×
    ((∀ {i ℓ} (ev′ : Ev ℓ (sf (er t′) ⊔ fl′)) (p : i <ᴵ ℓ) → Σ (Ev ℓ (sf (er s) ⊔ φ)) λ ev → X (er s) ev p ⊑ᴱ P′ (er t′) ev′ p) ×
     (∀ {i ℓ} (ev′ : Ev ℓ (sf (er t′) ⊔ fl′)) (p : i <ᴵ ℓ) → 𝓕b b′ (P′ (er t′) ev′ p)))

  RF : ∀ (d : ℕ) {φ} → (Base → WSp d → Set₁) → Fr d φ → Set₂
  RF d w X = RFP (WSp d) (er {d}) (SG {d}) (Rais d X) w X

Wld : ℕ → Set₂
Wld d = Base → WSp d → Set₁

sfW : ∀ {d : ℕ} (s : WSp d) → SF (er s)
sfW {d = zero}  _ = tt
sfW {d = suc d} (fl , P , w , r , s) = fX r , sfW s

SG-anti : ∀ {d : ℕ} {b b₁ : Base} (s : WSp d) → b₁ ⊂ᵇ b → SG b s → SG b₁ s
SG-anti {d = zero}  s h g = g
SG-anti {d = suc d} (fl , P , w , r , s) h (b′ , i , x , y) = b′ , (λ c → i (h c)) , x , y
```

## §2 类的引理

与 [UniformNF3D2F](UniformNF3D2F.lagda.md) `FoldQ` 同文, 只把吸收者的门槛从 "$a=Q\,ev\,p$" 换成 "$a\in\mathcal F$".

```agda
module Cls (b : Base) where
  𝓟 = 𝓟b b
  pCg = pCb b
  𝓕 = 𝓕b b
  cl′ = cl b

  VT : ∀ i → Cl i
  VT = VF 𝓟

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
  Ab C = Σ Ordᴵ λ i → Σ (Obs i) λ O → Σ (Ordˢ i) λ a → 𝓕 a × Ctx O × 𝓟 O × FL a O C

  abSem : ∀ {k k′} {A′ : Obs k} {B : Obs k′} → (∀ t → t ≅ˢ t → Σ (Ordˢ k′) λ u → (u ≅ˢ u) × (run A′ t ≅ˢ run B u)) → Ab B → Ab A′
  abSem h (i , O , a , ia , c , π , fl′) = i , O , a , ia , c , π , λ t et G →
    let d = toZ-≅ (proj₂ (proj₂ (h t et)))
        G′ = Goodᴺ-tr d G
        R = fl′ (proj₁ (h t et)) (proj₁ (proj₂ (h t et))) G′
    in proj₁ R , ⊑-trans (proj₂ R) (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym d) G′ G))

  abCg : ∀ {k} {C C′ : Obs k} → C ≈ᵒ C′ → Ab C′ → Ab C
  abCg o = abSem (λ s es → s , es , run-≅ o es)

  abAbove : ∀ {j ℓ} {C′ : Obs ℓ} {D′ : Obs j} → Above j C′ D′ → Ab D′ → Ab C′
  abAbove (above _ wrap) = abSem (λ t et → proj₁ (wrap t et) , proj₁ (proj₂ (wrap t et)) , proj₂ (proj₂ (proj₂ (wrap t et))))

  abTr⁻ : ∀ {a b} {X : Obs a} {e : a ≅ᴵ b} → Ab X → Ab (tr⁻o X e)
  abTr⁻ {e = e} (i , O , a , ia , c , π , fl′) = i , O , a , ia , c , π , λ s es G → fl′ (tr⁻ˢ e s) (self-tr⁻ˢ e es) G

  ab→𝓟 : ∀ {k} {C : Obs k} → Ctx C → Ab C → 𝓟 C
  ab→𝓟 x (i , O , a , ia , c , π , fl′) = cl′ ia c π x fl′

  cgT : ∀ {i} {C C′ : Obs i} → Ctx C → C ≈ᵒ C′ → VT i C′ → VT i C
  cgT {i = zero} c₀ o (refl , t) = ≈-id o , pCg c₀ o t
  cgT {i = suc _} c₀ o v = Vis-≈ c₀ o (proj₁ v) , pCg c₀ o (proj₂ v)
  cgT {i = lim _ _} c₀ o v = Vis-≈ c₀ o (proj₁ v) , pCg c₀ o (proj₂ v)

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
```
