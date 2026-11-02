# Uniform3 上的无符号闭包定理 (七): 塔

> [UniformPendingGoodTower](UniformPendingGoodTower.lagda.md) 的移植. 结论先说:
>
> 1. **`Gᴺk`, `Gᴺω`, `G₃` 在修正的折叠上成立.** 证书的构造不读记号; 验收在 [UniformNF3TowerAccept](UniformNF3TowerAccept.lagda.md).
> 2. **`MxZ` 没有了.** `Step` 的输入换成 `DmQ`: 折叠的层号支配前缀的地板. `bd⊑` 由 `ubd` 的泛性质得到 $\mathrm{Bd}\sqsubseteq$ 层号, 不再 `subst` 字面的最大者. 塔上 `DmZ` 平凡 (地板项都 $\cong0$).
> 3. `one⊑η`、`nzη` 改读 `evF`/`FM`. 其余逐字. 非平凡的 `DmQ` 在 [UniformNF3FloorS](UniformNF3FloorS.lagda.md).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3Tower where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ; _+ˢ_; z<suc)
open import OCF.Align.UniformS using (⊑ᴵ-≅ʳ; ⊑ᴵ-≅ˡ; ≅ᴵ→⊑ᴵ; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; toZ-≅; Ωˢ-≅; Ωˢ-refl; addˢ-≅; self-trˢ; self-tr⁻ˢ)
open import OCF.Align.Stage2Label using (one⁰; two⁰; two⊑)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; liftEv; Run; Top; bound; Bd; ubd; Fc; evF; iF; FM; FB; Dem; dem; fold; Ω̂A; ∅ᴿ; _≈ᴿ_; fold-≅0; ≺0)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3Base using (Obs; idO; fo; addo; tro; tr⁻o; run; _≈ᵒ_; run-≅; r∅; rΩ̂)
open import OCF.Align.UniformNF3NBase using (_⊑ᵒ_; fold-cong; Ω-monoᵒ)
open import OCF.Align.UniformNF3NGrow using (_⊑ᴱ_; Ctx; ctx-refl; PFl; pfl∅; pfl-Ω̂; AFl; afl; 𝟏; ⊑ᴱ-trans; ≅→⊑ᴱ; B1ᴱ; Ω1ᴱ; Ω<ᴱ; Ω-strict; fold-congᴱ; ŝ-rᴱ; add-floorᴱ)
open import OCF.Align.UniformNF3Class
open import OCF.Align.UniformNF3ClassF using (NZ-of)
open import OCF.Align.UniformNF3ClassF2

Ωvia : ∀ {a b} → a ≺ᴵ b → Ωˢ a ⊑ᴱ Ωˢ b
Ωvia (via e q) = Ωlt e q

≺ᴵ-up : ∀ {b A B} → b ≺ᴵ A → A ⊑ᴵ B → b ≺ᴵ B
≺ᴵ-up (via e q) h = ≺ᴵ-respˡ e (sim h q)

oneH : (H : Goodᴺ (Z.suc Z.zero)) {X : Ordᶜ zero} → forceᴺ _ H ⊑⁰ X → suc zero ⊑⁰ X
oneH (gs gz) h = h

read1 : ∀ {k} (O : Obs k) → Ctx O → (t : Ordˢ k) → t ≅ˢ t → (∀ {K} → 𝟏 {K} ⊑ᴱ t) → (G : Goodᴺ (toZ (run O t))) → suc zero ⊑ᴵ lvG G
read1 idO c t et one G = toLevel-⊑ (hs hz) (forceᴺ-HS _ G) (oneH (proj₁ (one idO G)) (proj₂ (one idO G)))
read1 (fo φ O P cv ev p) (pf , c) t et one G = read1 O c _ (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} (PFl.rP pf) et ev p ev p (≅ᴵ-refl _))
  (λ {K} → B1ᴱ {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} {x = 𝟏 {K}} (PFl.rP pf) (⊑ᴱ-trans (Ω1ᴱ _) (PFl.f0 pf (proj₁ ev) p)) t et) G
read1 (addo O a σ) (afl e₁ one₁ , c) t et one G = read1 O c _ (addˢ-≅ refl e₁ et) (λ {K} → add-floorᴱ {σ = σ} t one₁ et) G
read1 (tro O e) c t et one G = read1 O c _ (self-trˢ e et) (λ {K} → fl-tr e (s≅ z≅) one) G
read1 (tr⁻o O e) c t et one G = read1 O c _ (self-tr⁻ˢ e et) (λ {K} → fl-tr⁻ e (s≅ z≅) one) G

≺→⊑ : ∀ {a b} → a ≺ᴵ b → a ⊑ᴵ b
≺→⊑ h = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (s⊑′ h)

zlt : ∀ {b} → suc zero ⊑ᴵ b → zero <ᴵ b
zlt (s⊑ z≅ q) = q

trans< : ∀ {x a b} → x <ᴵ a → a <ᴵ b → x <ᴵ b
trans< x zero      = suc x
trans< x (suc q)   = suc (trans< x q)
trans< x (lim n q) = lim n (trans< x q)

τ : ∀ {a b} → a <ᴵ b → Simᴵ (suc a) b
τ q zero    = q
τ q (suc x) = trans< x q

one⊑ : ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → NZ i → suc zero ⊑ᴵ i
one⊑ z p nz with <ᴵ-dec z p
... | injᵃ r          = s⊑′ r
... | injᵇ (via e ())
... | injᶜ z≅         = ⊥-elim nz

NZ-≅₁ : ∀ {i j} → NZ i → i ≅ᴵ j → NZ j
NZ-≅₁ nz (s≅ _) = tt
NZ-≅₁ nz (l≅ _) = tt
NZ-≅₁ () z≅

T2 : ∀ {fl} → Run fl → Set
T2 {fl} Q = ∀ {φ k ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {z : zero <ᴵ ℓ} {y : Ordˢ k} →
            y ≅ˢ y → (∀ {K} → 𝟏 {K} ⊑ᴱ y) → (G : Goodᴺ (toZ (fold 0 φ cv Q y ev z))) → one⁰ ≺ forceᴺ _ G

h2N : (G : Goodᴺ (Z.suc (Z.suc Z.zero))) → one⁰ ≺ forceᴺ _ G
h2N (gs (gs gz)) = ≺z (s≅ z≅)

t2∅ : T2 ∅ᴿ
t2∅ {φ = φ} {k = k} {cv = cv} {ev = ev} {z = z} {y = y} ey oy G = proj₂ L (w (proj₁ L))
  where
  L = fold-congᴱ {φ = φ} {φ′ = φ} {P = ∅ᴿ} {cv = cv} {cv′ = cv} {ev = ev} {ev′ = ev} {p = z} {p′ = z} {x = 𝟏 {k}} {y = y} r∅ oy idO G
  w : (H : Goodᴺ (toZ (fold 0 φ cv ∅ᴿ (𝟏 {k}) ev z))) → one⁰ ≺ forceᴺ _ H
  w (gl Gs st) = ≺l 2 (h2N (Gs 2))

t2-Ω̂ : ∀ {fl} {Q : Run fl} → PFl Q → T2 Q → T2 (Ω̂A 0 Q)
t2-Ω̂ {fl} {Q} pf t2Q {φ = φ} {cv = cv} {ev = ev} {z = z} {y = y} ey oy G = proj₂ L (t2Q {φ = fk zero} {cv = λ e → e} {ev = proj₁ ev} {z = z} (Ωˢ-refl (suc zero)) (Ω1ᴱ (suc zero)) (proj₁ L))
  where
  rQ = PFl.rP pf
  t₀ = fold 0 (fk zero) (λ e → e) Q (Ωˢ (suc zero)) (proj₁ ev) z
  et : t₀ ≅ˢ t₀
  et = fold-≅0 {φ = fk zero} {φ′ = fk zero} {cv = λ e → e} {cv′ = λ e → e} {P = Q} {P′ = Q} rQ (Ωˢ-refl (suc zero)) (proj₁ ev) z (proj₁ ev) z (≅ᴵ-refl zero)
  L = B1ᴱ {φ = φ} {P = Ω̂A 0 Q} {cv = cv} {ev = ev} {p = z} {x = t₀} (rΩ̂ rQ) (ŝ-rᴱ (≅→⊑ᴱ et)) y ey idO G
```

## §1 守卫

`CQ O b`: 在 $O$ 下, 任何以 $Q$ 为前缀、目标 $i$ 的折叠 (任意地板与环境), 尾巴地板 $\sqsupseteq\Omega_b$, 层号 $\sqsupseteq b+1$. `Br η O`: 分支 $\eta$ 可读: 一切 $b\prec\eta$ 有 `CQ`, 且 $\eta$ 是上一个链点的层号 (`G₋`, `eη`) 并严格高于上上个 (`h₋`). 这就是 Pending 的 `Link`, 但相对上下文 $O$, 并且是闭包自己的链.

```agda
CQ : ∀ {fl} (Q : Run fl) {i} → Obs i → Ordᴵ → Set
CQ {fl} Q {i} O b = ∀ {k′ φ′} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ℓ′} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t → FlΩ b t →
                   (G : Goodᴺ (toZ (run O (fold 0 φ′ cv′ Q t ev′ p′)))) → suc b ⊑ᴵ lvG G

record Br {fl} (Q : Run fl) {i} (η : Ordᴵ) (O : Obs i) : Set where
  constructor br-mk
  field
    br  : ∀ {b} → b ≺ᴵ η → CQ Q O b
    η₋  : Ordᴵ
    φ₋  : Flr
    cv₋ : ∀ {L} → Ev L φ₋ → Simᴵ η₋ L
    ℓ₋  : Ordᴵ
    ev₋ : Ev ℓ₋ (fl ⊔ φ₋)
    p₋  : i <ᴵ ℓ₋
    G₋  : Goodᴺ (toZ (run O (fold 0 φ₋ cv₋ Q (Ωˢ η₋) ev₋ p₋)))
    eη  : η ≅ᴵ lvG G₋
    h₋  : η₋ ≺ᴵ η
open Br

module Step {fl} (Q : Run fl) (pf : PFl Q) (vQ : ∀ {i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → Good true (VisT i) (Q ev p)) (t2Q : T2 Q)
            (DmQ : ∀ {i} {O : Obs i} → VisT i O → ∀ {k′ φ′ ℓ′} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t →
                   (G : Goodᴺ (toZ (run O (fold 0 φ′ cv′ Q t ev′ p′)))) → ∀ {K} (k : InF K fl) → Dem (lvG G) k) where
  open FoldQ Q pf vQ
  open ChainM pf

  head≈ : ∀ {i} {O : Obs i} {φ₁ φ₂ k₁ k₂ ℓ₁ ℓ₂} {cv₁ : ∀ {L} → Ev L φ₁ → Simᴵ k₁ L} {cv₂ : ∀ {L} → Ev L φ₂ → Simᴵ k₂ L} {ev₁ : Ev ℓ₁ (fl ⊔ φ₁)} {ev₂ : Ev ℓ₂ (fl ⊔ φ₂)} {p₁ : i <ᴵ ℓ₁} {p₂ : i <ᴵ ℓ₂} →
          Ctx O → fo φ₁ O Q cv₁ ev₁ p₁ ≈ᵒ fo φ₂ O Q cv₂ ev₂ p₂
  head≈ {O = O} c = fo (ctx-refl O c) rQ

  CQ′ : ∀ {i} → Ordᴵ → Obs i → Ordᴵ → Set
  CQ′ {i} η₀ O b = ∀ {k′ φ′} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ℓ′} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t → Ωˢ η₀ ⊑ᴱ t →
                   (G : Goodᴺ (toZ (run O (fold 0 φ′ cv′ Q t ev′ p′)))) → suc b ⊑ᴵ lvG G

  rd : ∀ {i η₀ φ₀ ℓ₀ b} {O : Obs i} {cv₀ : ∀ {L} → Ev L φ₀ → Simᴵ η₀ L} {ev₀ : Ev ℓ₀ (fl ⊔ φ₀)} {p₀ : i <ᴵ ℓ₀} → Ctx O →
       (G₀ : Goodᴺ (toZ (run O (fold 0 φ₀ cv₀ Q (Ωˢ η₀) ev₀ p₀)))) → b ≺ᴵ lvG G₀ → CQ′ η₀ O b
  rd {i} {η₀} {φ₀} {O = O} {cv₀ = cv₀} {ev₀ = ev₀} {p₀ = p₀} cO G₀ h {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et fl G =
    s⊑′ (≺ᴵ-up h (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (toLevel-≅ (forceᴺ-HS _ G₀) (forceᴺ-HS _ (proj₁ L)) (forceᴺ-≅ d G₀ (proj₁ L))))
                             (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))))
    where
    d = toZ-≅ (run-≅ {O = O} {O′ = O} (ctx-refl O cO)
          (fold-≅0 {φ = φ₀} {φ′ = φ₀} {cv = cv₀} {cv′ = cv₀} {P = Q} {P′ = Q} rQ (Ωˢ-refl η₀) ev₀ p₀ ev₀ p₀ (≅ᴵ-refl i)))
    L = fold-congᴱ {φ = φ₀} {φ′ = φ′} {P = Q} {cv = cv₀} {cv′ = cv′} {ev = ev₀} {ev′ = ev′} {p = p₀} {p′ = p′} {x = Ωˢ η₀} {y = t} rQ fl (ctx-refl O cO) G

  one-fold′ : ∀ {i k′ φ′ ℓ′ K} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t → 𝟏 {K} ⊑ᴱ fold 0 φ′ cv′ Q t ev′ p′
  one-fold′ {φ′ = φ′} {K = K} {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et = one-fold {φ = φ′} {K = K} {cv = cv′} {ev = ev′} {p = p′} t et

  self-f : ∀ {i k′ φ′ ℓ′} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} {t : Ordˢ k′} → t ≅ˢ t → fold 0 φ′ cv′ Q t ev′ p′ ≅ˢ fold 0 φ′ cv′ Q t ev′ p′
  self-f {i} {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} et = fold-≅0 {φ = φ′} {φ′ = φ′} {cv = cv′} {cv′ = cv′} {P = Q} {P′ = Q} rQ et ev′ p′ ev′ p′ (≅ᴵ-refl i)

  ω1b : ∀ {b x L} → b ≅ᴵ x → x <ᴵ L → zero <ᴵ L → NZ b → Ωˢ (suc zero) ⊑ᴱ Ωˢ b
  ω1b {b} e q z nb = ω1′ (⊑ᴵ-≅ʳ (one⊑ z q (NZ-≅₁ nb e)) (≅ᴵ-sym e))
    where
    ω1′ : suc zero ⊑ᴵ b → Ωˢ (suc zero) ⊑ᴱ Ωˢ b
    ω1′ (s⊑ z≅ r) = Ω<ᴱ z≅ r

  twH : ∀ {i k′ φ′ ℓ′} {O : Obs i} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} → VisT i O → Tw (fo φ′ O Q cv′ ev′ p′)
  twH {i = zero} {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} refl s es os G = t2Q {φ = φ′} {cv = cv′} {ev = ev′} {z = p′} es os G
  twH {i = suc _} {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} v s es os G = tw v tt _ (self-f es) (λ {K} → one-fold′ {cv′ = cv′} {ev′ = ev′} {p′ = p′} s es) G
  twH {i = lim _ _} {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} v s es os G = tw v tt _ (self-f es) (λ {K} → one-fold′ {cv′ = cv′} {ev′ = ev′} {p′ = p′} s es) G

  cT : ∀ {i η φ′ ℓ′} {O : Obs i} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} → VisT i O → Br Q η O → Vis η (fo φ′ O Q cv′ ev′ p′)
  cT {i} v b = vis (pf , cxT i v) (λ _ → twH v) (λ h t et fl G → br b h t et fl G)

  c1 : ∀ {i φ′ ℓ′} {O : Obs i} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ (suc zero) L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} → VisT i O → Vis (suc zero) (fo φ′ O Q cv′ ev′ p′)
  c1 {i} {φ′} {O = O} {cv′ = cv′} {ev′ = ev′} {p′ = p′} v = vis (pf , cxT i v) (λ _ → twH v) cp₁
    where
    cp₁ : ∀ {b} → b ≺ᴵ suc zero → CvP (fo φ′ O Q cv′ ev′ p′) b
    cp₁ (via e zero) t et fl G = ⊑ᴵ-≅ˡ (s≅ (≅ᴵ-sym e)) (read1 O (cxT i v) _ (self-f et) (λ {K} → one-fold′ {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et) G)
    cp₁ (via e (suc ())) t et fl G

  readT : ∀ {i} {O : Obs i} (t : Ordˢ i) → VisT i O → t ≅ˢ t → Ωˢ i ⊑ᴱ t → (∀ {K} → 𝟏 {K} ⊑ᴱ t) → (G : Goodᴺ (toZ (run O t))) → suc i ⊑ᴵ lvG G
  readT {i = zero} t refl et fi one G = read1 idO tt t et one G
  readT {i = suc j} t v et fi one G = cp v (via (≅ᴵ-refl (suc j)) zero) t et (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fi) G
  readT {i = lim f s} t v et fi one G = cp v (via (≅ᴵ-refl (lim f s)) zero) t et (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fi) G

  growQ : ∀ {i a η₋ η′ φ₋ φ′ ℓ₋ ℓ′} {O : Obs i} {cv₋ : ∀ {L} → Ev L φ₋ → Simᴵ η₋ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} {ev₋ : Ev ℓ₋ (fl ⊔ φ₋)} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p₋ : i <ᴵ ℓ₋} {p′ : i <ᴵ ℓ′} →
          Ctx O → η₋ ≅ᴵ a → a <ᴵ η′ →
          (G₋ : Goodᴺ (toZ (run O (fold 0 φ₋ cv₋ Q (Ωˢ η₋) ev₋ p₋)))) (G′ : Goodᴺ (toZ (run O (fold 0 φ′ cv′ Q (Ωˢ η′) ev′ p′)))) → lvG G₋ ≺ᴵ lvG G′
  growQ {a = a} {η₋} {η′} {φ₋} {φ′} {O = O} {cv₋ = cv₋} {cv′ = cv′} {ev₋ = ev₋} {ev′ = ev′} {p₋ = p₋} {p′ = p′} cO e q G₋ G′ =
    ≺ᴵ-respˡ (toLevel-≅ (forceᴺ-HS _ G₋) (forceᴺ-HS _ (proj₁ S)) e₃) (toLevel-≺ (forceᴺ-HS _ (proj₁ S)) (forceᴺ-HS _ G′) (proj₂ L (proj₂ S)))
    where
    Os = fo φ′ O Q (λ e″ x → cv′ e″ (τ q x)) ev′ p′
    Oa = fo φ′ O Q (λ e″ x → cv′ e″ (τ q (suc x))) ev′ p′
    L = Ω<ᴱ (≅ᴵ-refl a) q {O = Os} {O′ = fo φ′ O Q cv′ ev′ p′} (head≈ cO) G′
    S = Ω-strict a {O = Oa} {O′ = Os} (head≈ cO) (pf , cO) (proj₁ L)
    e₃ = forceᴺ-≅ (toZ-≅ (run-≅ {O = fo φ₋ O Q cv₋ ev₋ p₋} {O′ = Oa} (head≈ cO) (Ωˢ-≅ e))) G₋ (proj₁ S)

  pickB : ∀ {i η b x y k′ φ′ ℓ′ φ₀ ℓ₀} {O : Obs i} {cv₀ : ∀ {L} → Ev L φ₀ → Simᴵ η L} {ev₀ : Ev ℓ₀ (fl ⊔ φ₀)} {p₀ : i <ᴵ ℓ₀} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} →
          Ctx O → Br Q η O → η ≅ᴵ x → b ≅ᴵ y → (G₀ : Goodᴺ (toZ (run O (fold 0 φ₀ cv₀ Q (Ωˢ η) ev₀ p₀)))) → b ≺ᴵ lvG G₀ →
          (y ≺ᴵ x ⊎ x ≺ᴵ y ⊎ y ≅ᴵ x) → (t : Ordˢ k′) → t ≅ˢ t → FlΩ b t → (G : Goodᴺ (toZ (run O (fold 0 φ′ cv′ Q t ev′ p′)))) → suc b ⊑ᴵ lvG G
  pickB cO B ex eb G₀ h (injᵃ s) t et fl G = br B (≺ᴵ-respˡ eb (≺ᴵ-respʳ s (≅ᴵ-sym ex))) t et fl G
  pickB cO B ex eb G₀ h (injᵇ s) t et fl G =
    rd cO G₀ h t et (fl (Ωˢ-refl _) (Ωvia (≺ᴵ-respˡ ex (≺ᴵ-respʳ s (≅ᴵ-sym eb))))) G
  pickB cO B ex eb G₀ h (injᶜ c) t et fl G =
    rd cO G₀ h t et (fl (Ωˢ-refl _) (≅→⊑ᴱ (Ωˢ-≅ (≅ᴵ-trans ex (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym eb)))))) G

  module V {i ℓ} (ev : Ev ℓ (fl ⊔ fk zero)) (p : i <ᴵ ℓ) where
    B : Top i ℓ (fl ⊔ fk zero)
    B = bound (fl ⊔ fk zero) ev p

    Lη : ∀ η → Bd B ⊑ᴵ η → Ordᴵ
    Lη η e = Mlev (Fc B) (suc η) (FB B e)

    evη : ∀ η (e : Bd B ⊑ᴵ η) → Ev (Lη η e) (fl ⊔ fk η)
    evη η e = liftEv fl (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)

    tg : ∀ η (e : Bd B ⊑ᴵ η) → i <ᴵ Lη η e
    tg η e = lim 0 (iF B)

    cvη : ∀ η {L} → Ev L (fk η) → Simᴵ η L
    cvη η e′ q = e′ (suc q)

    t₀ : Ordˢ i
    t₀ = fold 0 (fk zero) (λ e → e) Q (Ωˢ (suc zero)) ev p

    gη : ∀ η → Bd B ⊑ᴵ η → Ordˢ i
    gη η e = fold 0 (fk η) (cvη η) Q (Ωˢ η) (evη η e) (tg η e)

    one⊑η : ∀ η → Bd B ⊑ᴵ η → suc zero ⊑ᴵ η
    one⊑η η e = ⊑ᴵ-trans (s⊑ z≅ (proj₂ (evF B) zero)) (⊑ᴵ-trans (FM B) e)

    nzη : ∀ {η} → Bd B ⊑ᴵ η → NZ η
    nzη e with one⊑η _ e
    ... | s⊑ _ q = NZ-of q

    bd⊑ : ∀ {O : Obs i} → VisT i O → ∀ {k′ φ′ ℓ′} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t →
          (G : Goodᴺ (toZ (run O (fold 0 φ′ cv′ Q t ev′ p′)))) → suc i ⊑ᴵ lvG G → Bd B ⊑ᴵ lvG G
    bd⊑ v t et G (s⊑ e q) = ubd B (via e q) (λ { (inl k) → DmQ v t et G k ; (inr ink) → inj₂ z≅ })

    witV : ∀ j → Wit j (VisT j)
    witV zero = refl
    witV (suc _) = tt
    witV (lim _ _) = tt

    ch₀ : ∀ {O} → VisT i O → (G : Goodᴺ (toZ (run O t₀))) → Br Q (lvG G) O
    ch₀ {O} v G = br-mk brB (suc zero) (fk zero) (λ e → e) ℓ ev p G (≅ᴵ-refl _) two
      where
      cO = cxT i v
      z₁ : zero <ᴵ lvG G
      z₁ = zlt (read1 O cO t₀ (self-f (Ωˢ-refl (suc zero))) (λ {K} → one-fold′ {φ′ = fk zero} {cv′ = λ e → e} {ev′ = ev} {p′ = p} (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))) G)
      two : suc zero ≺ᴵ lvG G
      two = toLevel-≺ (hs hz) (forceᴺ-HS _ G) (twH {φ′ = fk zero} {cv′ = λ e → e} {ev′ = ev} {p′ = p} v (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) (Ω1ᴱ (suc zero)) G)
      brB : ∀ {b} → b ≺ᴵ lvG G → CQ Q O b
      brB {b = zero} h {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et fl G′ = read1 O cO _ (self-f et) (λ {K} → one-fold′ {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et) G′
      brB {b = suc b} h@(via e q) t et fl G′ = rd cO G h t et (fl (Ωˢ-refl _) (ω1b e q z₁ tt)) G′
      brB {b = lim f s} h@(via e q) t et fl G′ = rd cO G h t et (fl (Ωˢ-refl _) (ω1b e q z₁ tt)) G′

    chS : ∀ {O} η e → VisT i O → Br Q η O → (G : Goodᴺ (toZ (run O (gη η e)))) → Br Q (lvG G) O
    chS {O} η e v b G = br-mk brN η (fk η) (cvη η) (Lη η e) (evη η e) (tg η e) G (≅ᴵ-refl _) gr
      where
      cO = cxT i v
      gr : η ≺ᴵ lvG G
      gr = ≺ᴵ-respˡ (eη b) (grr (h₋ b))
        where
        grr : η₋ b ≺ᴵ η → lvG (G₋ b) ≺ᴵ lvG G
        grr (via e′ q) = growQ cO e′ q (G₋ b) G
      brN : ∀ {b′} → b′ ≺ᴵ lvG G → CQ Q O b′
      brN {b′} h t et fl G′ = go gr h
        where
        go : η ≺ᴵ lvG G → b′ ≺ᴵ lvG G → suc b′ ⊑ᴵ lvG G′
        go (via ex qx) h′@(via eb qb) = pickB cO b ex eb G h′ (<ᴵ-dec qb qx) t et fl G′

    val : Good true (VisT i) (Ω̂A 0 Q ev p)
    val = bŝ (λ η O → Br Q η O)
       (λ {η} {η′} eq b → br-mk (λ h → br b (≺ᴵ-respʳ h (≅ᴵ-sym eq))) (η₋ b) (φ₋ b) (cv₋ b) (ℓ₋ b) (ev₋ b) (p₋ b) (G₋ b) (≅ᴵ-trans (≅ᴵ-sym eq) (eη b)) (≺ᴵ-respʳ (h₋ b) eq))
       (Fk {φ = fk zero} {cv = λ e → e} {ev = ev} {p = p} tt {𝓖₁ = Vis (suc zero)} {𝓖₂ = VisT i} (λ v → c1 v) (λ v → v) (witV i) (Ωg (suc zero)) (Ωˢ-refl (suc zero)))
       (λ η e w → Fk {φ = fk η} {cv = cvη η} {ev = evη η e} {p = tg η e} (nzη e) {𝓖₁ = Vis η} {𝓖₂ = VisT i ∧ (λ O → Br Q η O)} (λ (v , b) → cT v b) proj₁ w (Ωg η) (Ωˢ-refl η))
       (self-f (Ωˢ-refl (suc zero)))
       (λ η e η′ e′ eq → fold-≅0 {φ = fk η} {φ′ = fk η′} {cv = cvη η} {cv′ = cvη η′} {P = Q} {P′ = Q} rQ (Ωˢ-≅ eq) (evη η e) (tg η e) (evη η′ e′) (tg η′ e′) (≅ᴵ-refl i))
       (λ η e → fold-cong {φ = fk zero} {φ′ = fk η} {cv = λ e′ → e′} {cv′ = cvη η} {ev = ev} {ev′ = evη η e} {p = p} {p′ = tg η e} rQ (Ω-monoᵒ (one⊑η η e)))
       (λ η e η′ e′ h → fold-cong {φ = fk η} {φ′ = fk η′} {cv = cvη η} {cv′ = cvη η′} {ev = evη η e} {ev′ = evη η′ e′} {p = tg η e} {p′ = tg η′ e′} rQ (Ω-monoᵒ h))
       (λ {O} v G → bd⊑ v (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G (readT t₀ v (self-f (Ωˢ-refl (suc zero))) (flw-fold {φ = fk zero} {cv = λ e → e} {ev = ev} {p = p} _ (Ωˢ-refl (suc zero))) (λ {K} → one-fold′ {φ′ = fk zero} {cv′ = λ e → e} {ev′ = ev} {p′ = p} (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))) G))
       (λ {O} η e v b G → bd⊑ v (Ωˢ η) (Ωˢ-refl η) G (readT (gη η e) v (self-f (Ωˢ-refl η)) (flw-fold {φ = fk η} {cv = cvη η} {ev = evη η e} {p = tg η e} _ (Ωˢ-refl η)) (λ {K} → one-fold′ {φ′ = fk η} {cv′ = cvη η} {ev′ = evη η e} {p′ = tg η e} (Ωˢ η) (Ωˢ-refl η)) G))
       ch₀ chS
```

## §2 塔: 一切 $k$ 与 $\omega$

`val∅`: 空前缀的值 $\Omega_i$. `vk`: 对 $k$ 递归, **每一步就是 `Step.V.val`**, 没有按阶段的输入; 除前缀的值 (`vk k`)、`PFl` 与 `T2` 外, 只用 `MxZ` (塔的地板全是 `fk zero`, 所以界字面是目标).

```agda
Fl : ℕ → Flr
Fl zero    = fz
Fl (suc k) = Fl k ⊔ fk zero

Pk : ∀ k → Run (Fl k)
Pk zero    = ∅ᴿ
Pk (suc k) = Ω̂A 0 (Pk k)

pfk : ∀ k → PFl (Pk k)
pfk zero    = pfl∅
pfk (suc k) = pfl-Ω̂ (pfk k)

t2k : ∀ k → T2 (Pk k)
t2k zero    = t2∅
t2k (suc k) = t2-Ω̂ (pfk k) (t2k k)

K-Fl : ∀ k {K} → InF K (Fl k) → K ≅ᴵ zero
K-Fl zero ()
K-Fl (suc k) (inl x)   = K-Fl k x
K-Fl (suc k) (inr ink) = z≅

DmZ : ∀ k {i} {O : Obs i} → VisT i O → ∀ {k′ φ′ ℓ′} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ev′ : Ev ℓ′ (Fl k ⊔ φ′)} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t →
      (G : Goodᴺ (toZ (run O (fold 0 φ′ cv′ (Pk k) t ev′ p′)))) → ∀ {K} (j : InF K (Fl k)) → Dem (lvG G) j
DmZ k v t et G j = dem j (inj₂ (K-Fl k j))

val∅ : ∀ {i ℓ} (ev : Ev ℓ fz) (p : i <ᴵ ℓ) → Good true (VisT i) (∅ᴿ ev p)
val∅ {i = zero}    ev p = b1
val∅ {i = suc j}   ev p = Good-mono (Vis-mono ≺-suc) (Ωg (suc j))
val∅ {i = lim f s} ev p = Good-mono (Vis-mono ≺-suc) (Ωg (lim f s))

vk : ∀ k {i ℓ} (ev : Ev ℓ (Fl k)) (p : i <ᴵ ℓ) → Good true (VisT i) (Pk k ev p)
vk zero    ev p = val∅ ev p
vk (suc k) ev p = Step.V.val (Pk k) (pfk k) (vk k) (t2k k) (DmZ k) ev p

Gᴺk : ∀ k {ℓ} (ev : Ev ℓ (Fl k)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Pk k ev z))
Gᴺk k ev z = Good→N refl (vk k ev z)

ev₁k : ∀ k → Ev (suc zero) (Fl k)
ev₁k zero    = tt
ev₁k (suc k) = ev₁k k , (λ q → q)

Tkᵁ : ℕ → Ordˢ zero
Tkᵁ k = Pk k (ev₁k k) zero

Gᵁk : ∀ k → Goodᴺ (toZ (Tkᵁ k))
Gᵁk k = Gᴺk k (ev₁k k) zero

rise-k : ∀ k → Tkᵁ k ⊑ᴱ Tkᵁ (suc k)
rise-k k = ŝ-rᴱ (B1ᴱ {φ = fk zero} {P = Pk k} {cv = λ e → e} {ev = ev₁k (suc k)} {p = zero} {x = Pk k (ev₁k k) zero} (PFl.rP (pfk k))
                     (≅→⊑ᴱ (PFl.rP (pfk k) (ev₁k k) zero (ev₁k k) zero z≅)) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)))

self-k : ∀ k → Tkᵁ k ≅ˢ Tkᵁ k
self-k k = PFl.rP (pfk k) (ev₁k k) zero (ev₁k k) zero z≅

Tωᵁ : Ordˢ zero
Tωᵁ = Ord₊ˢ.lim Tkᵁ

Gᴺω : Goodᴺ (toZ Tωᵁ)
Gᴺω = gl Gᵁk (λ k → ⊑-trans (≅→⊑ (forceᴺ-≅ (toZ-≅ (self-k k)) (Gᵁk k) (proj₁ (rise-k k idO (Gᵁk (suc k)))))) (proj₂ (rise-k k idO (Gᵁk (suc k)))))

G₃ : Goodᴺ (toZ (Tkᵁ 3))
G₃ = Gᵁk 3
```

## §3 判据

**闭包定理跨越帧数吗? 跨越.** `FoldQ.FF` 对任意前缀成立, `Step.V.val` 把上一阶段的值变成下一阶段的值, `vk` 对 $k$ 递归. 同一个定理, 同一个阶段步, 没有 $k$ 特有的情形.

**自动的:** 折叠的全部子句; 守卫沿链的封闭; 地板; 严格增长. **要输入的:** 只有塔的地板 (`MxZ`, `K-Fl`), 这是统一折叠的界的读法, 不是支配论证. **读记号得到的:** 无; Pending 的 `biV` 是读 `vs`/`occ<` 得到的启发, 本文的 `Above`/`St` 是它的语义替身, 证明与定义里没有记号.

**与 `PopCov` 三层的关系.** [UniformPendingGood](UniformPendingGood.lagda.md) 的三层在 $k=2$ 成立, 但 `mC` 只因 $\psi^{[]}$ 不弹栈才存在, 不能推到 $k=3$. 本文不是那套机器的修补, 而是换掉了 `Dom`: 从 "覆盖 + 全局 `ColC`" 换成 "上下文类的成员资格".

**还没做的.** 深度 $\ge1$ (`Obs` 没有 `fo1`, 等 `≅ᴬ`); 非紧界的前缀; `Goodᶻ` 的 "一切 $\eta$"; NotFree §6 (iii) 的树 $\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\Omega_{\mathtt{lvl}\,\gamma'_2}))$: 守卫 `Br` 不覆盖它, 所以本文的方法对它没有结论, 那条疑点既没有证实也没有否定.
