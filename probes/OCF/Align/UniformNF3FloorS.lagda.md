# 无符号闭包定理的地板形状 (二): 阶段步与非紧前缀

> 接 [UniformNF3FloorF](UniformNF3FloorF.lagda.md). 阶段步 `Step.V.val` 与 [UniformNF3Tower](UniformNF3Tower.lagda.md) 同形; 不同的是地板不再平凡.
>
> 结论先说:
>
> 1. **`Stage Q` (§2) 对两种操作封闭: `stΩ` ($Q\mapsto Q+\Omega_\Omega$) 与 `stTl` ($Q\mapsto Q+\Omega_\eta$, 非紧帧).** 任意交替都在里面; `cert` 给 `Goodᴺ`. 所以 $\psi_0(\Omega_\Omega+\Omega_\eta+\Omega_\Omega)$ 不需要新定理.
> 2. **`MxZ` 换成 `Bd` 的泛性质.** `bd⊑`: $\mathrm{Bd}\sqsubseteq$ 层号, 由 `ubd` 直接得到: 目标由 `readT` 给, 地板由 `dm` 给. `dm` 把类谓词 $D$ 翻译成 `Dem`.
> 3. **`stTl` 的唯一前提是覆盖 `cv0`: 第 0 层, 一切 $b\preceq\eta$ 有 `CQ`.** 链点自动满足它 (`Br→cv`, `first`). 这个前提也必须有: $\eta$ 高于前缀的值时支配是假的, 没有它 `Vis η` 不成立. 所以它是定义域而不是阶段特有的论证.
> 4. **第二条独立的阶段轴: 成立.** 地板形状和帧数一样, 不进证明.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3FloorS where

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
open import OCF.Align.UniformNF3NGrow using (_⊑ᴱ_; Ctx; ctx-refl; PFl; pfl; pfl∅; pfl-Ω̂; AFl; afl; 𝟏; ⊑ᴱ-trans; ≅→⊑ᴱ; B1ᴱ; Ω1ᴱ; Ω<ᴱ; Ω-strict; fold-congᴱ; ŝ-rᴱ; add-floorᴱ)
open import OCF.Align.UniformNF3Class
open import OCF.Align.UniformNF3ClassF using (NZ-of)
open import OCF.Align.UniformNF3FloorF

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

module Step (D : Ordᴵ → Set) (Dup : ∀ {X Y} → X ⊑ᴵ Y → D X → D Y) {fl} (Q : Run fl) (pf : PFl Q)
            (d0 : ∀ {φ k ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : zero <ᴵ ℓ} → LoD D (fo φ idO Q cv ev p))
            (vQ : ∀ {i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → Good true (VF D i) (Q ev p)) (t2Q : T2 Q)
            (dm : ∀ {X} → D X → ∀ {K} (q : InF K fl) → Dem X q) where
  open FoldQ D Dup Q pf d0 vQ
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

  twH : ∀ {i k′ φ′ ℓ′} {O : Obs i} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} → VT i O → Tw (fo φ′ O Q cv′ ev′ p′)
  twH {i = zero} {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} refl s es os G = t2Q {φ = φ′} {cv = cv′} {ev = ev′} {z = p′} es os G
  twH {i = suc _} {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} v s es os G = tw (proj₁ v) tt _ (self-f es) (λ {K} → one-fold′ {cv′ = cv′} {ev′ = ev′} {p′ = p′} s es) G
  twH {i = lim _ _} {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} v s es os G = tw (proj₁ v) tt _ (self-f es) (λ {K} → one-fold′ {cv′ = cv′} {ev′ = ev′} {p′ = p′} s es) G

  cT : ∀ {i η φ′ ℓ′} {O : Obs i} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} → VT i O → Br Q η O → Vis η (fo φ′ O Q cv′ ev′ p′)
  cT {i} v b = vis (pf , cxT i v) (λ _ → twH v) (λ h t et fl G → br b h t et fl G)

  c1 : ∀ {i φ′ ℓ′} {O : Obs i} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ (suc zero) L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} → VT i O → Vis (suc zero) (fo φ′ O Q cv′ ev′ p′)
  c1 {i} {φ′} {O = O} {cv′ = cv′} {ev′ = ev′} {p′ = p′} v = vis (pf , cxT i v) (λ _ → twH v) cp₁
    where
    cp₁ : ∀ {b} → b ≺ᴵ suc zero → CvP (fo φ′ O Q cv′ ev′ p′) b
    cp₁ (via e zero) t et fl G = ⊑ᴵ-≅ˡ (s≅ (≅ᴵ-sym e)) (read1 O (cxT i v) _ (self-f et) (λ {K} → one-fold′ {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et) G)
    cp₁ (via e (suc ())) t et fl G

  readT : ∀ {i} {O : Obs i} (t : Ordˢ i) → VT i O → t ≅ˢ t → Ωˢ i ⊑ᴱ t → (∀ {K} → 𝟏 {K} ⊑ᴱ t) → (G : Goodᴺ (toZ (run O t))) → suc i ⊑ᴵ lvG G
  readT {i = zero} t refl et fi one G = read1 idO tt t et one G
  readT {i = suc j} t v et fi one G = cp (proj₁ v) (via (≅ᴵ-refl (suc j)) zero) t et (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fi) G
  readT {i = lim f s} t v et fi one G = cp (proj₁ v) (via (≅ᴵ-refl (lim f s)) zero) t et (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fi) G

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

    bd⊑ : ∀ {O : Obs i} → VT i O → ∀ {k′ φ′ ℓ′} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t →
          (G : Goodᴺ (toZ (run O (fold 0 φ′ cv′ Q t ev′ p′)))) → suc i ⊑ᴵ lvG G → Bd B ⊑ᴵ lvG G
    bd⊑ v {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et G (s⊑ e q) =
      ubd B (via e q) (λ { (inl k) → dm (lfo v {φ = φ′} {cv = cv′} {ev = ev′} {p = p′} t et G) k ; (inr ink) → inj₂ z≅ })

    witV : ∀ j → Wit j (VT j)
    witV zero = refl
    witV (suc _) = tt
    witV (lim _ _) = tt

    ch₀ : ∀ {O} → VT i O → (G : Goodᴺ (toZ (run O t₀))) → Br Q (lvG G) O
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

    chS : ∀ {O} η e → VT i O → Br Q η O → (G : Goodᴺ (toZ (run O (gη η e)))) → Br Q (lvG G) O
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

    val : Good true (VT i) (Ω̂A 0 Q ev p)
    val = bŝ (λ η O → Br Q η O)
       (λ {η} {η′} eq b → br-mk (λ h → br b (≺ᴵ-respʳ h (≅ᴵ-sym eq))) (η₋ b) (φ₋ b) (cv₋ b) (ℓ₋ b) (ev₋ b) (p₋ b) (G₋ b) (≅ᴵ-trans (≅ᴵ-sym eq) (eη b)) (≺ᴵ-respʳ (h₋ b) eq))
       (Fk {φ = fk zero} {cv = λ e → e} {ev = ev} {p = p} tt {𝓖₁ = Vis (suc zero)} {𝓖₂ = VT i} (λ v → c1 v) (λ v → v) (witV i) (Ωg (suc zero)) (Ωˢ-refl (suc zero)))
       (λ η e w → Fk {φ = fk η} {cv = cvη η} {ev = evη η e} {p = tg η e} (nzη e) {𝓖₁ = Vis η} {𝓖₂ = VT i ∧ (λ O → Br Q η O)} (λ (v , b) → cT v b) proj₁ w (Ωg η) (Ωˢ-refl η))
       (self-f (Ωˢ-refl (suc zero)))
       (λ η e η′ e′ eq → fold-≅0 {φ = fk η} {φ′ = fk η′} {cv = cvη η} {cv′ = cvη η′} {P = Q} {P′ = Q} rQ (Ωˢ-≅ eq) (evη η e) (tg η e) (evη η′ e′) (tg η′ e′) (≅ᴵ-refl i))
       (λ η e → fold-cong {φ = fk zero} {φ′ = fk η} {cv = λ e′ → e′} {cv′ = cvη η} {ev = ev} {ev′ = evη η e} {p = p} {p′ = tg η e} rQ (Ω-monoᵒ (one⊑η η e)))
       (λ η e η′ e′ h → fold-cong {φ = fk η} {φ′ = fk η′} {cv = cvη η} {cv′ = cvη η′} {ev = evη η e} {ev′ = evη η′ e′} {p = tg η e} {p′ = tg η′ e′} rQ (Ω-monoᵒ h))
       (λ {O} v G → bd⊑ v (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G (readT t₀ v (self-f (Ωˢ-refl (suc zero))) (flw-fold {φ = fk zero} {cv = λ e → e} {ev = ev} {p = p} _ (Ωˢ-refl (suc zero))) (λ {K} → one-fold′ {φ′ = fk zero} {cv′ = λ e → e} {ev′ = ev} {p′ = p} (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))) G))
       (λ {O} η e v b G → bd⊑ v (Ωˢ η) (Ωˢ-refl η) G (readT (gη η e) v (self-f (Ωˢ-refl η)) (flw-fold {φ = fk η} {cv = cvη η} {ev = evη η e} {p = tg η e} _ (Ωˢ-refl η)) (λ {K} → one-fold′ {φ′ = fk η} {cv′ = cvη η} {ev′ = evη η e} {p′ = tg η e} (Ωˢ η) (Ωˢ-refl η)) G))
       ch₀ chS
```


## §2 阶段

`Stage Q`: 前缀 $Q$ 的全部输入, 没有阶段号. `D` 是类谓词 (`LoD D` 是非零目标的上下文要满足的层号下界), `dm` 说它支配 $Q$ 的地板. 塔的 `DmZ` 对应 `D` 恒真.

```agda
record Stage {fl} (Q : Run fl) : Set₁ where
  field
    D   : Ordᴵ → Set
    Dup : ∀ {X Y} → X ⊑ᴵ Y → D X → D Y
    pf  : PFl Q
    d0  : ∀ {φ k ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : zero <ᴵ ℓ} → LoD D (fo φ idO Q cv ev p)
    vQ  : ∀ {i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → Good true (VF D i) (Q ev p)
    t2  : T2 Q
    dm  : ∀ {X} → D X → ∀ {K} (q : InF K fl) → Dem X q

cert : ∀ {fl} {Q : Run fl} → Stage Q → ∀ {ℓ} (ev : Ev ℓ fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Q ev z))
cert S ev z = Good→N refl (Stage.vQ S ev z)

val∅ : ∀ {i ℓ} (ev : Ev ℓ fz) (p : i <ᴵ ℓ) → Good true (VF (λ _ → ⊤) i) (∅ᴿ ev p)
val∅ {i = zero}    ev p = b1
val∅ {i = suc j}   ev p = Good-mono (λ v → Vis-mono ≺-suc (proj₁ v)) (Ωg (suc j))
val∅ {i = lim f s} ev p = Good-mono (λ v → Vis-mono ≺-suc (proj₁ v)) (Ωg (lim f s))

stage∅ : Stage ∅ᴿ
stage∅ = record { D = λ _ → ⊤ ; Dup = λ _ _ → tt ; pf = pfl∅ ; d0 = λ _ _ _ → tt ; vQ = val∅ ; t2 = t2∅ ; dm = λ { _ () } }

module OfS {fl} {Q : Run fl} (S : Stage Q) where
  open Stage S
  module St = Step D Dup Q pf d0 vQ t2 dm
  open St using (self-f; twH; growQ)
  open FoldQ D Dup Q pf d0 vQ using (FF; Fk; flw-fold; cxT; lfo)
  open ChainM pf using (rQ)
```

`stΩ`: 下一帧是闭包. 类谓词不变; 第 0 层的 `d0` 走第 0 个链点.

```agda
  d0Ω : ∀ {φ k ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ ((fl ⊔ fk zero) ⊔ φ)} {p : zero <ᴵ ℓ} → LoD D (fo φ idO (Ω̂A 0 Q) cv ev p)
  d0Ω {φ} {cv = cv} {ev} {p} s es G = Dup (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)) (d0 {φ = fk zero} {cv = λ e → e} {ev = proj₁ ev} {p = p} (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) (proj₁ L))
    where
    et = fold-≅0 {φ = fk zero} {φ′ = fk zero} {cv = λ e → e} {cv′ = λ e → e} {P = Q} {P′ = Q} rQ (Ωˢ-refl (suc zero)) (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl zero)
    L = B1ᴱ {φ = φ} {P = Ω̂A 0 Q} {cv = cv} {ev = ev} {p = p} {x = fold 0 (fk zero) (λ e → e) Q (Ωˢ (suc zero)) (proj₁ ev) p} (rΩ̂ rQ) (ŝ-rᴱ (≅→⊑ᴱ et)) s es idO G

  stΩ : Stage (Ω̂A 0 Q)
  stΩ = record { D = D ; Dup = Dup ; pf = pfl-Ω̂ pf ; d0 = λ {φ} {k} {ℓ} {cv} {ev} {p} → d0Ω {φ = φ} {cv = cv} {ev = ev} {p = p}
               ; vQ = St.V.val ; t2 = t2-Ω̂ pf t2 ; dm = λ { d (inl q) → dm d q ; d (inr ink) → inj₂ z≅ } }
```

`Tail η φ₀ cv₀`: 非紧帧 $Q+\Omega_\eta$. `cv0` 是第 0 层的覆盖: 一切 $b\preceq\eta$ 有 `CQ`. 类谓词加上 "层号 $\sqsupseteq\eta+1$": 这是吸收者, 它出现在每一个非零目标的上下文上. `dmφ` 说这个下界支配新地板 ($\varphi_0=$ `fk η` 时平凡).

```agda
  module Tail (η : Ordᴵ) (nη : NZ η) (φ₀ : Flr) (cv₀ : ∀ {L} → Ev L φ₀ → Simᴵ η L)
              (dmφ : ∀ {X} → suc η ⊑ᴵ X → ∀ {K} (q : InF K φ₀) → Dem X q)
              (cv0 : ∀ {b} → b ≺ᴵ suc η → CQ Q {zero} idO b) where
    Tl : Run (fl ⊔ φ₀)
    Tl ev p = fold 0 φ₀ cv₀ Q (Ωˢ η) ev p

    D′ : Ordᴵ → Set
    D′ X = D X × (suc η ⊑ᴵ X)

    rT : Tl ≈ᴿ Tl
    rT ev p ev′ p′ ei = fold-≅0 {φ = φ₀} {φ′ = φ₀} {cv = cv₀} {cv′ = cv₀} {P = Q} {P′ = Q} rQ (Ωˢ-refl η) ev p ev′ p′ ei

    pfT : PFl Tl
    pfT = pfl rT (λ ev p → flw-fold {φ = φ₀} {cv = cv₀} {ev = ev} {p = p} (Ωˢ η) (Ωˢ-refl η))
              (λ {φ} {k} {i} {ℓ} {cv} ev p y ey oy → B1ᴱ {φ = φ} {P = Tl} {cv = cv} {ev = ev} {p = p} rT (PFl.fS pf {φ = φ₀} {cv = cv₀} (proj₁ ev) p (Ωˢ η) (Ωˢ-refl η) (Ω1ᴱ η)) y ey)

    t2T : T2 Tl
    t2T {φ = φ} {cv = cv} {ev = ev} {z = z} {y = y} ey oy G = proj₂ L (t2 {φ = φ₀} {cv = cv₀} {ev = proj₁ ev} {z = z} (Ωˢ-refl η) (Ω1ᴱ η) (proj₁ L))
      where
      L = B1ᴱ {φ = φ} {P = Tl} {cv = cv} {ev = ev} {p = z} {x = Tl (proj₁ ev) z} rT (≅→⊑ᴱ (rT (proj₁ ev) z (proj₁ ev) z (≅ᴵ-refl zero))) y ey idO G

    d0T : ∀ {φ k ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ ((fl ⊔ φ₀) ⊔ φ)} {p : zero <ᴵ ℓ} → LoD D′ (fo φ idO Tl cv ev p)
    d0T {φ} {cv = cv} {ev} {p} s es G =
      Dup upL (d0 {φ = φ₀} {cv = cv₀} {ev = proj₁ ev} {p = p} (Ωˢ η) (Ωˢ-refl η) (proj₁ L)) ,
      ⊑ᴵ-trans (cv0 {b = η} (via (≅ᴵ-refl η) zero) {φ′ = φ₀} {cv′ = cv₀} {ev′ = proj₁ ev} {p′ = p} (Ωˢ η) (Ωˢ-refl η) (λ _ h → h) (proj₁ L)) upL
      where
      L = B1ᴱ {φ = φ} {P = Tl} {cv = cv} {ev = ev} {p = p} {x = Tl (proj₁ ev) p} rT (≅→⊑ᴱ (rT (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl zero))) s es idO G
      upL = toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)

    H₂T : ∀ {i} {O : Obs i} → VF D′ i O → VF D i O
    H₂T {i = zero}    v = v
    H₂T {i = suc _}   (v , l) = v , (λ s es G → proj₁ (l s es G))
    H₂T {i = lim _ _} (v , l) = v , (λ s es G → proj₁ (l s es G))

    covT : ∀ {i b} {O : Obs i} → VF D′ i O → b ≺ᴵ η → CQ Q O b
    covT {i = zero} refl h = cv0 (≺ᴵ-up h (Sim→⊑ᴵ suc))
    covT {i = suc _} (v , l) h {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et fl G = ⊑ᴵ-trans (s⊑′ h) (⊑ᴵ-trans (Sim→⊑ᴵ suc) (proj₂ (l _ (self-f et) G)))
    covT {i = lim _ _} (v , l) h {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et fl G = ⊑ᴵ-trans (s⊑′ h) (⊑ᴵ-trans (Sim→⊑ᴵ suc) (proj₂ (l _ (self-f et) G)))

    witT : ∀ i → Wit i (VF D′ i)
    witT zero = refl
    witT (suc _) = tt
    witT (lim _ _) = tt

    vT : ∀ {i ℓ} (ev : Ev ℓ (fl ⊔ φ₀)) (p : i <ᴵ ℓ) → Good true (VF D′ i) (Tl ev p)
    vT {i} ev p = Fk {φ = φ₀} {cv = cv₀} {ev = ev} {p = p} nη {𝓖₁ = Vis η} {𝓖₂ = VF D′ i}
      (λ v → vis (pf , cxT i (H₂T v)) (λ _ → twH (H₂T v)) (λ h t et fl G → covT v h t et fl G))
      H₂T (witT i) (Ωg η) (Ωˢ-refl η)

    stTl : Stage Tl
    stTl = record { D = D′ ; Dup = λ u x → Dup u (proj₁ x) , ⊑ᴵ-trans (proj₂ x) u ; pf = pfT
                  ; d0 = λ {φ} {k} {ℓ} {cv} {ev} {p} → d0T {φ = φ} {cv = cv} {ev = ev} {p = p}
                  ; vQ = vT ; t2 = t2T ; dm = λ { x (inl q) → dm (proj₁ x) q ; x (inr q) → dmφ (proj₂ x) q } }
```

## §3 链点给出覆盖

`Br→cv`: 守卫 `Br Q η idO` 蕴含 `Tail` 的前提. $b\prec\eta$ 是字段 `br`; $b\cong\eta$ 是严格增长 `growQ`: 尾巴地板 $\sqsupseteq\Omega_\eta$ 的值不低于 $Q+\Omega_\eta$, 后者严格高于上一个链点, 其层号就是 $\eta$. `CP`: 第 0 层的链点 (层号, 界的支配, 守卫). `cpn n`: 第 $n$ 个. `TlAt`: 每个链点都给出一个非紧的阶段, 没有任何附加输入.

```agda
  Br→cv : ∀ {η φ₁ ℓ₁} {cv₁ : ∀ {L} → Ev L φ₁ → Simᴵ η L} {ev₁ : Ev ℓ₁ (fl ⊔ φ₁)} {p₁ : zero <ᴵ ℓ₁} → Br Q η idO → ∀ {b} → b ≺ᴵ suc η → CQ Q {zero} idO b
  Br→cv B (via e (suc q)) t et fl G = br B (via e q) t et fl G
  Br→cv {η} {φ₁} {cv₁ = cv₁} {ev₁ = ev₁} {p₁ = p₁} B {b} (via e zero) {φ′ = φ′} {cv′ = cv′} {ev′ = ev′} {p′ = p′} t et fl G =
    ⊑ᴵ-≅ˡ (s≅ (≅ᴵ-sym e)) (s⊑′ (≺ᴵ-up (≺ᴵ-respˡ (eη B) (gr (h₋ B))) (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))))
    where
    L = fold-congᴱ {φ = φ₁} {φ′ = φ′} {P = Q} {cv = cv₁} {cv′ = cv′} {ev = ev₁} {ev′ = ev′} {p = p₁} {p′ = p′} {x = Ωˢ η} {y = t} rQ (fl (Ωˢ-refl η) (≅→⊑ᴱ (Ωˢ-≅ (≅ᴵ-sym e)))) idO G
    gr : η₋ B ≺ᴵ η → lvG (G₋ B) ≺ᴵ lvG (proj₁ L)
    gr (via e′ q) = growQ tt e′ q (G₋ B) (proj₁ L)

  dmk : ∀ {η X} → suc η ⊑ᴵ X → ∀ {K} (q : InF K (fk η)) → Dem X q
  dmk (s⊑ e q) ink = inj₁ (via e q)

  module Chain {ℓ} (ev : Ev ℓ (fl ⊔ fk zero)) (z : zero <ᴵ ℓ) where
    open St.V ev z

    record CP : Set where
      constructor cp-mk
      field
        lvη : Ordᴵ
        leη : Bd B ⊑ᴵ lvη
        brη : Br Q lvη idO
    open CP public

    G₀ : Goodᴺ (toZ t₀)
    G₀ = Good→N refl (Fk {φ = fk zero} {cv = λ e → e} {ev = ev} {p = z} tt {𝓖₁ = Vis (suc zero)} {𝓖₂ = VF D zero} (λ v → St.c1 v) (λ v → v) refl (Ωg (suc zero)) (Ωˢ-refl (suc zero)))

    cp0 : CP
    cp0 = cp-mk (lvG G₀) (bd⊑ refl (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G₀
                 (St.readT t₀ refl (self-f (Ωˢ-refl (suc zero))) (flw-fold {φ = fk zero} {cv = λ e → e} {ev = ev} {p = z} _ (Ωˢ-refl (suc zero))) (λ {K} → St.one-fold′ {φ′ = fk zero} {cv′ = λ e → e} {ev′ = ev} {p′ = z} (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))) G₀))
                 (ch₀ refl G₀)

    Gnext : (c : CP) → Goodᴺ (toZ (gη (lvη c) (leη c)))
    Gnext (cp-mk η e b) = Good→N (refl , b) (Fk {φ = fk η} {cv = cvη η} {ev = evη η e} {p = tg η e} (nzη e) {𝓖₁ = Vis η} {𝓖₂ = VF D zero ∧ (λ O → Br Q η O)} (λ (v , b′) → St.cT v b′) proj₁ (refl , b) (Ωg η) (Ωˢ-refl η))

    cpS : CP → CP
    cpS c@(cp-mk η e b) = cp-mk (lvG (Gnext c)) (bd⊑ refl (Ωˢ η) (Ωˢ-refl η) (Gnext c)
                 (St.readT (gη η e) refl (self-f (Ωˢ-refl η)) (flw-fold {φ = fk η} {cv = cvη η} {ev = evη η e} {p = tg η e} _ (Ωˢ-refl η)) (λ {K} → St.one-fold′ {φ′ = fk η} {cv′ = cvη η} {ev′ = evη η e} {p′ = tg η e} (Ωˢ η) (Ωˢ-refl η)) (Gnext c)))
                 (chS η e refl b (Gnext c))

    cpn : ℕ → CP
    cpn zero    = cp0
    cpn (suc n) = cpS (cpn n)

    module TlAt (c : CP) = Tail (lvη c) (nzη (leη c)) (fk (lvη c)) (cvη (lvη c)) dmk
        (Br→cv {cv₁ = cvη (lvη c)} {ev₁ = evη (lvη c) (leη c)} {p₁ = tg (lvη c) (leη c)} (brη c))
```

## §4 实例: $\psi_0(\Omega_\Omega+\Omega_\eta+\Omega_\Omega)$

`Q₁`: $\Omega_\Omega$. `ηn n`: $\psi_0(\Omega_\Omega+\Omega_\ldots)$ 链上第 $n$ 个点的层号. `Q₂ n`: $\Omega_\Omega+\Omega_{\eta_n}$, 地板 `fk (ηn n)`, 非平凡. `Q₃ n`: 再加一个 $\Omega_\Omega$, 界 `Bd` 现在不是目标加一. `GᴺNT`: 证书, 对一切环境与一切 $n$. `Sk`: 再往上叠 $k$ 个 $\Omega_\Omega$, 地板形状不变, 仍在定理里.

```agda
Fl₁ : Flr
Fl₁ = fz ⊔ fk zero

Q₁ : Run Fl₁
Q₁ = Ω̂A 0 ∅ᴿ

S₁ : Stage Q₁
S₁ = OfS.stΩ stage∅

ev₁₁ : Ev (suc zero) (Fl₁ ⊔ fk zero)
ev₁₁ = (tt , (λ q → q)) , (λ q → q)

module Ch₁ = OfS.Chain S₁ ev₁₁ zero

ηn : ℕ → Ordᴵ
ηn n = Ch₁.lvη (Ch₁.cpn n)

module TA (n : ℕ) = OfS.Chain.TlAt S₁ ev₁₁ zero (Ch₁.cpn n)

Q₂ : ∀ n → Run (Fl₁ ⊔ fk (ηn n))
Q₂ n = TA.Tl n

S₂ : ∀ n → Stage (Q₂ n)
S₂ n = TA.stTl n

Q₃ : ∀ n → Run ((Fl₁ ⊔ fk (ηn n)) ⊔ fk zero)
Q₃ n = Ω̂A 0 (Q₂ n)

S₃ : ∀ n → Stage (Q₃ n)
S₃ n = OfS.stΩ (S₂ n)

GᴺNT : ∀ n {ℓ} (ev : Ev ℓ ((Fl₁ ⊔ fk (ηn n)) ⊔ fk zero)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Q₃ n ev z))
GᴺNT n = cert (S₃ n)

Flk : ∀ n → ℕ → Flr
Flk n zero    = (Fl₁ ⊔ fk (ηn n)) ⊔ fk zero
Flk n (suc k) = Flk n k ⊔ fk zero

Qk : ∀ n k → Run (Flk n k)
Qk n zero    = Q₃ n
Qk n (suc k) = Ω̂A 0 (Qk n k)

Sk : ∀ n k → Stage (Qk n k)
Sk n zero    = S₃ n
Sk n (suc k) = OfS.stΩ (Sk n k)

GᴺNTk : ∀ n k {ℓ} (ev : Ev ℓ (Flk n k)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Qk n k ev z))
GᴺNTk n k = cert (Sk n k)

zq : ∀ n → zero <ᴵ ηn n
zq n with OfS.St.V.one⊑η S₁ ev₁₁ zero (ηn n) (Ch₁.leη (Ch₁.cpn n))
... | s⊑ z≅ q = q

s₁ : ∀ n → Simᴵ (suc zero) (suc (suc (ηn n)))
s₁ n zero = suc (suc (zq n))
s₁ n (suc ())

ev₃ : ∀ n → Ev (suc (suc (ηn n))) ((Fl₁ ⊔ fk (ηn n)) ⊔ fk zero)
ev₃ n = (((tt , s₁ n) , (λ q → suc q)) , s₁ n)

GᴺNT₀ : ∀ n → Goodᴺ (toZ (Q₃ n (ev₃ n) (suc (suc (zq n)))))
GᴺNT₀ n = GᴺNT n (ev₃ n) (suc (suc (zq n)))
```
