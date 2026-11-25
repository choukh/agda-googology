# N 的跨层爬升
不读记号；编译定理 `climb`：`YiLXClimb.climb` 的陈述把 `Le` 换成 `YiRRRel.N`（底、起点、输出都按 `N`），其余前提（`NoΩ`、`Dom`）不变，`Fit` 多一条 `fSi`（后继形状结点上目标路径取 `inc`）；层号、路径、两侧的底与表、目标层都是变量。
证法逐行照 `YiLXClimb.climb`，同层一步换成 `YiRRFold.fl`。不否定什么；实例在 [YiRRTwo](YiRRTwo.lagda.md)。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRRClimb where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp)
open import OCF.Lean.YiVRRel using (NoΩ)
open import OCF.Lean.YiVRFold using (Pr)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono)
open import OCF.Lean.YiOFPath using (pull-base)
open import OCF.Lean.YiTYPath using (pull-ok)
open import OCF.Lean.YiLXClimb using (Dom; anchor; ⊴◃-◃; cum-pos)
open import OCF.Lean.YiRRRel
open import OCF.Lean.YiRRFold using (_⊴ⁿ_; fl; inflA; node≼ʳ)

```

`Fit` 照 `YiLXClimb.Fit`, 多一条 `fSi`: 后继形状的结点上目标路径也可取 `inc` (折叠的行与 `inu` 相同).

```agda
data Fit {j : L} : ∀ {ℓ ℓ′} → ℓ ⊑ ℓ′ → j ≤ ℓ → j ≤ ℓ′ → Set where
  fself : ∀ {ℓ} {w : j ≤ ℓ} → Fit self w w
  fS  : ∀ {ℓ} {h : ⊤ → L} {v : ℓ ⊑ h tt} {w w′} → Fit v w w′ → Fit {ℓ′ = nd sS h} (inc tt v) w (inu (λ _ → w′))
  fSi : ∀ {ℓ} {h : ⊤ → L} {v : ℓ ⊑ h tt} {w w′} → Fit v w w′ → Fit {ℓ′ = nd sS h} (inc tt v) w (inc tt w′)
  fSu : ∀ {ℓ} {h : ⊤ → L} {vs : (c : ⊤) → ℓ ⊑ h c} {w w′} → Fit (vs tt) w w′ → Fit {ℓ′ = nd sS h} (inu vs) w (inu (λ _ → w′))
  fL  : ∀ {ℓ} {g : ℕ → L} {n} {v : ℓ ⊑ g n} {w} {ws : (k : ℕ) → j ≤ g k} → Fit v w (ws n) → Fit (inc n v) w (inu ws)
  fLu : ∀ {ℓ} {g : ℕ → L} {vs : (k : ℕ) → ℓ ⊑ g k} {w} {ws : (k : ℕ) → j ≤ g k} → Fit (vs zero) w (ws zero) → Fit (inu vs) w (inu ws)
  fΩ  : ∀ {ℓ k} {h : Tr k → L} {v : ℓ ⊑ h zero} {w} {ws : (c : Tr k) → j ≤ h c} → Fit v w (ws zero) → Fit {ℓ′ = nd (sΩ k) h} (inc zero v) w (inu ws)
  fΩu : ∀ {ℓ k} {h : Tr k → L} {vs : (c : Tr k) → ℓ ⊑ h c} {w} {ws : (c : Tr k) → j ≤ h c} → Fit (vs zero) w (ws zero) → Fit {ℓ′ = nd (sΩ k) h} (inu vs) w (inu ws)

pull-ext : ∀ {ℓ ℓ′} (v : ℓ ⊑ ℓ′) {B : Base ℓ} {B₁ B₂ : Base ℓ′}
  → ((i : L) (u : i ≤ ℓ′) → Pr u → ∀ {a} → N i a (proj₁ (B₁ i u)) → N i a (proj₁ (B₂ i u)))
  → B ⊴ⁿ pull-base v B₁ → B ⊴ⁿ pull-base v B₂
pull-ext self H hB i u q = H i u q (hB i u q)
pull-ext (inc c v) {B} {B₁} {B₂} H hB = pull-ext v {B} {λ i u → B₁ i (inc c u)} {λ i u → B₂ i (inc c u)} (λ i u _ → H i (inc c u) tt) hB
pull-ext {ℓ′ = nd s h} (inu vs) {B} {B₁} {B₂} H hB =
  pull-ext (vs (c₀ s)) {B} {λ i u → B₁ i (inc (c₀ s) u)} {λ i u → B₂ i (inc (c₀ s) u)} (λ i u _ → H i (inc (c₀ s) u) tt) hB

peelS : (a : L) (o : Ok (nd sS (λ _ → a))) (r : Rb (nd sS (λ _ → a))) (bs : Base (nd sS (λ _ → a)))
  (j : L) (w : j ≤ a) (β : Tr⁺ j) {x : Tr j}
  → N j x (proj₁ (ψ a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β (proj₁ (Ωt a))))
  → a ⊢ proj₁ (Ωt a) ◃ suc (proj₁ (next⁺ (bs a (inc tt self))))
  → N j x (proj₁ (ψ (nd sS (λ _ → a)) o r bs j (inu (λ _ → w)) β (proj₁ (Ωt (nd sS (λ _ → a))))))
peelS a o r bs j w β e d = ≼l 1 (right-add
  (le◃ e (mono a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β d))
  (proj₁ (ψ a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β (suc zero))))

peelSi : (a : L) (o : Ok (nd sS (λ _ → a))) (r : Rb (nd sS (λ _ → a))) (bs : Base (nd sS (λ _ → a)))
  (j : L) (w : j ≤ a) (β : Tr⁺ j) {x : Tr j}
  → N j x (proj₁ (ψ a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β (proj₁ (Ωt a))))
  → a ⊢ proj₁ (Ωt a) ◃ suc (proj₁ (next⁺ (bs a (inc tt self))))
  → N j x (proj₁ (ψ (nd sS (λ _ → a)) o r bs j (inc tt w) β (proj₁ (Ωt (nd sS (λ _ → a))))))
peelSi a o r bs j w β e d = ≼l 1 (right-add
  (le◃ e (mono a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β d))
  (proj₁ (ψ a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β (suc zero))))

climb : ∀ {j ℓ ℓ′} (v : ℓ ⊑ ℓ′) {w : j ≤ ℓ} {w′ : j ≤ ℓ′} → Fit v w w′ → NoΩ ℓ
  → (o′ : Ok ℓ′) (r : Rb ℓ) (r′ : Rb ℓ′) (B : Base ℓ) (B′ : Base ℓ′)
  → B ⊴ⁿ pull-base v B′ → Dom B′ → (β β′ : Tr⁺ j) → N j (proj₁ β) (proj₁ β′)
  → N j (proj₁ (ψ ℓ (pull-ok v o′) r B j w β (proj₁ (Ωt ℓ))))
        (proj₁ (ψ ℓ′ o′ r′ B′ j w′ β′ (proj₁ (Ωt ℓ′))))
climb {j} {ℓ} _ {w} fself ν o′ r r′ B B′ hB dB β β′ hβ =
  fl ℓ ν o′ r r′ B B′ hB dB j w β β′ hβ (Ωt≼ ℓ ν)
climb {j} _ (fS {h = h} {v = v} {w′ = w′} fit) ν o′ r r′ B B′ hB dB β β′ hβ =
  peelS (h tt) o′ r′ B′ j w′ β′
    (climb v fit ν (proj₂ o′ tt) r (proj₂ r′ tt) B (λ i u → B′ i (inc tt u)) hB
      (λ i u _ → dB i (inc tt u) tt) β β′ hβ)
    (anchor (h tt) (B′ (h tt) (inc tt self)) (dB (h tt) (inc tt self) tt))
climb {j} _ (fSi {h = h} {v = v} {w′ = w′} fit) ν o′ r r′ B B′ hB dB β β′ hβ =
  peelSi (h tt) o′ r′ B′ j w′ β′
    (climb v fit ν (proj₂ o′ tt) r (proj₂ r′ tt) B (λ i u → B′ i (inc tt u)) hB
      (λ i u _ → dB i (inc tt u) tt) β β′ hβ)
    (anchor (h tt) (B′ (h tt) (inc tt self)) (dB (h tt) (inc tt self) tt))
climb {j} _ (fSu {h = h} {vs = vs} {w′ = w′} fit) ν o′ r r′ B B′ hB dB β β′ hβ =
  peelS (h tt) o′ r′ B′ j w′ β′
    (climb (vs tt) fit ν (proj₂ o′ tt) r (proj₂ r′ tt) B (λ i u → B′ i (inc tt u)) hB
      (λ i u _ → dB i (inc tt u) tt) β β′ hβ)
    (anchor (h tt) (B′ (h tt) (inc tt self)) (dB (h tt) (inc tt self) tt))
climb {j} _ (fL {g = g} {n = zero} {v = v} fit) ν o′ r r′ B B′ hB dB β β′ hβ =
  ≼l zero (climb v fit ν (proj₂ o′ zero) r (proj₂ r′ zero) B (λ i u → B′ i (inc zero u)) hB
    (λ i u _ → dB i (inc zero u) tt) β β′ hβ)
climb {j} _ (fL {g = g} {n = suc k} {v = v} {ws = ws} fit) ν o′ r r′ B B′ hB dB β β′ hβ =
  ≼l (suc k) (climb v fit ν (proj₂ o′ (suc k)) r (proj₂ r′ (suc k)) B Bk
    (pull-ext v {B} {λ i u → B′ i (inc (suc k) u)} {Bk}
      (λ i u _ d → inflA (nd sL g) o′ r′ B′ i (inc (suc k) u) (B′ i (inc (suc k) u)) Pk d) hB)
    (λ i u _ → ⊴◃-◃ (dB i (inc (suc k) u) tt)
      (mono (nd sL g) o′ r′ B′ i (inc (suc k) u) (B′ i (inc (suc k) u)) (cum-pos Fk k)))
    β βk (inflA (nd sL g) o′ r′ B′ j (inu ws) β′ Pk hβ))
  where
  Fk : ℕ → Tr⁺ (nd sL g)
  Fk m = upz m (Ωt (g m))
  Pk : Tr (nd sL g)
  Pk = cum (λ m → proj₁ (Fk m)) k
  Bk : Base (g (suc k))
  Bk i u = ψ (nd sL g) o′ r′ B′ i (inc (suc k) u) (B′ i (inc (suc k) u)) Pk
  βk : Tr⁺ j
  βk = ψ (nd sL g) o′ r′ B′ j (inu ws) β′ Pk
climb {j} _ (fLu {g = g} {vs = vs} fit) ν o′ r r′ B B′ hB dB β β′ hβ =
  ≼l zero (climb (vs zero) fit ν (proj₂ o′ zero) r (proj₂ r′ zero) B (λ i u → B′ i (inc zero u)) hB
    (λ i u _ → dB i (inc zero u) tt) β β′ hβ)
climb {j} _ (fΩ {k = k} {h = h} {v = v} {ws = ws} fit) ν o′ r r′ B B′ hB dB β β′ hβ =
  node≼ʳ (kp (nd (sΩ k) h) o′ (inj₁ (inj₁ tt)) (inu ws)) _ _
    (climb v fit ν (proj₂ o′ zero) r (proj₂ r′ zero) B (λ i u → B′ i (inc zero u)) hB
      (λ i u _ → dB i (inc zero u) tt) β β′ hβ)
climb {j} _ (fΩu {k = k} {h = h} {vs = vs} {ws = ws} fit) ν o′ r r′ B B′ hB dB β β′ hβ =
  node≼ʳ (kp (nd (sΩ k) h) o′ (inj₁ (inj₁ tt)) (inu ws)) _ _
    (climb (vs zero) fit ν (proj₂ o′ zero) r (proj₂ r′ zero) B (λ i u → B′ i (inc zero u)) hB
      (λ i u _ → dB i (inc zero u) tt) β β′ hβ)

climbₒ : ∀ {j ℓ ℓ′} (v : ℓ ⊑ ℓ′) {w : j ≤ ℓ} {w′ : j ≤ ℓ′} → Fit v w w′ → NoΩ ℓ
  → (o′ : Ok ℓ′) (o : Ok ℓ) → o ≡ pull-ok v o′ → (r : Rb ℓ) (r′ : Rb ℓ′) (B : Base ℓ) (B′ : Base ℓ′)
  → B ⊴ⁿ pull-base v B′ → Dom B′ → (β β′ : Tr⁺ j) → N j (proj₁ β) (proj₁ β′)
  → N j (proj₁ (ψ ℓ o r B j w β (proj₁ (Ωt ℓ))))
        (proj₁ (ψ ℓ′ o′ r′ B′ j w′ β′ (proj₁ (Ωt ℓ′))))
climbₒ v fit ν o′ _ refl r r′ B B′ hB dB β β′ hβ = climb v fit ν o′ r r′ B B′ hB dB β β′ hβ
```
