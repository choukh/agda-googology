# 折叠对字面路径与底的单调：一般形式
不读记号；编译定理 `climb`：ℓ ⊑ ℓ′ 是字面路径、源层 ℓ 无 Ω 形状，源底按 `Le` 不高于沿路径拉回的目标底，目标底不低于标准底（`Dom`），起点按 `Le`，则两个 Ω 树的折叠按 `Le` 有序；层号、路径、两侧的底与表、目标层都是变量。
限制：目标路径取 `inu` 形（`Fit`），路径经 Ω 形状的结点时只经孩子 `zero`；源层有 Ω 形状时不涉及（`YiVRRel.β-not`）。不否定什么。
来源：同层一步 `YiLXFold.fl`；后继层一步照 `YiOGRelPeel.peel-from`；ℕ 极限层取第 n 个累计前缀，底的更新由 `inflA` 吸收；Ω 形状层取第一分支。实例在 `YiLXOne`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLXClimb where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp)
open import OCF.Lean.YiVRRel
open import OCF.Lean.YiVRFold using (_⊴_; Pr; node≼ʳ)
open import OCF.Lean.YiKAMono using (le◃)
open import OCF.Lean.YiOGRelPeel using (right-add)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono)
open import OCF.Lean.YiOFPath using (pull-base)
open import OCF.Lean.YiTYPath using (pull-ok)
open import OCF.Lean.YiMTTab using (rbᶻ)
import OCF.Lean.YiLXFold as F
```

## 前提

`Fit v w w′`: 目标路径在路径 v 经过的每个结点取 `inu`, 到源层时与源路径相同; v 经过 Ω 形状的结点时只经孩子 `zero`. `Dom B`: 每个非 `self` 分量不低于标准 Ω 树 (相等或第一位置).

```agda
data Fit {j : L} : ∀ {ℓ ℓ′} → ℓ ⊑ ℓ′ → j ≤ ℓ → j ≤ ℓ′ → Set where
  fself : ∀ {ℓ} {w : j ≤ ℓ} → Fit self w w
  fS  : ∀ {ℓ} {h : ⊤ → L} {v : ℓ ⊑ h tt} {w w′} → Fit v w w′ → Fit {ℓ′ = nd sS h} (inc tt v) w (inu (λ _ → w′))
  fSu : ∀ {ℓ} {h : ⊤ → L} {vs : (c : ⊤) → ℓ ⊑ h c} {w w′} → Fit (vs tt) w w′ → Fit {ℓ′ = nd sS h} (inu vs) w (inu (λ _ → w′))
  fL  : ∀ {ℓ} {g : ℕ → L} {n} {v : ℓ ⊑ g n} {w} {ws : (k : ℕ) → j ≤ g k} → Fit v w (ws n) → Fit (inc n v) w (inu ws)
  fLu : ∀ {ℓ} {g : ℕ → L} {vs : (k : ℕ) → ℓ ⊑ g k} {w} {ws : (k : ℕ) → j ≤ g k} → Fit (vs zero) w (ws zero) → Fit (inu vs) w (inu ws)
  fΩ  : ∀ {ℓ k} {h : Tr k → L} {v : ℓ ⊑ h zero} {w} {ws : (c : Tr k) → j ≤ h c} → Fit v w (ws zero) → Fit {ℓ′ = nd (sΩ k) h} (inc zero v) w (inu ws)
  fΩu : ∀ {ℓ k} {h : Tr k → L} {vs : (c : Tr k) → ℓ ⊑ h c} {w} {ws : (c : Tr k) → j ≤ h c} → Fit (vs zero) w (ws zero) → Fit {ℓ′ = nd (sΩ k) h} (inu vs) w (inu ws)

infix 4 _⊴◃_
_⊴◃_ : ∀ {i} → Tr i → Tr i → Set
_⊴◃_ {i} x y = (x ≡ y) ⊎ (i ⊢ x ◃ y)

⊴◃-◃ : ∀ {i} {x y z : Tr i} → x ⊴◃ y → i ⊢ y ◃ z → x ⊴◃ z
⊴◃-◃ {i} {z = z} (inj₁ e) d = inj₂ (subst (λ t → i ⊢ t ◃ z) (sym e) d)
⊴◃-◃ (inj₂ e) d = inj₂ (◃t e d)

Dom : ∀ {ℓ} → Base ℓ → Set
Dom {ℓ} B = (i : L) (u : i ≤ ℓ) → Pr u → proj₁ (Ωt i) ⊴◃ proj₁ (B i u)

anchor : (a : L) (b : Tr⁺ a) → proj₁ (Ωt a) ⊴◃ proj₁ b → a ⊢ proj₁ (Ωt a) ◃ suc (proj₁ (next⁺ b))
anchor a b (inj₁ e) = subst (λ t → a ⊢ t ◃ suc (proj₁ (next⁺ b))) (sym e) (◃t (◃l 0) ◃s)
anchor a b (inj₂ d) = ◃t d (◃t (◃l 0) ◃s)

pull-ext : ∀ {ℓ ℓ′} (v : ℓ ⊑ ℓ′) {B : Base ℓ} {B₁ B₂ : Base ℓ′}
  → ((i : L) (u : i ≤ ℓ′) → Pr u → ∀ {a} → Le i a (proj₁ (B₁ i u)) → Le i a (proj₁ (B₂ i u)))
  → B ⊴ pull-base v B₁ → B ⊴ pull-base v B₂
pull-ext self H hB i u q = H i u q (hB i u q)
pull-ext (inc c v) {B} {B₁} {B₂} H hB = pull-ext v {B} {λ i u → B₁ i (inc c u)} {λ i u → B₂ i (inc c u)} (λ i u _ → H i (inc c u) tt) hB
pull-ext {ℓ′ = nd s h} (inu vs) {B} {B₁} {B₂} H hB =
  pull-ext (vs (c₀ s)) {B} {λ i u → B₁ i (inc (c₀ s) u)} {λ i u → B₂ i (inc (c₀ s) u)} (λ i u _ → H i (inc (c₀ s) u) tt) hB

cum-pos : ∀ {ℓ} (F : ℕ → Tr⁺ ℓ) (n : ℕ) → ℓ ⊢ zero ◃ cum (λ k → proj₁ (F k)) n
cum-pos F zero    = proj₂ (F zero)
cum-pos F (suc n) = ◃t (cum-pos F n) (+-mono _ (proj₂ (F (suc n))))
```

## 两种一步

后继层: 孩子层上的折叠接到 Ω 树折叠的第 1 个累计支 (同一底, 第一位置). ℕ 极限层的一步直接在 `climb` 里取第 n 个累计前缀. Ω 形状层的一步取结点的第一分支 (孩子 `zero`), 保留与否都用 `node≼ʳ`.

```agda
peelS : (a : L) (o : Ok (nd sS (λ _ → a))) (r : Rb (nd sS (λ _ → a))) (bs : Base (nd sS (λ _ → a)))
  (j : L) (w : j ≤ a) (β : Tr⁺ j) {x : Tr j}
  → Le j x (proj₁ (ψ a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β (proj₁ (Ωt a))))
  → a ⊢ proj₁ (Ωt a) ◃ suc (proj₁ (next⁺ (bs a (inc tt self))))
  → Le j x (proj₁ (ψ (nd sS (λ _ → a)) o r bs j (inu (λ _ → w)) β (proj₁ (Ωt (nd sS (λ _ → a))))))
peelS a o r bs j w β e d = ≼l 1 (right-add
  (le◃ e (mono a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β d))
  (proj₁ (ψ a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β (suc zero))))
```

## 定理

```agda
climb : ∀ {j ℓ ℓ′} (v : ℓ ⊑ ℓ′) {w : j ≤ ℓ} {w′ : j ≤ ℓ′} → Fit v w w′ → NoΩ ℓ
  → (o′ : Ok ℓ′) (r : Rb ℓ) (r′ : Rb ℓ′) (B : Base ℓ) (B′ : Base ℓ′)
  → B ⊴ pull-base v B′ → Dom B′ → (β β′ : Tr⁺ j) → Le j (proj₁ β) (proj₁ β′)
  → Le j (proj₁ (ψ ℓ (pull-ok v o′) r B j w β (proj₁ (Ωt ℓ))))
         (proj₁ (ψ ℓ′ o′ r′ B′ j w′ β′ (proj₁ (Ωt ℓ′))))
climb {j} {ℓ} _ {w} fself ν o′ r r′ B B′ hB dB β β′ hβ =
  F.fl ℓ ν o′ r r′ B B′ hB j w β β′ hβ (Ωt≼ ℓ ν)
climb {j} _ (fS {h = h} {v = v} {w′ = w′} fit) ν o′ r r′ B B′ hB dB β β′ hβ =
  peelS (h tt) o′ r′ B′ j w′ β′
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
    (pull-ext v {B} {λ i u → B′ i (inc (suc k) u)} {Bk} (λ i u _ d → F.inflA (nd sL g) o′ r′ B′ i (inc (suc k) u) (B′ i (inc (suc k) u)) Pk d) hB)
    (λ i u _ → ⊴◃-◃ (dB i (inc (suc k) u) tt)
      (mono (nd sL g) o′ r′ B′ i (inc (suc k) u) (B′ i (inc (suc k) u)) (cum-pos Fk k)))
    β βk (F.inflA (nd sL g) o′ r′ B′ j (inu ws) β′ Pk hβ))
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
```

源层的合法性证据作变量, 配一条等式 (实例里由 `refl` 给出), 免得检查器比较两个写法不同的证据时展开折叠.

```agda
climbₒ : ∀ {j ℓ ℓ′} (v : ℓ ⊑ ℓ′) {w : j ≤ ℓ} {w′ : j ≤ ℓ′} → Fit v w w′ → NoΩ ℓ
  → (o′ : Ok ℓ′) (o : Ok ℓ) → o ≡ pull-ok v o′ → (r : Rb ℓ) (r′ : Rb ℓ′) (B : Base ℓ) (B′ : Base ℓ′)
  → B ⊴ pull-base v B′ → Dom B′ → (β β′ : Tr⁺ j) → Le j (proj₁ β) (proj₁ β′)
  → Le j (proj₁ (ψ ℓ o r B j w β (proj₁ (Ωt ℓ))))
         (proj₁ (ψ ℓ′ o′ r′ B′ j w′ β′ (proj₁ (Ωt ℓ′))))
climbₒ v fit ν o′ _ refl r r′ B B′ hB dB β β′ hβ = climb v fit ν o′ r r′ B B′ hB dB β β′ hβ
```

例: 第 0 层沿塔各项的孩子 `zero` 一路上去 (每一步都经 Ω 形状的结点).

```agda
tz : (n : ℕ) → zero ⊑ tw n
tz zero    = self
tz (suc n) = inc zero (tz n)

fit-tz : (n : ℕ) → Fit (tz n) self (z≤ (tw n))
fit-tz zero    = fself
fit-tz (suc n) = fΩ (fit-tz n)

tower-low : (n : ℕ) → Le zero (proj₁ (ψ zero tt tt (B₀ zero) zero self (Ωt zero) (proj₁ (Ωt zero))))
  (proj₁ (ψ (tw n) (Ok-tw n) (rbᶻ (tw n)) (B₀ (tw n)) zero (z≤ (tw n)) (Ωt zero) (proj₁ (Ωt (tw n)))))
tower-low n = climbₒ (tz n) (fit-tz n) tt (Ok-tw n) tt refl tt (rbᶻ (tw n)) (B₀ zero) (B₀ (tw n))
  (λ { i self () }) (λ i u _ → inj₁ refl) (Ωt zero) (Ωt zero) (refl₀ _)
```
