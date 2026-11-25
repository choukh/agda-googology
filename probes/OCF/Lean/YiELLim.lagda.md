# 一般的 `LimAt`: ω-共尾的项的基本列在标准形里共尾

> 验收文件 (读记号, 记号一侧)。编译定理, 无前提: `limAt : ∀ u → cof u ≡ cω → LimAt u` (`YiGLFrame.LimAt`), 以及带 "不高于" 的加强式 `lim-gen`; 不要求 u 是标准形, 只要求被比较的 u′ 是标准形。
> 做了什么: 规则 6 一支用分量引理 `compA` 与 γ 链的界 `Chain.cofin` (对 u′ 的结构递归); Ω-共尾一侧的同类陈述 `cofinΩ` (给出见证 η)。实例 ω·2, ε₀。
> 来源: 共尾视图 `Vω`, `VΩ`, `fω`, `fΩ`, `γ` 与 `fω-eq` 取自 `EboLeanView`; `InG`, `GB`, `noG-le`, `G-mono` 取自 `EboLeanBase`。证明是本文新写的, 没有搬。不否定什么。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiELLim where
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; n≤1+n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; replicate; length)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Align.EboLeanDef
open import OCF.Align.EBO using (pred-suc; <-sucT)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLean3Base using (nf-suc)
open import OCF.Align.EboLeanView
open import OCF.Lean.YiGLFrame using (LimAt)
```

## 分量引理

b 的共尾度是 Ω_{ν+1}。标准形 d 低于 b, 且 d 里经不低于 ν 的下标可达的参数都低于 Z, 则 d 低于 b[ψ_ν(Z)]。对视图递归; 下标低于 ν 的头项里没有这样的参数 (`noG-le`)。

```agda
compA : ∀ {b ν} (w : VΩ b ν) {d Z} → NF d → d <ᵀ b → GB ν d Z → d <ᵀ fΩ w (ψ ν Z ∷ [])
compA (ωs w) nf []< g = []<
compA (ωs w) nf (hd< p) g = hd< p
compA (ωs w) nf (tl< p) g = tl< (compA w (nf-tl nf) p (λ h → g (gtl h)))
compA (ωr e) nf []< g = []<
compA (ωr {u} e) nf (hd< (lv< p)) g with <sucT (pred u) (subst (_ <ᵀ_) (sym (pred-suc u e)) p)
... | inj₁ r = hd< (lv< r)
... | inj₂ refl = hd< (ar< (g (gp (gh (inj₂ refl)))))
compA (ωl e v) nf []< g = []<
compA (ωl {μ} e v) {d = ψ p q ∷ ys} nf (hd< (lv< r)) g with dec≤ μ p
... | inj₁ l = hd< (lv< (compA v (nfp-u (nf-hd nf)) r (λ h → g (gp (gw l h)))))
... | inj₂ s = hd< (lv< (compA v (nfp-u (nf-hd nf)) r (λ h → ⊥-elim (noG-le (nfp-u (nf-hd nf)) (inj₁ s) h))))
compA (ωp be pen v) nf []< g = []<
compA (ωp be pen v) nf (hd< (lv< r)) g = hd< (lv< r)
compA (ωp {u} {μ} be pen v) nf (hd< (ar< r)) g =
  hd< (ar< (compA v (nfp-a (nf-hd nf)) r (λ h → g (gp (gc (inj₁ (<-≤ (<-sucT μ) (Pen→≤ (sucT μ) u pen))) h)))))
```

## γ 链的界

`bndT`: d 的那些参数都低于 b 时, 有一个 m 使它们都低于 b[γ_m]; 对 d 结构递归, 每个参数用一次 `compA`。`cofin`: 标准形 ψ_A(q) (A 不高于 ν) 的参数 q 低于 b 时, q 低于某个 b[γ_m]。

```agda
module Chain {b ν} (w : VΩ b ν) where
  V : ℕ → T
  V m = fΩ w (γ w m)

  V-le : ∀ {m n} → m ≤ n → V m ≤ᵀ V n
  V-le {n = n} z≤n = val-le0 w n
  V-le (s≤s l) with V-le l
  ... | inj₁ p = inj₁ (fΩ-mono w (hd< (ar< p)))
  ... | inj₂ e = inj₂ (cong (λ z → fΩ w (ψ ν z ∷ [])) e)

  bndT : ∀ d → NF d → GB ν d b → Σ ℕ λ m → GB ν d (V m)
  bndP : ∀ p q → NFP (ψ p q) → (∀ {z} → InGP ν z (ψ p q) → z <ᵀ b)
    → Σ ℕ λ m → ∀ {z} → InGP ν z (ψ p q) → z <ᵀ V m
  bndT [] nf g = 0 , λ ()
  bndT (ψ p q ∷ xs) nf g with bndP p q (nf-hd nf) (λ h → g (gp h)) | bndT xs (nf-tl nf) (λ h → g (gtl h))
  ... | m₁ , b₁ | m₂ , b₂ = m₁ ⊔ m₂ , λ
    { (gp h) → <-≤ (b₁ h) (V-le (m≤m⊔n m₁ m₂))
    ; (gtl h) → <-≤ (b₂ h) (V-le (m≤n⊔m m₁ m₂)) }
  bndP p q (nψ np nq _) g with dec≤ ν p
  ... | inj₂ s = 0 , λ
    { (gh l) → ⊥-elim (≤¬> l s) ; (gw l _) → ⊥-elim (≤¬> l s) ; (gc l _) → ⊥-elim (≤¬> l s) }
  ... | inj₁ l with bndT p np (λ h → g (gw l h)) | bndT q nq (λ h → g (gc l h))
  ...   | m₁ , b₁ | m₂ , b₂ = suc (m₁ ⊔ m₂) , λ
    { (gh _) → <-≤ (compA w nq (g (gh l)) b₂) (V-le (s≤s (m≤n⊔m m₁ m₂)))
    ; (gw _ h) → <-≤ (b₁ h) (V-le (≤-trans (m≤m⊔n m₁ m₂) (n≤1+n _)))
    ; (gc _ h) → <-≤ (b₂ h) (V-le (≤-trans (m≤n⊔m m₁ m₂) (n≤1+n _))) }

  cofin : ∀ {q} → NF q → q <ᵀ b → GB ν q q → Σ ℕ λ m → q <ᵀ V m
  cofin {q} nq r g with bndT q nq (λ h → <ᵀ-trans (g h) r)
  ... | m , bm = suc m , compA w nq r bm
```

## 主定理

对 ω-共尾视图递归。规则 4 用 "标准形的和不超过首项的有限倍" (`rep-big`), 规则 6 用 `cofin`。`tl≤′`, `arg≤′` 带等式参数是因为不开 K。

```agda
LimAt⁺ : T → Set
LimAt⁺ u = ∀ {u′} → NF u′ → u′ <ᵀ u → (∀ n → fsn u n ≤ᵀ u′) → ⊥

hd≤ : ∀ {x y : PT} {a b} → (x ∷ a) ≤ᵀ (y ∷ b) → x ≤ᴾ y
hd≤ (inj₁ (hd< p)) = inj₁ p
hd≤ (inj₁ (tl< _)) = inj₂ refl
hd≤ (inj₂ e) = inj₂ (∷-injectiveˡ e)

tl≤′ : ∀ {x y : PT} {a b} → x ≡ y → (x ∷ a) ≤ᵀ (y ∷ b) → a ≤ᵀ b
tl≤′ e (inj₁ (hd< p)) = ⊥-elim (<ᴾ-irrefl (subst (_<ᴾ _) e p))
tl≤′ e (inj₁ (tl< p)) = inj₁ p
tl≤′ e (inj₂ e′) = inj₂ (∷-injectiveʳ e′)

tl≤ : ∀ {x : PT} {a b} → (x ∷ a) ≤ᵀ (x ∷ b) → a ≤ᵀ b
tl≤ = tl≤′ refl

ψ-inj₂ : ∀ {u a v b} → ψ u a ≡ ψ v b → a ≡ b
ψ-inj₂ refl = refl

arg≤′ : ∀ {A A′ a q ys} → A ≡ A′ → (ψ A a ∷ []) ≤ᵀ (ψ A′ q ∷ ys) → a ≤ᵀ q
arg≤′ e (inj₁ (hd< (lv< s))) = ⊥-elim (<ᵀ-irrefl (subst (_<ᵀ _) e s))
arg≤′ e (inj₁ (hd< (ar< s))) = inj₁ s
arg≤′ e (inj₁ (tl< _)) = inj₂ refl
arg≤′ e (inj₂ e′) = inj₂ (ψ-inj₂ (∷-injectiveˡ e′))

arg≤ : ∀ {A a q ys} → (ψ A a ∷ []) ≤ᵀ (ψ A q ∷ ys) → a ≤ᵀ q
arg≤ = arg≤′ refl

rep-big : ∀ {x} t → NF t → HdLe x t → t <ᵀ replicate (suc (length t)) x
rep-big [] nf h = []<
rep-big (y ∷ ys) nf (inj₁ p) = hd< p
rep-big (y ∷ ys) nf (inj₂ refl) = tl< (rep-big ys (nf-tl nf) (nf-le nf))

nil≤ : ∀ {x : PT} {a} → (x ∷ a) ≤ᵀ [] → ⊥
nil≤ (inj₁ ())
nil≤ (inj₂ ())

limω : ∀ {u} (v : Vω u) {u′} → NF u′ → u′ <ᵀ u → (∀ n → fω v n ≤ᵀ u′) → ⊥
limω (ws v) nf []< big = nil≤ (big 0)
limω (ws v) nf (hd< p) big = ≤¬> (big 0) (hd< p)
limω (ws v) nf (tl< p) big = limω v (nf-tl nf) p (λ n → tl≤ (big n))
limω (wl e v) nf []< big = nil≤ (big 0)
limω (wl e v) nf (hd< (lv< p)) big = limω v (nfp-u (nf-hd nf)) p (λ n → sub≤ (hd≤ (big n)))
limω (w4 e) nf []< big = nil≤ (big 1)
limω (w4 e) nf (hd< (lv< p)) big = ≤¬> (big 1) (hd< (lv< p))
limω (w4 {b} e) {u′ = ψ _ q ∷ ys} nf (hd< (ar< r)) big with <sucT (pred b) (subst (q <ᵀ_) (sym (pred-suc b e)) r)
... | inj₁ s = ≤¬> (big 1) (hd< (ar< s))
... | inj₂ refl = ≤¬> (big (suc (suc (length ys)))) (tl< (rep-big ys (nf-tl nf) (nf-le nf)))
limω (w5 e v) nf []< big = nil≤ (big 0)
limω (w5 e v) nf (hd< (lv< p)) big = ≤¬> (big 0) (hd< (lv< p))
limω (w5 e v) nf (hd< (ar< r)) big = limω v (nfp-a (nf-hd nf)) r (λ n → arg≤ (big n))
limω (w6 be g w) nf []< big = nil≤ (big 0)
limω (w6 be g w) nf (hd< (lv< p)) big = ≤¬> (big 0) (hd< (lv< p))
limω (w6 {u = A} {ν} be g w) nf (hd< (ar< r)) big
  with Chain.cofin w (nfp-a (nf-hd nf)) r (λ h → nfp-g (nf-hd nf) (G-mono (gt→≤ ν A g) h))
... | m , lt′ = ≤¬> (arg≤ (big m)) lt′

lim-gen : ∀ u → cof u ≡ cω → LimAt⁺ u
lim-gen u e nf lt′ big = limω (vω u e) nf lt′ (λ n → subst (_≤ᵀ _) (fω-eq (vω u e) n) (big n))

limAt : ∀ u → cof u ≡ cω → LimAt u
limAt u e nf lt′ big = lim-gen u e nf lt′ (λ n → inj₁ (big n))
```

## Ω-共尾一侧与实例

`cofinΩ`: 低于 a 的标准形 c 低于某个 a[η], η 是标准形且低于 Ω_{κ+1} (见证取 c 的分量加一)。

```agda
suc<Ωs : ∀ {y μ} → y <ᵀ Ωs μ → sucT y <ᵀ Ωs μ
suc<Ωs {μ = μ} []< = hd< (lv< ([]<sucT′ μ))
  where
  []<sucT′ : ∀ a → [] <ᵀ sucT a
  []<sucT′ [] = []<
  []<sucT′ (x ∷ xs) = []<
suc<Ωs (hd< p) = hd< p

cofinΩ : ∀ {a κ} (v : VΩ a κ) {c} → NF c → c <ᵀ a → Σ T λ η → NF η × (η <ᵀ Ωs κ) × (c <ᵀ fΩ v η)
cofinΩ (ωs v) nf []< = [] , n[] , []< , []<
cofinΩ (ωs v) nf (hd< p) = [] , n[] , []< , hd< p
cofinΩ (ωs v) nf (tl< p) with cofinΩ v (nf-tl nf) p
... | η , nη , lt′ , q = η , nη , lt′ , tl< q
cofinΩ (ωr {u} e) {c} nf p = sucT c , nf-suc nf
  , suc<Ωs (subst (c <ᵀ_) (sym (reg-eq e)) p) , <-sucT c
cofinΩ (ωl e v) nf []< = [] , n[] , []< , []<
cofinΩ (ωl e v) nf (hd< (lv< p)) with cofinΩ v (nfp-u (nf-hd nf)) p
... | η , nη , lt′ , q = η , nη , lt′ , hd< (lv< q)
cofinΩ (ωp be pen v) nf []< = [] , n[] , []< , []<
cofinΩ (ωp be pen v) nf (hd< (lv< r)) = [] , n[] , []< , hd< (lv< r)
cofinΩ (ωp be pen v) nf (hd< (ar< r)) with cofinΩ v (nfp-a (nf-hd nf)) r
... | η , nη , lt′ , q = η , nη , lt′ , hd< (ar< q)

ω2 ε0 : T
ω2 = ψ [] (𝟏 ∷ []) ∷ ψ [] (𝟏 ∷ []) ∷ []
ε0 = ψ [] (ψ (𝟏 ∷ []) [] ∷ []) ∷ []
t-ω2 : LimAt ω2
t-ω2 = limAt ω2 refl
t-ε0 : LimAt ε0
t-ε0 = limAt ε0 refl
```
