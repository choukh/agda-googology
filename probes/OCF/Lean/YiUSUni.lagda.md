# 统一阈值在 Ω₂ 区间与 Ω₁ 区间不能闭合
验收文件（读记号，陈述只涉及记号的项）；编译否定：`no-uniform₂`（形如 ψ₂(a) 的阈值不能同时满足 ℕ 极限、Ω₁ 结点、Ω₂ 结点三行的闭合要求）、`no-uniform₁`（ψ₁(a) 对 ℕ 极限、Ω₁ 结点）。三条要求各自可满足：`reqL-Ω₂`、`req₀-Ω₂`、`req₁-θ₁`。
否定的是 `YiTFBound` 式工具（结点一行只用类内同一个阈值）在含这三种结点的树类上的闭合引理，不否定 `Refute`，也不涉及值。入口 `no-uniform₂`；第 1 层的阈值引理（`mLΩ₂`、`LΩ₂`）供 `YiUSBound.bL1` 用。
来源：`L2Ω₂`、`mLΩ₂`、`LΩ₂` 照 `YiTFBound.L2Ω`、`mLΩ`、`LΩ` 改阈值；`lv≤`、`ar≤` 抄自 `YiKTSlot`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUSUni where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<; hd<; tl<; lv<; ar<; lt; eq; gt; c0; c1; cω; cΩ)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; _≤ᴾ_; tri; <ᵀ-irrefl; <ᵀ-trans; ≤-<; Pen→≤)
open import OCF.Align.EboLean3Base using (one≤ᴾ)
open import OCF.Align.EBO using (pred-suc; pred-<; natT<Ωs)
open import OCF.Align.EboLeanView using (Vω; ws; wl; w4; w5; w6; vω; fω; fω-eq; VΩ; ωs; ωr; ωl; ωp; vΩ; fΩ; fΩ-eq; fΩ-pos; γ; γ<; reg-eq)
open import OCF.Lean.YiLLLeafNeg using (fω-big; fΩ-big; positive)
```

## 闭合要求与基本列的下降

`ReqL θ`、`Req₀ θ`、`Req₁ θ` 是对推导归纳时 ℕ 极限一行、Ω₁ 结点一行、Ω₂ 结点（读法共尾 Ω₂）一行在 t = θ 处要用的引理，量化对一切项，不看树类。下降对一切项成立，不要标准形。

```agda
ReqL Req₀ Req₁ : E.T → Set
ReqL θ = ∀ t → E.cof t ≡ cω → (∀ n → E.fsn t n <ᵀ θ) → t <ᵀ θ
Req₀ θ = ∀ t → E.cof t ≡ cΩ [] → (∀ η → η <ᵀ E.Ωs [] → E.fsT t η <ᵀ θ) → t <ᵀ θ
Req₁ θ = ∀ t → E.cof t ≡ cΩ (E.𝟏 ∷ []) → (∀ η → η <ᵀ E.Ωs (E.𝟏 ∷ []) → E.fsT t η <ᵀ θ) → t <ᵀ θ

fΩ< : ∀ {b ν} (w : VΩ b ν) {η} → η <ᵀ E.Ωs ν → fΩ w η <ᵀ b
fΩ< (ωs v) p = tl< (fΩ< v p)
fΩ< (ωr {u = u} e) {η} p = subst (η <ᵀ_) (reg-eq e) p
fΩ< (ωl e v) p = hd< (lv< (fΩ< v p))
fΩ< (ωp e pen v) p = hd< (ar< (fΩ< v p))

fω< : ∀ {t} (v : Vω t) n → fω v n <ᵀ t
fω< (ws v) n = tl< (fω< v n)
fω< (wl e v) n = hd< (lv< (fω< v n))
fω< (w4 e) zero = []<
fω< (w4 {b = b} e) (suc n) = hd< (ar< (pred-< b e))
fω< (w5 e v) n = hd< (ar< (fω< v n))
fω< (w6 e g w) n = hd< (ar< (fΩ< w (γ< w n)))

fsn< : ∀ t → E.cof t ≡ cω → ∀ n → E.fsn t n <ᵀ t
fsn< t e n = subst (_<ᵀ t) (sym (fω-eq (vω t e) n)) (fω< (vω t e) n)

fsT< : ∀ t {μ} → E.cof t ≡ cΩ μ → ∀ {η} → η <ᵀ E.Ωs μ → E.fsT t η <ᵀ t
fsT< t e p = subst (_<ᵀ t) (sym (fΩ-eq (vΩ t e) _)) (fΩ< (vΩ t e) p)
```

## 区间里主项的共尾度

ψ₂(a) 的共尾度只有 ω、Ω₁、Ω₂ 三种（`band₂`），ψ₁(a) 只有 ω、Ω₁（`band₁`）；不要标准形，下标字面是 2 或 1 即可。

```agda
no-below𝟏 : ∀ {x} → x E.<ᴾ E.𝟏 → ⊥
no-below𝟏 (lv< ())
no-below𝟏 (ar< ())

small₂ : ∀ μ → E.sucT μ ≤ᵀ E.natT 2 → (μ ≡ []) ⊎ (μ ≡ E.𝟏 ∷ [])
small₂ [] le = inj₁ refl
small₂ (x ∷ xs) (inj₁ (hd< p)) = ⊥-elim (no-below𝟏 p)
small₂ (_ ∷ []) (inj₁ (tl< q)) = ⊥-elim (<ᵀ-irrefl q)
small₂ (_ ∷ y ∷ ys) (inj₁ (tl< (hd< p))) = ⊥-elim (no-below𝟏 p)
small₂ (_ ∷ y ∷ ys) (inj₁ (tl< (tl< ())))
small₂ (x ∷ xs) (inj₂ e) = inj₂ (go x xs e)
  where
  go : ∀ x xs → (x ∷ (xs ++ E.𝟏 ∷ [])) ≡ E.𝟏 ∷ E.𝟏 ∷ [] → (x ∷ xs) ≡ E.𝟏 ∷ []
  go x [] refl = refl
  go x (_ ∷ []) ()
  go x (_ ∷ _ ∷ _) ()

small₁ : ∀ μ → E.sucT μ ≤ᵀ E.natT 1 → μ ≡ []
small₁ [] le = refl
small₁ (x ∷ xs) (inj₁ (hd< p)) = ⊥-elim (no-below𝟏 p)
small₁ (_ ∷ []) (inj₁ (tl< ()))
small₁ (_ ∷ _ ∷ _) (inj₁ (tl< ()))
small₁ (_ ∷ []) (inj₂ ())
small₁ (_ ∷ _ ∷ _) (inj₂ ())

Band₂ Band₁ : E.Cof → Set
Band₂ c = (c ≡ cω) ⊎ (c ≡ cΩ []) ⊎ (c ≡ cΩ (E.𝟏 ∷ []))
Band₁ c = (c ≡ cω) ⊎ (c ≡ cΩ [])

band₂Ω : ∀ μ m → E.cmpᵀ (E.sucT μ) (E.natT 2) ≡ m → Band₂ (E.cofψ₊ (E.natT 2) μ m)
band₂Ω μ lt e with small₂ μ (Pen→≤ (E.sucT μ) (E.natT 2) (inj₁ e))
... | inj₁ refl = inj₂ (inj₁ refl)
... | inj₂ refl = inj₂ (inj₂ refl)
band₂Ω μ eq e with small₂ μ (Pen→≤ (E.sucT μ) (E.natT 2) (inj₂ e))
... | inj₁ refl = inj₂ (inj₁ refl)
... | inj₂ refl = inj₂ (inj₂ refl)
band₂Ω μ gt e = inj₁ refl

band₂A : ∀ c → Band₂ (E.cofA (E.natT 2) c)
band₂A c0 = inj₁ refl
band₂A c1 = inj₁ refl
band₂A cω = inj₁ refl
band₂A (cΩ μ) = band₂Ω μ (E.cmpᵀ (E.sucT μ) (E.natT 2)) refl

band₂ : ∀ a → Band₂ (E.cof (E.ψ (E.natT 2) a ∷ []))
band₂ [] = inj₂ (inj₂ refl)
band₂ (y ∷ ys) = band₂A (E.cof (y ∷ ys))

band₁Ω : ∀ μ m → E.cmpᵀ (E.sucT μ) (E.natT 1) ≡ m → Band₁ (E.cofψ₊ (E.natT 1) μ m)
band₁Ω μ lt e with small₁ μ (Pen→≤ (E.sucT μ) (E.natT 1) (inj₁ e))
... | refl = inj₂ refl
band₁Ω μ eq e with small₁ μ (Pen→≤ (E.sucT μ) (E.natT 1) (inj₂ e))
... | refl = inj₂ refl
band₁Ω μ gt e = inj₁ refl

band₁A : ∀ c → Band₁ (E.cofA (E.natT 1) c)
band₁A c0 = inj₁ refl
band₁A c1 = inj₁ refl
band₁A cω = inj₁ refl
band₁A (cΩ μ) = band₁Ω μ (E.cmpᵀ (E.sucT μ) (E.natT 1)) refl

band₁ : ∀ a → Band₁ (E.cof (E.ψ (E.natT 1) a ∷ []))
band₁ [] = inj₂ refl
band₁ (y ∷ ys) = band₁A (E.cof (y ∷ ys))
```

## 否定

阈值自己就是反例：共尾度落在哪一行，那一行的要求在 t = θ 处推出 θ < θ。

```agda
no-uniform₂ : ∀ a → ReqL (E.ψ (E.natT 2) a ∷ []) → Req₀ (E.ψ (E.natT 2) a ∷ []) → Req₁ (E.ψ (E.natT 2) a ∷ []) → ⊥
no-uniform₂ a rl r0 r1 with band₂ a
... | inj₁ e = <ᵀ-irrefl (rl _ e (fsn< _ e))
... | inj₂ (inj₁ e) = <ᵀ-irrefl (r0 _ e (λ η p → fsT< _ e p))
... | inj₂ (inj₂ e) = <ᵀ-irrefl (r1 _ e (λ η p → fsT< _ e p))

no-uniform₁ : ∀ a → ReqL (E.ψ (E.natT 1) a ∷ []) → Req₀ (E.ψ (E.natT 1) a ∷ []) → ⊥
no-uniform₁ a rl r0 with band₁ a
... | inj₁ e = <ᵀ-irrefl (rl _ e (fsn< _ e))
... | inj₂ e = <ᵀ-irrefl (r0 _ e (λ η p → fsT< _ e p))
```

## 前提各自可满足

Ω₂（= ψ₂(0)，在区间里）满足 `ReqL`、`Req₀`；ψ₂(Ω₁) 满足 `Req₁`。阈值引理也是 `YiUSBound.bL1` 用的。

```agda
Ω₁ Ω₂ θ₁ : E.T
Ω₁ = E.ψ (E.𝟏 ∷ []) [] ∷ []
Ω₂ = E.ψ (E.natT 2) [] ∷ []
θ₁ = E.ψ (E.natT 2) Ω₁ ∷ []

lv≤ : ∀ {u v} → u ≤ᵀ v → (E.ψ u [] ∷ []) ≤ᵀ (E.ψ v [] ∷ [])
lv≤ (inj₁ p) = inj₁ (hd< (lv< p))
lv≤ (inj₂ refl) = inj₂ refl

ar≤ : ∀ u {a b} → a ≤ᵀ b → (E.ψ u a ∷ []) ≤ᵀ (E.ψ u b ∷ [])
ar≤ u (inj₁ p) = inj₁ (hd< (ar< p))
ar≤ u (inj₂ refl) = inj₂ refl

c1≢cω : c1 ≡ cω → ⊥
c1≢cω ()

c0≢c1 : c0 ≡ c1 → ⊥
c0≢c1 ()

c0≢cω : c0 ≡ cω → ⊥
c0≢cω ()

c0≢cΩ : ∀ {μ} → c0 ≡ cΩ μ → ⊥
c0≢cΩ ()

cΩ≢cω : ∀ {μ} → cΩ μ ≡ cω → ⊥
cΩ≢cω ()

ne2 : ∀ {s} (v : Vω s) → [] <ᵀ fω v 2
ne2 v = positive (fω-big v)

sucΩ₂ : ∀ {x} → x <ᵀ Ω₂ → E.sucT x <ᵀ Ω₂
sucΩ₂ {x = []} []< = hd< (lv< []<)
sucΩ₂ (hd< p) = hd< p

++Ω₂ : ∀ {a b} → a <ᵀ Ω₂ → b <ᵀ Ω₂ → (a ++ b) <ᵀ Ω₂
++Ω₂ {a = []} p q = q
++Ω₂ (hd< p) q = hd< p

Ω₁<Ω₂ : Ω₁ <ᵀ Ω₂
Ω₁<Ω₂ = hd< (lv< (tl< []<))

two≤′ : ∀ y ys → E.𝟏 ≤ᴾ y → E.natT 2 ≤ᵀ (E.𝟏 ∷ y ∷ ys)
two≤′ y ys (inj₁ p) = inj₁ (tl< (hd< p))
two≤′ _ [] (inj₂ refl) = inj₂ refl
two≤′ _ (_ ∷ _) (inj₂ refl) = inj₁ (tl< (tl< []<))

two≤ : ∀ {x} → E.natT 1 <ᵀ x → E.natT 2 ≤ᵀ x
two≤ (hd< p) = inj₁ (hd< p)
two≤ {x = _ ∷ y ∷ ys} (tl< []<) = two≤′ y ys (one≤ᴾ y)

L2Ω₂ : ∀ {s} (v : Vω s) → Ω₂ ≤ᵀ s → Ω₂ ≤ᵀ fω v 2
L2Ω₂ (ws v) (inj₁ (hd< p)) = inj₁ (hd< p)
L2Ω₂ (ws v) (inj₁ (tl< q)) = inj₁ (tl< (ne2 v))
L2Ω₂ (wl e v) (inj₁ (hd< (lv< p))) = lv≤ (two≤ (fω-big v))
L2Ω₂ (wl e v) (inj₁ (hd< (ar< ())))
L2Ω₂ (wl e v) (inj₁ (tl< ()))
L2Ω₂ (wl e v) (inj₂ refl) = ⊥-elim (c1≢cω e)
L2Ω₂ (w4 e) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< p))
L2Ω₂ (w4 {b = b} e) (inj₁ (hd< (ar< p))) with E.pred b
... | [] = inj₁ (tl< []<)
... | _ ∷ _ = inj₁ (hd< (ar< []<))
L2Ω₂ (w4 e) (inj₁ (tl< ()))
L2Ω₂ (w4 e) (inj₂ refl) = ⊥-elim (c0≢c1 e)
L2Ω₂ (w5 e v) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< p))
L2Ω₂ (w5 e v) (inj₁ (hd< (ar< p))) = inj₁ (hd< (ar< (ne2 v)))
L2Ω₂ (w5 e v) (inj₁ (tl< ()))
L2Ω₂ (w5 e v) (inj₂ refl) = ⊥-elim (c0≢cω e)
L2Ω₂ (w6 e g w) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< p))
L2Ω₂ (w6 e g w) (inj₁ (hd< (ar< p))) = inj₁ (hd< (ar< (fΩ-pos w []<)))
L2Ω₂ (w6 e g w) (inj₁ (tl< ()))
L2Ω₂ (w6 e g w) (inj₂ refl) = ⊥-elim (c0≢cΩ e)

mLΩ₂ : ∀ s → E.cof s ≡ cω → E.fsn s 2 <ᵀ Ω₂ → s <ᵀ Ω₂
mLΩ₂ s e q with tri s Ω₂
... | inj₁ lt′ = lt′
... | inj₂ (inj₁ refl) = ⊥-elim (cΩ≢cω e)
... | inj₂ (inj₂ gt′) = ⊥-elim (<ᵀ-irrefl (≤-< (subst (Ω₂ ≤ᵀ_) (sym (fω-eq (vω s e) 2)) (L2Ω₂ (vω s e) (inj₁ gt′))) q))

LΩ₂ : ∀ {s μ} (v : VΩ s μ) → μ ≡ [] → fΩ v (E.natT 2) <ᵀ Ω₂ → s <ᵀ Ω₂
LΩ₂ (ωs v) eμ (hd< p) = hd< p
LΩ₂ (ωs v) eμ (tl< ())
LΩ₂ (ωr {u = u} e) eμ q = subst (λ z → (E.ψ z [] ∷ []) <ᵀ Ω₂) (trans (cong E.sucT (sym eμ)) (pred-suc u e)) Ω₁<Ω₂
LΩ₂ (ωl e v) eμ q = ⊥-elim (helpl₂ (two≤ (fΩ-big v)) q)
  where
  helpl₂ : ∀ {X} → E.natT 2 ≤ᵀ X → (E.ψ X [] ∷ []) <ᵀ Ω₂ → ⊥
  helpl₂ le (hd< (lv< p)) = <ᵀ-irrefl (≤-< le p)
  helpl₂ le (hd< (ar< ()))
  helpl₂ le (tl< ())
LΩ₂ (ωp {u = u} {b = b} e pen v) eμ q = helpp₂ q
  where
  helpp₂ : ∀ {X} → (E.ψ u X ∷ []) <ᵀ Ω₂ → (E.ψ u b ∷ []) <ᵀ Ω₂
  helpp₂ (hd< (lv< p)) = hd< (lv< p)
  helpp₂ (hd< (ar< ()))
  helpp₂ (tl< ())

reqL-Ω₂ : ReqL Ω₂
reqL-Ω₂ t e h = mLΩ₂ t e (h 2)

req₀-Ω₂ : Req₀ Ω₂
req₀-Ω₂ t e h = LΩ₂ (vΩ t e) refl (subst (_<ᵀ Ω₂) (fΩ-eq (vΩ t e) (E.natT 2)) (h (E.natT 2) (natT<Ωs 2 [])))
```

`Req₁ θ₁`：比 θ₁ 大、共尾 Ω₂ 的项，在下标 natT 3 或 Ω₁ 处的基本列项仍不低于 θ₁（`G1`）。

```agda
one<ᴾ : ∀ u X → [] <ᵀ X → E.𝟏 E.<ᴾ E.ψ u X
one<ᴾ [] X p = ar< p
one<ᴾ (_ ∷ _) X p = lv< []<

nat-step : ∀ k → E.natT k <ᵀ E.natT (suc k)
nat-step zero = []<
nat-step (suc k) = tl< (nat-step k)

nat-pos : ∀ {k η} → E.natT k <ᵀ η → [] <ᵀ η
nat-pos {k = zero} p = p
nat-pos {k = suc k} (hd< p) = []<
nat-pos {k = suc k} (tl< p) = []<

head≤ : ∀ x xs → (x ∷ []) ≤ᵀ (x ∷ xs)
head≤ x [] = inj₂ refl
head≤ x (_ ∷ _) = inj₁ (tl< []<)

fΩ-gt : ∀ {s μ} (v : VΩ s μ) {k η} → E.natT k <ᵀ η → E.natT k <ᵀ fΩ v η
fΩ-gt (ωr e) p = p
fΩ-gt (ωs v) {k = zero} p = []<
fΩ-gt (ωs {x = E.ψ [] []} v) {k = suc k} p = tl< (fΩ-gt v (<ᵀ-trans (nat-step k) p))
fΩ-gt (ωs {x = E.ψ [] (_ ∷ _)} v) {k = suc k} p = hd< (ar< []<)
fΩ-gt (ωs {x = E.ψ (_ ∷ _) _} v) {k = suc k} p = hd< (lv< []<)
fΩ-gt (ωl e v) {k = zero} p = []<
fΩ-gt (ωl e v) {k = suc k} p = hd< (lv< (fΩ-pos v (nat-pos p)))
fΩ-gt (ωp e pen v) {k = zero} p = []<
fΩ-gt (ωp {u = u} e pen v) {k = suc k} p = hd< (one<ᴾ u _ (fΩ-pos v (nat-pos p)))

G0 : ∀ {b μ} (v : VΩ b μ) → μ ≡ E.𝟏 ∷ [] → Ω₁ <ᵀ b → Ω₁ ≤ᵀ fΩ v Ω₁
G0 (ωs v) eμ (hd< p) = inj₁ (hd< p)
G0 (ωs {x = x} v) eμ (tl< q) = head≤ x _
G0 (ωr e) eμ q = inj₂ refl
G0 (ωl e v) eμ q = lv≤ (inj₁ (fΩ-gt v {k = 1} (hd< (lv< []<))))
G0 (ωp e pen v) eμ (hd< (lv< p)) = inj₁ (hd< (lv< p))
G0 (ωp e pen v) eμ (hd< (ar< p)) = inj₁ (hd< (ar< (fΩ-pos v []<)))

nat2≢ : ∀ {w} → w ≡ E.natT 2 → θ₁ <ᵀ (E.ψ w [] ∷ []) → ⊥
nat2≢ refl (hd< (lv< p)) = <ᵀ-irrefl p
nat2≢ refl (hd< (ar< ()))

G1 : ∀ {t μ} (v : VΩ t μ) → μ ≡ E.𝟏 ∷ [] → θ₁ <ᵀ t → Σ E.T λ η → (η <ᵀ E.Ωs (E.𝟏 ∷ [])) × (θ₁ ≤ᵀ fΩ v η)
G1 (ωs v) eμ (hd< p) = [] , []< , inj₁ (hd< p)
G1 (ωs {x = x} v) eμ (tl< q) = [] , []< , head≤ x _
G1 (ωr {u = u} e) eμ q = ⊥-elim (nat2≢ (trans (sym (pred-suc u e)) (cong E.sucT eμ)) q)
G1 (ωl e v) eμ (hd< (lv< p)) = E.natT 3 , natT<Ωs 3 (E.𝟏 ∷ []) , inj₁ (hd< (lv< (fΩ-gt v (nat-step 2))))
G1 (ωp e pen v) eμ (hd< (lv< p)) = [] , []< , inj₁ (hd< (lv< p))
G1 (ωp e pen v) eμ (hd< (ar< p)) = Ω₁ , hd< (lv< (tl< []<)) , ar≤ (E.natT 2) (G0 v eμ p)

cofθ₁ : E.cof θ₁ ≡ cΩ (E.𝟏 ∷ []) → ⊥
cofθ₁ ()

req₁-gt : ∀ t (e : E.cof t ≡ cΩ (E.𝟏 ∷ [])) → (∀ η → η <ᵀ E.Ωs (E.𝟏 ∷ []) → E.fsT t η <ᵀ θ₁)
  → Σ E.T (λ η → (η <ᵀ E.Ωs (E.𝟏 ∷ [])) × (θ₁ ≤ᵀ fΩ (vΩ t e) η)) → ⊥
req₁-gt t e h (η , p , le) = <ᵀ-irrefl (≤-< le (subst (_<ᵀ θ₁) (fΩ-eq (vΩ t e) η) (h η p)))

req₁-case : ∀ t (e : E.cof t ≡ cΩ (E.𝟏 ∷ [])) → (∀ η → η <ᵀ E.Ωs (E.𝟏 ∷ []) → E.fsT t η <ᵀ θ₁)
  → (t <ᵀ θ₁) ⊎ (t ≡ θ₁) ⊎ (θ₁ <ᵀ t) → t <ᵀ θ₁
req₁-case t e h (inj₁ lt′) = lt′
req₁-case t e h (inj₂ (inj₁ refl)) = ⊥-elim (cofθ₁ e)
req₁-case t e h (inj₂ (inj₂ gt′)) = ⊥-elim (req₁-gt t e h (G1 (vΩ t e) refl gt′))

req₁-θ₁ : Req₁ θ₁
req₁-θ₁ t e h = req₁-case t e h (tri t θ₁)
```
