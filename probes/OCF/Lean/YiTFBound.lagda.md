# 第 0、1 层下界读法的上界: R 只读出低于 Ω₁ 或 Ω₁+Ω₁ 的项
验收文件 (读记号); 编译定理: 第 0 层 `bZ` (`M⁰` 只读出低于 Ω₁ 的项); 第 1 层无 Ω 结点的树 `bD` (低于 Ω₁), Ω₁ 树加可数尾巴的树 `bS` (低于 Ω₁+Ω₁).
记号一侧的阈值引理 `L2Ω`, `L2ΩΩ` (ω 共尾项的第 2 项不低于阈值), `LΩ` (Ω₁ 共尾项), `rd-zero` (第 0 层只读作空).
做法照 `YiLLLeafNeg.bound` (对推导归纳, `mc` 一行用项序传递, `mL` 一行用视图); 不涉及值, 不否定什么. 入口 `bS`, `bD`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTFBound where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ₀ʳ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiSUIface using (StepU′; PrefixU; WholeU)
open import OCF.Lean.YiLKIface using (feed; OK)
open import OCF.Lean.YiLLCheck using (leafC)
open import OCF.Lean.YiVRRel using (NoΩ; NoΩ≤)
open import OCF.Lean.YiLLLeafNeg using (fω-big; fsn-big; positive)
open import OCF.Lean.YiKVRel using (one; ⊴r)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; tri; <ᵀ-irrefl; <ᵀ-trans; ≤-<; Pen; Pen→≤)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Align.EboLeanView using (Vω; ws; wl; w4; w5; w6; vω; fω; fω-eq; VΩ; ωs; ωr; ωl; ωp; vΩ; fΩ; fΩ-eq; fΩ-pos; γ; cof0; ne)
```

## 记号一侧: 阈值 Ω₁ 与 Ω₁+Ω₁

`ωr` 一行要读法的下标为空 (由 `rd-zero` 给出); `ωl`, `ωp` 两行与阈值冲突. 视图一行在 `fΩ` 不化简时要用辅助函数把下标放成变量.

```agda
ΩP : E.PT
ΩP = E.ψ (E.𝟏 ∷ []) []

Ω₁ ΩΩ : E.T
Ω₁ = ΩP ∷ []
ΩΩ = ΩP ∷ ΩP ∷ []

c1≢cω : E.c1 ≡ E.cω → ⊥
c1≢cω ()

c0≢c1 : E.c0 ≡ E.c1 → ⊥
c0≢c1 ()

c0≢cω : E.c0 ≡ E.cω → ⊥
c0≢cω ()

c0≢cΩ : ∀ {μ} → E.c0 ≡ E.cΩ μ → ⊥
c0≢cΩ ()

cΩ≢cω : ∀ {μ} → E.cΩ μ ≡ E.cω → ⊥
cΩ≢cω ()

sucΩ : ∀ {x} → x <ᵀ Ω₁ → E.sucT x <ᵀ Ω₁
sucΩ {x = []} []< = hd< (lv< []<)
sucΩ (hd< p) = hd< p

sucΩΩ : ∀ {x} → x <ᵀ ΩΩ → E.sucT x <ᵀ ΩΩ
sucΩΩ {x = []} []< = hd< (lv< []<)
sucΩΩ (hd< p) = hd< p
sucΩΩ (tl< q) = tl< (sucΩ q)

++Ω : ∀ {a b} → a <ᵀ Ω₁ → b <ᵀ Ω₁ → (a ++ b) <ᵀ Ω₁
++Ω {a = []} p q = q
++Ω (hd< p) q = hd< p

below1 : ∀ {a} → [] <ᵀ a → a <ᵀ (E.𝟏 ∷ []) → ⊥
below1 []< (hd< (lv< ()))
below1 []< (hd< (ar< ()))
below1 []< (tl< ())

sucT-ne : ∀ μ → [] <ᵀ E.sucT μ
sucT-ne [] = []<
sucT-ne (_ ∷ _) = []<

le-nil : ∀ {a} → [] <ᵀ a → a ≤ᵀ [] → ⊥
le-nil p (inj₁ ())
le-nil () (inj₂ refl)

ne2 : ∀ {s} (v : Vω s) → [] <ᵀ fω v 2
ne2 v = positive (fω-big v)

γ2 : ∀ {b ν} (w : VΩ b ν) → [] <ᵀ fΩ w (γ w 2)
γ2 w = fΩ-pos w []<

L2Ω : ∀ {s} (v : Vω s) → Ω₁ ≤ᵀ s → Ω₁ ≤ᵀ fω v 2
L2Ω (ws v) (inj₁ (hd< p)) = inj₁ (hd< p)
L2Ω (ws v) (inj₁ (tl< q)) = inj₁ (tl< (ne2 v))
L2Ω (wl e v) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< (fω-big v)))
L2Ω (wl e v) (inj₁ (hd< (ar< ())))
L2Ω (wl e v) (inj₁ (tl< ()))
L2Ω (wl e v) (inj₂ refl) = ⊥-elim (c1≢cω e)
L2Ω (w4 e) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< p))
L2Ω (w4 {b = b} e) (inj₁ (hd< (ar< p))) with E.pred b
... | [] = inj₁ (tl< []<)
... | _ ∷ _ = inj₁ (hd< (ar< []<))
L2Ω (w4 e) (inj₁ (tl< ()))
L2Ω (w4 e) (inj₂ refl) = ⊥-elim (c0≢c1 e)
L2Ω (w5 e v) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< p))
L2Ω (w5 e v) (inj₁ (hd< (ar< p))) = inj₁ (hd< (ar< (ne2 v)))
L2Ω (w5 e v) (inj₁ (tl< ()))
L2Ω (w5 e v) (inj₂ refl) = ⊥-elim (c0≢cω e)
L2Ω (w6 e g w) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< p))
L2Ω (w6 e g w) (inj₁ (hd< (ar< p))) = inj₁ (hd< (ar< (γ2 w)))
L2Ω (w6 e g w) (inj₁ (tl< ()))
L2Ω (w6 e g w) (inj₂ refl) = ⊥-elim (c0≢cΩ e)

noVωΩ : Vω Ω₁ → ⊥
noVωΩ (wl e v) = c1≢cω e
noVωΩ (w4 e) = c0≢c1 e
noVωΩ (w5 e v) = c0≢cω e
noVωΩ (w6 e g w) = c0≢cΩ e

L2ΩΩ : ∀ {s} (v : Vω s) → ΩΩ ≤ᵀ s → ΩΩ ≤ᵀ fω v 2
L2ΩΩ (ws v) (inj₁ (hd< p)) = inj₁ (hd< p)
L2ΩΩ (ws v) (inj₁ (tl< q)) = H.∷≤ ΩP (L2Ω v (inj₁ q))
L2ΩΩ (ws v) (inj₂ refl) = ⊥-elim (noVωΩ v)
L2ΩΩ (wl e v) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< (fω-big v)))
L2ΩΩ (wl e v) (inj₁ (hd< (ar< ())))
L2ΩΩ (wl e v) (inj₁ (tl< ()))
L2ΩΩ (w4 e) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< p))
L2ΩΩ (w4 {b = b} e) (inj₁ (hd< (ar< p))) with E.pred b
... | [] = inj₂ refl
... | _ ∷ _ = inj₁ (hd< (ar< []<))
L2ΩΩ (w4 e) (inj₁ (tl< ()))
L2ΩΩ (w5 e v) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< p))
L2ΩΩ (w5 e v) (inj₁ (hd< (ar< p))) = inj₁ (hd< (ar< (ne2 v)))
L2ΩΩ (w5 e v) (inj₁ (tl< ()))
L2ΩΩ (w6 e g w) (inj₁ (hd< (lv< p))) = inj₁ (hd< (lv< p))
L2ΩΩ (w6 e g w) (inj₁ (hd< (ar< p))) = inj₁ (hd< (ar< (γ2 w)))
L2ΩΩ (w6 e g w) (inj₁ (tl< ()))

lvψ : ∀ {u X} → E.ψ u X E.<ᴾ ΩP → u <ᵀ (E.𝟏 ∷ [])
lvψ (lv< p) = p
lvψ (ar< ())

LΩ : ∀ {s μ} (v : VΩ s μ) → μ ≡ [] → fΩ v (E.natT 2) <ᵀ Ω₁ → s ≤ᵀ Ω₁
LΩ (ωs v) eμ (hd< p) = inj₁ (hd< p)
LΩ (ωs v) eμ (tl< ())
LΩ (ωr {u = u} e) eμ q = inj₂ (cong (λ z → E.ψ z [] ∷ []) (trans (sym (pred-suc u e)) (cong E.sucT eμ)))
LΩ (ωl e v) eμ q = ⊥-elim (helpl (fΩ-pos v []<) q)
  where
  helpl : ∀ {X} → [] <ᵀ X → (E.ψ X [] ∷ []) <ᵀ Ω₁ → ⊥
  helpl n (hd< q′) = below1 n (lvψ q′)
  helpl n (tl< ())
LΩ (ωp {u = u} {μ = μ} e pen v) eμ q = ⊥-elim (helpp u pen q)
  where
  helpp : ∀ u′ {X} → Pen (E.cmpᵀ (E.sucT μ) u′) → (E.ψ u′ X ∷ []) <ᵀ Ω₁ → ⊥
  helpp [] pen′ (hd< q′) = le-nil (sucT-ne μ) (Pen→≤ (E.sucT μ) [] pen′)
  helpp (_ ∷ _) pen′ (hd< q′) = below1 []< (lvψ q′)
  helpp u′ pen′ (tl< ())

mLΩ : ∀ s → E.cof s ≡ E.cω → E.fsn s 2 <ᵀ Ω₁ → s <ᵀ Ω₁
mLΩ s e q with tri s Ω₁
... | inj₁ lt = lt
... | inj₂ (inj₁ refl) = ⊥-elim (cΩ≢cω e)
... | inj₂ (inj₂ gt) = ⊥-elim (<ᵀ-irrefl (≤-< (subst (Ω₁ ≤ᵀ_) (sym (fω-eq (vω s e) 2)) (L2Ω (vω s e) (inj₁ gt))) q))

mLΩΩ : ∀ s → E.cof s ≡ E.cω → E.fsn s 2 <ᵀ ΩΩ → s <ᵀ ΩΩ
mLΩΩ s e q with tri s ΩΩ
... | inj₁ lt = lt
... | inj₂ (inj₁ refl) = ⊥-elim (cΩ≢cω e)
... | inj₂ (inj₂ gt) = ⊥-elim (<ᵀ-irrefl (≤-< (subst (ΩΩ ≤ᵀ_) (sym (fω-eq (vω s e) 2)) (L2ΩΩ (vω s e) (inj₁ gt))) q))

rd-zero : ∀ {κ} → GR.Rd zero κ → κ ≡ []
rd-zero {κ = []} (GR.c0 e) = refl
rd-zero {κ = _ ∷ _} (GR.c0 e) = ⊥-elim (cof0 _ ne e)
rd-zero (GR.ca ())
rd-zero (GR.cL e h) = ⊥-elim (nil1 (subst (E.natT 1 <ᵀ_) (rd-zero (h 2)) (fsn-big e)))
  where
  nil1 : E.natT 1 <ᵀ [] → ⊥
  nil1 ()
rd-zero (GR.cc le r) with rd-zero r
... | refl with le
... | inj₂ refl = refl
```

## 第 0 层

```agda
bZ : ∀ {s y} → H.M⁰ s y → s <ᵀ Ω₁
bZ H.mz = []<
bZ (H.m1 {t = s} e r) = subst (_<ᵀ Ω₁) (pred-suc s e) (sucΩ (bZ r))
bZ (H.mL {t = s} e h) = mLΩ s e (bZ (h 2))
bZ (H.mΩ {p = ()} _ _ _)
bZ (H.mU {c = ()} _ _)
bZ (H.mw m d) = bZ m
bZ (H.mc le m) = ≤-< le (bZ m)
```

## 第 1 层: 无 Ω 结点的树, Ω₁ 树加可数尾巴的树

`S` 关于 `◃` 向下封闭到 `S` 或无 Ω 结点 (`S-down`); Ω₁ 树的分支是可数树的嵌入, 用 `bD` 在第 2 个分支上取界.

```agda
data D0 : Tr one → Set where
  dz : D0 zero
  ds : ∀ {x} → D0 x → D0 (suc x)
  dl : ∀ {f a} → (∀ n → D0 (f n)) → D0 (lim f a)
  du : ∀ {x c y e} → D0 x → D0 (up x c y e)

data S : Tr one → Set where
  sb : S (proj₁ (Ωt one))
  ss : ∀ {x} → S x → S (suc x)
  sℓ : ∀ {f a} → (∀ n → S (f n)) → S (lim f a)

D0-down : ∀ {x y} → one ⊢ x ◃ y → D0 y → D0 x
D0-down ◃s (ds d) = d
D0-down (◃l n) (dl h) = h n
D0-down ◃w ()
D0-down (◃u x c y e) (du d) = d
D0-down (◃c x c d′) (du d) = du d
D0-down (◃t d e) dy = D0-down d (D0-down e dy)

S-down : ∀ {x y} → one ⊢ x ◃ y → S y → S x ⊎ D0 x
S-down ◃s (ss s) = inj₁ s
S-down (◃l n) (sℓ h) = inj₁ (h n)
S-down ◃w sb = inj₂ (du dz)
S-down (◃t d e) sy with S-down e sy
... | inj₁ s = S-down d s
... | inj₂ dd = inj₂ (D0-down d dd)

c2 : Tr zero
c2 = suc (suc zero)

r2 : H.M⁰ (E.natT 2) c2
r2 = H.m1 refl (H.m1 refl H.mz)

Ω<ΩΩ : Ω₁ <ᵀ ΩΩ
Ω<ΩΩ = tl< []<

mutual
  bD : ∀ {t x} → GR.R one t x → D0 x → t <ᵀ Ω₁
  bD H.mz _ = []<
  bD (H.m1 {t = t} e r) (ds d) = subst (_<ᵀ Ω₁) (pred-suc t e) (sucΩ (bD r d))
  bD (H.mL {t = t} e h) d = mLΩ t e (bD (h 2) d)
  bD (H.mΩ e nu h) ()
  bD (H.mU m ch) (du d) = ++Ω (bD m d) (bZ ch)
  bD (H.mw m dd) d = bD m (D0-down dd d)
  bD (H.mc le m) d = ≤-< le (bD m d)

  bS : ∀ {t x} → GR.R one t x → S x → t <ᵀ ΩΩ
  bS H.mz _ = []<
  bS (H.m1 {t = t} e r) (ss s) = subst (_<ᵀ ΩΩ) (pred-suc t e) (sucΩΩ (bS r s))
  bS (H.mL {t = t} e h) s = mLΩΩ t e (bS (h 2) s)
  bS (H.mΩ {t = t} e nu h) sb = ≤-< (LΩ (vΩ t e) (rd-zero nu)
    (subst (_<ᵀ Ω₁) (fΩ-eq (vΩ t e) (E.natT 2)) (bD (h (E.natT 2) c2 r2) (du dz)))) Ω<ΩΩ
  bS (H.mw m dd) s with S-down dd s
  ... | inj₁ s′ = bS m s′
  ... | inj₂ d′ = <ᵀ-trans (bD m d′) Ω<ΩΩ
  bS (H.mc le m) s = ≤-< le (bS m s)

S-plus : ∀ y → S (proj₁ (Ωt one) + ι one y)
S-plus zero = sb
S-plus (suc y) = ss (S-plus y)
S-plus (lim f a) = sℓ (λ n → S-plus (f n))

S-+ι : ∀ {x} → S x → ∀ y → S (x + ι one y)
S-+ι s zero = s
S-+ι s (suc y) = ss (S-+ι s y)
S-+ι s (lim f a) = sℓ (λ n → S-+ι s (f n))

S-⊞⁺ : ∀ (b : Tr⁺ one) (Y : Tr⁺ zero) → S (proj₁ b) → S (proj₁ (b ⊞ Y))
S-⊞⁺ b Y s = S-+ι s (proj₁ Y)
```
