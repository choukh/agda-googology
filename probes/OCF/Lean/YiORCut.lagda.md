# 原行审查：封闭判据所用的句法截界
验收文件（读记号）；编译定理：ψ₂(Ω₂) 的严格下段对余尾 ω 的基本列规则封闭。
来源：复用 `YiSUBound` 的有限下界；沿 `EboLeanView` 的共尾视图证明截界，不引用无封闭否定。
入口：`ω-cap`、`cap-suc`；不改树、折叠或合法性。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiORCut where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-irrefl; <-≤; ≤-<; gt→≤)
open import OCF.Align.EboLean3Base using (hd<Ω; Ωt-mono)
open import OCF.Align.EboLeanView using (Vω; ws; wl; w4; w5; w6; vω; fω; fω-eq; VΩ; ωs; ωr; ωl; ωp; fΩ; γ)
open import OCF.Lean.YiSUBound using (fω-nat; nat-prefix; nat-pos; nat-ψ)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)

cap : E.T
cap = ψᴺ 2 (Ωᴺ 2)

single< : ∀ {p xs q} → (p ∷ xs) <ᵀ (q ∷ []) → p <ᴾ q
single< (hd< p) = p
single< (tl< ())

single-suc : ∀ {t p} → E.𝟏 <ᴾ p → t <ᵀ (p ∷ []) → E.sucT t <ᵀ (p ∷ [])
single-suc op []< = hd< op
single-suc op (hd< p) = hd< p
single-suc op (tl< ())

Ω-suc : ∀ {t} → t <ᵀ Ωᴺ 2 → E.sucT t <ᵀ Ωᴺ 2
Ω-suc = single-suc (lv< []<)

cap-suc : ∀ {t} → t <ᵀ cap → E.sucT t <ᵀ cap
cap-suc = single-suc (lv< []<)

nat-leaf : ∀ n {u} → [] <ᵀ u → E.natT n <ᵀ (E.ψ u [] ∷ [])
nat-leaf zero p = []<
nat-leaf (suc n) p = hd< (lv< p)

fΩ-nat : ∀ {t κ η} (v : VΩ t κ) n → E.natT n <ᵀ η → E.natT n <ᵀ fΩ v η
fΩ-nat (ωs {x = x} v) n p = nat-prefix n x (fΩ-nat v n p)
fΩ-nat (ωr e) n p = p
fΩ-nat (ωl e v) n p = nat-leaf n (nat-pos (fΩ-nat v n p))
fΩ-nat (ωp {u = u} e cmp v) n p = nat-ψ n u (nat-pos (fΩ-nat v n p))

Ω-cut : ∀ {t κ η} (v : VΩ t κ) → Ωᴺ 2 ≤ᵀ η → fΩ v η <ᵀ Ωᴺ 2 → t <ᵀ Ωᴺ 2
Ω-cut (ωs v) ge p = hd< (single< p)
Ω-cut (ωr e) ge p = ⊥-elim (<ᵀ-irrefl (≤-< ge p))
Ω-cut (ωl e v) ge p = ⊥-elim (<ᵀ-irrefl (<-≤ (fΩ-nat v 2 (<-≤ (hd< (lv< []<)) ge)) (inj₁ (hd<Ω p))))
Ω-cut (ωp e cmp v) ge p = hd< (lv< (hd<Ω p))

ω-Ω-cut : ∀ {t} (v : Vω t) → (∀ n → fω v n <ᵀ Ωᴺ 2) → t <ᵀ Ωᴺ 2
ω-Ω-cut (ws v) all = hd< (single< (all 0))
ω-Ω-cut (wl e v) all = ⊥-elim (<ᵀ-irrefl (<-≤ (fω-nat v 2) (inj₁ (hd<Ω (all 3)))))
ω-Ω-cut (w4 e) all = hd< (lv< (hd<Ω (all 1)))
ω-Ω-cut (w5 e v) all = hd< (lv< (hd<Ω (all 0)))
ω-Ω-cut (w6 e cmp v) all = hd< (lv< (hd<Ω (all 0)))

index≤ : ∀ {u b v c} → E.ψ u b <ᴾ E.ψ v c → u ≤ᵀ v
index≤ (lv< p) = inj₁ p
index≤ (ar< p) = inj₂ refl

arg< : ∀ {b} → ψᴺ 2 b <ᵀ cap → b <ᵀ Ωᴺ 2
arg< (hd< (lv< p)) = ⊥-elim (<ᵀ-irrefl p)
arg< (hd< (ar< p)) = p
arg< (tl< ())

pred-principal : ∀ {u b} → E.cof b ≡ E.c1 → E.ψ u (E.pred b) <ᴾ E.ψ (E.natT 2) (Ωᴺ 2) → E.ψ u b <ᴾ E.ψ (E.natT 2) (Ωᴺ 2)
pred-principal e (lv< p) = lv< p
pred-principal {b = b} e (ar< p) = ar< (subst (_<ᵀ Ωᴺ 2) (pred-suc b e) (Ω-suc p))

ω-cap : ∀ {t} (v : Vω t) → (∀ n → fω v n <ᵀ cap) → t <ᵀ cap
ω-cap (ws v) all = hd< (single< (all 0))
ω-cap (wl e v) all = ⊥-elim (<ᵀ-irrefl (<-≤ (fω-nat v 2) (index≤ (single< (all 3)))))
ω-cap (w4 e) all = hd< (pred-principal e (single< (all 2)))
ω-cap (w5 e v) all with single< (all 0)
... | lv< p = hd< (lv< p)
... | ar< p = hd< (ar< (ω-Ω-cut v (λ n → arg< (all n))))
ω-cap (w6 {ν = ν} e cmp v) all with single< (all 0)
... | lv< p = hd< (lv< p)
... | ar< p = hd< (ar< (Ω-cut v (Ωt-mono (gt→≤ ν (E.natT 2) cmp)) p))
```
