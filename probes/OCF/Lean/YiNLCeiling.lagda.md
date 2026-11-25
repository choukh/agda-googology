# 第二塔项孩子读法的严格上界
验收文件；`Light` 只限制 Ω 下标层不含 Ω 形状，递归限制孩子。
编译定理：其全部读法严格低于 Ω_{Ω+1}，覆盖 `tw 2` 的每个孩子。
来源：共尾视图与小读法界引用 `YiCNTw1`、`YiLLLeafNeg` 的独立句法引理；未调用其否定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNLCeiling where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiLLLeafNeg as N
import OCF.Lean.YiCNTw1 as T1
open import OCF.Lean.YiVRRel using (NoΩ; NoΩ↑; NoΩ≤)
open import OCF.Lean.YiGICheck using (succᵍ)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-<; <-≤; <ᵀ-trans; <ᵀ-irrefl; <sucT)
open import OCF.Align.EboLean3Base using (hd<Ω; Ωt-mono)
open import OCF.Align.EBO using (<-sucT; pred-suc)
open import OCF.Align.EboLeanView using (Vω; ws; wl; w4; w5; w6; vω; fω; fω-eq; VΩ; ωs; ωr; ωl; ωp; vΩ; fΩ; fΩ-eq; fΩ-mono; fΩ-pos)
κ₂ : E.T
κ₂ = E.Ωs T1.Ω₁

suc-below₂ : ∀ {ν} → ν E.<ᵀ κ₂ → E.sucT ν E.<ᵀ κ₂
suc-below₂ {ν = []} p = E.hd< (E.lv< E.[]<)
suc-below₂ {ν = _ ∷ _} (E.hd< (E.lv< p)) = E.hd< (E.lv< p)
suc-below₂ (E.hd< (E.ar< ()))
suc-below₂ (E.tl< ())

fω-ceil₂ : ∀ {ν} (v : Vω ν) → fω v 2 E.<ᵀ κ₂ → ν E.<ᵀ κ₂
fω-ceil₂ (ws {x = E.ψ u b} v) p = E.hd< (E.lv< (hd<Ω p))
fω-ceil₂ (wl e v) p = E.hd< (E.lv< (<ᵀ-trans
  (T1.fω-below v (<sucT T1.Ω₁ (hd<Ω p))) (<-sucT T1.Ω₁)))
fω-ceil₂ (w4 e) p = E.hd< (E.lv< (hd<Ω p))
fω-ceil₂ (w5 e v) p = E.hd< (E.lv< (hd<Ω p))
fω-ceil₂ (w6 e cmp v) p = E.hd< (E.lv< (hd<Ω p))

probe : E.T → E.T
probe μ = E.sucT (E.Ωt μ)

probe≥2 : ∀ μ → E.natT 2 ≤ᵀ probe μ
probe≥2 [] = inj₂ refl
probe≥2 (_ ∷ _) = inj₁ (E.hd< (E.lv< E.[]<))

fΩ-big-probe : ∀ {ν μ} (v : VΩ ν μ) → E.natT 1 E.<ᵀ fΩ v (probe μ)
fΩ-big-probe {μ} v with probe≥2 μ
... | inj₁ p = <ᵀ-trans (N.fΩ-big v) (fΩ-mono v p)
... | inj₂ eq = subst (λ η → E.natT 1 E.<ᵀ fΩ v η) eq (N.fΩ-big v)

under1 : ∀ {μ} → μ E.<ᵀ E.natT 1 → μ ≡ []
under1 E.[]< = refl
under1 (E.hd< (E.lv< ()))
under1 (E.hd< (E.ar< ()))
under1 (E.tl< ())

fΩ-small : ∀ {ν μ} (v : VΩ ν μ) → fΩ v (probe μ) ≤ᵀ T1.Ω₁ → ν ≤ᵀ T1.Ω₁
fΩ-small (ωs {x = E.ψ u b} v) (inj₁ p) = inj₁ (E.hd< (E.lv< (hd<Ω p)))
fΩ-small {μ = μ} (ωs v) (inj₂ e) = ⊥-elim (bad (cong T1.tail e))
  where
  bad : fΩ v (probe μ) ≡ [] → ⊥
  bad eq = N.conflict (fΩ-big-probe v) (subst (_≤ᵀ E.natT 1) (sym eq) (inj₁ E.[]<))
fΩ-small {μ} (ωr {u} e) (inj₁ p) = inj₂ (cong E.Ωt (trans (sym (pred-suc u e)) (cong E.sucT (under1 (hd<Ω p)))))
fΩ-small (ωr e) (inj₂ eq) = ⊥-elim (T1.nonempty (cong T1.tail eq))
fΩ-small (ωl e v) le = ⊥-elim (N.conflict (fΩ-big-probe v) (T1.Ω-inv le))
fΩ-small (ωp {u} e pen v) (inj₁ p) = inj₁ (E.hd< (E.lv< (hd<Ω p)))
fΩ-small {μ = μ} (ωp e pen v) (inj₂ eq) = ⊥-elim (bad (cong T1.arg eq))
  where
  bad : fΩ v (probe μ) ≡ [] → ⊥
  bad eq = N.conflict (fΩ-big-probe v) (subst (_≤ᵀ E.natT 1) (sym eq) (inj₁ E.[]<))

fΩ-ceil₂ : ∀ {ν μ} (v : VΩ ν μ) → μ E.<ᵀ T1.Ω₁ → fΩ v (probe μ) E.<ᵀ κ₂ → ν E.<ᵀ κ₂
fΩ-ceil₂ (ωs {x = E.ψ u b} v) pm p = E.hd< (E.lv< (hd<Ω p))
fΩ-ceil₂ (ωr {u} e) pm p = subst (λ v → E.Ωt v E.<ᵀ κ₂) (pred-suc u e)
  (E.hd< (E.lv< (<ᵀ-trans (T1.suc-below pm) (<-sucT T1.Ω₁))))
fΩ-ceil₂ (ωl e v) pm p = ≤-< (Ωt-mono (fΩ-small v (<sucT T1.Ω₁ (hd<Ω p)))) (E.hd< (E.lv< (<-sucT T1.Ω₁)))
fΩ-ceil₂ (ωp {u} e pen v) pm p = E.hd< (E.lv< (hd<Ω p))

BaseNoΩ : Sh → Set
BaseNoΩ sS = ⊤
BaseNoΩ sL = ⊤
BaseNoΩ (sΩ k) = NoΩ k

data Light : L → Set where
  lz : Light zero
  ln : ∀ {s h} → BaseNoΩ s → (∀ c → Light (h c)) → Light (nd s h)

sh-bound : ∀ s h → BaseNoΩ s → (∀ c {ν} → GR.Rd (h c) ν → ν E.<ᵀ κ₂)
  → ∀ {ν} → GR.ShR s h ν → ν E.<ᵀ κ₂
sh-bound sS h nb cb {ν} (e , q) = subst (E._<ᵀ κ₂) (pred-suc ν e) (suc-below₂ (cb tt q))
sh-bound sL h nb cb ()
sh-bound (sΩ k) h nk cb {ν} (μ , e , qk , qh) = fΩ-ceil₂ (vΩ ν e) (T1.rdC-bound k nk qk)
  (subst (E._<ᵀ κ₂) (fΩ-eq (vΩ ν e) (probe μ))
    (cb (suc (proj₁ (O.Ωt k))) (qh (probe μ) (suc (proj₁ (O.Ωt k)))
      (succᵍ {ℓ = k} refl (LL.leafC k nk qk)))))

module BoundNode (s : Sh) (h : Ch s → L) (nb : BaseNoΩ s)
  (cb : ∀ c {ν} → GR.Rd (h c) ν → ν E.<ᵀ κ₂) where
  bound : ∀ {ν} → GR.Rd (nd s h) ν → ν E.<ᵀ κ₂
  bound (GR.c0 {ν = []} e) = E.[]<
  bound (GR.c0 {ν = _ ∷ _} e) = ⊥-elim (cof0 _ ne e)
    where open import OCF.Align.EboLeanView using (cof0; ne)
  bound (GR.ca (inj₁ (c , q))) = cb c q
  bound (GR.ca (inj₂ sh)) = sh-bound s h nb cb sh
  bound {ν} (GR.cL e ds) = fω-ceil₂ (vω ν e) (subst (E._<ᵀ κ₂) (fω-eq (vω ν e) 2) (bound (ds 2)))
  bound (GR.cc le q) = ≤-< le (bound q)

rd-light : ∀ ℓ → Light ℓ → ∀ {ν} → GR.Rd ℓ ν → ν E.<ᵀ κ₂
rd-light zero lz q = subst (E._<ᵀ κ₂) (sym (T1.rd-zero q)) E.[]<
rd-light (nd s h) (ln nb ls) = BoundNode.bound s h nb (λ c → rd-light (h c) (ls c))

light-noΩ : ∀ ℓ → NoΩ ℓ → Light ℓ
light-noΩ zero n = lz
light-noΩ (nd sS h) n = ln tt (λ _ → light-noΩ (h tt) n)
light-noΩ (nd sL h) n = ln tt (λ c → light-noΩ (h c) (n c))
light-noΩ (nd (sΩ k) h) ()

light-sum : ∀ a b → Light a → Light b → Light (a ⊕ b)
light-sum a zero la lb = la
light-sum a (nd s h) la (ln nb ls) = ln nb (λ c → light-sum a (h c) la (ls c))

Slots : L → Set
Slots ℓ = ∀ p → NoΩ (at ℓ p)

child-slots : ∀ s h → Slots (nd s h) → ∀ c → Slots (h c)
child-slots s h slots c p = slots (inj₂ (c , inj₂ p))

light-up : ∀ ℓ → Slots ℓ → ∀ c → Light (↑ ℓ c)
light-up ℓ slots zero = lz
light-up ℓ slots (suc c) = ln tt (λ _ → light-up ℓ slots c)
light-up ℓ slots (lim f a) = ln tt (λ n → light-up ℓ slots (f n))
light-up ℓ slots (Ω p g) = ln (slots p) (λ c → light-up ℓ slots (g (fromBr ℓ p c)))
light-up (nd s h) slots (up x c y e) = light-sum (↑ (nd s h) x) (↑ (h c) y)
  (light-up (nd s h) slots x) (light-up (h c) (child-slots s h slots c) y)

slots₁ : Slots (tw 1)
slots₁ (inj₁ (inj₁ tt)) = tt
slots₁ (inj₂ (c , p)) = NoΩ≤ (P.posW⁼ (zero ⊕ ↑ zero c) p) (NoΩ↑ c)

light₁ : Light (tw 1)
light₁ = ln tt (λ c → light-noΩ (zero ⊕ ↑ zero c) (NoΩ↑ c))

child-bound₂ : ∀ c {ν} → GR.Rd (tw 1 ⊕ ↑ (tw 1) c) ν → ν E.<ᵀ κ₂
child-bound₂ c = rd-light (tw 1 ⊕ ↑ (tw 1) c) (light-sum (tw 1) (↑ (tw 1) c) light₁ (light-up (tw 1) slots₁ c))
```
