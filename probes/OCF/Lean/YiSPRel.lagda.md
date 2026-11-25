# 验收：非零左项所需的前缀更新律
验收文件；条件编译定理：给出 `Shift` 时，`LF¹` 不要求嵌入左项推导为 `mz`。
`Shift` 要求左项朝孩子各层的折叠满足更新前缀后的底条件；本文件没有证明该律。
来源：零、后继、极限、下标槽位及回灌链照 `YiLTKid.Top.Fold`，嵌入改用任意前缀的孩子接口。
入口与可满足实例见 `YiSPInst`；孩子槽位结点尚未加入。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSPRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono; rb-no)
open import OCF.Lean.YiLTKid using (ℓ¹; ΩΩ; module Sem)
module Z = Sem (rb-no ℓ¹)
open Z using (nodeZ)
open import OCF.Lean.YiRBCrit using (h₁)
open import OCF.Lean.YiKVRel using (_⊴_; ++[])
open import OCF.Lean.YiHCRel using (Mᴴ; M⁰; mz; m1; mL; mΩ; mU; mw; mc; pos⁰; module G⁰)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; γT; natT)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)

record Kid⁺ (o : Ok ℓ¹) (r : Rb ℓ¹) : Set₁ where
  field
    Kd : (c : Tr zero) → E.T → Tr (h₁ c) → Set
    GBc : (c : Tr zero) → E.T → Base (h₁ c) → Set
    Pc : (c : Tr zero) → zero ≤ h₁ c → Set
    pz : ∀ c → Pc c (z≤ (h₁ c))
    pk : ∀ c → Pc c (self ∙ proj₂ (proj₁ o) c)
    foldᶜ : ∀ c (v : zero ≤ h₁ c) → Pc c v → (t : E.T)
          → (B : Base (h₁ c)) → GBc c t B
          → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
          → ∀ {s y} → Kd c s y
          → M⁰ (ψᴺ 0 (t ++ s)) (proj₁ (ψ (h₁ c) (proj₂ o c) (proj₂ r c) B zero v β y))

module Top (o : Ok ℓ¹) (r : Rb ℓ¹) (K : Kid⁺ o r) where
  open Kid⁺ K public

  Low¹ : (p : Pos ℓ¹) → E.T → Br ℓ¹ p → Set
  Low¹ (inj₁ (inj₁ tt)) = M⁰
  Low¹ (inj₁ (inj₂ ()))
  Low¹ (inj₂ _) = λ _ _ → ⊥

  Nu¹ : Pos ℓ¹ → E.T → Set
  Nu¹ (inj₁ (inj₁ tt)) ν = ν ≡ []
  Nu¹ (inj₁ (inj₂ ()))
  Nu¹ (inj₂ _) ν = ⊥

  M¹ : E.T → Tr ℓ¹ → Set
  M¹ = Mᴴ (Sig ℓ¹) Low¹ Kd Nu¹

  record GB¹ (B : Base ℓ¹) (t : E.T) : Set where
    constructor mkGB¹
    field
      bK : M⁰ (ψᴺ 0 t) (proj₁ (B zero (ink self)))
      bC : ∀ c → GBc c t (λ i u → B i (inc c u))
  open GB¹ public

  data Pw : zero ≤ ℓ¹ → Set where
    wu : Pw (inu (λ c → z≤ (h₁ c)))
    wi : Pw (ink self)

  cb : Base ℓ¹ → Tr ℓ¹ → (c : Tr zero) → Base (h₁ c)
  cb B x c i u = ψ ℓ¹ o r B i (inc c u) (B i (inc c u)) x

  Shift : Base ℓ¹ → E.T → Set
  Shift B t = ∀ {a x} → M¹ a x → ∀ c → GBc c (t ++ a) (cb B x c)

  module Fold (B : Base ℓ¹) (t : E.T) (gb : GB¹ B t) (shift : Shift B t) where
    F : zero ≤ ℓ¹ → Tr⁺ zero → Tr ℓ¹ → Tr⁺ zero
    F w β x = ψ ℓ¹ o r B zero w β x

    feed : (Tr zero → Tr ℓ¹) → Tr zero → Tr zero
    feed g z = proj₁ (F (ink self) (B zero (ink self)) (g z))

    Fz : ∀ w (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
       → ∀ x → M⁰ (ψᴺ 0 t) (proj₁ (F w β x))
    Fz w β hβ x = G⁰.m-zl (λ y → proj₁ (F w β y)) (mono ℓ¹ o r B zero w β) hβ x

    mutual
      LF¹ : ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
          → ∀ {a x} → M¹ a x → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (F w β x))
      LF¹ {w} pw β hβ (mz {x = x}) =
        ++[] (λ z → M⁰ (ψᴺ 0 z) (proj₁ (F w β x))) t (Fz w β hβ x)
      LF¹ {w} pw β hβ (m1 {t = a} {x = x} e h) =
        G⁰.m-next (F w β x) (cofψ1 (natT 0) (t ++ a) (cof++1 t a e))
          (λ k → trans (fsnψ1 (natT 0) (t ++ a) k (cof++1 t a e))
            (cong (λ z → replicate k (E.ψ (natT 0) z)) (pred++ t a e)))
          (LF¹ pw β hβ h)
      LF¹ {w} pw β hβ (mL {t = a} {x = x} e h) =
        mL (cofψω (natT 0) (t ++ a) (cof++ω t a e))
          (λ k → subst (λ z → M⁰ z (proj₁ (F w β x)))
            (sym (trans (fsnψω (natT 0) (t ++ a) k (cof++ω t a e))
              (cong (ψᴺ 0) (fsn++ t a k e)))) (LF¹ pw β hβ (h k)))
      LF¹ {w} pw β hβ (mΩ {t = a} {p = inj₁ (inj₁ tt)} {g = g} e refl h) =
        nodeZ (kp ℓ¹ o (inj₁ (inj₁ tt)) w) (λ Z → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ Z)) (λ z → F w β (g z)) (feed g)
          (mL (cofG (natT 0) (t ++ a) refl (cof++Ω t a e))
            (λ k → subst (λ z → M⁰ z (proj₁ (limc⁺ (λ k′ → F w β (g (iter (feed g) zero k′))))))
              (sym (trans (fsnG (natT 0) (t ++ a) k refl (cof++Ω t a e))
                (cong (ψᴺ 0) (fsT++ t a (γT (t ++ a) [] k) e))))
              (G⁰.m-cum (λ k′ → F w β (g (iter (feed g) zero k′))) (suc k)
                (LF¹ pw β hβ (h (γT (t ++ a) [] k) (iter (feed g) zero (suc k)) (chain e h k))))))
      LF¹ pw β hβ (mΩ {p = inj₁ (inj₂ ())} _ _ _)
      LF¹ pw β hβ (mΩ {p = inj₂ _} _ () _)
      LF¹ {w} pw β hβ (mU {t = a} {s = s} {x = x} {c = c} {y = y} {e = ey} m ch) =
        subst (λ z → M⁰ (ψᴺ 0 z) (proj₁ (F w β (up x c y ey)))) (++-assoc t a s)
          (LFU pw β hβ m ch)
      LF¹ {w} pw β hβ (mw m d) = mw (LF¹ pw β hβ m) (mono ℓ¹ o r B zero w β d)
      LF¹ pw β hβ (mc le m) = mc (app≤ 0 t le) (LF¹ pw β hβ m)

      LFU : ∀ {w a s x c y ey} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
          → M¹ a x → Kd c s y
          → M⁰ (ψᴺ 0 ((t ++ a) ++ s)) (proj₁ (F w β (up x c y ey)))
      LFU {c = c} wu β hβ m ch =
        foldᶜ c (z≤ (h₁ c)) (pz c) _ _ (shift m c) _ (LF¹ wu β hβ m) ch
      LFU {c = c} wi β hβ m ch =
        foldᶜ c (self ∙ proj₂ (proj₁ o) c) (pk c) _ _ (shift m c) _ (LF¹ wi β hβ m) ch

      chain : ∀ {a} {g : Tr zero → Tr ℓ¹} → cof a ≡ cΩ []
            → (h : ∀ η c → M⁰ η c → M¹ (fsT a η) (g c))
            → ∀ k → M⁰ (γT (t ++ a) [] k) (iter (feed g) zero (suc k))
      chain {g = g} e h zero = pos⁰ _ (proj₂ (F (ink self) (B zero (ink self)) (g zero)))
      chain {a} {g} e h (suc k) =
        subst (λ z → M⁰ (ψᴺ 0 z) (feed g (iter (feed g) zero (suc k))))
          (sym (fsT++ t a (γT (t ++ a) [] k) e))
          (LF¹ wi (B zero (ink self)) (bK gb)
            (h (γT (t ++ a) [] k) (iter (feed g) zero (suc k)) (chain e h k)))
```
