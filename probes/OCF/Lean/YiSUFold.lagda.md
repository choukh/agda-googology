# 带显式前缀供给的实际折叠归约
验收文件；条件定理：当前根底与每次嵌入更新底都带 `Support` 时，`Rows` 推出实际 `YiTBRow.ψ` 的零目标保持。
证明复用 `YiLKFold.Fold` 的各行；槽位步进明确传入根前缀，嵌入行明确传入更新底供给。
不改原 `Bdᵍ` 或 `LowKeep`，没有证明原域上总有 `Support`，不使用 `Leaf → ⊥`。
入口：`SupportedPres`、`Fold.chain`、`Fold.LF`、`fold`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSUFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono)
open import OCF.Lean.YiHCRel using (M⁰; mz; m1; mL; mΩ; mU; mw; mc; module G⁰)
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiTSNote using (gt0)
open import OCF.Lean.YiLTLim using (nodeZ)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; wz)
open import OCF.Lean.YiAbsGIface using (module Laws)
open import OCF.Lean.YiLKIface
open import OCF.Lean.YiSUIface using (PrefixU; StepU′)
open import OCF.Lean.YiSUSupport
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

SupportedPres : L → Set
SupportedPres ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → Support ℓ o r B t
  → (β : Tr⁺ zero) → M⁰ (E.ψ [] t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → M⁰ (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B zero (z≤ ℓ) β x))

module Fold (s : Sh) (h : Ch s → L)
            (child : (c : Ch s) → SupportedPres (h c))
            (start : StartU (nd s h)) (step : StepU′ (nd s h))
            (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h))
            (gb : OK B) (t : E.T) (sp : Support (nd s h) o r B t) where

  F : Tr⁺ zero → Tr (nd s h) → Tr⁺ zero
  F β x = ψ (nd s h) o r B zero (z≤ (nd s h)) β x

  Fz : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → ∀ x → M⁰ (ψᴺ 0 t) (proj₁ (F β x))
  Fz β mb x = G⁰.m-zl (λ y → proj₁ (F β y)) (mono (nd s h) o r B zero (z≤ (nd s h)) β) mb x

  chain : ∀ a (p : Pos (nd s h)) ν → GR.Nu (nd s h) p ν → E.cof a ≡ E.cΩ ν
    → (g : Br (nd s h) p → Tr (nd s h))
    → (∀ η c → GR.Low (nd s h) p η c → GR.R (nd s h) (E.fsT a η) (g c))
    → ∀ n → GR.Low (nd s h) p (E.γT (t ++ a) ν n)
      (iter (feed (nd s h) o r B p g) (fromBr (nd s h) p zero) (suc n))
  chain a p ν nu e g hg zero = start o r B gb t a p ν nu e g
  chain a p ν nu e g hg (suc n) = step o r B gb t (root s h o r B t sp) a p ν nu e g n
    (iter (feed (nd s h) o r B p g) (fromBr (nd s h) p zero) (suc n))
    (chain a p ν nu e g hg n)
    (hg (E.γT (t ++ a) ν n) _ (chain a p ν nu e g hg n))

  LF : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → ∀ {a x} → GR.R (nd s h) a x → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (F β x))
  LF β mb (mz {x = x}) = ++[] (λ z → M⁰ (ψᴺ 0 z) (proj₁ (F β x))) t (Fz β mb x)
  LF β mb (m1 {t = a} {x = x} e m) =
    G⁰.m-next (F β x) (cofψ1 [] (t ++ a) (cof++1 t a e))
      (λ n → trans (fsnψ1 [] (t ++ a) n (cof++1 t a e))
        (cong (λ z → replicate n (E.ψ [] z)) (pred++ t a e))) (LF β mb m)
  LF β mb (mL {t = a} {x = x} e m) =
    mL (cofψω [] (t ++ a) (cof++ω t a e))
      (λ n → subst (λ z → M⁰ z (proj₁ (F β x)))
        (sym (trans (fsnψω [] (t ++ a) n (cof++ω t a e)) (cong (ψᴺ 0) (fsn++ t a n e))))
        (LF β mb (m n)))
  LF β mb (mΩ {t = a} {ν = ν} {p = p} {g = g} e nu m) =
    nodeZ (kp (nd s h) o p (z≤ (nd s h))) (λ Z → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ Z))
      (λ c → F β (g c)) (feed (nd s h) o r B p g)
      (mL (cofG [] (t ++ a) (gt0 ν) (cof++Ω t a e))
        (λ n → subst
          (λ z → M⁰ z (proj₁ (limc⁺ (λ k → F β (g (iter (feed (nd s h) o r B p g) (fromBr (nd s h) p zero) k))))))
          (sym (trans (fsnG [] (t ++ a) n (gt0 ν) (cof++Ω t a e))
            (cong (ψᴺ 0) (fsT++ t a (E.γT (t ++ a) ν n) e))))
          (G⁰.m-cum (λ k → F β (g (iter (feed (nd s h) o r B p g) (fromBr (nd s h) p zero) k))) (suc n)
            (LF β mb (m (E.γT (t ++ a) ν n) _ (chain a p ν nu e g m n))))))
  LF β mb (mU {t = a} {s = b} {x = x} {c = c} {y = y} {e = ey} m ch) =
    subst (λ z → M⁰ (ψᴺ 0 z) (proj₁ (F β (up x c y ey)))) (++-assoc t a b)
      (child c (proj₂ o c) (proj₂ r c) (Updated s h o r B x c)
        (updated-ok s h o r B gb x c) (t ++ a) (update s h o r B t sp m c)
        (F β x) (LF β mb m) ch)
  LF β mb (mw m d) = mw (LF β mb m) (mono (nd s h) o r B zero (z≤ (nd s h)) β d)
  LF β mb (mc le m) = mc (app≤ 0 t le) (LF β mb m)

fold : ∀ ℓ → Rows ℓ → SupportedPres ℓ
fold zero rows o r B gb t sp = self-zero o r B gb t
fold (nd s h) rows o r B gb t sp =
  Fold.LF s h (λ c → fold (h c) (proj₂ rows c))
    (proj₁ (proj₁ rows)) (proj₂ (proj₁ rows)) o r B gb t sp
```
