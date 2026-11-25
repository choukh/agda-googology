# 可达分支域上的全层零目标归约
验收文件；编译条件定理：全层 `Startᵂ` 与 `Stepᵂ` 推出实际 domsᵍ 的 LowKeep。
来源：`YiLKFold.Fold.LF` 加 W 证据；Ω 行递归仅访问实际链，嵌入行用 W 的孩子闭包。
全层两律未实填，W 未证为真子域；带全域 Leaf 的附属归约不作为强度成果。
入口：`Presᵂ`、`Stepᵂ`、`fromSlots`、`slots→lowKeepᵂ`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPFReachFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock hiding (R; D)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono)
open import OCF.Lean.YiHCRel using (M⁰; mz; m1; mL; mΩ; mU; mw; mc; module G⁰)
open import OCF.Lean.YiKVRel using (++[]; _⊴_; ⊴r; ⊴◃)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiTSNote using (gt0)
open import OCF.Lean.YiLTLim using (nodeZ)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; wz)
open import OCF.Lean.YiAbsGIface using (module Laws)
open import OCF.Lean.YiLKIface using (OK; StartU; StepU; self-zero; updated-ok)
open import OCF.Lean.YiLKSlot using (start-from-leaf)
open import OCF.Lean.YiPFReach using (W; OKᵀ)
open import OCF.Lean.YiPFDom using (feedᴰ)
import OCF.Lean.YiPFReach as D
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

⊴-tree : ∀ {S} {x y : T S} → x ⊴ y → (x ≡ y) ⊎ Lt S x y
⊴-tree ⊴r = inj₁ refl
⊴-tree (⊴◃ d) = inj₂ d

ok-tree : ∀ {ℓ} {B : Base ℓ} → OK B → OKᵀ B
ok-tree gb i u = ⊴-tree (gb i u)

Presᵂ : L → Set
Presᵂ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
  → ∀ {a x} → W ℓ x → GR.R ℓ a x
  → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (ψ ℓ o r B zero (z≤ ℓ) β x))

Startᵂ : L → Set
Startᵂ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g)
  → GR.Low ℓ p (E.γT (t ++ a) ν zero) (D.chain ℓ o r B p g 1)

Stepᵂ : L → Set
Stepᵂ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g) → (n : ℕ)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) (D.chain ℓ o r B p g (suc n))
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g (D.chain ℓ o r B p g (suc n)))
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (D.chain ℓ o r B p g (suc (suc n)))

module Fold (s : Sh) (h : Ch s → L) (kid : (c : Ch s) → Presᵂ (h c))
  (st : Startᵂ (nd s h)) (sp : Stepᵂ (nd s h))
  (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (gb : OK B) (t : E.T) where

  F : Tr⁺ zero → Tr (nd s h) → Tr⁺ zero
  F β x = ψ (nd s h) o r B zero (z≤ (nd s h)) β x

  Fz : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → ∀ x → M⁰ (ψᴺ 0 t) (proj₁ (F β x))
  Fz β mb x = G⁰.m-zl (λ y → proj₁ (F β y)) (mono (nd s h) o r B zero (z≤ (nd s h)) β) mb x

  chain-law : ∀ a (p : Pos (nd s h)) ν → GR.Nu (nd s h) p ν → E.cof a ≡ E.cΩ ν
    → (g : Br (nd s h) p → Tr (nd s h)) → W (nd s h) (Ω p g)
    → (∀ η c → GR.Low (nd s h) p η c → GR.R (nd s h) (E.fsT a η) (g c))
    → ∀ n → GR.Low (nd s h) p (E.γT (t ++ a) ν n) (D.chain (nd s h) o r B p g (suc n))
  chain-law a p ν nu e g d hg zero = st o r B gb t a p ν nu e g d
  chain-law a p ν nu e g d hg (suc n) = sp o r B gb t a p ν nu e g d n
    (chain-law a p ν nu e g d hg n)
    (hg (E.γT (t ++ a) ν n) _ (chain-law a p ν nu e g d hg n))

  LF : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → ∀ {a x} → W (nd s h) x → GR.R (nd s h) a x
    → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (F β x))
  LF β mb d (mz {x = x}) = ++[] (λ z → M⁰ (ψᴺ 0 z) (proj₁ (F β x))) t (Fz β mb x)
  LF β mb d (m1 {t = a} {x = x} e m) =
    G⁰.m-next (F β x) (cofψ1 [] (t ++ a) (cof++1 t a e))
      (λ n → trans (fsnψ1 [] (t ++ a) n (cof++1 t a e))
        (cong (λ z → replicate n (E.ψ [] z)) (pred++ t a e))) (LF β mb (D.suc-inv d) m)
  LF β mb d (mL {t = a} {x = x} e m) =
    mL (cofψω [] (t ++ a) (cof++ω t a e))
      (λ n → subst (λ z → M⁰ z (proj₁ (F β x)))
        (sym (trans (fsnψω [] (t ++ a) n (cof++ω t a e)) (cong (ψᴺ 0) (fsn++ t a n e))))
        (LF β mb d (m n)))
  LF β mb d (mΩ {t = a} {ν = ν} {p = p} {g = g} e nu m) =
    nodeZ (kp (nd s h) o p (z≤ (nd s h))) (λ Z → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ Z))
      (λ c → F β (g c)) (feedᴰ (nd s h) o r B p g)
      (mL (cofG [] (t ++ a) (gt0 ν) (cof++Ω t a e))
        (λ n → subst
          (λ z → M⁰ z (proj₁ (limc⁺ (λ k → F β (g (D.chain (nd s h) o r B p g k))))))
          (sym (trans (fsnG [] (t ++ a) n (gt0 ν) (cof++Ω t a e))
            (cong (ψᴺ 0) (fsT++ t a (E.γT (t ++ a) ν n) e))))
          (G⁰.m-cum (λ k → F β (g (D.chain (nd s h) o r B p g k))) (suc n)
            (LF β mb (D.visit (nd s h) o r B (ok-tree {ℓ = nd s h} {B = B} gb) p g d (suc n))
              (m (E.γT (t ++ a) ν n) _ (chain-law a p ν nu e g d m n))))))
  LF β mb d (mU {t = a} {s = b} {x = x} {c = c} {y = y} {e = ey} m ch) =
    subst (λ z → M⁰ (ψᴺ 0 z) (proj₁ (F β (up x c y ey)))) (++-assoc t a b)
      (kid c (proj₂ o c) (proj₂ r c) _ (updated-ok s h o r B gb x c) (t ++ a) (F β x)
        (LF β mb (D.below d (◃u x c y ey)) m) (D.child d) ch)
  LF β mb d (mw m e) = mw (LF β mb (D.below d e) m) (mono (nd s h) o r B zero (z≤ (nd s h)) β e)
  LF β mb d (mc le m) = mc (app≤ 0 t le) (LF β mb d m)

pres-zero : Presᵂ zero
pres-zero o r B gb t β mb d m = self-zero o r B gb t β mb m

start-zero : Startᵂ zero
start-zero o r B gb t a ()

step-zero : Stepᵂ zero
step-zero o r B gb t a ()

fromSlots : (∀ ℓ → Startᵂ ℓ) → (∀ ℓ → Stepᵂ ℓ) → ∀ ℓ → Presᵂ ℓ
fromSlots st sp zero = pres-zero
fromSlots st sp (nd s h) = Fold.LF s h (λ c → fromSlots st sp (h c)) (st (nd s h)) (sp (nd s h))

slots→lowKeepᵂ : (∀ ℓ → Startᵂ ℓ) → (∀ ℓ → Stepᵂ ℓ) → Laws.LowKeep gradedᵍ domsᵍ
slots→lowKeepᵂ st sp {ℓ} (o , r , B) .(z≤ ℓ) β t rb wz (mb , gb) gx m =
  fromSlots st sp ℓ o r B gb t β mb (subst (W ℓ) (sym gx) (D.root ℓ)) m

start-from-full : ∀ ℓ → StartU ℓ → Startᵂ ℓ
start-from-full ℓ st o r B gb t a p ν nu e g d = st o r B gb t a p ν nu e g

step-from-full : ∀ ℓ → StepU ℓ → Stepᵂ ℓ
step-from-full ℓ sp o r B gb t a p ν nu e g d n = sp o r B gb t a p ν nu e g n (D.chain ℓ o r B p g (suc n))

steps→lowKeepᵂ : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → Stepᵂ ℓ) → Laws.LowKeep gradedᵍ domsᵍ
steps→lowKeepᵂ lf sp = slots→lowKeepᵂ (λ ℓ → start-from-full ℓ (start-from-leaf lf ℓ)) sp
```
