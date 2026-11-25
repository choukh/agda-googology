# 一般目标各行的统一保持
验收文件（读记号）；推导归纳据 `YiLKFold.Fold.LF`，嵌入各分支逐条使用现有 `YiTBRow.ψ`。
额外条件为 `IndexOK`、`PrefixU` 和每层的槽位保持、补前缀步进；条件的实例另交。
比较表缺项的指定孩子路径由 `IndexOK` 排除，不称任意路径保持；不用 Leaf。
入口：`pres`、`Fold.LF`、`Fold.emb-row`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (subst)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono; dW)
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiLKIface using (OK; updated-ok)
open import OCF.Lean.YiSUIface using (PrefixU; StepU′)
open import OCF.Lean.YiGTGen
open import OCF.Lean.YiGTNode using (NodeFrame; module Row)
open import OCF.Lean.YiGTIndex
open import OCF.Lean.YiGTUp using (UpFrame; up-pres)
import OCF.Lean.YiGTSelf as S
import OCF.Lean.YiGTEmb as Emb
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

pres-zero : PresAt zero
pres-zero o r B gb t pref .zero self ν idx = S.zero-self o r B t ν

module Fold (s : Sh) (h : Ch s → L) (child : (c : Ch s) → PresAt (h c))
  (sp : SlotPres (nd s h)) (st : StepU′ (nd s h))
  (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (gb : OK B)
  (t : E.T) (pref : PrefixU B t) where

  F : ∀ j → j ≤ nd s h → Tr⁺ j → Tr (nd s h) → Tr⁺ j
  F j w β x = ψ (nd s h) o r B j w β x

  cb : (x : Tr (nd s h)) (c : Ch s) → Base (h c)
  cb x c i u = ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x

  LF : ∀ j (w : j ≤ nd s h) ν → IndexOK (nd s h) o r j w ν
    → (β : Tr⁺ j) → GR.R j (E.ψ ν t ∷ []) (proj₁ β)
    → ∀ {a x} → GR.R (nd s h) a x
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F j w β x))
  LF j w ν idx β mb (H.mz {x = x}) =
    ++[] (λ z → GR.R j (E.ψ ν z ∷ []) (proj₁ (F j w β x))) t
      (zlᴿ j (λ y → proj₁ (F j w β y)) (mono (nd s h) o r B j w β) mb x)
  LF j w ν idx β mb (H.m1 {t = a} {x = x} e m) =
    nextψ j ν t a e (F j w β x) (LF j w ν idx β mb m)
  LF j w ν idx β mb (H.mL {t = a} {x = x} e m) =
    limψ j ν t a e (proj₁ (F j w β x)) (λ n → LF j w ν idx β mb (m n))
  LF j w ν idx β mb (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
    Row.node-row (nd s h) j o r B w ν t gb pref st β (proj₁ idx)
      p g e nu m (λ η c lc → LF j w ν idx β mb (m η c lc))
  LF j w ν idx β mb (H.mU {t = a} {s = b} {x = x} {c = c} {y = y} {e = ey} m ch) =
    subst (λ z → GR.R j (E.ψ ν z ∷ []) (proj₁ (F j w β (up x c y ey)))) (++-assoc t a b)
      (Emb.emb-row s h child o r B gb t pref j w ν idx β c y ey m (shift-prefix s h sp o r B gb t pref m) (LF j w ν idx β mb m) ch)
  LF j w ν idx β mb (H.mw m d) = weakᴿ j (LF j w ν idx β mb m) (mono (nd s h) o r B j w β d)
  LF j w ν idx β mb (H.mc le m) = closeᴿ j (app≤ν ν t le) (LF j w ν idx β mb m)

pres : ∀ ℓ → Kit ℓ → PresAt ℓ
pres zero k = pres-zero
pres (nd s h) (sp , st , ks) o r B gb t pref =
  Fold.LF s h (λ c → pres (h c) (ks c)) sp st o r B gb t pref
```
