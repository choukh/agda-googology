# LF 的非结点分支不依赖有限源层号
验收文件，读记号；编译定理：任意源层的零、后继、ℕ 极限与松弛分支，以及嵌入的零层输入。
来源：YiTBFam.LF 的 mz、m1、mL、mw 分支；目标固定第 1 层，源层、表、底与路径取变量。
未处理实际内链里的 Ω 与 up，不声称 YiQLRead.Step；实际首个未填行见 YiSQOmega。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSQLF where
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiCLLow as L
import OCF.Lean.YiMENote as N
import OCF.Align.EboLeanDef as E
module Fold (ell : B.L) (o : P.Ok ell) (r : TB.Rb ell) (base : F.Base ell)
  (w : P._≤_ K.one ell) (beta : O.Tr⁺ K.one) (prefix : E.T) where
  image : B.Tr ell → O.Tr⁺ K.one
  image = TB.ψ ell o r base K.one w beta
  Holds : E.T → B.Tr ell → Set
  Holds a x = H.M 1 (E.ψ (E.natT 1) (prefix ++ a) ∷ []) (proj₁ (image x))
  successor : ∀ {a x} → E.cof a ≡ E.c1 → Holds (E.pred a) x → Holds a (B.suc x)
  successor {a} {x} e ih = L.nextJ 1 (image x)
    (N.cofψ1 (E.natT 1) (prefix ++ a) (N.cof++1 prefix a e))
    (λ k → trans (N.fsnψ1 (E.natT 1) (prefix ++ a) k (N.cof++1 prefix a e))
      (cong (λ q → replicate k (E.ψ (E.natT 1) q)) (N.pred++ prefix a e))) ih
  initial : H.M 1 (E.ψ (E.natT 1) prefix ∷ []) (proj₁ beta) → ∀ x → Holds [] x
  initial hb x = K.++[] (λ q → H.M 1 (E.ψ (E.natT 1) q ∷ []) (proj₁ (image x))) prefix
    (L.zlJ 1 (λ y → proj₁ (image y)) (TB.mono ell o r base K.one w beta) hb x)
  limit : ∀ {a x} → E.cof a ≡ E.cω → (∀ n → Holds (E.fsn a n) x) → Holds a x
  limit {a} {x} e ih = K.mL (N.cofψω (E.natT 1) (prefix ++ a) (N.cof++ω prefix a e))
    (λ n → subst (λ q → H.M 1 q (proj₁ (image x)))
      (sym (trans (N.fsnψω (E.natT 1) (prefix ++ a) n (N.cof++ω prefix a e))
        (cong (λ q → E.ψ (E.natT 1) q ∷ []) (N.fsn++ prefix a n e)))) (ih n))
  weak : ∀ {a x y} → B._⊢_◃_ ell x y → Holds a x → Holds a y
  weak e m = H.mwN 1 m (TB.mono ell o r base K.one w beta e)
  countable : H.M 1 (E.ψ (E.natT 1) prefix ∷ []) (proj₁ beta)
    → ∀ {a d} → K.M⁰ a d → Holds a (O.ι ell d)
  countable hb (K.mz {x = d}) = initial hb (O.ι ell d)
  countable hb (K.m1 e m) = successor e (countable hb m)
  countable hb (K.mL e h) = limit e (λ n → countable hb (h n))
  countable hb (K.mΩ {p = ()} _ _ _)
  countable hb (K.mU {c = ()} _ _)
  countable hb (K.mw m e) = weak (O.ι-mono ell e) (countable hb m)
```
