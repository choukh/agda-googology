# 第 0 层读回延伸保留一个已证下界
验收文件，读记号；编译条件定理：任意偏移上的已有 Ω 折叠下界，沿指定读回路径保留。
前提 At 仍须实填；YiBVSmall 的 at-two 给出非空实例，YiBVZero 在全孩子域使用它。
不声称一般跨层单调、随记号后继提高下界或 BranchNeed；树、折叠、合法性不变。
来源：Succ.liftU 将 YiTBFam.liftU 的同一证明变量化；Limit.liftLn 取指定累计分支。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBVReadBound where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiRBFam as RF
open import OCF.Lean.YiKCStep using (⊴-trans)
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiCLLow as L
import OCF.Align.EboLeanDef as E
Bound : (t : E.T) (a : B.L) → P.Ok a → TB.Rb a → P._≤_ K.one a → Set
Bound t a o r v = (base : F.Base a) (beta : O.Tr⁺ K.one) → RF.OKB base
  → H.M 1 (E.Ωt (E.natT 1)) (proj₁ beta)
  → H.M 1 t (proj₁ (TB.ψ a o r base K.one v beta (proj₁ (O.Ωt a))))
At : E.T → (a : B.L) → P._≤_ K.one a → Set
At t a v = ∀ o r → Bound t a o r v
module Succ (a : B.L) (o : P.Ok (B.nd B.sS (λ _ → a)))
  (r : TB.Rb (B.nd B.sS (λ _ → a))) (v : P._≤_ K.one a) where
  layer = B.nd B.sS (λ _ → a)
  cb : F.Base layer → F.Base a
  cb base i u = base i (P.inc tt u)
  liftU : ∀ {t} → Bound t a (proj₂ o tt) (proj₂ r tt) v
    → Bound t layer o r (P.inu (λ _ → v))
  liftU s base beta ok hb =
    L.cumJ 1 (λ k → O.next⁺ (TB.ψ a (proj₂ o tt) (proj₂ r tt) (cb base) K.one v beta
      (O.iter (λ z → proj₁ (O.next⁺ (TB.ψ a (proj₂ o tt) (proj₂ r tt) (cb base) a P.self
        (base a (P.inc tt P.self)) z))) B.zero k))) 1
      (H.mwN 1 (H.mwN 1 (s (cb base) beta (λ i u → ok i (P.inc tt u)) hb)
        (TB.mono a (proj₂ o tt) (proj₂ r tt) (cb base) K.one v beta
          (K.⊴-◃ (ok a (P.inc tt P.self)) (B.◃l zero)))) (B.◃l zero))
module Limit (g : ℕ → B.L) (o : P.Ok (B.nd B.sL g))
  (r : TB.Rb (B.nd B.sL g)) (v : ∀ n → P._≤_ K.one (g n)) where
  layer : B.L
  layer = B.nd B.sL g
  part : ℕ → B.Tr layer
  part = O.cum (λ n → proj₁ (O.upz n (O.Ωt (g n))))
  advance : F.Base layer → (n : ℕ) → B.Tr layer → F.Base (g n)
  advance base n x i u = TB.ψ layer o r base i (P.inc n u) (base i (P.inc n u)) x
  liftLn : ∀ n {t} → Bound t (g n) (proj₂ o n) (proj₂ r n) (v n)
    → Bound t layer o r (P.inu v)
  liftLn zero s base beta ok hb = H.mwN 1
    (s (λ i u → base i (P.inc zero u)) beta (λ i u → ok i (P.inc zero u)) hb) (B.◃l zero)
  liftLn (suc n) s base beta ok hb = H.mwN 1
    (s (advance base (suc n) (part n))
      (TB.ψ layer o r base K.one (P.inu v) beta (part n))
      (λ i u → ⊴-trans (ok i (P.inc (suc n) u))
        (TF.ψ-⊵ layer o r base i (P.inc (suc n) u) (base i (P.inc (suc n) u)) (part n)))
      (H.m⊴N 1 hb (TF.ψ-⊵ layer o r base K.one (P.inu v) beta (part n)))) (B.◃l (suc n))
extend : ∀ t a (v : P._≤_ K.one a) → At t a v → (d : B.Tr B.zero)
  → At t (a B.⊕ B.↑ B.zero d) (v P.∙ P.lift a (B.↑ B.zero d))
extend t a v anchor B.zero = anchor
extend t a v anchor (B.suc d) o r = Succ.liftU (a B.⊕ B.↑ B.zero d) o r
  (v P.∙ P.lift a (B.↑ B.zero d)) (extend t a v anchor d (proj₂ o tt) (proj₂ r tt))
extend t a v anchor (B.lim f s) o r = Limit.liftLn (λ n → a B.⊕ B.↑ B.zero (f n)) o r
  (λ n → v P.∙ P.lift a (B.↑ B.zero (f n))) zero (extend t a v anchor (f zero) (proj₂ o zero) (proj₂ r zero))
extend t a v anchor (B.Ω () _)
extend t a v anchor (B.up _ () _ _)
canonical-mono : ∀ t a (v : P._≤_ K.one a) {x y : B.Tr B.zero}
  → B._⊢_◃_ B.zero x y
  → At t (a B.⊕ B.↑ B.zero x) (v P.∙ P.lift a (B.↑ B.zero x))
  → At t (a B.⊕ B.↑ B.zero y) (v P.∙ P.lift a (B.↑ B.zero y))
canonical-mono t a v (B.◃s {x = x}) old o r = Succ.liftU (a B.⊕ B.↑ B.zero x) o r
  (v P.∙ P.lift a (B.↑ B.zero x)) (old (proj₂ o tt) (proj₂ r tt))
canonical-mono t a v (B.◃l {f = f} n) old o r = Limit.liftLn
  (λ n → a B.⊕ B.↑ B.zero (f n)) o r (λ n → v P.∙ P.lift a (B.↑ B.zero (f n))) n
  (old (proj₂ o n) (proj₂ r n))
canonical-mono t a v (B.◃w {p = ()}) old
canonical-mono t a v (B.◃u _ () _ _) old
canonical-mono t a v (B.◃c _ () _) old
canonical-mono t a v (B.◃t {x = x} {y = y} {z = z} d e) old =
  canonical-mono t a v {x = y} {y = z} e (canonical-mono t a v {x = x} {y = y} d old)
extend-presented : ∀ t a (v : P._≤_ K.one a) → At t a v → (d : B.Tr B.zero)
  → (layer : B.L) → (eq : layer ≡ a B.⊕ B.↑ B.zero d)
  → At t layer (subst (P._≤_ K.one) (sym eq) (v P.∙ P.lift a (B.↑ B.zero d)))
extend-presented t a v anchor d .(a B.⊕ B.↑ B.zero d) refl = extend t a v anchor d
```
