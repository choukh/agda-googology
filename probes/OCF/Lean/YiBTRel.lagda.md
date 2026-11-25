# 换基候选在无 Ω 子层上的对应
验收文件；NoΩ 层及其上的单个 Ω 结点与既有 F2 块对应，不含嵌套 Ω 子层。
来源：YiMTRel 的 A/S/Am/Sm 与 topΩ 证明搬用，折叠改成 YiBSFold。
前提已在 <实验目录> 的 Premises 实填；不涉及换基地板以上的行，也不宣称第 1 项。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBTRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; kp⁼; node⁺; nodeLe)
open import OCF.Lean.YiBSBase using (Rb)
open import OCF.Lean.YiBSFold using (ψ; mono)
open import OCF.Lean.YiNRHit using (NoΩ)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem
open import OCF.Lean.YiBROps
open import OCF.Lean.YiBRFold using (W→L; B₀-R; iterR; node0; nodeLe0; kp-R)

-- perf: S-1/C-10，互递归对应证明出生处封装，外部只使用规格。
opaque
  mutual
    A : ∀ {ℓ ℓ′ o ε ρ} {tb : Rb ℓ} → RelE ℓ ℓ′ o ε ρ → NoΩ ℓ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
      → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
      → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
      → RelT zero F.zero (proj₁ (ψ ℓ o tb B zero (z≤ ℓ) β x)) (F.ψ⊥ ℓ′ ε ρ B′ x′)
      × RelD zero F.zero (proj₂ (ψ ℓ o tb B zero (z≤ ℓ) β x)) (F.nz⊥ ℓ′ ε ρ B′ x′)
    A {tb = tb} re nq B B′ rB β rβ rn {x = zero} iz = rβ , rn
    A {ℓ} {o = o} {tb = tb} re nq B B′ rB β rβ rn {x = suc x} (is r) =
      let u = A re nq B B′ rB β rβ rn r in next-R (ψ ℓ o tb B zero (z≤ ℓ) β x) (proj₁ u) (proj₂ u)
    A {tb = tb} re nq B B′ rB β rβ rn {x = lim f a} (il (rf , ra)) =
      il ((λ n → proj₁ (A re nq B B′ rB β rβ rn (rf n))) , (λ n → Am re nq B B′ rB β rβ rn (ra n)))
      , dt (proj₂ (A re nq B B′ rB β rβ rn (rf zero)) , dl)
    A {ℓ} {ℓ′} {o} {ε} {ρ} {tb = tb} re nq B B′ rB β rβ rn {x = Ω p g} {x′ = F.Ω p′ g′} (iw (rp , rg)) =
      node0 (kp ℓ o p (z≤ ℓ)) (λ z → ψ ℓ o tb B zero (z≤ ℓ) β (g z)) sR
        (limc-R (λ n → ψ ℓ o tb B zero (z≤ ℓ) β (g (iter sR (fromBr ℓ p zero) n)))
           (λ n → proj₁ (A re nq B B′ rB β rβ rn (rg _ _ (ch n)))) (λ n → proj₂ (A re nq B B′ rB β rβ rn (rg _ _ (ch n))))
         , dt (proj₂ (A re nq B B′ rB β rβ rn (rg _ _ (ch zero))) , dl))
      where
      rl : RelL ℓ ℓ′
      rl = E→L re
      sR : Br ℓ p → Br ℓ p
      sR z = fromBr ℓ p (proj₁ (ψ ℓ o tb B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
      s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
      s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
                  (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
      rb : RelT (at ℓ p) (F.at ℓ′ p′) (proj₁ (B (at ℓ p) (posW ℓ p)))
             (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
         × RelD (at ℓ p) (F.at ℓ′ p′) (proj₂ (B (at ℓ p) (posW ℓ p)))
             (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
      rb = rB (at ℓ p) (F.at ℓ′ p′) (posW ℓ p) (F.posW ℓ′ p′) (posW-R rl p p′ rp)
      ch : (n : ℕ) → RelB ℓ ℓ′ p p′ (iter sR (fromBr ℓ p zero) n) (F.iter s′R (F.br0 ℓ′ p′) n)
      ch = iterR (RelB ℓ ℓ′ p p′) (br0-R rl p p′ rp)
             (λ z z′ rz → fromBr-R rl p p′ rp
                (proj₁ (S re nq B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (rg z z′ rz))))
    A {o = o} {ε} {ρ} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
      let u = A re₀ nq B B′ rB β rβ rn rx
      in A re (nq c) (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ nq B B′ rB rx c)
           (ψ (nd sS h) o tb B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) ry
    A {o = o} {ε} {ρ} {tb = tb} re₀@(eL {g = g} {g′ = g′} rr re) nq B B′ rB β rβ rn {x = up x n y e} {x′ = F.up x′ n′ y′ e′} (iu (rx , (refl , ry , _))) =
      let u = A re₀ nq B B′ rB β rβ rn rx
      in A (re n) (nq n) (λ i w → ψ (nd sL g) o tb B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cL re₀ nq B B′ rB rx n)
           (ψ (nd sL g) o tb B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) ry
    A (eΩ _ _ _) ()

    Am : ∀ {ℓ ℓ′ o ε ρ} {tb : Rb ℓ} → RelE ℓ ℓ′ o ε ρ → NoΩ ℓ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
       → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
       → {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} {d : ℓ ⊢ x ◃ y} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′
       → RelD zero F.zero (mono ℓ o tb B zero (z≤ ℓ) β d) (F.mono⊥ ℓ′ ε ρ B′ d′)
    Am {tb = tb} re nq B B′ rB β rβ rn {d = ◃s} ds = dl
    Am {tb = tb} re nq B B′ rB β rβ rn {d = ◃l n} dl = dl
    Am {ℓ} {o = o} {tb = tb} re nq B B′ rB β rβ rn {d = ◃w {p = p}} (dw _) = nodeLe0 (kp ℓ o p (z≤ ℓ)) _ _ dl
    Am {o = o} {ε} {ρ} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
      let u = A re₀ nq B B′ rB β rβ rn rx
      in Am re (nq c) (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ nq B B′ rB rx c)
           (ψ (nd sS h) o tb B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) rye
    Am {o = o} {ε} {ρ} {tb = tb} re₀@(eL {g = g} {g′ = g′} rr re) nq B B′ rB β rβ rn {d = ◃u x n y e} {d′ = F.◃u x′ n′ y′ e′} (du (rx , (refl , ry , rye))) =
      let u = A re₀ nq B B′ rB β rβ rn rx
      in Am (re n) (nq n) (λ i w → ψ (nd sL g) o tb B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cL re₀ nq B B′ rB rx n)
           (ψ (nd sL g) o tb B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) rye
    Am (eΩ _ _ _) ()
    Am {o = o} {ε} {ρ} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
      let u = A re₀ nq B B′ rB β rβ rn rx
      in Am re (nq c) (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ nq B B′ rB rx c)
           (ψ (nd sS h) o tb B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) rr
    Am {o = o} {ε} {ρ} {tb = tb} re₀@(eL {g = g} {g′ = g′} rr₀ re) nq B B′ rB β rβ rn {d = ◃c x n r} {d′ = F.◃c x′ n′ r′} (dc (rx , (refl , rr))) =
      let u = A re₀ nq B B′ rB β rβ rn rx
      in Am (re n) (nq n) (λ i w → ψ (nd sL g) o tb B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cL re₀ nq B B′ rB rx n)
           (ψ (nd sL g) o tb B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) rr
    Am {tb = tb} re nq B B′ rB β rβ rn {d = ◃t d₁ d₂} (dt (r₁ , r₂)) = dt (Am re nq B B′ rB β rβ rn r₁ , Am re nq B B′ rB β rβ rn r₂)

    S : ∀ {ℓ ℓ′ o ε ρ} {tb : Rb ℓ} → RelE ℓ ℓ′ o ε ρ → NoΩ ℓ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
      → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
      → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
      → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
      → RelT j j′ (proj₁ (ψ ℓ o tb B j w β x)) (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
      × RelD j j′ (proj₂ (ψ ℓ o tb B j w β x)) (F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
    S {tb = tb} re nq B B′ rB rw β rβ rn {x = zero} iz = rβ , rn
    S {ℓ} {o = o} {tb = tb} re nq B B′ rB {j} {w = w} rw β rβ rn {x = suc x} (is r) =
      let u = S re nq B B′ rB rw β rβ rn r in next-R (ψ ℓ o tb B j w β x) (proj₁ u) (proj₂ u)
    S {tb = tb} re nq B B′ rB rw β rβ rn {x = lim f a} (il (rf , ra)) =
      il ((λ n → proj₁ (S re nq B B′ rB rw β rβ rn (rf n))) , (λ n → Sm re nq B B′ rB rw β rβ rn (ra n)))
      , dt (proj₂ (S re nq B B′ rB rw β rβ rn (rf zero)) , dl)
    S {ℓ} {ℓ′} {o} {ε} {ρ} {tb = tb} re nq B B′ rB {j} {j′} {w} {w′} rw β {β′} {nβ} rβ rn {x = Ω p g} {x′ = F.Ω p′ g′} (iw (rp , rg)) =
      kp-R re p p′ rp rw (λ Z → F._⊢_◃_ j′ F.zero Z) K d hk hd
        (λ m z qz → RelT j j′ (proj₁ (node⁺ m G sR)) z × RelD j j′ (proj₂ (node⁺ m G sR)) qz)
        (λ q q′ rq cv cv′ g₀ gd rcv →
           iw (rq , λ z z′ rz → proj₁ (S re nq B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz))))
           , dt (proj₂ (S re nq B B′ rB rw β rβ rn (rg _ _ (rcv _ _ (br0-R (W→L rl rw) q q′ rq))))
                , dw (rq , λ z z′ rz → proj₁ (S re nq B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz))))))
        (limc-R (λ n → G (iter sR (fromBr ℓ p zero) n))
           (λ n → proj₁ (S re nq B B′ rB rw β rβ rn (rg _ _ (ch n)))) (λ n → proj₂ (S re nq B B′ rB rw β rβ rn (rg _ _ (ch n))))
         , dt (proj₂ (S re nq B B′ rB rw β rβ rn (rg _ _ (ch zero))) , dl))
      where
      rl : RelL ℓ ℓ′
      rl = E→L re
      G : Br ℓ p → Tr⁺ j
      G z = ψ ℓ o tb B j w β (g z)
      sR : Br ℓ p → Br ℓ p
      sR z = fromBr ℓ p (proj₁ (ψ ℓ o tb B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
      s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
      s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
                  (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
      K : (q : F.Pos j′) → (F.Br j′ q → F.Br ℓ′ p′) → F.Tr j′
      K q cv = F.Ω q (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv z)))
      d : F.Tr j′
      d = F.limc (λ n → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.iter s′R (F.br0 ℓ′ p′) n)))
                 (λ n → F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.iter s′R (F.br0 ℓ′ p′) n)))
      hk : (q : F.Pos j′) (cv : F.Br j′ q → F.Br ℓ′ p′) → F.Good ℓ′ p′ j′ q cv → F._⊢_◃_ j′ F.zero (K q cv)
      hk q cv gd = F.◃t (F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv (F.br0 j′ q)))) F.◃w
      hd : F._⊢_◃_ j′ F.zero d
      hd = F.◃t (F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.br0 ℓ′ p′))) (F.◃l zero)
      rb : RelT (at ℓ p) (F.at ℓ′ p′) (proj₁ (B (at ℓ p) (posW ℓ p)))
             (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
         × RelD (at ℓ p) (F.at ℓ′ p′) (proj₂ (B (at ℓ p) (posW ℓ p)))
             (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
      rb = rB (at ℓ p) (F.at ℓ′ p′) (posW ℓ p) (F.posW ℓ′ p′) (posW-R rl p p′ rp)
      ch : (n : ℕ) → RelB ℓ ℓ′ p p′ (iter sR (fromBr ℓ p zero) n) (F.iter s′R (F.br0 ℓ′ p′) n)
      ch = iterR (RelB ℓ ℓ′ p p′) (br0-R rl p p′ rp)
             (λ z z′ rz → fromBr-R rl p p′ rp
                (proj₁ (S re nq B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (rg z z′ rz))))
    -- 自身行
    S {o = o} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB wself β rβ rn {x = up x c y e} (iu (rx , (ry , _))) =
      let u = S re₀ nq B B′ rB wself β rβ rn rx
      in Up-R (lS (E→L re)) (E→L re) (ddown (lS (E→L re)) dstop tt) (ψ (nd sS h) o tb B (nd sS h) self β x) (proj₁ u) (proj₂ u) ry
    S {o = o} {tb = tb} re₀@(eL {g = g} rr re) nq B B′ rB wself β rβ rn {x = up x n y e} (iu (rx , (refl , ry , _))) =
      let u = S re₀ nq B B′ rB wself β rβ rn rx
      in Up-R (lL (λ i → E→L (re i))) (E→L (re n)) (ddown (lL (λ i → E→L (re i))) dstop refl)
           (ψ (nd sL g) o tb B (nd sL g) self β x) (proj₁ u) (proj₂ u) ry
    S (eΩ _ _ _) ()
    -- 一致路径, 下标层侧, 后继形状进孩子 c
    S {o = o} {ε} {ρ} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
      let u = S re₀ nq B B′ rB (winuS rw) β rβ rn rx
      in S re (nq c) (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ nq B B′ rB rx c)
           rw (ψ (nd sS h) o tb B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
    S {o = o} {ε} {ρ} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
      let u = S re₀ nq B B′ rB (wincS rv) β rβ rn rx
      in S re (nq c) (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ nq B B′ rB rx c)
           rv (ψ (nd sS h) o tb B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) ry
    S {o = o} {ε} {ρ} {tb = tb} re₀@(eL {g = g} {g′ = g′} rr re) nq B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {x = up x m y e} {x′ = F.up x′ m′ y′ e′} (iu (rx , (refl , ry , _))) =
      let u = S re₀ nq B B′ rB (winuL rws) β rβ rn rx
      in S (re m) (nq m) (λ i w → ψ (nd sL g) o tb B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cL re₀ nq B B′ rB rx m)
           (rws m) (ψ (nd sL g) o tb B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
    -- ℕ 极限形状: 比较孩子编号
    S {o = o} {ε} {ρ} {tb = tb} re₀@(eL {g = g} {g′ = g′} rr re) nq B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {x = up x m y e} {x′ = F.up x′ m′ y′ e′} (iu (rx , (refl , ry , rye)))
      with S re₀ nq B B′ rB rw₀ β rβ rn rx | cL re₀ nq B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
    ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
      S (re n) (nq n) (λ i w → ψ (nd sL g) o tb B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
        rv (ψ (nd sL g) o tb B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (proj₁ (emb-R (re n) ru (y , e) ry rye))
    ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
      S (re m) (nq m) (λ i w → ψ (nd sL g) o tb B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
        (∙-R rv ru) (ψ (nd sL g) o tb B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) ry

    Sm : ∀ {ℓ ℓ′ o ε ρ} {tb : Rb ℓ} → RelE ℓ ℓ′ o ε ρ → NoΩ ℓ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
       → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
       → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
       → {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} {d : ℓ ⊢ x ◃ y} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′
       → RelD j j′ (mono ℓ o tb B j w β d) (F.monos ℓ′ ε ρ B′ j′ w′ β′ nβ d′)
    Sm {tb = tb} re nq B B′ rB rw β rβ rn {d = ◃s} ds = dl
    Sm {tb = tb} re nq B B′ rB rw β rβ rn {d = ◃l n} dl = dl
    Sm {ℓ} {ℓ′} {o} {ε} {ρ} {tb = tb} re nq B B′ rB {j} {j′} {w} {w′} rw β {β′} {nβ} rβ rn {d = ◃w {p = p} {g = g}} {d′ = F.◃w {p = p′} {g = g′}} (dw (rp , rg)) =
      kp-R re p p′ rp rw Q K d hk hd (λ m z qz → RelD j j′ (nodeLe m G sR) qz)
        (λ q q′ rq cv cv′ g₀ gd rcv →
           RelD-substˡ (λ t → proj₁ (G t)) (λ _ → Ω q (λ z → proj₁ (G (cv z)))) g₀
             (RelD-substʳ (λ t → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ t)) (λ _ → F.Ω q′ (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv′ z)))) gd
               (dw (rq , λ z z′ rz → proj₁ (S re nq B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz)))))))
        dl
      where
      G : Br ℓ p → Tr⁺ j
      G z = ψ ℓ o tb B j w β (g z)
      sR : Br ℓ p → Br ℓ p
      sR z = fromBr ℓ p (proj₁ (ψ ℓ o tb B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
      s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
      s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
                  (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
      K : (q : F.Pos j′) → (F.Br j′ q → F.Br ℓ′ p′) → F.Tr j′
      K q cv = F.Ω q (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv z)))
      d : F.Tr j′
      d = F.limc (λ n → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.iter s′R (F.br0 ℓ′ p′) n)))
                 (λ n → F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.iter s′R (F.br0 ℓ′ p′) n)))
      Q : F.Tr j′ → Set
      Q Z = F._⊢_◃_ j′ (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.br0 ℓ′ p′))) Z
      hk : (q : F.Pos j′) (cv : F.Br j′ q → F.Br ℓ′ p′) → F.Good ℓ′ p′ j′ q cv → Q (K q cv)
      hk q cv gd = subst (λ t → F._⊢_◃_ j′ (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ t)) (F.Ω q (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv z))))) gd F.◃w
      hd : Q d
      hd = F.◃l zero
    -- 自身行
    Sm {o = o} {tb = tb} re₀@(eS {h = h} re) nq B B′ rB wself β rβ rn {d = ◃u x c y e} (du (rx , (ry , rye))) =
      let u = S re₀ nq B B′ rB wself β rβ rn rx
      in Upm-R (lS (E→L re)) (E→L re) (ddown (lS (E→L re)) dstop tt) (ψ (nd sS h) o tb B (nd sS h) self β x) (proj₁ u) (proj₂ u) rye
    Sm {o = o} {tb = tb} re₀@(eL {g = g} rr re) nq B B′ rB wself β rβ rn {d = ◃u x n y e} (du (rx , (refl , ry , rye))) =
      let u = S re₀ nq B B′ rB wself β rβ rn rx
      in Upm-R (lL (λ i → E→L (re i))) (E→L (re n)) (ddown (lL (λ i → E→L (re i))) dstop refl)
           (ψ (nd sL g) o tb B (nd sL g) self β x) (proj₁ u) (proj₂ u) rye
    Sm (eΩ _ _ _) ()
    Sm {o = o} {tb = tb} re₀@(eS {h = h} re) nq B B′ rB wself β rβ rn {d = ◃c x c r} (dc (rx , rr)) =
      let u = S re₀ nq B B′ rB wself β rβ rn rx
      in Upm-R (lS (E→L re)) (E→L re) (ddown (lS (E→L re)) dstop tt) (ψ (nd sS h) o tb B (nd sS h) self β x) (proj₁ u) (proj₂ u) rr
    Sm {o = o} {tb = tb} re₀@(eL {g = g} rr₀ re) nq B B′ rB wself β rβ rn {d = ◃c x n r} (dc (rx , (refl , rr))) =
      let u = S re₀ nq B B′ rB wself β rβ rn rx
      in Upm-R (lL (λ i → E→L (re i))) (E→L (re n)) (ddown (lL (λ i → E→L (re i))) dstop refl)
           (ψ (nd sL g) o tb B (nd sL g) self β x) (proj₁ u) (proj₂ u) rr
    -- 进孩子的各行 (◃u)
    Sm {o = o} {ε} {ρ} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
      let u = S re₀ nq B B′ rB (winuS rw) β rβ rn rx
      in Sm re (nq c) (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ nq B B′ rB rx c)
           rw (ψ (nd sS h) o tb B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
    Sm {o = o} {ε} {ρ} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
      let u = S re₀ nq B B′ rB (wincS rv) β rβ rn rx
      in Sm re (nq c) (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ nq B B′ rB rx c)
           rv (ψ (nd sS h) o tb B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) rye
    Sm {o = o} {ε} {ρ} {tb = tb} re₀@(eL {g = g} {g′ = g′} rr re) nq B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {d = ◃u x m y e} {d′ = F.◃u x′ m′ y′ e′} (du (rx , (refl , ry , rye))) =
      let u = S re₀ nq B B′ rB (winuL rws) β rβ rn rx
      in Sm (re m) (nq m) (λ i w → ψ (nd sL g) o tb B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cL re₀ nq B B′ rB rx m)
           (rws m) (ψ (nd sL g) o tb B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
    Sm {o = o} {ε} {ρ} {tb = tb} re₀@(eL {g = g} {g′ = g′} rr re) nq B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {d = ◃u x m y e} {d′ = F.◃u x′ m′ y′ e′} (du (rx , (refl , ry , rye)))
      with S re₀ nq B B′ rB rw₀ β rβ rn rx | cL re₀ nq B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
    ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
      Sm (re n) (nq n) (λ i w → ψ (nd sL g) o tb B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
        rv (ψ (nd sL g) o tb B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (proj₂ (emb-R (re n) ru (y , e) ry rye))
    ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
      Sm (re m) (nq m) (λ i w → ψ (nd sL g) o tb B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
        (∙-R rv ru) (ψ (nd sL g) o tb B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) rye
    -- 进孩子的各行 (◃c)
    Sm {o = o} {ε} {ρ} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
      let u = S re₀ nq B B′ rB (winuS rw) β rβ rn rx
      in Sm re (nq c) (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ nq B B′ rB rx c)
           rw (ψ (nd sS h) o tb B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
    Sm {o = o} {ε} {ρ} {tb = tb} re₀@(eS {h = h} {a = a} re) nq B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
      let u = S re₀ nq B B′ rB (wincS rv) β rβ rn rx
      in Sm re (nq c) (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ nq B B′ rB rx c)
           rv (ψ (nd sS h) o tb B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) rr
    Sm {o = o} {ε} {ρ} {tb = tb} re₀@(eL {g = g} {g′ = g′} rr₀ re) nq B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {d = ◃c x m r} {d′ = F.◃c x′ m′ r′} (dc (rx , (refl , rr))) =
      let u = S re₀ nq B B′ rB (winuL rws) β rβ rn rx
      in Sm (re m) (nq m) (λ i w → ψ (nd sL g) o tb B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cL re₀ nq B B′ rB rx m)
           (rws m) (ψ (nd sL g) o tb B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
    Sm {o = o} {ε} {ρ} {tb = tb} re₀@(eL {g = g} {g′ = g′} rr₀ re) nq B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {d = ◃c x m r} {d′ = F.◃c x′ m′ r′} (dc (rx , (refl , rr)))
      with S re₀ nq B B′ rB rw₀ β rβ rn rx | cL re₀ nq B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr₀ m n
    ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
      Sm (re n) (nq n) (λ i w → ψ (nd sL g) o tb B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
        rv (ψ (nd sL g) o tb B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (emb-mono-R (re n) ru rr)
    ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
      Sm (re m) (nq m) (λ i w → ψ (nd sL g) o tb B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
        (∙-R rv ru) (ψ (nd sL g) o tb B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) rr
    Sm {tb = tb} re nq B B′ rB rw β rβ rn {d = ◃t d₁ d₂} (dt (r₁ , r₂)) = dt (Sm re nq B B′ rB rw β rβ rn r₁ , Sm re nq B B′ rB rw β rβ rn r₂)

    cS : ∀ {h a o ε ρ} {tb : Rb (nd sS h)} → (re : RelE (nd sS h) (F.suc a) o ε ρ) → NoΩ (nd sS h) → (B : Base (nd sS h)) (B′ : F.Base (F.suc a))
       → RelBase (nd sS h) (F.suc a) B B′ → {x : Tr (nd sS h)} {x′ : F.Tr (F.suc a)} → RelT (nd sS h) (F.suc a) x x′ → (c : ⊤)
       → RelBase (h c) a (λ i w → ψ (nd sS h) o tb B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′)
    cS re nq B B′ rB rx c i i′ w w′ rw =
      let rb = rB i i′ (inc c w) (F.ins w′) (wincS rw) in S re nq B B′ rB (wincS rw) (B i (inc c w)) (proj₁ rb) (proj₂ rb) rx

    cL : ∀ {g g′ o ε ρ} {tb : Rb (nd sL g)} → (re : RelE (nd sL g) (F.lim g′) o ε ρ) → NoΩ (nd sL g) → (B : Base (nd sL g)) (B′ : F.Base (F.lim g′))
       → RelBase (nd sL g) (F.lim g′) B B′ → {x : Tr (nd sL g)} {x′ : F.Tr (F.lim g′)} → RelT (nd sL g) (F.lim g′) x x′ → (n : ℕ)
       → RelBase (g n) (g′ n) (λ i w → ψ (nd sL g) o tb B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′)
    cL re nq B B′ rB rx n i i′ w w′ rw =
      let rb = rB i i′ (inc n w) (F.inl n w′) (wincL n rw) in S re nq B B′ rB (wincL n rw) (B i (inc n w)) (proj₁ rb) (proj₂ rb) rx


data U0 {k : L} {h : Tr k → L} : Tr (nd (sΩ k) h) → Set where
  u0 : ∀ z y e → U0 (up zero z y e)

upA : ∀ {k h k′ h′ o ε ρ} {tb : Rb (nd (sΩ k) h)} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ → ((c : Tr k) → NoΩ (h c))
    → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′)) → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′
    → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
    → {x : Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)} → U0 x → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) x x′
    → RelT zero F.zero (proj₁ (ψ (nd (sΩ k) h) o tb B zero (z≤ (nd (sΩ k) h)) β x)) (F.ψ⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
    × RelD zero F.zero (proj₂ (ψ (nd (sΩ k) h) o tb B zero (z≤ (nd (sΩ k) h)) β x)) (F.nz⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
upA {k′ = k′} {h′} {ε = ε} {ρ} (eΩ rk rwc rc) nΩ B B′ rB β rβ rn {x′ = F.up _ c′ y′ e′} (u0 z y e) (iu (iz , (rcc , ry , _))) =
  A (rc z c′ rcc) (nΩ z) (λ i u → B i (inc z u)) (F.dW k′ h′ ε ρ B′ c′ F.zero)
    (λ i i′ w w′ rw → rB i i′ (inc z w) (F.inb c′ w′) (wincΩ rcc rw)) β rβ rn ry

upS : ∀ {k h k′ h′ o ε ρ} {tb : Rb (nd (sΩ k) h)} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ → ((c : Tr k) → NoΩ (h c))
    → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′)) → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′
    → ∀ {j j′} {v : j ≤ k} {w′ : F._≤_ j′ (F.Ωₗ k′ h′)} → RelW (ink {h = h} v) w′
    → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
    → {x : Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)} → U0 x → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) x x′
    → RelT j j′ (proj₁ (ψ (nd (sΩ k) h) o tb B j (ink v) β x)) (F.ψs (F.Ωₗ k′ h′) ε ρ B′ j′ w′ β′ nβ x′)
    × RelD j j′ (proj₂ (ψ (nd (sΩ k) h) o tb B j (ink v) β x)) (F.nzs (F.Ωₗ k′ h′) ε ρ B′ j′ w′ β′ nβ x′)
upS {k′ = k′} {h′} {ε = ε} {ρ} (eΩ rk rwc rc) nΩ B B′ rB (wink rv) β rβ rn {x′ = F.up _ c′ y′ e′} (u0 z y e) (iu (iz , (rcc , ry , _))) =
  S (rc z c′ rcc) (nΩ z) (λ i u → B i (inc z u)) (F.dW k′ h′ ε ρ B′ c′ F.zero)
    (λ i i′ w w′ rw → rB i i′ (inc z w) (F.inb c′ w′) (wincΩ rcc rw)) (∙-R rv (rwc z c′ rcc)) β rβ rn ry

topΩ : ∀ {k h k′ h′ o ε ρ} {tb : Rb (nd (sΩ k) h)} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ → ((c : Tr k) → NoΩ (h c))
     → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′)) → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′
     → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
     → {t : Pos⁼ k} {g : Br (nd (sΩ k) h) (inj₁ t) → Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)}
     → ((z : Br (nd (sΩ k) h) (inj₁ t)) → U0 (g z)) → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) (Ω (inj₁ t) g) x′
     → RelT zero F.zero (proj₁ (ψ (nd (sΩ k) h) o tb B zero (z≤ (nd (sΩ k) h)) β (Ω (inj₁ t) g))) (F.ψ⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
     × RelD zero F.zero (proj₂ (ψ (nd (sΩ k) h) o tb B zero (z≤ (nd (sΩ k) h)) β (Ω (inj₁ t) g))) (F.nz⊥ (F.Ωₗ k′ h′) ε ρ B′ x′)
topΩ {k} {h} {k′} {h′} {o} {ε} {ρ} {tb} re nΩ B B′ rB β rβ rn {t} {g} {x′ = F.Ω p′ g′} uz (iw (rp , rg)) =
  node0 (kp ℓ o p (z≤ ℓ)) G sR
    (limc-R (λ n → G (iter sR (fromBr ℓ p zero) n))
       (λ n → proj₁ (upA re nΩ B B′ rB β rβ rn (uz _) (rg _ _ (ch n)))) (λ n → proj₂ (upA re nΩ B B′ rB β rβ rn (uz _) (rg _ _ (ch n))))
     , dt (proj₂ (upA re nΩ B B′ rB β rβ rn (uz _) (rg _ _ (ch zero))) , dl))
  where
  ℓ : L
  ℓ = nd (sΩ k) h
  ℓ′ : F.L
  ℓ′ = F.Ωₗ k′ h′
  p : Pos ℓ
  p = inj₁ t
  rl : RelL ℓ ℓ′
  rl = E→L re
  G : Br ℓ p → Tr⁺ zero
  G z = ψ ℓ o tb B zero (z≤ ℓ) β (g z)
  sR : Br ℓ p → Br ℓ p
  sR z = fromBr ℓ p (proj₁ (ψ ℓ o tb B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
  s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
  s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
              (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
  rb = rB (at ℓ p) (F.at ℓ′ p′) (posW ℓ p) (F.posW ℓ′ p′) (posW-R rl p p′ rp)
  ch : (n : ℕ) → RelB ℓ ℓ′ p p′ (iter sR (fromBr ℓ p zero) n) (F.iter s′R (F.br0 ℓ′ p′) n)
  ch = iterR (RelB ℓ ℓ′ p p′) (br0-R rl p p′ rp)
         (λ z z′ rz → fromBr-R rl p p′ rp
            (proj₁ (upS re nΩ B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (uz z) (rg z z′ rz))))
```
