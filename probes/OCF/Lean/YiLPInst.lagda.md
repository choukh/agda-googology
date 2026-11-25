# 合法块的接口: 实填

> 判决: 编译定理, 无前提, 成品候选 (导入闭包不含记号). `legI : Iface`: 合法块的折叠 (`YiLegFold`) 填满 [YiLPIface](YiLPIface.lagda.md) 的每个字段, 对一切层号, 一切证据, 路线与底; J2 一族复用 `YiLegCheck` (该文件标为验收文件, 但只导入块本身), 结点行, `kstep` 是 `refl`, `kall` 取自 [YiLPKall](YiLPKall.lagda.md).
> 塔第 n+1 项与它的证据就是下一站 `Nx (tw n)` (`tw-Nx`, `Ev-tw-Nx`, `Rt-tw-Nx`, 都是 `refl`), 所以接口的 `kstep`, `kall` 对塔各项成立 (`kall-legI-tw`).
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
import OCF.Lean.YiLegCheck as C
open import OCF.Lean.YiLPIface using (Nx; evc; Ev-Nx; Rt-Nx; InB; prE; Kept; Iface)
import OCF.Lean.YiLPKall as K
```

```agda
kstepᴸ : (a : L) (ea : Ev a) (ra : Rt a) (B : Base (Nx a)) (β : Tr a) (nβ : a ⊢ zero ◃ β) (x : Tr (Nx a))
  (p : Pos a) (g : Br a p → Tr a) (e : a ⊢ zero ◃ Ω p g)
  → ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ (up x zero (Ω p g) e)
  ≡ Ω p (λ z → ψs a ea ra (dW a (λ c → a ⊕ ↑ a c) (Ev-Nx a ea) (Rt-Nx a ra) B zero x) a self
                 (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ x)
                 (nzs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ x) (g z))
kstepᴸ a ea ra B β nβ x p g e = refl

legI : Iface
legI = record
  { ψ⊥ = ψ⊥ ; ψs = ψs ; nz⊥ = nz⊥ ; nzs = nzs ; kp⁼ = kp⁼
  ; J2-suc = C.J2-suc ; J2-lim = C.J2-lim ; J2-limu = C.J2-limu ; J2-Ωk = C.J2-Ωk ; J2-Ωu = C.J2-Ωu
  ; J2⊥-suc = C.J2⊥-suc ; J2⊥-lim = C.J2⊥-lim ; J2⊥-Ω = C.J2⊥-Ω
  ; mono⊥ = mono⊥ ; monos = monos
  ; self-up = C.self-up
  ; node = λ ℓ ε ρ B j w β nβ p G → refl
  ; node⊥ = λ ℓ ε ρ B p G → refl
  ; kp-fwd = λ g ε ρ m n p w K d v q → kp-fwdᴸ g ε ρ m n p w K d v q
  ; kp-bwd = λ g ε ρ m n p w K d v q → kp-bwdᴸ g ε ρ m n p w K d v q
  ; J2-lim-bwd = C.J2-lim-bwd ; J2-lim-fwd = C.J2-lim-fwd
  ; kstep = kstepᴸ
  ; kall = K.kall }
  where
  kp-fwdᴸ : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
    {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g m ≤ g n)
    → way g (proj₂ ρ) m n ≡ fwd v
    → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d
    ≡ kp⁼ (g n) (ε n) (proj₁ ρ n) (psh v p) w (λ q cv → K q (λ z → pshBr v p (cv z))) d
  kp-fwdᴸ g ε ρ m n p w K d v q rewrite q = refl
  kp-bwdᴸ : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
    {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g n ≤ g m)
    → way g (proj₂ ρ) m n ≡ bwd v
    → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d ≡ kp⁼ (g m) (ε m) (proj₁ ρ m) p (w ∙ v) K d
  kp-bwdᴸ g ε ρ m n p w K d v q rewrite q = refl
```

## 塔各项是下一站

```agda
tw-Nx : (n : ℕ) → tw (suc n) ≡ Nx (tw n)
tw-Nx n = refl

Ev-tw-Nx : (n : ℕ) → Ev-tw (suc n) ≡ Ev-Nx (tw n) (Ev-tw n)
Ev-tw-Nx n = refl

Rt-tw-Nx : (n : ℕ) → Rt-tw (suc n) ≡ Rt-Nx (tw n) (Rt-tw n)
Rt-tw-Nx n = refl

kall-legI-tw : (n : ℕ) (B : Base (tw (suc n))) (β : Tr (tw n)) (nβ : tw n ⊢ zero ◃ β) (x : Tr (tw (suc n)))
  (c : Tr (tw n)) {t : Pos (tw n ⊕ ↑ (tw n) c)} (G : Br (tw n ⊕ ↑ (tw n) c) t → Tr (tw n ⊕ ↑ (tw n) c))
  (e : tw n ⊕ ↑ (tw n) c ⊢ zero ◃ Ω t G)
  (i : InB (tw n) (↑ (tw n) c) t) (p : Pos (tw n)) → prE i (evc (tw n) (Ev-tw n) c) ≡ inj₂ p
  → Kept p (Iface.ψs legI (tw (suc n)) (Ev-tw (suc n)) (Rt-tw (suc n)) B (tw n) (ink self) β nβ (up x c (Ω t G) e))
kall-legI-tw n = Iface.kall legI (tw n) (Ev-tw n) (Rt-tw n)
```
