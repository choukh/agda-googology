# 新主线的折叠与带表的 F2 对照块的关系

> 验收文件 (不读记号), 不进成品. 编译定理, 无前提, 对一切层号: `YiTBRow.ψ` 配 `YiMTTab.rbᶻ` 与 [YiVTFold](YiVTFold.lagda.md) 的折叠保持 `YiBRRel` 的关系 (`A`, `S`, 单调 `Am`, `Sm`, 孩子的底 `cS`, `cL`, `cΩ`); 没有 `YiMTRel` 的 `NoΩ` 前提.
> 来源: 脚本从 `YiSMRel` 改写 (折叠换成配 `rbᶻ` 的 `YiTBRow.ψ`, F2 换成 `YiVTFold`); 新写的只有表的关系 `tb-R` 与 "Ω 形状经指定孩子" 三个子句里按条目分的三支.
> 不否定什么; `YiMTValue.norel` 说的是与原 F2 回退行不相关, 这里换了 F2 一侧的那一行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTRel where

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
open import OCF.Lean.YiTBRow using (ψ; mono)
open import OCF.Lean.YiMTTab using (lo; hi; tbᶻ; rbᶻ)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiVTFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem
open import OCF.Lean.YiBROps
open import OCF.Lean.YiBRFold using (W→L; B₀-R; iterR; node0; nodeLe0; kp-R)
```

## 配表 `rbᶻ` 的折叠

```agda
ψ⁰ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
ψ⁰ ℓ o = ψ ℓ o (rbᶻ ℓ)

mono⁰ : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
      → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ⁰ ℓ o B j w β x) ◃ proj₁ (ψ⁰ ℓ o B j w β y)
mono⁰ ℓ o = mono ℓ o (rbᶻ ℓ)
```

## 表的关系

两边的表在相关的孩子上给出同一种条目, 条目里的路径相关.

```agda
data RelM {A B A′ B′ : Set} (P : A → A′ → Set) (Q : B → B′ → Set) : Maybe (A ⊎ B) → Maybe (A′ ⊎ B′) → Set where
  m1 : ∀ {a a′} → P a a′ → RelM P Q (just (inj₁ a)) (just (inj₁ a′))
  m2 : ∀ {b b′} → Q b b′ → RelM P Q (just (inj₂ b)) (just (inj₂ b′))
  m0 : RelM P Q nothing nothing

z≤-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → RelW (z≤ ℓ) (F.z≤ᶠ ℓ′)
z≤-R lz         = wself
z≤-R (lS r)     = winuS (z≤-R r)
z≤-R (lL r)     = winuL (λ n → z≤-R (r n))
z≤-R (lΩ rk rh) = winuΩ (λ c c′ rc → z≤-R (rh c c′ rc))

RelEnt : ∀ {a b a′ b′} → Maybe ((b ≤ a) ⊎ (a ≤ b)) → Maybe ((F._≤_ b′ a′) ⊎ (F._≤_ a′ b′)) → Set
RelEnt = RelM (λ u u′ → RelW u u′) (λ u u′ → RelW u u′)

lo-R : ∀ {a b a′ b′} → RelL a a′ → RelL b b′ → RelEnt (lo a b) (F.loᶠ a′ b′)
lo-R lz       rb = m2 (z≤-R rb)
lo-R (lS _)   rb = m0
lo-R (lL _)   rb = m0
lo-R (lΩ _ _) rb = m0

hi-R : ∀ {a b a′ b′} → RelL a a′ → RelL b b′ → RelEnt (hi a b) (F.hiᶠ a′ b′)
hi-R ra lz       = m1 (z≤-R ra)
hi-R ra (lS _)   = m0
hi-R ra (lL _)   = m0
hi-R ra (lΩ _ _) = m0

tb-R : ∀ {k h k′ h′} → ((c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelL (h c) (h′ c′))
     → ∀ {c c′ c₁ c₂} → RelT k k′ c c₁ → RelT k k′ c′ c₂ → RelEnt (tbᶻ k h c c′) (F.tbᶠ k′ h′ c₁ c₂)
tb-R {k} {h} {k′} {h′} rh {c = zero} {c′ = zero} {c₁ = F.zero} {c₂ = F.zero} iz iz = m1 wself
tb-R {k} {h} {k′} {h′} rh {c = zero} {c′ = (suc c′)} {c₁ = F.zero} {c₂ = (F.suc c₂)} iz (is r) = lo-R (rh zero F.zero iz) (rh (suc c′) (F.suc c₂) (is r))
tb-R {k} {h} {k′} {h′} rh {c = zero} {c′ = (lim f′ a′)} {c₁ = F.zero} {c₂ = (F.lim f₂ a₂)} iz (il r) = lo-R (rh zero F.zero iz) (rh (lim f′ a′) (F.lim f₂ a₂) (il r))
tb-R {k} {h} {k′} {h′} rh {c = zero} {c′ = (Ω p′ g′)} {c₁ = F.zero} {c₂ = (F.Ω p₂ g₂)} iz (iw r) = lo-R (rh zero F.zero iz) (rh (Ω p′ g′) (F.Ω p₂ g₂) (iw r))
tb-R {k} {h} {k′} {h′} rh {c = zero} {c′ = (up x′ c′ y′ e′)} {c₁ = F.zero} {c₂ = (F.up x₂ c₂ y₂ e₂)} iz (iu r) = lo-R (rh zero F.zero iz) (rh (up x′ c′ y′ e′) (F.up x₂ c₂ y₂ e₂) (iu r))
tb-R {k} {h} {k′} {h′} rh {c = (suc c)} {c′ = zero} {c₁ = (F.suc c₁)} {c₂ = F.zero} (is r) iz = hi-R (rh (suc c) (F.suc c₁) (is r)) (rh zero F.zero iz)
tb-R {k} {h} {k′} {h′} rh {c = (suc c)} {c′ = (suc c′)} {c₁ = (F.suc c₁)} {c₂ = (F.suc c₂)} (is _) (is _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (suc c)} {c′ = (lim f′ a′)} {c₁ = (F.suc c₁)} {c₂ = (F.lim f₂ a₂)} (is _) (il _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (suc c)} {c′ = (Ω p′ g′)} {c₁ = (F.suc c₁)} {c₂ = (F.Ω p₂ g₂)} (is _) (iw _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (suc c)} {c′ = (up x′ c′ y′ e′)} {c₁ = (F.suc c₁)} {c₂ = (F.up x₂ c₂ y₂ e₂)} (is _) (iu _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (lim f a)} {c′ = zero} {c₁ = (F.lim f₁ a₁)} {c₂ = F.zero} (il r) iz = hi-R (rh (lim f a) (F.lim f₁ a₁) (il r)) (rh zero F.zero iz)
tb-R {k} {h} {k′} {h′} rh {c = (lim f a)} {c′ = (suc c′)} {c₁ = (F.lim f₁ a₁)} {c₂ = (F.suc c₂)} (il _) (is _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (lim f a)} {c′ = (lim f′ a′)} {c₁ = (F.lim f₁ a₁)} {c₂ = (F.lim f₂ a₂)} (il _) (il _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (lim f a)} {c′ = (Ω p′ g′)} {c₁ = (F.lim f₁ a₁)} {c₂ = (F.Ω p₂ g₂)} (il _) (iw _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (lim f a)} {c′ = (up x′ c′ y′ e′)} {c₁ = (F.lim f₁ a₁)} {c₂ = (F.up x₂ c₂ y₂ e₂)} (il _) (iu _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (Ω p g)} {c′ = zero} {c₁ = (F.Ω p₁ g₁)} {c₂ = F.zero} (iw r) iz = hi-R (rh (Ω p g) (F.Ω p₁ g₁) (iw r)) (rh zero F.zero iz)
tb-R {k} {h} {k′} {h′} rh {c = (Ω p g)} {c′ = (suc c′)} {c₁ = (F.Ω p₁ g₁)} {c₂ = (F.suc c₂)} (iw _) (is _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (Ω p g)} {c′ = (lim f′ a′)} {c₁ = (F.Ω p₁ g₁)} {c₂ = (F.lim f₂ a₂)} (iw _) (il _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (Ω p g)} {c′ = (Ω p′ g′)} {c₁ = (F.Ω p₁ g₁)} {c₂ = (F.Ω p₂ g₂)} (iw _) (iw _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (Ω p g)} {c′ = (up x′ c′ y′ e′)} {c₁ = (F.Ω p₁ g₁)} {c₂ = (F.up x₂ c₂ y₂ e₂)} (iw _) (iu _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (up x c y e)} {c′ = zero} {c₁ = (F.up x₁ c₁ y₁ e₁)} {c₂ = F.zero} (iu r) iz = hi-R (rh (up x c y e) (F.up x₁ c₁ y₁ e₁) (iu r)) (rh zero F.zero iz)
tb-R {k} {h} {k′} {h′} rh {c = (up x c y e)} {c′ = (suc c′)} {c₁ = (F.up x₁ c₁ y₁ e₁)} {c₂ = (F.suc c₂)} (iu _) (is _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (up x c y e)} {c′ = (lim f′ a′)} {c₁ = (F.up x₁ c₁ y₁ e₁)} {c₂ = (F.lim f₂ a₂)} (iu _) (il _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (up x c y e)} {c′ = (Ω p′ g′)} {c₁ = (F.up x₁ c₁ y₁ e₁)} {c₂ = (F.Ω p₂ g₂)} (iu _) (iw _) = m0
tb-R {k} {h} {k′} {h′} rh {c = (up x c y e)} {c′ = (up x′ c′ y′ e′)} {c₁ = (F.up x₁ c₁ y₁ e₁)} {c₂ = (F.up x₂ c₂ y₂ e₂)} (iu _) (iu _) = m0
```

## 折叠, 非零, 单调

```agda
mutual
  A : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
    → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
    → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
    → RelT zero F.zero (proj₁ (ψ⁰ ℓ o B zero (z≤ ℓ) β x)) (F.ψ⊥ ℓ′ ε ρ B′ x′)
    × RelD zero F.zero (proj₂ (ψ⁰ ℓ o B zero (z≤ ℓ) β x)) (F.nz⊥ ℓ′ ε ρ B′ x′)
  A re B B′ rB β rβ rn {x = zero} iz = rβ , rn
  A {ℓ} {o = o} re B B′ rB β rβ rn {x = suc x} (is r) =
    let u = A re B B′ rB β rβ rn r in next-R (ψ⁰ ℓ o B zero (z≤ ℓ) β x) (proj₁ u) (proj₂ u)
  A re B B′ rB β rβ rn {x = lim f a} (il (rf , ra)) =
    il ((λ n → proj₁ (A re B B′ rB β rβ rn (rf n))) , (λ n → Am re B B′ rB β rβ rn (ra n)))
    , dt (proj₂ (A re B B′ rB β rβ rn (rf zero)) , dl)
  A {ℓ} {ℓ′} {o} {ε} {ρ} re B B′ rB β rβ rn {x = Ω p g} {x′ = F.Ω p′ g′} (iw (rp , rg)) =
    node0 (kp ℓ o p (z≤ ℓ)) (λ z → ψ⁰ ℓ o B zero (z≤ ℓ) β (g z)) sR
      (limc-R (λ n → ψ⁰ ℓ o B zero (z≤ ℓ) β (g (iter sR (fromBr ℓ p zero) n)))
         (λ n → proj₁ (A re B B′ rB β rβ rn (rg _ _ (ch n)))) (λ n → proj₂ (A re B B′ rB β rβ rn (rg _ _ (ch n))))
       , dt (proj₂ (A re B B′ rB β rβ rn (rg _ _ (ch zero))) , dl))
    where
    rl : RelL ℓ ℓ′
    rl = E→L re
    sR : Br ℓ p → Br ℓ p
    sR z = fromBr ℓ p (proj₁ (ψ⁰ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
    s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
    s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
                (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
    rb = rB (at ℓ p) (F.at ℓ′ p′) (posW ℓ p) (F.posW ℓ′ p′) (posW-R rl p p′ rp)
    ch : (n : ℕ) → RelB ℓ ℓ′ p p′ (iter sR (fromBr ℓ p zero) n) (F.iter s′R (F.br0 ℓ′ p′) n)
    ch = iterR (RelB ℓ ℓ′ p p′) (br0-R rl p p′ rp)
           (λ z z′ rz → fromBr-R rl p p′ rp
              (proj₁ (S re B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (rg z z′ rz))))
  A {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in A re (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         (ψ⁰ (nd sS h) o B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) ry
  A {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB β rβ rn {x = up x n y e} {x′ = F.up x′ n′ y′ e′} (iu (rx , (refl , ry , _))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in A (re n) (λ i w → ψ⁰ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cL re₀ B B′ rB rx n)
         (ψ⁰ (nd sL g) o B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) ry
  A {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , _))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in A ((rc c c′ rcc)) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (ψ⁰ (nd (sΩ k) h) o B zero (z≤ (nd (sΩ k) h)) β x) (proj₁ u) (proj₂ u) ry

  Am : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
     → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
     → {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} {d : ℓ ⊢ x ◃ y} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′
     → RelD zero F.zero (mono⁰ ℓ o B zero (z≤ ℓ) β d) (F.mono⊥ ℓ′ ε ρ B′ d′)
  Am re B B′ rB β rβ rn {d = ◃s} ds = dl
  Am re B B′ rB β rβ rn {d = ◃l n} dl = dl
  Am {ℓ} {o = o} re B B′ rB β rβ rn {d = ◃w {p = p}} (dw _) = nodeLe0 (kp ℓ o p (z≤ ℓ)) _ _ dl
  Am {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am re (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         (ψ⁰ (nd sS h) o B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) rye
  Am {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB β rβ rn {d = ◃u x n y e} {d′ = F.◃u x′ n′ y′ e′} (du (rx , (refl , ry , rye))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am (re n) (λ i w → ψ⁰ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cL re₀ B B′ rB rx n)
         (ψ⁰ (nd sL g) o B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) rye
  Am {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am ((rc c c′ rcc)) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (ψ⁰ (nd (sΩ k) h) o B zero (z≤ (nd (sΩ k) h)) β x) (proj₁ u) (proj₂ u) rye
  Am {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am re (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         (ψ⁰ (nd sS h) o B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) rr
  Am {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr₀ re) B B′ rB β rβ rn {d = ◃c x n r} {d′ = F.◃c x′ n′ r′} (dc (rx , (refl , rr))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am (re n) (λ i w → ψ⁰ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cL re₀ B B′ rB rx n)
         (ψ⁰ (nd sL g) o B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) rr
  Am {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am ((rc c c′ rcc)) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (ψ⁰ (nd (sΩ k) h) o B zero (z≤ (nd (sΩ k) h)) β x) (proj₁ u) (proj₂ u) rr
  Am re B B′ rB β rβ rn {d = ◃t d₁ d₂} (dt (r₁ , r₂)) = dt (Am re B B′ rB β rβ rn r₁ , Am re B B′ rB β rβ rn r₂)

  S : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
    → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
    → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
    → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
    → RelT j j′ (proj₁ (ψ⁰ ℓ o B j w β x)) (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
    × RelD j j′ (proj₂ (ψ⁰ ℓ o B j w β x)) (F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
  S re B B′ rB rw β rβ rn {x = zero} iz = rβ , rn
  S {ℓ} {o = o} re B B′ rB {j} {w = w} rw β rβ rn {x = suc x} (is r) =
    let u = S re B B′ rB rw β rβ rn r in next-R (ψ⁰ ℓ o B j w β x) (proj₁ u) (proj₂ u)
  S re B B′ rB rw β rβ rn {x = lim f a} (il (rf , ra)) =
    il ((λ n → proj₁ (S re B B′ rB rw β rβ rn (rf n))) , (λ n → Sm re B B′ rB rw β rβ rn (ra n)))
    , dt (proj₂ (S re B B′ rB rw β rβ rn (rf zero)) , dl)
  S {ℓ} {ℓ′} {o} {ε} {ρ} re B B′ rB {j} {j′} {w} {w′} rw β {β′} {nβ} rβ rn {x = Ω p g} {x′ = F.Ω p′ g′} (iw (rp , rg)) =
    kp-R re p p′ rp rw (λ Z → F._⊢_◃_ j′ F.zero Z) K d hk hd
      (λ m z qz → RelT j j′ (proj₁ (node⁺ m G sR)) z × RelD j j′ (proj₂ (node⁺ m G sR)) qz)
      (λ q q′ rq cv cv′ g₀ gd rcv →
         iw (rq , λ z z′ rz → proj₁ (S re B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz))))
         , dt (proj₂ (S re B B′ rB rw β rβ rn (rg _ _ (rcv _ _ (br0-R (W→L rl rw) q q′ rq))))
              , dw (rq , λ z z′ rz → proj₁ (S re B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz))))))
      (limc-R (λ n → G (iter sR (fromBr ℓ p zero) n))
         (λ n → proj₁ (S re B B′ rB rw β rβ rn (rg _ _ (ch n)))) (λ n → proj₂ (S re B B′ rB rw β rβ rn (rg _ _ (ch n))))
       , dt (proj₂ (S re B B′ rB rw β rβ rn (rg _ _ (ch zero))) , dl))
    where
    rl : RelL ℓ ℓ′
    rl = E→L re
    G : Br ℓ p → Tr⁺ j
    G z = ψ⁰ ℓ o B j w β (g z)
    sR : Br ℓ p → Br ℓ p
    sR z = fromBr ℓ p (proj₁ (ψ⁰ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
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
    rb = rB (at ℓ p) (F.at ℓ′ p′) (posW ℓ p) (F.posW ℓ′ p′) (posW-R rl p p′ rp)
    ch : (n : ℕ) → RelB ℓ ℓ′ p p′ (iter sR (fromBr ℓ p zero) n) (F.iter s′R (F.br0 ℓ′ p′) n)
    ch = iterR (RelB ℓ ℓ′ p p′) (br0-R rl p p′ rp)
           (λ z z′ rz → fromBr-R rl p p′ rp
              (proj₁ (S re B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (rg z z′ rz))))
  -- 自身行
  S {o = o} re₀@(eS {h = h} {a = a} re) B B′ rB wself β rβ rn {x = up x c y e} (iu (rx , (ry , _))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Up-R (lS (E→L re)) (E→L re) (ddown (lS (E→L re)) dstop tt) (ψ⁰ (nd sS h) o B (nd sS h) self β x) (proj₁ u) (proj₂ u) ry
  S {o = o} re₀@(eL {g = g} rr re) B B′ rB wself β rβ rn {x = up x n y e} (iu (rx , (refl , ry , _))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Up-R (lL (λ i → E→L (re i))) (E→L (re n)) (ddown (lL (λ i → E→L (re i))) dstop refl)
         (ψ⁰ (nd sL g) o B (nd sL g) self β x) (proj₁ u) (proj₂ u) ry
  S {o = o} re₀@(eΩ {k = k} {h = h} rk rwc rc) B B′ rB wself β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , _))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Up-R (E→L re₀) (E→L ((rc c c′ rcc))) (ddown (E→L re₀) dstop rcc)
         (ψ⁰ (nd (sΩ k) h) o B (nd (sΩ k) h) self β x) (proj₁ u) (proj₂ u) ry
  -- 一致路径, 下标层侧, 后继形状进孩子 c
  S {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
    let u = S re₀ B B′ rB (winuS rw) β rβ rn rx
    in S re (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rw (ψ⁰ (nd sS h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
  S {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
    let u = S re₀ B B′ rB (wincS rv) β rβ rn rx
    in S re (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rv (ψ⁰ (nd sS h) o B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) ry
  S {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {x = up x m y e} {x′ = F.up x′ m′ y′ e′} (iu (rx , (refl , ry , _))) =
    let u = S re₀ B B′ rB (winuL rws) β rβ rn rx
    in S (re m) (λ i w → ψ⁰ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cL re₀ B B′ rB rx m)
         (rws m) (ψ⁰ (nd sL g) o B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
  S {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (winuΩ {vs = ws} rws) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , _))) =
    let u = S re₀ B B′ rB (winuΩ rws) β rβ rn rx
    in S ((rc c c′ rcc)) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (rws c c′ rcc) (ψ⁰ (nd (sΩ k) h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
  S {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (wink {v = v} rv) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , _))) =
    let u = S re₀ B B′ rB (wink rv) β rβ rn rx
    in S ((rc c c′ rcc)) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (∙-R rv ((rwc c c′ rcc))) (ψ⁰ (nd (sΩ k) h) o B j (ink v) β x) (proj₁ u) (proj₂ u) ry
  -- ℕ 极限形状: 比较孩子编号
  S {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {x = up x m y e} {x′ = F.up x′ m′ y′ e′} (iu (rx , (refl , ry , rye)))
    with S re₀ B B′ rB rw₀ β rβ rn rx | cL re₀ B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
  ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
    S (re n) (λ i w → ψ⁰ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
      rv (ψ⁰ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (proj₁ (emb-R (re n) ru (y , e) ry rye))
  ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
    S (re m) (λ i w → ψ⁰ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
      (∙-R rv ru) (ψ⁰ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) ry
  -- Ω 形状经指定孩子: 回退
  S {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} rw₀@(wincΩ {c = c₁} {c′ = c₁′} {v = v} rc₁ rv) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , rye)))
    with S re₀ B B′ rB rw₀ β rβ rn rx | cΩ re₀ B B′ rB rx | tbᶻ k h c c₁ | F.tbᶠ k′ h′ c′ c₁′ | tb-R (λ d d′ rd → E→L (rc d d′ rd)) rcc rc₁
  ... | r₀ | cB | just (inj₁ u) | just (inj₁ u′) | m1 ru =
    S (rc c c′ rcc) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′) (cB c c′ rcc)
      (∙-R rv ru) (ψ⁰ (nd (sΩ k) h) o B j (inc c₁ v) β x) (proj₁ r₀) (proj₂ r₀) ry
  ... | r₀ | cB | just (inj₂ u) | just (inj₂ u′) | m2 ru =
    S (rc c₁ c₁′ rc₁) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c₁ w) (B i (inc c₁ w)) x) (F.dW k′ h′ ε ρ B′ c₁′ x′) (cB c₁ c₁′ rc₁)
      rv (ψ⁰ (nd (sΩ k) h) o B j (inc c₁ v) β x) (proj₁ r₀) (proj₂ r₀) (proj₁ (emb-R (rc c₁ c₁′ rc₁) ru (y , e) ry rye))
  ... | r₀ | cB | nothing | nothing | m0 =
    let re₁ = rc c c′ rcc
        a₀ = A re₁ (B₀ _) (F.B₀ _) (B₀-R (E→L re₁)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) ry
    in +-R (proj₁ r₀) (ι-R (proj₁ a₀)) , dt (proj₂ r₀ , +m-R (proj₁ r₀) (ιm-R (proj₂ a₀)))
  Sm : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
     → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
     → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
     → {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} {d : ℓ ⊢ x ◃ y} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′
     → RelD j j′ (mono⁰ ℓ o B j w β d) (F.monos ℓ′ ε ρ B′ j′ w′ β′ nβ d′)
  Sm re B B′ rB rw β rβ rn {d = ◃s} ds = dl
  Sm re B B′ rB rw β rβ rn {d = ◃l n} dl = dl
  Sm {ℓ} {ℓ′} {o} {ε} {ρ} re B B′ rB {j} {j′} {w} {w′} rw β {β′} {nβ} rβ rn {d = ◃w {p = p} {g = g}} {d′ = F.◃w {p = p′} {g = g′}} (dw (rp , rg)) =
    kp-R re p p′ rp rw Q K d hk hd (λ m z qz → RelD j j′ (nodeLe m G sR) qz)
      (λ q q′ rq cv cv′ g₀ gd rcv →
         RelD-substˡ (λ t → proj₁ (G t)) (λ _ → Ω q (λ z → proj₁ (G (cv z)))) g₀
           (RelD-substʳ (λ t → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ t)) (λ _ → F.Ω q′ (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv′ z)))) gd
             (dw (rq , λ z z′ rz → proj₁ (S re B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz)))))))
      dl
    where
    G : Br ℓ p → Tr⁺ j
    G z = ψ⁰ ℓ o B j w β (g z)
    sR : Br ℓ p → Br ℓ p
    sR z = fromBr ℓ p (proj₁ (ψ⁰ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
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
  Sm {o = o} re₀@(eS {h = h} re) B B′ rB wself β rβ rn {d = ◃u x c y e} (du (rx , (ry , rye))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lS (E→L re)) (E→L re) (ddown (lS (E→L re)) dstop tt) (ψ⁰ (nd sS h) o B (nd sS h) self β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} re₀@(eL {g = g} rr re) B B′ rB wself β rβ rn {d = ◃u x n y e} (du (rx , (refl , ry , rye))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lL (λ i → E→L (re i))) (E→L (re n)) (ddown (lL (λ i → E→L (re i))) dstop refl)
         (ψ⁰ (nd sL g) o B (nd sL g) self β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} re₀@(eΩ {k = k} {h = h} rk rwc rc) B B′ rB wself β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (E→L re₀) (E→L ((rc c c′ rcc))) (ddown (E→L re₀) dstop rcc)
         (ψ⁰ (nd (sΩ k) h) o B (nd (sΩ k) h) self β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} re₀@(eS {h = h} re) B B′ rB wself β rβ rn {d = ◃c x c r} (dc (rx , rr)) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lS (E→L re)) (E→L re) (ddown (lS (E→L re)) dstop tt) (ψ⁰ (nd sS h) o B (nd sS h) self β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} re₀@(eL {g = g} rr₀ re) B B′ rB wself β rβ rn {d = ◃c x n r} (dc (rx , (refl , rr))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lL (λ i → E→L (re i))) (E→L (re n)) (ddown (lL (λ i → E→L (re i))) dstop refl)
         (ψ⁰ (nd sL g) o B (nd sL g) self β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} re₀@(eΩ {k = k} {h = h} rk rwc rc) B B′ rB wself β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (E→L re₀) (E→L ((rc c c′ rcc))) (ddown (E→L re₀) dstop rcc)
         (ψ⁰ (nd (sΩ k) h) o B (nd (sΩ k) h) self β x) (proj₁ u) (proj₂ u) rr
  -- 进孩子的各行 (◃u)
  Sm {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
    let u = S re₀ B B′ rB (winuS rw) β rβ rn rx
    in Sm re (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rw (ψ⁰ (nd sS h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
    let u = S re₀ B B′ rB (wincS rv) β rβ rn rx
    in Sm re (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rv (ψ⁰ (nd sS h) o B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {d = ◃u x m y e} {d′ = F.◃u x′ m′ y′ e′} (du (rx , (refl , ry , rye))) =
    let u = S re₀ B B′ rB (winuL rws) β rβ rn rx
    in Sm (re m) (λ i w → ψ⁰ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cL re₀ B B′ rB rx m)
         (rws m) (ψ⁰ (nd sL g) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (winuΩ {vs = ws} rws) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye))) =
    let u = S re₀ B B′ rB (winuΩ rws) β rβ rn rx
    in Sm ((rc c c′ rcc)) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (rws c c′ rcc) (ψ⁰ (nd (sΩ k) h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (wink {v = v} rv) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye))) =
    let u = S re₀ B B′ rB (wink rv) β rβ rn rx
    in Sm ((rc c c′ rcc)) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (∙-R rv ((rwc c c′ rcc))) (ψ⁰ (nd (sΩ k) h) o B j (ink v) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {d = ◃u x m y e} {d′ = F.◃u x′ m′ y′ e′} (du (rx , (refl , ry , rye)))
    with S re₀ B B′ rB rw₀ β rβ rn rx | cL re₀ B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
  ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
    Sm (re n) (λ i w → ψ⁰ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
      rv (ψ⁰ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (proj₂ (emb-R (re n) ru (y , e) ry rye))
  ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
    Sm (re m) (λ i w → ψ⁰ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
      (∙-R rv ru) (ψ⁰ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) rye
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} rw₀@(wincΩ {c = c₁} {c′ = c₁′} {v = v} rc₁ rv) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye)))
    with S re₀ B B′ rB rw₀ β rβ rn rx | cΩ re₀ B B′ rB rx | tbᶻ k h c c₁ | F.tbᶠ k′ h′ c′ c₁′ | tb-R (λ d d′ rd → E→L (rc d d′ rd)) rcc rc₁
  ... | r₀ | cB | just (inj₁ u) | just (inj₁ u′) | m1 ru =
    Sm (rc c c′ rcc) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′) (cB c c′ rcc)
      (∙-R rv ru) (ψ⁰ (nd (sΩ k) h) o B j (inc c₁ v) β x) (proj₁ r₀) (proj₂ r₀) rye
  ... | r₀ | cB | just (inj₂ u) | just (inj₂ u′) | m2 ru =
    Sm (rc c₁ c₁′ rc₁) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c₁ w) (B i (inc c₁ w)) x) (F.dW k′ h′ ε ρ B′ c₁′ x′) (cB c₁ c₁′ rc₁)
      rv (ψ⁰ (nd (sΩ k) h) o B j (inc c₁ v) β x) (proj₁ r₀) (proj₂ r₀) (proj₂ (emb-R (rc c₁ c₁′ rc₁) ru (y , e) ry rye))
  ... | r₀ | cB | nothing | nothing | m0 =
    let re₁ = rc c c′ rcc
        a₀ = A re₁ (B₀ _) (F.B₀ _) (B₀-R (E→L re₁)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) ry
    in +m-R (proj₁ r₀) (ιm-R (proj₂ a₀))
  -- 进孩子的各行 (◃c)
  Sm {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
    let u = S re₀ B B′ rB (winuS rw) β rβ rn rx
    in Sm re (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rw (ψ⁰ (nd sS h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
    let u = S re₀ B B′ rB (wincS rv) β rβ rn rx
    in Sm re (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rv (ψ⁰ (nd sS h) o B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr₀ re) B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {d = ◃c x m r} {d′ = F.◃c x′ m′ r′} (dc (rx , (refl , rr))) =
    let u = S re₀ B B′ rB (winuL rws) β rβ rn rx
    in Sm (re m) (λ i w → ψ⁰ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cL re₀ B B′ rB rx m)
         (rws m) (ψ⁰ (nd sL g) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (winuΩ {vs = ws} rws) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr))) =
    let u = S re₀ B B′ rB (winuΩ rws) β rβ rn rx
    in Sm ((rc c c′ rcc)) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (rws c c′ rcc) (ψ⁰ (nd (sΩ k) h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (wink {v = v} rv) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr))) =
    let u = S re₀ B B′ rB (wink rv) β rβ rn rx
    in Sm ((rc c c′ rcc)) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (∙-R rv ((rwc c c′ rcc))) (ψ⁰ (nd (sΩ k) h) o B j (ink v) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr₀ re) B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {d = ◃c x m r} {d′ = F.◃c x′ m′ r′} (dc (rx , (refl , rr)))
    with S re₀ B B′ rB rw₀ β rβ rn rx | cL re₀ B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr₀ m n
  ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
    Sm (re n) (λ i w → ψ⁰ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
      rv (ψ⁰ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (emb-mono-R (re n) ru rr)
  ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
    Sm (re m) (λ i w → ψ⁰ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
      (∙-R rv ru) (ψ⁰ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) rr
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} rw₀@(wincΩ {c = c₁} {c′ = c₁′} {v = v} rc₁ rv) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr)))
    with S re₀ B B′ rB rw₀ β rβ rn rx | cΩ re₀ B B′ rB rx | tbᶻ k h c c₁ | F.tbᶠ k′ h′ c′ c₁′ | tb-R (λ d d′ rd → E→L (rc d d′ rd)) rcc rc₁
  ... | r₀ | cB | just (inj₁ u) | just (inj₁ u′) | m1 ru =
    Sm (rc c c′ rcc) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′) (cB c c′ rcc)
      (∙-R rv ru) (ψ⁰ (nd (sΩ k) h) o B j (inc c₁ v) β x) (proj₁ r₀) (proj₂ r₀) rr
  ... | r₀ | cB | just (inj₂ u) | just (inj₂ u′) | m2 ru =
    Sm (rc c₁ c₁′ rc₁) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c₁ w) (B i (inc c₁ w)) x) (F.dW k′ h′ ε ρ B′ c₁′ x′) (cB c₁ c₁′ rc₁)
      rv (ψ⁰ (nd (sΩ k) h) o B j (inc c₁ v) β x) (proj₁ r₀) (proj₂ r₀) (emb-mono-R (rc c₁ c₁′ rc₁) ru rr)
  ... | r₀ | cB | nothing | nothing | m0 =
    let re₁ = rc c c′ rcc
    in +m-R (proj₁ r₀) (ιm-R (Am re₁ (B₀ _) (F.B₀ _) (B₀-R (E→L re₁)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) rr))
  Sm re B B′ rB rw β rβ rn {d = ◃t d₁ d₂} (dt (r₁ , r₂)) = dt (Sm re B B′ rB rw β rβ rn r₁ , Sm re B B′ rB rw β rβ rn r₂)

  cS : ∀ {h a o ε ρ} → (re : RelE (nd sS h) (F.suc a) o ε ρ) → (B : Base (nd sS h)) (B′ : F.Base (F.suc a))
     → RelBase (nd sS h) (F.suc a) B B′ → {x : Tr (nd sS h)} {x′ : F.Tr (F.suc a)} → RelT (nd sS h) (F.suc a) x x′ → (c : ⊤)
     → RelBase (h c) a (λ i w → ψ⁰ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′)
  cS re B B′ rB rx c i i′ w w′ rw =
    let rb = rB i i′ (inc c w) (F.ins w′) (wincS rw) in S re B B′ rB (wincS rw) (B i (inc c w)) (proj₁ rb) (proj₂ rb) rx

  cL : ∀ {g g′ o ε ρ} → (re : RelE (nd sL g) (F.lim g′) o ε ρ) → (B : Base (nd sL g)) (B′ : F.Base (F.lim g′))
     → RelBase (nd sL g) (F.lim g′) B B′ → {x : Tr (nd sL g)} {x′ : F.Tr (F.lim g′)} → RelT (nd sL g) (F.lim g′) x x′ → (n : ℕ)
     → RelBase (g n) (g′ n) (λ i w → ψ⁰ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′)
  cL re B B′ rB rx n i i′ w w′ rw =
    let rb = rB i i′ (inc n w) (F.inl n w′) (wincL n rw) in S re B B′ rB (wincL n rw) (B i (inc n w)) (proj₁ rb) (proj₂ rb) rx

  cΩ : ∀ {k h k′ h′ o ε ρ} → (re : RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ) → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′))
     → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′ → {x : Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)} → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) x x′
     → (c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′
     → RelBase (h c) (h′ c′) (λ i w → ψ⁰ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
  cΩ re B B′ rB rx c c′ rcc i i′ w w′ rw =
    let rb = rB i i′ (inc c w) (F.inb c′ w′) (wincΩ rcc rw) in S re B B′ rB (wincΩ rcc rw) (B i (inc c w)) (proj₁ rb) (proj₂ rb) rx
```
