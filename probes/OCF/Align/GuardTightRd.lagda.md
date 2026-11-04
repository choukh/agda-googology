# 读位置的实例: 分支字面地对 $\eta$ 结构递归的闭包

> 不含记号. 结论写在 [GuardTight](GuardTight.lagda.md). `Tail G`: 分支 $g\,\eta=G\,\eta$, 且 $G(\eta+1)$ 字面是 $G\,\eta$ 的后继, $G(\lim f)$ 字面是 $G\circ f$ 的极限. 这是 $a+\eta$ 的形状, 也就是 $\Omega\cdot m$, $\psi_1(1)+\Omega$ 的闭包. 接口是 "视图" (`VS`, `VL`): 实例只要说 $G(\eta+1)$, $G(\lim f)$ 的头一步怎么读, 其余一个定义.
>
> **读法.** 沿 $\eta$ 的结构下降到位置所在的项 $x$. $x=b+1$ 且位置就是它: 分支 $b+1$. $x=0$: 第一支. $x$ 是极限且位置就是它: 如果 $x$ 是 $\eta$ 的字面子项, 分支 $x$; 否则 (极限的第 $n$ 项还是极限) 不下降, 分支 $\eta$ (`rC`).
>
> **守卫不要判定: 判定的是公共上界之下的比较.** $b<^{\mathsf I}\eta$ 且 $0<^{\mathsf I}\eta$ (后者来自守卫 $e$), 所以 `<ᴵ-dec` 回答 $b$ 与 $0$ 的比较 (`guard₁`). 这只用字面上界. 没有比较两个分支.
>
> **路径的目标 (位置 `suc k`) 总在后继上, 所以总是精确的 (`rec-exact`). 只有极限层自己的位置 (`omk` 的 `st-lim`) 可能不下降**: 这时那一层的值还是 `ol`, 下一步的 `omk` 又读一次.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardTightRd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.GuardTightCum using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; _≅ᴵ_; Ordᶜ; Simᴵ; add; _+_; Ω; <ᴵ-dec; via; zero; suc; lim; limᵢ; up; z≅; s≅; l≅; z⊑; s⊑; l⊑)
open import OCF.Align.GuardTightLv
open Lv Dom₀
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₀; rb₁; em)
open import OCF.Align.GuardTightBase
```

## §1 守卫: 字面上界之下的比较

```agda
guard₁ : ∀ {b η} → b <ᴵ η → zero <ᴵ η → suc zero ⊑ᴵ suc b
guard₁ p z with <ᴵ-dec p z
... | injᵃ (via e ())
... | injᵇ (via z≅ r) = s⊑ z≅ (suc r)
... | injᶜ z≅ = s⊑ z≅ zero

guardL : ∀ {f s η} → lim f s <ᴵ η → zero <ᴵ η → suc zero ⊑ᴵ lim f s
guardL p z with <ᴵ-dec p z
... | injᵃ (via e ())
... | injᵇ (via z≅ r) = s⊑ z≅ r
```

## §2 视图

```agda
record TailI : Set₁ where
  field
    G    : Ordᴵ → LG
    t₁   : LG
    toT  : ∀ {k} → Cp k (G zero) → Cp k t₁
    adT  : ∀ {E k} (P : Cp k (G zero)) → AdmC E P → AdmC E (toT P)

data VS (G : Ordᴵ → LG) (b : Ordᴵ) {k : LG} (P : Cp k (G (suc b))) : Set where
  vS₀ : VS G b P
  vS₁ : (P′ : Cp k (G b)) → (∀ E → AdmC E P → AdmC E P′) → VS G b P

data VL (G : Ordᴵ → LG) (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n)) {k : LG} (P : Cp k (G (lim f s))) : Set where
  vL₀ : VL G f s P
  vL₁ : ∀ n (P′ : Cp k (G (f n))) → (∀ E → AdmC E P → AdmC E P′) → VL G f s P

module Tail (I : TailI)
            (vs : ∀ b {k} (P : Cp k (TailI.G I (suc b))) → VS (TailI.G I) b P)
            (vl : ∀ f s {k} (P : Cp k (TailI.G I (lim f s))) → VL (TailI.G I) f s P) where
  open TailI I

  g₁ : (η : Ordᴵ) → suc zero ⊑ᴵ η → LG
  g₁ η e = G η

  data Rc (η₀ : Ordᴵ) {x k : LG} (P : Cp k x) : Set where
    rF : ∀ {rep} → Lk k rep → (Q : Cp rep t₁) → (∀ E → AdmC E P → AdmC E Q) → Rc η₀ P
    rB : ∀ {rep} (a : Ordᴵ) (ea : suc zero ⊑ᴵ a) → a ⊲ η₀ → Lk k rep → (Q : Cp rep (G a)) → (∀ E → AdmC E P → AdmC E Q) → Rc η₀ P
    rC : Rc η₀ P

  module _ (η₀ : Ordᴵ) (z₀ : zero <ᴵ η₀) where
    rec : ∀ x {k} (P : Cp k (G x)) → Simᴵ x η₀ → Maybe (x <ᴵ η₀) → Rc η₀ P
    rec zero P σ l = rF (inj₂ refl) (toT P) (λ E a → adT P a)
    rec (suc b) P σ l with vs b P
    ... | vS₀ = rB (suc b) (guard₁ (σ zero) z₀) (⊲ˢ (λ σ′ → σ′ (σ zero))) (inj₂ refl) P (λ _ a → a)
    ... | vS₁ P′ tr with rec b P′ (λ r → σ (suc r)) (just (σ zero))
    ...   | rF d Q u = rF d Q (λ E a → u E (tr E a))
    ...   | rB a ea m d Q u = rB a ea m d Q (λ E a′ → u E (tr E a′))
    ...   | rC = rC
    rec (lim f s) P σ l with vl f s P
    rec (lim f s) P σ (just q) | vL₀ = rB (lim f s) (guardL q z₀) (⊲ˢ (λ σ′ → σ′ q)) (inj₂ refl) P (λ _ a → a)
    rec (lim f s) P σ nothing | vL₀ = rC
    rec (lim f s) P σ l | vL₁ n P′ tr with rec (f n) P′ (λ r → σ (lim n r)) nothing
    ...   | rF d Q u = rF d Q (λ E a → u E (tr E a))
    ...   | rB a ea m d Q u = rB a ea m d Q (λ E a′ → u E (tr E a′))
    ...   | rC = rC

  toRd : ∀ {η e k} {P : Cp k (G η)} → Rc η P → RdO (suc zero) t₁ g₁ η e P
  toRd (rF d Q u) = rdF d Q u
  toRd (rB a ea m d Q u) = rdB a ea m d Q u
  toRd {η} {e} {P = P} rC = rdB η e ⊲= (inj₂ refl) P (λ _ a → a)

  rdA : Rdr (suc zero) t₁ g₁
  rdA zero (s⊑ _ ()) P
  rdA (suc b) e@(s⊑ z≅ z₀) {k} P with vs b P
  ... | vS₀ = rdB (suc b) e ⊲= (inj₂ refl) P (λ _ a → a)
  ... | vS₁ P′ tr = toRd (compose (rec (suc b) z₀ b P′ (λ r → suc r) (just zero)) tr)
    where
    compose : ∀ {P′ : Cp k (G b)} → Rc (suc b) P′ → (∀ E → AdmC E P → AdmC E P′) → Rc (suc b) P
    compose (rF d Q u) t = rF d Q (λ E a → u E (t E a))
    compose (rB a ea m d Q u) t = rB a ea m d Q (λ E a′ → u E (t E a′))
    compose rC t = rC
  rdA (lim f s) e@(s⊑ z≅ z₀) {k} P with vl f s P
  ... | vL₀ = rdB (lim f s) e ⊲= (inj₂ refl) P (λ _ a → a)
  ... | vL₁ n P′ tr = toRd (compose (rec (lim f s) z₀ (f n) P′ (λ r → lim n r) nothing) tr)
    where
    compose : ∀ {P′ : Cp k (G (f n))} → Rc (lim f s) P′ → (∀ E → AdmC E P → AdmC E P′) → Rc (lim f s) P
    compose (rF d Q u) t = rF d Q (λ E a → u E (t E a))
    compose (rB a ea m d Q u) t = rB a ea m d Q (λ E a′ → u E (t E a′))
    compose rC t = rC
```

## §3 实例: $\Omega_1$ 与 $a+\Omega_1$

`Ω₁` 的分支是 $\mathrm{rb}_0\,(\mathrm{em}\,\eta)$. `add a σ` 的分支是 $a+\eta$. 两个都是字面的. 视图逐字.

```agda
module RdΩ₁ where
  I : TailI
  I = record { G = λ η → rb₀ (em η) ; t₁ = suc zero ; toT = λ P → suc P ; adT = λ P a → a }

  vs : ∀ b {k} (P : Cp k (rb₀ (em (suc b)))) → VS (TailI.G I) b P
  vs b self = vS₀
  vs b (suc P) = vS₁ P (λ _ a → a)

  vl : ∀ f s {k} (P : Cp k (rb₀ (em (lim f s)))) → VL (TailI.G I) f s P
  vl f s self = vL₀
  vl f s (lim n P) = vL₁ n P (λ _ a → a)

  open Tail I vs vl public using (rdA)

  Tc-em : ∀ η → Tc (rb₀ (em η))
  Tc-em zero = tt
  Tc-em (suc b) = Tc-em b
  Tc-em (lim f s) = λ n → Tc-em (f n)

module RdAdd (a : Ordᶜ (suc zero)) (σ : Simᴵ zero (suc zero)) (tca : Tc (rb₁ a)) where
  Gₐ : Ordᴵ → LG
  Gₐ η = rb₁ (add a σ (em η))

  I : TailI
  I = record { G = Gₐ ; t₁ = suc (rb₁ a) ; toT = λ P → suc P ; adT = λ P x → x }

  vs : ∀ b {k} (P : Cp k (Gₐ (suc b))) → VS Gₐ b P
  vs b self = vS₀
  vs b (suc P) = vS₁ P (λ _ x → x)

  vl : ∀ f s {k} (P : Cp k (Gₐ (lim f s))) → VL Gₐ f s P
  vl f s self = vL₀
  vl f s (lim n P) = vL₁ n P (λ _ x → x)

  open Tail I vs vl public using (rdA)

  Tc-G : ∀ η → Tc (Gₐ η)
  Tc-G zero = tca
  Tc-G (suc b) = Tc-G b
  Tc-G (lim f s) = λ n → Tc-G (f n)

  Tc-top : Tc (lc (suc zero) (suc (rb₁ a)) (λ η e → Gₐ η))
  Tc-top = rdA , tca , (λ η e → Tc-G η)
```

## §4 实例: $\Omega_1\cdot n$ 与 $\psi_1(1)$

$c\cdot(k+2)$ 的闭包的分支是 $c+(c+\cdots(c+\eta))$. 对变量 $k$ 这不是字面的后继, 只是逐点相等 (`Hs`, `Hl`). 视图由相等搬运, 所以对一切 $k$ 一个定义.

```agda
module RdIter where
  c : Ordᶜ (suc zero)
  c = Ω (suc zero)

  Y : ℕ → Ordᶜ zero → Ordᶜ (suc zero)
  Y zero    y = add c (λ q → suc q) y
  Y (suc k) y = add c (λ q → q) (Y k y)

  Gk : ℕ → Ordᴵ → LG
  Gk k η = rb₁ (Y k (em η))

  Ys : ∀ k x → Y k (suc x) ≡ suc (Y k x)
  Ys zero x = refl
  Ys (suc k) x = cong (add c (λ q → q)) (Ys k x)

  Yl : ∀ k (h : ℕ → Ordᶜ zero) → Y k (lim h) ≡ lim (λ n → Y k (h n))
  Yl zero h = refl
  Yl (suc k) h = cong (add c (λ q → q)) (Yl k h)

  sub-adm : ∀ {E a b x} (e : b ≡ a) (P : Cp x (rb₁ b)) → AdmC E P → AdmC E (subst (λ z → Cp x (rb₁ z)) e P)
  sub-adm refl P a = a

  I : ℕ → TailI
  I k = record
    { G = Gk k ; t₁ = rb₁ (Y k (suc zero))
    ; toT = λ P → subst (λ z → Cp _ (rb₁ z)) (sym′ (Ys k zero)) (suc P)
    ; adT = λ P a → sub-adm (sym′ (Ys k zero)) (suc P) a }
    where
    sym′ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym′ refl = refl

  vsS : ∀ {x} {u : Ordᶜ (suc zero)} (P : Cp x (rb₁ (suc u))) → (Σ (Cp x (rb₁ u)) λ P′ → ∀ E → AdmC E P → AdmC E P′) ⊎ ⊤
  vsS self = inj₂ tt
  vsS (suc P) = inj₁ (P , (λ _ a → a))

  vlS : ∀ {x} {h : ℕ → Ordᶜ (suc zero)} (P : Cp x (rb₁ (lim h))) → (Σ ℕ λ n → Σ (Cp x (rb₁ (h n))) λ P′ → ∀ E → AdmC E P → AdmC E P′) ⊎ ⊤
  vlS self = inj₂ tt
  vlS (lim n P) = inj₁ (n , P , (λ _ a → a))

  vs : ∀ k b {x} (P : Cp x (Gk k (suc b))) → VS (Gk k) b P
  vs k b P with vsS (subst (λ z → Cp _ (rb₁ z)) (Ys k (em b)) P)
  ... | inj₂ _ = vS₀
  ... | inj₁ (P′ , tr) = vS₁ P′ (λ E a → tr E (sub-adm (Ys k (em b)) P a))

  vl : ∀ k f s {x} (P : Cp x (Gk k (lim f s))) → VL (Gk k) f s P
  vl k f s P with vlS {h = λ n → Y k (em (f n))} (subst (λ z → Cp _ (rb₁ z)) (Yl k (λ n → em (f n))) P)
  ... | inj₂ _ = vL₀
  ... | inj₁ (n , P′ , tr) = vL₁ n P′ (λ E a → tr E (sub-adm (Yl k (λ n → em (f n))) P a))

  rdK : ∀ k → Rdr (suc zero) (rb₁ (Y k (suc zero))) (λ η e → Gk k η)
  rdK k = Tail.rdA (I k) (vs k) (vl k)

  tcS : ∀ {u v : Ordᶜ (suc zero)} → u ≡ v → Tc (rb₁ v) → Tc (rb₁ u)
  tcS refl t = t

  Tc-c : Tc (rb₁ c)
  Tc-c = RdΩ₁.rdA , tt , (λ η e → RdΩ₁.Tc-em η)

  eqL : ∀ k → Y (suc k) zero ≡ limᵢ zero (Y k)
  eqL zero = refl
  eqL (suc k) = cong (add c (λ q → q)) (eqL k)

  Tc-Y0 : ∀ k → Tc (rb₁ (Y k zero))
  Tc-Gk : ∀ k η → Tc (Gk k η)

  Tc-Y0 zero = Tc-c
  Tc-Y0 (suc k) = tcS (eqL k) (rdK k , Tc-Gk k (suc zero) , (λ η e → Tc-Gk k η))

  Tc-Gk k zero = Tc-Y0 k
  Tc-Gk k (suc b) = tcS (Ys k (em b)) (Tc-Gk k b)
  Tc-Gk k (lim f s) = tcS (Yl k (λ n → em (f n))) (λ n → Tc-Gk k (f n))

  eqI : ∀ k → iter (c +_) zero (suc k) ≡ Y k zero
  eqI zero = refl
  eqI (suc k) = cong (add c (λ q → q)) (eqI k)

  Tc-iter : ∀ n → Tc (rb₁ (iter (c +_) zero n))
  Tc-iter zero = tt
  Tc-iter (suc k) = tcS (eqI k) (Tc-Y0 k)
```
