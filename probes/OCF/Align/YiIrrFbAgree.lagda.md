# YiIrrFb 验收 (条件)：新的 ψ₀ 与旧的 ψ 在只含层号 0 的树上字面相等

**档位：条件定理，前提是函数外延 `Funext`；验收文件，不进定义与证书。** `agree`：两个定义域里的同一棵树，
`ψ₀ x ≡ ψ x`。用到外延的两处：极限行，与 gt 行里链的子折叠 (守卫无关的函数，由普通外延推出 `fe-irr`)。
极限行处的字面相等就是两个逐项函数相等 (`agree-lim-is-function-equality`，无条件)，所以没有去找不用外延的证明；
没有否定定理。不用外延的陈述是 [YiIrrFbInst](YiIrrFbInst.lagda.md) 的 `level0-rows`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFbAgree where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim-irr)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (tw)
open import OCF.Align.YiIrrIf
import OCF.Align.YiIrrFoldBase as OB
import OCF.Align.YiIrrFold as OF
open import OCF.Align.YiIrrFbIf
open import OCF.Align.YiIrrFbBase
open import OCF.Align.YiIrrFb
open import OCF.Align.YiIrrFbInst using (dom-Ω₁)

Funext : Set₁
Funext = ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g

record Squash (A : Set) : Set where
  constructor squash
  field
    .proof : A

via : ∀ {A B : Set} → (.A → B) → Squash A → B
via f (squash x) = f x

back : ∀ {A B : Set} → (Squash A → B) → .A → B
back k x = k (squash x)

-- 链只经由子折叠依赖两个 ψ; 子折叠相等时, 两条链的极限定义性相等 (其余参数都落在无关的守卫里).
chain-cong : ∀ c (body body′ : (η : R) → .(Gd zero c η) → R) → body ≡ body′ →
  .(l : ∀ η (e : Gd zero c η) → Lgl zero (body η e))
  .(l′ : ∀ η (e : Gd zero c η) → Lgl zero (body′ η e))
  (pos : ∀ η .(e : Gd zero c η) → Dn zero G.zero (body η e))
  (pos′ : ∀ η .(e : Gd zero c η) → Dn zero G.zero (body′ η e))
  (p : Point c) →
  OB.Chain.collapse c body l pos p ≡ OB.Chain.collapse c body′ l′ pos′ p
chain-cong c body .body refl l l′ pos pos′ p = refl

lim-injective : ∀ {P : Set} {L : P → Set} {Gl : (r : P) → L r → L r → Set}
  {K : Set} {B : K → Set} {f g : ℕ → G.R P L Gl K B} →
  G.lim f ≡ G.lim g → f ≡ g
lim-injective refl = refl

agree-lim-is-function-equality : ∀ f .(d : OB.Dom (lim f)) .(d′ : Dom (lim f)) →
  ψ₀ (lim f) d′ ≡ OF.ψ (lim f) d →
  (λ n → ψ₀ (f n) (dom-at f d′ n)) ≡ (λ n → OF.ψ (f n) (OB.dom-at f d n))
agree-lim-is-function-equality f d d′ q = lim-injective q

module _ (fe : Funext) where

  fe-irr : ∀ {A B : Set} {f g : .A → B} → (∀ .(x : A) → f x ≡ g x) → f ≡ g
  fe-irr {f = f} {g = g} h =
    cong back (fe {f = via f} {g = via g} (λ { (squash x) → h x }))

  agree : ∀ x .(d : OB.Dom x) .(d′ : Dom x) → ψ₀ x d′ ≡ OF.ψ x d
  agree zero d d′ = refl
  agree (suc x) d d′ = cong successor (agree x d d′)
  agree (lim f) d d′ =
    cong G.lim (fe (λ n → agree (f n) (OB.dom-at f d n) (dom-at f d′ n)))
  agree (lc zero c w b t g) d d′ =
    chain-cong c
      (λ η e → ψ₀ (g η e) (Node₀.branch c w b t g d′ η e))
      (λ η e → OF.ψ (g η e) (OB.dom-branch c w b t g d η e))
      (fe (λ η → fe-irr (λ e → agree (g η e)
        (OB.dom-branch c w b t g d η e) (Node₀.branch c w b t g d′ η e))))
      (λ η e → ψ₀-legal (g η e) (Node₀.branch c w b t g d′ η e))
      (λ η e → OF.ψ-legal (g η e) (OB.dom-branch c w b t g d η e))
      (λ η e → ψ₀-positive (g η e) (Node₀.branch c w b t g d′ η e))
      (λ η e → OF.ψ-positive (g η e) (OB.dom-branch c w b t g d η e))
      (start c w b)
  agree (lc (suc k) c w b t g) d d′ = ⊥-elim-irr (proj₁ d)
  agree (lc (lim f) c w b t g) d d′ = ⊥-elim-irr (proj₁ d)
  agree (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d d′ = ⊥-elim-irr (proj₁ d)

  -- 前提可满足的实例: 规范的 Ω₁ 在两个定义域里.
  agree-Ω₁ : ψ₀ (tw 2) dom-Ω₁ ≡ OF.ψ (tw 2) OB.dom-Ω₁
  agree-Ω₁ = agree (tw 2) OB.dom-Ω₁ dom-Ω₁
```
