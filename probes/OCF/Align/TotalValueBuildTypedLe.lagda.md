# 旧有界嵌入消费者在实际 Free 层的重基

本篇复用 BTBOFullLe 的完整 LeE 证明，唯一改变是类型底座与值工具
导入。保留异坐标分支、Cl 起点与双方源界内的派发；不引入裸回调单调。
这是验收证明的重复成本，不是成品定义简化。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildTypedLe where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.ValueJudgeBase using (_≼_; z≼; ≼l; l≼; ≼-trans; _≈ᵛ_)
open import OCF.Align.TotalValueBuildTypedValue using (iter-≼; 1≼ψ⁰)
open Restr

σ₀ : ∀ {ℓ} → Simᴵ Ordᴵ.zero ℓ
σ₀ ()

⊑≅ : ∀ {a b c} → a ⊑ᴵ b → b ≅ᴵ c → a ⊑ᴵ c
⊑≅ z⊑ e′ = z⊑
⊑≅ (s⊑ e q) e′ with <-≅ q e′
... | via e″ q′ = s⊑ (≅ᴵ-trans e e″) q′
⊑≅ (l⊑ k) e′ = l⊑ (λ n → ⊑≅ (k n) e′)

```

## §1 链起点的闭包

规则 `Lir` 的前提只看链的起点. 穿透之后新节点的起点是 $\mathtt{tr}^{-}_e\Omega_{j'}$, 字面上不是 $\Omega_j$. `Cl j` 是 $\Omega_j$ 在搬运下的闭包: 比 $z\cong\Omega_j$ 窄, 不需要 PER.

```agda
data Cl : (j : Ordᴵ) → Ordᶜ j → Set where
  cl0   : ∀ {j} → Cl j (Ω j)
  cl-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → Cl b x → Cl a (tr⁻ e x)
  cl-tr  : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → Cl a x → Cl b (tr e x)

Cl-back : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} → Cl (rep (res q e)) u → Cl j (back (res q e) u)
Cl-back zero      (s≅ e) c = cl-tr⁻ e c
Cl-back (suc q)   (s≅ e) c = Cl-back q e c
Cl-back (lim n q) (l≅ f) c = Cl-back q (f n) c

Cl-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} → Cl (rep (res⁻ q e)) u → Cl j (back (res⁻ q e) u)
Cl-back⁻ zero      (s≅ e) c = cl-tr e c
Cl-back⁻ (suc q)   (s≅ e) c = Cl-back⁻ q e c
Cl-back⁻ (lim n q) (l≅ f) c = Cl-back⁻ q (f n) c
```

## §2 关系

```agda
module LeE (E : Ordᴵ → Ordᴵ → Set) (resp : ∀ {a b a′ b′} → E a b → a ≅ᴵ a′ → b ≅ᴵ b′ → E a′ b′) (Allow : Set) where

  module _ (k : Ordᴵ) (L< : (i : Ordᴵ) (r : i ◃ k) → U i r → ∀ {k₁} → Ordᶜ k₁ → Set) where
    data Le₊ : ∀ {k₁} → Ordᶜ k₁ → Ordᶜ k → Set where
      Lz  : ∀ {k₁} {b : Ordᶜ k} → Le₊ {k₁} zero b
      Ls  : ∀ {k₁} {a : Ordᶜ k₁} {b : Ordᶜ k} → Le₊ a b → Le₊ (suc a) (suc b)
      Lsr : ∀ {k₁} {a : Ordᶜ k₁} {b : Ordᶜ k} → Le₊ a b → Le₊ a (suc b)
      Lll : ∀ {k₁} {f : ℕ → Ordᶜ k₁} {b : Ordᶜ k} → (∀ n → Le₊ (f n) b) → Le₊ (lim f) b
      Llr : ∀ {k₁} {a : Ordᶜ k₁} {g : ℕ → Ordᶜ k} n → Le₊ a (g n) → Le₊ a (lim g)
      Lii : ∀ {k₁ j j′} {p : j <ᴵ k₁} {p′ : j′ <ᴵ k} {f : U j (<→◃ p) → Ordᶜ k₁} {g : U j′ (<→◃ p′) → Ordᶜ k} →
            E j j′ →
            (∀ (z : Ordᶜ j) (z′ : Ordᶜ j′) → L< j′ (<→◃ p′) (into (<→◃ p′) z′) z →
               Le₊ (f (into (<→◃ p) z)) (g (into (<→◃ p′) z′))) →
            Le₊ (limᵢ p f) (limᵢ p′ g)
      Lir : ∀ {k₁ j′} {a : Ordᶜ k₁} {p′ : j′ <ᴵ k} {g : U j′ (<→◃ p′) → Ordᶜ k} →
            (∀ (z′ : Ordᶜ j′) → Cl j′ z′ → Le₊ a (g (into (<→◃ p′) z′))) → Le₊ a (limᵢ p′ g)
      Lb  : ∀ {k₁ j′ c} {a : Ordᶜ k₁} {p′ : j′ <ᴵ k} {g : U j′ (<→◃ p′) → Ordᶜ k} → Allow → c ⊑ᴵ j′ →
            (∀ (z′ : Ordᶜ j′) → L< j′ (<→◃ p′) (into (<→◃ p′) z′) (suc (zero {ℓ = Ordᴵ.zero})) → Le₊ (suc (zero {ℓ = Ordᴵ.zero})) (g (into (<→◃ p′) z′))) →
            (∀ (z′ : Ordᶜ j′) → L< j′ (<→◃ p′) (into (<→◃ p′) z′) (suc (Ω c)) → Le₊ a (g (into (<→◃ p′) z′))) →
            Le₊ a (limᵢ p′ g)
      Lul : ∀ {k₁ i} {r : i ◃₁ k₁} {x : U i (◃₁→◃ r)} {b : Ordᶜ k} → Le₊ (out (◃₁→◃ r) x) b → Le₊ (up r x) b
      Lur : ∀ {k₁ i} {a : Ordᶜ k₁} {r : i ◃₁ k} {y : U i (◃₁→◃ r)} → L< i (◃₁→◃ r) y a → Le₊ a (up r y)

  L< : ∀ {k} (i : Ordᴵ) (r : i ◃ k) → U i r → ∀ {k₁} → Ordᶜ k₁ → Set
  L< i zero         y a = Le₊ i L< a y
  L< i (suc r)      y a = L< i r y a
  L< _ (self {f} n) y a = Le₊ (f n) L< a y
  L< i (lim n r)    y a = L< i r y a

  Le : ∀ {k₁ k} → Ordᶜ k₁ → Ordᶜ k → Set
  Le {k = k} = Le₊ k L<

  L→Le : ∀ {i k k₁} (r : i ◃ k) {y : Ordᶜ i} {a : Ordᶜ k₁} → L< i r (into r y) a → Le a y
  L→Le zero      d = d
  L→Le (suc r)   d = L→Le r d
  L→Le (self n)  d = d
  L→Le (lim n r) d = L→Le r d

  Le→L : ∀ {i k k₁} (r : i ◃ k) {y : Ordᶜ i} {a : Ordᶜ k₁} → Le a y → L< i r (into r y) a
  Le→L zero      d = d
  Le→L (suc r)   d = Le→L r d
  Le→L (self n)  d = d
  Le→L (lim n r) d = Le→L r d
```

## §3 沿搬运不变

右边四个函数与 `BTBOValUp` 的 `M-tr` 一一对应. 左边四个函数只改 `Lii` 的左节点.

```agda
  Lr-tr    : ∀ {a a′ k₁} (e : a ≅ᴵ a′) {y : Ordᶜ a} {x : Ordᶜ k₁} → Le x y → Le x (tr e y)
  Lr-tr⁻   : ∀ {a a′ k₁} (e : a ≅ᴵ a′) {y : Ordᶜ a′} {x : Ordᶜ k₁} → Le x y → Le x (tr⁻ e y)
  Lr-back  : ∀ {j a b k₁} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} {x : Ordᶜ k₁} → Le x u → Le x (back (res q e) u)
  Lr-back⁻ : ∀ {j a b k₁} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} {x : Ordᶜ k₁} → Le x u → Le x (back (res⁻ q e) u)

  Lr-tr e Lz        = Lz
  Lr-tr e (Ls d)    = Ls (Lr-tr e d)
  Lr-tr e (Lsr d)   = Lsr (Lr-tr e d)
  Lr-tr e (Lll h)   = Lll (λ n → Lr-tr e (h n))
  Lr-tr e (Llr n d) = Llr n (Lr-tr e d)
  Lr-tr e (Lul {r = zero} d)   = Lul (Lr-tr e d)
  Lr-tr e (Lul {r = self n} d) = Lul (Lr-tr e d)
  Lr-tr e (Lii {p′ = q} {g = g} ej h) = Lii (resp ej (≅ᴵ-refl _) (eq (res q e))) (λ z z′ w →
    subst (λ u → Le _ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z′))
          (Lr-tr e (h z (back (res q e) z′) (Le→L (<→◃ q) (Lr-back q e (L→Le (<→◃ (lt (res q e))) w))))))
  Lr-tr e (Lir {p′ = q} {g = g} H) = Lir (λ z′ c →
    subst (λ u → Le _ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z′))
          (Lr-tr e (H (back (res q e) z′) (Cl-back q e c))))
  Lr-tr e (Lb {p′ = q} {g = g} α k nz H) = Lb α (⊑≅ k (eq (res q e)))
    (λ z′ w → subst (λ u → Le _ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z′))
                    (Lr-tr e (nz (back (res q e) z′) (Le→L (<→◃ q) (Lr-back q e (L→Le (<→◃ (lt (res q e))) w))))))
    (λ z′ w → subst (λ u → Le _ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z′))
                    (Lr-tr e (H (back (res q e) z′) (Le→L (<→◃ q) (Lr-back q e (L→Le (<→◃ (lt (res q e))) w))))))
  Lr-tr (s≅ e) (Lur {r = zero} d)   = Lur (Lr-tr e d)
  Lr-tr (l≅ f) (Lur {r = self n} d) = Lur (Lr-tr (f n) d)

  Lr-tr⁻ e Lz        = Lz
  Lr-tr⁻ e (Ls d)    = Ls (Lr-tr⁻ e d)
  Lr-tr⁻ e (Lsr d)   = Lsr (Lr-tr⁻ e d)
  Lr-tr⁻ e (Lll h)   = Lll (λ n → Lr-tr⁻ e (h n))
  Lr-tr⁻ e (Llr n d) = Llr n (Lr-tr⁻ e d)
  Lr-tr⁻ e (Lul {r = zero} d)   = Lul (Lr-tr⁻ e d)
  Lr-tr⁻ e (Lul {r = self n} d) = Lul (Lr-tr⁻ e d)
  Lr-tr⁻ e (Lii {p′ = q} {g = g} ej h) = Lii (resp ej (≅ᴵ-refl _) (eq (res⁻ q e))) (λ z z′ w →
    subst (λ u → Le _ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
          (Lr-tr⁻ e (h z (back (res⁻ q e) z′) (Le→L (<→◃ q) (Lr-back⁻ q e (L→Le (<→◃ (lt (res⁻ q e))) w))))))
  Lr-tr⁻ e (Lir {p′ = q} {g = g} H) = Lir (λ z′ c →
    subst (λ u → Le _ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
          (Lr-tr⁻ e (H (back (res⁻ q e) z′) (Cl-back⁻ q e c))))
  Lr-tr⁻ e (Lb {p′ = q} {g = g} α k nz H) = Lb α (⊑≅ k (eq (res⁻ q e)))
    (λ z′ w → subst (λ u → Le _ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
                    (Lr-tr⁻ e (nz (back (res⁻ q e) z′) (Le→L (<→◃ q) (Lr-back⁻ q e (L→Le (<→◃ (lt (res⁻ q e))) w))))))
    (λ z′ w → subst (λ u → Le _ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
                    (Lr-tr⁻ e (H (back (res⁻ q e) z′) (Le→L (<→◃ q) (Lr-back⁻ q e (L→Le (<→◃ (lt (res⁻ q e))) w))))))
  Lr-tr⁻ (s≅ e) (Lur {r = zero} d)   = Lur (Lr-tr⁻ e d)
  Lr-tr⁻ (l≅ f) (Lur {r = self n} d) = Lur (Lr-tr⁻ (f n) d)

  Lr-back zero      (s≅ e) d = Lr-tr⁻ e d
  Lr-back (suc q)   (s≅ e) d = Lr-back q e d
  Lr-back (lim n q) (l≅ f) d = Lr-back q (f n) d

  Lr-back⁻ zero      (s≅ e) d = Lr-tr e d
  Lr-back⁻ (suc q)   (s≅ e) d = Lr-back⁻ q e d
  Lr-back⁻ (lim n q) (l≅ f) d = Lr-back⁻ q (f n) d

  Ll-tr    : ∀ {a a′ k} (e : a ≅ᴵ a′) {x : Ordᶜ a} {y : Ordᶜ k} → Le x y → Le (tr e x) y
  Ll-tr⁻   : ∀ {a a′ k} (e : a ≅ᴵ a′) {x : Ordᶜ a′} {y : Ordᶜ k} → Le x y → Le (tr⁻ e x) y
  Ll-back  : ∀ {j a b k} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} {y : Ordᶜ k} → Le u y → Le (back (res q e) u) y
  Ll-back⁻ : ∀ {j a b k} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} {y : Ordᶜ k} → Le u y → Le (back (res⁻ q e) u) y

  Ll-tr e Lz        = Lz
  Ll-tr e (Ls d)    = Ls (Ll-tr e d)
  Ll-tr e (Lsr d)   = Lsr (Ll-tr e d)
  Ll-tr e (Lll h)   = Lll (λ n → Ll-tr e (h n))
  Ll-tr e (Llr n d) = Llr n (Ll-tr e d)
  Ll-tr e (Lur {r = zero} d)   = Lur (Ll-tr e d)
  Ll-tr e (Lur {r = self n} d) = Lur (Ll-tr e d)
  Ll-tr e (Lb α k nz H) = Lb α k nz (λ z′ w → Ll-tr e (H z′ w))
  Ll-tr e (Lir H)   = Lir (λ z′ c → Ll-tr e (H z′ c))
  Ll-tr e (Lii {p = q} {f = f} ej h) = Lii (resp ej (eq (res q e)) (≅ᴵ-refl _)) (λ z z′ w →
    subst (λ u → Le (tr e (f (into (<→◃ q) (back (res q e) u)))) _) (sym (out-into (<→◃ (lt (res q e))) z))
          (Ll-tr e (h (back (res q e) z) z′ (Le→L _ (Ll-b q e (L→Le _ w))))))
    where Ll-b = Ll-back
  Ll-tr (s≅ e) (Lul {r = zero} d)   = Lul (Ll-tr e d)
  Ll-tr (l≅ f) (Lul {r = self n} d) = Lul (Ll-tr (f n) d)

  Ll-tr⁻ e Lz        = Lz
  Ll-tr⁻ e (Ls d)    = Ls (Ll-tr⁻ e d)
  Ll-tr⁻ e (Lsr d)   = Lsr (Ll-tr⁻ e d)
  Ll-tr⁻ e (Lll h)   = Lll (λ n → Ll-tr⁻ e (h n))
  Ll-tr⁻ e (Llr n d) = Llr n (Ll-tr⁻ e d)
  Ll-tr⁻ e (Lur {r = zero} d)   = Lur (Ll-tr⁻ e d)
  Ll-tr⁻ e (Lur {r = self n} d) = Lur (Ll-tr⁻ e d)
  Ll-tr⁻ e (Lb α k nz H) = Lb α k nz (λ z′ w → Ll-tr⁻ e (H z′ w))
  Ll-tr⁻ e (Lir H)   = Lir (λ z′ c → Ll-tr⁻ e (H z′ c))
  Ll-tr⁻ e (Lii {p = q} {f = f} ej h) = Lii (resp ej (eq (res⁻ q e)) (≅ᴵ-refl _)) (λ z z′ w →
    subst (λ u → Le (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) u)))) _) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
          (Ll-tr⁻ e (h (back (res⁻ q e) z) z′ (Le→L _ (Ll-b q e (L→Le _ w))))))
    where Ll-b = Ll-back⁻
  Ll-tr⁻ (s≅ e) (Lul {r = zero} d)   = Lul (Ll-tr⁻ e d)
  Ll-tr⁻ (l≅ f) (Lul {r = self n} d) = Lul (Ll-tr⁻ (f n) d)

  Ll-back zero      (s≅ e) d = Ll-tr⁻ e d
  Ll-back (suc q)   (s≅ e) d = Ll-back q e d
  Ll-back (lim n q) (l≅ f) d = Ll-back q (f n) d

  Ll-back⁻ zero      (s≅ e) d = Ll-tr e d
  Ll-back⁻ (suc q)   (s≅ e) d = Ll-back⁻ q e d
  Ll-back⁻ (lim n q) (l≅ f) d = Ll-back⁻ q (f n) d
```

**加法.**

```agda
  L-add-r : ∀ {k₁ k₂ k₃} {a : Ordᶜ k₃} {a′ : Ordᶜ k₂} {σ : Simᴵ k₁ k₂} (b : Ordᶜ k₁) → Le a a′ → Le a (add a′ σ b)
  L-add-r zero       d = d
  L-add-r (suc b)    d = Lsr (L-add-r b d)
  L-add-r (lim g)    d = Llr 0 (L-add-r (g 0) d)
  L-add-r {a = a} {a′ = a′} {σ = σ} (limᵢ q g) d = Lir (λ z c →
    subst (λ u → Le a (add a′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (L-add-r (g (into (<→◃ q) z)) d))
  L-add-r {a = a} {a′ = a′} {σ = σ} (up zero x)     d = L-add-r {a = a} {a′ = a′} {σ = λ q → σ (suc q)} x d
  L-add-r {a = a} {a′ = a′} {σ = σ} (up (self n) x) d = L-add-r {a = a} {a′ = a′} {σ = λ q → σ (lim n q)} x d

  L-add-l : ∀ {k₁ k₂ k₃} {x : Ordᶜ k₃} {a′ : Ordᶜ k₂} {σ′ : Simᴵ k₁ k₂} {b′ : Ordᶜ k₁} → Le x b′ → Le x (add a′ σ′ b′)
  L-add-l Lz        = Lz
  L-add-l (Ls d)    = Ls (L-add-l d)
  L-add-l (Lsr d)   = Lsr (L-add-l d)
  L-add-l (Lll h)   = Lll (λ n → L-add-l (h n))
  L-add-l (Llr n d) = Llr n (L-add-l d)
  L-add-l (Lul {r = zero} d)   = Lul (L-add-l d)
  L-add-l (Lul {r = self n} d) = Lul (L-add-l d)
  L-add-l {x = x} {a′ = a′} {σ′ = σ′} (Lii {p′ = q} {g = g} e h) = Lii e (λ z z′ w →
    subst (λ u → Le _ (add a′ σ′ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ′ q)) z′))
          (L-add-l (h z z′ (Le→L (<→◃ q) (L→Le (<→◃ (σ′ q)) w)))))
  L-add-l {x = x} {a′ = a′} {σ′ = σ′} (Lir {p′ = q} {g = g} H) = Lir (λ z c →
    subst (λ u → Le x (add a′ σ′ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ′ q)) z)) (L-add-l (H z c)))
  L-add-l {x = x} {a′ = a′} {σ′ = σ′} (Lb {p′ = q} {g = g} α k nz H) = Lb α k
    (λ z w → subst (λ u → Le (suc zero) (add a′ σ′ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ′ q)) z))
                   (L-add-l (nz z (Le→L (<→◃ q) (L→Le (<→◃ (σ′ q)) w)))))
    (λ z w → subst (λ u → Le x (add a′ σ′ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ′ q)) z))
                   (L-add-l (H z (Le→L (<→◃ q) (L→Le (<→◃ (σ′ q)) w)))))
  L-add-l {σ′ = σ′} (Lur {r = zero} {y = y} d)   = L-add-l {σ′ = λ q → σ′ (suc q)} {b′ = y} d
  L-add-l {σ′ = σ′} (Lur {r = self n} {y = y} d) = L-add-l {σ′ = λ q → σ′ (lim n q)} {b′ = y} d

  L-add : ∀ {k₁ k₂ k₃ k₄} {a : Ordᶜ k₂} {a′ : Ordᶜ k₄} {σ : Simᴵ k₁ k₂} {σ′ : Simᴵ k₃ k₄} {b : Ordᶜ k₁} {b′ : Ordᶜ k₃} →
          Le a a′ → Le b b′ → Le (add a σ b) (add a′ σ′ b′)
  L-add {b′ = b′} da Lz = L-add-r b′ da
  L-add da (Ls d)    = Ls (L-add da d)
  L-add da (Lsr d)   = Lsr (L-add da d)
  L-add da (Lll h)   = Lll (λ n → L-add da (h n))
  L-add da (Llr n d) = Llr n (L-add da d)
  L-add {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} da (Lii {p = q₁} {p′ = q} {f = f} {g = g} e h) = Lii e (λ z z′ w →
    subst₂ (λ u v → Le (add a σ (f (into (<→◃ q₁) u))) (add a′ σ′ (g (into (<→◃ q) v))))
           (sym (out-into (<→◃ (σ q₁)) z)) (sym (out-into (<→◃ (σ′ q)) z′))
           (L-add da (h z z′ (Le→L (<→◃ q) (L→Le (<→◃ (σ′ q)) w)))))
  L-add {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} {b = b} da (Lir {p′ = q} {g = g} H) = Lir (λ z c →
    subst (λ u → Le (add a σ b) (add a′ σ′ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ′ q)) z)) (L-add da (H z c)))
  L-add {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} {b = b} da (Lb {p′ = q} {g = g} α k nz H) = Lb α k
    (λ z w → subst (λ u → Le (suc zero) (add a′ σ′ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ′ q)) z))
                   (L-add-l (nz z (Le→L (<→◃ q) (L→Le (<→◃ (σ′ q)) w)))))
    (λ z w → subst (λ u → Le (add a σ b) (add a′ σ′ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ′ q)) z))
                   (L-add da (H z (Le→L (<→◃ q) (L→Le (<→◃ (σ′ q)) w)))))
  L-add {σ = σ} da (Lul {r = zero} {x = x} d)     = L-add {σ = λ q → σ (suc q)} {b = x} da d
  L-add {σ = σ} da (Lul {r = self n} {x = x} d)   = L-add {σ = λ q → σ (lim n q)} {b = x} da d
  L-add {σ′ = σ′} da (Lur {r = zero} {y = y} d)   = L-add {σ′ = λ q → σ′ (suc q)} {b′ = y} da d
  L-add {σ′ = σ′} da (Lur {r = self n} {y = y} d) = L-add {σ′ = λ q → σ′ (lim n q)} {b′ = y} da d

  iter-Le : ∀ {k k′} {A : Ordᶜ k} {A′ : Ordᶜ k′} → Le A A′ → ∀ n → Le (iter (A +_) zero n) (iter (A′ +_) zero n)
  iter-Le d zero    = Lz
  iter-Le d (suc n) = L-add d (iter-Le d n)
```

## §4 $\Omega$

`Laws` 是对 $E$ 的全部要求. `Ωlaw` 由实例用 `walk` 证. `Allow` 决定这个实例用不用 `Lb`: 只有 $E=\cong^\mathsf{I}$ 用, 保序嵌入取 $\bot$.

```agda
  record Laws : Set₁ where
    field
      lt-pres : ∀ {a a′ b b′} → E a a′ → E b b′ → a ≺ᴵ b → a′ ≺ᴵ b′
      eq-pres : ∀ {a a′ b b′} → E a a′ → E b b′ → a ≅ᴵ b → a′ ≅ᴵ b′
      Ωlaw    : ∀ {a a′} → E a a′ → Le (Ω a) (Ω a′)
      Ωc      : ∀ {c j} → Allow → c ⊑ᴵ j → Le (Ω c) (Ω j)

  𝟏′ : ∀ {k} → Ordᶜ k
  𝟏′ = suc zero

  Le-one    : ∀ d₀ {b k} → b ≅ᴵ d₀ → Le (𝟏′ {k}) (Ω b)
  Le-one-Cl : ∀ d₀ {d z′ k} → d ≅ᴵ d₀ → Cl d z′ → Le (𝟏′ {k}) z′

  Le-one zero z≅             = Ls Lz
  Le-one (suc d₁) (s≅ e)     = Lir (λ z′ c → Lur (Le-one-Cl d₁ e c))
  Le-one (lim g s) (l≅ h)    = Llr 0 (Lur (Le-one (g 0) (h 0)))

  Le-one-Cl d₀ e cl0          = Le-one d₀ e
  Le-one-Cl d₀ e (cl-tr⁻ e₂ c) = Lr-tr⁻ e₂ (Le-one-Cl d₀ (≅ᴵ-trans (≅ᴵ-sym e₂) e) c)
  Le-one-Cl d₀ e (cl-tr e₂ c)  = Lr-tr e₂ (Le-one-Cl d₀ (≅ᴵ-trans e₂ e) c)

  walk    : ∀ d₀ {c c″ a′} → a′ ≅ᴵ d₀ → E c c″ → c″ <ᴵ a′ → Le (Ω (suc c)) (Ω a′)
  walk-Cl : ∀ d₀ {c c″ d z′} → d ≅ᴵ d₀ → E c c″ → c″ ≺ᴵ d → Cl d z′ → Le (Ω (suc c)) z′

  walk (suc d₁) (s≅ e) ec zero    = Lii ec (λ z z′ w → Lul (Lur w))
  walk (suc d₁) (s≅ e) ec (suc q) = Lir (λ z′ c → Lur (walk-Cl d₁ e ec (via (≅ᴵ-refl _) q) c))
  walk (lim g s) (l≅ h) ec (lim n q) = Llr n (Lur (walk (g n) (h n) ec q))

  walk-Cl d₀ e ec (via e′ q) cl0  = walk d₀ e (resp ec (≅ᴵ-refl _) e′) q
  walk-Cl d₀ e ec r (cl-tr⁻ e₂ c) = Lr-tr⁻ e₂ (walk-Cl d₀ (≅ᴵ-trans (≅ᴵ-sym e₂) e) ec (≺ᴵ-respʳ r e₂) c)
  walk-Cl d₀ e ec r (cl-tr e₂ c)  = Lr-tr e₂ (walk-Cl d₀ (≅ᴵ-trans e₂ e) ec (≺ᴵ-respʳ r (≅ᴵ-sym e₂)) c)

  ≺⊑ : ∀ {c b a} → c ≺ᴵ b → b ⊑ᴵ a → c ≺ᴵ a
  ≺⊑ (via e q) k = ≺ᴵ-respˡ e (sim k q)

  module WithLaws (ℒ : Laws) where
    open Laws ℒ

    Le-Ω : ∀ {a a′} → E a a′ → Le (Ω a) (Ω a′)
    Le-Ω = Ωlaw

    Le-B1 : ∀ {i i′ k ℓ′} → E i i′ → (p′ : i′ <ᴵ ℓ′) (σ : Simᴵ k ℓ′) (y : Ordᶜ k) → Le (Ω i) (ψ p′ σ y)
    Le-B1 ei p′ σ zero    = Le-Ω ei
    Le-B1 ei p′ σ (suc a) = Llr 1 (Le-B1 ei p′ σ a)
    Le-B1 ei p′ σ (lim g) = Llr 0 (Le-B1 ei p′ σ (g 0))
    Le-B1 ei p′ σ (limᵢ {i = j} q g) with <ᴵ-dec (σ q) p′
    ... | injᵃ (via e₁ r) = Lir (λ z c →
            subst (λ u → Le _ (ψ p′ σ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (Le-B1 ei p′ σ (g (into (<→◃ q) (tr⁻ e₁ z)))))
    ... | injᵇ _ = Llr 0 (Le-B1 ei p′ σ (g (into (<→◃ q) (Ω j))))
    ... | injᶜ _ = Llr 0 (Le-B1 ei p′ σ (g (into (<→◃ q) (Ω j))))
    Le-B1 ei p′ σ (up zero x)     = Le-B1 ei p′ (λ q → σ (suc q)) x
    Le-B1 ei p′ σ (up (self n) x) = Le-B1 ei p′ (λ q → σ (lim n q)) x
```

## §5 折叠

左右两条链都从 $\Omega$ 起, 逐项相关. 混合派发由 `lt-pres`, `eq-pres` 排除.

```agda
    clashᴸ₁ : ∀ {j j′ i i′} → E j j′ → E i i′ → j ≺ᴵ i → i′ ≺ᴵ j′ → ⊥
    clashᴸ₁ ej ei r r′ = ≺ᴵ-irrefl (≺ᴵ-trans (lt-pres ej ei r) r′)

    clashᴸ₂ : ∀ {j j′ i i′} → E j j′ → E i i′ → j ≺ᴵ i → j′ ≅ᴵ i′ → ⊥
    clashᴸ₂ ej ei r e = ≺ᴵ-irrefl (≺ᴵ-respʳ (lt-pres ej ei r) (≅ᴵ-sym e))

    clashᴸ₃ : ∀ {j j′ i i′} → E j j′ → E i i′ → i ≺ᴵ j → j′ ≺ᴵ i′ → ⊥
    clashᴸ₃ ej ei r r′ = clashᴸ₁ ei ej r r′

    clashᴸ₄ : ∀ {j j′ i i′} → E j j′ → E i i′ → j ≅ᴵ i → j′ ≺ᴵ i′ → ⊥
    clashᴸ₄ ej ei e r = ≺ᴵ-irrefl (≺ᴵ-respʳ r (≅ᴵ-sym (eq-pres ej ei e)))

    gen : ∀ {j k₁ ℓ k} {a : Ordᶜ k₁} → Le a (Ω j) → (p : j <ᴵ ℓ) (σ : Simᴵ k ℓ) (y : Ordᶜ k) → Le a (ψ p σ y)
    gen d p σ zero    = d
    gen d p σ (suc y) = Llr 1 (gen d p σ y)
    gen d p σ (lim g) = Llr 0 (gen d p σ (g 0))
    gen {a = a} d p σ (limᵢ {i = j} q g) with <ᴵ-dec (σ q) p
    ... | injᵃ (via e₁ r) = Lir (λ z c →
            subst (λ u → Le a (ψ p σ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (gen d p σ (g (into (<→◃ q) (tr⁻ e₁ z)))))
    ... | injᵇ _ = Llr 0 (gen d p σ (g (into (<→◃ q) (Ω j))))
    ... | injᶜ _ = Llr 0 (gen d p σ (g (into (<→◃ q) (Ω j))))
    gen d p σ (up zero x)     = gen d p (λ q → σ (suc q)) x
    gen d p σ (up (self n) x) = gen d p (λ q → σ (lim n q)) x

    one-ψ : ∀ {j ℓ k} {k₁} (p : j <ᴵ ℓ) (σ : Simᴵ k ℓ) (y : Ordᶜ k) → Le (𝟏′ {k₁}) (ψ p σ y)
    one-ψ {j} p σ y = gen (Le-one j (≅ᴵ-refl j)) p σ y

    Le-ψ : ∀ {i i′ k₁ k ℓ ℓ′} {x : Ordᶜ k₁} {y : Ordᶜ k} (ei : E i i′) (p : i <ᴵ ℓ) (σ : Simᴵ k₁ ℓ) (p′ : i′ <ᴵ ℓ′) (σ′ : Simᴵ k ℓ′) →
           Le x y → Le (ψ p σ x) (ψ p′ σ′ y)

    Sbt : ∀ {c j ℓ k} → Le (Ω c) (Ω j) → (p : j <ᴵ ℓ) (σ : Simᴵ k ℓ) {w : Ordᶜ k} → Le (𝟏′ {Ordᴵ.zero}) w → Le (suc (Ω c)) (ψ p σ w)
    Sbt d p σ {w = suc b} (Ls _) = Llr 2 (L-add {k₁ = Ordᴵ.zero} {σ = σ₀} {σ′ = λ q → q} (gen d p σ b) (one-ψ p σ b))
    Sbt d p σ {w = suc b} (Lsr x) = Llr 1 (Sbt d p σ x)
    Sbt d p σ (Llr n x) = Llr n (Sbt d p σ x)
    Sbt {c} d p σ (Lir {j′ = j′} {p′ = q} {g = g} H) with <ᴵ-dec (σ q) p
    ... | injᵃ (via e₁ r) = Lir (λ z cl →
            subst (λ u → Le (suc (Ω c)) (ψ p σ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (Sbt d p σ (H (tr⁻ e₁ z) (cl-tr⁻ e₁ cl))))
    ... | injᵇ _ = Llr 0 (Sbt d p σ (H (Ω j′) cl0))
    ... | injᶜ _ = Llr 0 (Sbt d p σ (H (Ω j′) cl0))
    Sbt {c} d p σ (Lb {j′ = j′} {p′ = q} {g = g} α k nz H) with <ᴵ-dec (σ q) p
    ... | injᵃ (via e₁ r) = Lb α (⊑≅ k e₁)
            (λ z w → subst (λ u → Le (suc zero) (ψ p σ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z)) (one-ψ p σ _))
            (λ z w → subst (λ u → Le (suc (Ω c)) (ψ p σ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (Sbt d p σ (H (tr⁻ e₁ z) (Le→L (<→◃ q) (Lr-tr⁻ e₁ (L→Le (<→◃ r) w))))))
    ... | injᵇ _ = Llr 1 (Sbt d p σ (H _ (Le→L (<→◃ q) (Sbt (Ωc α k) q (λ r → r) (nz (Ω j′) (Le→L (<→◃ q) (Le-one j′ (≅ᴵ-refl j′))))))))
    ... | injᶜ _ = Llr 1 (Sbt d p σ (H _ (Le→L (<→◃ q) (Sbt (Ωc α k) q (λ r → r) (nz (Ω j′) (Le→L (<→◃ q) (Le-one j′ (≅ᴵ-refl j′))))))))
    Sbt d p σ (Lur {r = zero} {y = y} x)   = Sbt d p (λ q → σ (suc q)) {w = y} x
    Sbt d p σ (Lur {r = self n} {y = y} x) = Sbt d p (λ q → σ (lim n q)) {w = y} x

    chain-L : ∀ {j j′ k₁ k} {q : j <ᴵ k₁} {q′ : j′ <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k₁} {g : U j′ (<→◃ q′) → Ordᶜ k} →
              E j j′ →
              (∀ (z : Ordᶜ j) (z′ : Ordᶜ j′) → L< j′ (<→◃ q′) (into (<→◃ q′) z′) z → Le (f (into (<→◃ q) z)) (g (into (<→◃ q′) z′))) →
              ∀ n → Le (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n)
                       (iter (λ x → ψ q′ (λ r → r) (g (into (<→◃ q′) x))) (Ω j′) n)
    chain-L ej h zero = Le-Ω ej
    chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h (suc n) =
      Le-ψ ej q (λ r → r) q′ (λ r → r) (h _ _ (Le→L (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))

    Le-ψ {y = y} ei p σ p′ σ′ Lz = Le-B1 ei p′ σ′ y
    Le-ψ ei p σ p′ σ′ (Ls d)     = Lll (λ n → Llr n (iter-Le (Le-ψ ei p σ p′ σ′ d) n))
    Le-ψ ei p σ p′ σ′ (Lsr d)    = Llr 1 (Le-ψ ei p σ p′ σ′ d)
    Le-ψ ei p σ p′ σ′ (Lll h)    = Lll (λ n → Le-ψ ei p σ p′ σ′ (h n))
    Le-ψ ei p σ p′ σ′ (Llr n d)  = Llr n (Le-ψ ei p σ p′ σ′ d)
    Le-ψ ei p σ p′ σ′ (Lul {r = zero} d)   = Le-ψ ei p (λ q → σ (suc q)) p′ σ′ d
    Le-ψ ei p σ p′ σ′ (Lul {r = self n} d) = Le-ψ ei p (λ q → σ (lim n q)) p′ σ′ d
    Le-ψ ei p σ p′ σ′ (Lur {r = zero} d)   = Le-ψ ei p σ p′ (λ q → σ′ (suc q)) d
    Le-ψ ei p σ p′ σ′ (Lur {r = self n} d) = Le-ψ ei p σ p′ (λ q → σ′ (lim n q)) d
    Le-ψ {i′ = i′} ei p σ p′ σ′ (Lir {j′ = j′} {p′ = q′} {g = g} H) with <ᴵ-dec (σ′ q′) p′
    ... | injᵃ (via e₁ r) = Lir (λ z c →
            subst (λ u → Le _ (ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (Le-ψ ei p σ p′ σ′ (H (tr⁻ e₁ z) (cl-tr⁻ e₁ c))))
    ... | injᵇ _ = Llr 0 (Le-ψ ei p σ p′ σ′ (H (Ω j′) cl0))
    ... | injᶜ _ = Llr 0 (Le-ψ ei p σ p′ σ′ (H (Ω j′) cl0))
    Le-ψ ei p σ p′ σ′ (Lb {j′ = j′} {p′ = q} {g = g} α k nz H) with <ᴵ-dec (σ′ q) p′
    ... | injᵃ (via e₁ r) = Lb α (⊑≅ k e₁)
            (λ z w → subst (λ u → Le (suc zero) (ψ p′ σ′ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z)) (one-ψ p′ σ′ _))
            (λ z w → subst (λ u → Le _ (ψ p′ σ′ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (Le-ψ ei p σ p′ σ′ (H (tr⁻ e₁ z) (Le→L (<→◃ q) (Lr-tr⁻ e₁ (L→Le (<→◃ r) w))))))
    ... | injᵇ _ = Llr 1 (Le-ψ ei p σ p′ σ′ (H _ (Le→L (<→◃ q) (Sbt (Ωc α k) q (λ r → r) (nz (Ω j′) (Le→L (<→◃ q) (Le-one j′ (≅ᴵ-refl j′))))))))
    ... | injᶜ _ = Llr 1 (Le-ψ ei p σ p′ σ′ (H _ (Le→L (<→◃ q) (Sbt (Ωc α k) q (λ r → r) (nz (Ω j′) (Le→L (<→◃ q) (Le-one j′ (≅ᴵ-refl j′))))))))
    Le-ψ ei p σ p′ σ′ (Lii {p = q} {p′ = q′} {f = f} {g = g} ej h) with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
    ... | injᵃ (via e₁ r) | injᵃ (via e₂ r′) = Lii (resp ej e₁ e₂) (λ z z′ w →
            subst₂ (λ u v → Le (ψ p σ (f (into (<→◃ q) (tr⁻ e₁ u)))) (ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₂ v)))))
                   (sym (out-into (<→◃ r) z)) (sym (out-into (<→◃ r′) z′))
                   (Le-ψ ei p σ p′ σ′ (h (tr⁻ e₁ z) (tr⁻ e₂ z′) (Le→L (<→◃ q′) (Lr-tr⁻ e₂ (Ll-tr⁻ e₁ (L→Le (<→◃ r′) w)))))))
    ... | injᵃ (via e₁ r) | injᵇ r′ = ⊥-elim (clashᴸ₁ ej ei (via e₁ r) r′)
    ... | injᵃ (via e₁ r) | injᶜ e  = ⊥-elim (clashᴸ₂ ej ei (via e₁ r) e)
    ... | injᵇ r′ | injᵃ (via e₂ r) = ⊥-elim (clashᴸ₃ ej ei r′ (via e₂ r))
    ... | injᶜ e  | injᵃ (via e₂ r) = ⊥-elim (clashᴸ₄ ej ei e (via e₂ r))
    ... | injᵇ _ | injᵇ _ = Lll (λ n → Llr n (Le-ψ ei p σ p′ σ′ (h _ _ (Le→L (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))
    ... | injᵇ _ | injᶜ _ = Lll (λ n → Llr n (Le-ψ ei p σ p′ σ′ (h _ _ (Le→L (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))
    ... | injᶜ _ | injᵇ _ = Lll (λ n → Llr n (Le-ψ ei p σ p′ σ′ (h _ _ (Le→L (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))
    ... | injᶜ _ | injᶜ _ = Lll (λ n → Llr n (Le-ψ ei p σ p′ σ′ (h _ _ (Le→L (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))

    Le-ψ⁰ : ∀ {k₁ k} {x : Ordᶜ k₁} {y : Ordᶜ k} → Le x y → ψ⁰ x ≼ ψ⁰ y
    Le-ψ⁰ {y = y} Lz  = 1≼ψ⁰ y
    Le-ψ⁰ (Ls d)      = l≼ (λ n → ≼l n (iter-≼ (Le-ψ⁰ d) n))
    Le-ψ⁰ (Lsr d)     = ≼l 1 (Le-ψ⁰ d)
    Le-ψ⁰ (Lll h)     = l≼ (λ n → Le-ψ⁰ (h n))
    Le-ψ⁰ (Llr n d)   = ≼l n (Le-ψ⁰ d)
    Le-ψ⁰ (Lul {r = zero} {x = x} d)   = Le-ψ⁰ {x = x} d
    Le-ψ⁰ (Lul {r = self n} {x = x} d) = Le-ψ⁰ {x = x} d
    Le-ψ⁰ (Lur {r = zero} {y = y} d)   = Le-ψ⁰ {y = y} d
    Le-ψ⁰ (Lur {r = self n} {y = y} d) = Le-ψ⁰ {y = y} d
    Le-ψ⁰ (Lir {j′ = j′} H)    = ≼l 0 (Le-ψ⁰ (H (Ω j′) cl0))
    Le-ψ⁰ (Lb {j′ = j′} {p′ = q} α k nz H) = ≼l 1 (Le-ψ⁰ (H _ (Le→L (<→◃ q) (Sbt (Ωc α k) q (λ r → r) (nz (Ω j′) (Le→L (<→◃ q) (Le-one j′ (≅ᴵ-refl j′))))))))
    Le-ψ⁰ (Lii {p = q} {p′ = q′} {f = f} {g = g} ej h) =
      l≼ (λ n → ≼l n (Le-ψ⁰ (h _ _ (Le→L (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))

    S-ψ : ∀ {i i′ k₁ k ℓ ℓ′} {u : Ordᶜ k₁} {v : Ordᶜ k} (ei : E i i′) (p : i <ᴵ ℓ) (σ : Simᴵ k₁ ℓ) (p′ : i′ <ᴵ ℓ′) (σ′ : Simᴵ k ℓ′) →
          Le (suc u) v → Le (suc (ψ p σ u)) (ψ p′ σ′ v)
    S-ψ {v = suc b} ei p σ p′ σ′ (Ls d) = Llr 2 (L-add {k₁ = Ordᴵ.zero} {σ = σ₀} {σ′ = λ q → q} (Le-ψ ei p σ p′ σ′ d) (one-ψ p′ σ′ b))
    S-ψ ei p σ p′ σ′ (Lsr d)   = Llr 1 (S-ψ ei p σ p′ σ′ d)
    S-ψ ei p σ p′ σ′ (Llr n d) = Llr n (S-ψ ei p σ p′ σ′ d)
    S-ψ ei p σ p′ σ′ (Lur {r = zero} d)   = S-ψ ei p σ p′ (λ q → σ′ (suc q)) d
    S-ψ ei p σ p′ σ′ (Lur {r = self n} d) = S-ψ ei p σ p′ (λ q → σ′ (lim n q)) d
    S-ψ ei p σ p′ σ′ (Lir {j′ = j′} {p′ = q} {g = g} H) with <ᴵ-dec (σ′ q) p′
    ... | injᵃ (via e₁ r) = Lir (λ z cl →
            subst (λ u → Le _ (ψ p′ σ′ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (S-ψ ei p σ p′ σ′ (H (tr⁻ e₁ z) (cl-tr⁻ e₁ cl))))
    ... | injᵇ _ = Llr 0 (S-ψ ei p σ p′ σ′ (H (Ω j′) cl0))
    ... | injᶜ _ = Llr 0 (S-ψ ei p σ p′ σ′ (H (Ω j′) cl0))
    S-ψ ei p σ p′ σ′ (Lb {j′ = j′} {p′ = q} {g = g} α k nz H) with <ᴵ-dec (σ′ q) p′
    ... | injᵃ (via e₁ r) = Lb α (⊑≅ k e₁)
            (λ z w → subst (λ u → Le (suc zero) (ψ p′ σ′ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z)) (one-ψ p′ σ′ _))
            (λ z w → subst (λ u → Le _ (ψ p′ σ′ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (S-ψ ei p σ p′ σ′ (H (tr⁻ e₁ z) (Le→L (<→◃ q) (Lr-tr⁻ e₁ (L→Le (<→◃ r) w))))))
    ... | injᵇ _ = Llr 1 (S-ψ ei p σ p′ σ′ (H _ (Le→L (<→◃ q) (Sbt (Ωc α k) q (λ r → r) (nz (Ω j′) (Le→L (<→◃ q) (Le-one j′ (≅ᴵ-refl j′))))))))
    ... | injᶜ _ = Llr 1 (S-ψ ei p σ p′ σ′ (H _ (Le→L (<→◃ q) (Sbt (Ωc α k) q (λ r → r) (nz (Ω j′) (Le→L (<→◃ q) (Le-one j′ (≅ᴵ-refl j′))))))))

    Ψ⁰-emb : ∀ {a a′} → E a a′ → ψ⁰ (Ω a) ≼ ψ⁰ (Ω a′)
    Ψ⁰-emb ea = Le-ψ⁰ (Le-Ω ea)
```
