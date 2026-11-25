# YiEmb2Le：带反向推导的层间比较，折叠单调落进 `≼ˣ`

**验收文件，档位：编译定理 (对一般的嵌入关系 E, E′)。** 照 `BTBOFullLe` 的 `LeE` 改写 (`Allow = ⊥`，去掉 `Lb`)：关系 `Lx` 与 `LeE.Le` 同形，只是后继对后继 (`Ls`) 另带一条反向关系 `B.Le b a` (E′ 上的 `LeE`)。`Le-ψ⁰ˣ : Lx x y → ψ⁰ x ≼ˣ ψ⁰ y`；`Lx` 对 Ω、加法、折叠封闭 (`Le-ψ`)，所需的反向推导由 `B` 一侧的同名引理与 `flip : E i i′ → E′ i′ i` 给出。
实例与定理 `VMˣ₂` 见 [YiEmb2](YiEmb2.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEmb2Le where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_)
open import OCF.Align.BTBOFullLe using (module LeE; Cl; cl0; cl-tr⁻; cl-tr; Cl-back; Cl-back⁻)
open import OCF.Align.YiVmConExact using (_≼ˣ_; zˣ; ≼lˣ; lˣ; reflˣ)
open import OCF.Lean.YiZeroAccP using (+ˣ)
open Restr
```

## 1 `≼ˣ` 的两条小引理 (一切层)

```agda
one≼ˣ : ∀ {k} (y : Ordᶜ k) → suc zero ≼ˣ ψ⁰ y
one≼ˣ zero               = reflˣ _
one≼ˣ (suc b)            = ≼lˣ 1 (one≼ˣ b)
one≼ˣ (lim g)            = ≼lˣ 0 (one≼ˣ (g 0))
one≼ˣ (limᵢ {i = j} q f) = ≼lˣ 0 (one≼ˣ (f (into (<→◃ q) (Ω j))))
one≼ˣ (up zero x)        = one≼ˣ x
one≼ˣ (up (self n) x)    = one≼ˣ x

iterˣ : ∀ {A A′ : Ordᶜ zero} → A ≼ˣ A′ → A′ ≼ A → ∀ n → iter (A +_) zero n ≼ˣ iter (A′ +_) zero n
iterˣ d r zero    = zˣ
iterˣ d r (suc n) = +ˣ d r (iterˣ d r n)
```

## 2 关系

```agda
module Two (E : Ordᴵ → Ordᴵ → Set) (resp : ∀ {a b a′ b′} → E a b → a ≅ᴵ a′ → b ≅ᴵ b′ → E a′ b′)
           (E′ : Ordᴵ → Ordᴵ → Set) (resp′ : ∀ {a b a′ b′} → E′ a b → a ≅ᴵ a′ → b ≅ᴵ b′ → E′ a′ b′) where

  module B = LeE E′ resp′ ⊥

  module _ (k : Ordᴵ) (X< : (i : Ordᴵ) (r : i ◃ k) → U i r → ∀ {k₁} → Ordᶜ k₁ → Set) where
    data Lx₊ : ∀ {k₁} → Ordᶜ k₁ → Ordᶜ k → Set where
      Lz  : ∀ {k₁} {b : Ordᶜ k} → Lx₊ {k₁} zero b
      Ls  : ∀ {k₁} {a : Ordᶜ k₁} {b : Ordᶜ k} → Lx₊ a b → B.Le b a → Lx₊ (suc a) (suc b)
      Lsr : ∀ {k₁} {a : Ordᶜ k₁} {b : Ordᶜ k} → Lx₊ a b → Lx₊ a (suc b)
      Lll : ∀ {k₁} {f : ℕ → Ordᶜ k₁} {b : Ordᶜ k} → (∀ n → Lx₊ (f n) b) → Lx₊ (lim f) b
      Llr : ∀ {k₁} {a : Ordᶜ k₁} {g : ℕ → Ordᶜ k} n → Lx₊ a (g n) → Lx₊ a (lim g)
      Lii : ∀ {k₁ j j′} {p : j <ᴵ k₁} {p′ : j′ <ᴵ k} {f : U j (<→◃ p) → Ordᶜ k₁} {g : U j′ (<→◃ p′) → Ordᶜ k} →
            E j j′ →
            (∀ (z : Ordᶜ j) (z′ : Ordᶜ j′) → X< j′ (<→◃ p′) (into (<→◃ p′) z′) z →
               Lx₊ (f (into (<→◃ p) z)) (g (into (<→◃ p′) z′))) →
            Lx₊ (limᵢ p f) (limᵢ p′ g)
      Lir : ∀ {k₁ j′} {a : Ordᶜ k₁} {p′ : j′ <ᴵ k} {g : U j′ (<→◃ p′) → Ordᶜ k} →
            (∀ (z′ : Ordᶜ j′) → Cl j′ z′ → Lx₊ a (g (into (<→◃ p′) z′))) → Lx₊ a (limᵢ p′ g)
      Lul : ∀ {k₁ i} {r : i ◃₁ k₁} {x : U i (◃₁→◃ r)} {b : Ordᶜ k} → Lx₊ (out (◃₁→◃ r) x) b → Lx₊ (up r x) b
      Lur : ∀ {k₁ i} {a : Ordᶜ k₁} {r : i ◃₁ k} {y : U i (◃₁→◃ r)} → X< i (◃₁→◃ r) y a → Lx₊ a (up r y)

  X< : ∀ {k} (i : Ordᴵ) (r : i ◃ k) → U i r → ∀ {k₁} → Ordᶜ k₁ → Set
  X< i zero         y a = Lx₊ i X< a y
  X< i (suc r)      y a = X< i r y a
  X< _ (self {f} n) y a = Lx₊ (f n) X< a y
  X< i (lim n r)    y a = X< i r y a

  Lx : ∀ {k₁ k} → Ordᶜ k₁ → Ordᶜ k → Set
  Lx {k = k} = Lx₊ k X<

  X→Lx : ∀ {i k k₁} (r : i ◃ k) {y : Ordᶜ i} {a : Ordᶜ k₁} → X< i r (into r y) a → Lx a y
  X→Lx zero      d = d
  X→Lx (suc r)   d = X→Lx r d
  X→Lx (self n)  d = d
  X→Lx (lim n r) d = X→Lx r d

  Lx→X : ∀ {i k k₁} (r : i ◃ k) {y : Ordᶜ i} {a : Ordᶜ k₁} → Lx a y → X< i r (into r y) a
  Lx→X zero      d = d
  Lx→X (suc r)   d = Lx→X r d
  Lx→X (self n)  d = d
  Lx→X (lim n r) d = Lx→X r d
```

## 3 沿搬运不变

逐字照 `LeE` §3；`Ls` 的反向推导用 `B` 的对侧引理搬 (右边搬运对应 `B` 的左边搬运)。

```agda
  Lr-tr    : ∀ {a a′ k₁} (e : a ≅ᴵ a′) {y : Ordᶜ a} {x : Ordᶜ k₁} → Lx x y → Lx x (tr e y)
  Lr-tr⁻   : ∀ {a a′ k₁} (e : a ≅ᴵ a′) {y : Ordᶜ a′} {x : Ordᶜ k₁} → Lx x y → Lx x (tr⁻ e y)
  Lr-back  : ∀ {j a b k₁} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} {x : Ordᶜ k₁} → Lx x u → Lx x (back (res q e) u)
  Lr-back⁻ : ∀ {j a b k₁} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} {x : Ordᶜ k₁} → Lx x u → Lx x (back (res⁻ q e) u)

  Lr-tr e Lz        = Lz
  Lr-tr e (Ls d rd) = Ls (Lr-tr e d) (B.Ll-tr e rd)
  Lr-tr e (Lsr d)   = Lsr (Lr-tr e d)
  Lr-tr e (Lll h)   = Lll (λ n → Lr-tr e (h n))
  Lr-tr e (Llr n d) = Llr n (Lr-tr e d)
  Lr-tr e (Lul {r = zero} d)   = Lul (Lr-tr e d)
  Lr-tr e (Lul {r = self n} d) = Lul (Lr-tr e d)
  Lr-tr e (Lii {p′ = q} {g = g} ej h) = Lii (resp ej (≅ᴵ-refl _) (eq (res q e))) (λ z z′ w →
    subst (λ u → Lx _ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z′))
          (Lr-tr e (h z (back (res q e) z′) (Lx→X (<→◃ q) (Lr-back q e (X→Lx (<→◃ (lt (res q e))) w))))))
  Lr-tr e (Lir {p′ = q} {g = g} H) = Lir (λ z′ c →
    subst (λ u → Lx _ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z′))
          (Lr-tr e (H (back (res q e) z′) (Cl-back q e c))))
  Lr-tr (s≅ e) (Lur {r = zero} d)   = Lur (Lr-tr e d)
  Lr-tr (l≅ f) (Lur {r = self n} d) = Lur (Lr-tr (f n) d)

  Lr-tr⁻ e Lz        = Lz
  Lr-tr⁻ e (Ls d rd) = Ls (Lr-tr⁻ e d) (B.Ll-tr⁻ e rd)
  Lr-tr⁻ e (Lsr d)   = Lsr (Lr-tr⁻ e d)
  Lr-tr⁻ e (Lll h)   = Lll (λ n → Lr-tr⁻ e (h n))
  Lr-tr⁻ e (Llr n d) = Llr n (Lr-tr⁻ e d)
  Lr-tr⁻ e (Lul {r = zero} d)   = Lul (Lr-tr⁻ e d)
  Lr-tr⁻ e (Lul {r = self n} d) = Lul (Lr-tr⁻ e d)
  Lr-tr⁻ e (Lii {p′ = q} {g = g} ej h) = Lii (resp ej (≅ᴵ-refl _) (eq (res⁻ q e))) (λ z z′ w →
    subst (λ u → Lx _ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
          (Lr-tr⁻ e (h z (back (res⁻ q e) z′) (Lx→X (<→◃ q) (Lr-back⁻ q e (X→Lx (<→◃ (lt (res⁻ q e))) w))))))
  Lr-tr⁻ e (Lir {p′ = q} {g = g} H) = Lir (λ z′ c →
    subst (λ u → Lx _ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
          (Lr-tr⁻ e (H (back (res⁻ q e) z′) (Cl-back⁻ q e c))))
  Lr-tr⁻ (s≅ e) (Lur {r = zero} d)   = Lur (Lr-tr⁻ e d)
  Lr-tr⁻ (l≅ f) (Lur {r = self n} d) = Lur (Lr-tr⁻ (f n) d)

  Lr-back zero      (s≅ e) d = Lr-tr⁻ e d
  Lr-back (suc q)   (s≅ e) d = Lr-back q e d
  Lr-back (lim n q) (l≅ f) d = Lr-back q (f n) d

  Lr-back⁻ zero      (s≅ e) d = Lr-tr e d
  Lr-back⁻ (suc q)   (s≅ e) d = Lr-back⁻ q e d
  Lr-back⁻ (lim n q) (l≅ f) d = Lr-back⁻ q (f n) d

  Ll-tr    : ∀ {a a′ k} (e : a ≅ᴵ a′) {x : Ordᶜ a} {y : Ordᶜ k} → Lx x y → Lx (tr e x) y
  Ll-tr⁻   : ∀ {a a′ k} (e : a ≅ᴵ a′) {x : Ordᶜ a′} {y : Ordᶜ k} → Lx x y → Lx (tr⁻ e x) y
  Ll-back  : ∀ {j a b k} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} {y : Ordᶜ k} → Lx u y → Lx (back (res q e) u) y
  Ll-back⁻ : ∀ {j a b k} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} {y : Ordᶜ k} → Lx u y → Lx (back (res⁻ q e) u) y

  Ll-tr e Lz        = Lz
  Ll-tr e (Ls d rd) = Ls (Ll-tr e d) (B.Lr-tr e rd)
  Ll-tr e (Lsr d)   = Lsr (Ll-tr e d)
  Ll-tr e (Lll h)   = Lll (λ n → Ll-tr e (h n))
  Ll-tr e (Llr n d) = Llr n (Ll-tr e d)
  Ll-tr e (Lur {r = zero} d)   = Lur (Ll-tr e d)
  Ll-tr e (Lur {r = self n} d) = Lur (Ll-tr e d)
  Ll-tr e (Lir H)   = Lir (λ z′ c → Ll-tr e (H z′ c))
  Ll-tr e (Lii {p = q} {f = f} ej h) = Lii (resp ej (eq (res q e)) (≅ᴵ-refl _)) (λ z z′ w →
    subst (λ u → Lx (tr e (f (into (<→◃ q) (back (res q e) u)))) _) (sym (out-into (<→◃ (lt (res q e))) z))
          (Ll-tr e (h (back (res q e) z) z′ (Lx→X _ (Ll-back q e (X→Lx _ w))))))
  Ll-tr (s≅ e) (Lul {r = zero} d)   = Lul (Ll-tr e d)
  Ll-tr (l≅ f) (Lul {r = self n} d) = Lul (Ll-tr (f n) d)

  Ll-tr⁻ e Lz        = Lz
  Ll-tr⁻ e (Ls d rd) = Ls (Ll-tr⁻ e d) (B.Lr-tr⁻ e rd)
  Ll-tr⁻ e (Lsr d)   = Lsr (Ll-tr⁻ e d)
  Ll-tr⁻ e (Lll h)   = Lll (λ n → Ll-tr⁻ e (h n))
  Ll-tr⁻ e (Llr n d) = Llr n (Ll-tr⁻ e d)
  Ll-tr⁻ e (Lur {r = zero} d)   = Lur (Ll-tr⁻ e d)
  Ll-tr⁻ e (Lur {r = self n} d) = Lur (Ll-tr⁻ e d)
  Ll-tr⁻ e (Lir H)   = Lir (λ z′ c → Ll-tr⁻ e (H z′ c))
  Ll-tr⁻ e (Lii {p = q} {f = f} ej h) = Lii (resp ej (eq (res⁻ q e)) (≅ᴵ-refl _)) (λ z z′ w →
    subst (λ u → Lx (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) u)))) _) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
          (Ll-tr⁻ e (h (back (res⁻ q e) z) z′ (Lx→X _ (Ll-back⁻ q e (X→Lx _ w))))))
  Ll-tr⁻ (s≅ e) (Lul {r = zero} d)   = Lul (Ll-tr⁻ e d)
  Ll-tr⁻ (l≅ f) (Lul {r = self n} d) = Lul (Ll-tr⁻ (f n) d)

  Ll-back zero      (s≅ e) d = Ll-tr⁻ e d
  Ll-back (suc q)   (s≅ e) d = Ll-back q e d
  Ll-back (lim n q) (l≅ f) d = Ll-back q (f n) d

  Ll-back⁻ zero      (s≅ e) d = Ll-tr e d
  Ll-back⁻ (suc q)   (s≅ e) d = Ll-back⁻ q e d
  Ll-back⁻ (lim n q) (l≅ f) d = Ll-back⁻ q (f n) d
```

**加法.** `L-add` 多要左加数的反向推导 `ra`：后继对后继处的反向推导是 `B.L-add ra rd`。不需要 `LeE` 的 `L-add-l` (它只服务于 `Lb`)。

```agda
  L-add-r : ∀ {k₁ k₂ k₃} {a : Ordᶜ k₃} {a′ : Ordᶜ k₂} {σ : Simᴵ k₁ k₂} (b : Ordᶜ k₁) → Lx a a′ → Lx a (add a′ σ b)
  L-add-r zero       d = d
  L-add-r (suc b)    d = Lsr (L-add-r b d)
  L-add-r (lim g)    d = Llr 0 (L-add-r (g 0) d)
  L-add-r {a = a} {a′ = a′} {σ = σ} (limᵢ q g) d = Lir (λ z c →
    subst (λ u → Lx a (add a′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (L-add-r (g (into (<→◃ q) z)) d))
  L-add-r {a = a} {a′ = a′} {σ = σ} (up zero x)     d = L-add-r {a = a} {a′ = a′} {σ = λ q → σ (suc q)} x d
  L-add-r {a = a} {a′ = a′} {σ = σ} (up (self n) x) d = L-add-r {a = a} {a′ = a′} {σ = λ q → σ (lim n q)} x d

  L-add : ∀ {k₁ k₂ k₃ k₄} {a : Ordᶜ k₂} {a′ : Ordᶜ k₄} {σ : Simᴵ k₁ k₂} {σ′ : Simᴵ k₃ k₄} {b : Ordᶜ k₁} {b′ : Ordᶜ k₃} →
          Lx a a′ → B.Le a′ a → Lx b b′ → Lx (add a σ b) (add a′ σ′ b′)
  L-add {b′ = b′} da ra Lz = L-add-r b′ da
  L-add {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} da ra (Ls d rd) = Ls (L-add da ra d) (B.L-add {σ = σ′} {σ′ = σ} ra rd)
  L-add da ra (Lsr d)   = Lsr (L-add da ra d)
  L-add da ra (Lll h)   = Lll (λ n → L-add da ra (h n))
  L-add da ra (Llr n d) = Llr n (L-add da ra d)
  L-add {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} da ra (Lii {p = q₁} {p′ = q} {f = f} {g = g} e h) = Lii e (λ z z′ w →
    subst₂ (λ u v → Lx (add a σ (f (into (<→◃ q₁) u))) (add a′ σ′ (g (into (<→◃ q) v))))
           (sym (out-into (<→◃ (σ q₁)) z)) (sym (out-into (<→◃ (σ′ q)) z′))
           (L-add da ra (h z z′ (Lx→X (<→◃ q) (X→Lx (<→◃ (σ′ q)) w)))))
  L-add {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} {b = b} da ra (Lir {p′ = q} {g = g} H) = Lir (λ z c →
    subst (λ u → Lx (add a σ b) (add a′ σ′ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ′ q)) z)) (L-add da ra (H z c)))
  L-add {σ = σ} da ra (Lul {r = zero} {x = x} d)     = L-add {σ = λ q → σ (suc q)} {b = x} da ra d
  L-add {σ = σ} da ra (Lul {r = self n} {x = x} d)   = L-add {σ = λ q → σ (lim n q)} {b = x} da ra d
  L-add {σ′ = σ′} da ra (Lur {r = zero} {y = y} d)   = L-add {σ′ = λ q → σ′ (suc q)} {b′ = y} da ra d
  L-add {σ′ = σ′} da ra (Lur {r = self n} {y = y} d) = L-add {σ′ = λ q → σ′ (lim n q)} {b′ = y} da ra d

  iter-Lx : ∀ {k k′} {A : Ordᶜ k} {A′ : Ordᶜ k′} → Lx A A′ → B.Le A′ A → ∀ n → Lx (iter (A +_) zero n) (iter (A′ +_) zero n)
  iter-Lx d r zero    = Lz
  iter-Lx d r (suc n) = L-add d r (iter-Lx d r n)
```

## 4 Ω

```agda
  Le-one    : ∀ d₀ {b k} → b ≅ᴵ d₀ → Lx (suc (zero {ℓ = k})) (Ω b)
  Le-one-Cl : ∀ d₀ {d z′ k} → d ≅ᴵ d₀ → Cl d z′ → Lx (suc (zero {ℓ = k})) z′

  Le-one zero z≅             = Ls Lz B.Lz
  Le-one (suc d₁) (s≅ e)     = Lir (λ z′ c → Lur (Le-one-Cl d₁ e c))
  Le-one (lim g s) (l≅ h)    = Llr 0 (Lur (Le-one (g 0) (h 0)))

  Le-one-Cl d₀ e cl0          = Le-one d₀ e
  Le-one-Cl d₀ e (cl-tr⁻ e₂ c) = Lr-tr⁻ e₂ (Le-one-Cl d₀ (≅ᴵ-trans (≅ᴵ-sym e₂) e) c)
  Le-one-Cl d₀ e (cl-tr e₂ c)  = Lr-tr e₂ (Le-one-Cl d₀ (≅ᴵ-trans e₂ e) c)

  walk    : ∀ d₀ {c c″ a′} → a′ ≅ᴵ d₀ → E c c″ → c″ <ᴵ a′ → Lx (Ω (suc c)) (Ω a′)
  walk-Cl : ∀ d₀ {c c″ d z′} → d ≅ᴵ d₀ → E c c″ → c″ ≺ᴵ d → Cl d z′ → Lx (Ω (suc c)) z′

  walk (suc d₁) (s≅ e) ec zero    = Lii ec (λ z z′ w → Lul (Lur w))
  walk (suc d₁) (s≅ e) ec (suc q) = Lir (λ z′ c → Lur (walk-Cl d₁ e ec (via (≅ᴵ-refl _) q) c))
  walk (lim g s) (l≅ h) ec (lim n q) = Llr n (Lur (walk (g n) (h n) ec q))

  walk-Cl d₀ e ec (via e′ q) cl0  = walk d₀ e (resp ec (≅ᴵ-refl _) e′) q
  walk-Cl d₀ e ec r (cl-tr⁻ e₂ c) = Lr-tr⁻ e₂ (walk-Cl d₀ (≅ᴵ-trans (≅ᴵ-sym e₂) e) ec (≺ᴵ-respʳ r e₂) c)
  walk-Cl d₀ e ec r (cl-tr e₂ c)  = Lr-tr e₂ (walk-Cl d₀ (≅ᴵ-trans e₂ e) ec (≺ᴵ-respʳ r (≅ᴵ-sym e₂)) c)
```

## 5 折叠与 ψ⁰

模块参数：E 的两条保持律 (同 `LeE.Laws`)，E′ 一侧的 `LeE.Laws`，翻转 `flip`，以及 `Lx` 的 Ω 律 (实例由 `walk` 证)。`Ls` 的情形用 `B.Le-ψ (flip ei)` 给出折叠后的反向推导。

```agda
  module WithLaws
    (lt-pres : ∀ {a a′ b b′} → E a a′ → E b b′ → a ≺ᴵ b → a′ ≺ᴵ b′)
    (eq-pres : ∀ {a a′ b b′} → E a a′ → E b b′ → a ≅ᴵ b → a′ ≅ᴵ b′)
    (ℒ′ : B.Laws)
    (flip : ∀ {i i′} → E i i′ → E′ i′ i)
    (Ωlaw : ∀ {a a′} → E a a′ → Lx (Ω a) (Ω a′)) where

    open B.WithLaws ℒ′ using () renaming (Le-ψ to Bψ; Le-ψ⁰ to Bψ⁰)

    Le-B1 : ∀ {i i′ k ℓ′} → E i i′ → (p′ : i′ <ᴵ ℓ′) (σ : Simᴵ k ℓ′) (y : Ordᶜ k) → Lx (Ω i) (ψ p′ σ y)
    Le-B1 ei p′ σ zero    = Ωlaw ei
    Le-B1 ei p′ σ (suc a) = Llr 1 (Le-B1 ei p′ σ a)
    Le-B1 ei p′ σ (lim g) = Llr 0 (Le-B1 ei p′ σ (g 0))
    Le-B1 ei p′ σ (limᵢ {i = j} q g) with <ᴵ-dec (σ q) p′
    ... | injᵃ (via e₁ r) = Lir (λ z c →
            subst (λ u → Lx _ (ψ p′ σ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (Le-B1 ei p′ σ (g (into (<→◃ q) (tr⁻ e₁ z)))))
    ... | injᵇ _ = Llr 0 (Le-B1 ei p′ σ (g (into (<→◃ q) (Ω j))))
    ... | injᶜ _ = Llr 0 (Le-B1 ei p′ σ (g (into (<→◃ q) (Ω j))))
    Le-B1 ei p′ σ (up zero x)     = Le-B1 ei p′ (λ q → σ (suc q)) x
    Le-B1 ei p′ σ (up (self n) x) = Le-B1 ei p′ (λ q → σ (lim n q)) x

    clashˣ₁ : ∀ {j j′ i i′} → E j j′ → E i i′ → j ≺ᴵ i → i′ ≺ᴵ j′ → ⊥
    clashˣ₁ ej ei r r′ = ≺ᴵ-irrefl (≺ᴵ-trans (lt-pres ej ei r) r′)

    clashˣ₂ : ∀ {j j′ i i′} → E j j′ → E i i′ → j ≺ᴵ i → j′ ≅ᴵ i′ → ⊥
    clashˣ₂ ej ei r e = ≺ᴵ-irrefl (≺ᴵ-respʳ (lt-pres ej ei r) (≅ᴵ-sym e))

    clashˣ₄ : ∀ {j j′ i i′} → E j j′ → E i i′ → j ≅ᴵ i → j′ ≺ᴵ i′ → ⊥
    clashˣ₄ ej ei e r = ≺ᴵ-irrefl (≺ᴵ-respʳ r (≅ᴵ-sym (eq-pres ej ei e)))

    Le-ψ : ∀ {i i′ k₁ k ℓ ℓ′} {x : Ordᶜ k₁} {y : Ordᶜ k} (ei : E i i′) (p : i <ᴵ ℓ) (σ : Simᴵ k₁ ℓ) (p′ : i′ <ᴵ ℓ′) (σ′ : Simᴵ k ℓ′) →
           Lx x y → Lx (ψ p σ x) (ψ p′ σ′ y)

    chain-L : ∀ {j j′ k₁ k} {q : j <ᴵ k₁} {q′ : j′ <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k₁} {g : U j′ (<→◃ q′) → Ordᶜ k} →
              E j j′ →
              (∀ (z : Ordᶜ j) (z′ : Ordᶜ j′) → X< j′ (<→◃ q′) (into (<→◃ q′) z′) z → Lx (f (into (<→◃ q) z)) (g (into (<→◃ q′) z′))) →
              ∀ n → Lx (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n)
                       (iter (λ x → ψ q′ (λ r → r) (g (into (<→◃ q′) x))) (Ω j′) n)
    chain-L ej h zero = Ωlaw ej
    chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h (suc n) =
      Le-ψ ej q (λ r → r) q′ (λ r → r) (h _ _ (Lx→X (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))

    Le-ψ {y = y} ei p σ p′ σ′ Lz = Le-B1 ei p′ σ′ y
    Le-ψ ei p σ p′ σ′ (Ls d rd)  =
      Lll (λ n → Llr n (iter-Lx (Le-ψ ei p σ p′ σ′ d) (Bψ (flip ei) p′ σ′ p σ rd) n))
    Le-ψ ei p σ p′ σ′ (Lsr d)    = Llr 1 (Le-ψ ei p σ p′ σ′ d)
    Le-ψ ei p σ p′ σ′ (Lll h)    = Lll (λ n → Le-ψ ei p σ p′ σ′ (h n))
    Le-ψ ei p σ p′ σ′ (Llr n d)  = Llr n (Le-ψ ei p σ p′ σ′ d)
    Le-ψ ei p σ p′ σ′ (Lul {r = zero} d)   = Le-ψ ei p (λ q → σ (suc q)) p′ σ′ d
    Le-ψ ei p σ p′ σ′ (Lul {r = self n} d) = Le-ψ ei p (λ q → σ (lim n q)) p′ σ′ d
    Le-ψ ei p σ p′ σ′ (Lur {r = zero} d)   = Le-ψ ei p σ p′ (λ q → σ′ (suc q)) d
    Le-ψ ei p σ p′ σ′ (Lur {r = self n} d) = Le-ψ ei p σ p′ (λ q → σ′ (lim n q)) d
    Le-ψ ei p σ p′ σ′ (Lir {j′ = j′} {p′ = q′} {g = g} H) with <ᴵ-dec (σ′ q′) p′
    ... | injᵃ (via e₁ r) = Lir (λ z c →
            subst (λ u → Lx _ (ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
                  (Le-ψ ei p σ p′ σ′ (H (tr⁻ e₁ z) (cl-tr⁻ e₁ c))))
    ... | injᵇ _ = Llr 0 (Le-ψ ei p σ p′ σ′ (H (Ω j′) cl0))
    ... | injᶜ _ = Llr 0 (Le-ψ ei p σ p′ σ′ (H (Ω j′) cl0))
    Le-ψ ei p σ p′ σ′ (Lii {p = q} {p′ = q′} {f = f} {g = g} ej h) with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
    ... | injᵃ (via e₁ r) | injᵃ (via e₂ r′) = Lii (resp ej e₁ e₂) (λ z z′ w →
            subst₂ (λ u v → Lx (ψ p σ (f (into (<→◃ q) (tr⁻ e₁ u)))) (ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₂ v)))))
                   (sym (out-into (<→◃ r) z)) (sym (out-into (<→◃ r′) z′))
                   (Le-ψ ei p σ p′ σ′ (h (tr⁻ e₁ z) (tr⁻ e₂ z′) (Lx→X (<→◃ q′) (Lr-tr⁻ e₂ (Ll-tr⁻ e₁ (X→Lx (<→◃ r′) w)))))))
    ... | injᵃ (via e₁ r) | injᵇ r′ = ⊥-elim (clashˣ₁ ej ei (via e₁ r) r′)
    ... | injᵃ (via e₁ r) | injᶜ e  = ⊥-elim (clashˣ₂ ej ei (via e₁ r) e)
    ... | injᵇ r′ | injᵃ (via e₂ r) = ⊥-elim (clashˣ₁ ei ej r′ (via e₂ r))
    ... | injᶜ e  | injᵃ (via e₂ r) = ⊥-elim (clashˣ₄ ej ei e (via e₂ r))
    ... | injᵇ _ | injᵇ _ = Lll (λ n → Llr n (Le-ψ ei p σ p′ σ′ (h _ _ (Lx→X (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))
    ... | injᵇ _ | injᶜ _ = Lll (λ n → Llr n (Le-ψ ei p σ p′ σ′ (h _ _ (Lx→X (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))
    ... | injᶜ _ | injᵇ _ = Lll (λ n → Llr n (Le-ψ ei p σ p′ σ′ (h _ _ (Lx→X (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))
    ... | injᶜ _ | injᶜ _ = Lll (λ n → Llr n (Le-ψ ei p σ p′ σ′ (h _ _ (Lx→X (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))
```

`Le-ψ⁰ˣ`：与 `LeE.Le-ψ⁰` 逐支对应，只有 `Ls` 一支要反向的值 (`Bψ⁰ rd`)，交给 `+ˣ`。

```agda
    Le-ψ⁰ˣ : ∀ {k₁ k} {x : Ordᶜ k₁} {y : Ordᶜ k} → Lx x y → ψ⁰ x ≼ˣ ψ⁰ y
    Le-ψ⁰ˣ {y = y} Lz  = one≼ˣ y
    Le-ψ⁰ˣ (Ls d rd)   = lˣ (λ n → ≼lˣ n (iterˣ (Le-ψ⁰ˣ d) (Bψ⁰ rd) n))
    Le-ψ⁰ˣ (Lsr d)     = ≼lˣ 1 (Le-ψ⁰ˣ d)
    Le-ψ⁰ˣ (Lll h)     = lˣ (λ n → Le-ψ⁰ˣ (h n))
    Le-ψ⁰ˣ (Llr n d)   = ≼lˣ n (Le-ψ⁰ˣ d)
    Le-ψ⁰ˣ (Lul {r = zero} {x = x} d)   = Le-ψ⁰ˣ {x = x} d
    Le-ψ⁰ˣ (Lul {r = self n} {x = x} d) = Le-ψ⁰ˣ {x = x} d
    Le-ψ⁰ˣ (Lur {r = zero} {y = y} d)   = Le-ψ⁰ˣ {y = y} d
    Le-ψ⁰ˣ (Lur {r = self n} {y = y} d) = Le-ψ⁰ˣ {y = y} d
    Le-ψ⁰ˣ (Lir {j′ = j′} H)    = ≼lˣ 0 (Le-ψ⁰ˣ (H (Ω j′) cl0))
    Le-ψ⁰ˣ (Lii {p = q} {p′ = q′} {f = f} {g = g} ej h) =
      lˣ (λ n → ≼lˣ n (Le-ψ⁰ˣ (h _ _ (Lx→X (<→◃ q′) (chain-L {q = q} {q′ = q′} {f = f} {g = g} ej h n)))))

    Ψ⁰ˣ : ∀ {a a′} → E a a′ → ψ⁰ (Ω a) ≼ˣ ψ⁰ (Ω a′)
    Ψ⁰ˣ ea = Le-ψ⁰ˣ (Ωlaw ea)
```
