# 跨族模拟, 向上: src 的折叠不超过 `Ordᶜ` 的折叠

> 接 [BTBOValDn](BTBOValDn.lagda.md). 另一个方向: 在形状相同的层号上, src 的 $\psi_0(\Omega_a)$ 不超过 Level 的 $\psi^0(\Omega_{\tau a})$. 这个方向要吸收 $\Omega_0=\omega$ 对 $1$: 同一个参数 $0$, src 给 $\omega$, Level 给 $1$.
>
> 办法是关系的叶子带条件. `Mh x y` ("$x$ 不超过 $y$") 的叶子 `Mz` 要求 $y$ **非零** (`NZ`). 所以 `Mh` 不是 $x\le y$, 差一点: 它不含 $0$ 对 $0$, 也不含 $1$ 对 $1$, 大致是 $1+x\le y$. 这正好够: 目标层 0 上大致有 $\psi_0^{\mathrm{src}}(x)=\psi^0(1+x)$ (纸面读法, 编译的是 `M-ψ`). 链的起点也一并解决: src 的 $0$ 与 Level 的 $\Omega_j$ 相关, 因为 $\Omega_j$ 非零.
>
> 只有一处要更强的规则 (`Mirω`): 层号的第 0 项. `Ω (lim f)` 的第 0 项可以是 `↑ (Ω 0)` $=\uparrow\omega$, 对面的 $\Omega_{f'1}$ 的第一个分支是 $1$, 够不到 $\omega$. 但 Level 的链第 1 步就过了 $\omega$, 所以规则说 "对一切已经过了 $\omega$ 的输入". 这一步要分支在链起点非零.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOValUp where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; module Trich; injᵃ; injᵇ; injᶜ)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; NonZero)
open S using (iter; ordᴰ; zero; suc; lim; limᵢ)
open import OCF.Align.Level
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValDn using (τ; τ-<; coe-coe₀; clash-lt-lt; clash-lt-eq; clash-gt-lt; clash-eq-lt)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-suc; ≼-trans; ≅→≼)
open Restr
```

## §1 非零

`NZ` 是 Level 树上的归纳谓词, 跨层号. `limᵢ` 只看链的起点 $z\cong\Omega_j$, 这是 `ψ` 读到的那个点 (目标层 0 上第 0 项).

```agda
data NZ : ∀ {k} → Ordᶜ k → Set where
  nzs : ∀ {k} {b : Ordᶜ k} → NZ (suc b)
  nzl : ∀ {k} {g : ℕ → Ordᶜ k} n → NZ (g n) → NZ (lim g)
  nzi : ∀ {k j} {q : j <ᴵ k} {g : U j (<→◃ q) → Ordᶜ k} →
        (∀ (z : Ordᶜ j) → z ≅ Ω j → NZ (g (into (<→◃ q) z))) → NZ (limᵢ q g)
  nzu : ∀ {k i} {r : i ◃₁ k} {x : U i (◃₁→◃ r)} → NZ (out (◃₁→◃ r) x) → NZ (up r x)

≅self : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≅ a
≅self e = ≅-trans e (≅-sym e)

NZ-≅ : ∀ {k k′} {a : Ordᶜ k} {b : Ordᶜ k′} → a ≅ b → NZ b → NZ a
NZ-≅ (upˡ {r = zero} e)   d = nzu (NZ-≅ e d)
NZ-≅ (upˡ {r = self n} e) d = nzu (NZ-≅ e d)
NZ-≅ (upʳ {r = zero} e)   (nzu d) = NZ-≅ e d
NZ-≅ (upʳ {r = self n} e) (nzu d) = NZ-≅ e d
NZ-≅ (s≅ e)   nzs       = nzs
NZ-≅ (l≅ h)   (nzl n d) = nzl n (NZ-≅ (h n) d)
NZ-≅ (lᵢ≅ {p = p} e h) (nzi prem) = nzi (λ z d →
  NZ-≅ (h z (tr e z) (≅→R (<→◃ p) (≅-tr e (≅self d)))) (prem (tr e z) (tr-≅ e (≅-trans d (Ω-≅ e)))))

NZ-Ω : ∀ a → NZ (Ω a)
NZ-Ω zero      = nzs
NZ-Ω (suc c)   = nzi (λ z d → nzu (NZ-≅ d (NZ-Ω c)))
NZ-Ω (lim g s) = nzl 0 (nzu (NZ-Ω (g 0)))

NZ-add-l : ∀ {k₁ k₂} {B : Ordᶜ k₂} {σ : Simᴵ k₁ k₂} → NZ B → (R : Ordᶜ k₁) → NZ (add B σ R)
NZ-add-l nb zero            = nb
NZ-add-l nb (suc R)         = nzs
NZ-add-l nb (lim g)         = nzl 0 (NZ-add-l nb (g 0))
NZ-add-l {B = B} {σ = σ} nb (limᵢ q g) = nzi (λ z d →
  subst (λ u → NZ (add B σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (NZ-add-l nb (g (into (<→◃ q) z))))
NZ-add-l nb (up zero x)     = NZ-add-l nb x
NZ-add-l nb (up (self n) x) = NZ-add-l nb x

NZ-add-r : ∀ {k₁ k₂} {a : Ordᶜ k₂} {σ : Simᴵ k₁ k₂} {b : Ordᶜ k₁} → NZ b → NZ (add a σ b)
NZ-add-r nzs       = nzs
NZ-add-r (nzl n d) = nzl n (NZ-add-r d)
NZ-add-r {a = a} {σ = σ} (nzi {q = q} {g = g} prem) = nzi (λ z d →
  subst (λ u → NZ (add a σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (NZ-add-r (prem z d)))
NZ-add-r {a = a} {σ = σ} (nzu {r = zero} {x = x} d)   = NZ-add-r {a = a} {σ = λ q → σ (suc q)} {b = x} d
NZ-add-r {a = a} {σ = σ} (nzu {r = self n} {x = x} d) = NZ-add-r {a = a} {σ = λ q → σ (lim n q)} {b = x} d

NZ-tr : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → NZ x → NZ (tr e x)
NZ-tr e nzs       = nzs
NZ-tr e (nzl n d) = nzl n (NZ-tr e d)
NZ-tr e (nzi {q = q} {g = g} prem) = nzi (λ z d →
  subst (λ u → NZ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z))
        (NZ-tr e (prem (back (res q e) z) (≅-trans (back-≅ q e d) (Ω-≅ (≅ᴵ-sym (eq (res q e))))))))
NZ-tr (s≅ e) (nzu {r = zero} d)   = nzu (NZ-tr e d)
NZ-tr (l≅ f) (nzu {r = self n} d) = nzu (NZ-tr (f n) d)

NZ-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → NZ x → NZ (tr⁻ e x)
NZ-tr⁻ e nzs       = nzs
NZ-tr⁻ e (nzl n d) = nzl n (NZ-tr⁻ e d)
NZ-tr⁻ e (nzi {q = q} {g = g} prem) = nzi (λ z d →
  subst (λ u → NZ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
        (NZ-tr⁻ e (prem (back (res⁻ q e) z) (≅-trans (back⁻-≅ q e d) (Ω-≅ (≅ᴵ-sym (eq (res⁻ q e))))))))
NZ-tr⁻ (s≅ e) (nzu {r = zero} d)   = nzu (NZ-tr⁻ e d)
NZ-tr⁻ (l≅ f) (nzu {r = self n} d) = nzu (NZ-tr⁻ (f n) d)

NZ-ψ : ∀ {i k ℓ} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (w : Ordᶜ k) → NZ (ψ p σ w)
NZ-ψ {i} p σ zero    = NZ-Ω i
NZ-ψ p σ (suc a)     = nzl 1 (NZ-ψ p σ a)
NZ-ψ p σ (lim g)     = nzl 0 (NZ-ψ p σ (g 0))
NZ-ψ p σ (limᵢ {i = j} q g) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = nzi (λ z d →
        subst (λ u → NZ (ψ p σ (g (into (<→◃ q) (tr⁻ e u))))) (sym (out-into (<→◃ r) z)) (NZ-ψ p σ (g (into (<→◃ q) (tr⁻ e z)))))
... | injᵇ _ = nzl 0 (NZ-ψ p σ (g (into (<→◃ q) (Ω j))))
... | injᶜ _ = nzl 0 (NZ-ψ p σ (g (into (<→◃ q) (Ω j))))
NZ-ψ p σ (up zero x)     = NZ-ψ p (λ q → σ (suc q)) x
NZ-ψ p σ (up (self n) x) = NZ-ψ p (λ q → σ (lim n q)) x
```

## §2 关系

```agda
natˢ : ℕ → S.Ord₀
natˢ zero    = zero
natˢ (suc n) = suc (natˢ n)

module _ (k : Ordᴵ) (M< : (i : Ordᴵ) (r : i ◃ k) → U i r → ∀ {ℓ} → S.Ord ℓ → Set) where
  data Mh₊ : ∀ {ℓ} → S.Ord ℓ → Ordᶜ k → Set where
    Mz  : ∀ {ℓ} {b : Ordᶜ k} → NZ b → Mh₊ {ℓ} zero b
    Ms  : ∀ {ℓ} {a : S.Ord ℓ} {b : Ordᶜ k} → Mh₊ a b → Mh₊ (suc a) (suc b)
    Msr : ∀ {ℓ} {a : S.Ord ℓ} {b : Ordᶜ k} → Mh₊ a b → Mh₊ a (suc b)
    Mll : ∀ {ℓ} {f : ℕ → S.Ord ℓ} {b : Ordᶜ k} → (∀ n → Mh₊ (f n) b) → Mh₊ (lim f) b
    Mlr : ∀ {ℓ} {a : S.Ord ℓ} {g : ℕ → Ordᶜ k} n → Mh₊ a (g n) → Mh₊ a (lim g)
    Mii : ∀ {ℓ j j′} {q : j B.< ℓ} {p′ : j′ <ᴵ k} {f : S.Ord< j q → S.Ord ℓ} {g : U j′ (<→◃ p′) → Ordᶜ k} →
          τ j ≅ᴵ j′ →
          (∀ (z′ : S.Ord j) (z : Ordᶜ j′) → M< j′ (<→◃ p′) (into (<→◃ p′) z) z′ →
             Mh₊ (f (S.coe₀ {p = q} z′)) (g (into (<→◃ p′) z))) →
          Mh₊ (limᵢ q f) (limᵢ p′ g)
    Mir : ∀ {ℓ j′} {a : S.Ord ℓ} {p′ : j′ <ᴵ k} {g : U j′ (<→◃ p′) → Ordᶜ k} →
          (∀ (z : Ordᶜ j′) → z ≅ Ω j′ → Mh₊ a (g (into (<→◃ p′) z))) → Mh₊ a (limᵢ p′ g)
    Mirω : ∀ {ℓ j′} {a : S.Ord ℓ} {p′ : j′ <ᴵ k} {g : U j′ (<→◃ p′) → Ordᶜ k} →
          (∀ (z : Ordᶜ j′) → z ≅ Ω j′ → NZ (g (into (<→◃ p′) z))) →
          (∀ (z : Ordᶜ j′) → (∀ m → M< j′ (<→◃ p′) (into (<→◃ p′) z) (natˢ m)) → Mh₊ a (g (into (<→◃ p′) z))) →
          Mh₊ a (limᵢ p′ g)
    Mur : ∀ {ℓ i} {a : S.Ord ℓ} {r : i ◃₁ k} {y : U i (◃₁→◃ r)} → M< i (◃₁→◃ r) y a → Mh₊ a (up r y)

M< : ∀ {k} (i : Ordᴵ) (r : i ◃ k) → U i r → ∀ {ℓ} → S.Ord ℓ → Set
M< i zero         y a = Mh₊ i M< a y
M< i (suc r)      y a = M< i r y a
M< _ (self {f} n) y a = Mh₊ (f n) M< a y
M< i (lim n r)    y a = M< i r y a

Mh : ∀ {ℓ k} → S.Ord ℓ → Ordᶜ k → Set
Mh {k = k} = Mh₊ k M<

M→Mh : ∀ {i k ℓ} (r : i ◃ k) {y : Ordᶜ i} {a : S.Ord ℓ} → M< i r (into r y) a → Mh a y
M→Mh zero      d = d
M→Mh (suc r)   d = M→Mh r d
M→Mh (self n)  d = d
M→Mh (lim n r) d = M→Mh r d

Mh→M : ∀ {i k ℓ} (r : i ◃ k) {y : Ordᶜ i} {a : S.Ord ℓ} → Mh a y → M< i r (into r y) a
Mh→M zero      d = d
Mh→M (suc r)   d = Mh→M r d
Mh→M (self n)  d = d
Mh→M (lim n r) d = Mh→M r d
```

## §3 关系对运算封闭

```agda
M-↑ : ∀ {k ℓ₁ ℓ₂} (r : ℓ₁ B.< ℓ₂) {x : S.Ord ℓ₁} {y : Ordᶜ k} → Mh x y → Mh (S.↑ r x) y
M-↑ r (Mz nz)   = Mz nz
M-↑ r (Ms d)    = Ms (M-↑ r d)
M-↑ r (Msr d)   = Msr (M-↑ r d)
M-↑ r (Mll h)   = Mll (λ n → M-↑ r (h n))
M-↑ r (Mlr n d) = Mlr n (M-↑ r d)
M-↑ r (Mii {q = q} {f = f} e h) = Mii e (λ z′ z w →
  subst (λ u → Mh (S.↑ r (f u)) _) (sym (coe-coe₀ (B.<-trans q r) q z′)) (M-↑ r (h z′ z w)))
M-↑ r (Mir H)      = Mir (λ z d → M-↑ r (H z d))
M-↑ r (Mirω nz H)  = Mirω nz (λ z b → M-↑ r (H z b))
M-↑ r (Mur {r = zero} d)   = Mur (M-↑ r d)
M-↑ r (Mur {r = self n} d) = Mur (M-↑ r d)

M-tr    : ∀ {a a′ ℓ} (e : a ≅ᴵ a′) {y : Ordᶜ a} {x : S.Ord ℓ} → Mh x y → Mh x (tr e y)
M-tr⁻   : ∀ {a a′ ℓ} (e : a ≅ᴵ a′) {y : Ordᶜ a′} {x : S.Ord ℓ} → Mh x y → Mh x (tr⁻ e y)
M-back  : ∀ {j a b ℓ} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} {x : S.Ord ℓ} → Mh x u → Mh x (back (res q e) u)
M-back⁻ : ∀ {j a b ℓ} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} {x : S.Ord ℓ} → Mh x u → Mh x (back (res⁻ q e) u)

M-tr e (Mz nz)   = Mz (NZ-tr e nz)
M-tr e (Ms d)    = Ms (M-tr e d)
M-tr e (Msr d)   = Msr (M-tr e d)
M-tr e (Mll h)   = Mll (λ n → M-tr e (h n))
M-tr e (Mlr n d) = Mlr n (M-tr e d)
M-tr e (Mii {p′ = q} {g = g} e₀ h) = Mii (≅ᴵ-trans e₀ (eq (res q e))) (λ z′ z w →
  subst (λ u → Mh _ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z))
        (M-tr e (h z′ (back (res q e) z) (Mh→M (<→◃ q) (M-back q e (M→Mh (<→◃ (lt (res q e))) w))))))
M-tr e (Mir {p′ = q} {g = g} H) = Mir (λ z d →
  subst (λ u → Mh _ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z))
        (M-tr e (H (back (res q e) z) (≅-trans (back-≅ q e d) (Ω-≅ (≅ᴵ-sym (eq (res q e))))))))
M-tr e (Mirω {p′ = q} {g = g} nz H) = Mirω
  (λ z d → subst (λ u → NZ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z))
                 (NZ-tr e (nz (back (res q e) z) (≅-trans (back-≅ q e d) (Ω-≅ (≅ᴵ-sym (eq (res q e))))))))
  (λ z b → subst (λ u → Mh _ (tr e (g (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z))
                 (M-tr e (H (back (res q e) z) (λ m → Mh→M (<→◃ q) (M-back q e (M→Mh (<→◃ (lt (res q e))) (b m)))))))
M-tr (s≅ e) (Mur {r = zero} d)   = Mur (M-tr e d)
M-tr (l≅ f) (Mur {r = self n} d) = Mur (M-tr (f n) d)

M-tr⁻ e (Mz nz)   = Mz (NZ-tr⁻ e nz)
M-tr⁻ e (Ms d)    = Ms (M-tr⁻ e d)
M-tr⁻ e (Msr d)   = Msr (M-tr⁻ e d)
M-tr⁻ e (Mll h)   = Mll (λ n → M-tr⁻ e (h n))
M-tr⁻ e (Mlr n d) = Mlr n (M-tr⁻ e d)
M-tr⁻ e (Mii {p′ = q} {g = g} e₀ h) = Mii (≅ᴵ-trans e₀ (eq (res⁻ q e))) (λ z′ z w →
  subst (λ u → Mh _ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
        (M-tr⁻ e (h z′ (back (res⁻ q e) z) (Mh→M (<→◃ q) (M-back⁻ q e (M→Mh (<→◃ (lt (res⁻ q e))) w))))))
M-tr⁻ e (Mir {p′ = q} {g = g} H) = Mir (λ z d →
  subst (λ u → Mh _ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
        (M-tr⁻ e (H (back (res⁻ q e) z) (≅-trans (back⁻-≅ q e d) (Ω-≅ (≅ᴵ-sym (eq (res⁻ q e))))))))
M-tr⁻ e (Mirω {p′ = q} {g = g} nz H) = Mirω
  (λ z d → subst (λ u → NZ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
                 (NZ-tr⁻ e (nz (back (res⁻ q e) z) (≅-trans (back⁻-≅ q e d) (Ω-≅ (≅ᴵ-sym (eq (res⁻ q e))))))))
  (λ z b → subst (λ u → Mh _ (tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
                 (M-tr⁻ e (H (back (res⁻ q e) z) (λ m → Mh→M (<→◃ q) (M-back⁻ q e (M→Mh (<→◃ (lt (res⁻ q e))) (b m)))))))
M-tr⁻ (s≅ e) (Mur {r = zero} d)   = Mur (M-tr⁻ e d)
M-tr⁻ (l≅ f) (Mur {r = self n} d) = Mur (M-tr⁻ (f n) d)

M-back zero      (s≅ e) d = M-tr⁻ e d
M-back (suc q)   (s≅ e) d = M-back q e d
M-back (lim n q) (l≅ f) d = M-back q (f n) d

M-back⁻ zero      (s≅ e) d = M-tr e d
M-back⁻ (suc q)   (s≅ e) d = M-back⁻ q e d
M-back⁻ (lim n q) (l≅ f) d = M-back⁻ q (f n) d
```

**加法.**

```agda
M-add-r : ∀ {k₁ k₂ ℓ} {a : S.Ord ℓ} {a′ : Ordᶜ k₂} {σ : Simᴵ k₁ k₂} (b : Ordᶜ k₁) → Mh a a′ → Mh a (add a′ σ b)
M-add-r zero       d = d
M-add-r (suc b)    d = Msr (M-add-r b d)
M-add-r (lim g)    d = Mlr 0 (M-add-r (g 0) d)
M-add-r {a = a} {a′ = a′} {σ = σ} (limᵢ q g) d = Mir (λ z _ →
  subst (λ u → Mh a (add a′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (M-add-r (g (into (<→◃ q) z)) d))
M-add-r {a = a} {a′ = a′} {σ = σ} (up zero x)     d = M-add-r {a = a} {a′ = a′} {σ = λ q → σ (suc q)} x d
M-add-r {a = a} {a′ = a′} {σ = σ} (up (self n) x) d = M-add-r {a = a} {a′ = a′} {σ = λ q → σ (lim n q)} x d

M-add : ∀ {k₁ k₂ ℓ} {a : S.Ord ℓ} {a′ : Ordᶜ k₂} {σ : Simᴵ k₁ k₂} {b : S.Ord ℓ} {b′ : Ordᶜ k₁} →
        Mh a a′ → Mh b b′ → Mh (a S.+ b) (add a′ σ b′)
M-add {b′ = b′} da (Mz nz) = M-add-r b′ da
M-add da (Ms d)    = Ms (M-add da d)
M-add da (Msr d)   = Msr (M-add da d)
M-add da (Mll h)   = Mll (λ n → M-add da (h n))
M-add da (Mlr n d) = Mlr n (M-add da d)
M-add {a = a} {a′ = a′} {σ = σ} da (Mii {q = q₁} {p′ = q} {f = f} {g = g} e h) = Mii e (λ z′ z w →
  subst (λ u → Mh (a S.+ f (S.coe₀ {p = q₁} z′)) (add a′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z))
        (M-add da (h z′ z (Mh→M (<→◃ q) (M→Mh (<→◃ (σ q)) w)))))
M-add {a = a} {a′ = a′} {σ = σ} {b = b} da (Mir {p′ = q} {g = g} H) = Mir (λ z d →
  subst (λ u → Mh (a S.+ b) (add a′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (M-add da (H z d)))
M-add {a = a} {a′ = a′} {σ = σ} {b = b} da (Mirω {p′ = q} {g = g} nz H) = Mirω
  (λ z d → subst (λ u → NZ (add a′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (NZ-add-r (nz z d)))
  (λ z c → subst (λ u → Mh (a S.+ b) (add a′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z))
                 (M-add da (H z (λ m → Mh→M (<→◃ q) (M→Mh (<→◃ (σ q)) (c m))))))
M-add {a = a} {a′ = a′} {σ = σ} {b = b} da (Mur {r = zero} {y = y} d)   = M-add {σ = λ q → σ (suc q)} {b′ = y} da d
M-add {a = a} {a′ = a′} {σ = σ} {b = b} da (Mur {r = self n} {y = y} d) = M-add {σ = λ q → σ (lim n q)} {b′ = y} da d

iter-Mh : ∀ {k ℓ} {A : S.Ord ℓ} {B′ : Ordᶜ k} → Mh A B′ → NZ B′ → ∀ n → Mh (iter (A S.+_) zero n) (iter (B′ +_) zero (suc n))
iter-Mh d nz zero    = Mz nz
iter-Mh d nz (suc n) = M-add d (iter-Mh d nz n)
```

**有限数.** 非零的 $B$ 的倍数 $B\cdot(n+1)$ 过得了 $n$. 这里左边必须有限: `L` 对无穷的 $x$ 是假的 ($B=1$, $R=\omega$, $1+\omega\not\ge\omega+1$).

```agda
data FinL : ∀ {ℓ} → S.Ord ℓ → Set where
  fz : ∀ {ℓ} → FinL {ℓ} zero
  fs : ∀ {ℓ} {a : S.Ord ℓ} → FinL a → FinL (suc a)

finˢ : ∀ n → FinL (natˢ n)
finˢ zero    = fz
finˢ (suc n) = fs (finˢ n)

L₀ : ∀ {k₁ k₂ ℓ} {B′ : Ordᶜ k₂} {σ : Simᴵ k₁ k₂} {R : Ordᶜ k₁} → NZ B′ → NZ R → Mh {ℓ} (suc zero) (add B′ σ R)
L₀ nb (nzs {b = R₀}) = Ms (Mz (NZ-add-l nb R₀))
L₀ nb (nzl n d)      = Mlr n (L₀ nb d)
L₀ {B′ = B′} {σ = σ} nb (nzi {q = q} {g = g} prem) = Mir (λ z d →
  subst (λ u → Mh (suc zero) (add B′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (L₀ nb (prem z d)))
L₀ {B′ = B′} {σ = σ} nb (nzu {r = zero} {x = y} d)   = L₀ {σ = λ q → σ (suc q)} {R = y} nb d
L₀ {B′ = B′} {σ = σ} nb (nzu {r = self n} {x = y} d) = L₀ {σ = λ q → σ (lim n q)} {R = y} nb d

L : ∀ {k₁ k₂ ℓ} {B′ : Ordᶜ k₂} {σ : Simᴵ k₁ k₂} {x : S.Ord ℓ} {R : Ordᶜ k₁} → NZ B′ → FinL x → Mh x R → Mh (suc x) (add B′ σ R)
L nb fz     (Mz nz)   = L₀ nb nz
L nb (fs f) (Ms d)    = Ms (L nb f d)
L nb f      (Msr d)   = Msr (L nb f d)
L nb f      (Mlr n d) = Mlr n (L nb f d)
L {B′ = B′} {σ = σ} {x = x} nb f (Mir {p′ = q} {g = g} H) = Mir (λ z d →
  subst (λ u → Mh (suc x) (add B′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (L nb f (H z d)))
L {B′ = B′} {σ = σ} {x = x} nb f (Mirω {p′ = q} {g = g} nz H) = Mirω
  (λ z d → subst (λ u → NZ (add B′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z)) (NZ-add-r (nz z d)))
  (λ z c → subst (λ u → Mh (suc x) (add B′ σ (g (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z))
                 (L nb f (H z (λ m → Mh→M (<→◃ q) (M→Mh (<→◃ (σ q)) (c m))))))
L {B′ = B′} {σ = σ} nb f (Mur {r = zero} {y = y} d)   = L {σ = λ q → σ (suc q)} {R = y} nb f d
L {B′ = B′} {σ = σ} nb f (Mur {r = self n} {y = y} d) = L {σ = λ q → σ (lim n q)} {R = y} nb f d

M-nat-iter : ∀ {k} {B′ : Ordᶜ k} → NZ B′ → ∀ n → Mh (natˢ n) (iter (B′ +_) zero (suc n))
M-nat-iter nb zero    = Mz nb
M-nat-iter nb (suc n) = L nb (finˢ n) (M-nat-iter nb n)

big-ψ : ∀ {i k ℓ} {w : Ordᶜ k} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) → NZ w → ∀ n → Mh (natˢ n) (ψ p σ w)
big-ψ p σ (nzs {b = b}) n = Mlr (suc n) (M-nat-iter (NZ-ψ p σ b) n)
big-ψ p σ (nzl m d)     n = Mlr m (big-ψ p σ d n)
big-ψ p σ (nzi {j = j} {q = q} {g = g} prem) n with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = Mir (λ z d →
        subst (λ u → Mh (natˢ n) (ψ p σ (g (into (<→◃ q) (tr⁻ e u))))) (sym (out-into (<→◃ r) z))
              (big-ψ p σ (prem (tr⁻ e z) (tr⁻-≅ e (≅-trans d (Ω-≅ (≅ᴵ-sym e))))) n))
... | injᵇ _ = Mlr 0 (big-ψ p σ (prem (Ω j) (Ω-refl j)) n)
... | injᶜ _ = Mlr 0 (big-ψ p σ (prem (Ω j) (Ω-refl j)) n)
big-ψ p σ (nzu {r = zero} d)   n = big-ψ p (λ q → σ (suc q)) d n
big-ψ p σ (nzu {r = self m} d) n = big-ψ p (λ q → σ (lim m q)) d n
```

## §4 $\Omega$

```agda
M-ω : ∀ {k} {Y : Ordᶜ k} → (∀ n → Mh (natˢ n) Y) → Mh S.ω Y
M-ω {Y = Y} big = go _ refl (λ _ → refl) where
  go : (g : ℕ → S.Ord₀) → g 0 ≡ zero → (∀ n → g (suc n) ≡ suc (g n)) → Mh (lim g) Y
  go g g0 gs = Mll (λ n → subst (λ x → Mh x Y) (sym (e n)) (big n)) where
    e : ∀ n → g n ≡ natˢ n
    e zero    = g0
    e (suc n) = Eq.trans (gs n) (cong suc (e n))
      where import Relation.Binary.PropositionalEquality as Eq

M-big-Ω : ∀ {a a′} → NonZero a → τ a ≅ᴵ a′ → ∀ n → Mh (natˢ n) (Ω a′)
M-big-Ω {a = B.suc c} {a′ = suc c′} _ (s≅ e) n = Mirω (λ z d → nzu (NZ-≅ d (NZ-Ω c′))) (λ z b → Mur (b n))
M-big-Ω {a = B.lim f m} _ (l≅ h) n = Mlr 1 (Mur (M-big-Ω (B.sth<nz (m Trich.zero)) (h 1) n))

M-step : ∀ {k L c} (r : c B.< L) {Y : Ordᶜ k} → (∀ n → Mh (natˢ n) Y) → (NonZero c → Mh (S.Ω c) Y) → Mh (S.↑ r (S.Ω c)) Y
M-step {c = B.zero}    r big ih = M-↑ r (M-ω big)
M-step {c = B.suc c}   r big ih = M-↑ r (ih tt)
M-step {c = B.lim f m} r big ih = M-↑ r (ih tt)

M-Ω : ∀ {a a′} → NonZero a → τ a ≅ᴵ a′ → Mh (S.Ω a) (Ω a′)
M-Ω {a = B.suc c}   _ (s≅ e) = Mii e (λ z′ z w → Mur (M-↑ B.zero w))
M-Ω {a = B.lim f m} _ (l≅ h) = Mll (λ n → M-step (B.f<l n)
  (λ n₀ → Mlr 1 (Mur (M-big-Ω (B.sth<nz (m Trich.zero)) (h 1) n₀)))
  (λ nz → Mlr n (Mur (M-Ω nz (h n)))))

M-B1′ : ∀ {i i′ k ℓ′} → NonZero i → τ i ≅ᴵ i′ → (p′ : i′ <ᴵ ℓ′) (σ : Simᴵ k ℓ′) (y : Ordᶜ k) → Mh (S.Ω i) (ψ p′ σ y)
M-B1′ nz e p′ σ zero    = M-Ω nz e
M-B1′ nz e p′ σ (suc a) = Mlr 1 (M-B1′ nz e p′ σ a)
M-B1′ nz e p′ σ (lim g) = Mlr 0 (M-B1′ nz e p′ σ (g 0))
M-B1′ nz e p′ σ (limᵢ {i = j} q g) with <ᴵ-dec (σ q) p′
... | injᵃ (via e₁ r) = Mir (λ z d →
        subst (λ u → Mh _ (ψ p′ σ (g (into (<→◃ q) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
              (M-B1′ nz e p′ σ (g (into (<→◃ q) (tr⁻ e₁ z)))))
... | injᵇ _ = Mlr 0 (M-B1′ nz e p′ σ (g (into (<→◃ q) (Ω j))))
... | injᶜ _ = Mlr 0 (M-B1′ nz e p′ σ (g (into (<→◃ q) (Ω j))))
M-B1′ nz e p′ σ (up zero x)     = M-B1′ nz e p′ (λ q → σ (suc q)) x
M-B1′ nz e p′ σ (up (self n) x) = M-B1′ nz e p′ (λ q → σ (lim n q)) x

M-B1 : ∀ {i i′ k ℓ′} {y : Ordᶜ k} → τ i ≅ᴵ i′ → (p′ : i′ <ᴵ ℓ′) (σ : Simᴵ k ℓ′) → NZ y → Mh (S.Ω i) (ψ p′ σ y)
M-B1 {i = B.zero}    z≅ p′ σ nz = M-ω (big-ψ p′ σ nz)
M-B1 {i = B.suc i}   e p′ σ {- y -} nz = M-B1′ tt e p′ σ _
M-B1 {i = B.lim f m} e p′ σ nz = M-B1′ tt e p′ σ _
```

## §5 折叠

这里两条链逐项相关: src 的 $0$ 与 Level 的 $\Omega_j$ (`Mz`), 然后归纳. 不错开. 只有 $i=j$ 时 src 的 `lfp` 多一个第 0 项 $0$.

```agda
M-ψ : ∀ {i i′ k ℓ′ ℓ} {x : S.Ord ℓ} {y : Ordᶜ k} (e : τ i ≅ᴵ i′) (p′ : i′ <ᴵ ℓ′) (σ : Simᴵ k ℓ′) (p : i B.< ℓ) →
      Mh x y → Mh (S.ψ< p x) (ψ p′ σ y)

chain-m : ∀ {j j′ k ℓ} {q : j B.< ℓ} (p : j B.< ℓ) (q′ : j′ <ᴵ k) {f : S.Ord< j q → S.Ord ℓ} {g : U j′ (<→◃ q′) → Ordᶜ k} →
          τ j ≅ᴵ j′ →
          (∀ (z′ : S.Ord j) (z : Ordᶜ j′) → M< j′ (<→◃ q′) (into (<→◃ q′) z) z′ → Mh (f (S.coe₀ {p = q} z′)) (g (into (<→◃ q′) z))) →
          ∀ n → Mh (iter (λ x → S.ψ< p (f (S.coe₀ {p = q} x))) zero n)
                   (iter (λ x → ψ q′ (λ r → r) (g (into (<→◃ q′) x))) (Ω j′) n)
chain-m {j′ = j′} p q′ ej h zero = Mz (NZ-Ω j′)
chain-m {q = q} p q′ {f = f} {g = g} ej h (suc n) =
  M-ψ ej q′ (λ r → r) p (h _ _ (Mh→M (<→◃ q′) (chain-m {q = q} p q′ {f = f} {g = g} ej h n)))

M-ψ e p′ σ p (Mz {b = y} nz) = M-B1 e p′ σ nz
M-ψ e p′ σ p (Ms {b = b} d)  = Mll (λ n → Mlr (suc n) (iter-Mh (M-ψ e p′ σ p d) (NZ-ψ p′ σ b) n))
M-ψ e p′ σ p (Msr d)   = Mlr 1 (M-ψ e p′ σ p d)
M-ψ e p′ σ p (Mll h)   = Mll (λ n → M-ψ e p′ σ p (h n))
M-ψ e p′ σ p (Mlr n d) = Mlr n (M-ψ e p′ σ p d)
M-ψ e p′ σ p (Mur {r = zero} d)   = M-ψ e p′ (λ q → σ (suc q)) p d
M-ψ e p′ σ p (Mur {r = self n} d) = M-ψ e p′ (λ q → σ (lim n q)) p d
M-ψ e p′ σ p (Mir {j′ = j′} {p′ = q′} {g = g} H) with <ᴵ-dec (σ q′) p′
... | injᵃ (via e₁ r) = Mir (λ z d →
        subst (λ u → Mh _ (ψ p′ σ (g (into (<→◃ q′) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
              (M-ψ e p′ σ p (H (tr⁻ e₁ z) (tr⁻-≅ e₁ (≅-trans d (Ω-≅ (≅ᴵ-sym e₁)))))))
... | injᵇ _ = Mlr 0 (M-ψ e p′ σ p (H (Ω j′) (Ω-refl j′)))
... | injᶜ _ = Mlr 0 (M-ψ e p′ σ p (H (Ω j′) (Ω-refl j′)))
M-ψ e p′ σ p (Mirω {j′ = j′} {p′ = q′} {g = g} nz H) with <ᴵ-dec (σ q′) p′
... | injᵃ (via e₁ r) = Mirω
        (λ z d → subst (λ u → NZ (ψ p′ σ (g (into (<→◃ q′) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z)) (NZ-ψ p′ σ _))
        (λ z b → subst (λ u → Mh _ (ψ p′ σ (g (into (<→◃ q′) (tr⁻ e₁ u))))) (sym (out-into (<→◃ r) z))
              (M-ψ e p′ σ p (H (tr⁻ e₁ z) (λ m → Mh→M (<→◃ q′) (M-tr⁻ e₁ (M→Mh (<→◃ r) (b m)))))))
... | injᵇ _ = Mlr 1 (M-ψ e p′ σ p (H _ (λ m → Mh→M (<→◃ q′) (big-ψ q′ (λ r → r) (nz (Ω j′) (Ω-refl j′)) m))))
... | injᶜ _ = Mlr 1 (M-ψ e p′ σ p (H _ (λ m → Mh→M (<→◃ q′) (big-ψ q′ (λ r → r) (nz (Ω j′) (Ω-refl j′)) m))))
M-ψ e p′ σ p (Mii {q = q} {p′ = q′} {f = f} {g = g} ej h) with <ᴵ-dec (σ q′) p′ | B.<-dec q p
... | injᵃ (via e₁ r) | injᵃ j<i = Mii (≅ᴵ-trans ej e₁) (λ z′ z w →
        subst₂ (λ v u → Mh (S.ψ< p (f v)) (ψ p′ σ (g (into (<→◃ q′) (tr⁻ e₁ u)))))
               (sym (coe-coe₀ j<i q z′)) (sym (out-into (<→◃ r) z))
               (M-ψ e p′ σ p (h z′ (tr⁻ e₁ z) (Mh→M (<→◃ q′) (M-tr⁻ e₁ (M→Mh (<→◃ r) w))))))
... | injᵃ (via e₁ r) | injᵇ i<j  = ⊥-elim (clash-lt-lt ej e (via e₁ r) i<j)
... | injᵃ (via e₁ r) | injᶜ refl = ⊥-elim (clash-lt-eq ej e (via e₁ r) refl)
... | injᵇ r          | injᵃ j<i  = ⊥-elim (clash-gt-lt ej e r j<i)
... | injᶜ r          | injᵃ j<i  = ⊥-elim (clash-eq-lt ej e r j<i)
... | injᵇ _          | injᵇ _    = Mll (λ n → Mlr n (M-ψ e p′ σ p (h _ _ (Mh→M (<→◃ q′) (chain-m {q = q} q q′ {f = f} {g = g} ej h n)))))
... | injᶜ _          | injᵇ _    = Mll (λ n → Mlr n (M-ψ e p′ σ p (h _ _ (Mh→M (<→◃ q′) (chain-m {q = q} q q′ {f = f} {g = g} ej h n)))))
... | injᵇ _          | injᶜ refl = Mll (λ where
        zero    → Mlr 0 (Mz (NZ-ψ p′ σ _))
        (suc n) → Mlr n (M-ψ e p′ σ p (h _ _ (Mh→M (<→◃ q′) (chain-m {q = q} p q′ {f = f} {g = g} ej h n)))))
... | injᶜ _          | injᶜ refl = Mll (λ where
        zero    → Mlr 0 (Mz (NZ-ψ p′ σ _))
        (suc n) → Mlr n (M-ψ e p′ σ p (h _ _ (Mh→M (<→◃ q′) (chain-m {q = q} p q′ {f = f} {g = g} ej h n)))))
```

## §6 结论

```agda
Mh→≼ : ∀ {x : S.Ord₀} {y : Ordᶜ zero} → Mh x y → tr₀ x ≼ y
Mh→≼ (Mz nz)   = z≼
Mh→≼ (Ms d)    = s≼s (Mh→≼ d)
Mh→≼ (Msr d)   = ≼-suc (Mh→≼ d)
Mh→≼ (Mll h)   = l≼ (λ n → Mh→≼ (h n))
Mh→≼ (Mlr n d) = ≼l n (Mh→≼ d)
Mh→≼ (Mii {q = ()} e h)
Mh→≼ (Mir {p′ = ()} H)
Mh→≼ (Mirω {p′ = ()} nz H)
Mh→≼ (Mur {r = ()} d)

Ψ⁰≽< : ∀ {a} (p : B.zero B.< a) → tr₀ (S.ψ< p (S.Ω a)) ≼ ψ⁰ (Ω (τ a))
Ψ⁰≽< {a} p = ≼-trans (Mh→≼ (M-ψ z≅ (τ-< p) (λ q → q) p (M-Ω (B.sth<nz p) (≅ᴵ-refl (τ a)))))
                     (≅→≼ (≅-sym (ψ⁰≅ψ {p = τ-< p} {σ = λ q → q} (Ω-refl (τ a)))))
```
