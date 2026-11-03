# 折叠的外部规格: 目标 1, 穿透与 `rise` (底座)

> 底座, 不含记号. 结论写在 [OCFSpec](OCFSpec.lagda.md). 目标 $v=1$: `ΩO-1`, 可数输入的折叠 (`correct₁`), 穿透行 `pen-right : IsPsi 1 Ω (ψ₁ Ω)` 与它的反面 `rise-rejected`: 派发答 `rise` 时 $\psi_1(\Omega)$ 变成 $\omega$-共尾的 $\sup\psi_1(\delta_n)$, 规格拒绝. 这是 `S = rise` (InaccFloor 的 `Zero.dev`) 的最小实例. `Zero.dev` 本身在 $\psi_0(\Omega_\Omega\cdots)$ 之上, 规格现在够不到, 见 [OCFSpec](OCFSpec.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OCFSpecOne where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.OCFSpecBase
open import OCF.Align.OCFSpecRule
open import OCF.Align.OCFSpecAnchor
```

## §1 `ΩO 1`

如果第 $w$ 层有 `limᵢ` (有字面的 $j<w$), 第 1 层的树就能搬进第 $w$ 层: `E₁`. 分支 $g$ 吃第 0 层的树, 新分支吃第 $j$ 层的树 $y$, 经 `ret` 读回第 0 层; `ret` 把 `limᵢ` 压成 0. 于是 $\Omega_{w+1}\preccurlyeq z$ ($z$ 在第 1 层) 时第 $w$ 层的树都不含 `limᵢ` (`no-high`), 也就都 $<\Omega_1$.

```agda
ret : ∀ {w} → Ordᶜ w → Ordᶜ zero
ret zero            = zero
ret (suc x)         = suc (ret x)
ret (lim f)         = lim (ret ∘ f)
ret (limᵢ p f)      = zero
ret (up zero y)     = ret y
ret (up (self n) y) = ret y

ret-emb : ∀ {j} (x : Ordᶜ zero) → x ≅ ret (emb {j} x)
ret-emb zero        = z≅
ret-emb (suc x)     = s≅ (ret-emb x)
ret-emb (lim f)     = l≅ (λ n → ret-emb (f n))
ret-emb (limᵢ () f)
ret-emb (up () x)

ret-≅ : ∀ {w w′} {x : Ordᶜ w} {y : Ordᶜ w′} → x ≅ y → ret x ≅ ret y
ret-≅ z≅ = z≅
ret-≅ (s≅ e) = s≅ (ret-≅ e)
ret-≅ (l≅ h) = l≅ (λ n → ret-≅ (h n))
ret-≅ (lᵢ≅ e h) = z≅
ret-≅ (upˡ {r = zero} e) = ret-≅ e
ret-≅ (upˡ {r = self n} e) = ret-≅ e
ret-≅ (upʳ {r = zero} e) = ret-≅ e
ret-≅ (upʳ {r = self n} e) = ret-≅ e

emb-cong : ∀ {w} {x y : Ordᶜ zero} → x ≅ y → emb {w} x ≅ emb {w} y
emb-cong z≅ = z≅
emb-cong (s≅ e) = s≅ (emb-cong e)
emb-cong (l≅ h) = l≅ (λ n → emb-cong (h n))
emb-cong (lᵢ≅ {p = ()} e h)
emb-cong (upˡ {r = ()} e)
emb-cong (upʳ {r = ()} e)

module E {j w} (q : j <ᴵ w) where
  E₁ : Ordᶜ (suc zero) → Ordᶜ w
  E₁ zero = zero
  E₁ (suc x) = suc (E₁ x)
  E₁ (lim f) = lim (E₁ ∘ f)
  E₁ (limᵢ zero g) = limᵢ q (λ y → E₁ (g (ret (out (<→◃ q) y))))
  E₁ (limᵢ (suc ()) g)
  E₁ (up zero x) = emb x

  cross : ∀ {x : Ordᶜ zero} {b : Ordᶜ (suc zero)} → x ≅ b → emb {w} x ≅ E₁ b
  cross z≅ = z≅
  cross (s≅ e) = s≅ (cross e)
  cross (l≅ h) = l≅ (λ n → cross (h n))
  cross (lᵢ≅ {p = ()} e h)
  cross (upˡ {r = ()} e)
  cross (upʳ {r = zero} e) = emb-cong e

  E-≅ : ∀ {x y : Ordᶜ (suc zero)} → x ≅ y → E₁ x ≅ E₁ y
  E-≅ z≅ = z≅
  E-≅ (s≅ e) = s≅ (E-≅ e)
  E-≅ (l≅ h) = l≅ (λ n → E-≅ (h n))
  E-≅ (lᵢ≅ {p = zero} {q = zero} {f = f} {g = g} e h) = lᵢ≅ (≅ᴵ-refl j) λ y y′ d →
    subst₂ (λ u v → E₁ (f (ret u)) ≅ E₁ (g (ret v))) (sym (out-into (<→◃ q) y)) (sym (out-into (<→◃ q) y′))
      (E-≅ (h (ret y) (ret y′) (ret-≅ (R→≅ (<→◃ q) d))))
  E-≅ (lᵢ≅ {p = suc ()} e h)
  E-≅ (lᵢ≅ {q = suc ()} e h)
  E-≅ (upˡ {r = zero} e) = cross e
  E-≅ (upʳ {r = zero} e) = ≅-sym (cross (≅-sym e))

  ≼E : ∀ (z : Ordᶜ (suc zero)) → z ≅ z → z ≼ E₁ z
  ≼E zero e = z≼
  ≼E (suc x) (s≅ e) = s≼s (≼E x e)
  ≼E (lim f) (l≅ h) = l≼ (λ n → ≼l n (≼E (f n) (h n)))
  ≼E (limᵢ zero g) (lᵢ≅ e h) = i≼ λ x ex →
    ≼i (emb x) (emb-≅ x)
       (subst (λ u → g x ≼ E₁ (g (ret u))) (sym (out-into (<→◃ q) (emb x)))
          (≼-trans (≅→≼ (h x (ret (emb x)) (ret-emb x)))
                   (≼E (g (ret (emb x))) (h (ret (emb x)) (ret (emb x)) (≅-refl⁰ _)))))
  ≼E (limᵢ (suc ()) g) e
  ≼E (up zero x) e = u≼ (≼emb x)

up-self : ∀ {k w} (r : k ◃₁ w) {y : U k (◃₁→◃ r)} → up r y ≅ up r y → out (◃₁→◃ r) y ≅ out (◃₁→◃ r) y
up-self zero (upˡ e) = ≅-trans e (≅-sym e)
up-self zero (upʳ e) = ≅-trans (≅-sym e) e
up-self (self n) (upˡ e) = ≅-trans e (≅-sym e)
up-self (self n) (upʳ e) = ≅-trans (≅-sym e) e

no-high : ∀ {w} (z : Ordᶜ (suc zero)) → z ≅ z → (∀ (x : Ordᶜ w) → x ≅ x → x ≼ z) → ∀ (x : Ordᶜ w) → x ≅ x → x ≼ ret x
no-high z ez p zero e = z≼
no-high z ez p (suc x) (s≅ e) = s≼s (no-high z ez (λ x′ ex′ → ≼-trans (≼-self-suc x′) (≼-trans (s≼s (≼-refl x′)) (p (suc x′) (s≅ ex′)))) x e)
no-high z ez p (lim f) (l≅ h) = l≼ (λ n → ≼l n (no-high z ez p (f n) (h n)))
no-high z ez p (limᵢ q f) e =
  ⊥-elim (≺ᵛ-irrefl z (≼-trans (s≼s (E.≼E q z ez)) (p (suc (E.E₁ q z)) (s≅ (E.E-≅ q ez)))))
no-high z ez p (up zero y) e =
  u≼ (no-high z ez (λ x ex → ≼-trans (≼u (≼-refl x)) (p (up zero x) (upˡ (upʳ ex)))) y (up-self zero e))
no-high z ez p (up (self n) y) e =
  u≼ (no-high z ez (λ x ex → ≼-trans (≼u (≼-refl x)) (p (up (self n) x) (upˡ (upʳ ex)))) y (up-self (self n) e))

ΩO-1 : ΩO (suc zero)
ΩO-1 zero z ez p = 1≼Ω (suc zero)
ΩO-1 (suc w) z ez p = i≼ (λ x ex → u≼
  (≼-trans (no-high z ez (λ x′ ex′ → ≼-trans (≼i x′ ex′ (≼u (≼-refl x′))) p) x ex) (≺→≼ (bnd⁰ (ret x)))))
ΩO-1 (lim f s) z ez p = l≼ (λ n → u≼ (ΩO-1 (f n) z ez (≼-trans (≼l n (≼u (≼-refl (Ω (f n))))) p)))
```

## §2 可数输入上的 $\psi_1$

$v=1$ 时一切可数树都在基底里, 所以标准形条件自动成立, 只要基本列严格增 (`Str`).

```agda
L₁ : Ordᴵ
L₁ = suc zero

L₂ : Ordᴵ
L₂ = suc (suc zero)

ψ₁ : Ordᶜ zero → Ordᶜ L₁
ψ₁ = ψ {i = L₁} {k = zero} {ℓ = L₂} zero (λ ())

data Str : Ordᶜ zero → Set where
  sz : Str zero
  ss : ∀ {b} → Str b → Str (suc b)
  sl : ∀ {f : ℕ → Ordᶜ zero} → (∀ n → Str (f n)) → (∀ n → f n ≺ᵛ f (suc n)) → Str (lim f)

b∈ : ∀ {k} {a : Ordᶜ k} (x : Ordᶜ zero) → C L₁ a x
b∈ x = base (bnd⁰ x)

correct₁ : ∀ {x} → Str x → IsPsi L₁ x (ψ₁ x)
correct₁ sz = T0 L₁
correct₁ {x = suc b} (ss r) = Tsuc ΩO-1 (correct₁ r) (b∈ b) (b∈ (forget L₁))
correct₁ {x = lim f} (sl r st) = Tlim ΩO-1 (λ n → correct₁ (r n)) st (λ n → b∈ (f n)) (λ n → b∈ (forget L₁))

ψ₁1 : IsPsi L₁ (𝟏 {zero}) (ψ₁ 𝟏)
ψ₁1 = correct₁ (ss sz)

Str-+ : ∀ {x y} → Str x → Str y → Str (x + y)
Str-+ sx sz = sx
Str-+ sx (ss sy) = ss (Str-+ sx sy)
Str-+ {x = x} sx (sl sf st) = sl (λ n → Str-+ sx (sf n)) (λ n → +-mono (≼-refl x) (st n))

reg→Str : ∀ {x : Ordᶜ zero} → Reg₀ x → Str x
reg→Str (rσ ())
reg→Str rz = sz
reg→Str (rs r c) = ss (reg→Str r)
reg→Str (rl r c st) = sl (λ n → reg→Str (r n)) st
```

**任何可数树都被严格增的树控制.** `⁺` 把 $\lim f$ 换成部分和.

```agda
_⁺ : Ordᶜ zero → Ordᶜ zero
pf : (ℕ → Ordᶜ zero) → ℕ → Ordᶜ zero
zero ⁺ = zero
(suc x) ⁺ = suc (x ⁺)
(lim f) ⁺ = lim (pf f)
(limᵢ () f) ⁺
(up () x) ⁺
pf f zero    = (f zero) ⁺
pf f (suc n) = suc (pf f n) + ((f (suc n)) ⁺)

⁺-≽ : ∀ x → x ≼ (x ⁺)
pf-≽ : ∀ f n → f n ≼ pf f n
⁺-≽ zero = z≼
⁺-≽ (suc x) = s≼s (⁺-≽ x)
⁺-≽ (lim f) = l≼ (λ n → ≼l n (pf-≽ f n))
⁺-≽ (limᵢ () f)
⁺-≽ (up () x)
pf-≽ f zero    = ⁺-≽ (f zero)
pf-≽ f (suc n) = ≼-trans (⁺-≽ (f (suc n))) (+-≽ʳ (suc (pf f n)) ((f (suc n)) ⁺))

str⁺ : ∀ x → Str (x ⁺)
str-pf : ∀ f n → Str (pf f n)
str⁺ zero = sz
str⁺ (suc x) = ss (str⁺ x)
str⁺ (lim f) = sl (str-pf f) (λ n → +-≽ˡ (suc (pf f n)) ((f (suc n)) ⁺))
str⁺ (limᵢ () f)
str⁺ (up () x)
str-pf f zero    = str⁺ (f zero)
str-pf f (suc n) = Str-+ (ss (str-pf f n)) (str⁺ (f (suc n)))
```

**折叠在第 0 层单调** (`ψ⁰-mono⁰` 的 $\psi_1$ 版本).

```agda
Ω≼ψ₁ : ∀ y → Ω L₁ ≼ ψ₁ y
Ω≼ψ₁ zero = ≼-refl (Ω L₁)
Ω≼ψ₁ (suc y) = ≼l 1 (Ω≼ψ₁ y)
Ω≼ψ₁ (lim f) = ≼l 0 (Ω≼ψ₁ (f 0))
Ω≼ψ₁ (limᵢ () f)
Ω≼ψ₁ (up () x)

ψ₁-mono : ∀ {x y} → x ≼ y → ψ₁ x ≼ ψ₁ y
ψ₁-mono {y = y} z≼ = Ω≼ψ₁ y
ψ₁-mono (s≼s e) = l≼ (λ n → ≼l n (·-≼ (ψ₁-mono e) n))
ψ₁-mono (≼l n e) = ≼l n (ψ₁-mono e)
ψ₁-mono (l≼ h) = l≼ (λ n → ψ₁-mono (h n))
ψ₁-mono (≼i {p = ()} x ex e)
ψ₁-mono (i≼ {p = ()} h)
ψ₁-mono (≼u {r = ()} e)
ψ₁-mono (u≼ {r = ()} e)
```

## §3 穿透是对的

`tp` 是折叠 $\psi_1(\Omega)$ 的字面输出, 因为 `<ᴵ-dec` 在 $(0,1)$ 上计算出穿透. `tp-eq` 是 `refl`, 证明这一点.

```agda
σ₁ : Simᴵ L₁ L₂
σ₁ q = suc q

tp : Ordᶜ L₁
tp = ψ {i = L₁} {k = L₁} {ℓ = L₂} zero σ₁ Ω₁

br : Ordᶜ zero → Ordᶜ L₁
br y = ψ {i = L₁} {k = L₁} {ℓ = L₂} zero σ₁ (up zero (tr⁻ z≅ y))

tp-eq : tp ≡ limᵢ zero br
tp-eq = refl

br≈ψ₁ : ∀ y → br y ≈ᵛ ψ₁ y
br≈ψ₁ y = ≅→≈ᵛ (ψ-≅ {k₁ = zero} {ℓ₁ = L₂} {k₂ = zero} {ℓ₂ = L₂} {p = zero} {σ = λ q → σ₁ (suc q)} {p′ = zero} {σ′ = λ ()}
                     {a = tr⁻ z≅ y} {b = y} (≅ᴵ-refl L₁) (tr⁻-≅ z≅ (≅-refl⁰ y)))

≼tp : ∀ y → ψ₁ y ≼ tp
≼tp y = ≼i y (≅-refl⁰ y) (proj₂ (br≈ψ₁ y))

ψ₁⁺ : Ordᶜ zero → Ordᶜ L₁
ψ₁⁺ x = ψ₁ (x ⁺)

s⁺ : ∀ x → IsPsi L₁ (x ⁺) (ψ₁⁺ x)
s⁺ x = correct₁ (str⁺ x)

tp-prin : Prin tp
tp-prin σ (≼i x₁ e₁ q₁) (≼i x₂ e₂ q₂) =
  let s = x₁ + x₂
      p₁ = ≼-trans q₁ (≼-trans (proj₁ (br≈ψ₁ x₁)) (ψ₁-mono (≼-trans (+-≽ˡ x₁ x₂) (⁺-≽ s))))
      p₂ = ≼-trans q₂ (≼-trans (proj₁ (br≈ψ₁ x₂)) (ψ₁-mono (≼-trans (+-≽ʳ x₁ x₂) (⁺-≽ s))))
  in ≼-trans (ψ̂-prin (s⁺ s) σ p₁ p₂) (≼tp (s ⁺))

pen-right : IsPsi L₁ Ω₁ tp
pen-right = sup
  (⇒bd tp (ψ-≅ {p = zero} {σ = σ₁} {p′ = zero} {σ′ = σ₁} (≅ᴵ-refl L₁) (Ω-refl L₁)) (≼-refl tp))
  (Ind.go (BndI L₁ tp)
     (λ q _ → ≼-trans q (≼i zero z≅ (≼-refl (Ω L₁))))
     (Bnd-plus tp-prin)
     (λ {u} {m} {n} {ξ} {w} q r _ _ bw → case q r bw)
     Bnd-cg)
  (λ { (≼i x e q) →
       let p = ≼-trans q (≼-trans (proj₁ (br≈ψ₁ x)) (ψ₁-mono (⁺-≽ x))) in
       wit (col (b∈ (forget L₁)) (b∈ (x ⁺)) (bnd⁰ (x ⁺)) (irr≡ (wf (x ⁺)) _ (s⁺ x))) (lt (s⁺ x)) (≺→≼ p) })
  where
  case : ∀ {u m n} {ξ : Ordᶜ m} {w : Ordᶜ n} (q : ξ ≺ᵛ Ω₁) → Recₐ Ω₁ (wf Ω₁) u ξ q w → w ≺ᵛ Ω (suc L₁) → w ≺ᵛ tp
  case {ξ = ξ} q r bw with bd⇒ q
  ... | z , ez , d =
    let e = col-bound (belowᵛ Ω₁ ξ q) ΩO-1 (≼-trans (≺→≼ d) (⁺-≽ z)) r (s⁺ z) bw in
    ≼-trans (suc≼M (1≼ψ̂ (wf (z ⁺)) (s⁺ z)) _ e) (≼tp (suc (z ⁺)))
```

## §4 `rise` 是错的

判决答 `rise` 时, 节点 $\Omega$ 上走链: `tr` 是 $\sup_n\psi_1(\delta_n)$, $\delta$ 是 $\psi_0$ 的链. 它是规格下的 $\psi_1(\varepsilon_0)$, 落在 $C_1(\Omega)$ 里.

```agda
Fr : ℕ → Ordᶜ L₁
Fr n = ψ {i = L₁} {k = L₁} {ℓ = L₂} zero σ₁ (up zero (δ n))

t-rise : Ordᶜ L₁
t-rise = lim Fr

δ≺ : ∀ i → δ i ≺ᵛ δ (suc i)
δ≺ i = ≼-trans (s≼s (≅→≼ (≅-sym (γ≅δ i)))) (≼-trans (γ-step i) (≅→≼ (γ≅δ (suc i))))

s-Fr : ∀ i → IsPsi L₁ (δ i) (Fr i)
s-Fr i = IsPsi-a (≅→≈ᵛ (γ≅δ i))
  (IsPsi-t (≅→≈ᵛ (ψ-≅ {p = zero} {σ = λ ()} {p′ = zero} {σ′ = λ q → σ₁ (suc q)} (≅ᴵ-refl L₁) (γ≅δ i)))
           (correct₁ (reg→Str (reg-γ i))))

rise-value : IsPsi L₁ (lim δ) t-rise
rise-value = Tlim ΩO-1 s-Fr δ≺ (λ i → b∈ (δ i)) (λ i → b∈ (forget L₁))

rise-in : C L₁ Ω₁ t-rise
rise-in = col (b∈ (forget L₁)) (b∈ (lim δ)) (bnd⁰ (lim δ)) (irr≡ (wf (lim δ)) _ rise-value)

rise-rejected : ¬ IsPsi L₁ Ω₁ t-rise
rise-rejected s = ¬in s rise-in

rise≺pen : t-rise ≺ᵛ tp
rise≺pen = ub pen-right rise-in (lt rise-value)
```
