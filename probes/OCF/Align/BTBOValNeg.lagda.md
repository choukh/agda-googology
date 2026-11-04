# 字面的 `⊑⁰` 对 src 的 BTBO 是假的

> 接 [BTBOValMain](BTBOValMain.lagda.md). **验收文件, 读 `Label`.** 值验收在 AGENTS 里写作 "与带字面标签的树互相 $\sqsubseteq^0$". 本文证: src 的 BTBO 过不了这一档, 对任何带字面标签 $\psi_0(\Omega_\Omega)$ 的树 (`no-⊑⁰`, `no-⊑⁰-lab`). 否定的只是这个字面关系, 不否定序数值相等 (`≼`).
>
> **理由.** $\sqsubseteq^0$ 的叶子是 $\cong$. src 的 $\Omega_0=\omega$ 让 $\omega^\omega$ 这一项的基本列是 $\omega,\omega^2,\dots$ (`Cs`), Level 的是 $1,\omega,\omega^2,\dots$ (`C′`). 两棵子树值相等, 不 $\cong$. `Cs` 是 src 的 BTBO 的字面前驱. 如果它也是 `BTBOᴵ` 的字面前驱, 那么 `Cs`, `C′` 就是同一棵 `HS` 树的两个前驱, 由层号的有界三歧, 一个严格小于另一个或二者 $\cong$, 都与值相等矛盾.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOValNeg where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; injᵃ; injᵇ; injᶜ)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ)
open S using (iter; ordᴰ; ψⁿ; BTBO; zero; suc; lim; limᵢ)
open import OCF.Align.Level
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValMain using (T-nat; g-nat)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; ≅→≼; s≼s⁻; s≼0; ≼lim⁻; ≼i; ≼u)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.Label using (BTBO-label)
import OCF.Align.EBO as E′
```

## §1 第 0 层的折叠, 基底作参数

`Pf b` 是第 0 层上的折叠, 只差基底: $b=\omega$ 是 src 的 $\psi_0$, $b=1$ 是 Level 的 $\psi^0$.

```agda
Pf : Ordᶜ Ordᴵ.zero → Ordᶜ Ordᴵ.zero → Ordᶜ Ordᴵ.zero
Pf b zero        = b
Pf b (suc a)     = lim (iter (Pf b a +_) zero)
Pf b (lim h)     = lim (λ n → Pf b (h n))
Pf b (limᵢ () f)
Pf b (up () x)

iter-≅ : ∀ {A A′ : Ordᶜ Ordᴵ.zero} → A ≅ A′ → ∀ n → iter (A +_) zero n ≅ iter (A′ +_) zero n
iter-≅ e zero    = z≅
iter-≅ e (suc n) = add-≅ e (iter-≅ e n)

Pf-≅ : ∀ {b x y} → b ≅ b → x ≅ y → Pf b x ≅ Pf b y
Pf-≅ eb z≅     = eb
Pf-≅ eb (s≅ e) = l≅ (iter-≅ (Pf-≅ eb e))
Pf-≅ eb (l≅ h) = l≅ (λ n → Pf-≅ eb (h n))
Pf-≅ eb (lᵢ≅ {p = ()} e h)
Pf-≅ eb (upˡ {r = ()} e)
Pf-≅ eb (upʳ {r = ()} e)

z≺Pf : ∀ {b} → 𝟎 {Ordᴵ.zero} ≺ b → ∀ w → 𝟎 {Ordᴵ.zero} ≺ Pf b w
z≺Pf zb zero        = zb
z≺Pf zb (suc a)     = ≺l 1 (z≺Pf zb a)
z≺Pf zb (lim h)     = ≺l 0 (z≺Pf zb (h 0))
z≺Pf zb (limᵢ () f)
z≺Pf zb (up () x)

add-≺ : ∀ (a : Ordᶜ Ordᴵ.zero) {c b : Ordᶜ Ordᴵ.zero} → c ≺ b → (a + c) ≺ (a + b)
add-≺ a (≺z e)   = ≺z (add-≅ (≅-refl⁰ a) e)
add-≺ a (≺s h)   = ≺s (add-≺ a h)
add-≺ a (≺l n h) = ≺l n (add-≺ a h)
add-≺ a (≺i {p = ()} x ex h)
add-≺ a (≺u {r = ()} h)

A-step : ∀ {b} → 𝟎 {Ordᴵ.zero} ≺ b → ∀ w → Pf b w ≺ Pf b (suc w)
A-step {b} zb w = ≺l 2 (add-≺ (Pf b w) (z≺Pf zb w))

B-step : ∀ {b w₁ w₂} → b ≅ b → w₁ ≺ w₂ → Pf b (suc w₁) ⊑ Pf b w₂
B-step eb (≺z e)   = ≅→⊑ (Pf-≅ eb (s≅ e))
B-step {b} {w₂ = suc w} eb (≺s h) = ⊑-trans (B-step eb h) (⊑-lim 1 (≅→⊑ (Pf-≅ eb (≅-refl⁰ w))))
B-step eb (≺l n h) = ⊑-lim n (B-step eb h)
B-step eb (≺i {p = ()} x ex h)
B-step eb (≺u {r = ()} h)

self≺ : ∀ {b} → b ≅ b → 𝟎 {Ordᴵ.zero} ≺ b → ωᶜ ≺ Pf b ωᶜ → Pf b ωᶜ ≺ Pf b (Pf b ωᶜ)
self≺ eb zb ω≺ = B-step eb ω≺ (A-step zb ωᶜ)
```

## §2 两棵子树

```agda
𝟏′ : Ordᶜ Ordᴵ.zero
𝟏′ = suc zero

Cs C′ : Ordᶜ Ordᴵ.zero
Cs = Pf ωᶜ ωᶜ
C′ = Pf 𝟏′ ωᶜ

Cs≇C′ : ¬ (Cs ≅ C′)
Cs≇C′ (l≅ h) with h 0
... | ()

e0 : Pf 𝟏′ 𝟏′ ≅ ωᶜ
e0 = l≅ (λ n → subst (λ u → iter (𝟏′ +_) zero n ≅ u) (T-nat n) (≅-refl⁰ _))

shift : ∀ n → Pf ωᶜ (natᶜ n) ≅ Pf 𝟏′ (natᶜ (suc n))
shift zero    = ≅-sym e0
shift (suc n) = l≅ (iter-≅ (shift n))

Cs≼C′ : Cs ≼ C′
Cs≼C′ = l≼ (λ n → ≼l (suc n) (≅→≼ (shift n)))

C′≼Cs : C′ ≼ Cs
C′≼Cs = l≼ (λ n → ≼l n (≼-trans (≼l 1 (≼-refl _)) (≅→≼ (≅-sym (shift n)))))
```

## §3 `Cs` 是 src 的 BTBO 的字面前驱

路径: $x_2$ 的第 1 项 ($\psi_0(\Omega_2)$) 的第 1 项 ($\psi_0(\Omega_1)$) 是 `lim Uˣ`, $U_3=\psi_0(\uparrow U_2)$, $U_2\cong$ `Cs`, $U_3\cong$ `Pf ω Cs`. `sq` 只用来写出路径, `refl` 核实.

```agda
sq : S.Ord₀ → ℕ → S.Ord₀
sq (lim f) = f
sq _       = λ _ → zero

Pp : B.zero B.< ordᴰ S.ω
Pp = B.lim 1 (B.suc B.zero)

Pr : B.suc (B.suc B.zero) B.< ordᴰ S.ω
Pr = B.lim 2 (B.suc (B.suc B.zero))

eU : S.Ord₀ → S.Ord (ordᴰ S.ω)
eU x = S.↑ Pr (S.↑ B.zero (S.↑ B.zero x))

Uˣ : ℕ → S.Ord₀
Uˣ = iter (λ x → S.ψ< Pp (eU x)) zero

deep : sq (sq (ψⁿ 2) 1) 1 ≡ lim Uˣ
deep = refl

tr₀-+ : ∀ (a b : S.Ord₀) → tr₀ (a S.+ b) ≅ (tr₀ a + tr₀ b)
tr₀-+ a zero        = ≅-refl⁰ _
tr₀-+ a (suc b)     = s≅ (tr₀-+ a b)
tr₀-+ a (lim h)     = l≅ (λ n → tr₀-+ a (h n))
tr₀-+ a (limᵢ () f)

tr₀-iter : ∀ {A : S.Ord₀} {A′ : Ordᶜ Ordᴵ.zero} → tr₀ A ≅ A′ → ∀ n → tr₀ (iter (A S.+_) zero n) ≅ iter (A′ +_) zero n
tr₀-iter e zero    = z≅
tr₀-iter {A} {A′} e (suc n) = ≅-trans (tr₀-+ A _) (add-≅ e (tr₀-iter e n))

tr₀ω : tr₀ S.ω ≅ ωᶜ
tr₀ω = go _ refl (λ _ → refl) where
  go : (g : ℕ → S.Ord₀) → g 0 ≡ zero → (∀ n → g (suc n) ≡ suc (g n)) → tr₀ (lim g) ≅ ωᶜ
  go g g0 gs = l≅ (λ n → subst (λ u → u ≅ natᶜ n) (sym (g-nat g g0 gs n)) (≅-refl⁰ _))

E : ∀ (x : S.Ord₀) → tr₀ (S.ψ< Pp (eU x)) ≅ Pf ωᶜ (tr₀ x)
E zero        = tr₀ω
E (suc a)     = l≅ (tr₀-iter (E a))
E (lim h)     = l≅ (λ n → E (h n))
E (limᵢ () f)

ωrefl : ωᶜ ≅ ωᶜ
ωrefl = ≅-refl⁰ ωᶜ

U1≅ : tr₀ (Uˣ 1) ≅ ωᶜ
U1≅ = E zero

U2≅ : tr₀ (Uˣ 2) ≅ Cs
U2≅ = ≅-trans (E (Uˣ 1)) (Pf-≅ ωrefl U1≅)

U3≅ : tr₀ (Uˣ 3) ≅ Pf ωᶜ Cs
U3≅ = ≅-trans (E (Uˣ 2)) (Pf-≅ ωrefl U2≅)

zω : 𝟎 {Ordᴵ.zero} ≺ ωᶜ
zω = ≺l 1 (≺z z≅)

ω≺Cs : ωᶜ ≺ Cs
ω≺Cs = ≺l 1 (A-step zω zero)

Cs≺src : Cs ≺ tr₀ BTBO
Cs≺src = ≺l 2 (≺l 1 (≺l 1 (≺l 3 (≺-respʳ (self≺ ωrefl zω ω≺Cs) (≅-sym U3≅)))))
```

## §4 `C′` 是 `BTBOᴵ` 的字面前驱

路径: `BTBOᴵ` 的第 0 项是 $\gamma_1=\lim\psi^0(G_n)$, 第 2 项 $\psi^0(G_2)\cong$ `Pf 1 C′`.

```agda
𝟏z : 𝟎 {Ordᴵ.zero} ≺ 𝟏′
𝟏z = ≺z z≅

𝟏refl : 𝟏′ ≅ 𝟏′
𝟏refl = s≅ z≅

ψ⁰-Pf : ∀ x → ψ⁰ x ≅ Pf 𝟏′ x
ψ⁰-Pf zero        = 𝟏refl
ψ⁰-Pf (suc a)     = l≅ (iter-≅ (ψ⁰-Pf a))
ψ⁰-Pf (lim h)     = l≅ (λ n → ψ⁰-Pf (h n))
ψ⁰-Pf (limᵢ () f)
ψ⁰-Pf (up () x)

G : ℕ → Ordᶜ Ordᴵ.zero
G = N.D.G

G-step : ∀ n → G (suc n) ≅ ψ⁰ (G n)
G-step n = ≅-sym (ψ⁰≅ψ {p = zero} {σ = λ q → suc q} (≅-refl⁰ (G n)))

G1≅ : G 1 ≅ ωᶜ
G1≅ = ≅-trans (G-step 0) (≅-trans (ψ⁰-Pf 𝟏′) e0)

G2≅ : G 2 ≅ C′
G2≅ = ≅-trans (G-step 1) (≅-trans (ψ⁰-Pf (G 1)) (Pf-≅ 𝟏refl G1≅))

ψG2≅ : ψ⁰ (G 2) ≅ Pf 𝟏′ C′
ψG2≅ = ≅-trans (ψ⁰-Pf (G 2)) (Pf-≅ 𝟏refl G2≅)

ω≺C′ : ωᶜ ≺ C′
ω≺C′ = ≺l 2 (≺-respˡ e0 (A-step 𝟏z 𝟏′))

C′≺I : C′ ≺ BTBOᴵ
C′≺I = ≺l 0 (≺l 2 (≺-respʳ (self≺ 𝟏refl 𝟏z ω≺C′) (≅-sym ψG2≅)))
```

## §5 否定

```agda
HS-≅ : ∀ {a b : Ordᶜ Ordᴵ.zero} → a ≅ b → HS b → HS a
HS-≅ z≅     h = hz
HS-≅ (s≅ e) h = hs (HS-≅ e (hs⁻ h))
HS-≅ (l≅ k) h = hl (λ n → HS-≅ (k n) (hl₁ h n))
                   (λ n → ⊑-trans (≅→⊑ (k n)) (⊑-trans (hl₂ h n) (≅→⊑ (≅-sym (k (suc n))))))
HS-≅ (lᵢ≅ {p = ()} e k) h
HS-≅ (upˡ {r = ()} e) h
HS-≅ (upʳ {r = ()} e) h

HS-≺ : ∀ {c b : Ordᶜ Ordᴵ.zero} → c ≺ b → HS b → HS c
HS-≺ (≺z e)   h = HS-≅ e (hs⁻ h)
HS-≺ (≺s d)   h = HS-≺ d (hs⁻ h)
HS-≺ (≺l n d) h = HS-≺ d (hl₁ h n)
HS-≺ (≺i {p = ()} x ex d) h
HS-≺ (≺u {r = ()} d) h

forget-≅ᴵ : ∀ {a b} → a ≅ᴵ b → forget a ≅ forget b
forget-≅ᴵ z≅     = z≅
forget-≅ᴵ (s≅ e) = s≅ (forget-≅ᴵ e)
forget-≅ᴵ (l≅ h) = l≅ (λ n → forget-≅ᴵ (h n))

<→s≼ : ∀ {a b} → a <ᴵ b → suc (forget a) ≼ forget b
<→s≼ zero      = s≼s (≼-refl _)
<→s≼ (suc q)   = ≼-suc (<→s≼ q)
<→s≼ (lim n q) = ≼l n (<→s≼ q)

≺ᴵ→s≼ : ∀ {a b} → a ≺ᴵ b → suc (forget a) ≼ forget b
≺ᴵ→s≼ (via e q) = ≼-trans (s≼s (≅→≼ (forget-≅ᴵ e))) (<→s≼ q)

≼-irr : ∀ (a : Ordᶜ Ordᴵ.zero) → ¬ (suc a ≼ a)
≼-irr zero        p = s≼0 p
≼-irr (suc a)     p = ≼-irr a (s≼s⁻ p)
≼-irr (lim f)     p with ≼lim⁻ p
... | n , q = ≼-irr (f n) (≼-trans (s≼s (≼l n (≼-refl (f n)))) q)
≼-irr (limᵢ () f) p
≼-irr (up () x)   p

two-preds : ∀ {a b c} → a ≺ᴵ c → b ≺ᴵ c → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
two-preds (via e q) (via e′ q′) with <ᴵ-dec q q′
... | injᵃ r = injᵃ (≺ᴵ-respˡ e (≺ᴵ-respʳ r (≅ᴵ-sym e′)))
... | injᵇ r = injᵇ (≺ᴵ-respˡ e′ (≺ᴵ-respʳ r (≅ᴵ-sym e)))
... | injᶜ r = injᶜ (≅ᴵ-trans e (≅ᴵ-trans r (≅ᴵ-sym e′)))

no-⊑⁰ : ¬ (tr₀ BTBO ⊑⁰ BTBOᴵ)
no-⊑⁰ k with Cs≺I | HS-≺ Cs≺I N.BTBO-HS | HS-≺ C′≺I N.BTBO-HS
  where Cs≺I = k Cs≺src
... | Cs≺I | hc | hc′ with two-preds (toLevel-≺ hc N.BTBO-HS Cs≺I) (toLevel-≺ hc′ N.BTBO-HS C′≺I)
... | injᵃ r = ≼-irr Cs (≼-trans (s≼s (≅→≼ (≅-sym (forget-toLevel Cs hc))))
                        (≼-trans (≺ᴵ→s≼ r) (≼-trans (≅→≼ (forget-toLevel C′ hc′)) C′≼Cs)))
... | injᵇ r = ≼-irr C′ (≼-trans (s≼s (≅→≼ (≅-sym (forget-toLevel C′ hc′))))
                        (≼-trans (≺ᴵ→s≼ r) (≼-trans (≅→≼ (forget-toLevel Cs hc)) Cs≼C′)))
... | injᶜ r = Cs≇C′ (≅-trans (≅-sym (forget-toLevel Cs hc)) (≅-trans (forget-≅ᴵ r) (forget-toLevel C′ hc′)))
```

**对一切带字面标签的树.** `Lab` 决定树到 $\cong$ (`Lab-uniq`), $\sqsubseteq^0$ 尊重 $\cong$, 所以换一棵带标签的树也一样.

```agda
no-⊑⁰-lab : ∀ {Y} → Lab Y (E′.EBOψ 2) → ¬ (tr₀ BTBO ⊑⁰ Y)
no-⊑⁰-lab L k = no-⊑⁰ (λ h → ≅→⊑ (Lab-uniq L BTBO-label) (k h))
```
