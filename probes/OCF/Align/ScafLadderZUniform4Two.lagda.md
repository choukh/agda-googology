> **机械克隆.** 由 `Uniform4Two` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (四): 层号 $\Omega+\alpha$ ($\alpha$ 可数) 上的数据树

> 接 [Uniform4Base](Uniform4Base.lagda.md). 把 `O c` 的层号从 ℕ 换成 `Ordᴵ`: `oΩ` 的层号 $k<^\mathsf I\alpha$, 比较用 `<ᴵ-dec` (两个下标都在同一字面界 $\alpha$ 之下), 穿透分支要层号搬运 `trO` (与 Prefix 的 `trˢ` 同形). 这样 $\psi_0(\Omega_{\Omega\cdot2})$ 是一个定义: 闭包, 分支 $\eta$ 处 $\psi_0(\Omega_{\Omega+\eta})$. **这里只有定义 (层 1–2) 与路径检验; 标签未做.** 本文件不导入记号; 路径检验与记号侧的第一个停点 (`NF₁` 不含 $\psi_0(\Omega_{\Omega\cdot2})$, `¬NF-Ω·2`) 在 [Uniform4TwoWalk](Uniform4TwoWalk.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZUniform4Two where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ; _+ˢ_)
open import OCF.Align.ScafLadderZUniform3Base using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; A; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun)
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
```

## §1 数据树

```agda
module _ (α : Ordᴵ) (U : (i : Ordᴵ) → i ◃ α → Flr → Set) where
  data O₊ : Flr → Set where
    o0   : ∀ {φ} → O₊ φ
    os   : ∀ {φ} → O₊ φ → O₊ φ
    ol   : ∀ {φ} → (ℕ → O₊ φ) → O₊ φ
    oi   : ∀ {φ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → O₊ φ) → O₊ φ
    oŝ   : ∀ {φ} (c₀ : Ordᴵ) → O₊ φ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ φ) → O₊ φ
    oĉ   : ∀ {φ} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → O₊ φ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ φ) → O₊ φ
    oclo : ∀ {φ} → O₊ (φ ⊔ fk zero) → ((η : Ordᴵ) → O₊ (φ ⊔ fk η)) → O₊ (φ ⊔ fk zero)
    owk  : ∀ {φ ψ} → (∀ {ℓ} → Ev ℓ ψ → Ev ℓ φ) → O₊ φ → O₊ ψ
    oΩ   : ∀ {φ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : k <ᴵ α) → (∀ ξ → U k (<→◃ q) ξ → O₊ (ξ ⊔ φ)) → O₊ φ
    omk  : ∀ {φ k} → (r : k ◃₁ α) → U k (◃₁→◃ r) φ → O₊ φ → O₊ φ

O  : Ordᴵ → Flr → Set
Us : ∀ {α} (i : Ordᴵ) → i ◃ α → Flr → Set
O α φ = O₊ α Us φ
Us i zero         φ = O i φ
Us i (suc r)      φ = Us i r φ
Us _ (self {f} n) φ = O (f n) φ
Us i (lim n r)    φ = Us i r φ

outU : ∀ {i α} (r : i ◃ α) {φ} → Us i r φ → O i φ
outU zero      x = x
outU (suc r)   x = outU r x
outU (self n)  x = x
outU (lim n r) x = outU r x

intoU : ∀ {i α} (r : i ◃ α) {φ} → O i φ → Us i r φ
intoU zero      x = x
intoU (suc r)   x = intoU r x
intoU (self n)  x = x
intoU (lim n r) x = intoU r x

<◃ : ∀ {k a b} → k <ᴵ a → a ◃ b → k <ᴵ b
<◃ q zero      = suc q
<◃ q (suc r)   = suc (<◃ q r)
<◃ q (self n)  = lim n q
<◃ q (lim n r) = lim n (<◃ q r)
```

## §2 加法、嵌入、层号搬运

```agda
infixl 6 _⊕_
_⊕_ : ∀ {c φ ψ} → O c φ → O c ψ → O c (φ ⊔ ψ)
W ⊕ o0       = owk proj₁ W
W ⊕ os a     = os (W ⊕ a)
W ⊕ ol F     = ol (λ n → W ⊕ F n)
W ⊕ oi ac f  = oi (λ e → ac (proj₂ e)) (λ x → W ⊕ f x)
W ⊕ oŝ c₀ t g = oŝ c₀ (W ⊕ t) (λ η e → W ⊕ g η e)
W ⊕ oĉ c₀ z zg o₀ o = oĉ c₀ z zg (W ⊕ o₀) (λ η e → W ⊕ o η e)
W ⊕ oclo t g = owk asl (oclo (owk asr (W ⊕ t)) (λ η → owk asr (W ⊕ g η)))
W ⊕ owk le t = owk (λ e → proj₁ e , le (proj₂ e)) (W ⊕ t)
W ⊕ oΩ fe q h = oΩ (λ e → fe (proj₂ e)) q (λ ξ z → owk swp (W ⊕ h ξ z))
W ⊕ omk r z x = W ⊕ x

ι : ∀ {a b} (r : a ◃ b) {φ} → O a φ → O b φ
ι r o0 = o0
ι r (os a) = os (ι r a)
ι r (ol F) = ol (λ n → ι r (F n))
ι r (oi ac f) = oi ac (λ x → ι r (f x))
ι r (oŝ c₀ t g) = oŝ c₀ (ι r t) (λ η e → ι r (g η e))
ι r (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ι r o₀) (λ η e → ι r (o η e))
ι r (oclo t g) = oclo (ι r t) (λ η → ι r (g η))
ι r (owk le t) = owk le (ι r t)
ι r (oΩ fe q h) = oΩ fe (<◃ q r) (λ ξ z → ι r (h ξ (intoU (<→◃ q) (outU (<→◃ (<◃ q r)) z))))
ι r (omk q z x) = ι r x

record RestrO (j b : Ordᴵ) : Set where
  constructor restrO
  field
    {repO} : Ordᴵ
    eqO    : j ≅ᴵ repO
    ltO    : repO <ᴵ b
    backO  : ∀ {ξ} → O repO ξ → O j ξ
open RestrO

trO  : ∀ {a b φ} → a ≅ᴵ b → O a φ → O b φ
tr⁻O : ∀ {a b φ} → a ≅ᴵ b → O b φ → O a φ
resO : ∀ {j a b} → j <ᴵ a → a ≅ᴵ b → RestrO j b
res⁻O : ∀ {j a b} → j <ᴵ b → a ≅ᴵ b → RestrO j a

trO e o0 = o0
trO e (os a) = os (trO e a)
trO e (ol F) = ol (λ n → trO e (F n))
trO e (oi ac f) = oi ac (λ x → trO e (f x))
trO e (oŝ c₀ t g) = oŝ c₀ (trO e t) (λ η d → trO e (g η d))
trO e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (trO e o₀) (λ η d → trO e (o η d))
trO e (oclo t g) = oclo (trO e t) (λ η → trO e (g η))
trO e (owk le t) = owk le (trO e t)
trO e (oΩ fe q h) = oΩ fe (ltO (resO q e)) (λ ξ z → trO e (h ξ (intoU (<→◃ q) (backO (resO q e) (outU (<→◃ (ltO (resO q e))) z)))))
trO (s≅ e) (omk zero z x) = omk zero (trO e z) (trO (s≅ e) x)
trO (l≅ h) (omk (self n) z x) = omk (self n) (trO (h n) z) (trO (l≅ h) x)

tr⁻O e o0 = o0
tr⁻O e (os a) = os (tr⁻O e a)
tr⁻O e (ol F) = ol (λ n → tr⁻O e (F n))
tr⁻O e (oi ac f) = oi ac (λ x → tr⁻O e (f x))
tr⁻O e (oŝ c₀ t g) = oŝ c₀ (tr⁻O e t) (λ η d → tr⁻O e (g η d))
tr⁻O e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (tr⁻O e o₀) (λ η d → tr⁻O e (o η d))
tr⁻O e (oclo t g) = oclo (tr⁻O e t) (λ η → tr⁻O e (g η))
tr⁻O e (owk le t) = owk le (tr⁻O e t)
tr⁻O e (oΩ fe q h) = oΩ fe (ltO (res⁻O q e)) (λ ξ z → tr⁻O e (h ξ (intoU (<→◃ q) (backO (res⁻O q e) (outU (<→◃ (ltO (res⁻O q e))) z)))))
tr⁻O (s≅ e) (omk zero z x) = omk zero (tr⁻O e z) (tr⁻O (s≅ e) x)
tr⁻O (l≅ h) (omk (self n) z x) = omk (self n) (tr⁻O (h n) z) (tr⁻O (l≅ h) x)

resO zero      (s≅ e) = restrO e zero (tr⁻O e)
resO (suc q)   (s≅ e) = restrO (eqO (resO q e)) (suc (ltO (resO q e))) (backO (resO q e))
resO (lim n q) (l≅ h) = restrO (eqO (resO q (h n))) (lim n (ltO (resO q (h n)))) (backO (resO q (h n)))

res⁻O zero      (s≅ e) = restrO (≅ᴵ-sym e) zero (trO e)
res⁻O (suc q)   (s≅ e) = restrO (eqO (res⁻O q e)) (suc (ltO (res⁻O q e))) (backO (res⁻O q e))
res⁻O (lim n q) (l≅ h) = restrO (eqO (res⁻O q (h n))) (lim n (ltO (res⁻O q (h n)))) (backO (res⁻O q (h n)))

tl : ∀ {c k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k ℓ) → Ordˢ k → O c φ
tl φ cv Ord₊ˢ.zero = o0
tl φ cv (Ord₊ˢ.suc a) = os (tl φ cv a)
tl φ cv (Ord₊ˢ.lim f) = ol (λ n → tl φ cv (f n))
tl φ cv (Ord₊ˢ.limᵢ q f) = oi (λ e → cv e q) (λ x → tl φ cv (f (intoˢ (<→◃ q) x)))
tl {k = suc k′} φ cv (Ord₊ˢ.up zero x) = owk (λ v → toFlo k′ (λ q → cv v (suc q))) (tl (flo k′) (cvFlo k′) x)
tl {k = lim f s} φ cv (Ord₊ˢ.up (self n) x) = owk (λ v → toFlo (f n) (λ q → cv v (lim n q))) (tl (flo (f n)) (cvFlo (f n)) x)
tl {k = zero} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = oĉ c₀ (toZ t₀) (λ η e → toZ (g η e)) (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl {k = suc _} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = oŝ c₀ (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl {k = lim _ _} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = oŝ c₀ (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl φ cv (Ord₊ˢ.ĉᴸ c₀ t₀ g o₀ o) = oĉ c₀ t₀ g (tl φ cv o₀) (λ η e → tl φ cv (o η e))


Ω̇ : ∀ α → O α Fl
Ω̇ zero = oclo (tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) (λ η → tl (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η))
Ω̇ (suc α) = oΩ (λ e → e) zero (λ ξ z → owk proj₁ (omk zero z (ι zero z)))
Ω̇ (lim f s) = ol (λ n → omk (self n) (Ω̇ (f n)) (ι (self n) (Ω̇ (f n))))
```

## §3 折叠

```agda
repᵒ : ∀ {c φ} → O c φ → ℕ → O c φ
repᵒ x zero          = o0
repᵒ x (suc zero)    = x
repᵒ x (suc (suc m)) = owk (λ e → e , e) (repᵒ x (suc m) ⊕ x)

chainᵒ : ∀ {k φ} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (O k φ → O k φ) → ℕ → O k φ
chainᵒ {k} fe f zero    = owk fe (Ω̇ k)
chainᵒ fe f (suc n) = f (chainᵒ fe f n)

ψᵒ : ∀ {α t} → t <ᴵ α → ∀ {φ} → O α φ → O t (Fl ⊔ φ)
ψᵒ {t = t} q o0 = owk proj₁ (Ω̇ t)
ψᵒ q (os a) = ol (repᵒ (ψᵒ q a))
ψᵒ q (ol F) = ol (λ n → ψᵒ q (F n))
ψᵒ q (oi ac f) = oi (λ e → ac (proj₂ e)) (λ x → ψᵒ q (f x))
ψᵒ q (oŝ c₀ t g) = oŝ c₀ (ψᵒ q t) (λ η e → ψᵒ q (g η e))
ψᵒ q (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψᵒ q o₀) (λ η e → ψᵒ q (o η e))
ψᵒ q (oclo t g) = owk asl (oclo (owk asr (ψᵒ q t)) (λ η → owk asr (ψᵒ q (g η))))
ψᵒ q (owk le x) = owk (λ e → proj₁ e , le (proj₂ e)) (ψᵒ q x)
ψᵒ q (omk r z x) = ψᵒ q x
ψᵒ q {φ} (oΩ fe r h) with <ᴵ-dec r q
... | injᵃ (via e s) =
  oΩ proj₁ s (λ ξ y → owk swp (ψᵒ q (h ξ (intoU (<→◃ r) (tr⁻O e (outU (<→◃ s) y))))))
... | injᵇ _ =
  ol (λ n → owk dupr2 (ψᵒ q (h (Fl ⊔ φ) (intoU (<→◃ r) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU (<→◃ r) z)))) n)))))
... | injᶜ _ =
  ol (λ n → owk dupr2 (ψᵒ q (h (Fl ⊔ φ) (intoU (<→◃ r) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU (<→◃ r) z)))) n)))))

ψ̄ : ∀ {c φ} → O c φ → Run φ
ψ̄ o0 = wk 0 (λ e → tt) ∅ᴿ
ψ̄ (os a) = sucRun (ψ̄ a)
ψ̄ (ol F) = limA 0 (λ n → ψ̄ (F n))
ψ̄ (oi ac f) = limᵢA 0 ac (λ x → ψ̄ (f x))
ψ̄ (oŝ c₀ t g) = ŝA 0 c₀ (ψ̄ t) (λ η e → ψ̄ (g η e))
ψ̄ (oĉ c₀ z zg o₀ o) = ĉA 0 c₀ z zg (ψ̄ o₀) (λ η e → ψ̄ (o η e))
ψ̄ (oclo t g) = cloA 0 (ψ̄ t) (λ η → ψ̄ (g η))
ψ̄ (owk le x) = wk 0 le (ψ̄ x)
ψ̄ (omk r z x) = ψ̄ x
ψ̄ {φ = φ} (oΩ fe r h) =
  limA 0 (λ n → wk 0 (λ v → v , v)
                (ψ̄ (h φ (intoU (<→◃ r) (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n)))))

-- ψ₀(Ω_{Ω·2}): 闭包, 分支 η 处 ψ₀(Ω_{Ω+η})
TΩ·2 : Run (Fl ⊔ fk zero)
TΩ·2 = cloA 0 {Fl} (wk 0 proj₁ (ψ̄ (Ω̇ (suc zero)))) (λ η → wk 0 proj₁ (ψ̄ (Ω̇ η)))
```

## §4 评估 (纸面)

**$\psi_0(\Omega_{\Omega\cdot2})$ 的标签还缺什么.** 三件. (1) `Ld`/`Rᵒ` 与全部封闭性从 ℕ 换到 `Ordᴵ`: `lΩ` 带 $k\cong$ `lvI Iν`, 头 $\Omega+\nu$. `cmp<` 的规格换成 `<ᴵ-dec` 对 `cmpᵀ` 的相容 (`Ilt`/`Ieq` + 可数项上 $\nu<\tau\Rightarrow\nu+1\le\tau$), 这是一对下标的比较, 不需要 `pickMax`: 两者都已在同一字面界 $\alpha$ 之下. (2) `trO` 保持标签与互模拟. (3) 记号: `NF₁` 的 `Sb` 不含 $\Omega+\Omega$; 顶层一步要 `NF₁` 的推广或换成 EBOI 的 `isOTᵉ`. (1)、(2) 是机械的, 我估计是 Uniform4 现有证明的一次改写; 这只是估计. (3) 是 StandardOmega 的范围问题, 不是树的问题.

**弹出的地板.** Uniform3OmegaPlus1 §6 担心 "弹出闭包的地板下标 $\Omega+c$ 没有 `Idx`". 这里不发生: `TΩ·2` 的闭包是 `cloA` 在可数目标上的行, 界只看目标与 `Fl`, 分支 $\eta$ 处的树不比较 $\Omega+\eta$ 与目标 (`ψ̄` 对 `oΩ` 总是链). `pickMax` 不必推广到这里.

**$\psi_0(\Omega_{\Omega_\Omega})$: 第一个看得见的墙 (纸面).** 下标 $u<\Omega_\Omega$ 不再是 `Ordᴵ`, 而是 `O 0` 的树. `O` 要对这样的下标定义, `ψᵒ` 要比较两个这样的下标. `<ᴵ-dec` 的类比是 "以 $\Omega_\Omega$ 为界的结构三歧", 而 InaccTree 的 `noBT` 说这是假的. 所以要么把地板搬到下标上 (下标比较也带字面证据), 要么下标比较读记号. 这与 `Lv` 的判决 `D` 是同一个问题, 数据树没有绕开它: 数据树就是 `Lv` 的 `ψ↓` 加上 Uniform3 的字面地板, 只把 `Lv` 的判决限制在 $\Omega+\alpha$ 这段可判定的范围里. 我没有试过这一步.
