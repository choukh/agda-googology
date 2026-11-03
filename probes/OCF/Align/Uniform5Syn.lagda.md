# 统一形 (五): 层号 $\Omega\cdot(m+1)+\alpha$ 的数据树 (下一堵墙的实验)

> 接 [Uniform4Two](Uniform4Two.lagda.md). 本文不导入记号. 结论先说:
>
> 1. **`Q m α φ`: $<\Omega_{\Omega\cdot(m+1)+\alpha}$ 的项的树.** 层号是一对 $(m,\alpha)$, 这对层号就是 `OmegaPlus1` §3 说的 `Syn` 的第一个非平凡实例. $m=0$ 时是 Uniform4Two 的 `O α` 加两个不用的构造子.
> 2. **两个新构造子.** `oΩ↓`: 输入在低 $m$ 的层 $(n,k)$, $k$ 不受 $\alpha$ 约束 (下层的 $k$ 取遍 `Ordᴵ`, 所以 $\Omega\cdot(m+1)$ 的节点不是任何一个 `Ordᴵ` 的字面子项). 它带地板证据 `ac : Ev ℓ φ → k <ᴵ ℓ`. `oev`: **推迟的节点**, 看到环境 $\ell$ 才决定形状.
> 3. **`ι↓` 产生地板.** 把 `Q n k` 嵌入 `Q m α` ($n<m$) 时, `Q n k` 的字面节点 $i<k$ 没有字面的上界, 所以输出多一个地板 `flo k` (证据 $i<k<\ell$). 这就是 $\Omega_{\Omega\cdot2}[\eta]=\Omega_{\Omega+\eta}$ 的闭包分支 $\eta$ 给的地板 `fk η` 的来源.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5Syn where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
open import OCF.Align.Uniform3Base using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; A; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun)
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2; _<ᴸ_; zero; suc; tr<)
open import OCF.Align.Uniform4Two using (<◃)
```

## §1 数据树

```agda
module _ (m : ℕ) (α : Ordᴵ) (U : (i : Ordᴵ) → i ◃ α → Flr → Set) (V : ∀ {n} → n <ᴸ m → Ordᴵ → Flr → Set) where
  data Q₊ : Flr → Set where
    o0   : ∀ {φ} → Q₊ φ
    os   : ∀ {φ} → Q₊ φ → Q₊ φ
    ol   : ∀ {φ} → (ℕ → Q₊ φ) → Q₊ φ
    oi   : ∀ {φ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → Q₊ φ) → Q₊ φ
    oŝ   : ∀ {φ} (c₀ : Ordᴵ) → Q₊ φ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Q₊ φ) → Q₊ φ
    oĉ   : ∀ {φ} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → Q₊ φ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Q₊ φ) → Q₊ φ
    oclo : ∀ {φ} → Q₊ (φ ⊔ fk zero) → ((η : Ordᴵ) → Q₊ (φ ⊔ fk η)) → Q₊ (φ ⊔ fk zero)
    owk  : ∀ {φ ψ} → (∀ {ℓ} → Ev ℓ ψ → Ev ℓ φ) → Q₊ φ → Q₊ ψ
    oΩ   : ∀ {φ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : k <ᴵ α) → (∀ ξ → U k (<→◃ q) ξ → Q₊ (ξ ⊔ φ)) → Q₊ φ
    oΩ↓  : ∀ {φ n k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : n <ᴸ m) → (∀ {ℓ} → Ev ℓ φ → k <ᴵ ℓ) → (∀ ξ → V q k ξ → Q₊ (ξ ⊔ φ)) → Q₊ φ
    oev  : ∀ {φ} → (∀ {ℓ} → Ev ℓ φ → Q₊ φ) → Q₊ φ

Q  : ℕ → Ordᴵ → Flr → Set
Us : ∀ m {α} (i : Ordᴵ) → i ◃ α → Flr → Set
Vs : ∀ m {n} → n <ᴸ m → Ordᴵ → Flr → Set
Q m α φ = Q₊ m α (Us m) (Vs m) φ
Us m i zero         φ = Q m i φ
Us m i (suc r)      φ = Us m i r φ
Us m _ (self {f} n) φ = Q m (f n) φ
Us m i (lim n r)    φ = Us m i r φ
Vs (suc m) zero    k φ = Q m k φ
Vs (suc m) (suc q) k φ = Vs m q k φ

outU : ∀ {m i α} (r : i ◃ α) {φ} → Us m i r φ → Q m i φ
outU zero      x = x
outU (suc r)   x = outU r x
outU (self n)  x = x
outU (lim n r) x = outU r x

intoU : ∀ {m i α} (r : i ◃ α) {φ} → Q m i φ → Us m i r φ
intoU zero      x = x
intoU (suc r)   x = intoU r x
intoU (self n)  x = x
intoU (lim n r) x = intoU r x

outV : ∀ {m n} (q : n <ᴸ m) {k φ} → Vs m q k φ → Q n k φ
outV zero    x = x
outV (suc q) x = outV q x

intoV : ∀ {m n} (q : n <ᴸ m) {k φ} → Q n k φ → Vs m q k φ
intoV zero    x = x
intoV (suc q) x = intoV q x
```

## §2 加法、嵌入、搬运

```agda
infixl 6 _⊕_
_⊕_ : ∀ {m c φ ψ} → Q m c φ → Q m c ψ → Q m c (φ ⊔ ψ)
W ⊕ o0       = owk proj₁ W
W ⊕ os a     = os (W ⊕ a)
W ⊕ ol F     = ol (λ n → W ⊕ F n)
W ⊕ oi ac f  = oi (λ e → ac (proj₂ e)) (λ x → W ⊕ f x)
W ⊕ oŝ c₀ t g = oŝ c₀ (W ⊕ t) (λ η e → W ⊕ g η e)
W ⊕ oĉ c₀ z zg o₀ o = oĉ c₀ z zg (W ⊕ o₀) (λ η e → W ⊕ o η e)
W ⊕ oclo t g = owk asl (oclo (owk asr (W ⊕ t)) (λ η → owk asr (W ⊕ g η)))
W ⊕ owk le t = owk (λ e → proj₁ e , le (proj₂ e)) (W ⊕ t)
W ⊕ oΩ fe q h = oΩ (λ e → fe (proj₂ e)) q (λ ξ z → owk swp (W ⊕ h ξ z))
W ⊕ oΩ↓ fe q ac h = oΩ↓ (λ e → fe (proj₂ e)) q (λ e → ac (proj₂ e)) (λ ξ z → owk swp (W ⊕ h ξ z))
W ⊕ oev f = oev (λ e → W ⊕ f (proj₂ e))

ι : ∀ {m a b} (r : a ◃ b) {φ} → Q m a φ → Q m b φ
ι r o0 = o0
ι r (os a) = os (ι r a)
ι r (ol F) = ol (λ n → ι r (F n))
ι r (oi ac f) = oi ac (λ x → ι r (f x))
ι r (oŝ c₀ t g) = oŝ c₀ (ι r t) (λ η e → ι r (g η e))
ι r (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ι r o₀) (λ η e → ι r (o η e))
ι r (oclo t g) = oclo (ι r t) (λ η → ι r (g η))
ι r (owk le t) = owk le (ι r t)
ι r (oΩ fe q h) = oΩ fe (<◃ q r) (λ ξ z → ι r (h ξ (intoU (<→◃ q) (outU (<→◃ (<◃ q r)) z))))
ι r (oΩ↓ fe q ac h) = oΩ↓ fe q ac (λ ξ z → ι r (h ξ z))
ι r (oev f) = oev (λ e → ι r (f e))

sw₃ : ∀ {a b d ℓ} → Ev ℓ ((a ⊔ b) ⊔ d) → Ev ℓ ((a ⊔ d) ⊔ b)
sw₃ ((u , v) , w) = (u , w) , v

ddup : ∀ {a b ℓ} → Ev ℓ (a ⊔ b) → Ev ℓ ((a ⊔ b) ⊔ b)
ddup (u , v) = (u , v) , v

ι↓ : ∀ {n m k α} (q : n <ᴸ m) {φ} → Q n k φ → Q m α (φ ⊔ flo k)
ι↓ q o0 = o0
ι↓ q (os a) = os (ι↓ q a)
ι↓ q (ol F) = ol (λ n → ι↓ q (F n))
ι↓ q (oi ac f) = oi (λ e → ac (proj₁ e)) (λ x → ι↓ q (f x))
ι↓ q (oŝ c₀ t g) = oŝ c₀ (ι↓ q t) (λ η e → ι↓ q (g η e))
ι↓ q (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ι↓ q o₀) (λ η e → ι↓ q (o η e))
ι↓ q (oclo t g) = owk sw₃ (oclo (owk sw₃ (ι↓ q t)) (λ η → owk sw₃ (ι↓ q (g η))))
ι↓ q (owk le t) = owk (λ e → le (proj₁ e) , proj₂ e) (ι↓ q t)
ι↓ {k = k} q (oΩ fe r h) =
  oΩ↓ (λ e → fe (proj₁ e)) q (λ e → cvFlo k (proj₂ e) r) (λ ξ z → owk asl (ι↓ q (h ξ (intoU (<→◃ r) (outV q z)))))
ι↓ q (oΩ↓ fe r ac h) =
  oΩ↓ (λ e → fe (proj₁ e)) (tr< r q) (λ e → ac (proj₁ e)) (λ ξ z → owk asl (ι↓ q (h ξ (intoV r (outV (tr< r q) z)))))
ι↓ q (oev f) = oev (λ e → ι↓ q (f (proj₁ e)))

record RestrO (m : ℕ) (j b : Ordᴵ) : Set where
  constructor restrO
  field
    {repO} : Ordᴵ
    eqO    : j ≅ᴵ repO
    ltO    : repO <ᴵ b
    backO  : ∀ {ξ} → Q m repO ξ → Q m j ξ
open RestrO public

trO  : ∀ {m a b φ} → a ≅ᴵ b → Q m a φ → Q m b φ
tr⁻O : ∀ {m a b φ} → a ≅ᴵ b → Q m b φ → Q m a φ
resO : ∀ {m j a b} → j <ᴵ a → a ≅ᴵ b → RestrO m j b
res⁻O : ∀ {m j a b} → j <ᴵ b → a ≅ᴵ b → RestrO m j a

trO e o0 = o0
trO e (os a) = os (trO e a)
trO e (ol F) = ol (λ n → trO e (F n))
trO e (oi ac f) = oi ac (λ x → trO e (f x))
trO e (oŝ c₀ t g) = oŝ c₀ (trO e t) (λ η d → trO e (g η d))
trO e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (trO e o₀) (λ η d → trO e (o η d))
trO e (oclo t g) = oclo (trO e t) (λ η → trO e (g η))
trO e (owk le t) = owk le (trO e t)
trO e (oΩ fe q h) = oΩ fe (ltO (resO q e)) (λ ξ z → trO e (h ξ (intoU (<→◃ q) (backO (resO q e) (outU (<→◃ (ltO (resO q e))) z)))))
trO e (oΩ↓ fe q ac h) = oΩ↓ fe q ac (λ ξ z → trO e (h ξ z))
trO e (oev f) = oev (λ d → trO e (f d))

tr⁻O e o0 = o0
tr⁻O e (os a) = os (tr⁻O e a)
tr⁻O e (ol F) = ol (λ n → tr⁻O e (F n))
tr⁻O e (oi ac f) = oi ac (λ x → tr⁻O e (f x))
tr⁻O e (oŝ c₀ t g) = oŝ c₀ (tr⁻O e t) (λ η d → tr⁻O e (g η d))
tr⁻O e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (tr⁻O e o₀) (λ η d → tr⁻O e (o η d))
tr⁻O e (oclo t g) = oclo (tr⁻O e t) (λ η → tr⁻O e (g η))
tr⁻O e (owk le t) = owk le (tr⁻O e t)
tr⁻O e (oΩ fe q h) = oΩ fe (ltO (res⁻O q e)) (λ ξ z → tr⁻O e (h ξ (intoU (<→◃ q) (backO (res⁻O q e) (outU (<→◃ (ltO (res⁻O q e))) z)))))
tr⁻O e (oΩ↓ fe q ac h) = oΩ↓ fe q ac (λ ξ z → tr⁻O e (h ξ z))
tr⁻O e (oev f) = oev (λ d → tr⁻O e (f d))

resO zero      (s≅ e) = restrO e zero (tr⁻O e)
resO (suc q)   (s≅ e) = restrO (eqO (resO q e)) (suc (ltO (resO q e))) (backO (resO q e))
resO (lim n q) (l≅ h) = restrO (eqO (resO q (h n))) (lim n (ltO (resO q (h n)))) (backO (resO q (h n)))

res⁻O zero      (s≅ e) = restrO (≅ᴵ-sym e) zero (trO e)
res⁻O (suc q)   (s≅ e) = restrO (eqO (res⁻O q e)) (suc (ltO (res⁻O q e))) (backO (res⁻O q e))
res⁻O (lim n q) (l≅ h) = restrO (eqO (res⁻O q (h n))) (lim n (ltO (res⁻O q (h n)))) (backO (res⁻O q (h n)))

tl : ∀ {m c k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k ℓ) → Ordˢ k → Q m c φ
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



Ω̇ : ∀ m α → Q m α Fl
Ω̇ zero zero = oclo (tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) (λ η → tl (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η))
Ω̇ (suc m) zero =
  owk ddup
      (oclo {φ = Fl} (ι↓ zero (Ω̇ m (suc zero)))
            (λ η → owk (λ e → proj₁ e , toFlo η (λ q → proj₂ e (suc q))) (ι↓ zero (Ω̇ m η))))
Ω̇ m (suc α) = oΩ (λ e → e) zero (λ ξ z → owk proj₁ (ι zero z))
Ω̇ m (lim f s) = ol (λ n → ι (self n) (Ω̇ m (f n)))
```
