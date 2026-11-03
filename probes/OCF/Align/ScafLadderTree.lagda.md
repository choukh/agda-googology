# 阶梯 (一): $\Omega\cdot2$ 之上的树, 闭包在目标同高度或更高处求值成字面闭包

> 结论写在 [ScafLadder](ScafLadder.lagda.md). 本文不导入记号. 这是定义.
>
> **修正 (`noW` 的那个界).** 旧树让高度 1 的闭包在目标 $\Omega+a$ 之下仍是闭包 `oclo`, 它的输入 $z$ 经 `ι` 再上去时被路径上的地板抬高. 这里 $\psi_{\Omega+a}$ 不再是 `P` 到 `P` 的函数, 而是 `P` 到 `O a` 的**求值** `Ψ`: 高度 1 的世界此时已知, 高度 1 的闭包落成字面闭包 `oŝ c₀`, $c_0$ 由目标与闭包自己的地板算出, 以后再也不读地板. 这与 `ψ̄` 从 `O` 到 `Ordˢ` 同形: `Ordˢ` 换成 `O`.
>
> **结构.** `O` (已有, [Uniform4Two](Uniform4Two.lagda.md)) 是 $\Omega+\alpha$ 的树. `P α φ χ` 是 $\Omega\cdot2+\alpha$ 的树, 两份地板: $\varphi$ 是高度 0 (可数节点, `oclo`), $\chi$ 是高度 1 (节点 $\Omega+k$, 闭包 $\Omega_{\Omega\cdot2}$). 没有项文法, 没有 `oev`, 没有判决参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.ScafLadderZUniform3Base using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun; bound; Bd; Fc; FB; evF; iF; liftEv; Top)
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.ScafLadderZUniform4Two using (O; Us; o0; os; ol; oi; oŝ; oĉ; oclo; owk; oΩ; omk; Ω̇; ψ̄; repᵒ; chainᵒ; outU; intoU; <◃; trO; tr⁻O; _⊕_) renaming (ι to ιᵒ)
```

## §1 `P`

`pcl`: 高度 1 的闭包, 分支 $\eta$ 是 $\Omega_{\Omega+\eta}$ 那样的树. `pΩ↓`: 高度 1 的节点 $\Omega+k$, 输入是已有的 `O k`, $k$ 不必是字面界的子项, 证据在 $\chi$ 里. `pΩ`: 高度 2 的节点, 字面的 $k<\alpha$.

```agda
module _ (α : Ordᴵ) (U : (i : Ordᴵ) → i ◃ α → Flr → Flr → Set) where
  data P₊ : Flr → Flr → Set where
    p0   : ∀ {φ χ} → P₊ φ χ
    psu  : ∀ {φ χ} → P₊ φ χ → P₊ φ χ
    pl   : ∀ {φ χ} → (ℕ → P₊ φ χ) → P₊ φ χ
    pi   : ∀ {φ χ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → P₊ φ χ) → P₊ φ χ
    pŝ   : ∀ {φ χ} (c₀ : Ordᴵ) → P₊ φ χ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → P₊ φ χ) → P₊ φ χ
    pĉ   : ∀ {φ χ} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → P₊ φ χ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → P₊ φ χ) → P₊ φ χ
    pclo : ∀ {φ χ} → P₊ (φ ⊔ fk zero) χ → ((η : Ordᴵ) → P₊ (φ ⊔ fk η) χ) → P₊ (φ ⊔ fk zero) χ
    pcl  : ∀ {φ χ} → P₊ φ (χ ⊔ fk zero) → ((η : Ordᴵ) → P₊ φ (χ ⊔ fk η)) → P₊ φ (χ ⊔ fk zero)
    pwk  : ∀ {φ φ′ χ χ′} → (∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ) → (∀ {ℓ} → Ev ℓ χ′ → Ev ℓ χ) → P₊ φ χ → P₊ φ′ χ′
    pΩ↓  : ∀ {φ χ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (∀ {ℓ} → Ev ℓ χ → k <ᴵ ℓ) → (∀ ξ → O k ξ → P₊ (ξ ⊔ φ) χ) → P₊ φ χ
    pΩ   : ∀ {φ χ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (∀ {ℓ} → Ev ℓ χ → Ev ℓ Fl) → (q : k <ᴵ α) → (∀ ξ ζ → U k (<→◃ q) ξ ζ → P₊ (ξ ⊔ φ) (ζ ⊔ χ)) → P₊ φ χ

P  : Ordᴵ → Flr → Flr → Set
Vs : ∀ {α} (i : Ordᴵ) → i ◃ α → Flr → Flr → Set
P α φ χ = P₊ α Vs φ χ
Vs i zero         φ χ = P i φ χ
Vs i (suc r)      φ χ = Vs i r φ χ
Vs _ (self {f} n) φ χ = P (f n) φ χ
Vs i (lim n r)    φ χ = Vs i r φ χ

outV : ∀ {i α} (r : i ◃ α) {φ χ} → Vs i r φ χ → P i φ χ
outV zero      x = x
outV (suc r)   x = outV r x
outV (self n)  x = x
outV (lim n r) x = outV r x

intoV : ∀ {i α} (r : i ◃ α) {φ χ} → P i φ χ → Vs i r φ χ
intoV zero      x = x
intoV (suc r)   x = intoV r x
intoV (self n)  x = x
intoV (lim n r) x = intoV r x
```

## §2 加法, 同高度嵌入与搬运

```agda
infixl 6 _⊞_
_⊞_ : ∀ {c φ χ ψ ρ} → P c φ χ → P c ψ ρ → P c (φ ⊔ ψ) (χ ⊔ ρ)
W ⊞ p0       = pwk proj₁ proj₁ W
W ⊞ psu a     = psu (W ⊞ a)
W ⊞ pl F     = pl (λ n → W ⊞ F n)
W ⊞ pi ac f  = pi (λ e → ac (proj₂ e)) (λ x → W ⊞ f x)
W ⊞ pŝ c₀ t g = pŝ c₀ (W ⊞ t) (λ η e → W ⊞ g η e)
W ⊞ pĉ c₀ z zg o₀ o = pĉ c₀ z zg (W ⊞ o₀) (λ η e → W ⊞ o η e)
W ⊞ pclo t g = pwk asl (λ e → e) (pclo (pwk asr (λ e → e) (W ⊞ t)) (λ η → pwk asr (λ e → e) (W ⊞ g η)))
W ⊞ pcl t g = pwk (λ e → e) asl (pcl (pwk (λ e → e) asr (W ⊞ t)) (λ η → pwk (λ e → e) asr (W ⊞ g η)))
W ⊞ pwk le le′ t = pwk (λ e → proj₁ e , le (proj₂ e)) (λ e → proj₁ e , le′ (proj₂ e)) (W ⊞ t)
W ⊞ pΩ↓ fe ac h = pΩ↓ (λ e → fe (proj₂ e)) (λ e → ac (proj₂ e)) (λ ξ z → pwk swp (λ e → e) (W ⊞ h ξ z))
W ⊞ pΩ fe fc q h = pΩ (λ e → fe (proj₂ e)) (λ e → fc (proj₂ e)) q (λ ξ ζ z → pwk swp swp (W ⊞ h ξ ζ z))

ι : ∀ {a b} (r : a ◃ b) {φ χ} → P a φ χ → P b φ χ
ι r p0 = p0
ι r (psu a) = psu (ι r a)
ι r (pl F) = pl (λ n → ι r (F n))
ι r (pi ac f) = pi ac (λ x → ι r (f x))
ι r (pŝ c₀ t g) = pŝ c₀ (ι r t) (λ η e → ι r (g η e))
ι r (pĉ c₀ z zg o₀ o) = pĉ c₀ z zg (ι r o₀) (λ η e → ι r (o η e))
ι r (pclo t g) = pclo (ι r t) (λ η → ι r (g η))
ι r (pcl t g) = pcl (ι r t) (λ η → ι r (g η))
ι r (pwk le le′ t) = pwk le le′ (ι r t)
ι r (pΩ↓ fe ac h) = pΩ↓ fe ac (λ ξ z → ι r (h ξ z))
ι r (pΩ fe fc q h) = pΩ fe fc (<◃ q r) (λ ξ ζ z → ι r (h ξ ζ (intoV (<→◃ q) (outV (<→◃ (<◃ q r)) z))))

record RestrP (j b : Ordᴵ) : Set where
  constructor restrP
  field
    {repP} : Ordᴵ
    eqP    : j ≅ᴵ repP
    ltP    : repP <ᴵ b
    backP  : ∀ {ξ ζ} → P repP ξ ζ → P j ξ ζ
open RestrP public

trP  : ∀ {a b φ χ} → a ≅ᴵ b → P a φ χ → P b φ χ
tr⁻P : ∀ {a b φ χ} → a ≅ᴵ b → P b φ χ → P a φ χ
resP : ∀ {j a b} → j <ᴵ a → a ≅ᴵ b → RestrP j b
res⁻P : ∀ {j a b} → j <ᴵ b → a ≅ᴵ b → RestrP j a

trP e p0 = p0
trP e (psu a) = psu (trP e a)
trP e (pl F) = pl (λ n → trP e (F n))
trP e (pi ac f) = pi ac (λ x → trP e (f x))
trP e (pŝ c₀ t g) = pŝ c₀ (trP e t) (λ η d → trP e (g η d))
trP e (pĉ c₀ z zg o₀ o) = pĉ c₀ z zg (trP e o₀) (λ η d → trP e (o η d))
trP e (pclo t g) = pclo (trP e t) (λ η → trP e (g η))
trP e (pcl t g) = pcl (trP e t) (λ η → trP e (g η))
trP e (pwk le le′ t) = pwk le le′ (trP e t)
trP e (pΩ↓ fe ac h) = pΩ↓ fe ac (λ ξ z → trP e (h ξ z))
trP e (pΩ fe fc q h) = pΩ fe fc (ltP (resP q e)) (λ ξ ζ z → trP e (h ξ ζ (intoV (<→◃ q) (backP (resP q e) (outV (<→◃ (ltP (resP q e))) z)))))

tr⁻P e p0 = p0
tr⁻P e (psu a) = psu (tr⁻P e a)
tr⁻P e (pl F) = pl (λ n → tr⁻P e (F n))
tr⁻P e (pi ac f) = pi ac (λ x → tr⁻P e (f x))
tr⁻P e (pŝ c₀ t g) = pŝ c₀ (tr⁻P e t) (λ η d → tr⁻P e (g η d))
tr⁻P e (pĉ c₀ z zg o₀ o) = pĉ c₀ z zg (tr⁻P e o₀) (λ η d → tr⁻P e (o η d))
tr⁻P e (pclo t g) = pclo (tr⁻P e t) (λ η → tr⁻P e (g η))
tr⁻P e (pcl t g) = pcl (tr⁻P e t) (λ η → tr⁻P e (g η))
tr⁻P e (pwk le le′ t) = pwk le le′ (tr⁻P e t)
tr⁻P e (pΩ↓ fe ac h) = pΩ↓ fe ac (λ ξ z → tr⁻P e (h ξ z))
tr⁻P e (pΩ fe fc q h) = pΩ fe fc (ltP (res⁻P q e)) (λ ξ ζ z → tr⁻P e (h ξ ζ (intoV (<→◃ q) (backP (res⁻P q e) (outV (<→◃ (ltP (res⁻P q e))) z)))))

resP zero      (s≅ e) = restrP e zero (tr⁻P e)
resP (suc q)   (s≅ e) = restrP (eqP (resP q e)) (suc (ltP (resP q e))) (backP (resP q e))
resP (lim n q) (l≅ h) = restrP (eqP (resP q (h n))) (lim n (ltP (resP q (h n)))) (backP (resP q (h n)))

res⁻P zero      (s≅ e) = restrP (≅ᴵ-sym e) zero (trP e)
res⁻P (suc q)   (s≅ e) = restrP (eqP (res⁻P q e)) (suc (ltP (res⁻P q e))) (backP (res⁻P q e))
res⁻P (lim n q) (l≅ h) = restrP (eqP (res⁻P q (h n))) (lim n (ltP (res⁻P q (h n)))) (backP (res⁻P q (h n)))
```

## §3 向上一层的嵌入

`ι↓`: `O k` 的字面节点 $i<k$ 变成高度 1 的节点, 证据是地板 `flo k`. 它不碰 `oclo`: 那是高度 0 的, 只读 $\varphi$. 走到 `omk` (`O` 里 $\dot\Omega$ 下降一层的记号) 时地板收紧到下一层, 与 `Ordˢ` 的 `up` 同形: 这就是 `noW` 的修正的第二半 (见 [ScafLadder](ScafLadder.lagda.md)).

```agda
ι↓ : ∀ {k α φ} → O k φ → P α φ (flo k)
ι↓ o0 = p0
ι↓ (os a) = psu (ι↓ a)
ι↓ (ol F) = pl (λ n → ι↓ (F n))
ι↓ (oi ac f) = pi ac (λ x → ι↓ (f x))
ι↓ (oŝ c₀ t g) = pŝ c₀ (ι↓ t) (λ η e → ι↓ (g η e))
ι↓ (oĉ c₀ z zg o₀ o) = pĉ c₀ z zg (ι↓ o₀) (λ η e → ι↓ (o η e))
ι↓ (oclo t g) = pclo (ι↓ t) (λ η → ι↓ (g η))
ι↓ (owk le t) = pwk le (λ e → e) (ι↓ t)
ι↓ {k = k} (oΩ fe r h) = pΩ↓ fe (λ e → cvFlo k e r) (λ ξ z → ι↓ (h ξ (intoU (<→◃ r) z)))
ι↓ {k = suc a} (omk zero z x) = pwk (λ e → e) (λ e → toFlo a (λ q → e (suc q))) (ι↓ z)
ι↓ {k = lim f s} (omk (self n) z x) = pwk (λ e → e) (λ e → toFlo (f n) (λ q → e (lim n q))) (ι↓ z)
```

## §4 $\Omega_{\Omega\cdot2+\alpha}$

```agda
Ω̇ᴾ : ∀ α → P α Fl Fl
Ω̇ᴾ zero = pcl {χ = fz} (pwk (λ e → e) proj₂ (ι↓ (Ω̇ (suc zero)))) (λ η → pwk (λ e → e) (λ e → toFlo η (λ q → proj₂ e (suc q))) (ι↓ (Ω̇ η)))
Ω̇ᴾ (suc α) = pΩ (λ e → e) (λ e → e) zero (λ ξ ζ z → pwk proj₁ proj₁ (ι zero z))
Ω̇ᴾ (lim f s) = pl (λ n → ι (self n) (Ω̇ᴾ (f n)))
```

## §5 折叠

三个折叠.

- `ψᵖ`: 目标在高度 2, 字面的 $t<\alpha$. 与 `ψᵒ` 同形, 高度 1 的节点与闭包都穿过.
- `Ψ`: 目标在高度 1, $\Omega+t$. **输出在已有的 `O t`.** 世界 $\ell$ 是参数. `pcl` 落成 `oŝ`: 界是目标与 $\chi$ 的上确界, 分支在新世界里求值. 节点 $\Omega+k$ 与目标在同一个 $\ell$ 之下比较, `<ᴵ-dec`. 高度 2 的节点总在目标之上, 走链, 链在 `P k` 里.
- `ψ̄ᴾ`: 目标可数. 高度 1 的世界是参数, 高度 0 留给 `Run`. `pcl` 的界**只**读 $\chi$: 分支里的节点都在 $\Omega$ 之上, 不与可数目标比较, 所以界不提目标 (与 `cloᵗ` 的 $h\ge1$ 行同理).

```agda
repᵖ : ∀ {c φ χ} → P c φ χ → ℕ → P c φ χ
repᵖ x zero          = p0
repᵖ x (suc zero)    = x
repᵖ x (suc (suc m)) = pwk (λ e → e , e) (λ e → e , e) (repᵖ x (suc m) ⊞ x)

chainᵖ : ∀ {k φ χ} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (∀ {ℓ} → Ev ℓ χ → Ev ℓ Fl) → (P k φ χ → P k φ χ) → ℕ → P k φ χ
chainᵖ {k} fe fc f zero    = pwk fe fc (Ω̇ᴾ k)
chainᵖ fe fc f (suc n) = f (chainᵖ fe fc f n)

ψᵖ : ∀ {α t} → t <ᴵ α → ∀ {φ χ} → P α φ χ → P t (Fl ⊔ φ) (Fl ⊔ χ)
ψᵖ {t = t} q p0 = pwk proj₁ proj₁ (Ω̇ᴾ t)
ψᵖ q (psu a) = pl (repᵖ (ψᵖ q a))
ψᵖ q (pl F) = pl (λ n → ψᵖ q (F n))
ψᵖ q (pi ac f) = pi (λ e → ac (proj₂ e)) (λ x → ψᵖ q (f x))
ψᵖ q (pŝ c₀ t g) = pŝ c₀ (ψᵖ q t) (λ η e → ψᵖ q (g η e))
ψᵖ q (pĉ c₀ z zg o₀ o) = pĉ c₀ z zg (ψᵖ q o₀) (λ η e → ψᵖ q (o η e))
ψᵖ q (pclo t g) = pwk asl (λ e → e) (pclo (pwk asr (λ e → e) (ψᵖ q t)) (λ η → pwk asr (λ e → e) (ψᵖ q (g η))))
ψᵖ q (pcl t g) = pwk (λ e → e) asl (pcl (pwk (λ e → e) asr (ψᵖ q t)) (λ η → pwk (λ e → e) asr (ψᵖ q (g η))))
ψᵖ q (pwk le le′ x) = pwk (λ e → proj₁ e , le (proj₂ e)) (λ e → proj₁ e , le′ (proj₂ e)) (ψᵖ q x)
ψᵖ q (pΩ↓ fe ac h) = pΩ↓ (λ e → proj₁ e) (λ e → ac (proj₂ e)) (λ ξ z → pwk swp (λ e → e) (ψᵖ q (h ξ z)))
ψᵖ q {φ} {χ} (pΩ fe fc r h) with <ᴵ-dec r q
... | injᵃ (via e s) =
  pΩ proj₁ proj₁ s (λ ξ ζ y → pwk swp swp (ψᵖ q (h ξ ζ (intoV (<→◃ r) (tr⁻P e (outV (<→◃ s) y))))))
... | injᵇ _ =
  pl (λ n → pwk dupr2 dupr2 (ψᵖ q (h (Fl ⊔ φ) (Fl ⊔ χ) (intoV (<→◃ r) (chainᵖ proj₁ proj₁ (λ z → pwk dupr2 dupr2 (ψᵖ r (h (Fl ⊔ φ) (Fl ⊔ χ) (intoV (<→◃ r) z)))) n)))))
... | injᶜ _ =
  pl (λ n → pwk dupr2 dupr2 (ψᵖ q (h (Fl ⊔ φ) (Fl ⊔ χ) (intoV (<→◃ r) (chainᵖ proj₁ proj₁ (λ z → pwk dupr2 dupr2 (ψᵖ r (h (Fl ⊔ φ) (Fl ⊔ χ) (intoV (<→◃ r) z)))) n)))))

-- 目标在高度 1
Ψ : ∀ {c φ χ t ℓ} → Ev ℓ χ → t <ᴵ ℓ → P c φ χ → O t (Fl ⊔ φ)
Ψ {t = t} e p p0 = owk proj₁ (Ω̇ t)
Ψ e p (psu a) = ol (repᵒ (Ψ e p a))
Ψ e p (pl F) = ol (λ n → Ψ e p (F n))
Ψ e p (pi ac f) = oi (λ u → ac (proj₂ u)) (λ x → Ψ e p (f x))
Ψ e p (pŝ c₀ x g) = oŝ c₀ (Ψ e p x) (λ η d → Ψ e p (g η d))
Ψ e p (pĉ c₀ z zg o₀ o) = oĉ c₀ z zg (Ψ e p o₀) (λ η d → Ψ e p (o η d))
Ψ e p (pclo x g) = owk asl (oclo (owk asr (Ψ e p x)) (λ η → owk asr (Ψ e p (g η))))
Ψ {φ = φ} {χ = χ ⊔ fk zero} {t = t} {ℓ = ℓ} e p (pcl x g) =
  oŝ (Bd B) (Ψ e p x)
     (λ η d → Ψ {ℓ = Mlev (Fc B) (suc η) (FB B d)} (liftEv χ (λ q → lim 0 q) (proj₁ (evF B)) , (λ {_} q → lim 1 q)) (lim 0 (iF B)) (g η))
  where B = bound (χ ⊔ fk zero) e p
Ψ e p (pwk le le′ x) = owk (λ u → proj₁ u , le (proj₂ u)) (Ψ (le′ e) p x)
Ψ {φ = φ} {χ = χ} e p (pΩ↓ {k = k} fe ac h) with <ᴵ-dec (ac e) p
... | injᵃ (via d s) = oΩ proj₁ s (λ ξ y → owk swp (Ψ e p (h ξ (tr⁻O d (outU (<→◃ s) y)))))
... | injᵇ _ = ol (λ n → owk dupr2 (Ψ e p (h (Fl ⊔ φ) (chainᵒ proj₁ (λ z → owk dupr2 (Ψ e (ac e) (h (Fl ⊔ φ) z))) n))))
... | injᶜ _ = ol (λ n → owk dupr2 (Ψ e p (h (Fl ⊔ φ) (chainᵒ proj₁ (λ z → owk dupr2 (Ψ e (ac e) (h (Fl ⊔ φ) z))) n))))
Ψ {φ = φ} {χ = χ} e p (pΩ fe fc r h) =
  ol (λ n → owk dupr2 (Ψ (e , e) p (h (Fl ⊔ φ) χ (intoV (<→◃ r) (chainᵖ proj₁ fc (λ z → pwk dupr2 (λ u → fc u , (u , u)) (ψᵖ r (h (Fl ⊔ φ) χ (intoV (<→◃ r) z)))) n)))))

-- 目标可数
ψ̄ᴾ : ∀ {c φ χ ℓ₂} → Ev ℓ₂ χ → zero <ᴵ ℓ₂ → P c φ χ → Run φ
ψ̄ᴾ e z p0 = wk 0 (λ _ → tt) ∅ᴿ
ψ̄ᴾ e z (psu a) = sucRun (ψ̄ᴾ e z a)
ψ̄ᴾ e z (pl F) = limA 0 (λ n → ψ̄ᴾ e z (F n))
ψ̄ᴾ e z (pi ac f) = limᵢA 0 ac (λ x → ψ̄ᴾ e z (f x))
ψ̄ᴾ e z (pŝ c₀ t g) = ŝA 0 c₀ (ψ̄ᴾ e z t) (λ η d → ψ̄ᴾ e z (g η d))
ψ̄ᴾ e z (pĉ c₀ t₀ zg o₀ o) = ĉA 0 c₀ t₀ zg (ψ̄ᴾ e z o₀) (λ η d → ψ̄ᴾ e z (o η d))
ψ̄ᴾ e z (pclo t g) = cloA 0 (ψ̄ᴾ e z t) (λ η → ψ̄ᴾ e z (g η))
ψ̄ᴾ {χ = χ ⊔ fk zero} e z (pcl t g) =
  ŝA 0 (Bd B) (ψ̄ᴾ e z t)
     (λ η d → ψ̄ᴾ {ℓ₂ = Mlev (Fc B) (suc η) (FB B d)} (liftEv χ (λ q → lim 0 q) (proj₁ (evF B)) , (λ {_} q → lim 1 q)) (lim 0 (iF B)) (g η))
  where B = bound (χ ⊔ fk zero) e z
ψ̄ᴾ e z (pwk le le′ x) = wk 0 le (ψ̄ᴾ (le′ e) z x)
ψ̄ᴾ {φ = φ} e z (pΩ↓ {k = k} fe ac h) =
  limA 0 (λ n → wk 0 (λ v → v , v)
                (ψ̄ᴾ e z (h φ (chainᵒ fe (λ y → owk (λ v → fe v , (v , v)) (Ψ e (ac e) (h φ y))) n))))
ψ̄ᴾ {φ = φ} {χ = χ} e z (pΩ fe fc r h) =
  limA 0 (λ n → wk 0 (λ v → v , v)
                (ψ̄ᴾ (e , e) z (h φ χ (intoV (<→◃ r) (chainᵖ fe fc (λ y → pwk (λ v → fe v , (v , v)) (λ v → fc v , (v , v)) (ψᵖ r (h φ χ (intoV (<→◃ r) y)))) n)))))

-- ψ₀(Ω_{Ω·2+α}). 高度 1 的世界取 1.
ev₂ : Ev (suc zero) Fl
ev₂ = tt , (λ q → q)

Tᴾ : ∀ α → Run Fl
Tᴾ α = ψ̄ᴾ ev₂ zero (Ω̇ᴾ α)
```
