# YiChainNeg：`ChainP` 没有否定可写，它在 LEM 下成立

**验收文件，档位：编译定理与条件定理。** `lem→chainP : LEM → ChainP`，并对一切 `n ≤ m` 给出 `D.γ n ≼ᵖ read (co (pts m))` (`tri→all`)；所以 `ChainP` 及其 n = 1 情形的否定都推出 `¬ LEM` (`no-negP`, `no-N1`, `no-N1⁺`)。m = 0、n ≥ 1 的否定是定理 (`neg₀ⁿ`，值的原因)。
不否定什么：不说 `ChainP` 可构造地证；"Agda 与 LEM 相容，故 `¬ LEM` 不可证" 是元定理 (判断)。§3：`ChainP` 只要参照与链点各自前驱对上的局部三歧 (`triOn→chainP`)，n = 1 只要一处 (`n1-from`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiChainNegLEM where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiLeanTw3
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read; plus≽)
open import OCF.Lean.YiLeanValFin using (ChainP; module FromVM; chain-cum; HS-read; lower-read)
import OCF.Align.Level as L
open L using (Ordᶜ)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-+ʳ; ≅→≼; ⊑→≼; two≼; s≼s⁻; ≼lim⁻)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiVmConExact using (_≼ˣ_; _≼ᵖ_; zˣ; sˣ; wˣ; ≼lˣ; lˣ; Tri; tri→cplˣ; tri→vm; ˣ→ᵖ; ᵖ→≼; irr; VMᵖ)
```

## 1 LEM 推出 `Tri`

`lt`, `le`：经典的全序，`¬ (b ≼ a)` 给 `a` 严格在 `b` 之下，`¬ (suc a ≼ b)` 给 `b ≼ a`。两者互递归 (参数交换，靠调用图的复合停机)。

```agda
LEM : Set₁
LEM = ∀ (P : Set) → P ⊎ ¬ P

lt : LEM → ∀ (a b : Ordᶜ L.zero) → ¬ (b ≼ a) → L.suc a ≼ b
le : LEM → ∀ (a b : Ordᶜ L.zero) → ¬ (L.suc a ≼ b) → b ≼ a
lt lem a L.zero nb = ⊥-elim (nb z≼)
lt lem a (L.suc b) nb = s≼s (le lem b a nb)
lt lem a (L.lim g) nb with lem (Σ ℕ λ n → L.suc a ≼ g n)
... | inj₁ (n , q) = ≼l n q
... | inj₂ nq = ⊥-elim (nb (l≼ (λ n → le lem a (g n) (λ q → nq (n , q)))))
lt lem a (L.limᵢ () f) nb
lt lem a (L.up () x) nb
le lem a L.zero ns = z≼
le lem a (L.suc b) ns = lt lem b a (λ q → ns (s≼s q))
le lem a (L.lim f) ns = l≼ (λ n → le lem a (f n) (λ q → ns (≼l n q)))
le lem a (L.limᵢ () f) ns
le lem a (L.up () x) ns

lem→tri : LEM → Tri
lem→tri lem a b _ with lem (b ≼ a)
... | inj₁ q = inj₁ q
... | inj₂ nq = inj₂ (lt lem a b nq)
```

## 2 `ChainP` 在 LEM 下成立；否定都推出 `¬ LEM`

链点读回的值随下标不降 (`pt-mono`)；`Tri` 给 `VMᴸ` (`tri→vm`)，于是有值的链 `FromVM.chainV`，再由 `tri→cplˣ` 进 `≼ˣ`。

```agda
pt-step : ∀ n → read (co (pts n)) ≼ read (co (pts (suc n)))
pt-step n = ≼-trans (≼-+ʳ (read (co (pts n))) (read (obs (pts n)))) (≅→≼ (L.≅-sym (chain-cum n)))

pt-mono : ∀ n k → read (co (pts n)) ≼ read (co (pts (k + n)))
pt-mono n zero = ≼-refl _
pt-mono n (suc k) = ≼-trans (pt-mono n k) (pt-step (k + n))

tri→all : Tri → ∀ n k → D.γ n ≼ˣ read (co (pts (k + n)))
tri→all t n k = tri→cplˣ t _ _ (≼-trans (FromVM.chainV (tri→vm t) n) (pt-mono n k))

tri→chainP : Tri → ChainP
tri→chainP t n = n , ˣ→ᵖ (tri→all t n 0)

lem→chainP : LEM → ChainP
lem→chainP lem = tri→chainP (lem→tri lem)

no-negP : ¬ ChainP → ¬ LEM
no-negP h lem = h (lem→chainP lem)

no-neg : ∀ n k → ¬ (D.γ n ≼ᵖ read (co (pts (k + n)))) → ¬ LEM
no-neg n k h lem = h (ˣ→ᵖ (tri→all (lem→tri lem) n k))

neg₀ : ¬ (D.γ 1 ≼ᵖ read (co (pts 0)))
neg₀ d = irr _ (≼-trans two≼ (ᵖ→≼ d))

γ-up : ∀ n → D.γ 1 ≼ D.γ (suc n)
γ-up zero = ≼-refl _
γ-up (suc n) = ≼-trans (γ-up n) (⊑→≼ (D.γ (suc n)) (D.diag-step (suc n)))

neg₀ⁿ : ∀ n → ¬ (D.γ (suc n) ≼ᵖ read (co (pts 0)))
neg₀ⁿ n d = irr _ (≼-trans two≼ (≼-trans (γ-up n) (ᵖ→≼ d)))

no-N1 : (∀ m → ¬ (D.γ 1 ≼ᵖ read (co (pts m)))) → ¬ LEM
no-N1 h = no-neg 1 0 (h 1)

no-N1⁺ : ∀ m → ¬ (D.γ 1 ≼ᵖ read (co (pts (suc m)))) → ¬ LEM
no-N1⁺ m h = no-neg 1 m (subst (λ j → ¬ (D.γ 1 ≼ᵖ read (co (pts j)))) (sym (+-comm m 1)) h)
```

## 3 只要前驱对上的局部三歧

`Sub x a`：`a` 由 `x` 经后继前驱与极限分支走到。`TriOn x y`：`Tri` 只对 `suc a` 在 `x` 里、`suc b` 在 `y` 里的对 (a, b)。`tri→cplˣ` 的递归只走这些对，所以局部三歧就够；
再沿链归纳，第 n 步的 `≼ᵖ` 经 `VMᵖ` 给第 n+1 步的值，不要 `VMᴸ`。

```agda
data Sub (x : Ordᶜ L.zero) : Ordᶜ L.zero → Set where
  here : Sub x x
  sub-s : ∀ {a} → Sub x (L.suc a) → Sub x a
  sub-l : ∀ {f} n → Sub x (L.lim f) → Sub x (f n)

TriOn : Ordᶜ L.zero → Ordᶜ L.zero → Set
TriOn x y = ∀ a b → Sub x (L.suc a) → Sub y (L.suc b) → a ≼ b → b ≼ a ⊎ L.suc a ≼ b

on-cplˣ : ∀ {X Y} → TriOn X Y → ∀ x y → Sub X x → Sub Y y → x ≼ y → x ≼ˣ y
on-cplˣ t L.zero y sx sy d = zˣ
on-cplˣ t (L.lim f) y sx sy d = lˣ (λ n → on-cplˣ t (f n) y (sub-l n sx) sy (≼-trans (≼l n (≼-refl (f n))) d))
on-cplˣ t (L.suc a) L.zero sx sy ()
on-cplˣ t (L.suc a) (L.suc b) sx sy d with t a b sx sy (s≼s⁻ d)
... | inj₁ e = sˣ (on-cplˣ t a b (sub-s sx) (sub-s sy) (s≼s⁻ d)) e
... | inj₂ e = wˣ (on-cplˣ t (L.suc a) b sx (sub-s sy) e)
on-cplˣ t (L.suc a) (L.lim g) sx sy d with ≼lim⁻ d
... | n , e = ≼lˣ n (on-cplˣ t (L.suc a) (g n) sx (sub-l n sy) e)
on-cplˣ t (L.suc a) (L.limᵢ () f) sx sy d
on-cplˣ t (L.suc a) (L.up () x) sx sy d
on-cplˣ t (L.limᵢ () f) y sx sy d
on-cplˣ t (L.up () x) y sx sy d

triOn→cplˣ : ∀ {x y} → TriOn x y → x ≼ y → x ≼ˣ y
triOn→cplˣ t d = on-cplˣ t _ _ here here d

module FromTriOn (t : ∀ n → TriOn (D.γ n) (read (co (pts n)))) where
  valᵗ : ∀ n → D.γ n ≼ read (co (pts n))
  inᵗ : ∀ n → D.γ n ≼ᵖ read (co (pts n))
  valᵗ zero = ≼-refl _
  valᵗ (suc n) = plus≽ (co (pts n)) (obs (pts n))
    (≼-trans (VMᵖ (D.γ n) (D.cert n) (read (co (pts n))) (HS-read (co (pts n)) (lw (pts n))) (inᵗ n))
      (lower-read (co (pts n)) (lw (pts n))))
  inᵗ n = ˣ→ᵖ (triOn→cplˣ (t n) (valᵗ n))

triOn→chainP : (∀ n → TriOn (D.γ n) (read (co (pts n)))) → ChainP
triOn→chainP t n = n , FromTriOn.inᵗ t n

val₁ : D.γ 1 ≼ read (co (pts 1))
val₁ = plus≽ (co (pts 0)) (obs (pts 0)) (lower-read (co (pts 0)) (lw (pts 0)))

n1-from : TriOn (D.γ 1) (read (co (pts 1))) → D.γ 1 ≼ᵖ read (co (pts 1))
n1-from t = ˣ→ᵖ (triOn→cplˣ t val₁)

lem→triOn : LEM → ∀ x y → TriOn x y
lem→triOn lem x y a b _ _ = lem→tri lem a b

sub1 : ∀ {c} → Sub (L.suc L.zero) c → (c ≡ L.suc L.zero) ⊎ (c ≡ L.zero)
sub1 here = inj₁ refl
sub1 (sub-s p) with sub1 p
... | inj₁ refl = inj₂ refl
... | inj₂ ()
sub1 (sub-l n p) with sub1 p
... | inj₁ ()
... | inj₂ ()

triOn₀ : TriOn (D.γ 0) (read (co (pts 0)))
triOn₀ a b sa sb d with sub1 sb
... | inj₁ refl = inj₁ z≼
... | inj₂ ()
```
