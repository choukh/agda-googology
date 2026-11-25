# 累加的读回: 层号的值

> 验收文件. 编译定理, 无前提: 由第 0 层的树读出的层号没有 Ω 结点 (`Cnt-↑`, `Cnt-↑ᶜ`), 按值读成参照框架的第 0 层树 `vL`; `v↑ c ≼ v↑ᶜ c` 对一切树 (`up≼upᶜ`); ω+ω 处 `suc (v↑ ωω) ≼ v↑ᶜ ωω` (`ωω-strict`), 所以 `¬ (v↑ᶜ ωω ≼ v↑ ωω)` (`ωω-not≼`).
> 每个 `↑ᶜ c` 都与某个 `↑ c′` 互相 `≼` (`cof`); 塔第 1 项两族分支层号在值上互相共尾 (`tw1-cof`). "层号 tw 1 与 twᶜ 1 的上确界相同" 是由此得出的判断 (没有 Ω 层号的值函数).
> 不涉及折叠的值. 证明用到无关参数 (`Cnt` 的证明只在无关位置).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCumVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (iter)
open import OCF.Lean.YiCumBlock
open import OCF.Lean.YiFreshValRead using (T₀)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc)
open import OCF.Align.RR4MonoFragment using (irr)
```

## 可数的层号按值读回

```agda
Cnt : L → Set
Cnt zero     = ⊤
Cnt (suc a)  = Cnt a
Cnt (lim g)  = (n : ℕ) → Cnt (g n)
Cnt (Ωₗ k h) = ⊥

vL : (ℓ : L) → .(Cnt ℓ) → T₀
vL zero     _ = L.zero
vL (suc a)  h = L.suc (vL a h)
vL (lim g)  h = L.lim (λ n → vL (g n) (h n))
vL (Ωₗ k h) ()

Cnt⊕ : (a b : L) → Cnt a → Cnt b → Cnt (a ⊕ b)
Cnt⊕ a zero     ha hb = ha
Cnt⊕ a (suc b)  ha hb = Cnt⊕ a b ha hb
Cnt⊕ a (lim g)  ha hb = λ n → Cnt⊕ a (g n) ha (hb n)
Cnt⊕ a (Ωₗ k h) ha ()

Cnt-cum : (s : ℕ → L) → ((n : ℕ) → Cnt (s n)) → (n : ℕ) → Cnt (cumₗ s n)
Cnt-cum s h zero    = h zero
Cnt-cum s h (suc n) = Cnt⊕ (cumₗ s n) (s (suc n)) (Cnt-cum s h n) (h (suc n))

Cnt-↑ : (c : Tr zero) → Cnt (↑ zero c)
Cnt-↑ zero        = tt
Cnt-↑ (suc c)     = Cnt-↑ c
Cnt-↑ (lim f)     = λ n → Cnt-↑ (f n)
Cnt-↑ (Ω () _)
Cnt-↑ (up _ () _)

Cnt-↑ᶜ : (c : Tr zero) → Cnt (↑ᶜ zero c)
Cnt-↑ᶜ zero        = tt
Cnt-↑ᶜ (suc c)     = Cnt-↑ᶜ c
Cnt-↑ᶜ (lim f)     = Cnt-cum (λ n → ↑ᶜ zero (f n)) (λ n → Cnt-↑ᶜ (f n))
Cnt-↑ᶜ (Ω () _)
Cnt-↑ᶜ (up _ () _)

v↑ v↑ᶜ : Tr zero → T₀
v↑  c = vL (↑ zero c) (Cnt-↑ c)
v↑ᶜ c = vL (↑ᶜ zero c) (Cnt-↑ᶜ c)
```

## 累加不低于原读回

```agda
⊕≽ : (a b : L) .(ha : Cnt a) .(hb : Cnt b) → vL b hb ≼ vL (a ⊕ b) (Cnt⊕ a b ha hb)
⊕≽ a zero     ha hb = z≼
⊕≽ a (suc b)  ha hb = s≼s (⊕≽ a b ha hb)
⊕≽ a (lim g)  ha hb = l≼ (λ n → ≼l n (⊕≽ a (g n) ha (hb n)))
⊕≽ a (Ωₗ k h) ha ()

cum≽ : (s : ℕ → L) .(h : (n : ℕ) → Cnt (s n)) (n : ℕ) → vL (s n) (h n) ≼ vL (cumₗ s n) (Cnt-cum s h n)
cum≽ s h zero    = ≼-refl (vL (s zero) (h zero))
cum≽ s h (suc n) = ⊕≽ (cumₗ s n) (s (suc n)) (Cnt-cum s h n) (h (suc n))

up≼upᶜ : (c : Tr zero) → v↑ c ≼ v↑ᶜ c
up≼upᶜ zero        = z≼
up≼upᶜ (suc c)     = s≼s (up≼upᶜ c)
up≼upᶜ (lim f)     =
  l≼ (λ n → ≼l n (≼-trans (up≼upᶜ (f n)) (cum≽ (λ m → ↑ᶜ zero (f m)) (λ m → Cnt-↑ᶜ (f m)) n)))
up≼upᶜ (Ω () _)
up≼upᶜ (up _ () _)
```

## ω+ω 处: 原读回的后继也不超过累加的读回

`ωω = lim (ω, ω+1, …)`. 原读回的值是 ω·2 (每项 ω+n); 累加的第 1 项已是 (ω ⊕ ω) + 1, 每个 ω+n 都低于 ω ⊕ ω.

```agda
ω₀ ωω : Tr zero
ω₀ = lim (iter suc zero)
ωω = lim (iter suc ω₀)

sucs : ℕ → T₀ → T₀
sucs zero    y = y
sucs (suc n) y = L.suc (sucs n y)

sucs-mono : (n : ℕ) {y y′ : T₀} → y ≼ y′ → sucs n y ≼ sucs n y′
sucs-mono zero    p = p
sucs-mono (suc n) p = s≼s (sucs-mono n p)

up-sucs : (x : Tr zero) (n : ℕ) → v↑ (iter suc x n) ≼ sucs n (v↑ x)
up-sucs x zero    = ≼-refl (v↑ x)
up-sucs x (suc n) = s≼s (up-sucs x n)

⊕⊕≽ : (a b d : L) .(ha : Cnt a) .(hb : Cnt b) .(hd : Cnt d)
  → vL (a ⊕ b) (Cnt⊕ a b ha hb) ≼ vL (a ⊕ (b ⊕ d)) (Cnt⊕ a (b ⊕ d) ha (Cnt⊕ b d hb hd))
⊕⊕≽ a b zero     ha hb hd = ≼-refl (vL (a ⊕ b) (Cnt⊕ a b ha hb))
⊕⊕≽ a b (suc d)  ha hb hd = ≼-suc (⊕⊕≽ a b d ha hb hd)
⊕⊕≽ a b (lim g)  ha hb hd = ≼l 0 (⊕⊕≽ a b (g 0) ha hb (hd 0))
⊕⊕≽ a b (Ωₗ k h) ha hb ()

F : ℕ → L
F m = ↑ᶜ zero (iter suc zero m)

W : L
W = ↑ᶜ zero ω₀

hW : Cnt W
hW = Cnt-↑ᶜ ω₀

hF : (n : ℕ) → Cnt (F n)
hF n = Cnt-↑ᶜ (iter suc zero n)

W-sucs : (n : ℕ) → sucs n (vL W hW) ≼ vL (W ⊕ cumₗ F n) (Cnt⊕ W (cumₗ F n) hW (Cnt-cum F hF n))
W-sucs zero    = ≼-refl (vL W hW)
W-sucs (suc n) = s≼s (≼-trans (W-sucs n) (⊕⊕≽ W (cumₗ F n) (F n) hW (Cnt-cum F hF n) (hF n)))

ωω-strict : L.suc (v↑ ωω) ≼ v↑ᶜ ωω
ωω-strict = ≼l 1 (s≼s (l≼ (λ n → ≼l n
  (≼-trans (up-sucs ω₀ n) (≼-trans (sucs-mono n (up≼upᶜ ω₀)) (W-sucs n))))))

ωω-not≼ : ¬ (v↑ᶜ ωω ≼ v↑ ωω)
ωω-not≼ p = irr (v↑ ωω) (≼-trans ωω-strict p)
```

## 两族读回互相共尾

`↓` 把可数的层号读回第 0 层的树; 原读回把它读回同一个值 (`↓-≼`, `↓-≽`). 所以每个 `↑ᶜ c` 都与某个 `↑ c′` 值相同, 反方向是 `up≼upᶜ`.

```agda
↓ : (ℓ : L) → .(Cnt ℓ) → Tr zero
↓ zero     _ = zero
↓ (suc a)  h = suc (↓ a h)
↓ (lim g)  h = lim (λ n → ↓ (g n) (h n))
↓ (Ωₗ k h) ()

↓-≼ : (ℓ : L) .(h : Cnt ℓ) → vL ℓ h ≼ v↑ (↓ ℓ h)
↓-≼ zero     h = z≼
↓-≼ (suc a)  h = s≼s (↓-≼ a h)
↓-≼ (lim g)  h = l≼ (λ n → ≼l n (↓-≼ (g n) (h n)))
↓-≼ (Ωₗ k h) ()

↓-≽ : (ℓ : L) .(h : Cnt ℓ) → v↑ (↓ ℓ h) ≼ vL ℓ h
↓-≽ zero     h = z≼
↓-≽ (suc a)  h = s≼s (↓-≽ a h)
↓-≽ (lim g)  h = l≼ (λ n → ≼l n (↓-≽ (g n) (h n)))
↓-≽ (Ωₗ k h) ()

cof : (c : Tr zero) → Σ (Tr zero) λ c′ → (v↑ᶜ c ≼ v↑ c′) × (v↑ c′ ≼ v↑ᶜ c)
cof c = ↓ (↑ᶜ zero c) (Cnt-↑ᶜ c) , ↓-≼ (↑ᶜ zero c) (Cnt-↑ᶜ c) , ↓-≽ (↑ᶜ zero c) (Cnt-↑ᶜ c)
```

塔第 1 项的分支层号是 `zero ⊕ ↑ c` 与 `zero ⊕ ↑ᶜ c`; 左加 `zero` 不改值, 所以两族分支层号在值上互相共尾 (`tw1-cof`).

```agda
z⊕≼ : (b : L) .(h : Cnt b) → vL (zero ⊕ b) (Cnt⊕ zero b tt h) ≼ vL b h
z⊕≼ zero     h = z≼
z⊕≼ (suc b)  h = s≼s (z⊕≼ b h)
z⊕≼ (lim g)  h = l≼ (λ n → ≼l n (z⊕≼ (g n) (h n)))
z⊕≼ (Ωₗ k h) ()

z⊕≽ : (b : L) .(h : Cnt b) → vL b h ≼ vL (zero ⊕ b) (Cnt⊕ zero b tt h)
z⊕≽ zero     h = z≼
z⊕≽ (suc b)  h = s≼s (z⊕≽ b h)
z⊕≽ (lim g)  h = l≼ (λ n → ≼l n (z⊕≽ (g n) (h n)))
z⊕≽ (Ωₗ k h) ()

w₁ w₁ᶜ : Tr zero → T₀
w₁  c = vL (zero ⊕ ↑ zero c) (Cnt⊕ zero (↑ zero c) tt (Cnt-↑ c))
w₁ᶜ c = vL (zero ⊕ ↑ᶜ zero c) (Cnt⊕ zero (↑ᶜ zero c) tt (Cnt-↑ᶜ c))

tw1-cof : ((c : Tr zero) → w₁ c ≼ w₁ᶜ c)
        × ((c : Tr zero) → Σ (Tr zero) λ c′ → (w₁ᶜ c ≼ w₁ c′) × (w₁ c′ ≼ w₁ᶜ c))
tw1-cof =
  (λ c → ≼-trans (z⊕≼ (↑ zero c) (Cnt-↑ c)) (≼-trans (up≼upᶜ c) (z⊕≽ (↑ᶜ zero c) (Cnt-↑ᶜ c)))) ,
  (λ c → let (c′ , p , q) = cof c in
    c′ , ≼-trans (z⊕≼ (↑ᶜ zero c) (Cnt-↑ᶜ c)) (≼-trans p (z⊕≽ (↑ zero c′) (Cnt-↑ c′)))
       , ≼-trans (z⊕≼ (↑ zero c′) (Cnt-↑ c′)) (≼-trans q (z⊕≽ (↑ᶜ zero c) (Cnt-↑ᶜ c))))
```
