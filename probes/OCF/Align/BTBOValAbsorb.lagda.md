# 吸收: `ordᴰ` 的放大有多大

> 接 [BTBOValBase](BTBOValBase.lagda.md). 问题: `ordᴰ` 把树的每个 `lim` 换成累加 (`cumsum`), 值变大 (`ordᴰ-≥`, `overshoot`: $\omega+\omega\mapsto\omega^2$). 放大是否被下一个闭包点吸收?
>
> 结论:
>
> 1. **对严格的树, 吸收在值上成立.** `St x` (`lim` 的相邻项值严格递增, 遗传) 时 `ordᴰ x` $\preccurlyeq\psi^0(x+1)$ (`absorb`). 对极限树还有 `ordᴰ x` $\preccurlyeq\psi^0(x)$ (`absorb-lim`). 这是定理.
> 2. **没有严格性就不成立.** `ordᴰ` 不是值的函数: $\lim(\omega,\omega,\dots)$ 与 $\omega$ 值相等, 都带 `HS` 证书, 累加后一个是 $\omega^2$ 量级, 一个是 $\omega$ (`ordᴰ-not-cong`). 所以 `HS` 不够, 要 `St`.
> 3. **没有证的:** src 的 $x_k$ 是否 `St`. 有限比较器在预算内没有给出结论 (见 [BTBOValTest](BTBOValTest.lagda.md) §4), 只有纸面判断. 这是吸收用到对角线上的一个前提.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOValAbsorb where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum; cumsum-mono) renaming (_+_ to _+ᴰ_)
open S using (iter; ordᴰ; zero; suc; lim; limᵢ)
open import OCF.Align.Level
open import OCF.Align.BTBOValBase using (tr₀; fd; fd-+; ordᴰ-≥; ≼-+ᴰ)
open import OCF.Align.BTBOValMain using (g-nat; cum-K; K; n≤K; natᴰ)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼i; ≼u; ≼-refl; ≼-trans; ≼-suc; +-mono; ψ⁰-mono⁰; 1≼ψ⁰; s≼s⁻; s≼0; ≼lim⁻)
```

## §1 严格

`St` 在第 0 层上. 步进是值的 `suc (f n) ≼ f (suc n)`, 比 `HS` 的 $\sqsubseteq$ 弱在只看值, 强在严格.

```agda
data St : Ordᶜ zero → Set where
  stz : St zero
  sts : ∀ {a} → St a → St (suc a)
  stl : ∀ {f : ℕ → Ordᶜ zero} → (∀ n → St (f n)) → (∀ n → suc (f n) ≼ f (suc n)) → St (lim f)

st-s⁻ : ∀ {a} → St (suc a) → St a
st-s⁻ (sts d) = d

st-l₁ : ∀ {f : ℕ → Ordᶜ zero} → St (lim f) → ∀ n → St (f n)
st-l₁ (stl h s) = h

st-l₂ : ∀ {f : ℕ → Ordᶜ zero} → St (lim f) → ∀ n → suc (f n) ≼ f (suc n)
st-l₂ (stl h s) = s
```

## §2 吸收定理

记 $P=\psi^0$, 在第 0 层上 $P(a+1)=P(a)\cdot\omega$ (基本列 $P(a)\cdot n$), 且单调 (`ψ⁰-mono⁰`). 关键计算: $U,V\preccurlyeq A=P(w)$, $A$ 非零, 则 $(U+V)+1\preccurlyeq A\cdot 3\preccurlyeq P(w+1)$.

```agda
P : Ordᶜ zero → Ordᶜ zero
P = ψ⁰

≼P-suc : ∀ w → P w ≼ P (suc w)
≼P-suc w = ≼l 1 (≼-refl (P w))

sA≼A+A : ∀ w → suc (P w) ≼ P w + P w
sA≼A+A w = +-mono (≼-refl (P w)) (1≼ψ⁰ w)

sum≼ : ∀ {w U V} → U ≼ P w → V ≼ P w → suc (U + V) ≼ P (suc w)
sum≼ {w} u v = ≼l 3 (≼-trans (s≼s (+-mono u v)) (+-mono (≼-refl (P w)) (sA≼A+A w)))

fd-+s : ∀ a v → fd (a +ᴰ B.suc v) ≼ suc (fd a + fd v)
fd-+s a v = s≼s (fd-+ a v)

absorb     : ∀ (x : S.Ord₀) → St (tr₀ x) → fd (ordᴰ x) ≼ P (suc (tr₀ x))
absorb-lim : ∀ (f : ℕ → S.Ord₀) → St (tr₀ (lim f)) → fd (ordᴰ (lim f)) ≼ P (tr₀ (lim f))
cum-C      : ∀ (f : ℕ → S.Ord₀) → St (tr₀ (lim f)) → ∀ n → fd (cumsum (ordᴰ ∘ f) n) ≼ P (suc (suc (tr₀ (f n))))

cum-C f st zero    = ≼-trans (absorb (f 0) (st-l₁ st 0)) (ψ⁰-mono⁰ (≼-suc (≼-refl (suc (tr₀ (f 0))))))
cum-C f st (suc n) = ≼-trans (fd-+s (cumsum (ordᴰ ∘ f) n) (ordᴰ (f (suc n))))
  (sum≼ (≼-trans (cum-C f st n) (ψ⁰-mono⁰ (s≼s (st-l₂ st n)))) (absorb (f (suc n)) (st-l₁ st (suc n))))

absorb-lim f st = l≼ (λ n → ≼l (suc (suc n)) (≼-trans (cum-C f st n)
  (ψ⁰-mono⁰ (≼-trans (s≼s (st-l₂ st n)) (st-l₂ st (suc n))))))

absorb zero        st = z≼
absorb (suc a)     st = ≼l 2 (≼-trans (s≼s (absorb a (st-s⁻ st))) (sA≼A+A (suc (tr₀ a))))
absorb (lim f)     st = ≼-trans (absorb-lim f st) (≼P-suc (tr₀ (lim f)))
absorb (limᵢ () f) st
```

**读法.** $x\preccurlyeq\mathrm{ordᴰ}\,x\preccurlyeq\psi^0(x+1)$ (`ordᴰ-≥`, `absorb`). 第 0 层上 $\psi^0(x)$ 大致是 $\omega^x$, 所以放大不超过一个 $\omega$-指数. 这就是 "累加改值在下一个 $\varepsilon$ 型闭包点被吸收" 在**值**上的精确形式: 对角线的项都是 $\varepsilon$ 型的不动点 (纸面), 所以 `ordᴰ` 不会越过下一项.

## §3 严格性不能去掉

$\omega$ 与 $\lim(\omega,\omega,\dots)$ 值相等, 都有 `HS` 证书, 而 `ordᴰ` 把后者放大到 $\omega$ 之上. 所以 `ordᴰ` 不尊重值, 上面的 `St` 不能换成 `HS`.

```agda
natᶜ-≤ : ∀ {m k} → m ≤ k → natᶜ m ≼ natᶜ k
natᶜ-≤ z≤n     = z≼
natᶜ-≤ (s≤s p) = s≼s (natᶜ-≤ p)

nat-irr : ∀ m → ¬ (natᶜ (suc m) ≼ natᶜ m)
nat-irr zero    = s≼0
nat-irr (suc m) p = nat-irr m (s≼s⁻ p)

lim-≼⁻ : ∀ {f : ℕ → Ordᶜ zero} {b : Ordᶜ zero} → lim f ≼ b → ∀ n → f n ≼ b
lim-≼⁻ (l≼ h)   n = h n
lim-≼⁻ (≼l k p) n = ≼l k (lim-≼⁻ p n)
lim-≼⁻ (≼i {p = ()} x ex p) n
lim-≼⁻ (≼u {r = ()} p) n

fd-nat : ∀ n → fd (natᴰ n) ≡ natᶜ n
fd-nat zero    = refl
fd-nat (suc n) = cong suc (fd-nat n)

module NotCong (g : ℕ → S.Ord₀) (g0 : g 0 ≡ zero) (gs : ∀ n → g (suc n) ≡ suc (g n)) where
  w : S.Ord₀
  w = lim g

  d : S.Ord₀
  d = lim (λ _ → w)

  val : tr₀ d ≈ᵛ tr₀ w
  val = l≼ (λ _ → ≼-refl (tr₀ w)) , ≼l 0 (≼-refl (tr₀ w))

  HS-w : HS (tr₀ w)
  HS-w = hl (λ n → subst HS (sym (g-nat g g0 gs n)) (natᶜ-HS n))
            (λ n h → subst (_ ≺_) (sym (cong tr₀ (gs n))) (≺s h))

  HS-d : HS (tr₀ d)
  HS-d = hl (λ _ → HS-w) (λ _ h → h)

  O : Ordᴰ
  O = ordᴰ w

  fdO-big : ∀ m → ¬ (fd O ≼ natᶜ m)
  fdO-big m p = nat-irr m (≼-trans (natᶜ-≤ (n≤K (suc m)))
    (subst (λ u → u ≼ natᶜ m) (trans (cong fd (cum-K g g0 gs (suc m))) (fd-nat (K (suc m)))) (lim-≼⁻ p (suc m))))

  not-cong : ¬ (fd (ordᴰ d) ≼ fd O)
  not-cong p with lim-≼⁻ p 1
  ... | q with ≼lim⁻ q
  ... | k , r = fdO-big (K k)
    (subst (λ u → fd O ≼ u) (trans (cong fd (cum-K g g0 gs k)) (fd-nat (K k)))
           (≼-trans (≼-suc (≼-+ᴰ O O)) r′))
    where
    r′ : suc (fd (O +ᴰ O)) ≼ fd (cumsum (ordᴰ ∘ g) k)
    r′ = r

seq₀ : S.Ord₀ → ℕ → S.Ord₀
seq₀ (lim f) = f
seq₀ _       = λ _ → zero

module NC = NotCong (seq₀ S.ω) refl (λ _ → refl)

_ : NC.w ≡ S.ω
_ = refl

ordᴰ-not-cong : (tr₀ NC.d ≈ᵛ tr₀ S.ω) × HS (tr₀ NC.d) × HS (tr₀ S.ω) × ¬ (fd (ordᴰ NC.d) ≼ fd (ordᴰ S.ω))
ordᴰ-not-cong = NC.val , NC.HS-d , NC.HS-w , NC.not-cong
```
