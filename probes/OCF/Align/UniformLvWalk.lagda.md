# 不要证书的走树: 链点的保形近似

> 不含记号. 结论写在 [UniformLv](UniformLv.lagda.md). 这是测试工具, 不是定义的一部分.
>
> 闭包的 $n\ge1$ 孩子要一个层号 $\eta$, 真值是链点, 要证书. 这里造一个**保形近似**: `apx⁺` 把符号树读成 `Ordᴵ`, 极限 $\lim f$ 读成部分和 $\sum_{m\le n}f(m)$, 所以步进证据是字面的. 孩子的头一般相同, 但部分和有左边的噪声 ($\omega[1]$ 读成 $2$ 不是 $1$), 所以走进近似层号的内部之后, 树与记号可能错位: 这样的不一致**不算发现**. 这是有限测试, 不是证明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformLvWalk where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ)
```

## §1 加法与部分和

```agda
infixl 6 _+ᶜ_
_+ᶜ_ : Ordᴵ → Ordᴵ → Ordᴵ
+ᶜ-mono : ∀ a {b c} → b ⊑ᴵ c → (a +ᶜ b) ⊑ᴵ (a +ᶜ c)
+ᶜ-lt : ∀ a {b c} → b <ᴵ c → (a +ᶜ b) <ᴵ (a +ᶜ c)
+ᶜ-≅ : ∀ a {b c} → b ≅ᴵ c → (a +ᶜ b) ≅ᴵ (a +ᶜ c)
+ᶜ-up : ∀ a c → a ⊑ᴵ (a +ᶜ c)

a +ᶜ zero    = a
a +ᶜ suc b   = suc (a +ᶜ b)
a +ᶜ lim f s = lim (λ n → a +ᶜ f n) (λ n → +ᶜ-mono a (s n))

+ᶜ-lt a zero      = zero
+ᶜ-lt a (suc q)   = suc (+ᶜ-lt a q)
+ᶜ-lt a (lim n q) = lim n (+ᶜ-lt a q)

+ᶜ-≅ a z≅     = ≅ᴵ-refl a
+ᶜ-≅ a (s≅ e) = s≅ (+ᶜ-≅ a e)
+ᶜ-≅ a (l≅ h) = l≅ (λ n → +ᶜ-≅ a (h n))

+ᶜ-mono a {c = c} z⊑ = +ᶜ-up a c
+ᶜ-mono a (s⊑ e q) = s⊑ (+ᶜ-≅ a e) (+ᶜ-lt a q)
+ᶜ-mono a (l⊑ h) = l⊑ (λ n → +ᶜ-mono a (h n))

+ᶜ-up a zero      = ⊑ᴵ-refl
+ᶜ-up a (suc c)   = ⊑ᴵ-trans (+ᶜ-up a c) (Sim→⊑ᴵ suc)
+ᶜ-up a (lim f s) = ⊑ᴵ-trans (+ᶜ-up a (f 0)) (Sim→⊑ᴵ (λ q → lim 0 q))

sums : (ℕ → Ordᴵ) → ℕ → Ordᴵ
sums a zero    = a 0
sums a (suc n) = sums a n +ᶜ a (suc n)

cum : (ℕ → Ordᴵ) → Ordᴵ
cum a = lim (sums a) (λ n → +ᶜ-up (sums a n) (a (suc n)))
```

## §2 试造域证据

只认后继链: $c=\mathrm{suc}\,a$ 时在 $\eta$ 的字面前驱里找一个与 $a$ 字面相同的. 极限的 $c$ 要 $\forall n$, 不试, 答 `nothing`.

```agda
eqI : (a b : Ordᴵ) → Maybe (a ≅ᴵ b)
eqI zero    zero    = just z≅
eqI (suc a) (suc b) with eqI a b
... | just e  = just (s≅ e)
... | nothing = nothing
eqI _ _ = nothing

find : ℕ → (a η : Ordᴵ) → Maybe (Σ Ordᴵ λ a′ → (a ≅ᴵ a′) × (a′ <ᴵ η))
findL : ℕ → ℕ → (a : Ordᴵ) → ∀ {f s} → Maybe (Σ Ordᴵ λ a′ → (a ≅ᴵ a′) × (a′ <ᴵ lim f s))
find fuel a zero = nothing
find fuel a (suc b) with eqI a b
... | just e = just (b , e , zero)
... | nothing with find fuel a b
...   | just (a′ , e , q) = just (a′ , e , suc q)
...   | nothing = nothing
find zero a (lim f s) = nothing
find (suc fuel) a (lim f s) = findL fuel fuel a {f} {s}
findL zero fuel a {f} {s} with find fuel a (f 0)
... | just (a′ , e , q) = just (a′ , e , lim 0 q)
... | nothing = nothing
findL (suc k) fuel a {f} {s} with findL k fuel a {f} {s}
... | just r = just r
... | nothing with find fuel a (f (suc k))
...   | just (a′ , e , q) = just (a′ , e , lim (suc k) q)
...   | nothing = nothing

dom : ℕ → (c η : Ordᴵ) → Maybe (c ⊑ᴵ η)
dom fuel zero η = just z⊑
dom fuel (suc a) η with find fuel a η
... | just (a′ , e , q) = just (s⊑ e q)
... | nothing = nothing
dom fuel (lim f s) η = nothing
```

## §3 孩子

```agda
data Kid : Set where
  ok   : Ordˢ zero → Kid
  stop : Kid

outs : Ordᴵ → (ℕ → Ordᴵ) → ℕ → Ordᴵ
outs o₀ o zero    = o₀
outs o₀ o (suc n) = o n
```

## §4 不看域证据的走法

`apx⁺`, `kid⁺`: 链点取 $x$, 造得出域证据就用; 造不出就取 $c+x$, 这样 $c\sqsubseteq c+x$ 是定理, 而孩子的头不变 ($x\ne0$ 时). 这个走法只看种类; 所以它测的是**比较的回答与节点的形状**, 不测闭包的界. 界的义务在 [UniformLvNeg](UniformLvNeg.lagda.md).

```agda
lvl : (c x : Ordᴵ) → Σ Ordᴵ λ η → c ⊑ᴵ η
lvl c x with dom 3 c x
... | just e  = x , e
... | nothing = c +ᶜ x , +ᶜ-up c x

chain⁺ : (Z → Ordᴵ) → (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → ℕ → Ordᴵ
chain⁺ rd c t₀ g zero    = rd t₀
chain⁺ rd c t₀ g (suc n) = rd (g (proj₁ (lvl c (chain⁺ rd c t₀ g n))) (proj₂ (lvl c (chain⁺ rd c t₀ g n))))

apx⁺ : ℕ → Z → Ordᴵ
apx⁺ zero x = suc zero
apx⁺ (suc d) Z.zero = zero
apx⁺ (suc d) (Z.suc x) = suc (apx⁺ d x)
apx⁺ (suc d) (Z.lim f) = cum (λ n → apx⁺ d (f n))
apx⁺ (suc d) (ĉᴸ c t₀ g o₀ o) = cum (outs (apx⁺ d o₀) (λ n → apx⁺ d (o (proj₁ (lvl c (chain⁺ (apx⁺ d) c t₀ g n))) (proj₂ (lvl c (chain⁺ (apx⁺ d) c t₀ g n))))))

kid⁺ : ℕ → ℕ → Ordˢ zero → Kid
kid⁺ d n (Ord₊ˢ.lim f) = ok (f n)
kid⁺ d zero (Ord₊ˢ.ŝ c t g) = ok t
kid⁺ d (suc n) (Ord₊ˢ.ŝ c t g) = ok (g _ (proj₂ (lvl c (chain⁺ (apx⁺ d) c (toZ t) (λ η e → toZ (g η e)) n))))
kid⁺ d zero (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = ok o₀
kid⁺ d (suc n) (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = ok (o _ (proj₂ (lvl c (chain⁺ (apx⁺ d) c t₀ g n))))
kid⁺ d n _ = stop
```
