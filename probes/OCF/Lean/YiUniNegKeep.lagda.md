# YiUni 否定：保留结点的分支取各支 `top` 的像，不单调

**非验收文件。判决：编译定理，无前提。** 目标是 `tw 2` 自己、派发 `self` 时，若接口的 `Kb` 在每个合法下标上等于那一支 `top` 的像 (不累加)，与 `Kb-br` 矛盾 (`honest-keep→⊥`，对任意 `Uni` 与 `tw 2` 上的任意 `Bd`)。
具体的族：`tw 2` 实例去掉累加 `Kf` 后的 `Tv` 处处有定义，但不是 `Br` (`noacc-not-br`)。失败在下标 `top ⊑ suc top`：两支的像是位置不同的结点，下行只碰到 `top` 的后继。
有折叠 (只用 `top` 的两行)，没有值，不是壁垒定理的实例。接口 [YiUniIf](YiUniIf.lagda.md)；单调为什么是合法性逼出的见 [YiUniForced](YiUniForced.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUniNegKeep where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; ⌜_⌝; Br; self; succ)
open import OCF.Lean.YiNextTop using (lv)
open import OCF.Lean.YiUniIf using (Uni)
open import OCF.Lean.YiUniTw2 using (Tv)
```

## 1 下行碰不到另一个结点

`S`：由 `top` 经后继得到的树；`top` 的 ω 倍的各项都是。

```agda
p₀ s₂ s₂′ : Pre (tw 2)
p₀ = G.top , tt , inj₁ tt
s₂ = G.suc G.top , tt , inj₁ tt
s₂′ = G.suc G.top , tt , inj₂ (inj₁ tt)

idx : Raw (tw 2) → R
idx (G.lc (η , _) _) = η
idx _ = G.zero

top≢suc : _≡_ {A = R} G.top (G.suc G.top) → ⊥
top≢suc ()

data S : Raw (tw 2) → Set where
  st : S G.top
  ss : ∀ {b} → S b → S (G.suc b)

S-plus : ∀ b → S b → S (plus (tw 2) G.top b)
S-plus .G.top st = ss st
S-plus .(G.suc _) (ss s) = ss (S-plus _ s)

S-acc : ∀ n → S (acc (λ _ z → plus (tw 2) G.top z) G.top n)
S-acc zero = st
S-acc (suc n) = S-plus _ (S-acc n)

S-noCp : ∀ {p g b} → S b → Cp (tw 2) (G.lc p g) b → ⊥
S-noCp st (inj₁ ())
S-noCp st (inj₂ ())
S-noCp (ss s) (inj₁ ())
S-noCp (ss s) (inj₂ c) = S-noCp s c

cpR : ∀ {m a b b′} → b ≡ b′ → Cp m a b → Cp m a b′
cpR refl c = c

cpL : ∀ {m a a′ b} → a ≡ a′ → Cp m a b → Cp m a′ b
cpL refl c = c

no₃ : ∀ {g} → Cp (tw 2) (G.lc p₀ g) (succ (tw 2) G.top) → ⊥
no₃ (inj₁ ())
no₃ (inj₂ (n , c)) = S-noCp (S-acc n) c

no₂ : ∀ {g gC} → gC G.top ≡ succ (tw 2) G.top → Cp (tw 2) (G.lc p₀ g) (G.lc s₂′ gC) → ⊥
no₂ e (inj₁ q) = top≢suc (cong idx q)
no₂ e (inj₂ c) = no₃ (cpR e c)

no₁ : ∀ {g gB gC} → gB G.top ≡ G.lc s₂′ gC → gC G.top ≡ succ (tw 2) G.top →
  Cp (tw 2) (G.lc p₀ g) (G.lc s₂ gB) → ⊥
no₁ e e′ (inj₁ q) = top≢suc (cong idx q)
no₁ e e′ (inj₂ c) = no₂ e′ (cpR e c)
```

## 2 否定

```agda
Hon : (U : Uni) (V : Uni.Bd U (tw 2)) → ∀ η → Lgl zero η → Raw (tw 2)
Hon U V η l = Uni.Ψ U (tw 2) (Uni.bC U {k = zero} {g = ⌜_⌝} V η l) (λ r → self (tw 2) (η , l , r)) G.top

honest-keep→⊥ : (U : Uni) (V : Uni.Bd U (tw 2)) →
  (∀ η l → Uni.Kb U (tw 2) {k = zero} {g = ⌜_⌝} V (self (tw 2)) η ≡ Hon U V η l) → ⊥
honest-keep→⊥ U V hon = no₁ eB eC (cpL eA (cpR eB₀ mono))
  where
  open Uni U
  x = self (tw 2)
  Vt = bC {k = zero} {g = ⌜_⌝} V G.top tt
  Vs = bC {k = zero} {g = ⌜_⌝} V (G.suc G.top) tt
  mono = proj₂ (Kb-br (tw 2) {k = zero} {g = ⌜_⌝} V x) G.top (G.suc G.top) tt (inj₂ (inj₁ refl)) tt
  eA = trans (hon G.top tt) (top-rowˢ (tw 2) {k = zero} Vt (λ r → x (G.top , tt , r)))
  eB₀ = trans (hon (G.suc G.top) tt) (top-rowˢ (tw 2) {k = suc zero} Vs (λ r → x (G.suc G.top , tt , r)))
  eB = top-rowˢ (tw 2) {k = zero} (bS {k = suc zero} Vs) (λ r → x (G.suc G.top , tt , inj₂ r))
  eC = top-row⁰ (tw 2) (bS {k = zero} (bS {k = suc zero} Vs)) (λ r → x (G.suc G.top , tt , inj₂ (inj₂ r)))

noacc-not-br : Br (layer zero) (tw 2) (Tv (tw 2) lv (self (tw 2))) → ⊥
noacc-not-br b = no₁ refl refl (proj₂ b G.top (G.suc G.top) tt (inj₂ (inj₁ refl)) tt)
```
