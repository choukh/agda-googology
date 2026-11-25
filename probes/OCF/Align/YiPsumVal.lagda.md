# YiPsumVal：部分和对值的影响 (目标第 0 层)

**判决 (编译定理，值序是 `YiRawNegNorm._≼_`)：折叠的部分和不降值 (`lim≼psumᵖ`)；各项满足吸收 `g n + g (n+1) ≼ g (n+1)` 时不升值 (`psum-flat`)。
`YiRawFold` 的闭项满足吸收：`closedᵐ k + closedᵐ (suc k) ≼ closedᵐ (suc k)` 对一切 `Plain` 且 `Legal` 的 `k` (`absorb-suc`)，所以在 ω 与 ω·2 上部分和与逐项极限互相 `≼`。
各支相同的极限层号 `lim (λ _ → zero)` (合法，一致，退化) 上部分和严格偏高 (`const-inflates`)，逐项的折叠在那里的闭项严格低于它 (`termwise-below-psum`)。** 只比了目标第 0 层的输出；保留模式下 `Raw ω` 里的那一处没有值序，没有比。
不否定部分和写法。逐项的折叠在 [YiPsumInst](YiPsumInst.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPsumVal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (R; _+ʳ_; self; Legal; iterate)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiIrrFbIf using (Pt; pt) renaming (at to atᵖ)
open import OCF.Align.YiLvIf using (Plain)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase using (fold; startᴸ; module ChainLegal)
open import OCF.Align.YiLvFoldFin using (fin; ω; ω-plain; ω-legal; fin-plain; fin-legal)
open import OCF.Align.YiRawIf using (base; dispatch)
open import OCF.Align.YiRawNegNorm
  using (_≼_; _≺_; s≼; l≼; ≺s; ≺l; ≼-lim; ≼-refl; ≼-suc; ≼-trans; ≺≼-trans; ≺-irrefl;
         add-right; add-monoˡ)
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiRawFold
open import OCF.Align.YiRawFoldInst
  using (closedᵐ; ω+; ω+-plain; ω+-legal; ω2; ω2-plain; ω2-legal)
open import OCF.Align.YiPsumInst using (closedᵗ; Domᵗ)
```

## 1 第 0 层：第一位置在值之下；折叠用的加法与 `_+ʳ_` 同值

`plus zero` 与 `_+ʳ_` 逐子句相同，是两个定义；极限之下的字面相等要函数外延，这里只用两个方向的 `≼`。

```agda
cp→≼ : ∀ {a} b → Cp zero a b → a ≼ b
dn→≼ : ∀ {a} b → Dn zero a b → a ≼ b
cp→≼ {a} b (inj₁ refl) = ≼-refl a
cp→≼ b (inj₂ p) = dn→≼ b p
dn→≼ (G.suc b) p = ≼-suc (cp→≼ b p)
dn→≼ (G.lim f) (n , p) = ≼-lim n (cp→≼ (f n) p)
dn→≼ (G.lc () c t g) p
dn→≼ (G.em () T) p

p≼ : ∀ x y → plus zero x y ≼ x +ʳ y
p≼ x G.zero = ≼-refl x
p≼ x (G.suc y) = s≼ (≺s (p≼ x y))
p≼ x (G.lim f) = l≼ (λ n → ≼-lim n (p≼ x (f n)))
p≼ x (G.lc () c t g)
p≼ x (G.em () T)
p≼ x G.top = ≼-refl (G.suc x)

≼p : ∀ x y → x +ʳ y ≼ plus zero x y
≼p x G.zero = ≼-refl x
≼p x (G.suc y) = s≼ (≺s (≼p x y))
≼p x (G.lim f) = l≼ (λ n → ≼-lim n (≼p x (f n)))
≼p x (G.lc () c t g)
≼p x (G.em () T)
≼p x G.top = ≼-refl (G.suc x)

plus-right : ∀ x y → y ≼ plus zero x y
plus-right x y = ≼-trans (add-right x y) (≼p x y)

plus-monoˡ : ∀ {x x′} → x ≼ x′ → ∀ y → plus zero x y ≼ plus zero x′ y
plus-monoˡ {x} {x′} p y = ≼-trans (p≼ x y) (≼-trans (add-monoˡ p y) (≼p x′ y))
```

## 2 部分和：不降；吸收时不升

`psum` 是 `YiRawFoldBase.psum` (折叠里的那一个，每步加上下一项本身)，不是 `YiLvNegCum.psum` (每步加上下一项的后继)。

```agda
psum-aboveᵖ : ∀ (g : ℕ → R) n → g n ≼ psum zero g n
psum-aboveᵖ g zero = ≼-refl (g zero)
psum-aboveᵖ g (suc n) = plus-right (psum zero g n) (g (suc n))

lim≼psumᵖ : ∀ (g : ℕ → R) → G.lim g ≼ G.lim (psum zero g)
lim≼psumᵖ g = l≼ (λ n → ≼-lim n (psum-aboveᵖ g n))

Absorb : (ℕ → R) → Set
Absorb g = ∀ n → plus zero (g n) (g (suc n)) ≼ g (suc n)

psum-below : ∀ (g : ℕ → R) → Absorb g → ∀ n → psum zero g n ≼ g n
psum-below g h zero = ≼-refl (g zero)
psum-below g h (suc n) = ≼-trans (plus-monoˡ (psum-below g h n) (g (suc n))) (h n)

psum-flat : ∀ (g : ℕ → R) → Absorb g → G.lim (psum zero g) ≼ G.lim g
psum-flat g h = l≼ (λ n → ≼-lim n (psum-below g h n))
```

## 3 折叠的输出以 `cO` 为第一位置；加上它至少是后继

`Ψ-low` 对 `Ψ` 的各子句归纳。`one-below`：`x + cO k` 的第一位置里有 `suc x` (加法在 `top` 处一路展开到层号 0 的后继)。

```agda
Ψ-low : ∀ m k pl L (x : Ext m k) ξ (l : Lgl k ξ) (nb : Nested k ξ) →
  Cp m (cO m) (Ψ m k pl L x ξ l nb)
Ψ-low m k pl L x G.zero l nb = inj₁ refl
Ψ-low m k pl L x (G.suc a) l nb = inj₂ (zero , Ψ-low m k pl L x a l nb)
Ψ-low m k pl L x (G.lim f) (st , lf) nb =
  inj₂ (zero , Ψ-low m k pl L x (f zero) (lf zero) (nb zero))
Ψ-low m k pl L x (G.lc r c t g) (tg , dir , irr , lt , lg) (lw , nw , nt , ng) =
  inj₂ (ΨN-dn m k pl r (wayOf x r)
    (ndL m k pl L x r c t g (tg , dir , irr , lt , lg) (lw , nw , nt , ng))
    (Ψ-low m k pl L x t lt nt) (seedL k r c lw nw)
    (Ψ-low m k pl L x (g c (seedL k r c lw nw))
      (lg c (seedL k r c lw nw)) (ng c (seedL k r c lw nw))))
Ψ-low m (suc k) pl L x (G.em _ T) l nb = Ψ-low m k pl L (inS x) T l nb
Ψ-low m (lim f) pl L x (G.em n T) l nb = Ψ-low m (f n) (pl n) (proj₂ L n) (inL x n) T l nb
Ψ-low m zero pl L x G.top l nb = inj₂ (zero , inj₁ refl)
Ψ-low m (suc k) pl L x G.top l nb =
  inj₂ (Ψn-dn m k pl (wayOf x (inj₁ tt)) (ndT m k pl L (inS x))
    (Ψ-low m k pl L (inS x) (cO k) (cO-Lgl k) (cO-Nested k))
    (inj₁ refl , cO-Lgl k , cO-Nested k)
    (Ψ-low m k pl L (inS x) (cO k) (cO-Lgl k) (cO-Nested k)))
Ψ-low m (lim f) pl L low G.top l nb =
  inj₂ (zero , Ψ-low m (f zero) (pl zero) (proj₂ L zero) low G.top tt tt)
Ψ-low m (lim f) pl L (mix w) G.top l nb =
  inj₂ (zero , Ψ-low m (f zero) (pl zero) (proj₂ L zero) (mix (λ r → w (zero , r))) G.top tt tt)

one-below : ∀ k → Plain k → (A : Alg k) (x : Alg.T A) →
  Alg.Cpᵀ A (Alg.sT A x) (add k A x (cO k))
one-belowᵀ : ∀ k → Plain k → (A : Alg k) (x : Alg.T A) →
  Alg.Cpᵀ A (Alg.sT A x) (add k A x G.top)
one-below zero pl A x = inj₁ refl
one-below (suc k) pl A x = one-belowᵀ (suc k) pl A x
one-below (lim f) pl A x = one-belowᵀ (lim f) pl A x
one-belowᵀ zero pl A x = inj₁ refl
one-belowᵀ (suc k) pl A x =
  inj₂ (Alg.dnN A (inj₁ tt) (cO k) _ _ (one-below k pl (shS A) x))
one-belowᵀ (lim f) pl A x =
  inj₂ (Alg.dnL A zero (one-belowᵀ (f zero) (pl zero) (shL A zero) x))
```

## 4 闭项的吸收

`closedᵐ (suc k)` 是 `Raw k` 里的链的观察的极限 `lim o`，`o 0` 是 `closedᵐ k`。第 `j+1` 个链点是第 `j` 个加上推进用的输出，
推进用的输出以 `cO k` 为第一位置，所以第 `j+1` 个链点的第一位置里有第 `j` 个的后继；观察在后继处是 ω 倍。于是
`o 0 + o j ≼ o j + o j ≼ o j · ω ≼ o (j+1)`。只用到：折叠保持第一位置，第 0 层的第一位置在值之下。

```agda
module Abs (k : LF) (pl : Plain k) (L : Legal k) where

  X : Ext zero k
  X = mix (λ r → fold)

  N : NdR zero k
  N = ndT zero k pl L X

  module CL = ChainLegal k pl (cO k) (Nd.gk N)
    (λ η e → Ψ-legal k pl k pl L (ownT k pl L) tt η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
    (λ η e → Ψ-nested k k pl L (ownT k pl L) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
    (Nd.pk N) (startᴸ k (cO k) (cO-Lgl k) (cO-Nested k))
    (inj₁ refl , cO-Lgl k , cO-Nested k)

  η : ℕ → Raw k
  η j = atᵖ (CL.points j)

  ηl : ∀ j → Lgl k (η j)
  ηl j = proj₁ (proj₂ (CL.guards j))

  ηn : ∀ j → Nested k (η j)
  ηn j = proj₂ (proj₂ (CL.guards j))

  o : ℕ → R
  o j = Ψ zero k pl L X (η j) (ηl j) (ηn j)

  closed-is-lim : closedᵐ (suc k) pl L ≡ G.lim o
  closed-is-lim = refl

  body : ∀ j → Raw k
  body j = Ψ k k pl L (ownT k pl L) (η j) (ηl j) (ηn j)

  next-is-plus : ∀ j → η (suc j) ≡ plus k (η j) (body j)
  next-is-plus j = refl

  suc-below-next : ∀ j → Cp k (G.suc (η j)) (η (suc j))
  suc-below-next j =
    Cp-tr k (one-below k pl (rawAlg k) (η j))
      (add-cp k pl (rawAlg k) (η j)
        (Ψ-low k k pl L (ownT k pl L) (η j) (ηl j) (ηn j)))

  o-first : ∀ j → o 0 ≼ o j
  o-first j = cp→≼ (o j)
    (Ψ-cp zero k pl L X {ξ = cO k} (η j) (cO-Lgl k) (cO-Nested k) (ηl j) (ηn j)
      (proj₁ (CL.guards j)))

  times-ω : ∀ j → successor zero (o j) ≼ o (suc j)
  times-ω j = cp→≼ (o (suc j))
    (Ψ-cp zero k pl L X {ξ = G.suc (η j)} (η (suc j)) (ηl j) (ηn j) (ηl (suc j)) (ηn (suc j))
      (suc-below-next j))

  double : ∀ j → plus zero (o 0) (o j) ≼ successor zero (o j)
  double j = ≼-lim 1 (plus-monoˡ (o-first j) (o j))

  absorb : plus zero (o 0) (G.lim o) ≼ G.lim o
  absorb = l≼ (λ j → ≼-lim (suc j) (≼-trans (double j) (times-ω j)))

o-zero : ∀ k pl L → Abs.o k pl L 0 ≡ closedᵐ k pl L
o-zero zero pl L = refl
o-zero (suc k) pl L = refl
o-zero (lim f) pl L = refl

absorb-suc : ∀ k pl L →
  plus zero (closedᵐ k pl L) (closedᵐ (suc k) pl L) ≼ closedᵐ (suc k) pl L
absorb-suc k pl L =
  subst (λ z → plus zero z (closedᵐ (suc k) pl L) ≼ closedᵐ (suc k) pl L)
    (o-zero k pl L) (Abs.absorb k pl L)
```

## 5 规范实例：ω 与 ω·2 上部分和不偏高

`closedᵐ (lim f)` 是各支闭项的部分和的极限 (`YiRawFoldUp.Φᵐ-lim-row`)。两个实例的第 `n+1` 支都是第 `n` 支的后继层号，吸收由 §4 给出。
右边 `lim (λ n → closedᵐ (f n))` 是同样各项的逐项极限。

```agda
ω-terms : ℕ → R
ω-terms n = closedᵐ (fin n) (fin-plain n) (fin-legal n)

ω-psum-row : closedᵐ ω ω-plain ω-legal ≡ G.lim (psum zero ω-terms)
ω-psum-row = refl

ω-absorb : Absorb ω-terms
ω-absorb n = absorb-suc (fin n) (fin-plain n) (fin-legal n)

ω-psum≼lim : closedᵐ ω ω-plain ω-legal ≼ G.lim ω-terms
ω-psum≼lim = psum-flat ω-terms ω-absorb

ω-lim≼psum : G.lim ω-terms ≼ closedᵐ ω ω-plain ω-legal
ω-lim≼psum = lim≼psumᵖ ω-terms

ω2-terms : ℕ → R
ω2-terms n = closedᵐ (ω+ n) (ω+-plain n) (ω+-legal n)

ω2-psum-row : closedᵐ ω2 ω2-plain ω2-legal ≡ G.lim (psum zero ω2-terms)
ω2-psum-row = refl

ω2-absorb : Absorb ω2-terms
ω2-absorb n = absorb-suc (ω+ n) (ω+-plain n) (ω+-legal n)

ω2-psum≼lim : closedᵐ ω2 ω2-plain ω2-legal ≼ G.lim ω2-terms
ω2-psum≼lim = psum-flat ω2-terms ω2-absorb

ω2-lim≼psum : G.lim ω2-terms ≼ closedᵐ ω2 ω2-plain ω2-legal
ω2-lim≼psum = lim≼psumᵖ ω2-terms
```

## 6 偏高的折叠实例：各支相同的极限层号

`Kc = lim (λ _ → zero)`，每一步是 `self`。它 `Plain`，合法，证书一致 (`CohP` 是 `refl`)；各支都是层号 0，闭项都是 `closedᵐ zero`。
部分和的第 1 项已经是 `closedᵐ zero` 的两倍，严格高于逐项极限 (各项相同，值就是 `closedᵐ zero`)。这是退化的层号 (相邻支相等)，不是规范读回的 ω。

```agda
Kc : LF
Kc = lim (λ _ → zero)

Kc-plain : Plain Kc
Kc-plain n = tt

Kc-legal : Legal Kc
Kc-legal = (λ n → self) , (λ n → tt)

Kc-coh : CohP Kc Kc-plain Kc-legal
Kc-coh = (λ n → refl) , (λ n → tt)

c₀ : R
c₀ = closedᵐ zero tt tt

Kc-row : closedᵐ Kc Kc-plain Kc-legal ≡ G.lim (psum zero (λ _ → c₀))
Kc-row = refl

const-inflates : G.lim (λ _ → c₀) ≺ closedᵐ Kc Kc-plain Kc-legal
const-inflates = ≺l 1 (≺l 0 (≺s (l≼ (λ _ → ≼-refl c₀))))

const-not-back : closedᵐ Kc Kc-plain Kc-legal ≼ G.lim (λ _ → c₀) → ⊥
const-not-back p = ≺-irrefl (G.lim (λ _ → c₀)) (≺≼-trans const-inflates p)

-- 同一个层号在逐项的折叠的域里; 它的闭项就是各项的逐项极限, 严格低于带部分和的闭项.
Kc-dom : Domᵗ Kc Kc-plain Kc-legal
Kc-dom = ((λ n → tt) , (λ n → tt)) , Kc-coh

Kc-rowᵗ : closedᵗ Kc Kc-plain Kc-legal Kc-dom ≡ G.lim (λ _ → c₀)
Kc-rowᵗ = refl

termwise-below-psum : closedᵗ Kc Kc-plain Kc-legal Kc-dom ≺ closedᵐ Kc Kc-plain Kc-legal
termwise-below-psum = const-inflates
```
