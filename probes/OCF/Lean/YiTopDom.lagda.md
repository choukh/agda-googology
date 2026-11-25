# 规范域: 结点都在顶槽位

> 验收文件. 编译定理, 无前提. 定义与证明搬自第十三次审查的临时试验 `R13Top` (留档附件 `Review13-R13Top.agda.txt`), 只改模块名与排版.
> `Top`: 树里每个 Ω 结点的槽位都是本层的下标层自身. 规范闭项与两种折叠保持它 (`Ωt-top`, `top⊥`, `tops`, `EBOᶜ-top`); 顶槽位的结点只在目标是 `self` 时保留 (`kpTop-default`).
> 不否定什么. 用处: `YiTopE2` 的测试对象在这个域里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTopDom where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold
open import OCF.Lean.YiFreshLegal using (seq; iterInv; dS; dL; dW; EBOᶜ)
open import OCF.Lean.YiFreshCheck using (p₃)
```

## 域

```agda
IsTop : (ℓ : L) → Pos ℓ → Set
IsTop (suc a) (inj₁ _) = ⊤
IsTop (suc a) (inj₂ _) = ⊥
IsTop (lim g) _ = ⊥
IsTop (Ωₗ k h) (inj₁ (inj₁ _)) = ⊤
IsTop (Ωₗ k h) (inj₁ (inj₂ _)) = ⊥
IsTop (Ωₗ k h) (inj₂ _) = ⊥

mutual
  Top : (ℓ : L) → Tr ℓ → Set
  Top ℓ zero       = ⊤
  Top ℓ (suc x)    = Top ℓ x
  Top ℓ (lim f)    = (n : ℕ) → Top ℓ (f n)
  Top ℓ (Ω p g)    = IsTop ℓ p × ((z : Br ℓ p) → TopBr ℓ p z → Top ℓ (g z))
  Top ℓ (up x c y) = Top ℓ x × TopCh ℓ c y

  TopBr : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Set
  TopBr (suc a)  t              z = TopBr⁼ a t z
  TopBr (lim g)  (n , t)        z = TopBr⁼ (g n) t z
  TopBr (Ωₗ k h) (inj₁ t)       z = TopBr⁼ k t z
  TopBr (Ωₗ k h) (inj₂ (c , t)) z = TopBr⁼ (h c) t z

  TopBr⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Set
  TopBr⁼ a (inj₁ _) z = Top a z
  TopBr⁼ a (inj₂ p) z = TopBr a p z

  TopCh : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → Set
  TopCh (suc a)  _ y = Top a y
  TopCh (lim g)  n y = Top (g n) y
  TopCh (Ωₗ k h) c y = Top (h c) y

mutual
  topFrom : (ℓ : L) (p : Pos ℓ) (x : Tr (at ℓ p)) → Top (at ℓ p) x → TopBr ℓ p (fromBr ℓ p x)
  topFrom (suc a)  t              x h = topFrom⁼ a t x h
  topFrom (lim g)  (n , t)        x h = topFrom⁼ (g n) t x h
  topFrom (Ωₗ k h) (inj₁ t)       x e = topFrom⁼ k t x e
  topFrom (Ωₗ k h) (inj₂ (c , t)) x e = topFrom⁼ (h c) t x e

  topFrom⁼ : (a : L) (t : Pos⁼ a) (x : Tr (at⁼ a t)) → Top (at⁼ a t) x → TopBr⁼ a t (fromBr⁼ a t x)
  topFrom⁼ a (inj₁ _) x h = h
  topFrom⁼ a (inj₂ p) x h = topFrom a p x h
```

## 运算与 Ω 树保持域

```agda
+-top : ∀ {ℓ} (a b : Tr ℓ) → Top ℓ a → Top ℓ b → Top ℓ (a + b)
+-top a zero       ha hb = ha
+-top a (suc b)    ha hb = +-top a b ha hb
+-top a (lim f)    ha hb = λ n → +-top a (f n) ha (hb n)
+-top a (Ω p g)    ha (it , hb) = it , λ z h → +-top a (g z) ha (hb z h)
+-top a (up y c w) ha (hy , hw) = +-top a y ha hy , hw

ι-top : (j : L) (a : Tr zero) → Top j (ι j a)
ι-top j zero    = tt
ι-top j (suc a) = ι-top j a
ι-top j (lim f) = λ n → ι-top j (f n)
ι-top j (Ω () _)
ι-top j (up _ () _)

next-top : ∀ {j} (b : Tr j) → Top j b → Top j (next b)
next-top {j} b hb = go
  where
  go : (n : ℕ) → Top j (iter (b +_) b n)
  go zero    = hb
  go (suc n) = +-top b _ hb (go n)

cum-top : ∀ {j} (F : ℕ → Tr j) → ((n : ℕ) → Top j (F n)) → (n : ℕ) → Top j (cum F n)
cum-top F hF zero    = hF zero
cum-top F hF (suc n) = +-top (cum F n) (F (suc n)) (cum-top F hF n) (hF (suc n))

Ωt-top : (ℓ : L) → Top ℓ (Ωt ℓ)
Ωt-top zero     = tt
Ωt-top (suc a)  = tt , λ c h → tt , h
Ωt-top (lim g)  = cl
  where
  cl : (n : ℕ) → Top (lim g) (seq (Ωt (lim g)) n)
  cl zero    = tt , Ωt-top (g zero)
  cl (suc n) = cl n , Ωt-top (g (suc n))
Ωt-top (Ωₗ k h) = tt , λ c _ → tt , Ωt-top (h c)
```

## 顶槽位的保留判定

只在 `self` 交出槽位 (交出的仍是顶), 其余走默认.

```agda
kpTop : (ℓ : L) (p : Pos ℓ) → IsTop ℓ p → {j : L} (w : j ≤ ℓ) {X : Set} (R : X → Set)
  {k : (q : Pos j) → (Br j q → Br ℓ p) → X} {d : X}
  → ((q : Pos j) (cv : Br j q → Br ℓ p) → IsTop j q → ((z : Br j q) → TopBr j q z → TopBr ℓ p (cv z)) → R (k q cv))
  → R d → R (kp ℓ p w k d)
kpTop ℓ         p               it self      R hk hd = hk p (λ z → z) it (λ z h → h)
kpTop (suc a)   (inj₁ _)        it (ins w)   R hk hd = hd
kpTop (lim g)   (m , p)         () (inl n w) R hk hd
kpTop (Ωₗ k′ h) (inj₁ (inj₁ _)) it (ink w)   R hk hd = hd
kpTop (Ωₗ k′ h) (inj₁ (inj₁ _)) it (inb c w) R hk hd = hd

data NotSelf : {j ℓ : L} → j ≤ ℓ → Set where
  ns-ins : ∀ {j a} {w : j ≤ a} → NotSelf (ins w)
  ns-inl : ∀ {j g n} {w : j ≤ g n} → NotSelf (inl {g = g} n w)
  ns-ink : ∀ {j k h} {w : j ≤ k} → NotSelf (ink {h = h} w)
  ns-inb : ∀ {j k h c} {w : j ≤ h c} → NotSelf (inb {k = k} {h = h} c w)

kpTop-default : (ℓ : L) (p : Pos ℓ) → IsTop ℓ p → {j : L} (w : j ≤ ℓ) → NotSelf w → {X : Set}
  (k : (q : Pos j) → (Br j q → Br ℓ p) → X) (d : X) → kp ℓ p w k d ≡ d
kpTop-default (suc a)   (inj₁ _)        it (ins w)   ns-ins k d = refl
kpTop-default (lim g)   (m , p)         () (inl n w) ns-inl k d
kpTop-default (Ωₗ k′ h) (inj₁ (inj₁ _)) it (ink w)   ns-ink k d = refl
kpTop-default (Ωₗ k′ h) (inj₁ (inj₁ _)) it (inb c w) ns-inb k d = refl
```

## 折叠保持域

```agda
TopB : (ℓ : L) → Base ℓ → Set
TopB ℓ B = Top zero (b⊥ B) × ((j : L) (w : j ≤ ℓ) → Top j (bs B j w))

TopB₀ : (ℓ : L) → TopB ℓ (B₀ ℓ)
TopB₀ ℓ = Ωt-top zero , λ j _ → Ωt-top j

mutual
  top⊥ : (ℓ : L) (B : Base ℓ) → TopB ℓ B → (x : Tr ℓ) → Top ℓ x → Top zero (ψ⊥ ℓ B x)
  top⊥ ℓ B hB zero    h = proj₁ hB
  top⊥ ℓ B hB (suc x) h = next-top _ (top⊥ ℓ B hB x h)
  top⊥ ℓ B hB (lim f) h = λ n → top⊥ ℓ B hB (f n) (h n)
  top⊥ ℓ B hB (Ω p g) (it , hg) =
    cum-top _ (λ n → top⊥ ℓ B hB (g _) (hg _ (iterInv (TopBr ℓ p) _ _ (topFrom ℓ p zero tt)
      (λ z hz → topFrom ℓ p _ (tops ℓ B hB (at ℓ p) (posW ℓ p) (g z) (hg z hz))) n)))
  top⊥ (suc a)  B hB (up x _ y) (hx , hy) =
    top⊥ a (dS a B x) (top⊥ (suc a) B hB x hx , λ j w → tops (suc a) B hB j (ins w) x hx) y hy
  top⊥ (lim g)  B hB (up x n y) (hx , hy) =
    top⊥ (g n) (dL g B n x) (top⊥ (lim g) B hB x hx , λ j w → tops (lim g) B hB j (inl n w) x hx) y hy
  top⊥ (Ωₗ k h) B hB (up x c y) (hx , hy) =
    top⊥ (h c) (dW k h B c x) (top⊥ (Ωₗ k h) B hB x hx , λ j w → tops (Ωₗ k h) B hB j (inb c w) x hx) y hy

  tops : (ℓ : L) (B : Base ℓ) → TopB ℓ B → (j : L) (v : j ≤ ℓ) (x : Tr ℓ) → Top ℓ x → Top j (ψs ℓ B j v x)
  tops ℓ B hB j v zero    h = proj₂ hB j v
  tops ℓ B hB j v (suc x) h = next-top _ (tops ℓ B hB j v x h)
  tops ℓ B hB j v (lim f) h = λ n → tops ℓ B hB j v (f n) (h n)
  tops ℓ B hB j v (Ω p g) (it , hg) =
    kpTop ℓ p it v (Top j)
      (λ q cv tq lc → tq , λ z hz → tops ℓ B hB j v (g (cv z)) (hg (cv z) (lc z hz)))
      (cum-top _ (λ n → tops ℓ B hB j v (g _) (hg _ (iterInv (TopBr ℓ p) _ _ (topFrom ℓ p zero tt)
        (λ z hz → topFrom ℓ p _ (tops ℓ B hB (at ℓ p) (posW ℓ p) (g z) (hg z hz))) n))))
  tops ℓ B hB _ self (up x c y) (hx , hy) = tops ℓ B hB ℓ self x hx , hy
  tops (suc a) B hB j (ins v) (up x _ y) (hx , hy) =
    tops a (dS a B x) (top⊥ (suc a) B hB x hx , λ j′ w′ → tops (suc a) B hB j′ (ins w′) x hx) j v y hy
  tops (lim g) B hB j (inl n v) (up x m y) (hx , hy) with eqℕ m n
  ... | just refl =
    tops (g m) (dL g B m x) (top⊥ (lim g) B hB x hx , λ j′ w′ → tops (lim g) B hB j′ (inl m w′) x hx) j v y hy
  ... | nothing = +-top _ _ (tops (lim g) B hB j (inl n v) x hx) (ι-top j _)
  tops (Ωₗ k h) B hB j (ink v)    (up x c y) (hx , hy) =
    +-top _ _ (tops (Ωₗ k h) B hB j (ink v) x hx) (ι-top j _)
  tops (Ωₗ k h) B hB j (inb c′ v) (up x c y) (hx , hy) =
    +-top _ _ (tops (Ωₗ k h) B hB j (inb c′ v) x hx) (ι-top j _)

EBOᶜ-top : Top zero EBOᶜ
EBOᶜ-top = top⊥ Λ (B₀ Λ) (TopB₀ Λ) (Ωt Λ) (Ωt-top Λ)
```

旧测试对象不在域内.

```agda
gap3-not-top : Top (tw 3) (Ω p₃ (λ _ → zero)) → ⊥
gap3-not-top (() , _)

j3-not-top : Top (suc (tw 3)) (Ω (inj₂ p₃) (λ _ → zero)) → ⊥
j3-not-top (() , _)
```
