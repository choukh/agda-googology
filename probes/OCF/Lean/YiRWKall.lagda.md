# 从头重写: k 侧对一切孩子保留

> 判决: 编译定理, 无前提. `kall`: 对任意带证据的层号 a, 下一站 `Nx a` 折到下标层 a (路径 `ink self`) 时, 孩子 c 里槽位带见证且严格在基底 a 里的结点, 以同一基底槽位保留; 对一切孩子 c, 一切底. `kall-tw`: 塔各项的实例.
> 证法与 F2 的 `YiLPKall` 同: 保留判定沿 `lift` 下行只经一致路径 `inu`, 不比较孩子; 这里只比较保留判定交出的槽位 (`qOf`), 不比较换型.
> 不否定什么. 只说保留, 不说分支.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRWKall where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
open import OCF.Lean.YiRWCheck using (Nx; Ok-Nx)
```

槽位在基底 a 里的见证 `InB` (经孩子下行, 或落在 Ω 形状的下标层侧), 它在 a 里的槽位 `prE`.

```agda
data InB (a : L) : (b : L) → Pos (a ⊕ b) → Set where
  ib0 : (p : Pos a) → InB a zero p
  ibc : ∀ {s h} (c : Ch s) {t} → InB a (h c) t → InB a (nd s h) (inj₂ (c , inj₂ t))
  ibK : ∀ {k h} (t : Pos⁼ k) → InB a (nd (sΩ k) h) (inj₁ t)

prE : ∀ {a b t} → InB a b t → OkO a b → Pos⁼ a
prE (ib0 p)   _             = inj₂ p
prE (ibc c i) (_ , ob)      = prE i (ob c)
prE (ibK t)   ((v , _) , _) = psh v t

qOf : ∀ {j X x₀} → Keep j X x₀ → Maybe (Pos j)
qOf (just (q , _)) = just q
qOf nothing        = nothing

qOf-mapK : ∀ {j X Y x₀ y₀} (f : X → Y) (e : f x₀ ≡ y₀) (m : Keep j X x₀) → qOf (mapK f e m) ≡ qOf m
qOf-mapK f e (just _) = refl
qOf-mapK f e nothing  = refl

lemA : (a b : L) (oa : Ok a) (ob : OkO a b) {K : L} (v : K ≤ a) (t : Pos⁼ K) {j : L} (u : j ≤ a)
  → qOf (kp⁼ (a ⊕ b) (Ok⊕ a b oa ob) (psh (v ∙ lift a b) t) (u ∙ lift a b)) ≡ qOf (kp⁼ a oa (psh v t) u)
lemA a zero     oa ob        v t u = refl
lemA a (nd s h) oa (os , ob) v t u = lemA a (h (c₀ s)) oa (ob (c₀ s)) v t u

lemB : (a b : L) (oa : Ok a) {t : Pos (a ⊕ b)} (i : InB a b t) (ob : OkO a b) {j : L} (u : j ≤ a)
  → qOf (kp (a ⊕ b) (Ok⊕ a b oa ob) t (u ∙ lift a b)) ≡ qOf (kp⁼ a oa (prE i ob) u)
lemB a _ oa (ib0 p)               ob             u = refl
lemB a _ oa (ibc c i)             (_ , ob)       u = lemB a _ oa i (ob c) u
lemB a _ oa (ibK {h = h} t)       ((v , ok) , ob) u =
  trans (qOf-mapK _ _ (kp⁼ (a ⊕ h zero) (Ok⊕ a (h zero) oa (ob zero)) (psh (v ∙ lift a (h zero)) t) (u ∙ lift a (h zero))))
        (lemA a (h zero) oa (ob zero) v t u)
```

## 保留

```agda
Kept : ∀ {j} → Pos j → Tr j → Set
Kept {j} p o = Σ (Br j p → Tr j) λ G′ → o ≡ Ω p G′

keptN : ∀ {j X x₀} (m : Keep j X x₀) (G : X → Tr⁺ j) (s : X → X) {p : Pos j} → qOf m ≡ just p
      → Kept p (proj₁ (node⁺ m G s))
keptN (just (q , cv , _)) G s refl = (λ z → proj₁ (G (cv z))) , refl

kall : (a : L) (oa : Ok a) (B : Base (Nx a)) (β : Tr⁺ a) (x : Tr (Nx a)) (c : Tr a) {t : Pos (a ⊕ ↑ a c)}
  (G : Br (a ⊕ ↑ a c) t → Tr (a ⊕ ↑ a c)) (e : a ⊕ ↑ a c ⊢ zero ◃ Ω t G)
  (i : InB a (↑ a c) t) (p : Pos a) → prE i (OkO↑ a a oa self c) ≡ inj₂ p
  → Kept p (proj₁ (ψ (Nx a) (Ok-Nx a oa) B a (ink self) β (up x c (Ω t G) e)))
kall a oa B β x c G e i p q =
  keptN _ _ _ (trans (lemB a (↑ a c) oa i (OkO↑ a a oa self c) self) (cong (λ s → qOf (kp⁼ a oa s self)) q))

kall-tw : (n : ℕ) (B : Base (tw (suc n))) (β : Tr⁺ (tw n)) (x : Tr (tw (suc n))) (c : Tr (tw n))
  {t : Pos (tw n ⊕ ↑ (tw n) c)} (G : Br (tw n ⊕ ↑ (tw n) c) t → Tr (tw n ⊕ ↑ (tw n) c))
  (e : tw n ⊕ ↑ (tw n) c ⊢ zero ◃ Ω t G) (i : InB (tw n) (↑ (tw n) c) t) (p : Pos (tw n))
  → prE i (OkO↑ (tw n) (tw n) (Ok-tw n) self c) ≡ inj₂ p
  → Kept p (proj₁ (ψ (tw (suc n)) (Ok-tw (suc n)) B (tw n) (ink self) β (up x c (Ω t G) e)))
kall-tw n = kall (tw n) (Ok-tw n)
```
