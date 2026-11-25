# YiOver 主线对参照：第 1 层树的上界关系

**验收文件，档位：编译定理 (引理)。** `_⊵_`：主线第 1 层的树 (`R₁`) 不高于参照第 1 层的树 (`T₁`)；结点逐点比较，只比读回 ≥ 1 的分支下标 (链从 `top` 即 1 起)。
`up⁰`：参照是好树 (`Gd`) 时，目标层 0 的折叠保持它到值序 (`read (Ψ⁰ ξ) ≼ ψ⁰ X`)；结点处主线的链累加、参照不累加，由 `SC` 给的倍增吸收 (链下标错开到 2n+1)。
`Φ-pres`, `+-comp`：主线的第 1 层折叠 `Φ` 与加法对应参照的 `ψ₁` 与加法。只谈第 1 层 (即 `F (fin 2)` 用到的树)。用法在 [YiOverTwo](YiOverTwo.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOverMain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3 using (R)
open import OCF.Lean.YiLeanAccFin using (read; read-plus; L1; R₁; Φ)
open import OCF.Lean.YiChainBack using (module PhiR)
open import OCF.Align.YiVmConExact using (ˣ→≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; ≼u; ≼-refl; ≼-trans; ≼-suc; ≅→≼;
  ≼-+ʳ; +-mono; ψ⁰-mono⁰)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
open import OCF.Lean.YiOverRef
open import OCF.Lean.YiOverOps
```

## 1 关系

```agda
infix 4 _⊵_
data _⊵_ : R₁ → T₁ → Set where
  s⊵ : ∀ {ξ X} → ξ ⊵ X → G.suc ξ ⊵ L.suc X
  w⊵ : ∀ {ξ X} → ξ ⊵ X → ξ ⊵ L.suc X
  ⊵l : ∀ {ξ} {f : ℕ → T₁} n → ξ ⊵ f n → ξ ⊵ L.lim f
  l⊵ : ∀ {g : ℕ → R₁} {X} → (∀ n → g n ⊵ X) → G.lim g ⊵ X
  ⊵1 : ∀ {ξ} {f : T₀ → T₁} → ξ ⊵ f 𝟙 → ξ ⊵ L.limᵢ L.zero f
  nd : ∀ {g : R → R₁} {f : T₀ → T₁} → (∀ (a : R) (y : T₀) → 𝟙 ≼ read a → read a ≼ y → g a ⊵ f y) →
       G.lc (inj₁ tt) g ⊵ L.limᵢ L.zero f
  tp : ∀ {f : T₀ → T₁} → (∀ (a : R) (y : T₀) → 𝟙 ≼ read a → read a ≼ y → G.em tt a ⊵ f y) →
       G.top ⊵ L.limᵢ L.zero f
  em : ∀ {a : R} {y : T₀} → read a ≼ y → G.em tt a ⊵ L.up L.zero y
```

## 2 目标层 0 的折叠

`Node`：一个结点的两条链。参照链 `δ f` 每步至少倍增 (`dbl`)，主线链的第 n 点落在参照链的第 2n+1 点之下 (`C`)。

```agda
module Node (f : T₀ → T₁) (s : SC f) (gm gk : R → R)
  (Hm : ∀ (a : R) (y : T₀) → 𝟙 ≼ read a → read a ≼ y → read (gm a) ≼ L.ψ⁰ (f y))
  (Hk : ∀ (a : R) (y : T₀) → 𝟙 ≼ read a → read a ≼ y → read (gk a) ≼ L.ψ⁰ (f y)) where

  d : ℕ → T₀
  d = δ f

  sucle : ∀ {a : T₀} → 𝟙 ≼ a → L.suc a ≼ (a L.+ a)
  sucle {a} o = +-mono (≼-refl a) o

  dbl : ∀ m → L.suc (d m) ≼ d (suc m) → (d (suc m) L.+ d (suc m)) ≼ d (suc (suc m))
  dbl m p = ≼-trans (+-mono (ψ₀≼ (f (d m))) (ψ₀≼ (f (d m))))
    (≼-trans (≼l 2 (≼-refl _))
    (≼-trans (mono⁰ (SC.db s (d m) (one f m)))
    (≼-trans (mono⁰ (SC.mo s (L.suc (d m)) (d (suc m)) (s≼s z≼) p))
    (≼ψ₀ (f (d (suc m)))))))

  two : L.suc (d 0) ≼ d 1
  two = ≼-trans (≼l 2 (≼-refl _)) (≼-trans (mono⁰ (SC.po s)) (≼ψ₀ (f 𝟙)))

  incr : ∀ m → L.suc (d m) ≼ d (suc m)
  incr zero = two
  incr (suc m) = ≼-trans (sucle (one f (suc m))) (dbl m (incr m))

  le : ∀ m → d m ≼ d (suc m)
  le m = ≼-trans (≼-suc (≼-refl (d m))) (incr m)

  idx : ℕ → ℕ
  idx zero = 1
  idx (suc n) = suc (suc (idx n))

  c : ℕ → R
  c = chain zero gk

  C : ∀ n → (𝟙 ≼ read (c n)) × (read (c n) ≼ d (idx n))
  C zero = ≼-refl 𝟙 , one f 1
  C (suc n) =
    ≼-trans (proj₁ (C n)) (≼-trans (≼-+ʳ (read (c n)) (read (gk (c n))))
      (≅→≼ (L.≅-sym (read-plus (c n) (gk (c n)))))) ,
    ≼-trans (≅→≼ (read-plus (c n) (gk (c n))))
      (≼-trans (+-mono (proj₂ (C n)) (Hk (c n) (d (idx n)) (proj₁ (C n)) (proj₂ (C n))))
      (≼-trans (+-mono (le (idx n)) (≼ψ₀ (f (d (idx n)))))
        (dbl (idx n) (incr (idx n)))))

  result : ∀ (w : Way zero zero) → read (Ψn zero zero w gm gk) ≼ L.ψ⁰ (L.limᵢ L.zero f)
  result (keep () e)
  result fold = l≼ (λ n → ≼l (idx n) (Hm (c n) (d (idx n)) (proj₁ (C n)) (proj₂ (C n))))
```

嵌入的第 0 层树：主线的第 0 层折叠不高于参照的 ψ⁰ (用 [YiChainBack](YiChainBack.lagda.md) 的 `PHIR`)。

```agda
em-up : ∀ {a : R} {Z : T₁} → G.em tt a ⊵ Z → ∀ (x₀ : Ext zero zero) → read (Ψ zero v0 x₀ a) ≼ L.ψ⁰ Z
em-up {a} (em q) x₀ = ≼-trans (ˣ→≼ (proj₁ (PhiR.PHIR x₀ a))) (ψ⁰-mono⁰ q)
em-up (w⊵ p) x₀ = ≼l 1 (em-up p x₀)
em-up (⊵l n p) x₀ = ≼l n (em-up p x₀)
em-up (⊵1 p) x₀ = ≼l 0 (em-up p x₀)

succ-up : ∀ (Y : R) {X : T₁} → read Y ≼ L.ψ⁰ X → read (succ zero Y) ≼ L.ψ⁰ (L.suc X)
succ-up Y {X} h = l≼ (λ n → ≼l (suc n) (cp n)) where
  cp : ∀ n → read (acc (λ _ z → plus zero Y z) Y n) ≼ iterᴸ (L.ψ⁰ X L.+_) L.zero (suc n)
  cp zero = h
  cp (suc n) = ≼-trans (≅→≼ (read-plus Y (acc (λ _ z → plus zero Y z) Y n))) (+-mono h (cp n))

up⁰ : ∀ (x : Ext zero L1) {ξ X} → Gd X → ξ ⊵ X → read (Ψ zero (vs v0) x ξ) ≼ L.ψ⁰ X
up⁰ x (gs g) (s⊵ {ξ} p) = succ-up (Ψ zero (vs v0) x ξ) (up⁰ x g p)
up⁰ x (gs g) (w⊵ p) = ≼l 1 (up⁰ x g p)
up⁰ x (gl g) (⊵l n p) = ≼l n (up⁰ x (g n) p)
up⁰ x g (l⊵ h) = l≼ (λ n → up⁰ x g (h n))
up⁰ x (gi s gb) (⊵1 p) = ≼l 0 (up⁰ x (gb 𝟙 (≼-refl 𝟙)) p)
up⁰ x (gi {f} s gb) (nd {g} h) =
  Node.result f s (λ η → Ψ zero (vs v0) x (g η)) (λ η → Ψ zero (vs v0) (cmp (vs v0) (inj₁ tt)) (g η))
    (λ a y o q → up⁰ x (gb y (≼-trans o q)) (h a y o q))
    (λ a y o q → up⁰ (cmp (vs v0) (inj₁ tt)) (gb y (≼-trans o q)) (h a y o q))
    (x (inj₁ tt))
up⁰ x (gi {f} s gb) (tp h) =
  Node.result f s (λ η → Ψ zero v0 (λ r → x (inj₂ r)) η) (λ η → Ψ zero v0 (self zero) η)
    (λ a y o q → em-up (h a y o q) (λ r → x (inj₂ r)))
    (λ a y o q → em-up (h a y o q) (self zero))
    (x (inj₁ tt))
up⁰ x gu (em q) = em-up (em q) (λ r → x (inj₂ r))
```

## 3 加法

```agda
infl⊵ : ∀ {ξ X} → ξ ⊵ X → ∀ {σ : Simₐ} (y : T₀) → ξ ⊵ L.add X σ y
infl⊵ p L.zero = p
infl⊵ p (L.suc y) = w⊵ (infl⊵ p y)
infl⊵ p (L.lim f) = ⊵l 0 (infl⊵ p (f 0))
infl⊵ p (L.limᵢ () f)
infl⊵ p (L.up () x)

B′ : Bld L1 zero
B′ r = G.lc (inj₂ r)

tail : ∀ {ξ X} → ξ ⊵ X → ∀ (a : R) {σ : Simₐ} {y : T₀} → read a ≼ y → add zero B′ ξ a ⊵ L.add X σ y
tail p G.zero {y = y} d = infl⊵ p y
tail p (G.suc a) (s≼s d) = s⊵ (tail p a d)
tail p (G.suc a) (≼l n d) = ⊵l n (tail p (G.suc a) d)
tail p (G.suc a) (≼i {p = ()} x ex d)
tail p (G.suc a) (≼u {r = ()} d)
tail p (G.lim f) (l≼ h) = l⊵ (λ n → tail p (f n) (h n))
tail p (G.lim f) (≼l n d) = ⊵l n (tail p (G.lim f) d)
tail p (G.lim f) (≼i {p = ()} x ex d)
tail p (G.lim f) (≼u {r = ()} d)
tail p G.top (s≼s {b = y} d) = s⊵ (infl⊵ p y)
tail p G.top (≼l n d) = ⊵l n (tail p G.top d)
tail p G.top (≼i {p = ()} x ex d)
tail p G.top (≼u {r = ()} d)
tail p (G.lc () g) d
tail p (G.em () a) d

em-add : ∀ {ξ X} → ξ ⊵ X → ∀ {a : R} {Z : T₁} → G.em tt a ⊵ Z → add zero B′ ξ a ⊵ (X L.+ Z)
em-add p {a} (em q) = tail p a q
em-add p (w⊵ q) = w⊵ (em-add p q)
em-add p (⊵l n q) = ⊵l n (em-add p q)
em-add p (⊵1 q) = ⊵1 (em-add p q)

+-comp : ∀ {ξ₁ X₁} → ξ₁ ⊵ X₁ → ∀ {ξ₂ X₂} → ξ₂ ⊵ X₂ → plus L1 ξ₁ ξ₂ ⊵ (X₁ L.+ X₂)
+-comp p (s⊵ q) = s⊵ (+-comp p q)
+-comp p (w⊵ q) = w⊵ (+-comp p q)
+-comp p (⊵l n q) = ⊵l n (+-comp p q)
+-comp p (l⊵ h) = l⊵ (λ n → +-comp p (h n))
+-comp p (⊵1 q) = ⊵1 (+-comp p q)
+-comp p (nd h) = nd (λ a y o q → +-comp p (h a y o q))
+-comp p (tp h) = nd (λ a y o q → em-add p (h a y o q))
+-comp p {G.em tt a} (em q) = tail p a q
```

## 4 第 1 层的折叠

```agda
top⊵B : ∀ (σ : Sim₀) (y : T₀) → G.top ⊵ B σ y
top⊵B σ L.zero = tp (λ a y o q → em q)
top⊵B σ (L.suc y) = ⊵l 1 (top⊵B σ y)
top⊵B σ (L.lim f) = ⊵l 0 (top⊵B σ (f 0))
top⊵B σ (L.limᵢ () f)
top⊵B σ (L.up () x)

succ-Φ : ∀ {Y X} → Y ⊵ X → succ L1 Y ⊵ L.lim (iterᴸ (X L.+_) L.zero)
succ-Φ {Y} {X} p = l⊵ (λ n → ⊵l (suc n) (cp n)) where
  cp : ∀ n → acc (λ _ z → plus L1 Y z) Y n ⊵ iterᴸ (X L.+_) L.zero (suc n)
  cp zero = p
  cp (suc n) = +-comp p (cp n)

Bup : ∀ (x₀ : Ext L1 zero) (a : R) {σ : Sim₀} {y : T₀} → read a ≼ y → Ψ L1 v0 x₀ a ⊵ B σ y
Bup x₀ G.zero {σ} {y} d = top⊵B σ y
Bup x₀ (G.suc a) (s≼s d) = succ-Φ (Bup x₀ a d)
Bup x₀ (G.suc a) (≼l n d) = ⊵l n (Bup x₀ (G.suc a) d)
Bup x₀ (G.suc a) (≼i {p = ()} x ex d)
Bup x₀ (G.suc a) (≼u {r = ()} d)
Bup x₀ (G.lim f) (l≼ h) = l⊵ (λ n → Bup x₀ (f n) (h n))
Bup x₀ (G.lim f) (≼l n d) = ⊵l n (Bup x₀ (G.lim f) d)
Bup x₀ (G.lim f) (≼i {p = ()} x ex d)
Bup x₀ (G.lim f) (≼u {r = ()} d)
Bup x₀ G.top {σ} (s≼s {b = y} d) = succ-Φ (top⊵B σ y)
Bup x₀ G.top (≼l n d) = ⊵l n (Bup x₀ G.top d)
Bup x₀ G.top (≼i {p = ()} x ex d)
Bup x₀ G.top (≼u {r = ()} d)
Bup x₀ (G.lc () g) d
Bup x₀ (G.em () a) d

em-Φ : ∀ {a : R} {Z : T₁} → G.em tt a ⊵ Z → ∀ (x₀ : Ext L1 zero) → Ψ L1 v0 x₀ a ⊵ ψ₁ Z
em-Φ {a} (em q) x₀ = Bup x₀ a q
em-Φ (w⊵ p) x₀ = ⊵l 1 (em-Φ p x₀)
em-Φ (⊵l n p) x₀ = ⊵l n (em-Φ p x₀)
em-Φ (⊵1 p) x₀ = ⊵1 (em-Φ p x₀)

Φ-pres : ∀ {ξ X} → ξ ⊵ X → Φ ξ ⊵ ψ₁ X
Φ-pres (s⊵ p) = succ-Φ (Φ-pres p)
Φ-pres (w⊵ p) = ⊵l 1 (Φ-pres p)
Φ-pres (⊵l n p) = ⊵l n (Φ-pres p)
Φ-pres (l⊵ h) = l⊵ (λ n → Φ-pres (h n))
Φ-pres (⊵1 p) = ⊵1 (Φ-pres p)
Φ-pres (nd h) = nd (λ a y o q → Φ-pres (h a (L.tr⁻ L.z≅ y) o (≼-trans q (proj₂ (tr⁻≈ y)))))
Φ-pres (tp h) = nd (λ a y o q → em-Φ (h a (L.tr⁻ L.z≅ y) o (≼-trans q (proj₂ (tr⁻≈ y)))) (λ r → self L1 (inj₂ r)))
Φ-pres {G.em tt a} (em q) = Bup (λ r → self L1 (inj₂ r)) a q
```
