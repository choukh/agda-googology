# 折叠带证据 (F1 原型): 树的路线证据与按证据取的路线

> 判决: 原型 (块的增量, 不改块). 树的证据 `E ℓ x`: 结点槽位里的孩子下标与嵌入的孩子下标各带自己的证据, ℕ 极限处可选地带相邻项的第一位置序; 对一切树有平凡证据 `E₀`.
> 路线 `Rt′` 在 `Ωₗ k h` 处改成 "给了下标 c 的证据才给孩子层 h c 的路线"; 读回层号的路线由树的证据算出 (`R↑`, 结点的分支也算).
> 不否定什么. `E` 是合法性的可计算部分 (可选), 不是合法性; 严格的合法谓词 `Leg′` 在 `YiFLLegal`, 折叠在 `YiFLFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFLBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshLegal using (_⊢_◃_)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiLimBlock
open import OCF.Lean.YiLimLegal using (◃→⊑)
```

## 树的证据

与 `Leg` 同步递归. 结点的分支只在分支带证据时给证据 (与合法性同一个形状), 所以折叠的保留行对裸的分支只能用 `E₀`.

```agda
mutual
  E : (ℓ : L) → Tr ℓ → Set
  E ℓ zero       = ⊤
  E ℓ (suc x)    = E ℓ x
  E ℓ (lim f)    = ((n : ℕ) → E ℓ (f n)) × Maybe ((n : ℕ) → ℓ ⊢ f n ◃ f (suc n))
  E ℓ (Ω p g)    = EP ℓ p × ((z : Br ℓ p) → EBr ℓ p z → E ℓ (g z))
  E ℓ (up x c y) = E ℓ x × EI ℓ c × ECh ℓ c y

  EP : (ℓ : L) → Pos ℓ → Set
  EP (suc a)  t              = EP⁼ a t
  EP (lim g)  (n , t)        = EP⁼ (g n) t
  EP (Ωₗ k h) (inj₁ t)       = EP⁼ k t
  EP (Ωₗ k h) (inj₂ (c , t)) = E k c × EP⁼ (h c) t

  EP⁼ : (a : L) → Pos⁼ a → Set
  EP⁼ a (inj₁ _) = ⊤
  EP⁼ a (inj₂ p) = EP a p

  EBr : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Set
  EBr (suc a)  t              z = EBr⁼ a t z
  EBr (lim g)  (n , t)        z = EBr⁼ (g n) t z
  EBr (Ωₗ k h) (inj₁ t)       z = EBr⁼ k t z
  EBr (Ωₗ k h) (inj₂ (c , t)) z = EBr⁼ (h c) t z

  EBr⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Set
  EBr⁼ a (inj₁ _) z = E a z
  EBr⁼ a (inj₂ p) z = EBr a p z

  EI : (ℓ : L) → Ch ℓ → Set
  EI zero     ()
  EI (suc a)  _ = ⊤
  EI (lim g)  n = ⊤
  EI (Ωₗ k h) c = E k c

  ECh : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → Set
  ECh (suc a)  _ y = E a y
  ECh (lim g)  n y = E (g n) y
  ECh (Ωₗ k h) c y = E (h c) y
```

平凡证据 (处处没有相邻序), 与分支换型.

```agda
mutual
  E₀ : (ℓ : L) (x : Tr ℓ) → E ℓ x
  E₀ ℓ zero       = tt
  E₀ ℓ (suc x)    = E₀ ℓ x
  E₀ ℓ (lim f)    = (λ n → E₀ ℓ (f n)) , nothing
  E₀ ℓ (Ω p g)    = EP₀ ℓ p , λ z _ → E₀ ℓ (g z)
  E₀ ℓ (up x c y) = E₀ ℓ x , EI₀ ℓ c , ECh₀ ℓ c y

  EP₀ : (ℓ : L) (p : Pos ℓ) → EP ℓ p
  EP₀ (suc a)  t              = EP⁼₀ a t
  EP₀ (lim g)  (n , t)        = EP⁼₀ (g n) t
  EP₀ (Ωₗ k h) (inj₁ t)       = EP⁼₀ k t
  EP₀ (Ωₗ k h) (inj₂ (c , t)) = E₀ k c , EP⁼₀ (h c) t

  EP⁼₀ : (a : L) (t : Pos⁼ a) → EP⁼ a t
  EP⁼₀ a (inj₁ _) = tt
  EP⁼₀ a (inj₂ p) = EP₀ a p

  EI₀ : (ℓ : L) (c : Ch ℓ) → EI ℓ c
  EI₀ zero     ()
  EI₀ (suc a)  _ = tt
  EI₀ (lim g)  n = tt
  EI₀ (Ωₗ k h) c = E₀ k c

  ECh₀ : (ℓ : L) (c : Ch ℓ) (y : ChT ℓ c) → ECh ℓ c y
  ECh₀ (suc a)  _ y = E₀ a y
  ECh₀ (lim g)  n y = E₀ (g n) y
  ECh₀ (Ωₗ k h) c y = E₀ (h c) y

mutual
  EBr₀ : (ℓ : L) (p : Pos ℓ) (z : Br ℓ p) → EBr ℓ p z
  EBr₀ (suc a)  t              z = EBr⁼₀ a t z
  EBr₀ (lim g)  (n , t)        z = EBr⁼₀ (g n) t z
  EBr₀ (Ωₗ k h) (inj₁ t)       z = EBr⁼₀ k t z
  EBr₀ (Ωₗ k h) (inj₂ (c , t)) z = EBr⁼₀ (h c) t z

  EBr⁼₀ : (a : L) (t : Pos⁼ a) (z : Br⁼ a t) → EBr⁼ a t z
  EBr⁼₀ a (inj₁ _) z = E₀ a z
  EBr⁼₀ a (inj₂ p) z = EBr₀ a p z

mutual
  eFrom : (ℓ : L) (p : Pos ℓ) (x : Tr (at ℓ p)) → E (at ℓ p) x → EBr ℓ p (fromBr ℓ p x)
  eFrom (suc a)  t              x e = eFrom⁼ a t x e
  eFrom (lim g)  (n , t)        x e = eFrom⁼ (g n) t x e
  eFrom (Ωₗ k h) (inj₁ t)       x e = eFrom⁼ k t x e
  eFrom (Ωₗ k h) (inj₂ (c , t)) x e = eFrom⁼ (h c) t x e

  eFrom⁼ : (a : L) (t : Pos⁼ a) (x : Tr (at⁼ a t)) → E (at⁼ a t) x → EBr⁼ a t (fromBr⁼ a t x)
  eFrom⁼ a (inj₁ _) x e = e
  eFrom⁼ a (inj₂ p) x e = eFrom a p x e

chE : (ℓ : L) (c : Ch ℓ) (y : ChT ℓ c) → ECh ℓ c y → E (chL ℓ c) (chT ℓ c y)
chE (suc a)  _ y e = e
chE (lim g)  n y e = e
chE (Ωₗ k h) c y e = e
```

## 按谓词取的路线

`Q k c` 是 "下标 c 带的东西". 与 `YiLimBlock.Rt`, `RtP` 不同的只有 `Ωₗ` 一行: 孩子层的路线以 `Q k c` 为前提. `Q` 取 `E` 是折叠用的; 取严格合法性 `Leg′` 的在 `YiFLLegal`.

```agda
module Rts (Q : (k : L) → Tr k → Set) where

  Rt′ : L → Set
  Rt′ zero     = ⊤
  Rt′ (suc a)  = Rt′ a
  Rt′ (lim g)  = ((n : ℕ) → Rt′ (g n)) × Maybe (Adj g)
  Rt′ (Ωₗ k h) = Rt′ k × ((c : Tr k) → Q k c → Rt′ (h c))

  RtP′ : L → Set
  RtP′ zero     = ⊤
  RtP′ (suc b)  = RtP′ b
  RtP′ (lim g)  = ((n : ℕ) → RtP′ (g n)) × Maybe (AdjP g)
  RtP′ (Ωₗ k h) = Rt′ k × ((c : Tr k) → Q k c → RtP′ (h c))

  Rt′⊕ : (a b : L) → Rt′ a → RtP′ b → Rt′ (a ⊕ b)
  Rt′⊕ a zero     ra rb        = ra
  Rt′⊕ a (suc b)  ra rb        = Rt′⊕ a b ra rb
  Rt′⊕ a (lim g)  ra (rb , R)  = (λ n → Rt′⊕ a (g n) ra (rb n)) , shiftA a g R
  Rt′⊕ a (Ωₗ k h) ra (rk , rb) = rk , λ c q → Rt′⊕ a (h c) ra (rb c q)

  RtP′⊕ : (b₁ b₂ : L) → RtP′ b₁ → RtP′ b₂ → RtP′ (b₁ ⊕ b₂)
  RtP′⊕ b₁ zero     r₁ r₂        = r₁
  RtP′⊕ b₁ (suc b)  r₁ r₂        = RtP′⊕ b₁ b r₁ r₂
  RtP′⊕ b₁ (lim g)  r₁ (r₂ , R)  = (λ n → RtP′⊕ b₁ (g n) r₁ (r₂ n)) , shiftP b₁ g R
  RtP′⊕ b₁ (Ωₗ k h) r₁ (rk , r₂) = rk , λ c q → RtP′⊕ b₁ (h c) r₁ (r₂ c q)

open Rts E public
```

槽位层的路线 (槽位里的孩子下标带证据).

```agda
mutual
  Rt-at : (ℓ : L) → Rt′ ℓ → (p : Pos ℓ) → EP ℓ p → Rt′ (at ℓ p)
  Rt-at (suc a)  ρ         t              e        = Rt-at⁼ a ρ t e
  Rt-at (lim g)  (ρc , _)  (n , t)        e        = Rt-at⁼ (g n) (ρc n) t e
  Rt-at (Ωₗ k h) (ρk , ρc) (inj₁ t)       e        = Rt-at⁼ k ρk t e
  Rt-at (Ωₗ k h) (ρk , ρc) (inj₂ (c , t)) (ec , e) = Rt-at⁼ (h c) (ρc c ec) t e

  Rt-at⁼ : (a : L) → Rt′ a → (t : Pos⁼ a) → EP⁼ a t → Rt′ (at⁼ a t)
  Rt-at⁼ a ρ (inj₁ _) e = ρ
  Rt-at⁼ a ρ (inj₂ p) e = Rt-at a ρ p e
```

## 读回层号的路线由树的证据算出

与 `YiLimLegal.RtP↑` 不同: 结点的分支也给路线 (以分支的证据为前提), 槽位层的路线取 `Rt-at`.

```agda
adjP : ∀ {k} {f : ℕ → Tr k} → Maybe ((n : ℕ) → k ⊢ f n ◃ f (suc n)) → Maybe (AdjP (λ n → ↑ k (f n)))
adjP (just a) = just (λ n → ◃→⊑ (a n))
adjP nothing  = nothing

mutual
  R↑ : (k : L) → Rt′ k → (t : Tr k) → E k t → RtP′ (↑ k t)
  R↑ k ρ zero       e            = tt
  R↑ k ρ (suc x)    e            = R↑ k ρ x e
  R↑ k ρ (lim f)    (ef , A)     = (λ n → R↑ k ρ (f n) (ef n)) , adjP A
  R↑ k ρ (Ω p g)    (ep , eg)    = Rt-at k ρ p ep , λ c ec → R↑ k ρ (g (fromBr k p c)) (eg _ (eFrom k p c ec))
  R↑ k ρ (up x c y) (ex , ei , ey) = RtP′⊕ (↑ k x) (↑ch k c y) (R↑ k ρ x ex) (R↑ch k ρ c ei y ey)

  R↑ch : (k : L) → Rt′ k → (c : Ch k) → EI k c → (y : ChT k c) → ECh k c y → RtP′ (↑ch k c y)
  R↑ch (suc a)  ρ         _ _  y e = R↑ a ρ y e
  R↑ch (lim g)  (ρc , _)  n _  y e = R↑ (g n) (ρc n) y e
  R↑ch (Ωₗ k h) (ρk , ρc) c ei y e = R↑ (h c) (ρc c ei) y e
```

## 塔与 Λ 的路线 (闭项)

塔第 n+1 项的孩子层 tw n ⊕ ↑c 的路线现在读 c 的证据.

```agda
Rt′-tw : (n : ℕ) → Rt′ (tw n)
Rt′-tw zero    = tt
Rt′-tw (suc n) = Rt′-tw n , λ c ec → Rt′⊕ (tw n) (↑ (tw n) c) (Rt′-tw n) (R↑ (tw n) (Rt′-tw n) c ec)

Rt′-Λ : Rt′ Λ
Rt′-Λ = Rt′-tw , just Adj-Λ
```

## 沿路径搬运的证据

路径里的孩子下标 (`inb c`) 不带证据, 搬出来的下标取 `E₀`. 这是本原型的已知退让 (路径的证据没有做).

```agda
pshE : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → EP⁼ k t → EP⁼ a (psh v t)
pshE self      t e = e
pshE (ins v)   t e = pshE v t e
pshE (inl n v) t e = pshE v t e
pshE (inlu vs) t e = pshE (vs zero) t e
pshE (ink v)   t e = pshE v t e
pshE {a = Ωₗ k h} (inb c v) t e = E₀ k c , pshE v t e
pshE (inu vs)  t e = tt , pshE (vs zero) t e

embE : (ℓ : L) (ε : Ev ℓ) {k : L} (v : k ≤ ℓ) (y : Tr k) → E k y → E ℓ (emb ℓ ε v y)
embE ℓ        ε        self      y e = e
embE (suc a)  ε        (ins v)   y e = tt , tt , embE a ε v y e
embE (lim g)  ε        (inl n v) y e = tt , tt , embE (g n) (ε n) v y e
embE (lim g)  ε        (inlu vs) y e = tt , tt , embE (g zero) (ε zero) (vs zero) y e
embE (Ωₗ k h) (ek , ε) (ink v)   y e = tt , tt , embE (h zero) (proj₂ (ε zero)) (v ∙ proj₁ (ε zero)) y e
embE (Ωₗ k h) (ek , ε) (inb c v) y e = tt , E₀ k c , embE (h c) (proj₂ (ε c)) v y e
embE (Ωₗ k h) (ek , ε) (inu vs)  y e = tt , tt , embE (h zero) (proj₂ (ε zero)) (vs zero) y e
```
