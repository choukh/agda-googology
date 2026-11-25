# 折叠带证据 (F1 原型): 更严的合法谓词

> 判决: 原型 (合法性的增量). `Leg′` 在 `YiFreshLegal.Leg` 上加两条: 嵌入 `up x c y` 的孩子下标 c 合法 (`LegI`), 结点槽位里的孩子下标合法 (`LegP`). 编译定理: 各层的 Ω 树满足它 (`Ωt-leg′`, 含塔各项与 Λ).
> 以 `Leg′` 为前提的路线 (`RL.Rt′`) 上, 合法树读出的偏移带路线, 结点的分支也带 (`R↑ᴸ`); 塔的路线 `Rtᴸ-tw` 是闭项.
> 不否定什么. `Leg′` 不蕴含也不被 `YiFLBlock.E` 蕴含 (结点的分支一行两边的前提不同); 第 0 层上 `Leg′` 给出 `E` (`le₀`). 折叠用的是 `E`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFLLegal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃t; Ωt-nz; seq)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiLimBlock
open import OCF.Lean.YiLimLegal using (◃→⊑)
open import OCF.Lean.YiFLBlock
```

## 合法性 (孩子下标也要合法)

```agda
mutual
  Leg′ : (ℓ : L) → Tr ℓ → Set
  Leg′ ℓ zero       = ⊤
  Leg′ ℓ (suc x)    = Leg′ ℓ x
  Leg′ ℓ (lim f)    = ((n : ℕ) → Leg′ ℓ (f n)) × ((n : ℕ) → ℓ ⊢ f n ◃ f (suc n))
  Leg′ ℓ (Ω p g)    = LegP ℓ p × ((z : Br ℓ p) → LegBr′ ℓ p z → Leg′ ℓ (g z))
  Leg′ ℓ (up x c y) = Leg′ ℓ x × LegI ℓ c × LegCh′ ℓ c y × (chL ℓ c ⊢ zero ◃ chT ℓ c y)

  LegP : (ℓ : L) → Pos ℓ → Set
  LegP (suc a)  t              = LegP⁼ a t
  LegP (lim g)  (n , t)        = LegP⁼ (g n) t
  LegP (Ωₗ k h) (inj₁ t)       = LegP⁼ k t
  LegP (Ωₗ k h) (inj₂ (c , t)) = Leg′ k c × LegP⁼ (h c) t

  LegP⁼ : (a : L) → Pos⁼ a → Set
  LegP⁼ a (inj₁ _) = ⊤
  LegP⁼ a (inj₂ p) = LegP a p

  LegBr′ : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Set
  LegBr′ (suc a)  t              z = LegBr⁼′ a t z
  LegBr′ (lim g)  (n , t)        z = LegBr⁼′ (g n) t z
  LegBr′ (Ωₗ k h) (inj₁ t)       z = LegBr⁼′ k t z
  LegBr′ (Ωₗ k h) (inj₂ (c , t)) z = LegBr⁼′ (h c) t z

  LegBr⁼′ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Set
  LegBr⁼′ a (inj₁ _) z = Leg′ a z
  LegBr⁼′ a (inj₂ p) z = LegBr′ a p z

  LegI : (ℓ : L) → Ch ℓ → Set
  LegI zero     ()
  LegI (suc a)  _ = ⊤
  LegI (lim g)  n = ⊤
  LegI (Ωₗ k h) c = Leg′ k c

  LegCh′ : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → Set
  LegCh′ (suc a)  _ y = Leg′ a y
  LegCh′ (lim g)  n y = Leg′ (g n) y
  LegCh′ (Ωₗ k h) c y = Leg′ (h c) y

mutual
  legFrom′ : (ℓ : L) (p : Pos ℓ) (x : Tr (at ℓ p)) → Leg′ (at ℓ p) x → LegBr′ ℓ p (fromBr ℓ p x)
  legFrom′ (suc a)  t              x h = legFrom⁼′ a t x h
  legFrom′ (lim g)  (n , t)        x h = legFrom⁼′ (g n) t x h
  legFrom′ (Ωₗ k h) (inj₁ t)       x e = legFrom⁼′ k t x e
  legFrom′ (Ωₗ k h) (inj₂ (c , t)) x e = legFrom⁼′ (h c) t x e

  legFrom⁼′ : (a : L) (t : Pos⁼ a) (x : Tr (at⁼ a t)) → Leg′ (at⁼ a t) x → LegBr⁼′ a t (fromBr⁼ a t x)
  legFrom⁼′ a (inj₁ _) x h = h
  legFrom⁼′ a (inj₂ p) x h = legFrom′ a p x h
```

## 各层的 Ω 树满足 `Leg′` (含塔各项与 Λ)

```agda
zl′ : ∀ {ℓ} (x : Tr ℓ) → Leg′ ℓ x → (zero ≡ x) ⊎ (ℓ ⊢ zero ◃ x)
zl′ zero h = inj₁ refl
zl′ (suc x) h with zl′ x h
... | inj₁ refl = inj₂ ◃s
... | inj₂ d    = inj₂ (◃t d ◃s)
zl′ (lim f) (hf , adj) with zl′ (f zero) (hf zero)
... | inj₁ e = inj₂ (subst (λ v → _ ⊢ v ◃ lim f) (sym e) (◃l zero))
... | inj₂ d = inj₂ (◃t d (◃l zero))
zl′ {ℓ} (Ω p g) (lp , h) with zl′ (g (fromBr ℓ p zero)) (h _ (legFrom′ ℓ p zero tt))
... | inj₁ e = inj₂ (subst (λ v → ℓ ⊢ v ◃ Ω p g) (sym e) ◃w)
... | inj₂ d = inj₂ (◃t d ◃w)
zl′ (up x c y) (hx , hi , hy , zy) with zl′ x hx
... | inj₁ refl = inj₂ (◃u zy)
... | inj₂ d    = inj₂ (◃t d (◃u zy))

z◃s′ : ∀ {ℓ} (x : Tr ℓ) → Leg′ ℓ x → ℓ ⊢ zero ◃ suc x
z◃s′ x h with zl′ x h
... | inj₁ refl = ◃s
... | inj₂ d    = ◃t d ◃s

Ωt-leg′ : (ℓ : L) → Leg′ ℓ (Ωt ℓ)
Ωt-leg′ zero     = tt
Ωt-leg′ (suc a)  = tt , λ z h → tt , tt , h , z◃s′ z h
Ωt-leg′ (lim g)  = cl , (λ n → ◃u (Ωt-nz (g (suc n))))
  where
  cl : (n : ℕ) → Leg′ (lim g) (seq (Ωt (lim g)) n)
  cl zero    = tt , tt , Ωt-leg′ (g zero) , Ωt-nz (g zero)
  cl (suc n) = cl n , tt , Ωt-leg′ (g (suc n)) , Ωt-nz (g (suc n))
Ωt-leg′ (Ωₗ k h) = tt , λ c lc → tt , lc , Ωt-leg′ (h c) , Ωt-nz (h c)

tw-leg′ : (n : ℕ) → Leg′ (tw n) (Ωt (tw n))
tw-leg′ n = Ωt-leg′ (tw n)

Λ-leg′ : Leg′ Λ (Ωt Λ)
Λ-leg′ = Ωt-leg′ Λ
```

## 以合法性为前提的路线

`RL.Rt′ (Ωₗ k h) = RL.Rt′ k × ((c : Tr k) → Leg′ k c → RL.Rt′ (h c))`. 合法树读出的偏移的路线对树递归; 结点一行用分支的合法性取分支的值的合法性.

```agda
module RL = Rts Leg′

mutual
  Rt-atᴸ : (ℓ : L) → RL.Rt′ ℓ → (p : Pos ℓ) → LegP ℓ p → RL.Rt′ (at ℓ p)
  Rt-atᴸ (suc a)  ρ         t              e        = Rt-at⁼ᴸ a ρ t e
  Rt-atᴸ (lim g)  (ρc , _)  (n , t)        e        = Rt-at⁼ᴸ (g n) (ρc n) t e
  Rt-atᴸ (Ωₗ k h) (ρk , ρc) (inj₁ t)       e        = Rt-at⁼ᴸ k ρk t e
  Rt-atᴸ (Ωₗ k h) (ρk , ρc) (inj₂ (c , t)) (lc , e) = Rt-at⁼ᴸ (h c) (ρc c lc) t e

  Rt-at⁼ᴸ : (a : L) → RL.Rt′ a → (t : Pos⁼ a) → LegP⁼ a t → RL.Rt′ (at⁼ a t)
  Rt-at⁼ᴸ a ρ (inj₁ _) e = ρ
  Rt-at⁼ᴸ a ρ (inj₂ p) e = Rt-atᴸ a ρ p e

mutual
  R↑ᴸ : (k : L) → RL.Rt′ k → (t : Tr k) → Leg′ k t → RL.RtP′ (↑ k t)
  R↑ᴸ k ρ zero       h          = tt
  R↑ᴸ k ρ (suc x)    h          = R↑ᴸ k ρ x h
  R↑ᴸ k ρ (lim f)    (hf , adj) = (λ n → R↑ᴸ k ρ (f n) (hf n)) , just (λ n → ◃→⊑ (adj n))
  R↑ᴸ k ρ (Ω p g)    (lp , h)   =
    Rt-atᴸ k ρ p lp , λ c lc → R↑ᴸ k ρ (g (fromBr k p c)) (h _ (legFrom′ k p c lc))
  R↑ᴸ k ρ (up x c y) (hx , hi , hy , zy) =
    RL.RtP′⊕ (↑ k x) (↑ch k c y) (R↑ᴸ k ρ x hx) (R↑chᴸ k ρ c hi y hy)

  R↑chᴸ : (k : L) → RL.Rt′ k → (c : Ch k) → LegI k c → (y : ChT k c) → LegCh′ k c y → RL.RtP′ (↑ch k c y)
  R↑chᴸ (suc a)  ρ         _ _  y h = R↑ᴸ a ρ y h
  R↑chᴸ (lim g)  (ρc , _)  n _  y h = R↑ᴸ (g n) (ρc n) y h
  R↑chᴸ (Ωₗ k h) (ρk , ρc) c hi y e = R↑ᴸ (h c) (ρc c hi) y e

Rtᴸ-tw : (n : ℕ) → RL.Rt′ (tw n)
Rtᴸ-tw zero    = tt
Rtᴸ-tw (suc n) = Rtᴸ-tw n , λ c lc → RL.Rt′⊕ (tw n) (↑ (tw n) c) (Rtᴸ-tw n) (R↑ᴸ (tw n) (Rtᴸ-tw n) c lc)

Rtᴸ-Λ : RL.Rt′ Λ
Rtᴸ-Λ = Rtᴸ-tw , just Adj-Λ
```

## 第 0 层: 合法性给出证据

第 0 层的树没有结点与嵌入, `Leg′` 的证明逐项就是 `E` 的证据 (相邻序取 `just`).

```agda
le₀ : (t : Tr zero) → Leg′ zero t → E zero t
le₀ zero        h          = tt
le₀ (suc t)     h          = le₀ t h
le₀ (lim f)     (hf , adj) = (λ n → le₀ (f n) (hf n)) , just adj
le₀ (Ω () _)    h
le₀ (up _ () _) h
```
