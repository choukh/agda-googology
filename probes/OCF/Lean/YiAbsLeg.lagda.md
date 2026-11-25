# 抽象理论 (五): 合法块填进同一个框架

> 验收文件 (实填). 判决: 编译定理, 无前提. 合法性进块的原型 (`YiLegBlock`, `YiLegFold`: 树与第一位置序归纳-归纳, 嵌入自带 "孩子非零", 偏移带 "非零" 证明) 填进 `YiAbsFrame` 的同一对记录 (`blkᴸ`, `foldᴸ`); `Hand` 在后继与 ℕ 极限层号上成立, `HandU` 在三种层号上成立, `Mono` 成立, `Pres` 平凡 (合法是类型).
> 所以框架上的定理对合法块不用重证: `leg-wdec`, `leg-branch` 是 `hand→wdec`, `branch→wdec` 在这个实例上的陈述.
> 不给出什么: 合法块上没有构造 `Hand (Ωₗ k h)` 的探针 (`leg-wdec` 的前提 `Probe` 在这里没有实例); 没有值定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsLeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
import OCF.Lean.YiLegCheck as C
open import OCF.Lean.YiAbsObs using (WDec)
open import OCF.Lean.YiAbsFrame
```

## 块

孩子层的树连同 "非零" 的推导一起作嵌入的参数.

```agda
hdΩ : ∀ {ℓ} → Tr ℓ → Bool
hdΩ (Ω _ _) = true
hdΩ _       = false

ChT⁺ : (ℓ : L) → Ch ℓ → Set
ChT⁺ ℓ c = Σ (ChT ℓ c) (RCh ℓ c (chZ ℓ c))

chTᴸ : (ℓ : L) (c : Ch ℓ) → ChT⁺ ℓ c → Tr (chL ℓ c)
chTᴸ (suc a)  _ (y , _) = y
chTᴸ (lim g)  n (y , _) = y
chTᴸ (Ωₗ k h) c (y , _) = y

incᴸ : ∀ {j} (ℓ : L) (c : Ch ℓ) → j ≤ chL ℓ c → j ≤ ℓ
incᴸ (suc a)  _ w = ins w
incᴸ (lim g)  n w = inl n w
incᴸ (Ωₗ k h) c w = inb c w

incUᴸ : ∀ {j} (ℓ : L) → Ch ℓ → ((c : Ch ℓ) → j ≤ chL ℓ c) → j ≤ ℓ
incUᴸ (suc a)  _ ws = ins (ws tt)
incUᴸ (lim g)  _ ws = inlu ws
incUᴸ (Ωₗ k h) _ ws = inu ws

blkᴸ : Block
blkᴸ = record
  { Lv = L ; Tr = Tr ; Ch = Ch ; chL = chL ; ChT = ChT⁺ ; chT = chTᴸ
  ; _⊑_ = _≤_ ; self = self ; inc = incᴸ ; incU = incUᴸ
  ; up = λ x c ye → up x c (proj₁ ye) (proj₂ ye) ; hd = hdΩ
  ; _◃_ = λ {ℓ} x y → ℓ ⊢ x ◃ y ; Leg = λ _ → ⊤ }
```

## 折叠

```agda
Bsᴸ : L → Set
Bsᴸ ℓ = Ev ℓ × Rt ℓ × Base ℓ

Btᴸ : L → Set
Btᴸ j = Σ (Tr j) λ β → j ⊢ zero ◃ β

dnᴸ : (ℓ : L) → Bsᴸ ℓ → (c : Ch ℓ) → Tr ℓ → Bsᴸ (chL ℓ c)
dnᴸ (suc a)  (ε , ρ , B) _ x = ε , ρ , dS a ε ρ B x
dnᴸ (lim g)  (ε , ρ , B) n x = ε n , proj₁ ρ n , dL g ε ρ B n x
dnᴸ (Ωₗ k h) (ε , ρ , B) c x = proj₂ (proj₂ ε c) , proj₂ ρ c , dW k h ε ρ B c x

foldᴸ : Fold blkᴸ
foldᴸ = record
  { Bs   = Bsᴸ
  ; LegB = λ _ _ → ⊤
  ; Bt   = Btᴸ
  ; LegT = λ _ _ → ⊤
  ; ψ    = λ ℓ b j w β x → ψs ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w (proj₁ β) (proj₂ β) x
  ; ψβ   = λ ℓ b j w β x → ψs ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w (proj₁ β) (proj₂ β) x
                         , nzs ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w (proj₁ β) (proj₂ β) x
  ; dn   = dnᴸ }

open Fold foldᴸ using (Hand; HandU; Mono; Pres; Probe; Offᴾ)

hand-suc : (a : L) → Hand (suc a)
hand-suc a (ε , ρ , B) j c w (β , nβ) x (y , e) = C.J2-suc a ε ρ B j w β nβ x y e

hand-lim : (g : ℕ → L) → Hand (lim g)
hand-lim g (ε , ρ , B) j n w (β , nβ) x (y , e) = C.J2-lim g ε ρ B n j w β nβ x y e

handU-suc : (a : L) → HandU (suc a)
handU-suc a (ε , ρ , B) j c₁ ws (β , nβ) x c (y , e) = C.J2-suc a ε ρ B j (ws tt) β nβ x y e

handU-lim : (g : ℕ → L) → HandU (lim g)
handU-lim g (ε , ρ , B) j c₁ ws (β , nβ) x n (y , e) = C.J2-limu g ε ρ B j ws β nβ x n y e

handU-Ω : (k : L) (h : Tr k → L) → HandU (Ωₗ k h)
handU-Ω k h (ε , ρ , B) j c₁ ws (β , nβ) x c (y , e) = C.J2-Ωu k h ε ρ B j ws β nβ x c y e

mono : Mono
mono ℓ (ε , ρ , B) j w (β , nβ) d = monos ℓ ε ρ B j w β nβ d

pres : Pres
pres ℓ b lb j w β lβ x lx = tt
```

## 框架的否定在合法块上的陈述

```agda
leg-wdec : ∀ {ℓ} → Hand ℓ → (P : Probe ℓ) → Offᴾ P → (c′ : Ch ℓ) → WDec (Probe.c₀ P ≡ c′)
leg-wdec = Fold.hand→wdec foldᴸ

leg-branch : (ℓ : L) (b : Bsᴸ ℓ) (j : L) (β : Btᴸ j) (c₀ : Ch ℓ) (w : (c′ : Ch ℓ) → j ≤ chL ℓ c′) (o : Tr ℓ)
  → hdΩ (ψs ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j (incᴸ ℓ c₀ (w c₀)) (proj₁ β) (proj₂ β) o) ≡ true
  → ((c′ : Ch ℓ) → (c₀ ≡ c′ → ⊥)
      → hdΩ (ψs ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j (incᴸ ℓ c′ (w c′)) (proj₁ β) (proj₂ β) o) ≡ false)
  → (c′ : Ch ℓ) → WDec (c₀ ≡ c′)
leg-branch = Fold.branch→wdec foldᴸ
```
