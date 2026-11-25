# φ 的配对否定: 量化域与各探针的位置

> 验收文件 (否定). 判决: 编译定理与有限测试. 证据 `Ev` 的量化过宽: 同一层号、同一棵树、同一目标, 证据路径取 `inu` 时 `phi` 保留结点, 取 `inb zero` 时折叠 (`ev-kept`, `ev-folds`, 有限测试); 两者都满足接口的律, 律不区分证据的好坏; 接口里讲保留的律只有塔的规范证据上的 `kstep` (本线的加强 `YiPhiNegK.KAll` 同样只在塔上).
> 规范域取 `R13Top` 的 `Top` (结点槽位都是本层下标层自身; 这里逐字重写了它的块上部分). 规范域内 `KAll` 只涉及下标层侧的槽位 (`top-inB`). 各否定的探针: `YiPhiNegB` 的在域内且合法; `YiPhiNegKSem` 的孩子层不合法、结点不在顶槽位 (`ksem-not-top`, `ksem-illegal`).
> 不否定什么: 不说接口错; 证据例子的对象不在规范域, 读作 "谓词太宽". 未做: `phi` 是否保持 `Top` (判断: 保留交出的槽位是基底的顶槽位).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPhiNegDom where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃t; Leg; _◃ₗ_; ◃ls; ◃ll; ◃lw; ◃lt; LegL)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold
open import OCF.Lean.YiPhiCheck using (isΩ; isLim)
open import OCF.Lean.YiPhiNegK using (InB; ib0; ibS; ibL; ibW; ibK)
import OCF.Lean.YiPhiNegB as NB
import OCF.Lean.YiPhiNegKSem as KS
```

## 规范域 (`R13Top` 的块上部分)

```agda
IsTop : (ℓ : L) → Pos ℓ → Set
IsTop (suc a)  (inj₁ _)        = ⊤
IsTop (suc a)  (inj₂ _)        = ⊥
IsTop (lim g)  _               = ⊥
IsTop (Ωₗ k h) (inj₁ (inj₁ _)) = ⊤
IsTop (Ωₗ k h) (inj₁ (inj₂ _)) = ⊥
IsTop (Ωₗ k h) (inj₂ _)        = ⊥

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
```

## 规范域内的 `KAll`

带见证 `InB` 的槽位若是顶槽位, 见证只能是 c = 0 (`ib0`) 或下标层侧 (`ibK`); 经孩子下行的见证不在规范域.

```agda
IsK0 : ∀ {a b t} → InB a b t → Set
IsK0 (ib0 _) = ⊤
IsK0 (ibK _) = ⊤
IsK0 _       = ⊥

top-inB : ∀ {a b t} (i : InB a b t) → IsTop (a ⊕ b) t → IsK0 i
top-inB (ib0 p)   it = tt
top-inB (ibS i)   ()
top-inB (ibL n i) ()
top-inB (ibW c i) ()
top-inB (ibK t)   it = tt
```

## 证据的量化 (有限测试)

层号 `ℓE = Ωₗ 1 (λ _ → Ωₗ 0 (λ _ → 1))`, 目标是下标层 1. 孩子层里的结点槽位在内层第 0 个孩子 (层号 1) 的层号 0 处, 严格在目标里. 两份证据只差 "下标层 1 在孩子层里的路径": `inu` (对一切内层孩子) 或 `inb zero` (指定内层第 0 个孩子).

```agda
ℓE : L
ℓE = Ωₗ (suc zero) (λ _ → Ωₗ zero (λ _ → suc zero))

evIn : Ev (Ωₗ zero (λ _ → suc zero))
evIn = tt , λ _ → ins self , tt

ε₁ ε₂ : Ev ℓE
ε₁ = tt , λ _ → inu (λ _ → self) , evIn
ε₂ = tt , λ _ → inb zero self , evIn

nodeE : Tr (Ωₗ zero (λ _ → suc zero))
nodeE = Ω (inj₂ (zero , inj₂ (inj₁ tt))) (λ _ → zero)

outE : Ev ℓE → Tr (suc zero)
outE ε = ψs ℓE ε (B₀ _) (suc zero) (ink self) (Ωt (suc zero)) (up zero zero nodeE)

ev-kept : isΩ (outE ε₁)
ev-kept = tt

ev-folds : isLim (outE ε₂)
ev-folds = tt

nodeE-not-top : Top (Ωₗ zero (λ _ → suc zero)) nodeE → ⊥
nodeE-not-top (() , _)
```

## 各探针在不在规范域

`YiPhiNegB`: c₀, cα α, 嵌入的树都在规范域且合法.

```agda
top-sucs : ∀ {ℓ} (m : ℕ) → Top ℓ (NB.sucs m)
top-sucs zero    = tt
top-sucs (suc m) = top-sucs m

top-bump : ∀ {ℓ} (b : Bool) (t : Tr ℓ) → Top ℓ t → Top ℓ (NB.bump b t)
top-bump true  t h = h
top-bump false t h = h

b-c₀-top : Top (tw 2) NB.c₀
b-c₀-top n = top-sucs (NB.double n)

b-cα-top : ∀ α → Top (tw 2) (NB.cα α)
b-cα-top α n = top-bump (α n) (NB.ev n) (top-sucs (NB.double n))

b-y₀-top : Top (NB.h₃ NB.c₀) NB.y₀
b-y₀-top = tt , tt , tt , λ _ _ → tt

leg-sucs : ∀ {ℓ} (m : ℕ) → Leg ℓ (NB.sucs m)
leg-sucs zero    = tt
leg-sucs (suc m) = leg-sucs m

leg-bump : ∀ {ℓ} (b : Bool) (t : Tr ℓ) → Leg ℓ t → Leg ℓ (NB.bump b t)
leg-bump true  t h = h
leg-bump false t h = h

step-bump : ∀ {ℓ} (b b′ : Bool) (t : Tr ℓ) → ℓ ⊢ NB.bump b t ◃ NB.bump b′ (suc (suc t))
step-bump false false t = ◃t ◃s ◃s
step-bump false true  t = ◃t ◃s (◃t ◃s ◃s)
step-bump true  false t = ◃s
step-bump true  true  t = ◃t ◃s ◃s

b-c₀-leg : Leg (tw 2) NB.c₀
b-c₀-leg = (λ n → leg-sucs (NB.double n)) , λ n → step-bump false false (NB.ev n)

b-cα-leg : ∀ α → Leg (tw 2) (NB.cα α)
b-cα-leg α = (λ n → leg-bump (α n) (NB.ev n) (leg-sucs (NB.double n)))
           , λ n → step-bump (α n) (α (suc n)) (NB.ev n)
```

`YiPhiNegKSem`: 结点不在顶槽位; 孩子层不合法 (第 0 项是极限层, 第 1 项是有限层, 不按 `◃ₗ` 步进).

```agda
ksem-not-top : ∀ α → Top (KS.hα α zero) (Ω (KS.t₂ α) (λ _ → zero)) → ⊥
ksem-not-top α (() , _)

FinL : L → Set
FinL zero     = ⊤
FinL (suc a)  = FinL a
FinL (lim _)  = ⊥
FinL (Ωₗ _ _) = ⊥

fin-down : ∀ {a b} → a ◃ₗ b → FinL b → FinL a
fin-down ◃ls       f = f
fin-down (◃ll n)   ()
fin-down ◃lw       ()
fin-down (◃lt d e) f = fin-down d (fin-down e f)

ksem-illegal : ∀ α → LegL (KS.hα α zero) → ⊥
ksem-illegal α (_ , adj) = fin-down (adj zero) tt
```
