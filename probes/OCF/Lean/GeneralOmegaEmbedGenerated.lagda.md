# 原地板的后继与可数并闭包

本篇直接使用原flL与ΣF，不复制地板。证书标明已建立的层号域：lz、
ls与ll闭包。它含任意有限后继塔及其完整可数并，也含实际twL的第1站。
尚不含一般lΩ；不可将该域冒称完整ΩL/twL闭包。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedGenerated where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (ΩL; twL)
open import OCF.Lean.LHRecFl using (flL; ΣF)
open import OCF.Lean.GeneralOmegaEmbedIf
open import OCF.Lean.GeneralOmegaEmbedRun
open import OCF.Lean.GeneralOmegaEmbedContext using (Embedding; put; identity; map)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
import OCF.Lean.GeneralOmegaConsumeRun as R

up-both : ∀ {x y a b} → Coded x y a b → Coded (ls x) (ls y) (up a) (up b)
up-both cz = cz
up-both (cs p) = cs (up-both p)
up-both (cl p) = cl (λ n → up-both (p n))
up-both (co p) = co (λ q → up-both (p q))

up-right : ∀ {x y a b} → Coded x y a b → Coded x (ls y) a (up b)
up-right cz = cz
up-right (cs p) = cs (up-right p)
up-right (cl p) = cl (λ n → up-right (p n))
up-right (co p) = co (λ q → up-right (p q))

sum-both : ∀ {f g n m a b} → Coded (f n) (g m) a b →
  Coded (OCF.Lean.LHRecTy.ll f) (OCF.Lean.LHRecTy.ll g) (ι n a) (ι m b)
sum-both cz = cz
sum-both (cs p) = cs (sum-both p)
sum-both (cl p) = cl (λ n → sum-both (p n))
sum-both (co p) = co (λ q → sum-both (p q))

branch-right : ∀ {x k g e a b} → Coded x (g e) a b →
  Coded x (lΩ k g) a (ι {IxL k} {FXL k g} (inj₂ e) b)
branch-right cz = cz
branch-right (cs p) = cs (branch-right p)
branch-right (cl p) = cl (λ n → branch-right (p n))
branch-right (co p) = co (λ q → branch-right (p q))

data Generated : LH → Set where
  base : Generated lz
  successor : ∀ {x} → Generated x → Generated (ls x)
  supremum : ∀ {f} → (∀ n → Generated (f n)) → Generated (OCF.Lean.LHRecTy.ll f)

floor-related : ∀ {x} → Generated x → Coded x x (flL x) (flL x)
sums-related : ∀ {f} → (∀ n → Generated (f n)) → ∀ n →
  Coded (OCF.Lean.LHRecTy.ll f) (OCF.Lean.LHRecTy.ll f) (ΣF f n) (ΣF f n)
floor-related base = cz
floor-related {ls x} (successor p) = co (λ q →
  up-both (add (floor-related p) (pure-related x x (leg-same q))))
floor-related (supremum p) = cl (sums-related p)
sums-related p zero = sum-both (floor-related (p zero))
sums-related p (suc n) = add (sums-related p n) (sum-both (floor-related (p (suc n))))

floor-up : ∀ {x} → Generated x →
  Same (R.run x (flL x)) (R.run (ls x) (up (flL x)))
floor-up p = sound (up-right (floor-related p))

floor-branch : ∀ {k g} e → Generated (g e) →
  Same (R.run (g e) (flL (g e)))
    (R.run (lΩ k g) (ι {IxL k} {FXL k g} (inj₂ e) (flL (g e))))
floor-branch e p = sound (branch-right (floor-related p))

finite : ℕ → LH
finite zero = lz
finite (suc n) = ls (finite n)
finite-generated : ∀ n → Generated (finite n)
finite-generated zero = base
finite-generated (suc n) = successor (finite-generated n)
finite-sup-up = floor-up (supremum finite-generated)
first-tower-up : Same (R.run (twL 1) (flL (twL 1)))
  (R.run (ls (twL 1)) (up (flL (twL 1))))
first-tower-up = floor-up (successor base)
```

floor-up在整个Generated域连接真实A与低层地板输出，比较的是完整
回灌输出，不只是首项。floor-branch可进入任意原lΩ层的实际分量。
一般lΩ的自身地板涉及θ(code)，不同反馈可产生不同分量编号；所需
编号对应层的相关性尚未由本篇Generated提供，不能据此关闭该路线。
