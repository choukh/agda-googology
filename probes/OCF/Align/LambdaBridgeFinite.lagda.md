# 回灌的有限轨道给出完整值界

验收文件，不改树或折叠。先消除非恒定坐标读取就会提升序数值的错觉：
若起点有限且每个有限坐标的分支输出仍有限，那么整个回灌不超过 ω。
若所有被读分支又至少为 1，则恰好为 ω。定理对分支函数统一，
不按具体轨道逐项展开。其前提由 `WorldFoldClosed.coordinate-node` 实例化。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LambdaBridgeFinite where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; _⊞_; _⊲_)
open import OCF.Lean.WorldFoldIf using (orbit; partial; series; feedback)
open import OCF.Lean.WorldFoldRun using (run)
open import OCF.Lean.WorldFoldClosed using (nat; ω; U; embed)
open import OCF.Lean.NegFab6Sim using (_≼_; z≼; s≼s; l≼; ≼l; ≼-refl; ⊞-mono)

data Finite : Cd → Set where
  fz : Finite hz
  fs : ∀ {a} → Finite a → Finite (hs a)

height : ∀ {a} → Finite a → ℕ
height fz = zero
height (fs p) = suc (height p)

height-correct : ∀ {a} (p : Finite a) → nat (height p) ≡ a
height-correct fz = refl
height-correct (fs p) = cong hs (height-correct p)

finite≤ω : ∀ {a} → Finite a → a ≼ ω
finite≤ω p = subst (λ a → a ≼ ω) (height-correct p)
  (≼l (height p) (≼-refl (nat (height p))))

finite-add : ∀ {a b} → Finite a → Finite b → Finite (a ⊞ b)
finite-add p fz = p
finite-add p (fs q) = fs (finite-add p q)

finite-partial : ∀ f → (∀ n → Finite (f n)) → ∀ n → Finite (partial f n)
finite-partial f p zero = p zero
finite-partial f p (suc n) = finite-add (finite-partial f p n) (p (suc n))

module OrbitBound (B : Cd) (h : (e : Cd) → B ⊲ e → Cd)
                  (base : Finite B)
                  (closed : ∀ e p → Finite e → Finite (h e p)) where
  finite-orbit : ∀ n → Finite (proj₁ (orbit B h n))
  finite-orbit zero = base
  finite-orbit (suc n) = finite-add base
    (fs (closed (proj₁ (orbit B h n)) (proj₂ (orbit B h n)) (finite-orbit n)))

  finite-output : ∀ n → Finite (h (proj₁ (orbit B h n)) (proj₂ (orbit B h n)))
  finite-output n = closed _ _ (finite-orbit n)

  upper : feedback B h ≼ ω
  upper = l≼ (λ n → finite≤ω (finite-partial _ finite-output n))

positive-partial : ∀ f → (∀ n → hs hz ≼ f n) → ∀ n → nat (suc n) ≼ partial f n
positive-partial f p zero = p zero
positive-partial f p (suc n) = ⊞-mono (positive-partial f p n) (p (suc n))

positive-series : ∀ f → (∀ n → hs hz ≼ f n) → ω ≼ series f
positive-series f p = l≼ lower
  where
  lower : ∀ n → nat n ≼ series f
  lower zero = z≼
  lower (suc n) = ≼l n (positive-partial f p n)

embed-finite : ∀ {B a} → Finite a → Finite (run (embed {B} a))
embed-finite fz = fz
embed-finite (fs p) = fs (embed-finite p)

module UBound = OrbitBound hz (λ e p → hs (run (embed {hs e} e))) fz
  (λ e p fe → fs (embed-finite fe))

U≤ω : U ≼ ω
U≤ω = UBound.upper

ω≤U : ω ≼ U
ω≤U = positive-series _ (λ n → s≼s z≼)

U-value : (U ≼ ω) × (ω ≼ U)
U-value = U≤ω , ω≤U
```

翻译账：没有新增构造子或记号规则。有限轨道不变量来自实际回灌操作；
它能给闭项完整值，不把“坐标越来越复杂”的描述当强度。
本定理不否定其他回灌或世界索引路线；要越过本上界，至少须使这组
有限闭包前提在实际轨道上不再成立。ψ₀Λ 的强度桥仍未给出。
