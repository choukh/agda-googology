# 最低一步的合法闭项

只在输出没有旧种类的 S⊥ 上，所有输入都折成合法可数树。
不把这个结果推广到任意 S；迭代高层所需的旧分支单调仍缺。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerCollapseClosed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf
open import OCF.Lean.TowerCollapseRun

module LegalSum (S : KS) where
  open Ops S
  partial-legal : ∀ f → (∀ n → LgB (f n)) → ∀ n → LgB (partial f n)
  partial-legal f l zero = l zero
  partial-legal f l (suc n) = Lg-⊞ (partial f n) (f (suc n)) (partial-legal f l n) (l (suc n))
  sum-legal : ∀ f → (∀ n → LgB (f n)) → LgB (sum f)
  sum-legal f l = (λ n → ⊞-fst (partial f n) (f (suc n))) , partial-legal f l

open Run S⊥
open Ops S⊥
open LegalSum S⊥

legal-fold : ∀ a → LgB (fold a)
legal-fold hz = tt
legal-fold (hs a) = sum-legal _ (λ n → legal-fold a)
legal-fold (hl f) = sum-legal _ (λ n → legal-fold (f n))
legal-fold (hΩ (inj₁ ()) g)
legal-fold (hΩ (inj₂ _) g) = sum-legal _ (λ n → legal-fold (g (orbit (λ c → fold (g c)) n)))

lowest-preserves : PreservesLegal S⊥ instance-fold
lowest-preserves = record { legal = λ a _ → legal-fold a }

Ω-input : HB (step S⊥)
Ω-input = hΩ (inj₂ tt) (λ c → up c)

T : Cd
T = fold Ω-input

legal-T : LgB T
legal-T = legal-fold Ω-input
```

该闭项与值分别交付：合法性已证，大小须由验收文件独立证明。
与 Fab3Typed/Fold1 的关系是既有一步折叠形状的简化实验，不是新强度。
差异是这里没有世界参数，ℕ-极限一律累加；这恰好暴露了高层合法性
需要补的具体义务，而不是消除了它。
