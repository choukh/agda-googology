# 实际第二层最高反馈坐标带Reg

直接引用原M及已证明的SecondCoordinate动作，不复制fold。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedTargetRegClosure where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedTargetRegIf
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.BoundedFoldRun using (chain)
import OCF.Align.BoundedFoldValueMixed as M
import OCF.Align.BoundedMixedSecondCoordinate as D

reg-add : ∀ a b → Reg a → Reg b → Reg (a ⊞ b)
reg-add a hz ra rb = ra
reg-add a (hs b) ra rb = reg-add a b ra rb
reg-add a (hl f) ra rb = λ n → reg-add a (f n) ra (rb n)
reg-add a (hΩ (inj₁ κ) g) ra rb = λ c → reg-add a (g c) ra (rb c)
reg-add a (hΩ (inj₂ _) g) ra (mo , rb) =
  (λ bc bd p → ⊞-⊲ a (mo bc bd p)) , (λ c → reg-add a (g c) ra (rb c))

reg-partial : ∀ f → (∀ n → Reg (f n)) → ∀ n → Reg (Ops.partial Layer f n)
reg-partial f r zero = r zero
reg-partial f r (suc n) = reg-add _ _ (reg-partial f r n) (r (suc n))

reg-base : ∀ c → Reg (D.base c)
reg-base hz = tt
reg-base (hs c) = reg-partial _ (λ n → reg-base c)
reg-base (hl f) = λ n → reg-base (f n)
reg-base (hΩ κ g) = λ c → reg-base (g c)

reg-branch : ∀ c → Reg (D.branch c)
reg-branch hz = reg-base _
reg-branch (hs c) = reg-partial _ (λ n → reg-branch c)
reg-branch (hl f) = λ n → reg-branch (f n)
reg-branch (hΩ κ g) = λ c → reg-branch (g c)

reg-prefix : Reg D.Actual.prefix
reg-prefix = (λ bc bd p → D.branch-position p) , reg-branch

module Action (A : HB M.S) where
  module E = D.Action A
  reg-run : Reg E.prefix → ∀ c → Reg c → Reg (E.run c)
  reg-run ra hz r = ra
  reg-run ra (hs c) r = reg-partial _ (λ n → reg-run ra c r)
  reg-run ra (hl f) r = λ n → reg-run ra (f n) (r n)
  reg-run ra (hΩ (inj₁ κ) g) r = λ c → reg-run ra (g c) (r c)
  reg-run ra (hΩ (inj₂ _) g) (mo , r) =
    (λ bc bd p → E.position (mo bc bd p)) , (λ c → reg-run ra (g c) (r c))

  reg-chain : Reg E.prefix → ∀ n → Reg (chain E.run n)
  reg-chain ra zero = tt
  reg-chain ra (suc n) = reg-add _ _ (reg-chain ra n) (reg-run ra _ (reg-chain ra n))

module Actual = Action (M.sums 1)
actual-reg : ∀ n → Reg (chain D.Actual.run n)
actual-reg = Actual.reg-chain reg-prefix
```

reg-prefix不是常值或零前缀；它含真实第1层新Ω，其分支由原M.sums1
的全部旧前缀产生。此证书与actual-coordinate-legal共同覆盖全部实际坐标。
