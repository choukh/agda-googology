# 同一折叠接口下，稳定树的搬运降低值

本篇是验收文件。对共享 `CountableFold` 的每个实例证明：
稳定性不保证世界上抬后折叠值保持，甚至不保证原值 ≤ 新值。
实例由 `WorldFoldRun.instance-fold` 给出。比较使用仓库已有的标准
可数树前序 `TLRuleSpec._≤_`，不是仅比较结构。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldObstructionValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; hl; _⊲_; hself; _⊞_)
open import OCF.Lean.NegFab6Idx
open import OCF.Lean.WorldFoldIf
open import OCF.Lean.WorldObstructionLift
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
import OCF.Align.TLRuleSpec as V

toA : Cd → A
toA hz = azero
toA (hs a) = asuc (toA a)
toA (hl f) = alim (λ n → toA (f n))

partial-zero : ∀ f → (∀ n → f n ≡ hz) → ∀ n → partial f n ≡ hz
partial-zero f eq zero = eq zero
partial-zero f eq (suc n) rewrite eq (suc n) = partial-zero f eq n

module For (F : CountableFold) where
  open CountableFold F

  lifted-zero : ∀ e (p : hs hz ⊲ e) → fold (spike e (OCF.Lean.Fab6Base.⊲ᴮ-tr rise p)) ≡ hz
  lifted-zero hz ()
  lifted-zero (hs e) p = zero-law
  lifted-zero (hl f) p = zero-law

  lifted-value-zero : toA (fold (lift rise low)) V.≤ azero
  lifted-value-zero rewrite node-law (λ e p → spike e (OCF.Lean.Fab6Base.⊲ᴮ-tr rise p)) =
    V.l≤ (λ n → subst (λ x → toA x V.≤ azero) (sym (partial-zero _ each n)) V.z≤)
    where
    each : ∀ n → (let s = orbit (hs hz) (λ e p → fold (spike e (OCF.Lean.Fab6Base.⊲ᴮ-tr rise p))) n
                  in fold (spike (proj₁ s) (OCF.Lean.Fab6Base.⊲ᴮ-tr rise (proj₂ s)))) ≡ hz
    each n = let s = orbit (hs hz) (λ e p → fold (spike e (OCF.Lean.Fab6Base.⊲ᴮ-tr rise p))) n
             in lifted-zero (proj₁ s) (proj₂ s)

  low-positive : asuc azero V.≤ toA (fold low)
  low-positive rewrite node-law spike = V.≤l zero first
    where
    first : asuc azero V.≤ toA (fold (ws (wz {hs hz})))
    first rewrite suc-law (wz {hs hz}) | zero-law {hs hz} = V.s≤ V.z≤

  no-lift-monotone : toA (fold low) V.≤ toA (fold (lift rise low)) → ⊥
  no-lift-monotone p = V.irr azero (V.≤-trans low-positive (V.≤-trans p lifted-value-zero))
```

`stable-low` 在配套文件给出；世界有字面证据 `rise`。因此否定不是
由不可满足的稳定性前提得到。仅否定该接口下对稳定树的一般世界单调律；
不否定加强输入分支单调性的方案，也不否定其他折叠。
翻译账：只新增关系与定理，不改树、折叠、稳定性接口。

无条件实例：把构造路的实际运行器代入上述证明。零值结论是
`alim (λ _ → azero) ≤ azero` 的值关系证明，不声称两者字面相等；
只有每个有限部分和逐一以 `partial-zero` 证明字面等于零。

```agda
open import OCF.Lean.WorldFoldRun using (instance-fold)
module Concrete = For instance-fold
```
