# 站间一步的第 0 站检查
不读记号；Φ 把零层树读成层号，再折叠该层的 Ω 树。构造合法，第 0 站的不等式编译通过。
第 1 行的形状据 `YiMTKeel.rowσᶻ` 重写，值改用 `YiVWVal`；不导入原文件。
一般步仍缺 `RowBridge n`；`source1-different` 只否定字面源层号相等，不否定值不等式或路线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSXStart where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab
import OCF.Lean.YiVWVal as V

ok↑ : (x : Tr zero) → Ok (zero ⊕ ↑ zero x)
ok↑ x = Ok⊕ zero (↑ zero x) tt (OkO↑ zero zero tt self x)

Φ⁺ : Tr zero → Tr⁺ zero
Φ⁺ x = ψ₀ᶻ (zero ⊕ ↑ zero x) (ok↑ x) (proj₁ (Ωt (zero ⊕ ↑ zero x)))

Φ : Tr zero → Tr zero
Φ x = proj₁ (Φ⁺ x)

head : Tr zero → ℕ → Tr zero
head (lim f _) n = f n
head _ n = zero

private
  right+ : (a b : Tr zero) → V.val zero b V.≼ V.val zero (a + b)
  right+ a zero      = V.z≼
  right+ a (suc b)   = V.s≼s (right+ a b)
  right+ a (lim f _) = V.l≼ (λ n → V.≼l n (right+ a (f n)))

selfPoint : (n : ℕ) → Tr (tw n)
selfPoint n = proj₁ (ψ (tw n) (Ok-tw n) (rbᶻ (tw n)) (B₀ (tw n)) (tw n) self
                      (Ωt (tw n)) (proj₁ (Ωt (tw n))))

rowLevel : ℕ → L
rowLevel n = tw n ⊕ ↑ (tw n) (selfPoint n)

rowValue : ℕ → Tr zero
rowValue n = proj₁ (ψ₀ᶻ (rowLevel n) (proj₂ (Ok-tw (suc n)) (selfPoint n))
                        (proj₁ (Ωt (rowLevel n))))

row1-shape : (n : ℕ) → head (twᶻ (suc n)) 1 ≡ twᶻ n + rowValue n
row1-shape n = refl

row1-bound : (n : ℕ) → V.val zero (rowValue n) V.≼ V.val zero (twᶻ (suc n))
row1-bound n = V.≼l 1 (right+ (twᶻ n) (rowValue n))

RowBridge : ℕ → Set
RowBridge n = V.val zero (Φ (twᶻ n)) V.≼ V.val zero (rowValue n)

bridge0 : RowBridge 0
bridge0 = V.≼-refl _

step-from-row : ∀ n → RowBridge n
  → V.val zero (Φ (twᶻ n)) V.≼ V.val zero (twᶻ (suc n))
step-from-row n b = V.≼-trans b (row1-bound n)

step0 : V.val zero (Φ (twᶻ 0)) V.≼ V.val zero (twᶻ 1)
step0 = step-from-row 0 bridge0

source0 : zero ⊕ ↑ zero (twᶻ 0) ≡ rowLevel 0
source0 = refl

source1-different : zero ⊕ ↑ zero (twᶻ 1) ≡ rowLevel 1 → ⊥
source1-different ()
```
