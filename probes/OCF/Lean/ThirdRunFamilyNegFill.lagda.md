# 真实运行族不能免费补成“界外为零”的全目标族

共享 `ThirdRunFamilyIf.RunFamily` 只要求带目标位置的原运行；本篇不否定它。
另写候选桥 `ZeroFill`：在界内逐字给原运行结果，在界外填零。
对原 `Sb 0`、合法源高度、原零输入、原 `Er/Φ` 的整参数族，若总能填此桥，
便推出 WLPO。这里不是 LPO：非零观察只排除“没有位置”，不擅自消去双重否定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRunFamilyNegFill where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
import OCF.Lean.ThirdRunFamilyIf as Shared
open import OCF.Lean.NegThirdPre using (Bα; Lg-Bα; →one⊲; one⊲→)

one : ∀ {S} → HB S
one = hs hz

module ZeroSource (M : Cd) (lm : LgB M) where
  module S = Shared.Source 0 tt tt hz M lm
  open S

  -- 本篇使用原运行器的非空实例，exact 和 shape 都实填。
  actual : RunFamily hz tt
  actual = record
    { run = λ t pt b → F.F.Φ E.Er M (F.F.wfC E.Er M) lm t pt b hz tt
    ; exact = λ t pt b → refl
    ; shape = λ t pt b → F.F.Sh-Φ E.Er M (F.F.wfC E.Er M) lm t pt b hz tt }

  seed : ∀ t → F.GT t
  seed t = hz , tt

  output : ∀ t → t ⊲ M → HB (Tw S⊥ t)
  output t pt = proj₁ (RunFamily.run actual t pt (seed t))

  output-one : ∀ t pt → output t pt ≡ one
  output-one t pt = refl

  record ZeroFill : Set where
    field
      fill : ∀ t → HB (Tw S⊥ t)
      inside : ∀ t (pt : t ⊲ M) → fill t ≡ output t pt
      outside : ∀ t → ¬ (t ⊲ M) → fill t ≡ hz

  -- 不要求外域零时，本实际运行族有总扩张；并非否定任何全族。
  full-one : ∀ t → HB (Tw S⊥ t)
  full-one t = one

  full-one-exact : ∀ t pt → full-one t ≡ output t pt
  full-one-exact t pt = refl

  zero-outside : ∀ t → ¬ (t ⊲ M) → (hz {Tw S⊥ t}) ≡ hz
  zero-outside t absent = refl

TotalZeroFill : Set
TotalZeroFill = ∀ M lm → ZeroSource.ZeroFill M lm

WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)

is-zero : ∀ {S} → HB S → Bool
is-zero hz = true
is-zero (hs _) = false
is-zero (hl _) = false
is-zero (hΩ _ _) = false

false≢true : ¬ (false ≡ true)
false≢true ()

not-true : ∀ b → ¬ (b ≡ true) → b ≡ false
not-true false nt = refl
not-true true nt = ⊥-elim (nt refl)

all-false-no-position : ∀ α → (∀ n → α n ≡ false) → ¬ (one ⊲ Bα α)
all-false-no-position α all p with one⊲→ α p
... | n , eq = false≢true (trans (sym (all n)) eq)

zero-fill→WLPO : TotalZeroFill → WLPO
zero-fill→WLPO total α = split (is-zero result) refl
  where
  module Z = ZeroSource (Bα α) (Lg-Bα α)
  open Z.ZeroFill (total (Bα α) (Lg-Bα α))

  result : HB (Tw S⊥ (one {S⊥}))
  result = fill one

  hit-result : ∀ n → α n ≡ true → is-zero result ≡ false
  hit-result n eq = cong is-zero (inside one (→one⊲ α n eq))

  empty-result : (∀ n → α n ≡ false) → is-zero result ≡ true
  empty-result all = cong is-zero (outside one (all-false-no-position α all))

  split : ∀ b → is-zero result ≡ b →
    (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)
  split true eq = inj₁ λ n → not-true (α n) λ hit →
    false≢true (trans (sym (hit-result n hit)) eq)
  split false eq = inj₂ λ all → false≢true (trans (sym eq) (empty-result all))
```

## 合同确有个别实例，失败的是统一补齐要求

源高度为零时，可直接按目标的构造子填充，不需要判任意目标的隶属关系。
全源参数族中的合法世界、源树与路径要求都由上面的 `ZeroSource.actual`
和 `Lg-Bα` 提供；没有把不满足前提的假运行器塞进否定证明。

```agda
module AtZero where
  module Z = ZeroSource hz tt

  fill : ∀ t → HB (Tw S⊥ t)
  fill hz = one
  fill (hs _) = hz
  fill (hl _) = hz
  fill (hΩ () _)

  inside : ∀ t (p : t ⊲ hz) → fill t ≡ Z.output t p
  inside .hz hself = refl

  outside : ∀ t → ¬ (t ⊲ hz) → fill t ≡ hz
  outside hz absent = ⊥-elim (absent hself)
  outside (hs _) absent = refl
  outside (hl _) absent = refl
  outside (hΩ () _) absent

  instance-zero-fill : Z.ZeroFill
  instance-zero-fill = record { fill = fill ; inside = inside ; outside = outside }
```

结论只针对零外补齐合同。若“外域保原界”的通用桥允许原界族恒零，
它也必须覆盖这个实例，因而继承同一 WLPO 后果。这里没有否定不约束
外域的扩张（`full-one` 就是正例），也没有否定仅在带字面位置的目标域
更新世界。后者应直接消费 `run t pt`，不需要猜测 `pt` 是否存在。
