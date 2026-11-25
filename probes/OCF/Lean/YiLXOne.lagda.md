# 一般形式在实际前缀上的实例
不读记号；编译定理：`YiLXClimb.climbₒ` 在两条实际链的前缀 0、1 上给出值界（`prefix-zero`、`prefix-one`，与 `YiOFLocal.At.first`、`YiOGFirst.prefix-one` 同陈述）。
编译否定：源前缀 2 的底在零层槽位上有一个分量不满足 `Dry`（`source-wet`），所以拉回分量满足 `Dry` 的任何目标底都不满足 `climb` 的底前提（`no-base-dry`）；对齐到目标前缀 0、1 时无条件（`no-base-two-at0/1`），对齐到 2 时以 `Dry target-next` 为条件。
不否定前缀 2 的值比较、ActualMissing、Offset 或 Cover，只说 `Le` 形式的底前提在这里给不出前缀 2。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLXOne where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiVRRel
open import OCF.Lean.YiVRFold using (_⊴_)
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiOFPath as OP
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiOGState as St
import OCF.Lean.YiOGActual as A
import OCF.Lean.YiOGTransfer as X
import OCF.Lean.YiOGBaseAll as BA
import OCF.Lean.YiOGCanon as Can
import OCF.Lean.YiOGSelf as Self
open import OCF.Lean.YiLXClimb
```

## 前缀 0 与 1

两个孩子层号之间的字面路径是 `inc tt (inc tt self)`; 源层的合法性证据经等式 `refl` 换成拉回的证据 (`climbₒ`).

```agda
v0 : C.g 0 ⊑ C.h 0
v0 = inc tt (inc tt self)

base0 : St.G.base-at 0 ⊴ OP.pull-base v0 (St.T.base-at 0)
base0 i u _ = subst₂ (λ x y → Le i (proj₁ x) (proj₁ y))
  (sym (St.source-base-first i u)) (sym (St.target-base-first i (inc tt (inc tt u))))
  (Ωt≼ i (NoΩ≤ u (Can.source-no 0)))

dom0 : Dom (St.T.base-at 0)
dom0 i u _ = inj₁ (cong proj₁ (sym (St.target-base-first i u)))

beta0 : Le zero (proj₁ (St.G.start-at 0)) (proj₁ (St.T.start-at 0))
beta0 = subst₂ (λ x y → Le zero (proj₁ x) (proj₁ y))
  (sym St.source-start-first) (sym St.target-start-first) (refl₀ _)

row0 : Le zero (proj₁ (TB.ψ (C.g 0) (proj₂ C.og 0) (MT.rbᶻ (C.g 0)) (St.G.base-at 0) zero (C.wg 0) (St.G.start-at 0) (proj₁ (Ωt (C.g 0)))))
               (proj₁ (TB.ψ (C.h 0) (proj₂ St.oh 0) (MT.rbᶻ (C.h 0)) (St.T.base-at 0) zero (C.wh 0) (St.T.start-at 0) (proj₁ (Ωt (C.h 0)))))
row0 = climbₒ v0 (fS (fS fself)) (Can.source-no 0) (proj₂ St.oh 0) (proj₂ C.og 0) refl (MT.rbᶻ (C.g 0)) (MT.rbᶻ (C.h 0))
  (St.G.base-at 0) (St.T.base-at 0) base0 dom0 (St.G.start-at 0) (St.T.start-at 0) beta0

prefix-zero : V.val zero (proj₁ (St.G.piece 0)) V.≼ V.val zero (proj₁ (St.T.piece 0))
prefix-zero = subst₂ (λ x y → V.val zero (proj₁ x) V.≼ V.val zero (proj₁ y))
  (sym (St.G.state-row 0)) (sym (St.T.state-row 0)) (X.r→v row0)

v1 : C.g 1 ⊑ C.h 1
v1 = inc tt (inc tt self)

dom1 : Dom (St.T.base-at 1)
dom1 i u _ = inj₂ (St.target-base-growth 0 i u)

beta1 : Le zero (proj₁ (St.G.start-at 1)) (proj₁ (St.T.start-at 1))
beta1 = X.v→r (proj₁ (St.G.start-at 1)) (proj₁ (St.T.start-at 1)) A.beta-one

row1 : Le zero (proj₁ (TB.ψ (C.g 1) (proj₂ C.og 1) (MT.rbᶻ (C.g 1)) (St.G.base-at 1) zero (C.wg 1) (St.G.start-at 1) (proj₁ (Ωt (C.g 1)))))
               (proj₁ (TB.ψ (C.h 1) (proj₂ St.oh 1) (MT.rbᶻ (C.h 1)) (St.T.base-at 1) zero (C.wh 1) (St.T.start-at 1) (proj₁ (Ωt (C.h 1)))))
row1 = climbₒ v1 (fS (fS fself)) (Can.source-no 1) (proj₂ St.oh 1) (proj₂ C.og 1) refl (MT.rbᶻ (C.g 1)) (MT.rbᶻ (C.h 1))
  (St.G.base-at 1) (St.T.base-at 1) BA.base-transfer-one dom1 (St.G.start-at 1) (St.T.start-at 1) beta1

prefix-one : V.val zero (proj₁ (St.G.piece 1)) V.≼ V.val zero (proj₁ (St.T.piece 1))
prefix-one = subst₂ (λ x y → V.val zero (proj₁ x) V.≼ V.val zero (proj₁ y))
  (sym (St.G.state-row 1)) (sym (St.T.state-row 1)) (X.r→v row1)
```

## 前缀 2 的底前提

源第 2 前缀的底在零层槽位 `inc tt self` 上的分量是 `YiOGSelf.source-next`, 它的第一分支含 `source-carry`, 不满足 `Dry`; `Dry` 沿 `Le` 向下封闭 (`YiOGSelf.down`). 所以对任意目标层号、路径与目标底, 只要拉回的那个分量满足 `Dry`, `climb` 的底前提就不成立 (`no-base-dry`).

```agda
source-wet : Self.Dry (C.g 1) (proj₁ Self.source-next) → ⊥
source-wet d = Self.left-bad (subst (λ x → Self.Dry (C.g 1) (proj₁ x)) Self.source-carry-two (proj₂ d 0))

no-base-dry : ∀ {ℓ′} (v : C.g 2 ⊑ ℓ′) (B′ : F.Base ℓ′)
  → Self.Dry (C.g 1) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self)))
  → St.G.base-at 2 ⊴ OP.pull-base v B′ → ⊥
no-base-dry v B′ d hB = source-wet (Self.down (subst (λ x → Le (C.g 1) (proj₁ x) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self))))
  Self.source-query-two (hB (C.g 1) (inc tt self) tt)) d)
```

对齐到目标前缀 0、1 时, 那个分量是标准 Ω 树或 `YiOGSelf.right`, 二者满足 `Dry` (已证); 对齐到目标前缀 2 时是 `YiOGSelf.target-next`, 它是否满足 `Dry` 未证.

```agda
no-base-two-at0 : St.G.base-at 2 ⊴ OP.pull-base {b = C.h 0} self (St.T.base-at 0) → ⊥
no-base-two-at0 = no-base-dry self (St.T.base-at 0)
  (subst (λ x → Self.Dry (C.g 1) (proj₁ x)) (sym (St.target-base-first (C.g 1) (inc tt self))) Self.omega-two)

no-base-two-at1 : St.G.base-at 2 ⊴ OP.pull-base {b = C.h 1} (inc tt self) (St.T.base-at 1) → ⊥
no-base-two-at1 = no-base-dry (inc tt self) (St.T.base-at 1) Self.right-dry

v2 : C.g 2 ⊑ C.h 2
v2 = inc tt (inc tt self)

no-base-two : Self.Dry (C.g 1) (proj₁ Self.target-next) → St.G.base-at 2 ⊴ OP.pull-base v2 (St.T.base-at 2) → ⊥
no-base-two dt = no-base-dry v2 (St.T.base-at 2)
  (subst (λ x → Self.Dry (C.g 1) (proj₁ x)) (sym Self.target-query-two) dt)
```
