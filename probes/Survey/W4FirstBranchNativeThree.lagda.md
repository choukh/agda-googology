# 标准旧 Ω₃ 对角的第一次非零返回

第四层。标准底的旧三级折叠恰值 ψ₀(Ω₃)。其第 1 个基本列项包含首两行之和，已由真实 W4 第三级运行覆盖。第二个实参中 Ω₂ 的任意有限倍数统一用 2k 重编号。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchNativeThree where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≈ᵛ_; _≼_; ≼-refl; ≼-trans; ≼l; l≼; 1≼ψ⁰; ≅→≼; +-mono)
open import OCF.BTBO using (module Ord-Ord)
import OCF.Lean.YiLegBlock as O
import OCF.Lean.YiLegOps as A
import OCF.Lean.YiLegFold as G
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLSFold as Sim
import OCF.Lean.YiLSRel as Rel
import OCF.Lean.YiLSRead as V
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Assoc as Assoc
import OCF.Lean.YiXVCan2Add as Add
import OCF.Lean.YiXVCan2Psi as Pow
import OCF.Lean.YiXVCan2Plus as Plus
import OCF.Lean.YiXVCan2Self as Self
import OCF.Lean.YiXVCan2Gamma as Gamma
import OCF.Lean.YiXVCan2Domain as D
import OCF.Lean.YiXVCan2Zero as Z
import OCF.Lean.YiXVCan2Sem as Sem
import OCF.Lean.YiXVCarry as Carry
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as Ops
import OCF.Lean.YiXVCan2Ceiling as Frame
import B12Omega3Ref as Target
import B12BtboCut as Cut
import B12Terminal as T
import B12ActualSlots as Slots
import B18OrbitRows as Paid
import WVOne as W
import WKShape as Shape
import W4Fold as Native

two three : O.L
two = O.suc (O.suc O.zero)
three = O.suc two
base : G.Base three
base = G.B₀ three
E : G.Base two
E = G.dS two tt tt base O.zero

standard : Cut.finite 3 ≼ V.read (G.ψ⊥ three tt tt base (A.Ωt three))
standard = Sim.lower (Sim.n+ (Sim.n+ (Sim.n+ Sim.n0))) tt tt base (Sim.ok-B₀ three)
  (Rel.cs (Rel.cs (Rel.cs Rel.cz)))

old-whole = V.read (G.ψ⊥ three tt tt base (A.Ωt three))

first-positive : O.Tr two
first-positive = A.next (A.Ωt two) (A.Ωt-nz two)
operand = G.ψ⊥ two tt tt E first-positive
old-row = G.ψ⊥ two tt tt E (O.suc first-positive)

Ω₁-upper : I.U.U (A.Ωt (O.suc O.zero)) (F.ψ₁ F.Ω₂)
Ω₁-upper = I.U.uw (Ops.Gd-ψ₁ Ops.Gd-Ω) Carry.ΩψU (R.≤l 0 (Ops.reflₚ (Ops.Gd-ψ₁ Ops.Gd-Ω)))

module Rows = Frame.Frame I.D1 base I.zeroU refl (1≼ψ⁰ F.Ω₂) (1≼ψ⁰ F.Ω₂) (Ω₁-upper , H.Ω-closed)

actual-index : Rows.rows 1 ≡ old-row
actual-index = refl

```

旧对角回灌从零起，第 1 行使用自身种子 Ω₂ 对 1 的返回；旧基本列的第 1 项还要加上第 0 行。

```agda
prefix-index : V.read (A.cum Rows.rows 1) ≡ Target.at old-whole 1
prefix-index = refl

seed : D.U.U (A.Ωt two) (Pow.Ψ (Gamma.Γ 4 L.+ F.Ω₂))
seed = D.U.uw D.ΩψU (Pow.mono (Add.rightE (Pow.base (Gamma.Γ 3) (Gamma.good 4)) C.Gd-Ω₂
  (Add.good (Gamma.good 4) C.Gd-Ω₂)))

module SelfFold = Self.Fold I.D1 E (Gamma.Γ 4) (Gamma.good 4) (A.Ωt two) (A.Ωt-nz two) seed
chain-bound : ∀ n → D.U.U (Rows.c n) (Gamma.Γ (D.idx n))
chain-bound zero = D.U.uw D.U.uz (Pow.base (Gamma.Γ 3) (Gamma.good 4))
chain-bound (suc n) = D.U.uw (SelfFold.result (C.gs (Gamma.good (D.idx n))) (D.U.us (chain-bound n)))
  (Pow.mono (C.trans (Add.plus (D.floor n) (Gamma.inv (D.idx n))) (Gamma.step (D.idx n) (C.refl (Gamma.good (D.idx n))))))

exact : Cut.finite 3 ≈ᵛ old-whole
exact = standard , Rows.Run.ceiling chain-bound

module Interpretation = Sem.Sem I.D1 E (1≼ψ⁰ F.Ω₂) (1≼ψ⁰ F.Ω₂) (Ω₁-upper , H.Ω-closed) I.zeroU refl
module Out = Sem.Value I.D1 E

double : F.T₂
double = F.Ω₂ L.+ F.Ω₂
good-double = Add.good C.Gd-Ω₂ C.Gd-Ω₂
copies = Ord-Ord.iter (double L.+_) L.zero
twice : ℕ → ℕ
twice zero = zero
twice (suc k) = suc (suc (twice k))

bound : ∀ k → C.Le (copies k) (Target.left (twice k))
bound zero = C.refl C.gz
bound (suc k) = C.trans (Assoc.same C.Gd-Ω₂ C.Gd-Ω₂ (Pow.good-iter good-double k))
  (Add.plus C.Ω₂-refl (Add.plus C.Ω₂-refl (bound k)))

upper : V.read operand ≼ Target.inside
upper = ≼-trans {b = L.ψ⁰ (L.lim copies)}
  (Out.Out.bot≤ (Interpretation.upper (C.gl (Pow.good-iter good-double))
    (Plus.Closure.next I.D1 (A.Ωt-nz two) good-double D.ΩU)))
  (l≼ λ k → ≼l (twice k) (Z.mono₀ (bound k)))

paid-operand : ∀ (r : T.Run Shape.lvl3) → Slots.Covered r → V.read operand ≼ W.read (T.value r)
paid-operand r cv = ≼-trans {b = Target.inside} upper
  (≼-trans {b = Target.at (Cut.finite 3) 1} Target.inside-below-one (Paid.At.whole r cv))

```

每次对参照取正有限倍数的极限。第二次得到旧第 1 行的界，第三次容纳两行之和；这个切片已在 W4 的完整第三层返回内。

```agda
good-power : ∀ n → C.Gd (Target.finitePower n)
good-power zero = C.Gd-Ω₂
good-power (suc n) = C.gl (Pow.good-iter (good-power n))

extend-power : ∀ n → C.Le (Target.finitePower n) (Target.finitePower (suc n))
extend-power n = C.pack (good-power n) (good-power (suc n)) (C.lr 1 (C.refl (good-power n)))

positive : ∀ n → C.Le C.one (Target.finitePower n)
positive zero = Pow.pos-Ω
positive (suc n) = C.trans (positive n) (extend-power n)

raise-power : ∀ n → C.Le (L.suc (Target.finitePower n)) (Target.finitePower (suc n))
raise-power n = Pow.strict (good-power n) (positive n)

to-first-power : C.Le (L.lim copies) (Target.finitePower 1)
to-first-power = C.pack (C.gl (Pow.good-iter good-double)) (good-power 1) (C.ll λ k →
  C.pack (Pow.good-iter good-double k) (good-power 1) (C.lr (twice k) (bound k)))

at-second-power : V.read old-row ≼ L.ψ⁰ (Target.finitePower 2)
at-second-power = Out.Out.bot≤ (Interpretation.upper (good-power 2)
  (D.U.uw (D.U.us (Plus.Closure.next I.D1 (A.Ωt-nz two) good-double D.ΩU))
    (C.trans (C.s≤ to-first-power) (raise-power 1))))

zero-at-second : V.read (Rows.rows 0) ≼ L.ψ⁰ (Target.finitePower 2)
zero-at-second = Out.Out.bot≤ (Interpretation.upper (good-power 2) (D.U.uw (D.U.us D.U.uz)
  (C.trans (raise-power 0) (extend-power 1))))

first-prefix : V.read (A.cum Rows.rows 1) ≼ L.ψ⁰ (Target.finitePower 3)
first-prefix = ≼-trans {b = V.read (Rows.rows 0) L.+ V.read (Rows.rows 1)}
  (≅→≼ (V.read-+ (Rows.rows 0) (Rows.rows 1)))
  (≼-trans {b = L.ψ⁰ (L.suc (Target.finitePower 2))}
    (≼l 2 (+-mono zero-at-second at-second-power)) (Z.mono₀ (raise-power 2)))

actual-prefix : ∀ (r : T.Run Shape.lvl3) → Slots.Covered r →
  V.read (A.cum Rows.rows 1) ≼ W.read (T.value r)
actual-prefix r cv = ≼-trans {b = L.ψ⁰ (Target.finitePower 3)} first-prefix
  (≼-trans {b = Target.at (Cut.finite 3) 1} (Target.cuts-below 3) (Paid.At.whole r cv))

live : V.read (A.cum Rows.rows 1) ≼ W.read (T.value (T.finiteRun 2))
live = actual-prefix (T.finiteRun 2) (Slots.all-finite 2)

terminal : V.read (A.cum Rows.rows 1) ≼ W.read Native.EBOᶜ
terminal = ≼-trans {b = W.read (T.value (T.finiteRun 2))} live (T.finite-ge 2)
```

从 Ω₂ 反复取正有限倍数的极限，所有有限次结果的后继观察共用同一个 W4 运行。

```agda
power-seed : D.U.U (A.Ωt two) (Target.finitePower 1)
power-seed = D.U.uw D.ΩU (C.pack good-double (good-power 1) (C.lr 2 (C.refl good-double)))

mutual
  argument : ℕ → O.Tr two
  argument zero = A.Ωt two
  argument (suc n) = A.next (argument n) (nonzero n)
  nonzero : ∀ n → two O.⊢ O.zero ◃ argument n
  nonzero zero = A.Ωt-nz two
  nonzero (suc n) = O.◃t (nonzero n) (O.◃l zero)

powers : ∀ n → D.U.U (argument n) (Target.finitePower (suc n))
powers zero = power-seed
powers (suc n) = Plus.Closure.next I.D1 (nonzero n) (good-power (suc n)) (powers n)

observation : ℕ → W.T₀
observation n = V.read (G.ψ⊥ two tt tt E (O.suc (argument n)))

bound-observation : ∀ n → observation n ≼ L.ψ⁰ (Target.finitePower (suc (suc n)))
bound-observation n = Out.Out.bot≤ (Interpretation.upper (good-power (suc (suc n)))
  (D.U.uw (D.U.us (powers n)) (raise-power (suc n))))

all-powers : ∀ (r : T.Run Shape.lvl3) → Slots.Covered r → L.lim observation ≼ W.read (T.value r)
all-powers r cv = ≼-trans {b = Target.at (Cut.finite 3) 1}
  (l≼ λ n → ≼-trans {b = L.ψ⁰ (Target.finitePower (suc (suc n)))} (bound-observation n)
    (Target.cuts-below (suc (suc n)))) (Paid.At.whole r cv)

live-powers : L.lim observation ≼ W.read (T.value (T.finiteRun 2))
live-powers = all-powers (T.finiteRun 2) (Slots.all-finite 2)
```

下一次正回灌中，旧 Ω₂ 自身作用于 Ω₂ 已经作为指定的子树出现。

```agda
positive-self : O.Tr two
positive-self = Rows.χ (A.Ωt two)

second-position : two O.⊢ positive-self ◃ Rows.c 2
second-position = O.◃t (O.◃l 0) (O.◃l 0)

second-observation : V.read (G.ψ⊥ two tt tt E positive-self) L.≺
                     V.read (G.ψ⊥ two tt tt E (Rows.c 2))
second-observation = V.◃→≺ (G.mono⊥ two tt tt E second-position)
```
