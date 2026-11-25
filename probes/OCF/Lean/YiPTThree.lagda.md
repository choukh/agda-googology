# 两条实际链的前缀 3：起点义务与值界
不读记号；编译定理，无前提：`YiRRThree.Obl3` 成立（`obl3`），前缀 3 的值界 `prefix-three`（源第 3 项不高于目标第 3 项）。
做法：前缀 k 在第 3 支上的折叠化成第 4 层上嵌入的 Ω 树的折叠（`fs0`–`fs2`、`ft0`–`ft2`，`refl`），对 k 逐级用 `YiPTLadder.E`；`Obl3` 是 k = 1 那一级在（第 3 层，`inc tt self`）的分量。前缀 2 的起点由 `YiRRTwo.prefix-two` 给出。
不否定什么；一切前缀在 [YiPTAll](YiPTAll.lagda.md)（不经本文件）。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPTThree where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiOFPath as OP
import OCF.Lean.YiOGState as St
import OCF.Lean.YiOGCanon as Can
import OCF.Lean.YiOGTransfer as X
import OCF.Lean.YiTNShape as H
import OCF.Lean.YiRRThree as R3
open import OCF.Lean.YiVRRel using (NoΩ≤)
open import OCF.Lean.YiLXClimb using (Dom)
open import OCF.Lean.YiRRRel
open import OCF.Lean.YiRRFold using (_⊴ⁿ_; geβ)
open import OCF.Lean.YiRRClimb using (climbₒ; fself; fS)
open import OCF.Lean.YiRRTwo using (le→n₀; prefix-two)
open import OCF.Lean.YiPTLadder using (E; ups; ups′)
open import OCF.Lean.YiRRUp using (L2; L3)
```

## 前缀 k 在第 3 支上的折叠

`Fs k i u`: 源前缀 k 沿 `inc 3 u` 的折叠, 起点 Ω_i; 第 3 项的底是 `Fs 2`. `Ft` 同为目标.

```agda
Fs : ℕ → F.Base (C.g 3)
Fs k i u = TB.ψ St.G.ℓ C.og (MT.rbᶻ St.G.ℓ) (F.B₀ St.G.ℓ) i (inc 3 u) (Ωt i) (St.G.prefix k)
Ft : ℕ → F.Base (C.h 3)
Ft k i w = TB.ψ St.T.ℓ St.oh (MT.rbᶻ St.T.ℓ) (F.B₀ St.T.ℓ) i (inc 3 w) (Ωt i) (St.T.prefix k)

opaque
  unfolding St.G.base-at St.G.previous St.G.prefix St.G.part
  fs0 : (i : L) (u : i ≤ C.g 3) → Fs 0 i u ≡ TB.ψ (C.g 3) (proj₂ C.og 3) (MT.rbᶻ (C.g 3)) (F.B₀ (C.g 3)) i u (Ωt i) (proj₁ (ups L1 3))
  fs0 i u = refl
  fs1 : (i : L) (u : i ≤ C.g 3) → Fs 1 i u ≡ TB.ψ (C.g 3) (proj₂ C.og 3) (MT.rbᶻ (C.g 3)) (Fs 0) i u (Fs 0 i u) (proj₁ (ups L2 2))
  fs1 i u = refl
  fs2 : (i : L) (u : i ≤ C.g 3) → Fs 2 i u ≡ TB.ψ (C.g 3) (proj₂ C.og 3) (MT.rbᶻ (C.g 3)) (Fs 1) i u (Fs 1 i u) (proj₁ (ups L3 1))
  fs2 i u = refl
  gbase : (i : L) (u : i ≤ C.g 3) → St.G.base-at 3 i u ≡ Fs 2 i u
  gbase i u = refl

opaque
  unfolding St.T.base-at St.T.previous St.T.prefix St.T.part H.first H.curve H.line
  ft0 : (i : L) (w : i ≤ C.h 3) → Ft 0 i w ≡ TB.ψ (C.h 3) (proj₂ St.oh 3) (MT.rbᶻ (C.h 3)) (F.B₀ (C.h 3)) i w (Ωt i) (proj₁ (ups′ L1 3))
  ft0 i w = refl
  ft1 : (i : L) (w : i ≤ C.h 3) → Ft 1 i w ≡ TB.ψ (C.h 3) (proj₂ St.oh 3) (MT.rbᶻ (C.h 3)) (Ft 0) i w (Ft 0 i w) (proj₁ (ups′ L2 2))
  ft1 i w = refl
  ft2 : (i : L) (w : i ≤ C.h 3) → Ft 2 i w ≡ TB.ψ (C.h 3) (proj₂ St.oh 3) (MT.rbᶻ (C.h 3)) (Ft 1) i w (Ft 1 i w) (proj₁ (ups′ L3 1))
  ft2 i w = refl
  tbase : (i : L) (w : i ≤ C.h 3) → St.T.base-at 3 i w ≡ Ft 2 i w
  tbase i w = refl
```

## 逐级比较

```agda
Cmp : ℕ → Set
Cmp k = (i : L) (u : i ≤ C.g 3) → N i (proj₁ (Fs k i u)) (proj₁ (Ft k i (inc tt (inc tt u))))

dFt : (k : ℕ) → Dom (Ft k)
dFt k i w _ = geβ St.T.ℓ St.oh (MT.rbᶻ St.T.ℓ) (F.B₀ St.T.ℓ) i (inc 3 w) (Ωt i) (St.T.prefix k)

cmp0 : Cmp 0
cmp0 i u = subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (fs0 i u)) (sym (ft0 i (inc tt (inc tt u))))
  (E L1 tt 3 (proj₂ St.oh 3) (MT.rbᶻ (C.g 3)) (MT.rbᶻ (C.h 3)) (F.B₀ (C.g 3)) (F.B₀ (C.h 3))
     (λ j w _ → Ωt≼ j (NoΩ≤ w tt)) (λ j w _ → inj₁ refl) i u false false (Ωt i) (Ωt i) (Ωt≼ i (NoΩ≤ u tt)))

cmp1 : Cmp 1
cmp1 i u = subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (fs1 i u)) (sym (ft1 i (inc tt (inc tt u))))
  (E L2 tt 2 (proj₂ St.oh 3) (MT.rbᶻ (C.g 3)) (MT.rbᶻ (C.h 3)) (Fs 0) (Ft 0)
     (λ j w _ → cmp0 j w) (dFt 0) i u false false (Fs 0 i u) (Ft 0 i (inc tt (inc tt u))) (cmp0 i u))

cmp2 : Cmp 2
cmp2 i u = subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (fs2 i u)) (sym (ft2 i (inc tt (inc tt u))))
  (E L3 tt 1 (proj₂ St.oh 3) (MT.rbᶻ (C.g 3)) (MT.rbᶻ (C.h 3)) (Fs 1) (Ft 1)
     (λ j w _ → cmp1 j w) (dFt 1) i u false false (Fs 1 i u) (Ft 1 i (inc tt (inc tt u))) (cmp1 i u))
```

## 起点义务

```agda
obl3 : R3.Obl3
obl3 = subst₂ (λ x y → N (C.g 2) (proj₁ x) (proj₁ y)) R3.qs3-full R3.qt3-full (cmp1 (C.g 2) (inc tt self))
```

## 前缀 3 的底、起点与值界

```agda
v3 : C.g 3 ⊑ C.h 3
v3 = inc tt (inc tt self)

base3 : St.G.base-at 3 ⊴ⁿ OP.pull-base v3 (St.T.base-at 3)
base3 i u _ = subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (gbase i u)) (sym (tbase i (inc tt (inc tt u)))) (cmp2 i u)

dom3 : Dom (St.T.base-at 3)
dom3 i u _ = inj₂ (St.target-base-growth 2 i u)

beta3 : N zero (proj₁ (St.G.start-at 3)) (proj₁ (St.T.start-at 3))
beta3 = subst₂ (λ x y → N zero (proj₁ x) (proj₁ y)) (sym (St.source-start-next 2)) (sym (St.target-start-next 2))
  (le→n₀ (X.v→r (proj₁ (St.G.piece 2)) (proj₁ (St.T.piece 2)) prefix-two))

row3 : N zero (proj₁ (TB.ψ (C.g 3) (proj₂ C.og 3) (MT.rbᶻ (C.g 3)) (St.G.base-at 3) zero (C.wg 3) (St.G.start-at 3) (proj₁ (Ωt (C.g 3)))))
              (proj₁ (TB.ψ (C.h 3) (proj₂ St.oh 3) (MT.rbᶻ (C.h 3)) (St.T.base-at 3) zero (C.wh 3) (St.T.start-at 3) (proj₁ (Ωt (C.h 3)))))
row3 = climbₒ v3 (fS (fS fself)) (Can.source-no 3) (proj₂ St.oh 3) (proj₂ C.og 3) refl (MT.rbᶻ (C.g 3)) (MT.rbᶻ (C.h 3))
  (St.G.base-at 3) (St.T.base-at 3) base3 dom3 (St.G.start-at 3) (St.T.start-at 3) beta3

prefix-three : V.val zero (proj₁ (St.G.piece 3)) V.≼ V.val zero (proj₁ (St.T.piece 3))
prefix-three = subst₂ (λ x y → V.val zero (proj₁ x) V.≼ V.val zero (proj₁ y))
  (sym (St.G.state-row 3)) (sym (St.T.state-row 3)) (sound zero ser₀ row3)

prefix-three-cover : Σ ℕ λ m → V.val zero (proj₁ (St.G.piece 3)) V.≼ V.val zero (proj₁ (St.T.piece m))
prefix-three-cover = 3 , prefix-three
```
