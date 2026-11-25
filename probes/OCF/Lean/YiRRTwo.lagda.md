# 两条实际链的前缀 2：N 下的底前提与值界
不读记号；编译定理，无前提：源前缀 2 的底按 `N` 不高于沿 `inc tt (inc tt self)` 拉回的目标前缀 2 的底（`base2`），`YiRRClimb.climbₒ` 给出前缀 2 的值界 `prefix-two`（陈述同 `YiLXOne.prefix-one` 的第 2 项）；`Le`、`W` 形式的这一底前提对拉回分量满足 `Dry` 的目标底不成立（`YiLXOne.no-base-dry`、`YiWBNeg.no-base`，对齐到前缀 2 时以 `Dry target-next` 为条件）。
做法：底的每个分量化成后继层号上 Ω 树的折叠（`F1`–`F3`、`qs-form`、`qt-form`，`refl`），再用 `climb`；零层槽位那一支的起点是 `left`/`right` 一对，用 `YiRRPair.in-P`。
不否定什么；一切前缀与 ActualMissing 未填，见回报。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRRTwo where
open import Data.Nat using (ℕ; zero; suc)
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
import OCF.Lean.YiVRRel as R
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiOFPath as OP
import OCF.Lean.YiOGState as St
import OCF.Lean.YiOGCanon as Can
import OCF.Lean.YiOGTransfer as X
import OCF.Lean.YiTNShape as H
import OCF.Lean.YiWBNeg as WN
open import OCF.Lean.YiLXOne using (prefix-one)
open import OCF.Lean.YiLXClimb using (Dom)
open import OCF.Lean.YiRRRel
open import OCF.Lean.YiRRFold using (_⊴ⁿ_; geβ)
open import OCF.Lean.YiRRClimb using (climb; climbₒ; fself; fS; fSi)
open import OCF.Lean.YiRRPair using (in-P)

one two three four : L
one = C.g 0
two = C.g 1
three = C.h 0
four = C.h 1

o₁ : Ok one
o₁ = proj₂ C.og 0
o₂ : Ok two
o₂ = proj₂ C.og 1
o₃ : Ok three
o₃ = proj₂ St.oh 0
o₄ : Ok four
o₄ = proj₂ St.oh 1

v₁ : one ⊑ three
v₁ = inc tt (inc tt self)
v₂ : two ⊑ four
v₂ = inc tt (inc tt self)
```

## 底的分量的形状

`Qs`, `Qt`: 前缀 0 的折叠在前缀 2 的孩子路径上 (源前缀 2 的底读的就是它).

```agda
Qs : (i : L) → i ≤ C.g 2 → Tr⁺ i
Qs i w = TB.ψ St.G.ℓ C.og (MT.rbᶻ St.G.ℓ) (F.B₀ St.G.ℓ) i (inc 2 w) (Ωt i) (St.G.prefix 0)
Qt : (i : L) → i ≤ C.h 2 → Tr⁺ i
Qt i w = TB.ψ St.T.ℓ St.oh (MT.rbᶻ St.T.ℓ) (F.B₀ St.T.ℓ) i (inc 2 w) (Ωt i) (St.T.prefix 0)
Bs : F.Base two
Bs i u = Qs i (inc tt u)
Bt : F.Base four
Bt i u = Qt i (inc tt u)

opaque
  unfolding St.G.base-at St.G.previous St.G.prefix St.G.part
  F1 : (i : L) (u : i ≤ two) → St.G.base-at 2 i (inc tt u) ≡ TB.ψ two o₂ (MT.rbᶻ two) Bs i u (Qs i (inc tt u)) (proj₁ (Ωt two))
  F1 i u = refl
  F2 : (i : L) (vs : ⊤ → i ≤ two) → St.G.base-at 2 i (inu vs) ≡ TB.ψ two o₂ (MT.rbᶻ two) Bs i (vs tt) (Qs i (inu vs)) (proj₁ (Ωt two))
  F2 i vs = refl
  qs-form : (i : L) (w : i ≤ two) → Qs i (inc tt w)
    ≡ TB.ψ two o₂ (MT.rbᶻ two) (F.B₀ two) i w (Ωt i) (proj₁ (upz {sS} {λ _ → one} tt (Ωt one)))
  qs-form i w = refl
  qs-form-u : (i : L) (vs : ⊤ → i ≤ two) → Qs i (inu vs)
    ≡ TB.ψ two o₂ (MT.rbᶻ two) (F.B₀ two) i (vs tt) (Ωt i) (proj₁ (upz {sS} {λ _ → one} tt (Ωt one)))
  qs-form-u i vs = refl

opaque
  unfolding St.T.base-at St.T.previous St.T.prefix St.T.part H.first H.curve H.line
  F3 : (i : L) (u : i ≤ C.g 2) → St.T.base-at 2 i (inc tt (inc tt u))
    ≡ TB.ψ four o₄ (MT.rbᶻ four) Bt i (inc tt u) (Qt i (inc tt (inc tt u))) (proj₁ (Ωt four))
  F3 i u = refl
  qt-form : (i : L) (w : i ≤ three) → Qt i (inc tt (inc tt w))
    ≡ TB.ψ three o₃ (MT.rbᶻ three) (F.B₀ three) i w (Ωt i) (proj₁ (Ωt three))
  qt-form i w = refl
```

## 前缀 0 的折叠: 第 1 层对第 3 层

路径 `self` 那一支是 `left` 对 `right` 的形状 (目标路径取 `inc` 或 `inu`), 由 `YiRRPair.in-P` 给出; 其余各支是第 1 层到第 3 层的 `climb`, 底都是标准底.

```agda
νi : (i : L) (u : i ≤ one) → R.NoΩ i
νi i u = R.NoΩ≤ u (Can.source-no 0)

hB₀ : F.B₀ one ⊴ⁿ OP.pull-base v₁ (F.B₀ three)
hB₀ j w _ = Ωt≼ j (νi j w)

dB₀ : Dom (F.B₀ three)
dB₀ i u _ = inj₁ refl

left-high : N two (proj₁ WN.leftT) (proj₁ (TB.ψ three o₃ (MT.rbᶻ three) (F.B₀ three) two (inc tt self) (Ωt two) (proj₁ (Ωt three))))
left-high = ≼l 1 (right-add in-P _)

left-high-u : N two (proj₁ WN.leftT) (proj₁ (TB.ψ three o₃ (MT.rbᶻ three) (F.B₀ three) two (inu (λ _ → self)) (Ωt two) (proj₁ (Ωt three))))
left-high-u = ≼l 1 (right-add in-P _)

p0 : (i : L) (w : i ≤ two) → N i (proj₁ (TB.ψ two o₂ (MT.rbᶻ two) (F.B₀ two) i w (Ωt i) (proj₁ (upz {sS} {λ _ → one} tt (Ωt one)))))
       (proj₁ (TB.ψ three o₃ (MT.rbᶻ three) (F.B₀ three) i (inc tt w) (Ωt i) (proj₁ (Ωt three))))
p0 .two self = left-high
p0 i (inc tt w′) = climb v₁ (fSi (fSi fself)) (νi one self) o₃ (MT.rbᶻ one) (MT.rbᶻ three) (F.B₀ one) (F.B₀ three)
  hB₀ dB₀ (Ωt i) (Ωt i) (Ωt≼ i (νi i w′))
p0 i (inu vs) = climb v₁ (fSi (fS fself)) (νi one self) o₃ (MT.rbᶻ one) (MT.rbᶻ three) (F.B₀ one) (F.B₀ three)
  hB₀ dB₀ (Ωt i) (Ωt i) (Ωt≼ i (νi i (vs tt)))

p0u : (i : L) (w : i ≤ two) → N i (proj₁ (TB.ψ two o₂ (MT.rbᶻ two) (F.B₀ two) i w (Ωt i) (proj₁ (upz {sS} {λ _ → one} tt (Ωt one)))))
       (proj₁ (TB.ψ three o₃ (MT.rbᶻ three) (F.B₀ three) i (inu (λ _ → w)) (Ωt i) (proj₁ (Ωt three))))
p0u .two self = left-high-u
p0u i (inc tt w′) = climb v₁ (fS (fSi fself)) (νi one self) o₃ (MT.rbᶻ one) (MT.rbᶻ three) (F.B₀ one) (F.B₀ three)
  hB₀ dB₀ (Ωt i) (Ωt i) (Ωt≼ i (νi i w′))
p0u i (inu vs) = climb v₁ (fS (fS fself)) (νi one self) o₃ (MT.rbᶻ one) (MT.rbᶻ three) (F.B₀ one) (F.B₀ three)
  hB₀ dB₀ (Ωt i) (Ωt i) (Ωt≼ i (νi i (vs tt)))
```

## 前缀 2 的底

第 2 层到第 4 层的 `climb`; 底是上一节的 `p0`, 右侧的底不低于标准 Ω 树由 `geβ` 给出.

```agda
hBs : Bs ⊴ⁿ OP.pull-base v₂ Bt
hBs i u _ = subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (qs-form i u)) (sym (qt-form i (inc tt u))) (p0 i u)

dBt : Dom Bt
dBt i u _ = geβ St.T.ℓ St.oh (MT.rbᶻ St.T.ℓ) (F.B₀ St.T.ℓ) i (inc 2 (inc tt u)) (Ωt i) (St.T.prefix 0)

ν₂ : R.NoΩ two
ν₂ = Can.source-no 1

v2 : C.g 2 ⊑ C.h 2
v2 = inc tt (inc tt self)

base2 : St.G.base-at 2 ⊴ⁿ OP.pull-base v2 (St.T.base-at 2)
base2 i (inc tt u) _ = subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (F1 i u)) (sym (F3 i (inc tt u)))
  (climb v₂ (fSi (fSi fself)) ν₂ o₄ (MT.rbᶻ two) (MT.rbᶻ four) Bs Bt hBs dBt (Qs i (inc tt u)) (Qt i (inc tt (inc tt (inc tt u))))
    (subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (qs-form i u)) (sym (qt-form i (inc tt u))) (p0 i u)))
base2 i (inu vs) _ = subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (F2 i vs)) (sym (F3 i (inu vs)))
  (climb v₂ (fSi (fS fself)) ν₂ o₄ (MT.rbᶻ two) (MT.rbᶻ four) Bs Bt hBs dBt (Qs i (inu vs)) (Qt i (inc tt (inc tt (inu vs))))
    (subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (qs-form-u i vs)) (sym (qt-form i (inu vs))) (p0u i (vs tt))))

dom2 : Dom (St.T.base-at 2)
dom2 i u _ = inj₂ (St.target-base-growth 1 i u)
```

## 起点与值界

```agda
le→n₀ : {x y : Tr zero} → R.Le zero x y → N zero x y
le→n₀ R.z≼ = z≼
le→n₀ (R.s≼s d) = s≼s (le→n₀ d)
le→n₀ (R.≼s d) = ≼s (le→n₀ d)
le→n₀ (R.≼l n d) = ≼l n (le→n₀ d)
le→n₀ (R.l≼ h) = l≼ (λ n → le→n₀ (h n))
le→n₀ (R.≼w {p = ()} d)
le→n₀ (R.w≼w {p = ()} h)
le→n₀ (R.≼u {c = ()} d)
le→n₀ (R.u≼u {c = ()} dx dy)

beta2 : N zero (proj₁ (St.G.start-at 2)) (proj₁ (St.T.start-at 2))
beta2 = subst₂ (λ x y → N zero (proj₁ x) (proj₁ y)) (sym (St.source-start-next 1)) (sym (St.target-start-next 1))
  (le→n₀ (X.v→r (proj₁ (St.G.piece 1)) (proj₁ (St.T.piece 1)) prefix-one))

row2 : N zero (proj₁ (TB.ψ (C.g 2) (proj₂ C.og 2) (MT.rbᶻ (C.g 2)) (St.G.base-at 2) zero (C.wg 2) (St.G.start-at 2) (proj₁ (Ωt (C.g 2)))))
              (proj₁ (TB.ψ (C.h 2) (proj₂ St.oh 2) (MT.rbᶻ (C.h 2)) (St.T.base-at 2) zero (C.wh 2) (St.T.start-at 2) (proj₁ (Ωt (C.h 2)))))
row2 = climbₒ v2 (fS (fS fself)) (Can.source-no 2) (proj₂ St.oh 2) (proj₂ C.og 2) refl (MT.rbᶻ (C.g 2)) (MT.rbᶻ (C.h 2))
  (St.G.base-at 2) (St.T.base-at 2) base2 dom2 (St.G.start-at 2) (St.T.start-at 2) beta2

prefix-two : V.val zero (proj₁ (St.G.piece 2)) V.≼ V.val zero (proj₁ (St.T.piece 2))
prefix-two = subst₂ (λ x y → V.val zero (proj₁ x) V.≼ V.val zero (proj₁ y))
  (sym (St.G.state-row 2)) (sym (St.T.state-row 2)) (sound zero ser₀ row2)

prefix-two-cover : Σ ℕ λ m → V.val zero (proj₁ (St.G.piece 2)) V.≼ V.val zero (proj₁ (St.T.piece m))
prefix-two-cover = 2 , prefix-two
```
