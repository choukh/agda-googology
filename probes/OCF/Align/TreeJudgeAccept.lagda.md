# 盲测: 与记号比较 (验收)

> **验收节, 读记号.** 写在 [TreeJudgeBlind](TreeJudgeBlind.lagda.md) 封存之后. 比较器 `dfZ` 来自 [GuardTightAccept](GuardTightAccept.lagda.md), 没有改. **有限测试, 不是定理; `dfZ` 只比种类, 闭包只走第一支, 不看界.** 结论写在 [TreeJudge](TreeJudge.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.EBO as E
open E using (T; Ωt; natT; sucT)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ)
open import OCF.Align.Uniform5Wall using (ψ₁)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.GuardTightAccept using (dfZ; is-ok; tF; Why)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightTree using (T₀)
open import OCF.Align.GuardTightCum using (suc)
open import OCF.Align.GuardTightLv
open Lv Dom₀ using (suc)
open import OCF.Align.TreeJudgeBlind using (a; c; Cf-a; Tc-a; Cf-ab; Tc-ab; Lab; LaΩ; Cf-aΩ; Tc-aΩ; LaΩ2; Cf-aΩ2; Tc-aΩ2; Lψ2; Cf-ψ2; Tc-ψ2; sucCf)
open import OCF.Align.GuardTightUni Dom₀ using (rb₁)
open import OCF.Align.EBOI using (isOTᵉ)
open import OCF.Align.TreeJudgeBlind2 using (W₁; Cf-W)
open import OCF.Align.TreeJudgeRdF using (Tc-F1)

ta : T
ta = tF 0

uA uB uC uD uAa u2 uaΩ uaΩ1 uaΩ2 : T
uAa = ψ₀ᵗ (Ωt ta)
uA = ψ₀ᵗ (Ωt (sucT ta))
u2 = ψ₀ᵗ (Ωt (sucT (sucT ta)))
uB = ψ₀ᵗ (Ωt (ta ++ ta))
uC = ψ₀ᵗ (Ωt (ψ₁ (natT 2)))
uD = ψ₀ᵗ (Ωt (sucT (ta ++ ta)))
uaΩ = ψ₀ᵗ (Ωt (ta ++ Ωᵗ))
uaΩ1 = ψ₀ᵗ (Ωt (sucT (ta ++ Ωᵗ)))
uaΩ2 = ψ₀ᵗ (Ωt (ta ++ (Ωᵗ ++ Ωᵗ)))

zAa zA z2 zB zC zD zaΩ zaΩ1 zaΩ2 : Z
zAa = T₀ (rb₁ a) Cf-a Tc-a
zA = T₀ (suc (rb₁ a)) (sucCf Cf-a) Tc-a
z2 = T₀ (suc (suc (rb₁ a))) (sucCf (sucCf Cf-a)) Tc-a
zB = T₀ Lab Cf-ab Tc-ab
zC = T₀ Lψ2 Cf-ψ2 Tc-ψ2
zD = T₀ (suc Lab) (sucCf Cf-ab) Tc-ab
zaΩ = T₀ LaΩ Cf-aΩ Tc-aΩ
zaΩ1 = T₀ (suc LaΩ) (sucCf Cf-aΩ) Tc-aΩ
zaΩ2 = T₀ LaΩ2 Cf-aΩ2 Tc-aΩ2
```

## §1 比较: 一致

都是 `nothing`: 深度, 宽度之内种类一致. 分支的值由 `pB6`, `pB7`, `pE4`, `pE5` ([TreeJudgeBlindResult](TreeJudgeBlindResult.lagda.md)) 接到这里比过的树上. **这些测试看不到闭包的非第一支, 看不到界.**

```agda
-- 预测的深度: 10, 宽 2
n-A : dfZ 10 2 uA zA ≡ nothing
n-A = refl
n-B : dfZ 10 2 uB zB ≡ nothing
n-B = refl
n-C : dfZ 10 2 uC zC ≡ nothing
n-C = refl
n-D : dfZ 10 2 uD zD ≡ nothing
n-D = refl
n-aΩ : dfZ 10 2 uaΩ zaΩ ≡ nothing
n-aΩ = refl
n-aΩ1 : dfZ 10 2 uaΩ1 zaΩ1 ≡ nothing
n-aΩ1 = refl
n-aΩ2 : dfZ 10 2 uaΩ2 zaΩ2 ≡ nothing
n-aΩ2 = refl

-- 加深
d-A : dfZ 14 2 uA zA ≡ nothing
d-A = refl
d-B : dfZ 14 2 uB zB ≡ nothing
d-B = refl
d-C : dfZ 14 2 uC zC ≡ nothing
d-C = refl
d-D : dfZ 14 2 uD zD ≡ nothing
d-D = refl
w-B : dfZ 10 3 uB zB ≡ nothing
w-B = refl
w-C : dfZ 10 3 uC zC ≡ nothing
w-C = refl
w-D : dfZ 10 3 uD zD ≡ nothing
w-D = refl
```

## §2 对照: 比较器不是空的

项都是标准形, 错配的一对被报出来.

```agda
ot-B : isOTᵉ uB ≡ true
ot-B = refl
ot-C : isOTᵉ uC ≡ true
ot-C = refl
ot-D : isOTᵉ uD ≡ true
ot-D = refl

c-1 : is-ok (dfZ 10 2 uB zA) ≡ false
c-1 = refl
c-2 : is-ok (dfZ 10 2 uA zB) ≡ false
c-2 = refl
c-3 : is-ok (dfZ 10 2 uC zB) ≡ false
c-3 = refl
c-4 : is-ok (dfZ 10 2 uB zC) ≡ false
c-4 = refl
c-5 : is-ok (dfZ 10 2 uD zB) ≡ false
c-5 = refl
c-6 : is-ok (dfZ 10 2 uB zD) ≡ false
c-6 = refl
```

## §3 第二次: $E,E^+$

```agda
uE uE⁺ : T
uE = ψ₀ᵗ (Ωt (tF 1))
uE⁺ = ψ₀ᵗ (Ωt (sucT (tF 1)))

zE zE⁺ : Z
zE = T₀ W₁ Cf-W Tc-F1
zE⁺ = T₀ (suc W₁) (sucCf Cf-W) Tc-F1

n-E : dfZ 10 2 uE zE ≡ nothing
n-E = refl
n-E⁺ : dfZ 10 2 uE⁺ zE⁺ ≡ nothing
n-E⁺ = refl
d-E⁺ : dfZ 14 2 uE⁺ zE⁺ ≡ nothing
d-E⁺ = refl
w-E⁺ : dfZ 10 3 uE⁺ zE⁺ ≡ nothing
w-E⁺ = refl
ot-E⁺ : isOTᵉ uE⁺ ≡ true
ot-E⁺ = refl
c-7 : is-ok (dfZ 10 2 uE zE⁺) ≡ false
c-7 = refl
c-8 : is-ok (dfZ 10 2 uE⁺ zE) ≡ false
c-8 = refl
```

## §4 压力

种类比较到更深也没有不一致. 还是只有第一支.

```agda
s-B : dfZ 18 2 uB zB ≡ nothing
s-B = refl
s-B₁ : dfZ 26 1 uB zB ≡ nothing
s-B₁ = refl
s-C : dfZ 18 2 uC zC ≡ nothing
s-C = refl
s-D : dfZ 18 2 uD zD ≡ nothing
s-D = refl
s-E : dfZ 18 2 uE⁺ zE⁺ ≡ nothing
s-E = refl
s-E₁ : dfZ 26 1 uE⁺ zE⁺ ≡ nothing
s-E₁ = refl
w-E₂ : dfZ 12 3 uE⁺ zE⁺ ≡ nothing
w-E₂ = refl
```
