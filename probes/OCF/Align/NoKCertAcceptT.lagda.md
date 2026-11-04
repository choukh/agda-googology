# 验收: 测试本身

> **验收节, 全部是有限测试 (`refl`), 不是证明.** 比较器在 [NoKCertAccept](NoKCertAccept.lagda.md), [NoKCertProbe](NoKCertProbe.lagda.md). 结论写在 [NoKCert](NoKCert.lagda.md). 编译约 2 分钟.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoKCertAcceptT where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (LF)
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelNoKFold using (rb; Tψ)
open import OCF.Align.NoKCertRd
open import OCF.Align.NoKCertTc
open import OCF.Align.NoKCertAccept
open import OCF.Align.NoKCertEval using (Zᵁ; rdZ)
open import OCF.Align.NoKCertProbe using (tally; findB; firstNo; legalNo; chainSteps)
```

## §1 界对塔: `LevelNoKAccept` 里不一致的三条

`LevelNoKAccept` 的 `b-Ω+1` (10, 3), `b-Ω+1₂` (10, 2), `b-Ω2` (10, 3) 是 3 对 2, 2 对 1, 2 对 1. 这里同一比较器, 紧读法加 `owk` 一行.

```agda
t-Ω : misQ 10 3 [] (Tψᵗ ΩL₁ L-Ω₁ c-Ω₁ 0) qΩ ≡ nothing
t-Ω = refl

t-Ω+1₂ : misQ 10 2 [] (Tψᵗ Ω₁₊₁ L-Ω₁ c-Ω₁ 0) qΩ+1 ≡ nothing
t-Ω+1₂ = refl

t-Ω+1₈ : misQ 8 3 [] (Tψᵗ Ω₁₊₁ L-Ω₁ c-Ω₁ 0) qΩ+1 ≡ nothing
t-Ω+1₈ = refl

t-Ω2₂ : misQ 8 2 [] (Tψᵗ Ω₁₂ L-Ω₁₂ c-Ω₁₂ 0) qΩ2 ≡ nothing
t-Ω2₂ = refl

t-Ω+2 : misQ 6 3 [] (Tψᵗ Ω₁₊₂ L-Ω₁ c-Ω₁ 0) qΩ+2 ≡ nothing
t-Ω+2 = refl
```

沿旧的报错路径: `b-Ω+1`, `b-Ω2`, `b-Ω+1₂` 报的路径 (反转, 尾部多一步, 让末尾的闭包也比到), 不穷尽, 只走这一条. `ctl-*`: 同一条路径上恒等读法的旧树确实报错, 所以这条比较不是空的.

```agda
p₁ p₂ p₃ : List ℕ
p₁ = 2 ∷ 2 ∷ 2 ∷ 2 ∷ 300 ∷ 0 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ []
p₂ = 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 300 ∷ 0 ∷ 2 ∷ 2 ∷ 2 ∷ []
p₃ = 1 ∷ 300 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ 0 ∷ 2 ∷ []

w-p₁ : misP 3 p₁ (Tψᵗ Ω₁₊₁ L-Ω₁ c-Ω₁ 0) qΩ+1 ≡ nothing
w-p₁ = refl

w-p₂ : misP 3 p₂ (Tψᵗ Ω₁₂ L-Ω₁₂ c-Ω₁₂ 0) qΩ2 ≡ nothing
w-p₂ = refl

w-p₃ : misP 2 p₃ (Tψᵗ Ω₁₊₁ L-Ω₁ c-Ω₁ 0) qΩ+1 ≡ nothing
w-p₃ = refl

isJ : ∀ {A : Set} → Maybe A → Bool
isJ (just _) = true
isJ nothing = false

ctl-p₁ : isJ (misP 3 p₁ (Tψ Ω₁₊₁ L-Ω₁ 0) qΩ+1) ≡ true
ctl-p₁ = refl

ctl-p₂ : isJ (misP 3 p₂ (Tψ Ω₁₂ L-Ω₁₂ 0) qΩ2) ≡ true
ctl-p₂ = refl

ctl-p₃ : isJ (misP 2 p₃ (Tψ Ω₁₊₁ L-Ω₁ 0) qΩ+1) ≡ true
ctl-p₃ = refl
```

## §2 读回的字面合法性, 守卫

$\psi_1(\Omega_{\Omega_2})$ 的读回, `legalNo`: 极限的相邻项, 第一支, 分支 $c+i$ 的步进, 字面第一位置, 比较器 `eqL` (0 个不过). 第一个 `oĉ` 的链点 $z$: 下界 `top` 在 $z$ 的第一路径上, 链点上的极限步进.

```agda
Ω₂L : LF
Ω₂L = Ω̂ (natF 2)
LΩ₂ : Legal Ω₂L
LΩ₂ = Legal-Ω̂ (natF 2) (Legal-nat 2)
cΩ₂ : Cnt Ω₂L
cΩ₂ = cnt-Ω̂ (natF 2) (cnt-nat 2)

l-ψ₁Ω₂ : legalNo 5 6 40 2 (rb (Tψᵗ Ω₂L LΩ₂ cΩ₂ 1)) ≡ 0
l-ψ₁Ω₂ = refl

g-Ω₂ : proj₂ (tally (findB 8 5 60 2 (Tψᵗ Ω₂L LΩ₂ cΩ₂ 0))) ≡ 0
g-Ω₂ = refl

c-Ω₂ : chainSteps 6 6 6 40 3 (Tψᵗ Ω₂L LΩ₂ cΩ₂ 0) ≡ 0
c-Ω₂ = refl
```

第 0 层的树的头: `h-*`. $\Omega$ 是 `ŝ` (第 0 层的自链), $\Omega_2$ 是 `ĉ`, $1$ 是极限.

```agda
head : Zᵁ → ℕ
head Zᵁ.zero = 0
head (Zᵁ.suc _) = 1
head (Zᵁ.lim _) = 2
head (Zᵁ.ŝ _ _ _) = 3
head (Zᵁ.ĉ _ _ _ _ _) = 4

h-1 : head (rdZ (x̂ᵗ 1)) ≡ 2
h-1 = refl

h-Ω : head (rdZ (Tψᵗ ΩL₁ L-Ω₁ c-Ω₁ 0)) ≡ 3
h-Ω = refl

h-Ω₂ : head (rdZ (Tψᵗ Ω₂L LΩ₂ cΩ₂ 0)) ≡ 4
h-Ω₂ = refl
```
