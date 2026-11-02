# 降维打击的检验: 与 EBO 的比较 (验收)

> **验收节.** 记号只出现在本文件与 [InaccStrikeCommute](InaccStrikeCommute.lagda.md). 结论汇总在 [InaccStrike](InaccStrike.lagda.md). 全部是有限检验 (`refl`), 不是定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccStrikeAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.InaccTreeBase
open import OCF.Align.InaccTree using (L₁)
open import OCF.Align.InaccTreeAccept using (diff; L; ωᵗ; module Tr⁰)
open import OCF.Align.InaccStrikeOracle using (D★)
import OCF.Align.EBO as E
open E using (T; PT; Ωt; Ωs; 𝟏) renaming (ψ to ψᵗ; natT to natᵗ)
open import OCF.Align.EBOI using (isOTᵉ)
open import OCF.Align.OmegaKBase using (tΩ2)

open Tr⁰ D★ using () renaming (⟦_⟧⁰ to ⟪_⟫)
open Tr⁰ ver using () renaming (⟦_⟧⁰ to ⟦_⟧ᵛ)

Ωn : ℕ → T
Ωn n = Ωt (natᵗ n)

ψ0 : PT → T
ψ0 p = ψᵗ [] (p ∷ []) ∷ []

-- 判决与 cmpᵀ 是否一致 (穿透时路径处的层号要在采样下相同)
chkV : ∀ {j i} → E.Cmp → Verdict j i → Bool
chkV {j} {i} E.lt (pen r b) = same j (at i r)
chkV E.lt rise = false
chkV E.eq (pen r b) = false
chkV E.gt (pen r b) = false
chkV E.eq rise = true
chkV E.gt rise = true

chk : Oracle → T → T → Bool
chk D u v = chkV (E.cmpᵀ u v) (D (L D u) (L D v))
```

## §1 `ver` 的树确实偏离 EBO

遗留问题的回答: 偏离. 上一轮宽度 1 查不到, 因为偏离在第 1 号分支. `tA = ψ₀(ψ_{Ω₂}(Ω_{Ω₁+1}))` 是标准形, 在路径 `[1,0,0,1,0,0,0]` 处不一致. 原因是 `reify` 把 `limᴼ` 读成 0: `ver` 答 `Ω₁` 不低于 `Ω₂`.

```agda
tA : T
tA = ψ0 (ψᵗ (Ωn 2) (Ωs (Ωn 1)))

tA-NF : isOTᵉ tA ≡ true
tA-NF = refl

ver-dev : diff 8 2 tA ⟦ tA ⟧ᵛ ≡ just (1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ [])
ver-dev = refl

isRise : ∀ {j i} → Verdict j i → Bool
isRise rise      = true
isRise (pen _ _) = false

ver-wrong-Ω : chk ver (Ωn 1) (Ωn 2) ≡ false
ver-wrong-Ω = refl

ver-rise-Ω : isRise (ver (L ver (Ωn 1)) (L ver (Ωn 2))) ≡ true
ver-rise-Ω = refl
```

## §2 `b` 确实要被规格约束

`corrupt D` 与 `D` 判决标签处处相同, 路径也相同, 只把搬运换成常值. InaccTreeAccept 的 `Agree` 只看 `at i r`, 在 `L` 不变时分辨不出它们; 树却错了. 所以 `GV` 要求 `strip (b y) ≡ strip y`.

```agda
corrupt : Oracle → Oracle
corrupt D j i with D j i
... | pen r b = pen r (λ _ → zero)
... | rise    = rise

tψ22 : T
tψ22 = ψ0 (ψᵗ (natᵗ 2) (Ωn 2))

tψ22-NF : isOTᵉ tψ22 ≡ true
tψ22-NF = refl

b-ok : diff 8 2 tψ22 ⟦ tψ22 ⟧ᵛ ≡ nothing
b-ok = refl

b-bad : diff 8 2 tψ22 (Tr⁰.⟦_⟧⁰ (corrupt ver) tψ22) ≡ just (1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ [])
b-bad = refl
```

## §3 `D★` 的有限检验与编译的反驳

`D★` 修掉了 `tA` 的偏离, 通过深度 2 的 `tP2 = ψ₀(ψ_Ω(ψ_Ω(Ω_Ω)))` 与 `EBOψ 3` 的 `diff`. **但直接检查判决, 它是错的:** `D★ (L Ω_Ω) (L Ω_Ω)` 答 `pen`, 也就是说它在同一个标准形层号上判 `≺` (`★-wrong-OO`). `diff` 没有发现这一点, 所以有限的逐项比较不足以评价判决.

错误的机制 (由修补过程观察到, 非定理): 目标 `limᴼ k g` 处 `D★` 取 `x = suc (toT k j)`, `toT` 把 `j` 读成第 `k` 层的树, 于是 `toLv x` 在任何有限采样下都像 `j`. 采样式的 `same` 分不开它们. 三版修补 (采样 2 点、4 点、`nrm` 个点) 依次把错误推后, 没有消除. 全对偶扫描 (12 个项, 144 对, 采样 4 点的版本) 有 7 对错, 全部涉及奇异 Ω 下标; 本文件是最后一版, 只列出到此为止的结果.

```agda
OO : T
OO = Ωt (Ωn 1)

tP2 : T
tP2 = ψᵗ [] (ψᵗ (Ωn 1) (ψᵗ (Ωn 1) OO ∷ []) ∷ []) ∷ []

tP2-NF : isOTᵉ tP2 ≡ true
tP2-NF = refl

★-tA : diff 8 2 tA ⟪ tA ⟫ ≡ nothing
★-tA = refl

★-tΩ2 : diff 7 2 tΩ2 ⟪ tΩ2 ⟫ ≡ nothing
★-tΩ2 = refl

★-tP2 : diff 6 2 tP2 ⟪ tP2 ⟫ ≡ nothing
★-tP2 = refl

★-EBO3 : diff 6 2 (E.EBOψ 3) ⟪ E.EBOψ 3 ⟫ ≡ nothing
★-EBO3 = refl

★-Ω₁Ω₂ : chk D★ (Ωn 1) (Ωn 2) ≡ true
★-Ω₁Ω₂ = refl

★-ωω : chk D★ (Ωt ωᵗ) (Ωt ωᵗ) ≡ true
★-ωω = refl

★-wrong-OO : chk D★ OO OO ≡ false
★-wrong-OO = refl

★-wrong-Ω₂ : chk D★ (Ωt (Ωn 2)) OO ≡ false
★-wrong-Ω₂ = refl
```
