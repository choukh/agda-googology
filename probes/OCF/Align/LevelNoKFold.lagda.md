# 折叠, 读回闭合, 塔与 $\psi_0(\Lambda)$ 的无参数闭项

> 不含记号. 结论写在 [LevelNoK](LevelNoK.lagda.md). `Tψ x w n` 是 $\psi_n(\Omega_x)$ 的树, 对任何合法的 `x`, **没有 `Un`**. `x̂ n`, `ψ₀Λ` 是闭项: 类型里没有条件, 也不在任何模块参数下. **闭项不等于序数:** 树里的闭包是待计值的符号 (`oŝ`, `oĉ`). 读回 `feed` 落在 `LF` 里, 所以读回的值再作下标不需要新类型; 它的合法性没有定理, 与 [LevelFixFold](LevelFixFold.lagda.md) 相同.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelNoKFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import OCF.Align.LevelFixCore using (LF)
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelNoKU
open import OCF.Align.LevelNoKBase XF using (Tc; Tc-id)
import OCF.Align.LevelNoKTree XF as TT′
module TT = TT′
open TT public using (O; rb; Tn; T⁰; natL)

-- ψ_n(Ω_x). 一个定义, 没有阶段. 对 x 的要求只有 Legal.
Tψ : (x : LF) → Legal x → (n : ℕ) → T⁰ n
Tψ x w n = Tn (toU x) (Cf-toU x w) (Tc-id (toU x)) n

-- 读回: 输出是 LG 𝕌, 再读成 LF. 没有外部的新层.
feed : (x : LF) → Legal x → ℕ → LF
feed x w n = fromU (rb (Tψ x w n))

-- 读回再作下标, 不用新类型: Ω_{ψ_n(Ω_x)} 的值. 合法性没有定理.
Ωfeed : (x : LF) → Legal x → ℕ → LF
Ωfeed x w n = Ω̂ (feed x w n)

-- 塔的每一项: 无条件, 无参数
x̂ : ∀ n → T⁰ 0
x̂ n = Tψ (tw n) (Legal-tw n) 0

-- ψ₀(Λ): 无条件, 无参数
ψ₀Λ : T⁰ 0
ψ₀Λ = Tψ Λ Legal-Λ 0

-- ψ_k(Ω_Λ), ψ_k(Ω_{Ω_η}): 同一个定义
ψ₀ΩΛ : T⁰ 0
ψ₀ΩΛ = Tψ (Ω̂ Λ) Legal-ΩΛ 0

ψ-ΩΩ : (η : LF) → Legal η → ∀ k → T⁰ k
ψ-ΩΩ η w k = Tψ (ΩΩ η) (Legal-ΩΩ η w) k

-- ψ₁(Ω_θ), 对合法的 θ
ψ₁θ : (θ : LF) → Legal θ → LF
ψ₁θ θ w = feed θ w 1

-- ψ_k(Ω_{Ω_n}), ψ_k(Ω_{Ω_ω}): 对 n 与 k 一个定义
Tψ-Ωn : ∀ n k → T⁰ k
Tψ-Ωn n k = Tψ (Ω̂ (natF n)) (Legal-Ω̂ (natF n) (Legal-nat n)) k

Tψ-Ωω : ∀ k → T⁰ k
Tψ-Ωω k = Tψ Ωω Legal-Ωω k
```
