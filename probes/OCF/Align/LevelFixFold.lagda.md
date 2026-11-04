# 折叠, 读回闭合, 塔与 $\psi_0(\Lambda)$ 的闭项

> 不含记号. 结论写在 [LevelFix](LevelFix.lagda.md). `Tψ x w n` 是 $\psi_n(\Omega_x)$ 的树, 对任何合法的 `x`. **闭项不等于序数:** 树里的闭包是待计值的符号 (`oŝ`, `oĉ`). 读回 `feed` 落在 `LF` 里, 所以读回的值再作下标不需要新类型; 它的合法性没有定理 (见文件头).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelFixFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.LevelFixCore using (LF)
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelFixU
open import OCF.Align.LevelFixBase XF using (Tc; Tc-id)
import OCF.Align.LevelFixTree XF as TT′
module TT = TT′
open TT public using (O; rb; Tn; T⁰; natL)

-- ψ_n(Ω_x). 一个定义, 没有阶段. 对 x 的要求是 Legal 与名字的 UIP (条件, 见 LevelFixU §2).
Tψ : (x : LF) → Legal x → Un x → (n : ℕ) → T⁰ n
Tψ x w u n = Tn (toU x) (Cf-toU x w u) (Tc-id (toU x)) n

-- 读回: 输出是 LG 𝕌, 再读成 LF. 没有外部的新层.
feed : (x : LF) → Legal x → Un x → ℕ → LF
feed x w u n = fromU (rb (Tψ x w u n))

-- 读回再作下标, 不用新类型: Ω_{ψ_n(Ω_x)} 的值. 合法性没有定理.
Ωfeed : (x : LF) → Legal x → Un x → ℕ → LF
Ωfeed x w u n = Ω̂ (feed x w u n)

-- 塔的前三项, 无条件
Un-tw2 : Un (tw 2)
Un-tw2 = uip-nat 0 , tt , (λ η e → Un-up 0 η)

x̂₀ x̂₁ x̂₂ : T⁰ 0
x̂₀ = Tψ (tw 0) (Legal-tw 0) tt 0
x̂₁ = Tψ (tw 1) (Legal-tw 1) tt 0
x̂₂ = Tψ (tw 2) (Legal-tw 2) Un-tw2 0

-- 一切 n: 条件于 Un (tw n). ψ₀(Λ) 同样: 条件于 Un Λ. 没有得到无条件的闭项.
x̂-if : ∀ n → Un (tw n) → T⁰ 0
x̂-if n u = Tψ (tw n) (Legal-tw n) u 0

ψ₀Λ-if : Un Λ → T⁰ 0
ψ₀Λ-if u = Tψ Λ Legal-Λ u 0

-- ψ_k(Ω_{Ω_n}), ψ_k(Ω_{Ω_ω}): 无条件闭项, 一个定义, 对 n 与 k
Tψ-Ωn : ∀ n k → T⁰ k
Tψ-Ωn n k = Tψ (Ω̂ (natF n)) (Legal-Ω̂ (natF n) (Legal-nat n)) (Un-T n) k

Tψ-Ωω : ∀ k → T⁰ k
Tψ-Ωω k = Tψ Ωω Legal-Ωω Un-Ωω k

-- ψ₁(Ω_θ), 对合法且名字 UIP 的 θ
ψ₁θ : (θ : LF) → Legal θ → Un θ → LF
ψ₁θ θ w u = feed θ w u 1
```
