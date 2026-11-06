# NegSameV (六): 目标 `Goal` 的严格只是 "多一个后继" 档

> 不含记号. 入口 [NegSameV](NegSameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延. 只导入 [CRw](CRw.lagda.md), [ValCRel](ValCRel.lagda.md), [ValCBase](ValCBase.lagda.md).
>
> **问题.** `ValXGoal.goal-if` 的结论 $\mathrm{TX}+1\le\mathrm{TU}\,1$ 的证明只用: `TU 1` 是部分和的极限, 第 0 项不低于 `TX` (`Hyp`), 第 1 项不低于 $1$ (`oneX`). 本篇问这个 "+1" 能不能当强度证据.
>
> **`shape-up`, `shape-bound` (定理, 对一切可数树 $X$).** 取族 $G_0=X$, $G_{n+1}=1$: $X+1\le\lim\Sigma^+G$, 而 $\lim\Sigma^+G\le X+\omega$. 所以 **"部分和的极限, 第 0 项 $\ge X$, 其余项 $\ge1$" 这个形状的结论, 不区分 `TU 1` 与 $\mathrm{TX}+\omega$**. 取 $X=$ `TX` 就是 `shape-TX`. 同样 $X+2\le\lim\Sigma^+G$ (`shape-up2`), 对应构造一路的 `SameV.goal2`. 所以 $\mathrm{TX}+2\le\mathrm{TU2}$ 也不区分 `TU2` 与 $\mathrm{TX}+\omega$.
>
> **前提实例.** 对一切 $X$; 实例 `TX`.
>
> **只否定什么.** 只否定 "`Goal` 的严格说明 `TU 1` 比 `TX` 高一档" 这个读法. **不否定** `Goal`, 也不否定 `TU 1` 真的远高于 `TX` (读法 ψ₀(Ω_{Ω+1}) 对 ψ₀(Ω_Ω), 判断, 没有定理).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegSameVStrict where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; TX)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁
open import OCF.Lean.NegSameVSpine using (nat)

fk : Cd → ℕ → Cd
fk X zero = X
fk X (suc n) = hs hz

ω̂ : Cd
ω̂ = hl nat

-- 部分和就是 X + (n 个 1)
pt : ∀ X n → LeAt hz (Σ⁺ (fk X) n) (X ⊞ nat n)
pt X zero = L.≤-refl hz X
pt X (suc n) = Rel.s≤s (pt X n)

shape-up : ∀ X → LeAt hz (hs X) (hl (Σ⁺ (fk X)))
shape-up X = Rel.≤l 1 (L.≤-refl hz (hs X))

-- SameV.goal2 的 +2 同样
shape-up2 : ∀ X → LeAt hz (hs (hs X)) (hl (Σ⁺ (fk X)))
shape-up2 X = Rel.≤l 2 (L.≤-refl hz (hs (hs X)))

shape-bound : ∀ X → LeAt hz (hl (Σ⁺ (fk X))) (X ⊞ ω̂)
shape-bound X = Rel.l≤l (λ n → n) (L.idInc hz) (pt X)

shape-TX : LeAt hz (hs TX) (hl (Σ⁺ (fk TX))) × LeAt hz (hl (Σ⁺ (fk TX))) (TX ⊞ ω̂)
shape-TX = shape-up TX , shape-bound TX
```

## 结论 (按档)

- **[定理, 不用 UIP]** `pt`, **`shape-up`**, `shape-up2`, **`shape-bound`**, `shape-TX`.
- **[判断]** `Goal` 的 "+1" 不是强度证据; 要说 `TU 1` 高于 `TX` 一档, 要另外的定理 (例如 $\mathrm{TX}\cdot\omega\le\mathrm{TU}\,1$ 或更高).
