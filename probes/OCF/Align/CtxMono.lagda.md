# 带上下文的层单调: 入口 (暂停)

> **判决: PARTIAL, 上界未走通, 暂停, 没有否定定理.** 选的路线是 `NoCumNode` (不累加, 第 0 层是值). 全文 `--safe --without-K --lossy-unification`. 本文件只用 `OCF.Align.Value` 的 $\preccurlyeq$, 它的导入闭包含记号模块 (`importclosure.py` 给 FAIL, 经 `Value`), 所以本文件算验收侧; 定义 (`NoCumNode*`) 不受影响. 参照树与标签在 [CtxMonoAccept](CtxMonoAccept.lagda.md).
>
> 这里编译的只有**把验收化成逐项比较**的那一步: `upper-if`, `accept-if`. 剩下的前提 `∀ n → fr (tm {m} {gm} {um} {am} d n) ≼ y` 就是 "带上下文的层单调" 在这一棵树上的实例: 第 $n+1$ 项是 $\psi_0(\psi_\Omega(\gamma_n))$, 要对参照树的 $\psi_0(\psi_\Omega(\gamma'_n))$ 在 $\gamma_n\preccurlyeq\gamma'_n$ 下单调, 上下文 $\psi_0(\psi_\Omega(\cdot))$ 里有闭包. 这条没有写.
>
> **没有写的原因 (判断).** 两棵树的类型不同: 左边是 `𝓞 p a u` 的值 (`NoCumNodeE`), 右边是 `OCF.Free` 的 `O c φ` 经 `ψ̄` 到 `Ordˢ zero` 再 `forceᴺ`. 逐项比较要一个跨树的关系, 覆盖 `oc`/`oclo`, `oi`/`oΩ`, 加法与 `ĉᴸ`, 地板与 `tr`, 并对证书全称. 估计 1200 到 2000 行, 与上一轮同一个估计, 这一轮没有新的实测. `Ψ-emb` 只在 `Level` 的 $\psi^0(\Omega_\ell)$ 上, `AddCloRel.Main.main` 只在和的折叠上 (没有闭包 `nκ`), `V-≃` 只在 `LadderOrd` 的树上; 三个都不直接给跨树的一步.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CtxMono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open import OCF.Align.Level using (Ordᶜ)
open import OCF.Align.Value using (_≼_; l≼; _≈ᵛ_)
open import OCF.Align.CumUpAcceptSim using (fr)
open import OCF.Align.CumReadCF using (A; azero)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (Ord₀)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumNodeE
open import OCF.Align.NoCumNodeMain using (G₁; T₁)
```

## §1 项

`tm d n`: $\psi_0(\Omega_{\Omega+1})$ 的第 $n$ 项, 对任何证书.

```agda
tm : ∀ {m gm um am} (d : E (Ω̇ 1 one) g₀ m gm um am) → ℕ → Ord₀
tm d = vRs d

-- 值就是项的极限, 定义性相等
val-tm : ∀ {m gm um am} (d : E (Ω̇ 1 one) g₀ m gm um am) → val (Ω̇ 1 one) {g₀} {m} {gm} {um} {am} d ≡ FL.lim (tm {m} {gm} {um} {am} d)
val-tm d = refl
```

## §2 验收化成逐项

```agda
upper-if : ∀ {m gm um am} (d : E (Ω̇ 1 one) g₀ m gm um am) {ℓ} {y : Ordᶜ ℓ} → (∀ n → fr (tm {m} {gm} {um} {am} d n) ≼ y) → fr (val (Ω̇ 1 one) {g₀} {m} {gm} {um} {am} d) ≼ y
upper-if d H = l≼ H

accept-if : ∀ {m gm um am} (d : E (Ω̇ 1 one) g₀ m gm um am) {ℓ} {y : Ordᶜ ℓ} → (∀ n → fr (tm {m} {gm} {um} {am} d n) ≼ y) → y ≼ fr (val (Ω̇ 1 one) {g₀} {m} {gm} {um} {am} d) →
            fr (val (Ω̇ 1 one) {g₀} {m} {gm} {um} {am} d) ≈ᵛ y
accept-if d H L = upper-if d H , L
```
