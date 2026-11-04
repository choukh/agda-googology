# 高度抽象: 验收

> **验收文件, 不在证书的闭包内.** 记号与标签只在这里出现. 结论写在 [LadderInf](LadderInf.lagda.md).
>
> **判决: PARTIAL.** 只有 $\theta=0$ 有标签.
>
> 证书 `LadderInf*` 只改导入, 克隆成 `LadderInfW*` (`Survey/scripts/laddernf/mk_infw.py`), 落在标签阶梯的树上, 与 [LadderNFAccept](LadderNFAccept.lagda.md) 的做法相同.
>
> 1. **`label-∞0`: `Lab (forceᴺ _ (GᴺTᵠ ∞ zero ev p)) tω`.** $\dot\Omega_\infty\,0$ 的计值带标签 $\psi_0(\Omega_{\psi_1(1)})$. 证明: 克隆世界的 `anchor` 加上已有的 `Tω-cert-label`.
> 2. **`label-fin`:** 实例 ℕ∪{∞} 的有限部分带已有的标签 $\psi_0(\Omega_{\Omega\cdot(m+1)+\theta})$, 经克隆世界的 `agree-fin`.
> 3. **记号一侧的形状 (`refl`, 有限检查):** `cof-t₁`: $\psi_0(\Omega_{\psi_1(1)+1})$ 是 $\omega$-共尾; `cof-u₁`, `pred-u₁`: $\psi_1(1)+1$ 是 $\psi_1(1)$ 的后继.
> 4. **有限测试:** `fgh-∞0`: 主线与克隆世界在第 0 项相等, `refl`. 不是证明.
>
> **没有做到的, 第一个障碍 (没有试完, 不是否定).** $\theta\ge1$ 的标签要两件事:
>
> - **标准形.** `labelᵠ` 的前提是 `NF₁ (ψ₀ u)`, 而 `Sb` 不含 $\psi_1(1)+c$. 单文件试验 (在 scratch 里, 没有留在仓库, 不算定理): 给 `ScafLadderZStandardOmega` 的副本加 `sψ : Ctbl c → Sb (ψ₁1 ∷ c)`, 只有 `leafInv₁`, `Sb-pred`, `Sb-fsn` 三处缺情形, 补上约 10 行, 全文件编译过, `NF₁-fsn` 等不用动. `Sb-fsn (sψ c[])` 落回已有的 `Ωᵐ n []`. 下游没有试: `Sb` 在克隆世界的底层, 改它要把 `ScafLadderZ*` 重新生成一份 (49 个模块, 约 2.6 万行), `NF-Ωᵐ` 的 ∞ 版本是新的记号证明.
> - **标签类.** `ScafLadderQClass`, `ScafLadderQPsi`, `ScafLadderQEval` 对 $m:\mathbb N$ 写的, 高度 $n$ 的节点标 $\Omega\cdot(n+1)+\nu$ (`Ωᵉ`). 要对 `HtS` 抽象, 加一个前缀映射 `fin n ↦ Ωᵉ (suc n)`, `∞ ↦ ψ₁1 ∷_`, 并给 `ql F` 这一行标 `lω`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInfAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.ScafLadderZUniform3Base using (Ev; ψ₀ᵗ)
open import OCF.Align.ScafLadderZUniform4Base using (Fl)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁)
import OCF.Align.EBO as E
open E using (T; natT; Ωt; cof; c1; cω; pred) renaming (_<ᵀ_ to _<ᵗ_)
open import OCF.Align.ScafLadderQClass using (Ωᵉ)
open import OCF.Align.ScafLadderQTop using (tω; ψ₁1; B)
open import OCF.Align.LadderMonoAccept using (Tω-cert-label)
open import OCF.Align.LadderNFAccept using (label-cert)
open import OCF.Align.LadderNFWForce
open import OCF.Align.LadderNFWEq using (toZ-≅; z≅)
open import OCF.Align.LadderInfWTop using (HS∞; fin; ∞)
open import OCF.Align.LadderInfWAgree using (anchor; agree-fin)
import OCF.Align.LadderInfWMain
import OCF.Align.LadderMonoWMain as MM
module I∞ = OCF.Align.LadderInfWMain HS∞
```

## §1 标签

```agda
label-∞0 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ ∞ zero ev p)) tω
label-∞0 ev p = Lab-≅ (≅-sym (forceᴺ-≅ (toZ-≅ (anchor ev p ev p z≅)) (MM.GᴺTω ev p) (I∞.GᴺTᵠ ∞ zero ev p))) (Tω-cert-label ev p)

label-fin : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ B m → ∀ {α} → α ≅ᴵ toLevel Y hY →
            ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ (fin m) α ev p)) (ψ₀ᵗ (Ωt (Ωᵉ (suc m) θ)))
label-fin m Y hY lY nθ pm {α} e ev p = Lab-≅ (≅-sym (agree-fin m α ev p)) (label-cert m Y hY lY nθ pm e ev p)
```

## §2 记号一侧的形状

$\psi_0(\Omega_{\psi_1(1)+1})$: 下面的 `refl` 只算形状.

```agda
u₁ : T
u₁ = E.ψ (natT 1) (natT 1) ∷ natT 1

t₁ : T
t₁ = ψ₀ᵗ (Ωt u₁)

cof-u₁ : cof u₁ ≡ c1
cof-u₁ = refl

pred-u₁ : pred u₁ ≡ ψ₁1
pred-u₁ = refl

cof-t₁ : cof t₁ ≡ cω
cof-t₁ = refl
```

## §3 跨世界的有限测试

**有限测试, 不是证明.**

```agda
import OCF.Free.Level as FL
import OCF.Align.LadderInfClosed as C

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

fgh-∞0 : C.fgh₀∞ 0 ≡ FGH (forceᴺ _ (I∞.GᴺTᵠ ∞ zero ev₀ zero)) 0
fgh-∞0 = refl
```
