# 累加是否必需: 分离实验

> **判决: PARTIAL.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞. 这里只放入口和 `no-Lit-x₀`, 验收在 `NoCumAccept*`. 强度一律写 $\psi_0(\Omega_x)$.
>
> ## 分离的结果
>
> **`HS-T` 分成两半, 编译事实.**
>
> 1. **(p, a) 世界的闭包定理不碰链.** [NoCumMain](NoCumMain.lagda.md) 的 `ψW`: 折叠保 `WF`, 对一切高度, 一切层, 一切目标. [NoCumW](NoCumW.lagda.md) 到 `NoCumMain` 的导入闭包不含 `CumReadBase`, 编译器保证不引用 `next`, `⊞`, `cumA`. 目标 $(0,0)$ 也不特殊, 闭包留在数据里 (`Tᴰ`).
> 2. **链只在计值时出现** ([NoCumForce](NoCumForce.lagda.md)). 累加在这里只干两件事: 下标字面合法, 下标高于闭包的世界 (守卫).
>
> **第一件事不要累加.** `lit`, `graft₀` ([NoCumLit](NoCumLit.lagda.md)): 输出有 `Lit₀` 就有逐点 $\approx$ 于读出的字面合法副本, 还能指定第一位置. 没有前缀, 没有 $+1$, 不搬运. `Lit-force`: 计值的输出都有 `Lit₀`. 代价是定义依赖证书.
>
> **第二件事还没有去掉.** `G-T`, `HS-Tᴺ` 是条件定理, 前提是 `Hn`: 闭包的第一支的读出以闭包的世界为第一位置, 只在链点上的分支要求.
>
> | 站 | 不累加 | 档 |
> |---|---|---|
> | $\psi_0(\Omega_\Omega)$ | `T⁰`, `HS-T⁰`, 无条件; `T⁰≅ : fr T⁰ ≅ BTBOᴵ`, `label-T⁰` | **基本列验收, 定理** |
> | $\psi_0(\Omega_\Omega)$, 过 (p, a) 世界 | `TΩᴺ`, `Hn-Ω`, `HS-TΩᴺ`, 无条件 | 与 `T⁰` 只有有限测试 |
> | $\psi_0(\Omega_{\Omega+1})$ 及以上 | `HS-Tᴺ`, **条件于 `Hn`** | `Hn` 未证: **暂停, 未走通**, 不是否定 |
> | 一切 $\Omega\cdot p+a$, 只留世界前缀 $u+$ | `Tᵖ`, `HS-Tᵖ`, 无条件 | 不是目标形状; 强度只有有限测试 |
>
> ## 没有否定定理
>
> 不写 "非累加不可". `OCF.Free` 的 `FC.TΩ₂`, `HSᵀ` 已经说明: 到 $\psi_0(\Omega_{\Omega\cdot2})$ 有不累加的 `HS` 树, 下标是 `toLevel (ys m)` (源码事实). 所以 "累加是必需的" 在这一站是假的. 没走通的是 "(p, a) 世界 + 不累加 + 字面第一位置" 这一版的 `Hn`.
>
> ## 第一个障碍
>
> `Hn (Tᴰ 1 one one g₀ C.self)` 的范式 (Agda 输出):
>
>     (n : ℕ) → Hn (ψ⁰ 0 azero (chainᵒ (gw tt self)
>        (λ z₁ → ow self (gw tt self) (ow self (gw tt self)
>           (ψ⁰ 1 azero z₁ (gw tt self) (asuc azero) (gw tt self) self (suc self) (suc self)))) n)
>        (gw tt self) (asuc azero) (gw tt self) self (suc self) (suc self))
>
> $n=0$ 是 `Hn-Ω` 那一棵. $n=1$ 起分支里有 $\psi_{0,c}$ 作用在闭包上, $c\ll v$, $v$ 是链点. 这个闭包的世界含 $c$ (`mx`), `fp₁` 只给 $1$. 要的是 $c$ 在第一支的读出里. **纸面判断:** 第一支 $\trianglerighteq$ 外层分支在 $c$ 处的值 (`Ωfst`, `ψL′`), 外层分支单调给 $y_j\trianglelefteq$ 它, 而 $c\ll v_j=\mathrm{rd}\,y_j$. 嵌套时要对上下文归纳: 这是 `OCF.Free` 的 `Vis`, `Hon`, `Above` 同一件事. 所以判断是: **不累加只是证明更长, 长在这条守卫**, 没有编译. 没有动手写上下文类.
>
> 另一点, 判断: `mx` 把目标 $t$ 放进世界, 同高度的目标其实不需要 (比较只用层 $a$). 对字面上任意的 $a$, 当前写法的 `Hn` 可能是假的. 只有 $a$ 是输出的读出时上面的论证才适用. 没有定理.
>
> ## 账
>
> **省掉 (编译事实):** `next`, `cumA`, `cs`, `asuc` 补偿, 链上的 $\eta+$, 全部不在闭包里. 基本列: `T⁰` 与带标签的树逐项 $\cong$ (`term`), 累加的 `Tᶜ` 第 1 项就严格更大. 第一个下标的 $G(0),G(1),G(2)$: $0,1,16$ 对 $2,9,206933$. `OCF.Free` 的 `tr`, `back`, $\cong^I$ 比较这里也没有: 下标字面合法, `cmpN` 不搬运. 高度世界的文件比累加版短: `Psi` 215 行对 452, `Main` 379 对 607, 省的是第 0 层单独的折叠 (`ψ₀`, `em`).
>
> **新付:**
>
> - 定义依赖证书: `force` 读 `G`, `cell` 读 `Y-lit`, `Y-⊴`. 不累加的 `Tᴰ` 只是数据, 计值要证书. 这与 `Goodᴺ` 同形. 累加版 `Tψ` 不读证书.
> - 嫁接 `graftA`, `graftAt`, `lit`: `NoCumLit` 195 行, 累加版没有这一块.
> - 模 $\approx$: 下标与读出只差逐点相等 (`tie`), 证书无关性 `fo≅` 要走链.
> - `Vis`, `Hon` 的同类义务: `Hn`. 在 $\psi_0(\Omega_\Omega)$ 平凡, 再往上未证. 累加版这件事是 `next-⊲`.
>
> ## 与否定定理的关系
>
> - `no-rd`, `no-HS→Lgl`: 反例是 `HS` 而不是 `Lit₀` 的树 (下面的 `no-Lit-x₀`). 这里只读 `Lit₀` 的树, 不在前提里.
> - `dec⊲→LPO`: 这里不判定 $\triangleleft$, 嫁接只用已有的第一位置.
> - `no-cum-⊲`: 关于累加, 这里没有累加. `Tᵖ` 的前缀不走 `cumA`.
> - `no-⊞-left`: 只有 `Tᵖ` 有前缀, 世界 $u$ 是闭包自己的, 同一闭包的 $u$ 模 $\approx$ 相同.
> - `no-T`: `ψᵉ′` 一族的坏节点是占位值. 这里 `o0` 处写 $\Omega_t$, 没有占位 (判断, 没有编译的比较).
> - 壁垒: 比较都在字面上界之下 (`cmpN`), 与上一轮相同.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCum where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁)
open import OCF.Free.Level using (HS; z≅; s≅; l≅)
import OCF.Free.Level as FL
open import OCF.Align.CumReadBase using (natO; ω₁)
open import OCF.Align.CumUpClean using (x₀; HS-x₀)
open import OCF.Align.NoCumLit using (Lit₀; _⊴₀_; r0; s0; l0; Ord₀)
open import OCF.Align.NoCumOmega using (T⁰; HS-T⁰)
open import OCF.Align.NoCumHon using (TΩᴺ; HS-TΩᴺ; Hn-Ω)
open import OCF.Align.NoCumForce using (G-T; Tᴺ; HS-Tᴺ; Hn; G; force; Lit-force)
open import OCF.Align.NoCumPre using (Tᵖ; HS-Tᵖ)
open import OCF.Align.NoCumMain using (ψW)
```

## `no-rd` 的反例不在 `Lit₀` 里

```agda
nope : ∀ n → ω₁ ⊴₀ natO n → ⊥
nope zero (r0 ())
nope (suc n) (r0 ())
nope (suc n) (s0 d) = nope n d

no-Lit-x₀ : Lit₀ x₀ → ⊥
no-Lit-x₀ (st , _) with st 0
... | r0 (l≅ h) with h 0
...   | ()
no-Lit-x₀ (st , _) | l0 k d = nope (suc k) d

-- 前提可满足: x₀ 是 HS 的
_ : HS x₀
_ = HS-x₀
```
