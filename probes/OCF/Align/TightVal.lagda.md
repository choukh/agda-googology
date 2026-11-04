# 紧界旧树的值: 判决

> 入口. 问题: 当年停在 $\psi_0(\Omega_\Omega^2)$ 的两棵旧树, 值是不是错了? [OCFSpec](OCFSpec.lagda.md) 记着 "没有编译的否定", [Value](Value.lagda.md) §8 第 4 条写的是纸面判断.
>
> **判决: 两棵旧树都没有值 (没有证书), 不是值小. 紧界这棵树把占位换成单调的也上不去: 不超过 $\psi_0(\Omega_\Omega\cdot\Omega_2)$, 严格低于 $\psi_0(\Omega_\Omega^2)$. 占位没有被吸收.**
>
> 对象是三棵树, 都在 `Ordˢ zero` 里, 计值后都在 `Ordᶜ zero` 里, 不需要翻译:
>
> | 记号 | 定义 | 闭包的界 | 判决 |
> |---|---|---|---|
> | 紧界树 `TΩ2′ˢ` | [OmegaSqBase](OmegaSqBase.lagda.md) `ψᵉ′` | 紧, $i+1$; 第 $\ge2$ 层后继占位 $0$ | 没有 `Goodᴺ` (`no-T`) |
> | 旧地板树 | [Uniform2Base](Uniform2Base.lagda.md) `ψᵀ (Ψ (Ψ ∅ᵀ))` | 非紧, 字面最大者, `up (self n)` 不收紧 | 没有 `Goodᴺ` (`no-cert`) |
> | 新树 | [Uniform3Base](Uniform3Base.lagda.md) `ψᵀ (Ψ (Ψ ∅ᵀ))` | 非紧, 逐点上确界 | 带字面标签 `TΩ2-label` |
>
> **没有值怎么比.** 比较器是 `Cp B x`: $x$ 的任何 `Goodᴺ` 计值 $\preccurlyeq B$. 它不看链点. 前提无居留时是空真的, 所以每条都写明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TightVal where

open import OCF.Align.TightValBase public using (Cp; C; cloE; s≼-irrefl)
open import OCF.Align.TightValCap public using (High; module Cap)
open import OCF.Align.TightValAccept public using (A; tight-capΩ; tight-cap; above-gap; drop-at; A≺X; tight-drop; tight≼X; agree-Ω₂; Ω₃-above; Ω₃-tree; Ω₃-tree-above; low-true; low-true≼X)
open import OCF.Align.TightValNeg public using (no-W; no-low; no-Ω₃)
open import OCF.Align.TightValGlobal public using (ψᵉ′-≅ᴬ; no-Ω₃-any; no-T)
open import OCF.Align.TightValFloor public using (no-cert)
open import OCF.Align.TightValPh public using (module Capᴾ; idle; Tⁱ; idle-capΩ; idle-cap; idle-drop; idle-no-value; idle-witness; idle-witness-drop)
import OCF.Align.TightValTest
```

## 定理

- **`no-T : Goodᴺ (toZ TΩ2′ˢ) → ⊥`** ([TightValGlobal](TightValGlobal.lagda.md)). 坏节点 $\psi_0(\psi_\Omega(\Omega_2+\omega))$: 第 0 项非零, 第 1 项是占位 $0$, 极限不单调. 它在 $\Omega_3$ 的第 $[1,0,0,1,0,0,2,0,2,0,0,1,0,0]$ 项 (`refl`), 而第一个链点沿 $[0,1,0,0,3]$ 把分支带到 $\Omega_3$. 所以 `low-tree` 的 $0$ 不只是值小, 它让树不合法.
- **`no-cert`: 对一切环境, 旧地板树没有 `Goodᴺ`** ([TightValFloor](TightValFloor.lagda.md)). 比 `¬TΩ2-label` 强: 去掉了标签. 字段 `dy 0` 要 $L_1+1\sqsubseteq$ 第 0 点的层号, 假.
- **`tight-capΩ`: 一切 $\eta$, 一切环境, 紧界树在 $\Omega_\eta$ 处的任何证书计值 $\preccurlyeq$ `A`**, `A` 是带标签 $\psi_0(\Omega_\Omega\cdot\Omega_2)$ 的树. $\eta=2$ 处有证书 (`OmegaSq.GLΩ₂`), 不空真; $\eta=3$ 处空真 (`no-Ω₃-any`); 更高的 $\eta$ 有没有证书没有证, 判断没有.
- **`idle-capΩ`, `idle-cap`, `idle-drop`, `idle-no-value`: 占位换成空转, 同一个上界.** `Capᴾ` 对一切满足 `cPh`, `capPh` 的占位成立. 这里的证书存在性没有证, 没有否定. 前提可满足的实例是 `idle-witness`: $\Omega_2+1$ 处有证书, 值 $\cong$ `A`, `idle-witness-drop` 说它不 $\succcurlyeq$ 任何严格大于 `A` 的树, 而 `low-true` 给出带标签 $\psi_0(\psi_\Omega(\Omega_2+1))$ 的这样一棵.
- **值验收的回答.** `idle-no-value`: 空转树的任何计值都不能与 `TΩ2-label` 的树互相 `⊑⁰`.

## 第一个真掉值的地方

指数 $\Omega_2+1$. 到 $\Omega_2$ 为止紧界树与新树同标签 (`agree-Ω₂`). 占位 $0$ 在这里给 $0$, 空转给 `A`, 真值严格大于 `A` (`low-true`). 上确界在 $\Omega_3$ 处第一次掉: `Ω₃-tree-above` 说带标签 $\psi_0(\Omega_\Omega\cdot\Omega_3)$ 的树 (`Uniform3SqA.TΩ₃-label`) 严格 $\succ$ `A`, 而 `tight-capΩ` 与 `idle-capΩ` 在 $\eta=3$ 给 $\preccurlyeq$ `A`. 紧界树不存在 "走到 $\psi_0(\Omega_\Omega^2)$ 以上" 的问题.

## 有限测试

都在 [TightValTest](TightValTest.lagda.md), 比较器与盲区写在文件头.

- `same-Ω₂`: $\Omega_2$ 上紧界树与新树同形, 深度 9, 宽度 3.
- `same-low₂`, `diff-low-a`, `diff-low-c`: $\psi_2(1)$ 上深度 2 同形, 第一个分岔在 $[2,0,0]$, $0$ 对极限.
- `new-not-tight`: 新树在 `low-pop` 的位置界是 $2$, 不是紧的 $1$.
- `same-floor`, `bound-old`, `bound-new`: 指数 $\Omega_\omega$ 上旧地板树与新树外形相同 (深度 10, 宽度 3), 差别在闭包的界, 路径 $[0,2]$ 处 $\omega+1$ 对 $1$.

## 判断

- 旧地板树的问题是守卫, 不是值: 除了闭包的界, 这棵树与新树同形. 依据只有上面的有限测试和定义的差别 (`up (self n)` 一条子句), 没有编译的 "模界互模拟".
- 空转的 `Tⁱ` 有证书, 值就是 `A`. 没有证.
- 增长型占位 (`Ph r = lim (r·m)`) 不满足 `capPh`, 这里不覆盖. 不压帧就没有新的 $\hat\Omega$, 判断它到不了 $\psi_0(\psi_\Omega(\Omega_2+1))$.

## 这些定理不否定什么

只否定写明的树. 不否定别的紧界设计: `GuardTightTree`, `GuardWeakTree` 的栈和层号都不同, 没有比较. 不说 `Mlev`, `Stage Q`, `LoD` 能不能从新树去掉: 这里只说它们不能靠换回 `ψᵉ′` 这一族去掉. `D3-question` 不在这个工具的范围: $T_2$ 没有占位, 类 `C` 用不上; 它开放.

[Value](Value.lagda.md) §8 的第 4 条因此变成: 在 `ψᵉ′` 这一族里, 去掉非紧界的代价是定理 (`no-T`, `idle-capΩ`, `drop-at`), 不再是纸面.
