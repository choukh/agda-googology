# $\psi_0(\Omega_{\Omega+1})$, 不累加: 入口

> **判决: 证书 HOLDS, 序数值验收未走通.** 不累加, 无前缀, (p, a) 世界的 $\psi_0(\Omega_{\Omega+1})$ 的数据树有无条件的证书 `G₁` ([Om1HnMain](Om1HnMain.lagda.md)). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞. 不含记号; 记号只在 [Om1HnAccept](Om1HnAccept.lagda.md).
>
> ## 定理
>
> | 定理 | 说的 | 档 |
> |---|---|---|
> | `G₁ : G (Tᴰ 1 one one g₀ C.self)`, `T₁`, `HS-T₁` | $\psi_0(\Omega_{\Omega+1})$ 的数据树有证书, 闭项 | 证书, 定理 |
> | `G-Tᴿ : Root p a → G (Tᴰ p a …)` | 对一切 $p,a$, 只差根上的义务 | 证书, 条件定理 |
> | `root₀`, `root₁`, `root₂` | $a=0,1,2$ 时 `Root` 对一切 $p$ 成立 | 定理 |
> | `G-p₁`, `G-p₀` | $\psi_0(\Omega_{\Omega\cdot p+1})$, $\psi_0(\Omega_{\Omega\cdot p})$ 的数据树对一切 $p$ 有证书. **读法是判断**, 大小没验 | 证书, 定理 |
> | `no-Root` | 对字面任意的 $a$, `Root` 是假的 | 否定, 定理 |
> | `shift` | 第 $(0,0)$ 层 $W\oplus$ 闭包的第 0 个链点读的输出以 $W$ 为第一位置 | 定理 |
> | `same-T⁰`, `term₀`, `label-term₀`, `low` | $\psi_0(\Omega_\Omega)$ 这一站不变; 第 0 项过基本列验收; 非严格下界 | 验收, 定理 |
>
> ## `Hn`
>
> **字面的 `Hn (Tᴰ 1 one one g₀ C.self)` 没有证, 也不需要.** 这里不经 `Hn`, 直接造证书 (`X`). 字面的 `Hn` 比链需要的强: `Rdv` 的 `rdS` 对任意 $v'$ 的输出都要守卫, 不只是链点. `Bb` 的 `chS` 要 $v\triangleleft v'$, 这里只有链上才有 (判断: 这一条不是字面任意 $v'$ 能给的, 是否为假未判定).
>
> **写成结构字段: 可以.** 义务分三层, 只有第三层看具体的项:
>
> 1. **闭包定理不看阶段.** `Psi`, `AddG.Add`, `X` 都是对一切 `Gd` 的项, 一步. 守卫是 `OcR.gd`, 每个折叠帧贡献一个候选 ($u$ 来自源, $t$ 来自 `𝓥′` 的 `vs`, $a$ 来自源的 `gd`).
> 2. **`Bach` 这一步是 `ΩG` 里的 `ch₀`, `chS`** (`bach₁`), 只出现在 $\Omega_{p+1,0}$ 这一行, 对一切 $p$.
> 3. **根上的义务:** `Root p a`. 这就是 "下标带证据" 的准确形状: 不在世界上, 不在每个下标上, 只在根 $\psi_{0,0}$ 对 $a$ 之下的层.
>
> 所以上一轮的判断 "`a>t` 时 $C\circ\psi_{q,t}\notin\mathcal V(a,u)$, 类省不掉" 对了一半: 对子类全称 (`BrR.prem`) 确实留着; 但 `Class`, `ClassF`, `Rules` 里层的下移, 搬运, 地板的大部分没有对应.
>
> ## 比 `OCF.Free` 省的 (读源码, 判断)
>
> - 上下文不按层分类 (`Cx` 没有层指标), 所以 `oe`, `oL`, `ow` 不下移上下文: 没有 `Dn`, `sh`, `Inp`, `Tr`, `Bk`, `Dtr`.
> - 字面合法的层, `cmpN` 不搬运: 没有 $\cong^I$, `≈ᶜ`, `≈ᵒ`, `cg` 字段.
> - `WF` 已给单调和同余, `Gd` 不再带; `⊴` 无条件被折叠保持, `Rules` 的 $\sqsubseteq^T$ 一族没有对应.
> - 写成对项递归的函数 (同 `WF`), 不是归纳族.
>
> 留下的: 类, 对子类全称, `FlOver`, `Over` (即 `Above`), `dn` (即 $\sqsubseteq^E$ 的往下搬).
>
> ## 第一个障碍 (序数值验收)
>
> 见 [Om1HnAccept](Om1HnAccept.lagda.md): `add⁰` 对第 $(0,0)$ 层闭包, 链点读 $W\oplus x$ 的输出; `OCF.Free` 读没加的 $t_0$. 判断: `T₁` 与 `GᴺΩ̇ 1` 的树不 $\cong$, 所以互模拟走不通, 要吸收, 或者改折叠 (加一个 `oĉ` 型的节点, 新文件). 都没做, 暂停. 这是判断, 没有否定定理.
>
> ## 翻译账
>
> | 东西 | 来源 |
> |---|---|
> | $(p,a)$ 层的形状 | 读自记号, 上一轮已有 |
> | 这一轮的折叠 | 没有改. 没有新构造子, 新节点 |
> | `Sees`, `𝓥`, `𝓥′`, `Fo` | 树逼的: 守卫要字面第一位置 |
> | `Over`, `st` | 树逼的: 上升时链的上下文要留在类里 |
> | `FlOver`, `OsR.clk` | 树逼的: `rep` 的上下文 $C\circ(W\oplus)\circ\psi$ 要留在类里 |
> | `OsR.hon` | 树逼的; 前提 `Fp one` 是因为 `os o0` 的第一支是 $0$ |
> | `Bb` (即 `𝓑`) | 树逼的: 链点之下看得见 |
> | `Hb`, `Hd` | 树逼的: 只为 `idC` 不收高层的项 |
> | `Root` | 树逼的, `no-Root` 说明不能去掉 |
> | 整体的类的写法 | 照 `OCF.Free.Good` 的形状, 那边是记号无关的 |
>
> 全文没有读记号的字段.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1Hn where

open import OCF.Align.Om1HnMain using (G₁; T₁; HS-T₁; G-Tᴿ; Root; root₀; root₁; root₂; G-p₁; G-p₀)
open import OCF.Align.Om1HnNeg using (no-Root; shift)
```
