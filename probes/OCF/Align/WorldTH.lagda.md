# 高度进世界: $\psi_0(\Omega_{\Omega^2+a})$

> **判决: HOLDS (第一站 $\alpha=1$ 的 `HS`, 同一条闭包定理覆盖顶), PARTIAL ($T_\top\prec$ 这棵树没拿到, 给的是同族的定理).** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 这里不含记号, 记号和有限测试在 [WorldTHAccept](WorldTHAccept.lagda.md). 强度写 $\psi_0(\Omega_x)$. **读法都是判断, 没有基本列验收, 没有前驱结构验收, 没有序数值验收.**
>
> ## 做法
>
> `CumUp` 的层是 $(p,a)$, $p:\mathbb N$, 目标 $(q,t)$ 的 $t$ 自己是世界下界, 输出世界 $\max(u,t,a)$. 这里只改一处: **高度也是世界里的下标** (`WorldTHW` 的 `Hg`):
>
>     data Hg where  ht : A → Hg ; tφ : (A → Hg) → Hg
>     top = tφ ht
>
> - `ht a` 读作 $\Omega\cdot a$; `top` 读作 $\Omega^2$. `tφ` 带函数只是为了让 `Ω̇` 结构递归 (`f a` 是 `tφ f` 的子项; 零元的 `top` 在 `--without-K` 下过不了停机检查). 合法的只有 `f ≡ ht` (`HT`).
> - 层是 $(p,a)$, $p:$ `Hg`. 世界 $m=\max(u,t,a,\hat p,\hat q)$, $\hat p$ 是 `hA p` (`mx`). 顶的 $\hat{}$ 是 0.
> - **顶行是普通的 `oc`:** `Ω̇ top azero` 的第 $v$ 支是 `Ω̇ (ht v) azero`, $v$ 取世界里的下标. 没有新构造子. 第一支 `ht 0`, 单调性由 `Ωh⊴` 给.
> - 高度的比较 `hcmp` 在字面的世界之下做, 和 `cmpF` 同一件事. 顶之下的路径 `tp`, `tq`, 只在 `f ≡ ht` 时要求世界盖住高度 (`Hb`).
>
> ## 目标 1 的回答
>
> 判断 "目标自己是世界下界" 能落下来, 而且 **`T₊`, `tH` 这层不需要**. 上一轮的两条链不可比, 因为同一个闭包在两个世界算出的链差一个路径. 这里没有路径: 第 $n$ 个链点是 `chainᵒ gm (ψ p k …)`, 世界 $m$ 由 `mx` 规范给出, 两边模 `≈ᴬ` 相同 (`m≈`). 所以 `ψ⁰Q` 的 `hgt` 分支里两条链逐点 `≈` (`ch`), 和 `CumUp` 同一段代码, 只把 `<ᴺ-dec` 换成 `hcmp`, 对齐由 `hc≈` 给. 最小的可编译形状就是 `WorldTHW`.
>
> ## 闭包定理: 新写的, 不是迁移
>
> `WorldTHW` 到 `WorldTHMain` 合计 2741 行, 由 `CumUp` 的 2160 行改写, 多 581 行, 全在高度的接口 (`HO`, `Hb`, `hcmp`, `hc≈`, `Ωh⊴`, `Lh`). `ψW`, `ψ₀W` 对项递归, 不按高度分情况; `WF` 的定义没有变. 没有迁移 `CrossNext` 的 1 万行. `T₊`, `tH` 不在闭包里.
>
> ## 定理
>
> | 名字 | 陈述 | 文件 |
> |---|---|---|
> | `HS-T` | 对一切 $p$, $a$, `LB p a u₀`, `Gw u₀`: `HS (Tψ p a u₀ g e)` | `WorldTHMain` |
> | `HS-T₁` | $\psi_0(\Omega_{\Omega^2+1})$ 这棵闭树 `HS` (读法是判断) | `WorldTHInst` |
> | `HS-T₀`, `HS-T+` | $\psi_0(\Omega_{\Omega^2})$; 一切合法 $a\ge1$ 的 $\psi_0(\Omega_{\Omega^2+a})$ | `WorldTHInst` |
> | `T-strict` | 对一切 `NL p a`: `Tψ p a ≺ Tψ p (asuc a)` | `WorldTHGrow` |
> | `T₀≺T₁` | `T₀ ≺ T₁`, `T+≺` 对一切 $a$ | `WorldTHInst` |
> | `T+⊑`, `row-mono`, `row⊑top` | 下标, 行号上单调, 第 0 行 $\sqsubseteq$ 顶 | `WorldTHInst`, `WorldTHGrow` |
> | `top-val` | 顶行第 $i$ 个下标上的值 $\cong$ `Tψ (ht (η i)) azero` | `WorldTHGrow` |
> | `fsI`, `fsC`, `Shape.ch₀₁₂` | 节点和闭包的基本列; 链 $\Omega,\psi(\Omega),\psi(\psi(\Omega))$ | `WorldTHInst` |
>
> 为什么 `T-strict` 不是平凡的: `HS` 对很小的树也成立. `T-strict` 的证明走第 1 项 $\psi_0(\psi_{p,a}(\Omega_{p,a}))$ 的第一支 $\psi_{p,a}(1)$ 的第 2 项 $\Omega_{p,a}+\Omega_{p,a}\trianglerighteq\Omega_{p,a}+1$ (`Rep.D⁰`, `one⊴Ω`), 用到折叠确实把 $\Omega_{p,a}$ 作用进去. 但 **这只是 "比上一站大", 不是 "比上一站大很多"**: 这条定理不说 $T_1$ 超过 $T_0$ 的任何固定运算. 强度的读法仍是判断.
>
> ## 没有拿到的
>
> - **`T⊤ ≺ T₁`: 未走通, 没有动手.** `T⊤` 是 `CrossM` 一族, 这里是 `CumUp` 一族, 要跨族比较两个折叠. `CumUpAcceptVal`, `CumUpAcceptSim` 在 $\psi_0(\Omega_\Omega)$ 这一站做同类的事就要 600 行. 这不是否定. `t-⊤₃` 只说深度 3 形状不同.
> - **序数值, 基本列.** 第 $v$ 支是 $\Omega_{\Omega\cdot v}$, 记号的第 $\nu$ 项是 $\Omega_{\psi_1(\nu)}$, 下标的路不同, 基本列验收不期望成立 (判断). 没有写序数值的比较.
> - **$\Omega^2+\Omega$ 以上.** `Hg` 只有 `ht` 和顶, 下标 $a$ 是可数的. 再往上要把顶当作高度序列的一项 (比如 `tφ (λ a → top ⊕ ht a)`), `HT`, `hcmp` 要递归, 没有做 (判断).
>
> ## 累加
>
> **累加还在.** 输出没有前缀, 但第 0 层的闭包仍走 `next η y = η ⊞ (⌈y⌉+1)` (`v₀`, `vₛ`). 这不是修法二的前缀, 但和 `CumUp` 一样是累加的下标. 作者要去掉的话, 这一层还要换: [NoCum](NoCum.lagda.md) 的 `ψW` 不碰链, `Hg` 的改动与链无关 (判断, 没有编译), 卡点仍是那边的 `Hn`.
>
> ## 壁垒
>
> 判断: 不触犯. 壁垒要的是以 `Ordᴰ` 为精确初始段, 含 $\Omega$-共尾元, 且 **有界三歧**. `top` 是 $\Omega$-共尾的, 但它不作比较的上界: `hcmp` 要字面的 $m$ 盖住两边 (`HO`, `Lg m`), $m:$ `A`. `top` 之下任取 `ht a`, `ht b` 没有三歧. 也没有不可数下标作可数层的构造子: 第 $v$ 支的 $v$ 在 `oc` 的函数里, 和 `CumUp` 的 `Ω̇ (suc p) azero` 同一个位置.
>
> ## 受记号影响的形状
>
> `Hg` 的 `ht` 与 `top` 是照着 $\Omega\cdot a$, $\Omega^2$ 写的; 第一站选 $\alpha=1$, 对照 `fs-ψΩ1-1`. 不算 "树自足". 树侧的判据: `HS-T` 的证明不看记号, 新高度要给的接口是 `HO`, `Hb`, `hcmp` 这几个.
>
> ## 审计
>
> - **导入闭包.** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.CumRead --only OCF.Align.LevelFix --only OCF.Align.WorldTH OCF.Align.WorldTHInst`: 禁用表命中 0, `--only` 之外 0, 退出码 0; 本地 14 个模块. `agda --dependency-graph` 核对: 同样 14 个, 无 `EBO`, `Accept`. 正对照: `importclosure.py OCF.Align.WorldTHAccept` 退出码 1, 命中 `OCF.Align.EBO`.
> - **定义级切片 `depslice.py` (块数, 记号块, 词命中).** `Tψ` 142, 0, 0; `T₁` 144, 0, 0; `fgh₁` 148, 0, 0; `HS-T₁` 380, 0, 0; `HS-T` 377, 0, 0; `ψW` 347, 0, 0; `T-strict` 337, 0, 0; `T₀≺T₁` 341, 0, 0. 正对照 `WorldTHAccept:fs₂`: 51, 43, 2. 切片是语法级的.
> - **禁用构造.** `postulate`, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, 洞, `--cubical`, `--with-K`: 全部文件 0 命中.
>
> ## 代价
>
> `WorldTHMain` 742 秒, 峰值 15.2 GB. `ψ₀` 的字面展开很贵: 带抽象世界的陈述 5 秒, 同一件事带 `mx` 嵌套的陈述过 20 GB (`WorldTHGrow` 全部写成世界抽象). 把 `fsI` 代入 `Ω̇` 再写 `refl` 过 8 GB, 所以只留一般形式.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldTH where

open import OCF.Align.WorldTHInst public
```
