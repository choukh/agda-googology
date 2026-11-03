# 脚手架阶梯: 从标签顶上往上爬 (判决: 到 $\psi_0(\Omega_{\psi_1(1)})$ 是定理, $\psi_0(\Omega_{\psi_1(1)+1})$ 未到)

> 底座: `P` 一层 [ScafLadderTree](ScafLadderTree.lagda.md), [ScafLadderClass](ScafLadderClass.lagda.md), [ScafLadderPsi](ScafLadderPsi.lagda.md), [ScafLadderRel](ScafLadderRel.lagda.md), [ScafLadderEval](ScafLadderEval.lagda.md), [ScafLadderTop](ScafLadderTop.lagda.md); 塔 [ScafLadderQ](ScafLadderQ.lagda.md) (定义, 切片 0), [ScafLadderQClass](ScafLadderQClass.lagda.md), [ScafLadderQPsi](ScafLadderQPsi.lagda.md), [ScafLadderQRel](ScafLadderQRel.lagda.md), [ScafLadderQEval](ScafLadderQEval.lagda.md), [ScafLadderQTop](ScafLadderQTop.lagda.md); 记号 [ScafLadderNF](ScafLadderNF.lagda.md); 有限测试 [ScafLadderWalk](ScafLadderWalk.lagda.md); 克隆世界 `ScafLadderZ*` (机械复制加补丁, 见文末). 接 [LvCert](LvCert.lagda.md), [Uniform5Top](Uniform5Top.lagda.md).
>
> **判决 (编译过的定理, 无条件, `--safe`).**
>
> | 目标 | 定理 | 一条还是抄写 |
> | --- | --- | --- |
> | $\psi_0(\Omega_{\Omega\cdot2+1})$ | `TΩ·2+1` (塔), `TΩ·2+1-label` (`P`) | `TΩᵠ-label` 的实例 |
> | $\psi_0(\Omega_{\Omega\cdot2+\theta})$, $\theta<\psi_0(\Omega_{\Omega\cdot3})$ | `TΩᵠ-label 1`, `TΩ₂-label` | 同一条, 对 $\theta$ 一致 |
> | $\psi_0(\Omega_{\Omega\cdot3})$ | `TΩ·3` | 实例 |
> | $\psi_0(\Omega_{\Omega\cdot(m+1)})$, 一切 $m$ | `TΩ·-label m` | 同一条, 对 $m$ 一致 |
> | $\psi_0(\Omega_{\Omega\cdot(m+1)+\theta})$, $\theta<\psi_0(\Omega_{\Omega\cdot(m+2)})$ | `TΩᵠ-label m` | **一条定理, 不按 $m$, $\theta$ 抄写** |
> | $\psi_0(\Omega_{\Omega\cdot\omega})=\psi_0(\Omega_{\psi_1(1)})$ | `Tω-label` | 顶层一步 (这个项不在 `NF₁`, 基本列都在) |
> | $\psi_0(\Omega_{\psi_1(1)+1})$ | **没有** | 第一个障碍, 见下 |
>
> 全部是 `Lab₀ x t = Σ (Goodᴸ (toZ x)) (λ G → Lab (forceᴸ _ G) t)`, 证书走标签路线. 树 `Tᴾ`, `Ψ`, `Tᵠ`, `Tω` 的依赖切片到记号定义 0 个 (正对照 `TΩ₂-label` 92 个), 所以**树本身不读记号, 只有证书读.** `agree-Ω₂`: `P` 与塔的树经 `Lab-uniq` $\cong$.
>
> **任务 1: 树的修正 (编译).** 三件, 都写在定义里, 没有项文法, 没有 `oev`, 没有判决参数.
>
> 1. **目标在同高度或更低时, 折叠是求值, 不是树到树.** `Ψ : … → t <ᴵ w H → Q m α φ χ → Q H t (Fl ⊔ φ) (Z* χ)`. 这与 `ψ̄ : O → Ordˢ` 同形, `Ordˢ` 换成 `O`, 再换成 `Q H`. 高度 $n\ge H$ 的闭包落成字面闭包 `qŝ c₀` (守卫 $c_0\sqsubseteq\eta$, 不是上界), $c_0$ 由目标与闭包自己的地板算出 (`head-lit`, `bound-free`), 以后不再读地板. `noW` 的反例里那个闭包的界是 $a+1$, 不再是路径上的 $\tau+1$. 比较 $k$ 对 $t$ 在世界 $w\,H$ 之下 (`<ᴵ-dec`), 不要 `oev`.
> 2. **高度由类型分开.** 高度 $n$ 就是层号 $\Omega\cdot(n+1)$ 的 $n$: `Q m` 的第 $n$ 格地板 `χ n`, 节点 `qΩ↓ q` 的输入是 `Q n k`. 目标 $H$ 的求值只吃 $i\ge H$ 的世界 (`Eh`). 这不是 [LvKey](LvKey.lagda.md) 否定的节点标签 (`noTag`): 它不是 `Ordᴵ` 上的函数, 是层号语法的一个坐标. 代价: $\psi_1(1)+\Omega$ 起 ℕ 不够 (`noTimes`, 那里没走到).
> 3. **地板在下降时收紧 (`omk`).** 协调者提示的 `at a`/`oup`, 这里写成记号: $\dot\Omega_{a+1}$ 的分支与 $\dot\Omega_{\lim f}$ 的第 $n$ 项带构造子 `omk r z x`, $z$ 是低一层的原树, $x=$ `ι r z`. 其余函数都忘掉 $z$, 只有 `ι↓` 读 $z$, 地板收紧到下一层, 与 `Ordˢ` 的 `up` 同形.
>
> **为什么第 3 件不可省 (判断, 纸面, 没有编译成否定).** 第 1 件只修了那个闭包本身. 和式 $x+x$ (`repᵠ`) 里右边那份的闭包要读左边那份的地板, 因为分支 $\eta$ 的世界要装下左边的节点 (目标 $k$ 与左边的节点 $i$ 真要比较, 公共上界只能是 $\eta$). 左边若是 `ι↓` 的像而地板是路径上的 $\tau$, 节点却已走到 $a<\tau$ 之下, 就又是假的支配. 所以地板必须是真实出现的节点. 标签类里的落点是档位 `Lq … true`: `ls` 行多一个字段 `FC`, "$c$ 的地板在标签里出现". `ψ` 的输出天然满足 (`FC-Ω`, 目标 $\tau$ 经 `oτ` 出现).
>
> **任务 2: 第一个障碍 (判断).** 两件, 都是工程量, 没有否定定理, 也没有试.
>
> 1. **树.** $\Omega\cdot\omega+\alpha$ 的树要高度跑遍全部 ℕ: 一层 `Qω` 建在整个塔上 (`qΩ↓ n`, `qcl n` 对一切 $n$). `Q m` 的证明几乎不看 $n<m$, 把 `n <ᴸ m` 抽象成高度集就行.
> 2. **记号.** `Sb` 要加 $\psi_1(1)+c$. 这是极限叶, `leafInv₁` 不碰它; `Sb-fsn` 落回 `SbΩᵐ`. 标签侧 `LimRow`, `gtμ`, `FC-Ω` 的 $\Omega\cdot(n+1)+\nu$ 要换成 $\psi_1(1)+\nu$.
>
> 试验 (临时改动, 已撤回, 不在仓库): 给克隆的 `StandardOmega` 加 `sω : Ctbl c → Sb (ψ₁(1) ∷ c)` 约 15 行, 这一篇编译通过; 下游没有重建.
>
> 再往上 ($\psi_1(1)+\Omega$) 才撞 `noTimes`: 高度要超出 ℕ, 那是 [LvKey](LvKey.lagda.md) 的键的问题 (判断).
>
> **任务 3: 去除账本.** 每条读法: 这项义务现在由什么证出; 它是否看起来是树侧命题 (判断); `Goodᴺ` 是否也要它. 证书的字段都在 `Od` 的行里 (`limᴸ`, `ĉᴸ-mk`, `domᴸ`, `clo0`, `ŝ0`), 这里没有新增证书规则.
>
> | 字段或条件 | 现在的来源 | 树侧命题? (判断) | `Goodᴺ` 也要? |
> | --- | --- | --- | --- |
> | `gl.st`, `gc.mo₀`, `gc.mo`: 相邻基本列的树单调 | `mono-lab`: `fs-mono₁` (记号单调, 要 `NF₁`) + `Lab-oc` | 是, "分支随下标单调". [UniformNF5Main](UniformNF5Main.lagda.md) 的 `Vm` 在 `O` 上已证 | 要 (`gl`, `mo₀`, `mo`) |
> | `gc.d₀`, `gc.dE`: 链点 $\sqsupseteq$ 界 $c$, $c\le$ 目标 $+1$ 或 $\chi$ 的项 | `domᴸ`: `occ<` (可见参数小于项, 要 `Bnd₁`) + `Lab-oc`; 见证经 `pickΨ`, `pickF` | **是, 且是这次的关键.** "$\psi_0(\ldots\psi_{\Omega+a}(\ldots)\ldots)\sqsupseteq a+1$", 因为叶子是 $\dot\Omega_a$, 而 $\psi_0(\Omega_{\Omega+a})\sqsupseteq a$ 对 $a$ 归纳可得 (纸面). 记号没有贡献这个不等式的形状 | 要 (`dy`). 这是 [LvCert](LvCert.lagda.md) 说的同层支配 |
> | `FW₀`, `Ob`, `Occ` (含新的 `oτ`) 的见证 | 树的地板 + 标签, 下标在标签里的出现 | 部分. `oτ` 是 "目标 $\tau$ 是 $\Omega+\tau$ 的尾巴". 树侧对应是 `flo` 的收紧 | 不要: `Goodᴺ` 直接要不等式 |
> | `pickMax` (多个地板项挑最大的见证) | `cmpᵀ` + `Ilt`/`Ieq` | 否, 是证明手段: 界是逐点上确界, 直接支配每一项就够 | 不要 |
> | `γ`, `Gg`, `lE`, 链点的标签 | `gtW`, `penW`, `repW` 的 `refl` 级计算 | 否. 这正是标签定理的内容, 去掉证书不需要它 | 不要 (`ys` 取代 $\gamma$) |
> | `li` 的 `hP`/`hI`, `InpW`, `Hn`, 模式 `wkm` | Uniform3 的类, 读 `NF₁`, `Idx` | 是 (与 `UniformNF5` 的 `Gᵀ`, `dt`, `dg` 同题), 已有树侧写法到 `O` | 要, 形式不同 |
> | 比较的回答 `pen-of`, `gt-ofᵇ`, `gt-ofᶜ`, `ltμ`, `gtμ` | `cmpᵀ`, `Ilt`/`Ieq`; 只用于对上基本列 | 否. 树里是 `<ᴵ-dec`, 不读这些 | 不要 |
> | `NF₁` 含一切 $\Omega\cdot(n+2)+c$ (`sΩ² n`), `NF₁-fsn`, `fs-mono₁`, `cofin₁`, `NF-Ωᵐ` | 克隆 `StandardOmega`, 约 150 行补丁. 一次写完, 对 $n$ 一致 (`SW`, `pick²`, `visΩᵐ`) | 否, 纯记号; 不再是每阶段输入, 但 $\psi_1(1)$ 还要一次 | 不要 |
> | `FC` (档位 `true`): 层 $c$ 的地板在标签里出现 | `FC-τ`, `FC-pre`, `FC-rep`; `ψ` 的输出头是 $\tau$ | **是, 伪装的树命题:** "`ι↓` 的地板是真实出现的节点". 应当能写成 `omk` 上的树谓词 (判断) | 不要这个形式, 但 `ι↓` 上的 `Goodᴺ` 要它的结论 |
> | 文法 | 树不读. 高度 $n$ 是层号的语法坐标, 判断: 这是读来的形状, 不是读来的定义. `Syn` 的项文法没有用 | | |
>
> **从记号读了什么 (步骤 2 的目标).** 树的定义没有读记号的定义 (切片 0). 形状是看记号定的, 四处: (a) `Ψ` 的存在: `c-low`, `c-fs` 说界是目标 $a$; (b) 地板必须真实出现: 来自 `Occ`, `Bnd₁`; (c) 闭包第一支在 $\eta=1$; (d) 高度 $\Omega\cdot m$ 的分块. 判断: (a) 可以写成树语言: 闭包是守卫函数 $(\eta,c\sqsubseteq\eta)$, 世界一到就落成字面. (b) 也可以: `flo` 跟着 `omk`. (c), (d) 不知道怎么由树逼出.
>
> **`noW` 到这里的回答.** `Goodᴺ` 的 `dy`, 也就是 "链点 $\sqsupseteq$ 界", 现在的界是 $a+1$. 纸面上它是树命题: 链点的叶子是 $\dot\Omega_a$, 而 $\psi_0(\Omega_{\Omega+a})\sqsupseteq a$ 对 $a$ 归纳. 我没有编译这一句, 这里 `dy` 仍由 `domᴸ` 证. 这是步骤 2 第一个要做的.
>
> **有限测试 ([ScafLadderWalk](ScafLadderWalk.lagda.md), `refl`, 不是证明).** `c-t₂`, `c-t₁`, `c-t₁′`, `c-t₂₂`: `P`, 精确, 深 12 到 16. `c-W`, `c-W₂`, `c-W⁺`, `c-dev`: $W$ 与 `Zero.dev`, 比较器与 [UniformLvAccept](UniformLvAccept.lagda.md) 同一套. `q-t₂`, `q-t₁`, `q-t₃`, `q-t₃₁`, `q-t₄`, `q-tω`: 塔. `ctl`: 对照报告不一致. $W$ 不被标签定理直接覆盖 (走到它要经过证书), 所以它的测试不是冗余的.
>
> **克隆世界.** `ScafLadderZ*` 是 48 篇机械复制 (加 `ScafLadderZLvWalk`), 因为 `NF₁`, `Occ` 进了类型, 而规则禁止改已有文件. 补丁: `Sb` 加 `sΩ² n`, `Leaf₁` 加 `sing² n`; `Occ` 加 `oτ`. `O` 加 `omk`, `Ld` 加档位与 `lob`, `Rᵒ` 加 `rob` 是 `P` 路线用的, 塔不用 `O`. 其余逐字. **要是作者同意就地改 `StandardOmega`, `SystemOmega`, 这些克隆都可以删** (判断: 补丁约 200 行).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadder where

open import OCF.Align.ScafLadderTree using (P; Ω̇ᴾ; Ψ; ψ̄ᴾ; Tᴾ; ι↓)
open import OCF.Align.ScafLadderWalk using (c-t₁; c-W; ctl; q-t₃; q-tω)
open import OCF.Align.ScafLadderTop using (TΩ₂-label; TΩ·2+1-label; TΩ·2′-label; NF-Ω₂; head-lit; bound-free)
open import OCF.Align.ScafLadderQ using (Q; Tᵠ; Tω)
open import OCF.Align.ScafLadderQTop using (TΩᵠ-label; TΩ·-label; TΩ·+1-label; TΩ·2+1; TΩ·3; Tω-label; agree-Ω₂)
open import OCF.Align.ScafLadderNF using (NF-Ωᵐ)
```
