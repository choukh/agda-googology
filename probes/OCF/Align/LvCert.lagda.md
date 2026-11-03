# 新树上的证书: 这棵树过不了 $\Omega\cdot2$ (判决: FAILS)

> 接 [UniformLv](UniformLv.lagda.md). 底座 [LvCertRel](LvCertRel.lagda.md), 否定 [LvCertNeg](LvCertNeg.lagda.md), 接口 [LvCertWorld](LvCertWorld.lagda.md) 都不用记号的定义 (切片见文末). 记号只在验收节 [LvCertAccept](LvCertAccept.lagda.md).
>
> **判决: FAILS. [UniformLvTree](UniformLvTree.lagda.md) 的 `T₀` 在任务的每一个过 $\Omega\cdot2$ 的目标上都没有 `Goodᴺ`. 这是编译过的定理, 不是证明没写出来. 种类检验看不见它, 因为坏的是闭包的界, 不是形状. 新树上的正面定理一个也没有: 锚点 $\psi_0(\Omega_{\Omega\cdot2})$ 也没有证出, 闭包定理没有写.**
>
> **编译过的否定.**
>
> - `noCert₂ cf`: `Goodᴺ (toZ (T₀ (suc (Ω· 2)) cf)) → ⊥`, 对一切证书 `cf`. 即 $\psi_0(\Omega_{\Omega\cdot2+1})$ 没有证书.
> - `noΩ· m cf`: `T₀ (Ω· (3+m)) cf` 没有证书. 即 $\psi_0(\Omega_{\Omega\cdot m})$, $m\ge3$.
> - `noΩ·ω cf`: `T₀ Ω·ω cf` 没有证书. `noLv₊ m`: $\Omega\cdot m+1$, $m\ge2$.
> - `noW`: 更基本的形式, 对任何 $W=$ `owk wl (Ω̇ D)`, $\psi(W\oplus\dot\Omega_D)$ 没有证书, 世界任意.
>
> **第一个障碍, 也是任务 3 的答案: 同层支配是假的.** "链点严格增长所以支配 $\tau$" 不成立, 反例就在 $\Omega_{\Omega\cdot2}+\Omega_{\Omega\cdot2}$ 里:
>
> 1. 外层闭包的第 0 个链点 $\tau=\psi_0(W+\Omega_{\Omega+1})$, 走进分支 $\tau$: $W\oplus$ `ι (db τ)` $\dot\Omega_{\Omega+\tau}$.
> 2. 沿 $0<\tau$ 的字面路径走到节点 $\Omega_{\Omega+1}$ (`Walk`), 取第 1 个链点, $W$ 落到目标 $\Omega$ 之下: $\psi_\Omega(W\oplus\dots)$. 走到那份 $W$ 的闭包 (`node`).
> 3. **`ι (db τ)` 对闭包加地板 `tk 1 τ`.** 闭包与外层同高度, 所以界 $\ge\tau+1$ (`Bd-in`, 路径 `kl (kl (kr (kr k)))` 读的正是嵌入的那一项).
> 4. 那个闭包的第 0 点是 $\psi_0(W+\psi_\Omega(\Omega_{\Omega+1}))$. 它与 $\tau$ 无关: 掩码互模拟 (`⊕≈`, `M.R-ψ`) 把它与 $\tau$ 自己的展开里的同一个点连起来, 所以层号 $\sqsubseteq\tau$.
> 5. $\tau+1\sqsubseteq\tau$, 矛盾. 这里 $\tau$ 是真实的链点, 不是 `noAll` 那样的 "对一切 $K$".
>
> **为什么是定义的错, 不是记号的错.** `c-low`, `c-fs` (验收节, `refl`): 记号说这个第 0 点确实低于 $\tau$, 目标 $\Omega$ 之下 $\Omega_{\Omega\cdot2}$ 的基本列的第 0 元不看 $\tau$. 真正要的界是目标的层 $\Omega+a$ 的 $a$, 不是路径穿过的分支 $\tau$.
>
> **编译过的定理 (底座).** `irr`, `clashL`, `clashE`: 字面前驱不回到自身, 比较跨世界一致, 对一切 `LI`, 不要 `WF`. `Rel S`: 新树上的跨层互模拟, 带 `oev` 的跨世界行 `rev` 与高度掩码; `R-⊕`, `R-ι`, `R-ιˡ`, `R-ιʳ`, `RΩ̇`, `R-tr*`, `R-ψ`, `R→≈`. `_∼ᶜ_`: 地板的语义对齐, 有单位律. 这部分对任何修正后的树大概都用得上 (判断).
>
> **没有做到的, 按任务编号.**
>
> - 任务 1: `Worlds` 是接口, `worldℕ` 是实例, `Core.noSame` 对任何实例成立. 闭包定理不存在, 所以 "定理在换键后不变" 无从说起. 判断: 否定的形状换键不变, 因为 $W$ 的闭包与外层闭包都在层号 $D$ 上; 键若随层号走, 它们同键.
> - 任务 2: **锚点没有证出.** 没有走桥: `T₀ (Ω· 2)` 与旧的 `TΩ·2` 大概不是 $\cong$ 的 (判断, 未编译). `Fold` 的目标地板 $\chi$ 取节点的整个 $\pi$, 而旧树取平凡的 `Fl`; 节点地板含第 0 层的 $K$ 时 (第二份 $X$ 里的节点, 地板来自第一份 $X$), 目标之下的闭包的界比旧树高, `ŝ≅` 要界 $\cong$, `Goodᴺ-tr` 用不上. 我相信 $\psi_0(\Omega_{\Omega\cdot2})$ 的证书存在 (那个 $K$ 被 $X$ 支配), 但那要新的闭包定理.
> - 任务 3: 反驳, 见上.
> - 任务 4: 全部反驳, 见上.
> - 任务 5: 未到. `F θ` 没有证书的前提 (它的 `WF` 也没有写), 而它用同一个 `ι (db η)`, 判断会撞同一处.
> - 任务 6: 闭包定理不存在. 否定里对 $m$ 的归纳只是把 $\Omega\cdot m+1$ 连到 $\Omega\cdot2+1$, 不进任何定义. 新的: 上面的反例, `rev`, 掩码, `_∼ᶜ_`. 继承的: 互模拟的行来自 [UniformNF5Base](UniformNF5Base.lagda.md).
>
> **第二个设计, 判断, 未编译: 只收紧目标地板不够.** 把 `Fold` 的 $\chi$ 从 $\pi$ 换成目标路径自己的地板, 上面的反例不受影响, 因为第 3 步读的是 `ι (db τ)` 的地板, 不是 $\chi$. 把路径改成穿过 $a+1$ 而不是 $\tau$ 也不够: 只要第 3 步的闭包还经过 `ι (db τ)`, 界就是 $\tau$. 第 3 步的闭包在输入 $z$ 里, $z$ 的层号是 $\Omega+a$, 而 `ι` 的结构递归把外层的 $\tau$ 带了进去. 所以两个设计败在同一点, 按任务的规定停在这里.
>
> **往后的方向 (判断, 未编译).** 值层早就遇到过同一件事: [Uniform3Base](Uniform3Base.lagda.md) 的修正是 `up` 经过时地板换成目标层的紧地板. 树层缺这个构造: 嵌入不能是把外层分支带下去的结构递归, 输入 $z\in O(L+a)$ 进第 $h$ 层时地板应当只是 $a$. 这要求 (i) 路径 `at a : L+a < L·Ω`, 比较看 $a$ 而不看穿过的分支, `<-dec` 要 $g$ 严格单调; (ii) 一个保留层号的懒嵌入 `oup r x`, 嵌入的复合化成路径的复合, 否则 $\dot\Omega_{L+a}$ 的第 0 个链点又把 $a$ 带进更低的输入; (iii) 支配的义务变成 "$a\prec\tau$ 且 $t\sqsupseteq\dot\Omega_{L+a}$ 推出 $a\prec$ 层号", 与 [UniformNF5Omega](UniformNF5Omega.lagda.md) 的 `Brᵀ` 同形, 只用单步严格增长. (i), (ii) 要改树, `lcl h g` 的 $g$ 不能再是黑箱.
>
> **有限测试 (验收节, `refl`).** `c-low`: $\psi_0(W+\psi_\Omega(\Omega_{\Omega+1}))<\psi_0(W+\Omega_{\Omega+1})$. `c-fs`: 目标 $\Omega$ 之下 $W$ 的基本列第 0 元低于 $\tau$.
>
> **审计 (`depslice.py`, 语法级).** `LvCertNeg:noCert₂`, `LvCertNeg:noΩ·`, `LvCertNeg:noΩ·ω`, `LvCertRel:irr`, `LvCertWorld:worldℕ` 到达的记号定义都是 0; 正对照 `LvCertAccept:noLab`, `LvCertAccept:c-low` 大于 0. 模块层面的导入不干净: `UniformLvTree` 经 `Uniform3Base` 的导入链含 `OCF.Align.EBO`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvCert where

open import OCF.Align.LvCertRel using (irr; clashL; clashE; module Rel; _∼ᶜ_)
open import OCF.Align.LvCertNeg using (noCert₂; noLv₊; noΩ·; noΩ·ω; module Top₀; Bd-in)
open import OCF.Align.LvCertWorld using (Worlds; worldℕ; module Core)
```
