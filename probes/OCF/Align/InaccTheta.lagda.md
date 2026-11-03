# 第 5 站的证书: 对一切 $\theta$ 的好树定理 (判决: LEVEL SIDE OK, 相对于判决 `S` 的正确性)

> 接 [InaccFloor](InaccFloor.lagda.md). 底座 [InaccThetaRel](InaccThetaRel.lagda.md), [InaccThetaEq](InaccThetaEq.lagda.md), [InaccThetaObs](InaccThetaObs.lagda.md), [InaccThetaGood](InaccThetaGood.lagda.md), [InaccThetaClose](InaccThetaClose.lagda.md), [InaccThetaFin](InaccThetaFin.lagda.md), [InaccThetaMono](InaccThetaMono.lagda.md), [InaccThetaStation](InaccThetaStation.lagda.md), [InaccThetaSpine](InaccThetaSpine.lagda.md), [InaccThetaNeg](InaccThetaNeg.lagda.md), [InaccThetaTarget](InaccThetaTarget.lagda.md). 全部不含记号, 导入链里没有 `OCF.Align.EBO`, 也没有验收节. 没有新的验收: 这里的树就是 [InaccFloorTree](InaccFloorTree.lagda.md) 的 `PF.F`, `PF.T₅`, 它们的验收在 [InaccFloorAccept](InaccFloorAccept.lagda.md).
>
> **判决: LEVEL SIDE OK. 证据是遗传的好树 `Good` 加判决的语义正确性 `LvG`. 还差的只有后者, 它正是 [InaccFloor](InaccFloor.lagda.md) 的定义一侧的障碍, 证书这边没有新的障碍.** 目标 $k\ge2$ 的闭包定理成立, 但取证书不成立 (PARTIAL, 见任务 4).
>
> **编译过的定理.**
>
> 1. **$\theta=3$, 以及一切自然数 (`Cert-nᴼ`, `Cert₃ᴼ`).** `WFᴬ (toLv (F (natL n)))` 在**原来的** `Rel (Aℓ ℓ)` 里成立, 对任何 `S`, 任何 $\ell\ni1$. `Aℓ` 一个字没改. [InaccFloorNeg](InaccFloorNeg.lagda.md) 的 `¬WF-L₂` 说的是输入的层号; 证书要的是输出的层号, 而 `F θ` 是第 1 层的树, 它的参数层全是 0. 证据放在输入的树上 (`Good`), 不放在可容许集上.
> 2. **对角的好树定理 (`Good-ψ`, `Cert`).** `Good` 是 [Uniform](Uniform.lagda.md) 的 `Good₊` 在 `Lv` 上的版本: 分支在**好输入**上好且单调; 第 0 层的好输入是 `Aℓ`, 第 $\ge1$ 层的好输入是好且自相似的树, 没有有向性. `Cert : ∀ θ → LvP θ → WFᴬ (toLv (F θ))`, 对 `Good` 的推导结构递归. 没有 `Acc`, 没有项文法. 第 0 层的有向性只在 `wf` 里用一次 (`A-dir`).
> 3. **"好"的层号 `LvP θ`.** 三部分, 都是树语言: `GLv` (极限脊上 $\Omega$ 单调, `limᴼ` 的分支在好输入上好且单调), `LvR` (`limᴼ` 的分支尊重相似), `LvG` (每个 $\Omega$ 节点要的链的模式 `OK`). 封闭性: `lvp-lim`, `lvp-limᴼ` ($\lim$, `limᴼ 0`), `lvp` (第 0, 1 层的好树的 `toLv`, 所以第 1 层的链点也算), `lvpΩΩ` ($\Omega_\Omega$ 的层号), `lvp-F` (`F θ` 自身, 所以嵌套下标 $\psi_1(\Omega_{\psi_1(\Omega_\Omega)})$), `Cert-Tw` (任意深的嵌套). `Ω-mono` 把层号的 `⊑ᴬ` 变成 $\Omega$ 的观测单调. 这些闭包都以那一层的 `LvG` 为前提; `lvp`, `lvpΩΩ`, `lvp-F` 还要叶子取 `Aℓ` (`StA`, `Feed`).
> 4. **第 5 站 (`Station5`, `Lv₅≡`).** 第 5 站的层号就是 `toLv (F LΩ)` (`refl`). `Station5 : HE → WFᴬ Lv₅`, `HE` 说 `S` 在 `Aℓ` 里的每个层号的 $\Omega$ 节点上正确. `cmp₅` 是它的比较.
> 5. **无条件的范围.** 模式 `fin` 对任何 `S` 都 `OK` (`okF`). 模式 `lt` 在 $\omega+m$ 的脊上不问 `S` (`okLt`). 所以 `HE` 在世界 $\omega\cdot2+1$ 里是定理: `Station5ω2`, 以及原来的 `Rel` 里的 `Station5ᴼ`, `cmp₅ᴼ`, 对任何 `S`. 这个世界的第 5 站的字面比较是定理.
>
> **编译过的否定.**
>
> - `no-uniform : (∀ a → LvT (E a)) → WLPO`. **一个拿原始层号对的 `S` 不能对一切 `Ordᴵ` 层号正确.** 没有用函数外延性. 反例族的层号相同, 但 "全假" 与 "第 $n$ 位真" 给不同的步进证据, 所以与 `<ᴵ-dec` 不矛盾: 带证据时比较是定理, 证据不能一致地给出. 所以 `HE` 不能对全部世界一次性兑现.
> - `frontier`, `¬frontier`: 边界是精确的. $\omega\cdot2+1$ 作节点层就要 `S` 在 $(\omega,\omega+1)$ 上正确, `S = rise` 过不去.
> - `no-Ωᵀ`: 叶子用原来的 `≈` (`B₀ = ⊤`) 时, $\Omega_\Omega$ 的层号作输入就要全部原始分支上正确, 推出 WLPO. 这是嵌套下标要把叶子换成 `≈ᴮ` 的理由 (`StA`). 第 5 站自己不碰它.
> - `no-Ω₂`: 下标含参数层 $1$ 的 `limᴼ` (如 $\Omega_{\Omega_2}$, 第 $\ge2$ 层链点的 `toLv`) 时, `LvG` 要全部原始分支上正确, 同样推出 WLPO. **这个设计的 "好层号" 的 `limᴼ` 只能是参数层 0.** 这是下面的第一个具体障碍.
> - `¬WF-ψ₂`: 目标 2 的输出在 `Aℓ` 下没有证书.
>
> **第一个具体障碍, 精确位置.**
>
> - **第 5 站的一般世界.** `HE` 在世界 $>\omega\cdot2+1$ 里问 `S`. 一个原始的 `S` 能否对**单个固定的** $\ell$ 正确, 没有解决; 对全部 $\ell$ 一致地正确是 WLPO. 这与证书无关, 是 `PF` 的 `sib` 丢了路径与证据 ([InaccFloor](InaccFloor.lagda.md) 的定义一侧). 看来定义要改: 让层号的分支带证据, 判决读证据 (判断, 未编译).
> - **参数层 $\ge1$ 的 `limᴼ` 作下标** (`no-Ω₂`). 根源: `Eq` 与 `LvG` 对参数层 $\ge1$ 的分支全称. 限制到好输入要 `Eq` 依赖 `Good`, 而 `Good` 经观测前序依赖 `Eq`, 是循环的 (判断, 没有试编译). 我认为要分阶段: 第 $k$ 阶段的好输入来自第 $k-1$ 阶段. 第 5 站用不到它.
>
> **任务 4: 目标的推广.** 闭包不分阶段: `Good-ψ` 对任何 `OK` 的目标 (`Good-ψₖ`: 目标 $k$ 无条件; 目标是字面层号 $L$ 时就是 `ch` 的那一步). 取证书分阶段: `wf` 只管第 0, 1 层, 因为参数层 $\ge1$ 的节点要 `A` 在那一层非空且有向 (`¬WF-ψ₂`). **没有写第 2 层的地板, 下面是判断.** 第 $k$ 层的 `A` 取 "`toLv` 落在第 $k-1$ 层证书的字面前驱" 的树, 比较用上一层的 `<-decᴬ`; 观测的目标限制到 $\ge k$, 第 $<k$ 层就都穿透, `limᵢ-l₀`, `limᵢ-r₀` 的论证照搬. 还要一个 `toLv x ⊑ᴬ toLv y → x ⊑ᵒ y` 的引理 (第 $<k$ 层), 我估计它要 `Eq` 的传递性, 这里没有. 所以到目标 1 为止定理与阶段无关, 目标 $\ge2$ 的证书需要一个对 $k$ 递归的结构, 没有依据说它不会再要新东西.
>
> **树侧逼出的, 与读记号的.**
>
> - 树侧逼出: `CV` (由 `verdict` 的类型不要求真, 而 `clash` 要它); `Eq` 的跨层 (由 `≅ᴵ` 的步进); `DB` 与 `AdmB` (由 `add` 的路径要落在可容许处); `LvT` 与 `LvG` 分开 (由 `Ω` 节点只要自己那一条链; 第一版把它们合在一起, $\Omega_\Omega$ 上多要了一堆 `S` 的正确性); `Zp` (`limᵢ-l₀` 要 $0$ 在右边, 而 `add` 要保持它); `≈ᴮ` (`no-Ωᵀ`); "$\psi_0$ 不是观测" (`rise≠0`, 第 0 层没有 Bachmann 条件, 所以 `limᵢ-r₀` 成立).
> - 读记号的: 没有新读. 目标站点与层号的形状来自任务; [Uniform](Uniform.lagda.md) 的 `HS` 结构是树侧已有的定理. $\omega\cdot2+1$ 这个边界是对 `lit` 手算后编译确认的 (`frontier`), 没有看记号.
>
> **下一步该问谁.** 证书这边到目标 1 为止是定理, 不再是第 5 站的瓶颈. 下一步的选择在定义一侧: 让 `limᴼ` 的分支带证据, 还是接受 `Syn`. 这个选择应当交给作者.
>
> **审计 (`depslice.py`, 语法级).** `Cert₃ᴼ`, `Station5ᴼ`, `Station5`, `no-uniform` 到达的记号定义都是 0; 正对照 `InaccFloorAccept:ψ₀t` 是 43.
>
> 全文 `--safe --without-K` (只有 `InaccThetaRel`, `InaccThetaEq` 加 `--lossy-unification`), 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.InaccTheta where

open import OCF.Align.InaccThetaClose using (module Close)
open import OCF.Align.InaccThetaFin using (module Fin)
open import OCF.Align.InaccThetaMono using (module Mono)
open import OCF.Align.InaccThetaStation using (module St; module StA; module Wω)
open import OCF.Align.InaccThetaSpine using (module Sp; module NoRise; module OrigSp)
open import OCF.Align.InaccThetaNeg using (module Neg; module NegT)
open import OCF.Align.InaccThetaTarget using (module Tgt; module Orig)
```
