# 归纳-递归块: 从 EBO 往回推的决定性设计测试 (判决: BLOCKED)

> 底座 [LvIRBase](LvIRBase.lagda.md), [LvIRBlock](LvIRBlock.lagda.md) (块), [LvIRNeg](LvIRNeg.lagda.md) (否定), [LvIRReach](LvIRReach.lagda.md) (路径), [LvIRPos](LvIRPos.lagda.md) (检查器的实测). 验收 [LvIRAccept](LvIRAccept.lagda.md). 接 [EBOTop](EBOTop.lagda.md) 的第一个障碍与 [EBOTopIR](EBOTopIR.lagda.md) 的侦察.
>
> **判决: BLOCKED. 块的形状过了检查器, 闭包定理在块里, 没有 `ev`; 但它只走到 $x_1$. 这条路线到不了 $\psi_0(\Omega_{\Omega_2})$, 理由是编译过的: 那一站里字面地有目标 $\omega+1$, 分支是全部第 0 层的好输入 (`hard`), 而在这样的目标上, 任何读证据的判决只要好输入含反例族就是 WLPO (`no-read`, `no-verdict`). 好输入是内在谓词时含不含反例族是实质问题; 好输入要是一个有公共上界的族, 块里写不出来 (`P1`–`P3`, `P11`–`P13`). EBO 没有定义出来, `x₂` 在块里也没有定义.**
>
> **回答协调者的问题: 归纳-递归买到的不是 `limᴼ` 作低层, 也不是 `HS`.** 见下面 "归纳-递归买到了什么".
>
> **编译过的定理 (无条件).**
>
> 1. **块过了正性与停机, 闭包定理在块里 (`LvIRBlock`).** `Lv` 的分支在好输入上, `Good` 读折叠的输出 (节点带基点与步进, 极限带相邻步进), 折叠读 `Good`, 链的下一点的证据由 `cloT` 给, `cloT` 在同一个块里. 模块没有参数. `EBOTopIR` 的开放问题 "闭包定理进块过不过" 的回答是: **过**.
> 2. **头两项 (`hs-x₀`, `hs-x₁`).** 无条件, 没有 `S`, 没有假设. $x_0,x_1$ 的 `HS` 此前已知 (`EBOTopLink`); 新的只是它们由块里的闭包定理给出.
> 3. **这个块的范围 (`¬Good-L₂`).** 块只有目标 0, 节点层必须字面是 0. $\Omega_\Omega$ 在第 $y=2$ 枝上不 `Good`. 这是块的范围, 不是证明的缺口. 所以 $x_2$ 没有定义, 这是如实的边界.
> 4. **第 0 层的折叠 (`P₀-mono`, `P₀-HS`).** 对一切树, 不要 `HS` 前提的单调.
> 5. **`no-read`, `no-verdict`, `no-read-HS` (`LvIRNeg`).** 下面.
> 6. **路径 (`LvIRReach`, `refl`).** `reach-sucL₂`, `reach-node` 对一切 `S`; `reach-hard`, `hard`, `ask` 对 `S = ver`. 有限条路径, 每一步都是编译过的等式.
>
> **编译过的否定.**
>
> - `no-read : (G : O₀ → Set) → (∀ s → G (y s)) → (∀ a → G a → Dec (a ≺⁰ ω+1)) → WLPO`, 带正确性证据的 `no-verdict`, 以及分支形状的 `no-branch`, `no-branch-HS` (好输入是 $a+1$, 比前驱 $a$, 这正是 `ask`). 反例族 `y s` `HS`, 严格 (`y-strict`), 规整 (`y-walk`). **`G` 是任意的, 派发可以读证据.**
> - `¬Good-L₂`: 这个块上 $L_2$ 不好.
>
> **任务 2: 为什么 `no-uniform` 与 `bad-S` 不适用, 而 `no-read` 适用.** `no-uniform` 的前提是一个 `S : (j i : Lv) → Verdict j i`, 只看原始层号; 反例族层号相同, 证据不同. 块里的派发读证据, 不是 `S` 的函数, 所以这两条的前提都不成立. 但这条逃生口很窄: `no-read` 的派发函数的第二个参数就是证据, 反例族每一项都有证据, 所以读证据没有用. **`no-uniform` 是 "不读证据不行", `no-read` 是 "内在的证据也不行".** 只有 "好输入不含反例族" 才逃得掉.
>
> **第一个障碍, 精确位置.** $\psi_0(\Omega_{\Omega_2})$ 的第 $(1,0,0,2,0)$ 项是 $\psi_0(\Omega_{\Omega+1})$; 它的第 $(1,1,0,1,0,1,2,2,2)$ 项是 $\psi_0(\psi_\Omega(\Omega_{\omega+2}))$; 再 $(1,0,0,1)$ 是 $\psi_0(\psi_\Omega(\psi_{\omega+1}(\Omega_\Omega)))$ (`hard-tm`, 记号一侧的项, `refl`). 而 $\psi_{\omega+1}(\Omega_\Omega)$ 的分支是**全部** $v$ (`hard`), 第 $v$ 枝要比 $v$ 的前驱与 $\omega+1$ (`ask`). [EBOTop](EBOTop.lagda.md) 把这三件事 (好输入, 非自然数目标, 跨分支) 记在 $x_3$ 名下, 又把 $\psi_0(\Omega_{\Omega_2})$ 当作 "精确的第一步, 缺的是把 `no-Ω₂` 换掉". 这里的路径说这个第一步自己就要非自然数目标. `reach-W` 也在 $T(2)$ 之内 (`W-head`). 所以 "先做 $\psi_0(\Omega_{\Omega_2})$ 再做非自然数目标" 这个分步不成立: **$\psi_0(\Omega_{\Omega_2})$ 的 `HS` 已经要好输入是有公共上界的族.**
>
> **目标的状态 (任务 3).**
>
> | 目标 | 状态 |
> |---|---|
> | `HS` $x_0, x_1$ | 定理, 无条件 |
> | `HS` $x_2$ | 块里没有定义. 不是被否定: 目标 $\ge1$ 的闭包要单调性, 没有写 |
> | `HS` $\psi_0(\Omega_{\Omega_2})$ | **没有达到**. 内在的好输入上被 `no-read` 挡住 |
> | `HS` $x_3$, `Family`, `Stage`, 闭的 `EBOᵀ` | **没有达到** |
>
> **任务 3 里没有做, 如实.** 块里目标 $\ge1$ 的折叠没有写. 我判断它要单调性的全部机器 (观测或结构序, 约等于把 `InaccTheta*` 搬进块), 而且写了也越不过上面的障碍, 所以没有投入. 接口上还有一个不合: `Stage` 的 `ψ₀` 不带证据, 块里的折叠带, 所以块不是 `Stage` 的实例; 真要接要改接口 (判断).
>
> **归纳-递归买到了什么 (回答协调者).**
>
> | 东西 | 归纳-递归给吗 | 依据 |
> |---|---|---|
> | 闭包定理与定义同块 | **给.** 证据可以在定义里流动, 没有 `S`, 没有 `ev` | `LvIRBlock` |
> | 判决从证据读 | **形式上给**, 内在的好输入上是 WLPO | `no-read` |
> | $\psi_0(\ldots)$ 的 `HS` 超过 $x_1$ | **不给.** 还是要单调性, 而单调性的机器在块里更难写: 观测不能是数据类型 | `P4`, `P5` 对 `Fuel` |
> | `limᴼ` 作低层 | **不给.** 那是 `o≈` 的字面参数层问题, 与分支带不带证据无关 | `LevelK` 的 `¬both-low`; 块里没有 `≈`, 判断 |
> | 有公共上界的好输入族 | **不给.** 正性挡住提 `Lv` (`P1`–`P3`), 宇宙层次挡住节点谓词提 `Lv` (`P7`), 自界的写法一读证书就停机失败 (`P11`–`P13`) | `LvIRPos` |
>
> 所以 `LevelK` 的层号地板比归纳-递归更合适: 地板的定义只提层号, 循环在那里断开, 而且不要 `Lv` 进块. 块相对于它的唯一优势是没有 `S`; 但在 `LevelK` 走得到的范围里 `S` 本来也不被问.
>
> **任务 5: 壁垒逐字段.**
>
> | 块的字段 | `¬tri` | `noBT` | `dec-A→WLPO` | `no-Ω₂` |
> |---|---|---|---|---|
> | `Lv` 的 `limᴼ`, 分支在 `Σ (Ord k) (Good k)` | 块里没有全局比较 | 分支只在好输入上, `noBT` 的 `zigzag` 不 `HS`, 不进分支 | 成员资格是证据, 块不判定它 | `no-Ω₂` 要全部原始分支; 这里分支受限 |
> | `Good zero = HS` | | 比较没有写, 所以不碰. **一写就碰 `no-read`** | 不判定 `HS` | |
> | `GoodT`, `NodeG`, `ZN` | 只有目标 0, 节点层字面是 0, 从不比较 | 同左 | 同左 | 节点层 1 直接是 $\bot$ (`¬Good-L₂`), 所以走不到 `no-Ω₂` 的层号 |
> | `ψ₀`, `node`, `zn` | 上升不比较 | 同左 | 不读 `Good` 判定, 只取分量 | 同左 |
> | `clo*` | 结论是 `HS`, 只提第 0 层 | 同左 | 同左 | 同左 |
>
> 这张表是**块现在写的部分**; 它不碰壁垒, 是因为它没有比较. 一旦写目标 $\omega+1$ 的比较, 就撞 `no-read`, 这正是判决的内容. `no-read` 是 `dec-A→WLPO` 的同类, 不是壁垒定理本身的推论.
>
> **有限测试 (`LvIRAccept`).** `b0`, `b1`: 块的 $x_0,x_1$ 对 `EBOψ 0`, `EBOψ 1` 宽 3 深 6. 对照 `c0ctl`, `c1ctl`. 裸层号 `S = ver`: `e2`–`e4`, `hard-tm`, `W-tm`, `W-head`, `W-ok`, 对照 `hard-ctrl`, `W-ctrl`. **`hard-blind`: 这个比较器在这个深度内分不开 $\omega+1$ 与 $\omega+2$**, 所以 `hard-ok` 是弱证据. 没有发现偏离. $x_2,x_3,x_4$ 在块里没有定义, 块上没有它们的检查.
>
> **判断 (未编译).**
>
> - "好输入非得是有公共上界的族". 依据是 `no-read` 加 "比较只能经字面上界". 没有证 "任何不含反例族的内在谓词都不对".
> - "节点自带谓词 (`P7`) 只是把问题搬到链上". 我没有写这个设计. 它是这里唯一没有被编译结果挡住的方向, 但它要证 "下一点字面含目标", 对一般的目标我没有办法.
> - `P8` 的 `val → prf` 过了而 `P12` 没过, 差别我归因于比较读证书, 没有查清检查器内部的原因.
>
> **审计.** 除验收外, 导入链到不了记号 (`importclosure.py`). 全文 `--safe --without-K` (`LvIRBlock`, `LvIRReach`, `LvIRAccept` 加 `--lossy-unification`), 无公设、无洞、无停机或正性编译指示. `P1`–`P13` 是临时文件, `P13` 带两个假设只测形状, 都不进仓库.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvIR where

open import OCF.Align.LvIRBase using (P₀; P₀-mono; P₀-HS)
open import OCF.Align.LvIRBlock using (Lv; Good; GoodT; ψ₀; cloT; x₀; x₁; hs-x₀; hs-x₁; ¬Good-L₂)
open import OCF.Align.LvIRNeg using (y; y-HS; y-strict; y-walk; no-read; no-read-HS; no-verdict; no-branch; no-branch-HS)
open import OCF.Align.LvIRReach using (module AllS; module Ver; module Link)
open import OCF.Align.LvIRPos using (module Fuel; module SelfBound)
```
