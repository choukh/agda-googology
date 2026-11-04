# 树侧判据与盲测 (判决: PARTIAL)

> 底座 [TreeJudgeBase](TreeJudgeBase.lagda.md) (判据的定义与定理), [TreeJudgeObs](TreeJudgeObs.lagda.md), [TreeJudgeRead](TreeJudgeRead.lagda.md) (有限测试的工具). 使用 [TreeJudgeRd](TreeJudgeRd.lagda.md), [TreeJudgeRdF](TreeJudgeRdF.lagda.md) (判据选出的读法). 检验旧树 (不干净) [TreeJudgeNeg](TreeJudgeNeg.lagda.md), [TreeJudgeCheck](TreeJudgeCheck.lagda.md), [TreeJudgeCheckBad](TreeJudgeCheckBad.lagda.md), [TreeJudgeCheckOld](TreeJudgeCheckOld.lagda.md), [TreeJudgeCheckVer](TreeJudgeCheckVer.lagda.md), [TreeJudgeNoTrim](TreeJudgeNoTrim.lagda.md) (机械生成). 盲测 [TreeJudgeBlind](TreeJudgeBlind.lagda.md), [TreeJudgeBlind2](TreeJudgeBlind2.lagda.md), [TreeJudgeBlindResult](TreeJudgeBlindResult.lagda.md), [TreeJudgeAccept](TreeJudgeAccept.lagda.md) (读记号). 候选 `Rs` 的检验 [TreeJudgeRs](TreeJudgeRs.lagda.md). 接 [GuardTight](GuardTight.lagda.md), [LvCertNeg](LvCertNeg.lagda.md), [OCFSpec](OCFSpec.lagda.md), [VerdictSpec](VerdictSpec.lagda.md), [InaccModulusBase](InaccModulusBase.lagda.md).
>
> **判决: PARTIAL. 界这一半有了一个只用树的语言的判据, 它分开了所有测过的对错读法, 并且指出了一个之前没写的定义 (`Tc-F1`). 但它的拒绝与接受大多只是有限测试, 且它不管值: 值这一半我只写出了折叠方程本身的关系形式, 这不是新判据. "判断定义是否正确" 只做到 "判断界的合法性"; "写出下一步" 只做到读法, 折叠是继承的. 不是 FAILS: 没有接受错的读法, 也没有拒绝对的树 (取样之内). 不是 HOLDS.**
>
> **判据.** 一棵第 0 层的树 $T$ (`Z`), 四条, 都不读记号, 不看目标:
>
> | 条款 | 说什么 | 新吗 | 档 |
> |---|---|---|---|
> | `Goodᴺ` | 闭包的链存在且单调; 含 `head-law`: 界 $\sqsubseteq\mathrm{lv}$(头) | 旧 | 判定不了, 只能证 |
> | **`HF`** | **任意两个闭包, 头相同, 界相同** | **新** | 不可判定; 用法是取样 (`run`) |
> | `Reg⁰` | $\omega$-极限节点上 $h\,n$ 在 $h(n+1)$ 的 1-走步上 | 旧 (`Reg`) | 取样, 力量弱 |
> | `Climb`, `Vis` | 上升的链爬升; 字面路径上穿透 | **不新: 折叠方程的关系形式** | 对这些树可证 |
>
> **`HF` 的理由, 编译过的定理, 无条件:**
>
> - **`ghost` (对一切 `Z`):** 闭包 $X$ 的每个分支 $\tau$ 的第一路径上有闭包, 界 $\ge\tau+1$, 头在 $X$ 自己的头的第一路径上, 则 $X$ 没有 `Goodᴺ`. 这是 `noW` 的抽象. **它给了 `Tc` "最小" 一个不看目标的理由:** 把头不读的分支值读进界, 窗口就空了.
> - **`force-≃`, `rebound`:** 只差界的两棵树, 都有证书, 值 $\cong$. **界不进值.** 所以 "这里 2, 塔 1" 单独不是值的错误.
> - **`toy-ghost`, `toy-fine`:** `ghost` 不是空的. 两棵树只差内层的界 ($\tau+1$ 对 1): 前者没有证书, 后者有. 这是 `noW` 去掉折叠后的全部内容.
> - **`hf-indep`:** 有 `Goodᴺ` 而违反 `HF` 的树. `HF` 不是合法性, 也不是值的性质. 它是比合法性更严的设计约束, **根据只有下面的表**.
> - **`hf-blind`:** 没有闭包的树都过 `HF`. 它管不了值.
>
> **这不是 `Lab` 换说法, 内部也不读记号:** 定义的导入闭包干净, 陈述里只有 `Z`, `Sub`, `≅ᶻ`, `≅ᴵ`. **但它不是树逼出来的:** `HF` 受 `tail-free` 启发, `tail-free` 来自 `ScafLadderTop`, 那是看记号定的. 结论不依赖记号, 来路如实写.
>
> **拒绝.**
>
> | 树 | 定理 | 有限测试 | 哪一条 |
> |---|---|---|---|
> | `UniformLvTree` 的 `T₀` | `reject-uniformLv` (`noCert₂`) | `hf-u` | `Goodᴺ`; `HF` 独立地测到 |
> | `ver` 的树 | `reject-ver`: 这一对上 (层号直接写出, `L₁-is`, `L₂-is` 说就是它算出的) | `d★-pen` 对照 | `Vis`. `Reg⁰` 取样**拒绝不了** (`reg-ver`, `reg-D★`: 命中 96, 超预算 22, 与正确的树相同) |
> | `static-rejected` | `reject-static`: 不存在任何链 | | `Climb` |
> | `wrong-fold` | `reject-wrong-fold`: 对任意判决 | | `Reg⁰`: 常值的极限 |
> | 没有 `trim` | **无定理** | `hf-n2`, `hf-n21`: 在 $\Omega\cdot2$. $\Omega+1$ 上不报 (`hf-n11`) | `HF` |
> | `Tc-id` | **无定理** | `hf-t2id`, `hf-t21id`, `pH2` ($\psi_1(\Omega)+1$), `hf-L5s-id` | `HF` |
>
> **接受.**
>
> | 树 | 定理 | 有限测试 |
> |---|---|---|
> | `OCF/Free/Tree` 的 `TΩ·2` | `accept-free` (`certᵀ`) | `hf-free`, `reg-free` |
> | `GuardTight` 的 `T₀` | 只在 $\Omega_1$: `accept-tight-Ω₁` (`Good-Ω₁`) | `hf-t1`..`hf-tf0Ω`, `reg-t21`, `reg-tf0s` |
> | `ScafLadderQ` 的 `Tᵠ` | 无 (证书走标签, 不算) | `hf-q1`, `hf-q2`, `hf-q21`, `hf-qω`; $\Omega\cdot3$ 没跑完, 无结果 |
>
> 真实的折叠过 `Climb` (`real-climb`) 是定义展开, 不算证据.
>
> **这张表里什么是真正的判据, 什么只是旧结果的换名.** 拒绝的四条定理: `reject-uniformLv` 就是 `noCert₂`; `reject-wrong-fold` 用的 `Reg` 是旧的, 这个观察 (常值极限) 是新的但简单; `reject-static`, `reject-ver` 用的是折叠方程. **`HF` 自己只有有限测试.** 对对错错的读法它都分对了, 而且取样是我选的: 分母小的地方力量弱 ($\psi_1(2)$ 深 9 只有 1 个闭包).
>
> **第 2 步, 盲测.** 预测写在 `TreeJudgeBlind`, `TreeJudgeBlind2`, 用 `shasum` 封存后才计值和比较 (`Blind` `52ad223b…`, `Blind2` `b21e05d4…`). 没有改过.
>
> | 目标 | 新定义 | 预测 | 对 | 与记号比较 (`dfZ`) |
> |---|---|---|---|---|
> | $\psi_0(\Omega_{\psi_1(1)+1})$ | 无 (`Tc-a`) | 11 | 11 | 深 14 宽 2 一致 |
> | $\psi_0(\Omega_{\psi_1(1)\cdot2})$ | `Tc-m` (`RdPre`, 前缀的紧读法) | 16 | 15 | 深 18 宽 2, 深 26 宽 1, 深 10 宽 3 一致 |
> | $\psi_0(\Omega_{\psi_1(2)})$ | `Tc-ψ2` | 8 | 8 | 深 18 宽 2, 深 10 宽 3 一致 |
> | $\psi_0(\Omega_{\psi_1(1)\cdot2+1})$ | 同上 | 7 | 7 | 深 18 宽 2, 深 10 宽 3 一致 |
> | Bachmann 取样 | | 2 | 2 | |
> | $\psi_0(\Omega_{\psi_1(\Omega)})$, $+1$ | **`Tc-F1`, 不要 `Str`/`Cont`** | 22 | 22 | $+1$: 深 18 宽 2, 深 26 宽 1, 深 12 宽 3 一致 |
>
> **基本列前几项 (预测, 都对).** 记 $a=\psi_1(1)$, $T(L)=\psi_0(\Omega_L)$. $T(a+1)[0]=T(a)$; $[1]$ 是极限, $[1][0][1]=T(a)$, $[1][1]$ 是闭包, 界 1. $T(a+a)[n]=T(a+\Omega\cdot n)$; $[1]$ 是闭包, 界 1, 头与第一支 $T(a+1)$, 分支 $\eta$ 是 $T(a+\eta)$. $T(\psi_1(2))$: $[0]$ 极限, $[1]=T(a)$, $[2]=T(a+a)$, $[3][0]=T(a+a)$. $T(\psi_1(\Omega))$: 闭包, 界 1, 头 $T(a)$, 分支 $1,2$ 是 $T(a)$, $T(\psi_1(2))$. 相等都是深 7 宽 2 的指纹.
>
> **猜错的一条: `pB14`.** 我预测恒等读法在 $\psi_1(1)\cdot2$ 上深 9 违反 `HF`, 没有. **用法的问题, 不是判据的问题:** 那个取样只有 26 个闭包, 深 11 就违反了 (`post-TBid`, 事后探查, 不算预测). 第二次的深度是看了这次的结果才定的.
>
> **最有分量的预测是界:** `pY1`..`pY6`, `Tc-F1` 在 $\psi_1(\Omega)$ 上界恒为 1, 恒等读法界是 $\tau$ ($\tau=2,3,5$). 这是 `c-bra*` 在第 5 站这一半的取样. 其余结构预测大多是折叠的行的展开, **猜对不算多大的证据.**
>
> **这次盲测有多盲.**
>
> - **没看:** `EBO` 在这些目标上的规则, `fsT`, `fsn` 的计算; `ScafLadder*` 对这些目标的处理 (我只看了 `ScafLadderQ` 的文件头与 `Tᵠ` 的定义行, 调用 `Tᵠ` 作接受的对照).
> - **看过:** [GuardTight](GuardTight.lagda.md) 全文头与 [GuardTightAccept](GuardTightAccept.lagda.md) 全文, 所以知道 $\psi_0(\Omega_{\psi_1(1)+1})$ 的种类测试已通过, 知道 $\psi_1(\Omega)$ 的 `Tc-id` 种类测试已通过, 也知道 $\Omega\cdot2$, $\psi_1(1)+\Omega$ 上紧读法的界是 1. 所以 `pY1`..`pY3` 的先验就高. 判据是在这些树上调出来的: `HF` 在 `t2`, `t3`, `tf1` 上跑过才定.
> - **继承自记号的设计:** 折叠 `T₀` 整个是继承的, 按 [GuardTight](GuardTight.lagda.md) 的说明它的形状 ($\Omega\cdot m$ 的落地, `omk`, "地板必须真实出现") 来自 `ScafLadder`. 目标的选择按记号的名字 ($\psi_1(1)\cdot2$, $\psi_1(2)$). 层号由 `ψ¹` 读回, `ψ¹` 与 `ψ⁰` 同形, 来自 BTBO. `HF` 的来路见上. **真正由判据决定的只有读法.**
> - **比较器的限度:** `dfZ` 只比种类, 闭包只走第一支, 不看界. 所以记号这边其实看不到 `HF` 管的东西. 由 `force-≃`, 这是必然的: 界不进值, 记号比的是值.
> - **`GuardRead*`:** 别的智能体同时写的 (磁盘上 18:26 起有), 我到 18:51 才读到它的名字, 两次预测的封存都在这之前 (18:43, 约 18:50). `Tc-F1` 是独立写的, 事后发现被 `Tc-F` 覆盖 (`Tc-F` 对一切 $\theta$, 我的只到 $\theta=1$), 两者指纹相同 (`same-F1`).
>
> **候选 `Rs` ([TreeJudgeRs](TreeJudgeRs.lagda.md)).** 不能作这份列表的判官: 错不在层号上, 错的树的层号与输入都是 `Rs` (`rs-static`, `rs-Ω2`). 经典地切口没有限制 (`sp-total`, 条件定理, 第 0 层); 外延的限制只有 `Cont` (`rs-cont`). 它是**生成器**: `Tc-of` 给读法. 判断: 正确的搭配是 `Rs` 写读法, `HF` 在树上查. `hf-L5s`, `hf-L5s-id` 是这个搭配的第一次测试 (事后, 不是盲测).
>
> **判断.** `HF` 是目标判据 "有树侧的合法性标准" 上的进展, 不是 "树自足". 它回答 "这个读法错了吗", 回答 "下一步的读法该是什么样", 不回答 "这棵树的值对吗". 对值我没有树侧判据: 静态替身的树自己没有错, 错的是它与输入的关系, 所以任何只看输出树的谓词都拒绝不了它, 要的是输入与输出的关系, 而那就是折叠方程或 `IsPsi` (判断, 这一句没有编译).
>
> **第一个障碍.**
>
> 1. `HF` 没有一般定理: "紧读法的 `T₀` 满足 `HF`" 没有证. `HF` 的量词过全部分支, 而 `free-bound` ([GuardReadBound](GuardReadBound.lagda.md)) 说的是同一个目标, 不是同一个头. 要的桥是 "头相同推出目标相同", 这对折叠的输出未必成立 (判断).
> 2. `ghost` 没有实例化到 `Tc-id` 与没有 `trim` 的树: 要 $\tau$ 对一切 `Ordᴵ` 的走树证明 (`LvCertNeg` 的 §5 到 §7 那种, 约 300 行), 没有写. 所以它们的 "没有证书" 还是判断.
> 3. 证书没有动: 这里没有新的 `Goodᴺ`. `Goodᴺ` 也不能取样, 因为 $\mathrm{lv}$(头) 的 `lim` 要单调的证明.
>
> **审计.** `importclosure.py`: `TreeJudgeBase`, `Obs`, `Read`, `Rd`, `RdF`, `Blind`, `Blind2`, `BlindResult`, `NoTrim`, `Rs` 闭包干净 (编译器保证). `TreeJudgeNeg`, `Check`, `CheckBad`, `CheckOld`, `CheckVer`, `Accept` 不干净, 文件头写明. `depslice.py` (语法级): `HF`, `ghost`, `force-≃`, `Tc-F1`, `Tc-ψ2`, `reject-static`, `reject-ver`, `reject-wrong-fold`, `hf-blind` 到达的记号定义都是 0; 正对照 `TreeJudgeAccept:n-B` 48, `TreeJudgeNeg:d★-pen` 8. `Tc-ψ2` 的 "token hit 1" 是我的层号名字 `Lab` ($a+a$ 的层号, 与标签无关) 撞了脚本的禁用词; 文件已封存, 没有改名. 全文 `--safe --without-K` (加 `--lossy-unification`, `Obs` 除外), 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`. 模块参数: `Rows` 的载体是抽象的, 不是假设; `Wrong` 的 `S` 是任意判决; `Pre.At` 的 `ea`, `tca` 是实例给的; `Total` 的 `Tot` **是条件**.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudge where

open import OCF.Align.TreeJudgeBase using (Sub; FP; head-law; Ghost; ghost; _≃ᶻ_; force-≃; rebound; HF; hf-indep; Tr; Reg⁰; lim-const; module Rows; Vis)
open import OCF.Align.TreeJudgeObs using (Obs; run; nclo; reg)
open import OCF.Align.TreeJudgeRd using (Wr; module RdPre; module Pre)
open import OCF.Align.TreeJudgeRdF using (Tc-F1; Tc-ψ; vA₁)
open import OCF.Align.TreeJudgeBlind using (TA; TB; TC; TD)
open import OCF.Align.TreeJudgeBlind2 using (TE; TE⁺; Yt; Yi)
```
