# K2′ 第一阶段续做：irr 检验与 Ω₁·ω 下界，完整 ψ 仍未交

**主任务未完成。** 对纲领与目标的意义是：原块上已能递归生成任意有限
深度的 lc 0 嵌套及其折叠闭项，再交规范 Ω₁·ω 输入的合法正输出和值下界；
并把上轮的跨证书问题缩成了可复核的运输陈述。尚未在全部 Only0 Source
上构造完整 ψ，也没有否定该目标、乙线或树自足的可能性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2c where

import OCF.Align.YiK2cIrr
import OCF.Align.YiK2cFamily
```

## 作者两个建议的检验结果

| 检验 | 编译结果及范围 |
|---|---|
| 用 Legal.irr 运输子调用 | `branch-tree-irr` 给底层树相等；`transported-source`、`transported-call` 证明**沿该等式运输** Carry／Legal／Only0 后，任意子算子调用相等 |
| 实际 branch-source 是否就是运输后的 Source | 不能直接这样加强。`parent-source` 是完全合法、满足 Carry／Only0 的闭源；同一坐标的两个原守卫给底层树相同的两份实际分支 Source，但 `actual-sources-differ` 编译否定它们相等 |
| irr 加合法正输出能否推出任意算子的守卫不依赖性 | `sensitive-B`、`sensitive-positive` 实填合法正输出，`sensitive-not-irr` 给反例。这个算子读取证书，不满足 ψ 四行；本否定不涉及满足四行的特定 ψ |
| ψ 只读字面的树时 | `TreeOnly.certificate-coherence`、`lim-function-coherence` 均为 refl，`branch-call-irr` 用原 irr 给子输出相等，完全不需要函数外延。**但没有构造满足四行的 run : LF → Raw 0** |

反例的精确差别是子树 Legal 的第一条 CP 证据用了不同的极限分支号，
父结点分支树恒定，原 irr 为 refl。反例没有判定链点是否相等，也没有
运行高层比较。它否定的是“一律先把实际 Source 证明相等再用 cong”的
充分前提；不能据此说正确 ψ 的两份输出不同。

`lim-equality-reflects` 是 Raw.lim 的构造子反演：两棵极限树字面相等，
其整个分支函数就相等。`lim-function-equality-required` 从冻结的完整
目标记录推出跨证书的这项函数相等。它是必要接口推论，不是完整记录
的可满足性结果；本轮没有证明其结论不可得，也没有证明必须使用函数外延。

**判断：** irr 对底层 LF 的相等与运输已经足够；仍缺特定完整递归 ψ
对实际投影证书的不依赖性。只读树的办法能定义性消除此问题，然而直接
对所有裸 LF 的 lc 行执行原守卫 gt 程序还要求非法下界也能启动，旧
YiK2Stop.no-coordinate 已排除该加强。那个坏源在 Carry 域外，
不排除 Source0 域上的其他只读树办法。

## (a) 本轮交出的闭族与保持

[Family](YiK2cFamily.lagda.md) 采用上轮的 Only0，没有缩小完整任务的定义域。
其中定义规范有限和 `sum n = Ω₁·(n+1)` 与 `limit = lim sum`。

| 定理／构造 | 精确范围 |
|---|---|
| `sum-only`、`sum-carry`、`sum-legal`、`sum-source` | 全部有限 n 的原块 Source0，全部原守卫分支递归实填，不只是有限样本 |
| `Append` | 对任意合法正 seed，沿原 Raw 0 尾部递归出子输出，使用原加法生成 PointB 链；无 Grow 假设 |
| `Append.Chain.next`、`chain-grow`、`Append.additive` | 返回的下一点带原 guard 与 LglB；相邻点原 Dn，更新确为坐标加子输出 |
| `fold`、`fold-step`、`fold-start` | 全 n 的合法正折叠闭族；相邻输出 Cp，初项与**该输入自身的** start0-B 字面相同 |
| `second-is-previous-input`、`second-is-previous-output` | n=1 的输入和 Raw 输出分别与上轮 Ω₁+Ω₁ 闭例字面相等，未换掉已交闭项来攀爬 |
| `limit-source`、`closed-B`、`closed-legal`、`closed-positive`、`closed-row` | 规范 Ω₁·ω 的闭 Source0 及逐项极限折叠输出，读回合法且正 |

Append 的所有前提都有实例：`fold n` 对全 n 递归提供 seed 的合法性、
正性；其内部 `out`、`mono` 来自上轮的任意种子 tail 保持，而非临时假设
某条未知完整 ψ 的分支已经单调。

## (b) 比 Ω₁+Ω₁ 更高的输入上的值下界

[Value](YiK2cValue.lagda.md) 明标第 4 层。`omega-lower` 是无条件定理：

```text
Value.ψ⁰ (lim n (Ω₁·(n+1))) ≼ read (raw closed)
```

证明经过 `Bound.append-lower`：给定第 1 层前缀 X 的结构自模拟 `X ≅ X`、
合法正 seed 及既有 `ψ⁰ X ≼ read seed`，给下一次加 Ω₁ 的下界。
全 n 的 `reference-self`、`finite-lower` 逐步实填这两个值侧前提，
初项用上轮规范 Ω₁ 的值定理；
最后用极限得到 `omega-lower`。条件前提已由闭族全数实填，不是假设待证
站的强度。一般高层 ψ 对值单调没有被使用或声称。

`above-previous` 给 `suc (Ω₁+Ω₁) ≼ omega-reference`；
`not-below-previous` 排除反向。它使用对整个第 1 层的 `irr₁`，即不存在
`suc x ≼ x`。因此新输入确实高于上轮输入。
没有证输出的反向值界，没有基本列或 FGH 相同的结论，也不把它另标为
某个更高 ψ₀(Ω_x) 站的精确验收。

## 未交部分、止损与档位

- **编译定理：** 上述 irr 运输、充分前提的闭反例、只读树的局部一致性、全有限嵌套闭族、Ω₁·ω 合法正闭输出及值下界。
- **有限测试：** 无。
- **判断／未完成：** 全 Only0 域的 ψ、四行同时实现、OutputB／output-legal／positive 与片段内全 bounded-position 仍未交。

完整目标仍是上轮冻结的 `YiK2bBase.FoldRows0`，本轮没有给实例，
没有用一个新增的“分支已保持”输入条件缩域后冒称填完。
跨实际证书的一致性尚未证明；没有编译否定指出所求四行或其保持中
哪一行不成立。因此**没有触发行失败止损，没有消耗写法更换，也不把
实际 Source 不相等的反例冒充完整 ψ 的否定**。本轮返回的是部分成果，
没有将连续受阻写成路线已关闭。

## 翻译账

| 部分 | 来源与边界 |
|---|---|
| ψ 四行与输出形状 | 仍参考 JiaExactFold 模板；本轮没有导入该模块或宣布模板由树侧唯一逼出，也没有填完完整 ψ |
| 加法链 | 仍为 RR4／作者 D10 的树侧候选；只复用原右递归加法及第一位置运输，不改链更新写法 |
| 新闭族 | 使用原 LF 加法反复加 Ω₁，极限沿自身的 CP；Append 对 seed 参数化，不按每一阶段增加专用保持前提 |
| irr 检验 | 只读原 Legal 字段与 Source 投影；mark／inspect 是反面对照，明确不作为最终 ψ |
| 证书与界 | guard 与 LglB 随 AddChain.next 产生，初项与原 start0-B 相同；没有链点判等、k>0 回灌或全分支高层比较 |
| 第 4 层义务 | YiK2cValue 对闭族与原 ψ⁰ 比较，只新增定理，不参与定义或合法性；一般 Only0 树的值关系仍未交 |
| 第 4 层逼出 | 无；未改原块、Carry、Legal、接口或 YiK2b* |

没有把无记号引用等同于树已自足，也没有安装包、提交或推送。

## 冷编与审计

2026-11-10，逐件删除自身 .agdai 后冷编，依赖用缓存。每次单进程
`+RTS -M6G -RTS`，不使用 ignore-interfaces，退出码不经过管道。

| 模块 | 堆上限 | 退出码 | 有目标 Checking |
|---|---|---|---|
| YiK2cIrr | 6G | 0 | 是 |
| YiK2cFamily | 6G | 0 | 是 |
| YiK2cValue | 6G | 0 | 是 |
| YiK2c | 6G | 0 | 是 |

逐一代入四件文件的配方，库文件含 stdlib 2.4 与 cubical 0.9：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiK2c.lagda.md +RTS -M6G -RTS
```

Irr／Family／入口的源码本地闭包为 24／25／27，禁用表命中和白名单外均为 0。
`importclosure.py --only` 的全部参数为 OCF.Align.LevelFix、OCF.Align.Yi、
OCF.Align.RR4CoordRoot、OCF.Align.RR4RegOmega2、OCF.BTBO、OCF.Free.Level。
Value 是明标的第 4 层验收，源码本地闭包 57，不声称其导入闭包干净。
四件编译器 dependency-graph 的本地集合分别与源码闭包完全相同。

成功 HTML 的定义切片（到达块数／记号模块／记号词）：
transported-call 45／0／0，actual-originals-differ 70／0／0，
branch-call-irr 51／0／0，lim-function-coherence 46／0／0，
sum-carry 61／0／0，closed-legal 120／0／0，append-lower 204／0／0，
omega-lower 265／0／0，irr₁ 31／0／0。
正对照 Value.ts-vlab 为 563／92／65，脚本能发现记号依赖。
切片是语法近似，不把验收叶的零切片当作其整个导入闭包无记号。

四件均 safe／without-K，无公设、洞、停机／正性绕过、信任相等、函数外延；
无本机绝对路径或尾随空白。YiK2b* 四件及 YiCarry／YiCarryBounds 的字节摘要
与开工前相同；没有删除或强制重编它们的接口。本轮只新建四件 YiK2c*，
没有修改既有数学文件、README 或 LOG，没有提交或推送。
