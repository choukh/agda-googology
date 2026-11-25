# S3 第一轮：合法树层号与有界 CP 比较，派发位置覆盖仍缺

**档次：对一切合法层号的 Ω 闭包与有界第一位置比较；
另有一个排除“层号字段自动是第一位置”的编译反例。**
按作者选定先做层号基础，不写 ψ。S1 的结束决定已写入
[JiaRound5](JiaRound5.lagda.md)，新顺序为 S3（并入 S2）→ S5 → S4。
本轮不把局部位置比较称为完整派发，不交低层强度测试代替成品。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound1 where

import OCF.Align.YiLevelBase
import OCF.Align.YiLevelCompare
import OCF.Align.YiLevelView
import OCF.Align.YiLevelAudit
```

## 层号、合法性与 Ω

[YiLevelBase](YiLevelBase.lagda.md) 复用作者指定先例 LevelFixCore／LevelFixVal
中不含记号的 LF 树与 Legal。Level 同时存树与合法性；零、后继、极限、
Ω 结点的构造函数均同时给出结果证据，没有事后合法性检查器。
没有导入旧 LevelFixU、旧折叠或其 Un 条件。

Ω 沿原树结构递归；四个树投影方程均为 refl。其输出仍是 Level，
合法性对一切输入层号一次成立。塔、Λ 与 ΩΛ 在同一类型中合法；
这里的 Λ 是合法塔的 ℕ 极限，不是固定高度类型中的一个回收编码。

[YiLevelView](YiLevelView.lagda.md) 的 view 给原树投影的内部四形视图，
所有子树仍带合法性且属于 Level。read-low 从低层树及 Lgl 证据给合法层号，
omega-coordinate 再对它构造 Ω。这些运算不读有限码，也不把高层输出
送进固定 HB 类型。最终序数值解释尚未建立，未声称完成成品的值上 View 验收。

## 比较定理的精确范围

Position bound 存储合法子对象 part，及它到同一个合法 bound 的 CP 证据。
CP 是原树的字面第一位置：可经过后继、ℕ 分支和 lc 的第一支 t。

[YiLevelCompare](YiLevelCompare.lagda.md) 的 bounded-compare 对任意 bound
及任意两份 Position bound 返回三种结果之一：

- 第一对象是第二对象的真第一位置；
- 两对象的原树相等；
- 第二对象是第一对象的真第一位置。

证明只沿公共界递归。ℕ 行比较分支编号，再用相邻位置证据进入同一个实际子树；
lc 行进入第一支 t。equal 不识别两份 Legal 证明，也不返回 Level 记录相等。
Ω-position 把已有的定位证据与层号一起送到 Ω 后的合法公共界。

这是给定同界位置证据的定理，不是裸树上的判等或全局三歧。
它也不生产尚未给出的 place 证据。

## 已暴露的覆盖限制

层号树的原 Pre 类型还允许经过 lc.k 和一般分支子层；CP 不自动包含它们。
[YiLevelAudit](YiLevelAudit.lagda.md) 证明一个精确反例：
原 Ω₃ 整体合法，根的层号字段为 2，但 2 不是该 Ω₃ 的 CP 第一位置。
相应地，也不存在原树字段为 2 的 Position Ωthree。

这不是有限展开测试；它否定的是“合法 lc 的层号字段总会自动成为其 CP 位置”。
低层闭对象在这里是该否定的非空实例，不是成品或强度交付。
它没有否定原 Ω₃ 合法、CP 比较或 S3 路线。

**因此尚不能说建议的派发基础全部齐备。**
下一项实质义务是：给 ψ 所需的实际 Ω 索引与目标构造同一个合法公共界下的
位置证据；或者在新文件设计能覆盖它们的位置／合法性接口，并证明 Ω 闭包。
不能直接把 Pre 改名成 Position，也不能给任意两棵裸树假设比较律。
本轮未强加世界更新、拷贝间界互保或自收缩等接口。

## 五堵墙：已读的前提与本轮范围

| 既有定理 | 它约束的具体前提 | 本轮状态 |
|---|---|---|
| DiagKLev／CohWUpd 的 upd→wdec | 对任意裸名字更新一个世界分量，并同时满足 at／off | 无此更新器或律；只比较有 CP 同界证据的对象 |
| CohWNeg 的 no-cross／no-route，HtTowerNStage 的 no-wmatch | 指定拷贝间的单向保界运输，或经中间世界映射同时满足指定两端保界 | 未构造世界拷贝或 Bd 运输，不声称解决相干问题 |
| HtTowerNeg 的 no-retract | 一个固定种类坐标容纳全部 HB，并有读回的截面恒等式 | 未固定 HB 种类或写这种收缩；Ω 返回同一树层号类型 |
| NegLHRecIf 的 fb-must-legalize | LHRecIf 实例及新界恒为 hs e，继而要求全部回灌输出合法 | 没有 ψ／nxt／该反馈实例；Level 构造带证据不等于已经解决反馈 |
| NegThirdPre 的 keep-req／no-lower-rule | 指定留下形状、Sound 的 PS、ad↓ 与两对世界上的路径条件 | 尚无这些留下／下层路径结构，未声称越过此墙 |

本轮没有实填这些墙的反例前提，也没有据 Ω₃ 的 CP 覆盖反例宣称撞上其中一堵。
后续若需要这些前提、UIP／Funext、裸下标律或固定类型回收，按作者条件停下报告。

## 翻译账与未交付项

| 位置 | 来源及当前依据 | 尚需核查 |
|---|---|---|
| LF 的 lc：层号、下界、第一支、守卫分支 | 继承 LevelFixCore 的树侧接口；本轮没有加记号字段 | 守卫为 Cp 加 Lgl，不等于覆盖全部未来派发输入 |
| Ω 后继行的 cO、第一支 Ω_k、up | 继承 LevelFixVal／旧 DomFold 的模板；不是本轮证明唯一必需的形状 | S5 逐字段核查，不能以复用为由免审 |
| Ω 的极限与 lc 行 | 对所有分支逐点结构递归，合法性由泛闭包给出 | 未由此推出 EBO 值或最终 ψ 合法性 |
| Level 的 Legal 证据 | 使层号与合法性同时生成 | 不把它与旧 Cf／HS 证书混为一谈 |
| node 的证据参数独立性 | 沿用 Legal 的 g η e 与 g η e′ 原树相等字段 | 是节点自己的条件，不是 UIP；后续闭合必须实填 |
| Position 与三路比较 | 使用同一合法界下的 CP，借树的相邻第一位置而非记号码 | 位置域有限制，Ω 索引覆盖尚缺 |
| 内部 View 的子对象包装 | 只保存已有树与合法性，原树投影精确匹配 | 成品序数值解释和对应尚缺 |

尚未写 ψ、输出合法性及位置保持、完整回灌、T₃、FGH、S4 的 ι／对应与终点下界。
本轮没有照搬 JiaExactFold 的 ψ 代码；其规则与旧翻译账保留为后续模板。
P1 仍为 x = Ω·ω²，没有新的乙成品下界。

## 复核

从仓库根，用含 stdlib／cubical 的外部库文件，单路 6G：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound1.lagda.md +RTS -M6G -RTS
```

四个数学模块与入口删除各自接口后冷编，五件均 Checking，退出 0。
只使用依赖已有接口，不 ignore-interfaces。代码 safe／without-K，禁用构造 0。
审查文件已由主路从头读陈述和证明，再删接口冷编，不仅引用智能体自报。
本轮没有失败的正式类型检查、堆耗尽或超时，也没有 FGH 数值测试。

导入闭包、成功编译器依赖图及定义切片的范围见 LOG；记号模块和标签依赖均为 0。
切片只是语法近似，编译器导入闭包才保证本候选不引用记号；
二者均不证明未来位置生成或值验收已完成。
