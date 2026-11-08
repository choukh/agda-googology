# 统一生成、读回闭包与有界运行分派

接续 [实际高源生成](EventGenerated.lagda.md)。本批开始把逐层特例
替换成按结构参数的一步构造：生成关系不再只写 D₁/D₂，读回包能够
生成自己的编码，并在后继、有覆盖证据的 ℕ-极限处返回同一种记录。
这不是 ψ₀Λ 闭项，也没有新增强度下界。

## 已写出的结构结果

| 部分 | 定理或构造 | 精确范围 |
|---|---|---|
| [统一关系](UniformGeneratedIf.lagda.md)、[换证与种子](UniformGeneratedBuild.lagda.md) | 任意 KS 与许可 Z，异层低坐标按两份原 Acc 递归；关系推导可以换 Acc，不要求证明相等。原 Ωd 全层实例实填。 | 世界及未来路径相同，不是任意跨历史关系，也没有所有 raw 数据自反。 |
| [原 Int](UniformGeneratedInt.lagda.md)、[实际生成族](UniformGeneratedActual.lagda.md) | 原 Int 全部 nc 与 ni 内外递归保持关系；原 Ωd 源、原 Ωd 前缀和 identity 回调实填；零层原 sum 保完整 Same。 | 原程序的参数域是 step T/ZK T，T 任意；不把它扩大成任意 Z 上已有 Int，也没有补回旧 nc 丢失的坐标前缀。 |
| [后继解释](UniformReaderStep.lagda.md)、[编码闭包](UniformReaderReify.lagda.md) | RenderingReader 的编码由泛目标 render 按树结构生成；Successor.next 返回同类读回包，family 真实递归调用它。新种类使用完整 HB T 坐标反馈。 | 源数据仍是旧双槽 Wd₂，render 的层位置须对所有世界成立；合法性不等于编码读回保值。 |
| [极限闭包](ReadLayerLimit.lagda.md) | 分支包与 step(F n)→sup F 的覆盖给同类极限包；omega 及其后继实填。Climb 对任意起包迭代后继并取极限，包可再次使用。 | coverage 必须给出；不从一般合法极限推断它。尚非世界局部 Ω 准入或全事件迁回。 |
| [覆盖的正反信息](ReadLayerBoundary.lagda.md)、[树侧充分条件](ReadLayerCofinal.lagda.md) | 合法常零极限否定旧 NdI 对任意合法 x 的直接推广；实际后继覆盖路径则能把整份新种类放进族并。任意底树的后继塔实填条件。 | 只否定写明的旧接口推广；已有有限／ω 包有效。嵌入本身不是 reader、编码或完整运行。 |
| [有界同形等式](BoundedShapeEquality.lagda.md)、[实际分派](UniformGeneratedDispatch.lagda.md) | 同合法世界／同合法字面公共界内，Shape 层相等；原 rkT 对相关层给同一 keep/rise 分类。结果证书实际来自原比较程序。 | 没有全局函数外延、跨历史自动公共界、StH 路径相等或完整 Run 状态保持。 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformCore where

import OCF.Align.UniformGeneratedIf
import OCF.Align.UniformGeneratedBuild
import OCF.Align.UniformGeneratedInt
import OCF.Align.UniformGeneratedActual
import OCF.Align.UniformGeneratedDispatch
import OCF.Align.UniformReaderStep
import OCF.Align.UniformReaderReify
import OCF.Align.ReadLayerBoundary
import OCF.Align.ReadLayerCofinal
import OCF.Align.ReadLayerLimit
import OCF.Align.BoundedShapeEquality
```

## 对目标的意义

此前只有单向后继解释时，每次继续都还要另给编码；现在后继和有
覆盖的 ℕ-极限得到的是同类包，可以再次组合。新增字段来自原构造子、
实际低坐标输入与字面位置；没有按记号基本列加新节点。包的初值和
原理继承 FamFold/LvRd 的既有有限与极限工作，不将它们重新算成新站。

有界同形定理补了统一关系到实际层分派的一项证明义务，却只同步
分支类别。后续仍需 keep 坐标、状态、运行输出及实际读回之间的
保持；旧 GenFold 的有损 reader 方程没有因关系证明而改变。

统一关系载体是原 DataG，当前读回构造使用另一套原数据和 Wd₂。
两部分尚未接成一个全种类事件程序；不能将它们并列就当作接口已经
互相实填。原 EvFold 双历史的数据转换、世界局部 Ω 路径、全事件
read/drop、内部 View、完整前三层成本及终点 EBO 下界都仍需交付。

本批是摆脱侧的结构信息，不据此开启新的攀爬模块。没有完整成本
切片，不拿新叶文件行数声称满足 1513，也不以未来压缩作保证。
