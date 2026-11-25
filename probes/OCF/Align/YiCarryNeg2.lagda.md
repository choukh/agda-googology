# YiCarryNeg2：读回域复查与增补接口的部分否定

**交付：部分否定；读回域反例未找到，K2′⁺ 未否定。**
对“让树自足”的意义是把本轮能排除的情况与仍缺的义务分开：
旧的 tw 4 证书缺口已经补齐，不能再拿它当读回反例；前三行不能单独
保证输出位置保持。对一个满足前三行的具体检验函数，
已有闭反例精确落在 output-step 与 OutputB，不能推广成所有 ψ 的否定。
原纲领、树、证书与接口均不改，没有新强度或值验收。

按任务顺序，先完成 [Read](YiCarryNeg2Read.lagda.md) 的读回搜索，
之后等 README 中 YiCarryPlus 标为“定稿”，单独编译该接口退出 0，
才开始 [Flat](YiCarryNeg2Flat.lagda.md) 对增补接口的检验。
本篇只汇总两件结果，不另造共用接口或实现折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryNeg2 where

import OCF.Align.YiCarryNeg2Read as Read
import OCF.Align.YiCarryNeg2Flat as Flat
```

## 编译定理

| 结果 | 精确范围与失败字段 |
|---|---|
| Read.tw3-omega-carry | `Carry (Ω̂ (tw 3))` 的闭证据，由既有 `tower-carry 4` 给出 |
| Read.no-tw3-fails | index 字面固定为 tw 3 时，全部原守卫且带 LglB 的输入都有目标 Carry；排除该固定层号的 fails |
| Read.constant-read-target、Read.successor-read-target | 上轮两个 Ω̂ 2 的真正读回层号上，全部原守卫且带 LglB 的输入都有目标 Carry；环境全部由既有全塔／有限次读回定理实填 |
| Flat.gate-source | 同一个闭源同时有 Carry⁺、Legal、Reg、PointB，另给严格下一点 p₁；并非空守卫 |
| Flat.no-flat-generator | 对具体函数 flatψ，任何 GtGenerator⁺ 的 grow 都使其在 p₀ 的 output-step.path 失败；不依赖 seed 或指定更新式 |
| Flat.no-flat-rows | 同一个 flatψ 没有冻结的 PsiRows⁺；前三行各自有闭证明，但不能填全记录 |
| Flat.limit-source、Flat.no-flat-output-B | 另一个 Carry⁺ 且 Legal 的闭源上，flatψ 输出的极限相邻 Cp 失败，故其 OutputB⁺ 不可满足 |

flatψ 是保持零、后继、ℕ 极限三行、把 lc 一律送到 1 的具体检验函数。
它没有满足 gt 行，所以这两条输出否定不能推出 `K2′⁺ → ⊥`。
输入源的 Carry⁺、Legal 与其它背景前提均在 Flat 中实填；每个定理
被否定的目标不另当作可满足假设。没有函数外延前提。

## 有限测试与判断

**有限测试：无。** Read 中列出的八个具体输入／层号组合都有类型检查
证书；固定三层号上的全量词结论由已有定理推出。Flat 的源虽是闭项，
“任意 next 的 grow 都破坏 output-step”也是编译定理，不是抽样结论。

**判断／未完成：** 没有找到 ReadOmegaCounterexample，也没有证明其
一般环境为空。tw 3 的 top、suc top、lim const top、三个不同 lc 槽位
及旧的两个读回层号均已检查；不存在尚缺 tw 4 或 tw 5 的证明停点。
原记录未给较强根路径和两次 Ω 的完整 Carry 包，本轮既未从原记录
生产它们，也未找到满足原输入条件而目标 Carry 不成立的源。

K2′⁺ 方面，未找到与 ψ 无关的 next／grow／output-step 否定，也未找到
已经满足完整行律的 ψ 的 OutputB 反例。本轮的部分否定只排除 flatψ
及其常 1 的 lc 读法，不关闭 K2′⁺、规范塔折叠或乙路线。没有实施修补。

翻译账：只新建三个本前缀文件；应用既有树侧证书、构造闭反例并反演
失败字段，没有新构造子、合法性字段、记号规则或阶段专属前提。
公共界逐对保留，没有无界比较或全局三歧。第 4 层逼出：无。

## 冷编与审计清单（2026-11-10）

| 模块 | 仅删自身字面接口后重编 | 堆上限 | 退出码 | 目标 Checking |
|---|---|---|---|---|
| YiCarryNeg2Read | 是 | 6G | 0 | 有 |
| YiCarryNeg2Flat | 是 | 6G | 0 | 有 |
| YiCarryNeg2 | 是 | 6G | 0 | 有 |

只删除这三个模块自己的字面接口，
依赖用缓存；不使用 ignore-interfaces，不声称从头重编整个导入闭包。
每次 Agda 单路使用 6G 堆，退出码直接读取，不经过管道。

- 三件均 safe／without-K／lossy-unification；代码中的公设、洞、
  停机／正性豁免、信任相等、函数外延前提均为 0，无尾随空白。
- Read／Flat／入口的本地导入闭包分别 31／24／34，库叶均 19；
  成功编译器依赖图与源码的本地集合逐一相等。importclosure 的
  完整白名单为 OCF.Align.Yi、OCF.Align.RR4RegOmega2、
  OCF.Align.RR4CoordRoot、OCF.Align.LevelFix、OCF.Free.Level、
  OCF.BTBO；白名单外与禁用表命中均为 0，无记号／C 线。
- 成功 HTML 的定义切片：Read 的 tw3-omega-carry 143、no-tw3-fails
  147、constant-read-target 153、successor-read-target 152 块；
  Flat 的 gate-source-carry 46、gate-source-legal 43、no-flat-generator
  79、no-flat-output-B 60、no-flat-rows 84 块。各根记号模块块数与
  记号词命中均为 0。单路 6G 成功生成 EboLean3Lab HTML 作正对照，
  ebo-lab″ 为 352／33／36，未删其旧接口，不导入本轮模块。
  切片只作语法近似，不代替编译器闭包或值验收。
- 已有 YiCarry、Bounds、Neg、NegRead、YiK1b 四件、LevelFixCore、
  LevelFixVal、YiRegBase 共 11 个文件的源码摘要与开工时相同。
  本路只新增本前缀三件；没有改 README／LOG 或其它已有文件，
  没有改 src／archive、安装包、提交或推送。

复现从仓库根，库文件包含 stdlib 与 cubical 的有效路径：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryNeg2Read.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryNeg2Flat.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryNeg2.lagda.md +RTS -M6G -RTS
python3 probes/Survey/scripts/importclosure.py OCF.Align.YiCarryNeg2Read OCF.Align.YiCarryNeg2Flat OCF.Align.YiCarryNeg2 --only OCF.Align.Yi --only OCF.Align.RR4RegOmega2 --only OCF.Align.RR4CoordRoot --only OCF.Align.LevelFix --only OCF.Free.Level --only OCF.BTBO
```
