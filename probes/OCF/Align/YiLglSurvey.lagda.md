# D7 侦察：禁止极限内自反步的依赖与代价

**(i)** 守卫原本显式包含等号，第一路径选择有明示理由，弱步进也有后来的作者决定；未找到原始 Raw.Lgl 专门要求相邻自反的理由，不能判作误写。

**(ii)** 在现有 lc 分支接口下须平行 LF／Raw／Gd 整个块；基础 Core＋Val 原文约663行，按当前全层覆盖的导入文件粒度扩展约20件、2291行，均是复制范围估计。

**(iii)** Ω̂、up、cO、全部塔层及 Λ 可以随构造给结构严格步进，已有平行编译证明；完整 ψ 模板的实际严格保持仍未查清，不能从基础闭包自动推出。

本轮只侦察。已先读 [RouteReview3 §5.8](../../Survey/RouteReview3.md#58-s3-第八至十一轮与止损-2026-11-09-补记)。
所有新文件均 YiLgl*；旧 LF／Raw／Lgl／Legal／Reg 与既有结论不动。
新平行定义只是编译探针，没有采用为成品，也不续写 ψ、γ 或 Reg。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglSurvey where

import OCF.Align.YiLglCore
import OCF.Align.YiLglVal
import OCF.Align.YiLglStrict
import OCF.Align.YiLglCompare
-- 以下明读甲与记号，仅为模板的第4层诊断；前四件不依赖它。
import OCF.Align.YiLglTemplate
```

## 1 定位：两种自反分得开

[LevelFixCore](LevelFixCore.lagda.md) 第113、158、162行：

```text
Cp y a b = (a ≡ b) ⊎ Dn y a b
Gd k c η = Cp k c η × Lgl k η
Lgl y (G.lim f) = (∀n Cp y (f n) (f (suc n))) × (∀n Lgl y (f n))
```

前两行使 η=c 在 Lgl k c 有证据时可入，是包含下界；第三行才是相邻项可相等。
[LevelFixVal](LevelFixVal.lagda.md) 第156行另有块外 Legal 的弱 CP 步进。
它不进入旧 LF 的定义，与块内 Lgl 的类型传播地位不同。

本轮 [YiLglCore](YiLglCore.lagda.md) 仅把第三行 Cp 改为 Dn，
保留 Cp 的等号分支、Gd 的下界 Cp，以及 lc 的第一支界与单调性的弱 Cp。
“禁自反”在这里精确指携带一条 Dn 真第一路径，不要求判定 a≠b，
也不是把全部 Cp 全局改成严格关系。
YiLglStrict.lower-equality 对一切 k 实填 Gd k (cO k) (cO k)，
而 no-old-coordinate 排第十一轮的 raw-lim const raw1：两种要求可同时成立。

不过块内定义必须一同平行：

```text
Lgl → Gd → lc 的 g 参数类型
             → Pre／Low／GdL／Kid／KidR／Raw 的相关分支
```

Lgl 不是改一个外部谓词就能从旧 lc 的既定函数定义域里删去输入。
若保留旧 LF、另加过滤谓词，旧 g 仍须在全部旧 Gd 上定义；这不是同一接口的 D7 替换。
本轮平行块确已通过正性、宇宙与停机检查；不声称其它编码也逻辑上必须复制 LF。

## 2 历史依据：原文与查找边界

以下是读原文与语法检索所得，不是关于作者动机的形式定理。

- [LevelFixCore](LevelFixCore.lagda.md) 第7行称守卫是“同层的字面相等 (`≡`) 与第一位置. 不穿过分支”，并指向 no-WFˢ-Ω⁺ 逼出的 Fg。
- [DomFold](DomFold.lagda.md) 第11行的守卫显式取相等或第一路径，并说“第一路径没有分支, 所以搬运带对一切表的转移”。这解释守卫路径的选择，不能冒充相邻项允许停顿的理由。
- [LvIRGuardProbe](LvIRGuardProbe.lagda.md) 第133、150至159行使用弱输出步进，说明第一支／各支输出在守卫之上，因而链点是合法输入；未找到“相邻必须相等可入”的专门解释。
- [LOG](../../LOG.md) 第298至310行记录 LevelFix 的归纳递归块、闭包与当年的 UIP 停点，没有写 Raw 相邻自反的专门理由。
- [LOG](../../LOG.md) 第1069、1072行记录后来保留弱步进的决定，原文如下；针对的是值上严格 View，不是2026-11-03 Raw.Cp 子句的原始动机证明。
- LevelFixCore 第6行解释 top 是为了让极限层 Ω 不必写跨孩子步进；LevelFixVal 第53行解释 cO zero 用字面1才可走到字面2。这些理由也不能当作停顿必需的证据。

> 与纲领第 1 条解释的差别: AGENTS 写 "ℕ-极限 (严格递增的 f)"; `strict→LPO` 说按值严格递增不可得, 记录改用目标树自己的合法性 (第一位置 `⊲`, 自反). 是否改 AGENTS 的措辞, 作者定.
>
> 作者 2026-11-05 定: AGENTS 纲领第 1 条解释里 "严格递增的 f" 改为 "相邻项按目标树自己的合法性步进 (第一位置)" (依据 `strict→LPO`); 派 BrwWf 证 View 部分的良基.

语法检索范围：上述四篇全部讲解及代码、LOG 中 LevelFix／LvIRGuard／DomFold、
“自反／停顿／严格／步进”条目。未找到专门理由只表示这个范围的查找结果，
不是穷尽所有历史材料，也不表示从未有意这样设计。

## 3 依赖清单

表中“用到”专指**允许相邻自反**，不把一般位置关系的自反混进去。
编译事实与仅按源码读取的结论逐项分开。

| 项目 | 相邻自反依赖 | 证据与保留的义务 |
|---|---|---|
| Legal-Ω̂ | 未用到 | Raw 改严格后，平行原定理编译通过；另有 Ω-legalˢ，连 LF 的 lim 也要求 Properˢ 时仍全层成立。需要输入的步进证据，但不需要其为自反。 |
| cO／Lgl-cO／branch | 未用到 | cO 只构造 raw1 或 top，没有 Raw lim；平行原证明不改。lower-equality 也给下界等号可入。 |
| lgl→Legal | 未用到 | 原证明一处需要 Dn→Cp 的 inj₂ 适配；严格版 read-legalˢ 用 dn-proper 直接输出 Properˢ。 |
| Legal-tw | 未用到 | 平行弱原定理通过；tower-legalˢ 对全部 n 成立，没有逐层补证。 |
| Legal-Λ／tw-step | 未用到 | tw-proper 对全部 n 给严格步；Λ-legalˢ 直接组合。旧 tw-step 的 suc self 是外层真路径，不是相邻项用 self。 |
| cmpC／cmpD | 未用到 | 全部平行比较证明通过；仅两处 stepsC 调用将严格步注入 Cp。仍保留位置相等和有公共界的比较。 |
| compare／bounded-compare | 未用到 | YiLglCompare 在平行严格 Legalˢ 下编译通过；极限行只把 Properˢ 弱化成 CP。未变为宽位置／裸层号比较。 |
| S3 Level | 用到其弱 lim 接口 | 旧 Level.lim 接受 ∀n CP，可写常列；YiLglCompare 的最小 Level／Ω／塔／Λ 已平行编译，lim 改收 Properˢ。旧全部调用点尚未逐件移植。 |
| S3 InvD | 未用到（逐体读源码）；平移未查 | YiDBase 的记录和需求弱化没有构造极限列。zero-position／zero-common 的 self 是位置证据。它仍依赖旧 Level／Field／Ctx，不能直接作用于新 LF。 |
| all-retained-reg | 未用到（逐体读源码）；平移未查 | YiRegCover 的 up-cover 对任意 Raw 结构递归，不消费 Lgl.lim 的步进；接入 RetainedDomain 时才带原 Gd。仍要迁移 Below／Field／Reg 等类型，不能据源码相似称全线已编译。 |
| JiaExactFold 的 ψ 模板 | 一般接口允许停顿；实际严格输入未查 | constant-output 已编译为 refl：常零极限源输出常种子极限。它没有实际 Rep／Reach 源证书，也不满足新源严格性，不能据此否定实际轨道。 |

所有“未用到”都不意味着可以删除 Cp／CP 的自反构造子。
CP-tr、cp→CP、比较的相等行、守卫、第一支与单调性的弱关系仍使用它们。

### 隔离改动的编译证据

按 Agda 代码块逐行 diff：

1. YiLglCore 对旧 Core：除模块名，只改 Lgl.lim 的 Cp→Dn，以及 cmpD 两处 inj₂ 适配。
2. YiLglVal 对旧 Val：除模块／导入名，只改 lgl→Legal 的 lim 行一处 inj₂。
   此文件保留弱 Legal，用来隔离 Raw 改动；不能误称它已改严格 Legal。
3. YiLglStrict 另定义 Properˢ、Legalˢ，并给全层闭包。
   所有结论属于平行 LF，旧证书和新证书不能混用。

这些编译只说明上述接口有实现，不保证最终 ψ 或终点值，也不把 D7 当成已批准的成品改动。

为定位唯一读回适配，另尝试把 Dn step 直接送给旧形状的 cp→CP；单6G退出42：

```text
<实验目录>/YiLglReadAttempt.agda:7.52-56: error: [UnequalTerms]
(Dn y a b) !=<
((a Agda.Builtin.Equality.≡ b) Data.Sum.Base.⊎ Dn y a b)
when checking that the expression step has type
OCF.Align.YiLglCore.Cp y a b
```

这里只缺 inj₂ 包装，正式平行模块加上后退出0；不是不可能性定理。
失败轮没有用于 HTML 或依赖切片。

## 4 范围与行数估计

计数方法：语法 importclosure 从旧 YiRegCover 出发，有22个本地模块。
OCF.BTBO／OCF.Free.Level 是不读 LF 的共享基础，可复用；其余20件现有全文2291行。
下表行数是源文件现有实测行数，**作为平行复制成本的估计**，不是最终新增行数承诺。
表按当前文件粒度给范围，不表示每个证明都需重写。

| 平行候选模块 | 估计行数 | 平行候选模块 | 估计行数 |
|---|---:|---|---:|
| LevelFixCore | 324 | LevelFixVal | 339 |
| YiLevelBase | 101 | YiLevelCompare | 60 |
| YiSpineCommon | 33 | YiSpinePrefix | 34 |
| YiCtxBase | 48 | YiCtxFork | 213 |
| YiCtxStep | 105 | YiDBase | 55 |
| YiRBase | 39 | YiRTransport | 119 |
| YiRCountable | 124 | YiRStep | 67 |
| YiGammaBase | 85 | YiDispBase | 116 |
| YiDispCountable | 117 | YiDispHigher | 137 |
| YiRegBase | 59 | YiRegCover | 116 |

这里包含现有导入带来的旧反例模块（如 Fork／Higher）；它们的反例在新域是否仍成立要重查，
不应不加核对地复制成结论。提取纯接口可以减少复制，但本轮没有改旧模块做此优化。
若只要 Level 与比较，则旧闭包分别为5、6件本地模块，已在本轮做最小平行接口。
若还要旧内部视图 YiLevelView，其现文52行须另迁；完整 InvD 实例／实际验收文件未计入此2291行。

不需要平行复制旧 LevelFixU 或因 D7 重开旧 UIP 折叠；S3 本来就没有导入它。
S1 的 Jia* 使用不同树族，不直接依赖 LevelFixCore；其源码无需因更换 LF 而改导入，
但未来把其规则实现到新树上的合法性合同仍是新工作，不能漏计。
本轮没有移动、修改 src 或 archive，也未把历史全部反向依赖都当作迁移目标。

## 5 构造的严格步进、壁垒与未决项

**编译过的事实：** YiLglStrict 的 dn-proper 把每个固定层 y 上已有 Dn 证据
读成 Properˢ；Ω-proper 把已有 Properˢ 映成 Ω 两端的 Properˢ。
firstN 沿 Pre 的实际槽位递归，em／top 行也由具体第一支给严格路径。
没有先判定两个对象是否相等或谁更大。

Ω-legalˢ／read-legalˢ／readK-legalˢ 互递归，随输出产生严格合法性；
Legalˢ 的 lc 仍只要原形状的弱第一支和单调证据。
tower-legalˢ、tw-proper 对一切 n，Λ-legalˢ 一次组合，均不是有限采样。
cO 不输出极限，因而没有相邻步义务。

**可选小样本已编译：** no-old-coordinate 排第十一轮坐标；
omega1-R₂ 给新 LF 的 Ω̂1 满足与旧 Reg₂ 同形的谓词 R₂。
R₂ 只作该单点检验，未证全层 R₂ Ω 封闭，也不能拿来填旧 Reg₂。

**模板的界限：** [YiLglTemplate](YiLglTemplate.lagda.md) 只读已有 ψ 的归约，
constant-output 对全部 Seeds 成立；one-spec 给种子合同非空实例。
但常零源没有新严格性、Rep 或实际 Reach 证据。
JiaExactFold 的逐点极限行、gt 中 out(iter step start n) 本身未携带
“out／step 保持严格路径”或“链点输出不相等”的字段。
所以完整模板的严格步进必须另证，不能由本轮基础闭包代替。
本轮未实现或改写 ψ／γ，也未枚举实际链来把测试冒称全称证明。

**壁垒核对（接口判断）：** 本轮不需在宽位置上判定是否严格。
[Barrier.barrier](../Barrier.lagda.md) 要含 Ordᴰ 精确初始段、Ω共尾元及相应有界三歧接口；
这里的比较仍只针对有字面 CP 公共界的两个位置，未给那项精确初始段接口。
[BrwViewNeg.strict→LPO](BrwViewNeg.lagda.md) 要值上的严格 View 与 Enc；
本轮只有结构 Properˢ，没有值严格性或把任意弱合法对象严格化的程序。
故本次编译没有实填上述壁垒前提，不能由“strict”这个词推出撞墙。
未来若为 ψ 所有原弱输入事后消除停顿、或通过宽位置判定来选严格子列，
须重新逐项核对；本轮没有这样的构造或否定定理。
没有证出“禁止相邻自反必然推出 LPO”，也不否定 D7 路线。

## 6 验证与三个答案的范围

六件新模块从仓库根、逐件删除自己的字面接口，单6G冷编；禁用构造与导入审计见 LOG。
Core／Val／Strict／Compare 的树侧闭包不含记号或 C 线；
Template／Survey 明读已有甲模板作第4层诊断，不能标作成品闭包干净。

最终回答仍是：

1. 有后来保留弱步进的决定；原始 Raw 相邻自反的专门必要性理由未找到，守卫等号与相邻自反另算。
2. 基础修改小，但类型传播需平行块；到当前全层覆盖约20件、2291行只是文件粒度估计，未完成整线移植。
3. 基础 Ω／读回／全塔／Λ 可随构造严格；ψ 的实际相关严格输入是否也能这样输出，仍未查清。

P1仍 x=Ω·ω²；本轮没有新值下界、FGH 或成品闭项。
