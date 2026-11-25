# YiIntr：证据进树的平行块侦察

**对纲领与目标的意义：内置 Carry⁺ 的类型可以通过正性、归纳—递归与
停机检查，gt 的起点确实能只读结点字段取得；但证据进入树后也成为树的
可观察数据。本次按原四行配方构造到 tw 3，已编译证明它不满足原 Legal.irr
的同形要求。因此本次交付是可编译骨架、有限闭项及具体成本／障碍，
不能作为整线迁移已可行的结论，不采用为新主线。是否继续改定义交作者定。**

没有完整 ψ，没有全塔或 Λ 迁移，没有序数值界、FGH 或内部 View 的值一致性
定理；没有否定“证据进树”整条方向。本轮只新建 YiIntr*，原文件不动。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIntr where

import OCF.Align.YiIntrCore
import OCF.Align.YiIntrRaw
import OCF.Align.YiIntrFinite
import OCF.Align.YiIntrCheck
import OCF.Align.YiIntrPosition
```

## 1 交付与三档

| 档 | 结果 | 精确范围 |
|---|---|---|
| 编译事实 | [Core](YiIntrCore.lagda.md) 的完整块通过 | 独立 LF／Raw／Gd／Lgl／Nested／Reach；不是旧 LF 的外部子类型，也没有跳过检查 |
| 编译定理 | [Position](YiIntrPosition.lagda.md) 的 parts-below | 第一支相等或路径条件推出**原类型**的 Below；parts-instance 对任意 k 给非空实例 |
| 编译定理 | branch-no-parts 及 branch-reg／branch-carry⁺／branch-legal | 原根位置可能只经 Ω 分支成立，第一支条件是加强，不是等价改写 |
| 编译定理 | [Check](YiIntrCheck.lagda.md) 的 root-bound／all-Reg／all-Carry⁺ | 对全部新 LF，从内置字段重建新类型上的对应证书；Reg 量化新守卫域 |
| 编译构造 | [Finite](YiIntrFinite.lagda.md) 的 cO／Ω̂／tw₀..tw₃ | Ω̂ 的类型是 `∀ {x} → Ready x → LF`；Ready 是本次配方所需的显式构造环境，不是 LF → LF |
| 编译定理 | positiveWorld／CountResult.canonical | 对全部合法 Raw 0 正坐标递归生产规范环境，非有限坐标枚举，亦无未知 Ω 闭包前提 |
| 编译定理 | start-lc／tw₂-start／tw₃-start | 起点是下界自身；tw₂ 的初支为 tw₁，tw₃ 的初支为 tw₂，均 refl |
| 编译定理 | TreeOnly.certificate-coherence／lim-function-coherence | 同一棵新 LF 上，任意外部证书被定义性忽略；没有构造满足四行的 run |
| 编译否定 | no-total-ready | 本次 World／CanonicalWorld／Ready 合同不能对全部新 LF 无条件实填；闭反例是 suc(lim const 0) |
| 编译否定 | tw₃-not-root-irr | 本次 tw₃ 的同一坐标有两份真实守卫，其分支输出 LF 不相等，故不满足原 Legal.irr 的同形要求 |
| 有限测试 | 只构造塔的 0..3 项 | 有限覆盖不冒称全塔；tw₃-form 与起点等式为这些闭项的编译等式 |
| 判断 | 可以把起点证据移入树，但尚未解除证据一致性成本 | 在本构造中，外部证书问题转成了树内位置字段的分支一致性问题；不据此穷尽其它方案 |

否定定理不以前提矛盾的折叠记录为条件：suc(lim const 0) 本身是闭 LF，
flat-successor-carry⁺ 实填其新 Carry⁺；tw₃ 本身已构造，coord-lawful 与
coord-guard 0／1 实填坐标和两份新 Gd。World0、world1 及所有本轮使用的
CanonicalWorld 也有闭证据。无条件的 no-total-ready 只排本次环境合同的
全域化，不把不可满足的某个 World 假设冒称有信息的条件定理。

## 2 骨架定义原文与接口差别

下面逐字摘录 [完整骨架](YiIntrCore.lagda.md) 的关键声明；其余 Raw 位置、
合法性及 Nested 的完整方程都在该文件内，未用省略号或洞交付。

```text
data LF where
  zero : LF
  suc  : LF → LF
  lim  : (ℕ → LF) → LF
  lc   : (k : LF) (c : Raw k) (w : Lgl k c) (b : Nested k c)
         (t : LF) (p : Reach (suc k) t)
         (g : (η : Raw k) → Gd k c η → LF) → LF

data Reach where
  here : ∀ {a} → Reach a a
  via-suc : ∀ {a x} → Reach a x → Reach a (suc x)
  via-lim : ∀ {a f} n → Reach a (f n) → Reach a (lim f)
  via-first : ∀ {a k c w b t p g} → Reach a t →
    Reach a (lc k c w b t p g)
  via-branch : ∀ {a k c w b t p g} η e → Reach a (g η e) →
    Reach a (lc k c w b t p g)

Gd k c η = Cp k c η × (Lgl k η × Nested k η)
```

位置改写的理由：原 Reg 的 `Below (suc k) node` 提及待造结点，
不能直接当作这个构造子的自指参数。本次只要求已有第一支 t 承载
`Reach (suc k) t`。Reach 是包含端点自身的有限子树路径；在新类型上，
reach-edge 把它接到 e-first，root-bound 遂给原形状的 Below。
旧类型上 parts-below 对等号分支用 one e-first，对真路径分支用
more p e-first；两个版本都没有假定结点已经存在。

这是明确的充分条件选择。Position 的 branch-node 同时有原 Reg、
Carry⁺、Legal，却没有 Parts；所以不宣称原树都能搬入新类型。
另外两项改变同样不能略过：k 自身现在也是内置证据的 LF，强于原 Carry⁺
只要求 Reg k；新 Reg 的分支只量化新 Gd，而原 Reg 覆盖全部旧 Gd。
本轮没有给跨类型的 forget／保值关系，不能把 all-Carry⁺ 送入旧 K1′。

Raw 保留独立的参数化语法 G.R，含 zero／suc／lim／lc／em／top。
Raw.lc 的下界由 Nested 检查，不是每个裸 Raw 都自动可读回。
因为 Gd 进入 LF 和 Raw.lc 的负位置，新增 Nested 及其 Low／Kid 运输
必须随 Pre／Low／Kid／Raw／Cp／Lgl 一起进原归纳—递归块。
同层 Raw 的相等仍保留；没有引入把层号和坐标打包后比较的 Elt 相等，
也没有在 Gd 中加入 LF 上的相等。因此没有重演 LevelFixCore 开头 P1
的那种异层相等依赖。本次正性接受是检查器事实，不是一般编码定理。

## 3 Ω、tw 3 与“只读树”的实际范围

cO 仍在零层取 raw1，在其它层取 top，Lgl／Nested 均有全层证明。
Ω̂ 的四行沿原配方：零取 1，后继用下层 cO 与读回，ℕ极限逐项，
lc 保留下界并递归第一支和各支。区别是每次构造 lc 必须当场生产 p。

World 只保存候选目标与读回环境，不单凭路径认证它是 Ω。
CanonicalWorld 另用零／后继／极限的归纳配方认证环境；Ready 的后继行
要求该认证。其余行按结构显式列出新第一支的 p 与递归环境。
positiveWorld 内外都是实际结构递归：后继用真子坐标环境，极限的每项
与 raw1 在字面公共界 f(j+m) 下比较，界的 Lgl 来自输入列。
没有按塔层硬填不同的子情形，也没有假定所求 tw₃ 或下一次 Ω 已存在。

本轮定义了 tw₀、tw₁、tw₂、tw₃；没有用截断的 ℕ 函数冒充全塔 tw。
tw₃ 的外层仍是第零层 lc，其第一支为 tw₂，每个合法正坐标 η 的分支
为按上述配方构造的 Ω̂(read0 η)。这个全部坐标族已经通过类型与停机检查。
但 Ω̂ 是带 Ready 的操作，不能删去环境后宣称任意裸新树均可再取 Ω；
no-total-ready 精确限制本次合同，生成域中的后续环境仍是开放义务。

gt 起点程序的原文是：

```text
start-node (lc k c w b t p g) = g c (inj₁ refl , w , b)
```

因此答案是**起点可直接调用，且对所有 k 成立**；第零层自然包含其中。
这不生产 next、grow、output-step，不证明整个 gt 行或 ψ。

同一 LF 的外部 Carry／Legal 等证明被 run 忽略时，TreeOnly 的两个一致性
等式都是 refl。内部证据却已成为 LF 的参数，本轮还测到了真实差别：
coord = suc(lim const raw1)，两份守卫分别在极限里选 0、1；其 Lgl 和
Nested 相同。tw₃ 分支返回的 lc.p 以 via-lim 0、via-lim 1 开头，
actual-mark 直接读出这个数。tw₃-not-root-irr 所否定的是这两棵输出树的
字面相等，正是原 Legal.irr 会要求的内容。
没有把“外部证书被忽略”说成“任意换内部证据仍相等”。

这也给迁移的硬限制：本次 tw₃ 虽有内置 Carry⁺，不能原样补出原 Legal
的同形证书。本轮未修改 Legal 或其 irr 以让例子通过，亦不继续补完整 ψ。
若采用该方向，必须先由作者决定是否另选内置字段／生成方法；
本侦察不把这种尚未设计的改动计作已经解决。

## 4 迁移成本：现有文件粒度的估计

以下是**估计口径**：取现有 YiCarryPlusInstances 的语法导入闭包，
共享 OCF.BTBO 与 OCF.Free.Level 两件不平行，其余 25 件全文共 4204 行。
数字由当前源码实际计数，但把它们当作未来平行复制范围是判断。
这不是成品四层切片预算，也不是已经完成的迁移行数。

| 范围 | 件数 | 现有全文行数，作为复制范围估计 |
|---|---:|---:|
| LevelFixCore／Val | 2 | 663 |
| Level／Spine／Ctx／D／Disp／Gamma／R／Reg 基础和现有诊断依赖 | 12 | 1128 |
| RR4CoordRoot／RR4RegOmega2 的读回路径基础 | 2 | 326 |
| YiK1／YiK1bBase／YiK1bReg 的有限次数归纳 | 3 | 694 |
| YiK2Base 的 Raw 运算，以及 Carry／Bounds／Plus／Read／Instances | 6 | 1393 |
| 合计 | 25 | 4204 |

12 件的具体名单是 YiLevelBase、YiLevelCompare、YiSpineCommon、YiCtxBase、
YiCtxStep、YiDBase、YiDispBase、YiDispHigher、YiGammaBase、YiRCountable、
YiRegBase、YiRegZeroLimit。最后一组含 YiCarry、YiCarryBounds、YiCarryPlus、
YiCarryPlusRead、YiCarryPlusInstances、YiK2Base。没有重复算共享依赖。

与 D7 参照的 20 件／2291 行不同：D7 的根是 YiRegCover，本表的根是
规范 Carry⁺ 全塔／Λ 实例。25 件里有因旧导入组织带来的诊断模块；
新域下它们的反例未必成立，提取接口能少复制，不能逐字搬结论。
若还迁全层保留覆盖，YiRegCover 的现有闭包与本表联合另增 7 件／705 行，
合计为 32 件／4909 行的复制范围估计，不把两个有重叠的闭包直接相加；
完整 InvD 实例、γ／回灌、ψ 与值验收均不在本表中。

判断性的工程预留：在不另增主要机制、且先解决本次 irr 失败的条件下，
内置字段的构造、规范环境及新旧对应另预留约 300–800 行，
于是按现有文件边界是约 25 件、4500–5000 行的工作量级。
这不是完成迁移的上界；本次 irr 反例之后，修复方案未定，无法可靠给出
总上界。不能以本轮约千行的有限骨架替代这个全塔估计。

必须重证或重新实现的内容：

- Legal-Ω̂、lgl→Legal／legalN、Ω̂-CP：新 Gd 改变 Raw 函数域，
  lc 多了证据字段，守卫 irr 不能再靠“读回不读证据”的原 refl 结束。
  其中本次 tw₃ 的同形 irr 已明确失败，不能只改导入名。
- Legal-tw、tw-step、Legal-Λ、Legal-ΩΛ：须先生产全部次数的 Ready，
  再交新合法性及相邻位置；本轮没有 Λ，也没有无条件 Ω 闭包。
- K1′ 与 Carry⁺ 全塔／Λ：在新类型上 all-Carry⁺ 使“已存在闭项的伴随
  证书”成为结构定理，但全塔闭项存在性及其 Legal 仍要另证；旧 K1′
  的记录属于旧 LF，不能直接实例化。
- Reg／Below／槽位覆盖与读回根路径：root-bound／all-Reg 已有新版本；
  后续 Field、保留分支覆盖及跨层读回必须随新域核查。
- Raw 第一位置运算：本轮 Raw 已重编 Cp-tr／lgl-cp／cmpC 等，
  只覆盖新类型的相同公共界接口；不是所有旧下游合同都已迁移。
- 内部 View 的值一致性、旧树与新树的值关系、最终 EBO 验收均是独立义务。
  本轮不以构造成功、环境认证或树的语法相似作为强度定理。

## 5 冷编、禁用构造与导入审计

2026-11-10，Agda 2.8.0.2，六件依次单进程冷编，全部
`+RTS -M6G -RTS`。只删本轮模块自己的精确接口，依赖用缓存，
不使用 ignore-interfaces，不称从头重编整个闭包。退出码由子进程直接
取得，不经过管道；每件都有自己的 Checking 行。

| 模块 | 自身接口已删 | 堆上限 | 退出码 | 编译器图总数／本地数 |
|---|---|---|---:|---:|
| YiIntrPosition | 是 | 6G | 0 | 169／24 |
| YiIntrCore | 是 | 6G | 0 | 68／1 |
| YiIntrRaw | 是 | 6G | 0 | 138／3 |
| YiIntrFinite | 是 | 6G | 0 | 139／4 |
| YiIntrCheck | 是 | 6G | 0 | 140／5 |
| YiIntr | 是 | 6G | 0 | 174／29 |

六份 dependency-graph 的本地模块集合逐一与 importclosure 的源码集合相同。
Core／Raw／Finite／Check 的源码本地数为 1／3／4／5，库叶为 6／10／11／11；
白名单完整为 OCF.Align.YiIntr、OCF.BTBO，禁用表命中与白名单外均为 0。
Position／入口本地数 24／29，库叶均 19；它们用于核对旧类型，白名单为
OCF.Align.Yi、OCF.Align.RR4RegOmega2、OCF.Align.RR4CoordRoot、
OCF.Align.LevelFix、OCF.Free.Level、OCF.BTBO，同样全为 0。
不把 Position 的旧类型导入算进独立 Core 的依赖。

入口及 EboLean3Lab 分别以单路 6G 成功生成完整 HTML，退出码均 0。
正对照没有导入本轮数学模块，没有删除它自己的接口。

| 成功 HTML 的切片根 | 到达块／记号模块块／记号词命中 |
|---|---:|
| all-Carry⁺ | 33／0／0 |
| start-node | 26／0／0 |
| TreeOnly.certificate-coherence | 28／0／0 |
| positiveWorld | 86／0／0 |
| tw₃-form | 89／0／0 |
| tw₃-not-root-irr | 100／0／0 |
| 正对照 EboLean3Lab.ebo-lab″ | 352／33／36 |

切片仍只是语法近似，不看见全部隐式参数或模块别名；不代替类型检查和
导入闭包，更不代替值验收。五件数学模块全文 995 行，报告入口另计。
全部新文件代码无公设、洞、函数外延、跳过停机／正性／宇宙检查的指示、
信任相等、with-K 或真正的 cubical 选项；无本机绝对路径与尾随空白。
Raw 附录配方已用拦截写入的方式重生成，所得字节与交付文件完全相同。

开发时 Check 有两轮退出 42：一次是 without-K 下直接匹配两个极限函数
端点的 Reach 索引导致 UnificationStuck，改用沿路径遗传的 NoFlat 谓词；
另一次是 LF／ℕ 重载的零、后继在一个相等类型中没有写类型，显式指定 LF
后解决。这两轮都不是正性／归纳—递归拒绝，没有用于 HTML 或切片。
骨架第一次编译即退出 0；正式六件冷编均为 0，无 251／124。

复现从仓库根，库文件含 stdlib 与 cubical 的有效库路径；逐件换入表中模块名：

```sh
agda --library-file=<libraries> -i src -i probes probes/OCF/Align/YiIntr.lagda.md +RTS -M6G -RTS
python3 probes/Survey/scripts/importclosure.py OCF.Align.YiIntrCore OCF.Align.YiIntrRaw OCF.Align.YiIntrFinite OCF.Align.YiIntrCheck --only OCF.Align.YiIntr --only OCF.BTBO
python3 probes/Survey/scripts/importclosure.py OCF.Align.YiIntrPosition OCF.Align.YiIntr --only OCF.Align.Yi --only OCF.Align.RR4RegOmega2 --only OCF.Align.RR4CoordRoot --only OCF.Align.LevelFix --only OCF.Free.Level --only OCF.BTBO
```

## 6 翻译账与停点

新增 Lgl／Nested 来自冻结 Carry⁺ 的树侧起点需求，p 来自 Reg 的位置需求；
没有按 EBO 阶段增加字段。Raw 的 em／top、Ω 四行与有限归纳仍继承
LevelFix／K1 的既有配方，不宣称已摆脱其历史启发。
位置改写与守卫缩域是本候选的主动选择，已经明列原域的损失及新闭项的
irr 反例。没有借第 4 层验收反改前三层；第 4 层逼出：无。
下一步若继续，先处理本次具体一致性义务，不能直接把有限构造扩成全塔。
这是一项范围判断，不是对其它顺序或方案的穷尽／不可能性结论。

本轮没有改旧树、合法性、Carry⁺、README、LOG、src 或 archive，
没有安装包、提交或推送；工作区原有改动保留。

## 附：Raw 平行证明的字节重生成

以下 Python 从仓库根运行，只写本轮 YiIntrRaw；全文与交付文件逐字相同。
这不是生成整个 YiIntr 族的脚本：Core、Finite、Check、Position 是新写的定义／证明。

```python
from pathlib import Path
src = Path('probes/OCF/Align/LevelFixCore.lagda.md').read_text()
section = src.split('## §3 同层的第一位置: 传递, 比较\n', 1)[1]
code = section.split('```agda\n', 1)[1].split('```', 1)[0]
code = code.replace('lc k c t g', 'lc k c w₀ b₀ t p₀ g')
header = '''# YiIntr：骨架上的 Raw 位置运算

本篇只平行有限构造需要的第一位置传递、合法性回传与有公共界比较。
证明来源是 LevelFixCore 第 3 节；所有新 lc 模式增加三个证据参数，
没有把坐标证据当作可判等对象。字节重生成配方见 YiIntr。

@AGDA_FENCE@
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIntrRaw where

open import OCF.Align.YiIntrCore
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

'''
header = header.replace('@AGDA_FENCE@', '`' * 3 + 'agda')
Path('probes/OCF/Align/YiIntrRaw.lagda.md').write_text(header + code + '```\n')
```
