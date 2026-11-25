# 处处严格检验：(b) 规范 Ω 闭包在第3步失败

**交付 (b)，停在第3步。** 新 Legalˢˢ 排除了上一轮常1 Ω 分支的源，
且 Ω̂1 仍满足它；但输入2合法，规范 Ω̂2 却不满足它。
既有塔第3项及 Λ 也有直接否定。按“若规范构造不满足，立即报告，这一版作废”
停止本版检验，不进入 ψ 归纳步，不再补 Raw 或正则性形状。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglAllReport where

import OCF.Align.YiLglAllBase
import OCF.Align.YiLglAllStop
```

## 定义与第2步

[YiLglAllBase](YiLglAllBase.lagda.md) 严格按本轮指定形状在现有平行 LF 上定义：

```text
Legalˢˢ 0 = ⊤
Legalˢˢ (suc x) = Legalˢˢ x
Legalˢˢ (lim f) = (∀n Properˢ(f n,f(n+1))) × (∀n Legalˢˢ(f n))
Legalˢˢ (lc k c t g) =
  Legalˢˢ k × (∀ηe CP(t,gηe)) ×
  (∀ηeη′e′ Dn k η η′ → Properˢ(gηe,gη′e′)) ×
  (∀ηee′ gηe=gηe′) × Legalˢˢ t × (∀ηe Legalˢˢ(gηe))
```

坐标相等时只沿用守卫无关性；weaken-branch 对相等与 Dn 两行给原弱单调性，
forget 对全部 LF 给 Legalˢˢ→Legalˢ，没有识别两份证据或使用 UIP。
第一支弱 CP 与下界等号不变。Raw／Lgl／Gd 也均不变。
no-old-source 用同一合法严格坐标对排除上一轮 source；第2步已完成。
nat-legal 对所有自然数，omega-one-legal 给 Ω̂1，所有正面前提均非空。

## 第3步的规范反例

[YiLglAllStop](YiLglAllStop.lagda.md) 给以下原合法坐标，代码里的 eta 是下式：

```text
One = 1
OmegaOne = Ω̂1
eta : Raw One
eta = raw-lc (首个 Ω 槽) raw1 top (λ _ _ → suc top)
Lgl One eta
Gd One (cO One) eta
up One eta = lc 0 raw1 OmegaOne (λ _ _ → suc OmegaOne) = bad
```

eta-lawful 逐字段实填 Raw 合法性；eta-above-top 给 top 到 eta 的 Dn 真路径，
故 eta-guard 不用下界等号。eta-first-step 给 Raw 第一支 top 到 suc top 的真路径。
eta-read 是 refl；读回结点 bad 的第一支到分支也有 Properˢ，见 bad-first-strict。
因此即使这些第一支关系都严格，这个反例仍成立。

在 bad 的低层域取 raw2、raw3：

```text
Dn 0 raw1 raw2
Dn 0 raw1 raw3
Dn 0 raw2 raw3
```

两坐标都严格高于守卫下界 raw1，guard 也已实填。
若 Legalˢˢ bad，新增 Ω 单调性就给
Properˢ(suc OmegaOne,suc OmegaOne)。
no-proper-suc-omega-one 排除此路径：目标后继只能进入 OmegaOne，
随后沿其第一支1下降；有限位置向下闭包会使 suc OmegaOne 有限，与它的 Ω 子树冲突。
这里不比较两个宽位置，也不比较两个极限函数。

因此正式否定为：

```text
no-bad : Legalˢˢ bad → ⊥
no-omega-two : Legalˢˢ (Ω̂2) → ⊥
no-omega-preservation : (∀x Legalˢˢ x → Legalˢˢ(Ω̂x)) → ⊥
```

two-legal 实填输入2的 Legalˢˢ；Ω̂2 的原分支必须对 eta 有定义，
其全部分支合法性就在 eta 上要求 Legalˢˢ bad，故不能填。
这不是在空的规范闭包前提下推矛盾，亦不只是某次证明尝试失败。

### 塔与 Λ 的直接推论

tower3-form 为 refl：tw 3 就是 Ω̂(OmegaOne)。其根的合法 raw2 分支
按规范 Ω 算法化简为 Ω̂2，tower3-raw2 也是 refl。
no-tower3 直接调用 no-omega-two；no-all-towers 取第3项，no-Lambda 从 Λ 的逐支合法性取第3项。
没有把 Raw(OmegaOne) 中的另一个槽位冒称为塔第3项自己的根分支。

这些都是同一反例的直接推论，不是止损后继续展开 ψ 或逐层修补。

## 哪一处弱关系造成失败

残留字段在 [YiLglCore](YiLglCore.lagda.md) 第141至145行：

```text
Lgl y (G.lc r c t g) =
  (∀ηe Cp y t (gηe)) ×
  (∀ηeη′e′ GdL y r η η′ → Cp y (gηe) (gη′e′)) × ...
```

Raw Ω 分支的单调仍用 Cp，eta 的常 suc top 分支以 Cp 自反通过。
本轮加强的是块外 LF 的 Legalˢˢ，未改变这项块内 Lgl；
规范 Ω₂ 的原分支域因而仍包含 eta，读回后被新的 Properˢ 单调性拒绝。

**不是本轮特意保留的那两处弱关系造成的停顿：**
所选 Raw／LF 第一支到分支都有真路径，内外所用守卫也都有真路径，
两个被比较的内坐标均严格高于下界。失败明确落在 Raw lc 的弱分支单调性。
把它也改严格将再改变 Gd／Raw／LF 的归纳递归块；本轮没有作这项追加修补。

## 止损、ψ 状态与 D8 交接

执行第3条的立即作废条件后，第4条各行没有开始。
已有 Legalˢ 上的条件定理不被冒称为 Legalˢˢ 上的证明；
本轮既没证明“Legalˢˢ 源经 ψ 停顿”，也没证明“γ 的增长只能靠判定”。
γ 严格的状态是未查，停点比它更早：规范种子／层号闭包尚不能实填。

本版 D7 检验到此结束，不再补形状。为 D8 保留的已证事实是：
历史弱 Raw 曾允许常 ℕ 列；当前平行 Raw 已排除该列，却仍允许本轮的常 Ω 分支。
本轮已证后一种来源进入规范 Ω、既有塔与 Λ 的全合法分支域。
D8 若处理这些坐标，必须覆盖这项当前来源；本轮没有实施 D8 或证明其可行性。
此为本轮作者指定候选的规范闭包否定，不是所有严格 Raw 方案的数学否定。

所用坐标没有 EBO Reach 选择证书，不称实际记号基本列或实际 ψ／γ 输出反例。
反例本身是规范树的全合法分支义务，不需要实际列选中该坐标。
未用 UIP／Funext、裸下标律、高层固定类型回收或宽位置三歧；
没有实例化 Barrier.barrier 或 BrwViewNeg.strict→LPO。

## 翻译账与验证

新的 Dn→Properˢ 字段由上一轮 no-rule-preservation 的常 Ω 分支反例逼出，
只用树的路径语言；规则形状仍以 JiaExactFold（照 EBO 规则）的模板为背景。
本轮尚未应用那些 ψ 规则，不将新增字段称为已证明足够，也不为验收方便改变 Raw。

Base／Stop／Report 三件新模块逐件删除自己的字面接口，单6G冷编；
配对否定由主路读全文、核对陈述及输入实例后重新编译复核。
本轮按“不改已有文件”的约束，不更新 README／LOG；翻译账和验证记录集中在本篇。
已有数学文件未改，未迁移20模块或新增 ψ／γ／FGH／值下界；P1仍 x=Ω·ω²。

正式从仓库根逐件编译：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiLglAllReport.lagda.md +RTS -M6G -RTS
```

- Base／Stop／Report 三件逐件删各自字面接口，均有 Checking，单6G退出0；无堆耗尽或超时。
- safe／without-K 齐全，禁用构造／洞／UIP／Funext 前提命中0，无绝对路径／尾随空白。
- 源码导入闭包本地9／10／11件，库叶各15，importclosure均退出0，记号／C线命中0。
- 三件及 EboLean3Lab 正对照成功生成 HTML／编译器图，均单6G退出0；编译器本地集合与源码逐一相同。
- 定义切片 Legalˢˢ25、forget29、no-old-source41、omega-one-legal41、no-omega-two50、no-tower3 52、no-Lambda55块，记号模块／其它记号词命中均0；正对照 ebo-lab″352／33／36。
- 切片是语法近似，不作值或完整成品认证；本轮没有失败编译或将错误码用作否定依据。
- 三件文章的名字／导航检查0问题，3个本地链接逐个存在，git diff --check退出0。

配对路的 Stop 首编退出0；主路读全文后已删接口冷复核。
配对路另只读 Base／Report，核对了同坐标运输、first／guard 的严格隔离、
塔第3项的真实根分支与第3条停点。报告据此明确区分历史常 ℕ 列和当前常 Ω 分支。
没有提交或推送；仅新增本轮三件 YiLglAll* 源文件。
