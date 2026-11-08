# 输出更新整底世界后的完整闭项

**已交无参数闭项、合法性和 FGH；未验收到 EBO。** 此处不再由外界
给未来世界：每个槽以其自身树类型为底，运行完整原高源，输出更新该槽，
全槽共同组成原 Sb 的底世界。更新后再次读实际界运行，所有底的路径族
重新实填，逐底下降到可数树，最后用原第一位置合法的累计极限封口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDriven where

open import OCF.Lean.OutputDrivenClosed public
  using (closed; legal-closed; fgh)
open import OCF.Lean.OutputDrivenGrid public
  using (closedGrid; legal-closedGrid; fghGrid; cell-in-closed)
import OCF.Lean.OutputDrivenValue
```

## 真实运行链

1. [Whole](OutputDrivenBuild.lagda.md) 把 `V=Tw(Sb n)m` 作为底，
   源是完整 `hΩ ιK(gtX V fb)`。比较高度在 V 内取合法 1，目标零，
   因而无需猜测原 raw m 合法，也不把一个有界目标运行补成全目标族。
2. [World](OutputDrivenWorld.lagda.md) 每槽取这个原 ΦX 的真实输出，
   经已有富合法化累加到当前界；[Top](OutputDrivenTop.lagda.md) 读取
   当前世界的实际界。所有槽及指标一起形成真正的 `Wd(Sb(suc n))`。
3. [Family](OutputDrivenFamily.lagda.md) 递归产生全部底的合法世界。
   上轮最终 Cd 输出进入最低非平凡底的指标界；高槽由整源运行输出生成。
4. [Down](OutputDrivenDown.lagda.md) 在这些实际世界重新建立完整 QL/PH
   证书，运行全部逐底下降；不偷搬旧证书，不在下降源中插入正规化。
5. [Closed](OutputDrivenClosed.lagda.md) 同时增加底深度和更新轮数。
   [Grid](OutputDrivenGrid.lagda.md) 进一步在每阶段运行全部有限二参数
   方格，同格使用同一上轮 Cd 种子，不要求两参数或种子的值单调。

Grid 的每格包含定理保留真实种子；它只证明某阶段各格的完整输出进入
最终树，不从公平枚举推出固定种子下的全域支配或 EBO 覆盖。

## 肉眼评估的内容与边界

这次可直接看见：所有类型层的塔槽均由实际高源输出更新，更新后的界
被实际读取，完整下降后的结果又进入下一外阶段。旧程序的组件零槽
不再作为所有轮固定的默认环境。

但是原 `Er` 仍会删除穿过 Ω 高度分量的坐标节点，跨底折叠也仍只在
一个当前代表坐标取某类分支。代表从固定零改为实际界，并不自动保留
全部分支信息。`State.index` 不被同层槽运行直接读取；其逐轮累加本身
不能冒充高反馈，真实动态在非零塔槽和后续完整下降的界读取处。

所以这是可运行、可估值的新构造，不应仅按“任意底 × 任意轮数”就
读作 ψ₀Λ。能否达到 EBO 的实质检查在整源回灌是否覆盖完整 Ω 塔；
最终序数值及完整前三层成本、内部 View 的验收还需分别完成。

## 翻译账

没有新树节点，没有记号导入。将 raw m 用作结构参数选择 V 是为了
取得同类型可执行输出；全槽世界操作不判下标成员关系、不要求界外补零。
下降继承 Third 的泛 Q 结构，未改旧定义。源与底族本身仍继承历史中受
记号启发的组织，不因干净导入而宣称已经树自足。新增运行、证书和世界
操作都须计入成品成本，不能只数本入口或最后的对角定义。

## 当前成本校准

成功编译的 HTML 上，[切片脚本](../../Survey/scripts/outputdriven/locslice_outputdriven.py)
按原 Third 的口径计本地非空非注释代码，补原参数化折叠／路径根，并对
本地模块别名补根到不动点：同步对角闭项连合法性与 FGH 为 **1148**，
全方格闭项为 **1160**。标准库按既有口径不计。两者均未计尚待验收的
内部 View；脚本仍有语法切片局限，故不是已经满足 1513 的成品认证。
