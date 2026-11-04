# 树能不能自己说 "现有操作走到头, 必须加新东西"

> **判决: 目前不能. 分四句, 档次不同.**
>
> 1. **相对封顶是定理.** 树侧定义了闭包点 `Cl`, 它有实例 (`closed-self`), 有最小性 (`closed-min`). 世界内的类从闭包点下面到不了它 (`rel-cap`). 这些不看记号, 不按阶段, 对一切读法算子成立.
> 2. **绝对封顶是空的, 也是定理.** 带外部输入时, 一切 `HS` 树都落在某个闭包点之下 (`cofinal`), 闭包点没有最后一个 (`no-stop`), 带绑定读法的 `T₁` 喂给世界的行也被越过 (`T₁-below-F`). 任意 ℕ-极限进类, 类就是全体 (`gen-all`). 可数类有上界本身不说明任何事 (`diag`). **所以 "值超过世界内的一切" 这句话, 不限定输入时是假的: 只看值, 世界内的操作永远不必加新东西.** 这只否定写明的判据形状, 不否定绑定有用.
> 3. **去掉外部输入的类, 上界有了, 分辨力没有证出来.** `Cap` 是不带外部输入的类的闭项上界 (`word<`, `F-closed`, `N-closed`). 判据要有分辨力, 要 `Target` (`Cap` 从 `T₀` 起 $\preceq$ `T₁`). **未走通:** 没有证明, 也没有否定.
> 4. **答案.** 树现在能说 "不把 $\beta$ 喂进来, 这些操作到不了 $\beta$". 它不能说 "必须加新原语", 因为喂进来就过了, 而 "喂进来" 和 "新原语" 的值的差别还要靠 `Target`. "必须" 这个词目前只有记号的序支持 (`lt₄`, 事后对照), 和两条类型报错 (`TLOne`), 后者只说写不进现有数据树.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

## 时间线

1. 上一轮 (`TLOne`) 已读: `CrossMAccept`, `CrossNextAccept`, `EBO` 的 `fs-1`, `fs-2`, `lt-b`. **这一轮的类不是盲的:** 两个算子 `F`, `N` 是那一轮判断的上界论证里用过的.
2. 这一轮写 `TLEndCap`, `TLEndNeg`, `TLEndWord`, `TLEndTop` 时没有打开记号文件. 读了 `WorldTH`, `WorldTHInst`, `WorldTHGrow` 开头, `WorldTHLe` 的 `⊴`, `EmbVVMain`, `EmbVV` 的陈述 (这些文件的正文会提到读法).
3. 最后写 `TLEndAccept`.

## 定理 (编译过)

| 定理 | 陈述 | 文件 |
| --- | --- | --- |
| `AB.cap`, `At.cap` | 类 `𝓦` (一条 `⊂`-链的世界的第 0 行, 被读的行, 对后继和下方封闭): `suc x ≼ lvβ` | [TLEndCap](TLEndCap.lagda.md) |
| `lub`, `lim-closed`, `cof`, `dn` | 最小上界; 下面对后继封闭; 下面的都被世界的值盖住 | 同上 |
| `Cl`, `closed-self` | 闭包点的定义; `lvβ` 对链上的世界是闭包点 | 同上 |
| `closed-min`, `rel-cap` | 对任何闭包点 $\beta'$: `lvβ ≼ β′`, 类封顶 | 同上 |
| `no-worldᵇ`, `⊂-linear` | 没有码含整条链; 有向族都是链 | 同上 |
| `mono→row` | **条件于 `Mono`:** `lvβ` 对一切世界的第 0 行封闭 | 同上 |
| `gen-all` | 0, 后继, 任意 ℕ-极限生成全部 `Ordᴵ` | [TLEndNeg](TLEndNeg.lagda.md) |
| `cofinal`, `no-stop` | 一切 `HS` 树低于某个闭包点; 闭包点没有最后一个 | 同上 |
| `Diag.diag` | 任何可数带证书族有带证书的严格上界 | 同上 |
| `Top.word<`, `cap≺`, `F-closed`, `N-closed`, `esc` | 不带外部输入的类: 上界, 对算子封闭, 喂自己就逃逸 | [TLEndWord](TLEndWord.lagda.md) |
| `T₁-below-F`, `T₁-below-Cap`, `T₀<T₁ᵛ` | 正对照的编译部分 | [TLEndTop](TLEndTop.lagda.md) |
| `lt₀` 到 `lt₄` | **只关于记号** | [TLEndAccept](TLEndAccept.lagda.md) |

**否定的范围.** `gen-all`, `cofinal`, `no-stop`, `diag`, `T₁-below-F` 都是无假设的构造, 不存在前提是否可满足的问题. 它们否定的是这几个判据形状: 类含任意 ℕ-极限; 类含任意外部输入; "可数类有上界" 本身. 不否定 `rel-cap`, 不否定 `Target`, 不否定绑定路线.

**三个缺口, 都是未走通, 不是否定.**

- `Cl (λ _ → ⊤) β′` (对**一切**世界封闭) 有没有实例, 没有定理. `closed-self` 只对链上的世界. 第一条子句的障碍是 `Mono`, 第三条子句还要 `val (next M)` 的算术. `closed-min` 对 $W=\top$ 成立, 但它的前提现在可能是空的, 所以这种情形只算条件定理.
- `Mono` (码的值 $\preceq$ 推第 0 行 $\preceq$). 没有证明, 没有否定. 需要非初始段的码嵌入下折叠单调; `up-sim` 只管初始段, `V-≃` 只管去头.
- `Target`. 见下.

## 正对照: 差什么

要证 `Target`, 至少要下面两件 (判断).

1. **跨族.** `F`, `N` 在 `CrossM` 一族, `T₀`, `T₁` 在 `CumUp` 一族. `WorldTH` 已写 `T⊤ ≺ T₁` 未走通, 估计与 `CumUpAcceptSim` 同量级. 或者把 `F`, `N` 在 `WorldTH` 里重写: 行 `Tψ (ht v) azero`, 下标 `next`.
2. **右加单调.** $\psi_0(\Omega_u+\Omega_{\Omega\cdot v})\succeq\psi_0(\Omega_{\Omega\cdot v})$, 也就是折叠对 "左边加一项" 的值单调. `WorldTHLe` 的 `⊴` 只管第一位置, `T-strict` 只走了 $\Omega_u+1$, `WorldTH` 自己说 "这不说 $T_1$ 超过 $T_0$ 的任何固定运算". 没有这一条, `T₁` 的第 1 项 $\psi_0(\psi_u(\Omega_u))$ 里的 $\psi_0(\Omega_u+\Omega_u)$ 与世界的行之间没有比较.

已经编译的只有 `T₀ ≺ T₁`: 第 0 行的闭包点被 `T₁` 越过. 但 `no-stop` 说回灌同样越过闭包点, 所以这一条**没有分辨力**.

## 判断

- `Target` 成立. 依据只有上一轮的纸面嵌入和记号的序 (`lt₂`, `lt₃`, `lt₄`), 树与记号之间没有定理.
- 真正的判据应该不是值的上界, 而是问 "这个对象在折叠下怎么行动": 常数在折叠下只有算术, 世界的行的 Ω-节点高度有界, `tH` 的高度无界. 这可以写成谓词, 但我写出来的版本等于 "有没有绑定", 是循环的, 所以没有编译.

## 翻译账

这一轮没有新增数据树字段, 也没有新的 `Goodᴺ` 规则.

| 东西 | 来源 |
| --- | --- |
| `AB`, `Cl`, `𝓦`, `rel-cap`, `closed-min` | 树逼的 (`⊂`, `val`, 回灌) |
| 第一步读行, 第二步接第 0 行 (`next`) | 我的选择, 让 `req≼` 和 `ly≼val` 同时成立 |
| `F`, `N`, `run`, `Cap` | 现成算子; 选这两个受上一轮判断影响 (时间线第 1 条) |
| `Target` | 由树的语言陈述, 想到要它是因为记号的序 |

**这不算树自足.** 进展: 相对封顶和闭包点的定义不看记号, 不按阶段. 缺口: 见判决第 4 句.

## 工程上的坑

这几条都不是否定, 只是写法. 下面的 "原因" 都是根据现象判断, 没有查 Agda 的实现.

1. 闭合或带 `cs` 头的世界上比较 `lvG`, `forceᴺ` 的不同写法要化简证书 (`CrossMInst` 已写). 第一版 `TLEndCap`, 以及 `TLEndWord` 还写在具体算子上时编译 `TLEndTop`, 都在 10G 堆内退出码 251. 办法: 定理写在抽象的 `G` 上, 用模块实例化代入.
2. `data` 的构造子类型含 `lvG (Gᵖ …)` 时, 单是声明就过不了 (6G, 50 秒内没结果), 写成指标或等式字段都一样; 改成 `Σ` 的普通定义就好. 判断是正性分析在范式化.
3. 对这种项用 `with` 也一样, 改用 `proj₁`, `proj₂`.

## 壁垒

没有新的下标类型. 比较都在一个世界或字面前缀里. `Cl` 里的 `≼` 是陈述用的序, 不作判定. `barrier`, `no-tri-code` 的前提都不被要求.

## 审计

记号只在 [TLEndAccept](TLEndAccept.lagda.md), 入口不导入它.

- **导入闭包:** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf --only OCF.Align.LadderOrd --only OCF.Align.CrossM --only OCF.Align.CrossNext --only OCF.Align.CumRead --only OCF.Align.LevelFix --only OCF.Align.WorldTH --only OCF.Align.TLEnd OCF.Align.TLEnd`: 退出码 0, 禁用表 0, `--only` 之外 0, 72 个本地模块. 正对照 `OCF.Align.TLEndAccept`: 命中 `EBO`, 退出码 1.
- **定义级切片 `depslice.py` (块数, 记号块, 词命中):** `closed-min` 1237, 0, 0; `rel-cap` 1243, 0, 0; `closed-self` 1242, 0, 0; `above` 1140, 0, 0; `cofinal` 1144, 0, 0; `gen-all` 8, 0, 0; `word<` 1248, 0, 0; `T₁-below-F` 1536, 0, 0; `Capᵀ` 1234, 0, 0. 正对照 `TLEndAccept:lt₄`: 53, 43, 2. 切片看不见模块别名的实参, 以闭包为准.
- **禁用构造:** 全部 `TLEnd*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `--cubical`; 全部带 `--safe --without-K`.
- 闭包只保证不引用, 不说明没受记号启发: 见时间线第 1 条.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLEnd where

open import OCF.Align.TLEndCap using (module AB; module Req; ⊂-linear)
open import OCF.Align.TLEndNeg using (gen-all; cofinal; no-stop; module Diag)
open import OCF.Align.TLEndWord using (module Ops; module Top)
open import OCF.Align.TLEndTop using (T₁-below-F; T₁-below-Cap; T₀<T₁ᵛ; Target; Capᵀ; fghCap)
```
