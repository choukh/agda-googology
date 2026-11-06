# 链从 0 起: 审查 D2 (回灌不读界)

> 入口. 审查 [ClosedTermReview](../../Survey/ClosedTermReview.md) 的 D2: BTBO 的链从 0 起 ($\gamma_0=0$, $\gamma_{k+1}=\psi_q(f\,\gamma_k)$), 不读界; 把它搬到树侧, 只改折叠的回灌格: $x_0=\mathrm{bot}$, $x_{n+1}=x_n\boxplus\mathrm{rd}(\Delta_n)$, 世界操作只剩 "让 $x_{n+1}$ 有界", 由只增长的世界给出; 命题 W′ 的 "忠实相等" 弱化成 "有界". 本篇按审查的四步做.
>
> **判决: D2 在 `κ₂` 处撞到一条编译过的否定 (前提可满足, 范围写明); `LevelFold towerL′` 与无条件的 `Top.Tᴰ towerL′` 没有写出, ψ₀Λ 的候选闭项在这条路上未走通.** 不否定 D1, 不否定以 `HB S₁` 为增量的一致搬运 (`DiagK4` 的 $\mathrm{tr}$).
>
> 1. **第一步 (定理 + 测试).** 在 `HtTowerF` 这一站 (层 `HB S₁`, 世界成对) 写了链不读界的折叠 `ChainZFold`: 链的值 $x_n$ 从不引用世界的界 $\beta$, 格的世界是 $(a,\beta\boxplus x_n)$ (只增长, 一个分量). 闭项合法 (`Lg-Zs-Ω₂²`), 有 FGH. 但**字面的 $x_0=\mathrm{bot}$ 停在底** (`ChainZStall.stall`, 定理): 节点在当前高度界下造的时候, 第 0 格到节点的路是空的, 增量是差树, 路空则增量空, 链每一格都是 `hz`, 闭包每一格都输出空树 (`stall-out`). 种子改取状态里的输出 ($x_0=\mathrm{rd}(\mathrm{hz},z_1)$, 仍不读界) 就不停: 闭项与原折叠在深度 18 内相同 (测试).
> 2. **第二步 (否定定理).** 第 1 级 `κ₂` (坐标 `HB S₁`): 由 `dW 1` 经任意多次 `growL′` 得到的世界里, **含新种类节点的格 $y\boxplus\delta$ 从不有界** (`ChainZNeg.no-chain`, 对一切 $y$ 与一切含新节点的 $\delta$; 前提可满足 `sat`). 原因只有一行: 有界是字面第一位置, 第一位置是子项, 子项继承 "无新节点" (`noNew⊲`), 而 `growL′` 给 `κ₂` 的界只接 `up h` (`reach-noNew`). 所以 "有界" 与 "等于" 对新节点携带同样的信息, W′ 的弱化不扩大能到达的坐标; 只增长的世界在 `κ₂` 处的损失就是 `DiagK3One.noNew-emb`, D2 没有绕开它. 另有一条对一切 `S` 的定理 `dich`: 比某个旧世界大的合法世界里, 有界的格与旧界字面可比; 所以不读界的格要爬过旧界, 就必须字面含旧界 (`no-world`: 字面不可比的 $\omega'$ 没有世界). 正对照: 无新节点的格有界 (`pos-κ₂`), 读界的格有界 (`pos-ctl`).
> 3. **第三步 (没有做).** 每级的折叠要在 `κ₂` 处让含新节点的格有界; 只增长的世界给不了 (第二步), 恰好改一个分量要弱判定 (`DiagKLev.updL′→wdec`). 剩下的是以 `HB S₁` 为增量、对一切分量一致的搬运, 即 `DiagK4` 的 $\mathrm{tr}$ (底分支倒译不合法 `¬Lg-Tr₀`, 常值倒译有损 `Lg-const`, 一般情形无定理). 本路没有重复 `DiagK4`, 也没有写 D1 (另一路 `TelW`).
> 4. **第四步 (判断).** 读法: `Zs-Ω₂²` 与 `HtTowerFClosed.T-Ω₂²` 测试上相同, 同读 $\psi_0(\Omega_{\Omega_2^2})$ (判断). 链从 0 起的代价: 字面从底起, 新种类闭包无输出, 闭项沿前两项深度只有 4 (测试), 读法跌到不用新种类的那一档 (判断); 种子取输出则在这一站不损失也不增益, 只是同一条链的重新结合 ($\beta\boxplus\mathrm{rd}(\mathrm{hz},\cdot)$ 对 $\mathrm{rd}(\beta,\cdot)$; 判断, 有测试). 与主线 `HtFeedFold` 比: 第 0 层的回灌没有动, 不受影响. `HtFeedGrow.Sup` 那一档的增长越过 `noNew-emb` 的证据: **没有**, 因为没有越过.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. 定义不读记号, 没有打开 `EBO`, `Lab`, 标签. 没有改任何已有文件.

## 文件

| 文件 | 内容 |
|---|---|
| [ChainZFold](ChainZFold.lagda.md) | 链不读界的折叠 (`HtTowerFFold` 的互递归块, 只换 `κc₁`; 种子是模块参数 `sd`) |
| [ChainZClosed](ChainZClosed.lagda.md) | 两种种子 `bot₀`, `out₀`; 闭项 `Z-…`, `Zs-…`; 合法; FGH |
| [ChainZStall](ChainZStall.lagda.md) | 字面 $x_0=\mathrm{bot}$ 的链停在底 |
| [ChainZNeg](ChainZNeg.lagda.md) | `dich`, `no-world`; `κ₂` 处 `no-chain` |
| [ChainZTest](ChainZTest.lagda.md) | 有限测试 |

## 定理表

| 名字 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `ClZ`, `toCl`, `κc₁` (新子句), `Run` 一族 | ChainZFold | 链不读界的折叠; 第 $n$ 格的界 $\beta\boxplus x_n$ | 定义 (停机检查通过) |
| `TΛ`, `T⁺`, `Z-Ω₂` … `Zs-Ω₂²` | ChainZClosed | 闭项 | 定义 |
| `Lg-Z-Ω₂²`, `Lg-Zs-Ω₂²`, `Lg-T⁺` | ChainZClosed | 合法 (由形状, `Lg-sum`) | 定理 |
| `fgh` | ChainZClosed | `Zs-Ω₂²` 上的 FGH | 定义 |
| **`stall`**, `stall-out` | ChainZStall | 种子 `bot₀`, 节点在当前高度界下: 链每格是 `hz`, 每格输出空树 | 定理; 前提可满足 (`sat-stall`) |
| **`dich`** | ChainZNeg | 一切 `S`: 合法的更大世界里有界的格与旧界字面可比 | 定理 |
| `no-world` | ChainZNeg | 世界 $(0,\omega)$ 之上没有让 $\omega'$ 有界的合法世界 | 定理 (否定); 前提可满足 (`lW₀`, `lω′`); 正对照 `pos-ctl` |
| `noNew⊲`, `noNew-⊞r` | ChainZNeg | 第一位置继承无新节点; 和的右边含新节点则和含新节点 | 定理 |
| `Reach`, `reach-noNew`, `reach-lg` | ChainZNeg | `dW 1` 经 `growL′` 生成的世界合法, `κ₂` 界无新节点 | 定理 |
| **`no-chain`**, `no-cell`, `no-Ω-cell` | ChainZNeg | 这些世界里 `κ₂` 处含新节点的格从不有界 | 定理 (否定); 前提可满足 (`sat`); 正对照 `pos-κ₂` |
| `lift₂`, `grow₂` | ChainZNeg | 同一件事在第 1 级的层 (`L′ 2` 链分量) 上 | 定理 (`refl`) |
| `s-Ω₂`, `s-Ω₂²`, `s9`, `s10`, `z-·2`, `z-²`, `z-dp`, `zs2`, `zs3` | ChainZTest | 见该文件 | 有限测试 |
| "种子取输出与原折叠是同一条链的重新结合" | — | | 判断 (有测试) |
| "字面从底起读法跌到不用新种类的一档" | — | | 判断 |
| "D2 不能到 ψ₀Λ" | — | 只在 `growL′` 生成的世界这一族内是定理 (`no-chain`); 一般搬运开放 | 范围内定理, 范围外未走通 |

## 第一个障碍

`no-chain`. 精确范围: 世界由 `dW 1` 经 `growL′ 1` (任意 $f$, 任意 $h:H_0$) 生成; 格在 `κ₂` 处 (或经 `lift₂` 在第 1 级的层里) 含新种类 $\Omega$-节点. 它不说:

- 世界由别的操作生成时怎样. 只要某个操作把含新节点的东西放进 `κ₂` 的界, `no-chain` 就不适用; 但那个操作要么只动 `κ₂` (选择性, `upd→wdec`), 要么对一切分量一致地搬运 `HB S₁` 的增量 (`DiagK4`).
- D1 (望远镜世界: 种类是位置, 选择性更新是定义).

审查对 D2 的论证 ("对更高坐标类型的分量, 增量只要能嵌入 (`up`/`ι` 忠实), 不要求等于") 漏了一点: 回灌升高的就是 `κ₂` 自己的分量, 它的坐标类型 `HB S₁` 正是增量的类型; `growL′` 给这个分量的是 `up h` ($h:H_0$), 不是 `HB S₁` 的增量. 向上嵌入忠实, 帮的是更高的分量, 帮不到目标分量.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 链从底起, 链的值不引用界 | 作者的 BTBO (`ψ<` 的 `injᵇ` 行, `iter … zero`) | **树侧** (作者自己的树, 不是记号) |
| 格的世界 = 界 $\boxplus$ 链的值 | 有界要字面可比 (`dich`), 没有字面的并 (`no-joinᴮ`) | 树逼的 |
| 种子取状态里的输出 (`out₀`) | 字面从底起停在底 (`stall`) | **树逼的** (差树: 路空则增量空) |
| `ClZ`, `toCl` | 记账: 存链的值, 界算出来 | 重构 |
| 互递归块的复制 (`ChainZFold` §2) | `Run` 与 `RunM` 互递归, 换 `κc₁` 要重写整块 | 工程复制 (由脚本按行抽取; 不是翻译) |
| `dich`, `no-world`, `noNew⊲`, `Reach`, `no-chain` | 划出不能有的世界操作 | 否定形状 (提供信息) |

没有字段读自记号的基本列规则. 按 `AGENTS.md` 归类: **摆脱侧, 提供信息** (不加构造子, 只改回灌; 一条对一切 `S` 的定理 `dich`, 一条带范围的否定 `no-chain`, 一条停机现象的定理 `stall`). 加深翻译的三个标志都没有: 无读自规则的字段; 无闭包定理的专属前提 (合法性只用 `Lg-sum`); 不用 `Lab` 验收.

## 账

**定义级切片** (口径同 `diagk3/locslice_diagk3.py`: 计 agda 非空非注释行, 记号模块除外; 读 `agda --html` 的输出; 本路的脚本在临时目录 `chainz/locslice_chainz.py`, 只换了根).

| 闭项 | 层 1 (类型) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) |
|---|---|---|---|
| `Zs-Ω₂²` (本路, 种子取输出) | 225 (去共用 202) | 1012 (去共用 929) | **1020** (去共用 937) |
| 对照 `HtTowerFClosed.T-Ω₂²` (同一脚本) | 225 (去共用 202) | 988 (去共用 905) | 996 (去共用 913) |

- 都在 1513 之下. 比原折叠多 24 行: 互递归块复制了 (`ChainZFold` 156 行, 其中由脚本抽取的约 135 行), 但 `HtTowerFFold` 被用到的部分从 291 行降到 154 行 (只用它的 §1–§4), 净增来自 `ClZ`, `toCl`, 种子参数与 `ChainZClosed` 的包装.
- 层 3 按模块: HtTowerFTree 264, ChainZFold 156, HtTowerFFold 154, HtTowerTy 147, HtTowerFRead 75, Free.Level 56, HtTowerCont 38, ChainZClosed 37, CumReadCF 36, HtTowerFClosed 30, BTBO 27.
- 独立切片: `no-chain` 309 (ChainZNeg 27, DiagK3Grow 20, DiagK3One 19, 其余是 `HtTowerTy` 等), `dich` 142, `no-world` 223, `stall` 854.
- 这是 `HtTowerF` 这一站的账, 不是 ψ₀Λ 的候选闭项的账 (那个没有写出).
- 文件级代码行 (代码块里非空非注释行): `ChainZFold` 177, `ChainZClosed` 61, `ChainZStall` 56, `ChainZNeg` 115, `ChainZTest` 32, 入口 6; 共 447.

## 审计

- **导入闭包** (`importclosure.py`, `--only` 表: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.CumReadCF`, `TLRuleSpec`, `TLRuleSum`, `SumOne`, `HtGen`, `HtFeed`, `HtOut`, `HtCross`, `SumVar`, `HtTower`, `LFRe`, `DiagK`, `CohW`, `ChainZ`): 六个模块都是退出码 0, 禁用表 0, `--only` 之外 0; 入口闭包 42 个模块 (本地 32).
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `ChainZClosed:fgh` 240/0/0, `ChainZClosed:Lg-Zs-Ω₂²` 226/0/0, `ChainZFold:κc₁` 175/0/0, `ChainZStall:stall` 181/0/0, `ChainZNeg:no-chain` 92/0/0, `ChainZNeg:dich` 44/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用.
- **禁用构造**: 六个文件无 `postulate`, 无洞, 无停机或正性编译指示, 无 `trustMe`, 无函数外延; 都带 `--safe --without-K --lossy-unification`.
- **从头编译** (删去本路的 `.agdai`, 堆上限 6G): 入口退出码 0 (16 秒, 0.6G; 含 `ChainZTest` 的测试).

## 时间线

读过: `AGENTS.md`, 审查全文, `README` 的 HtFeed/HtTowerF/HtTowerN/LFRe/CohW/CohW2/DiagK/DiagK3 各行, 手册 §3–4, `src/OCF/BTBO.lagda.md` (`ψ<`, `ψⁿ`), `HtTowerTy`, `HtTowerFFold` (全文), `HtTowerFTree`, `HtTowerFRead`, `HtTowerFClosed`, `HtTowerFTest`, `HtTowerNStage`, `DiagK3`, `DiagK3Grow`, `DiagK3One`, `DiagKTop`. 没有打开 `EBO`, `Lab`, 标签, 也没有读任何基本列规则. 第一次编译的闭项 (`bot₀`) 在测试里塌成同一棵浅树, 由此找到 `stall`; 种子改取输出后与原折叠一致.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ChainZ where

open import OCF.Align.ChainZClosed using (Seed; bot₀; out₀; module Inst; Z-Ω₂; Z-Ω₂²; Zs-Ω₂; Zs-Ω₂²; Lg-Z-Ω₂²; Lg-Zs-Ω₂²; fgh) public
open import OCF.Align.ChainZNeg using (dich; no-world; pos-ctl; noNew⊲; noNew-⊞r; Reach; reach-noNew; reach-lg; no-cell; no-chain; no-Ω-cell; sat; pos-κ₂; lift₂; grow₂) public
import OCF.Align.ChainZStall
import OCF.Align.ChainZTest
```
