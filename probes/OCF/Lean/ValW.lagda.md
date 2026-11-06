# ValW: 带世界证据的模拟 (入口与判决)

> 不含记号. 作者选定原话: "值定理: 带世界证据的模拟"; 选项说明: "两线共同的缺口: 写一条带 W≤W′ 证据的模拟关系穿过整个折叠, 拿 '回灌提高值' 的第一条定理 (配否定; 注意 strict-cell). 不算攻击也不算摆脱, 是第 4 层". 本路 ValW (构造), 配对否定一路 NegValW, 共用接口 [ValWIf](ValWIf.lagda.md). 第 4 层: 只新增关系与定理, 不改树、折叠、合法性, 不改已有文件. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延 (连前提也没有).
>
> **判决: 关系穿过整个折叠 未走通; "回灌提高值" (`TL ≤ᵥ TF`) 未证, 也未否定.** 已编译的是: 结点决定的两条律 (R1, R2), 两层两世界的关系 `Mx` 与它的第 0 层读法, 回灌那一行的一步定理 (条件), 以及卡点所在情形在 `TL`/`TF` 参数上确实出现.
>
> - **R1 `rk-agree`** (定理, 无前提): 同一结点层、同一目标层、目标世界 $m_1\le m_2$, 两个实例 (级回灌参数任意) 的 "保留/上升" 一致. 此前 `LeanLvVal` §3 卡点 (a) 的担心 (世界变大让结点决定分歧) 在**同层**时不成立.
> - **R2 `rk-cross`** (定理, 无前提): 结点层 $k_1\lhd k_2$ 时 "左上升右保留" 不出现.
> - **`kr-occurs`** (定理, `refl`): "左保留右上升" 在 `TL`/`TF` 的参数上出现 ($k_1=0$, $k_2=1$, $t=1$, 基世界). 否定一路另有一个实例 (`NegValWInst.rk-split`).
> - **`Mx`, `x-sum`** (定理): 两个层 (带 $k_1\lhd k_2$ 证据的结点)、两个世界 (分支在成对的更大世界 $W_1'\le W_2'$ 上比) 的模拟; 第 0 层推出 `sum` 的值序 (接口律 X1).
> - **`Ωd-self`** (条件定理, 条件 `TopMono` 与层合法): $\Omega_t$ 在 $W_1$, $W_2$ 里相关; 闭包分支在两个世界里过的层 $g(\mathrm{top}\,\kappa\,W_1')\lhd g(\mathrm{top}\,\kappa\,W_2')$ 不同, 由 `mi` 的跨层证据接住 (接口律 X2 的同层情形).
> - **`RKa-step`** (条件定理, 前提 `RunH` = 分支的折叠保持关系, 即完整证明里的递归调用): 左边有损的 `ω⋅ c` 被右边回灌的 `nl Δ` **逐格**模拟. 用到的三件事是无前提的定理: 第 $n$ 格的世界在右边当前世界之上 (`cell-≤`), 前缀是 `nw` 套 (`cell-w`), 状态的累计输出右边多出一段 (`cell-Y`). 所以**回灌那一行本身不是卡点**; 卡点在下面.
>
> **卡点 (编译错误原文; "这是唯一的卡点" 是判断, 见 "穷尽").** 回灌把右边的世界升高, $\Omega_L$ 的 $\Omega$-行在世界 $W'$ 里过第 $g(\mathrm{top}\,\kappa\,W')$ 层, 右边走到的层更高, 所以模拟必须**跨层**. 跨层时 `rkT` 可以左保留 (输出结点 `ni`) 右上升 (输出链的极限 `nl`, `kr-occurs`). 关系里没有把 `ni` 与 `nl` 的项连起来的构造子: 在草稿里试 `mlₙ 0 (mi …)` (右边取第 0 项, 再当结点比), Agda 报 (节选, 草稿 `ValWKrTry.agda`, 在会话临时目录里, 仓库外, 退出码 42):
>
>     error: [UnequalTerms]
>     ni _R₂_257 _v₂_261 !=
>     FoldTy.yc
>     (F₂.Run ac′₂ (FoldTy.yc (FoldTy.d Y₂) (OCF.Lean.LeanTFold.tg ≤rf (F₂.kk r₂ q₂ ll₂) lW₂))
>      ≤rf lW₂ (F₂.kk r₂ q₂ ll₂) (F₂.Ai ac₂ ac′₂ r₂ u₂ q₂ (F₂.kk r₂ q₂ ll₂) ll₂ A₂ w₂) … ) Tq₂
>     of type DG₊ (λ W k → StH W k t) (Vs t) (ZK t) m₂
>
> 即: 右边链的第 0 项是在结点层 $k_2$ 上**跑过的**折叠输出 (中性项), 不是结点; 左边是一个尚未跑的结点. 把两者连起来要一条新的律: "第 $t$ 层上的结点 (指向 $k_1$) 被 '在 $k_2\rhd k_1$ 上把状态跑一遍再读到 $t$' 模拟", 并证折叠以后消费它们时保持. 本路没有写这条律 (接手清单 1). 第二个跨层的口子: `rs` (都上升) 时链的第 0 项读状态在目标 $k_1$ 与 $k_2$ 上的输出, 状态关系要跨目标层, 进而 $\Omega_{t_1}$ 对 $\Omega_{t_2}$ ($t_1\lhd t_2$) 要相关, 其中 $t_2$ 是 $\Omega$-结点而 $t_1$ 是后继时一边是结点、一边是闭包 (判断, 没有写尝试).
>
> **对纲领与目标.** 纲领 1: 比较都在布劳威尔树 (`HB S⊥`) 的值序上, 关系是数据之间的模拟. 纲领 2: 无公理, 停机由检查器. 纲领 3: 律都带字面公共上界 (两个世界 $W_1\le W_2$, 成对的更大世界带 $W_1'\le W_2'$, 两个层带 $k_1\lhd k_2$); 没有两个任意世界或任意下标的比较; R1, R2 的证明只用 "上升带证据 $t\lhd k$" 与可达, 不比较两个 `cmpB` 的结果. 纲领 4: 第 4 层, 不进成品. **目标 "让树自足"**: 关系的构造子都读自折叠字面 (见翻译账), 不读记号; 这一站给出的树侧信息是 "回灌提高值" 的证明结构: 回灌行本身是一步定理, 真正的障碍是**层对世界的依赖** ($g(\mathrm{top}\,\kappa\,W)$) 迫使模拟跨层, 跨层时结点的决定会分裂 (`kr`). 这与 `TpMono` 的第一个障碍 (`ChangeHs`, 同一折叠对层单调) 是同一件事: 否定一路的 `Forced.mono` 说明任何 `RunPres` 都推出 "同一折叠对层与世界同时单调".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ValW where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbSt using (SLs; ΛF; lΛF; oneF)
open import OCF.Lean.LeanFbTm using (bkS; fb; TF)
open import OCF.Lean.LeanFbTest using (TL)
open import OCF.Lean.NegLeanLvVal using () renaming (_≤_ to _≤ᵥ_)
import OCF.Lean.ValWRel
import OCF.Lean.ValWRk
import OCF.Lean.ValWRow
open Tree SLs
open import OCF.Lean.ValWIf SLs bkS ΛF lΛF oneF (λ _ → inj₂ tt) fb
module Rk = OCF.Lean.ValWRk SLs bkS ΛF lΛF oneF (λ _ → inj₂ tt) fb
module Row = OCF.Lean.ValWRow SLs bkS ΛF lΛF oneF fb
```

**`kr` 在 `TL`/`TF` 的参数上出现 (定理, `refl`).** 基世界, 目标层 $t=1$: 左结点层 $k_1=0$ 保留 (`ss hself`), 右结点层 $k_2=1$ 上升; $0\lhd1$.

```agda
kr-L : F₁.rkT {k = hz} {t = hs hz} {m = w₀ L₀} (z⊲ᴮ ΛF) oneF (lw₀ L₀) ≡ F₁.keep (ss hself)
kr-L = refl

kr-R : F₂.rkT {k = hs hz} {t = hs hz} {m = w₀ L₀} oneF oneF (lw₀ L₀) ≡ F₂.rise
kr-R = refl

kr-occurs : RkR (F₁.rkT {k = hz} {t = hs hz} {m = w₀ L₀} (z⊲ᴮ ΛF) oneF (lw₀ L₀))
                (F₂.rkT {k = hs hz} {t = hs hz} {m = w₀ L₀} oneF oneF (lw₀ L₀))
kr-occurs = kr

-- 律 R1, R2 在这组参数上 (定理)
R1 : RkAgree
R1 = Rk.rk-agree

R2 : RkCross
R2 = Rk.rk-cross
```

**目标 (未证).** 回灌提高值的第一条: `TL ≤ᵥ TF`. 本路没有它的证明, 也没有否定.

```agda
Goal-TL≤TF : Set
Goal-TL≤TF = TL ≤ᵥ TF
```

## 定理表

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| `RkR`, `RkSame`, `RkAgree`, `RkCross`, `SimW`, `Goals.{DfX, StX, IgX, RunPres, Cross0}` | If | 接口: 律与目标的陈述 | 定义 |
| `Val.rk-valid` | Rk §1 | 一切级回灌参数: `rkT` 上升时带 $t\lhd k$ | 定理 |
| **`rk-agree`** (`R1`) | Rk §2 | 同层, $m_1\le m_2$ ⇒ 两边决定一致 | 定理, 无前提 |
| **`rk-cross`** (`R2`) | Rk §3 | $k_1\lhd k_2$, $m_1\le m_2$ ⇒ `RkR` (无 "左上升右保留") | 定理, 无前提 |
| **`kr-L`, `kr-R`, `kr-occurs`** | 入口 | `TL`/`TF` 参数上左保留右上升 | 定理 (`refl`) |
| `Mx`, `RelA` | Rel §1 | 两层两世界的模拟 | 定义 |
| **`x-sum`**, `x-pt`, `sum≥`, `pt≥`, `⊲→≤` | Rel §2 | 第 0 层: 关系 ⇒ `sum b x ≤ᵥ sum b′ y` (接口律 X1 的形状) | 定理 |
| `topMono-new` | Rel §3 | 新种类的顶沿 $W\le W'$ 是第一位置 (`TopMono` 前提的实例) | 定理 |
| `OmX.gUp`, **`OmX.Ωd-self`** | Rel §3 | 条件 `TopMono`, `LgB t`: $\Omega_t$ 在 $W_1$, $W_2$ 里相关 | 条件定理 |
| `drp-M` | Row §1 | `drp` 保持关系 (两个世界) | 定理 |
| **`Cells.cell-≤`, `cell-w`, `cell-Y`** | Row §3 | 回灌格的世界、前缀、状态 | 定理, 无前提 |
| **`RKa-step`** | Row §4 | 前提 `RunH`: 有损 `RKa` 行被回灌 `RKa` 行逐格模拟 | 条件定理 |
| `Goal-TL≤TF` | 入口 | `TL ≤ᵥ TF` 的陈述 | 目标, 未证 |

## 前提与可满足性

- `TopMono`: 新种类有实例 (`topMono-new`). 对 `SLs` 的一切种类成立是判断 (头的顶由 `rz` 沿 $\boxplus$ 升, `top0`), 本路没有证.
- `RunH`: 是 `RKa-step` 在完整证明里的递归调用. 本路没有证它, 也没有它的否定; 否定一路 `NegValWBlind.no-RunPres` 只说 X1, X2 推不出 X3 (对盲关系 `Bl`), 不说 `Mx` 的 `RunH` 不成立. 所以 `RKa-step` 读作 "回灌行不增加障碍", 不读作 "回灌行保持关系" 的无条件定理.
- `LgB t` (`Ωd-self`): 第一位置于合法最高层的层由 `lgB⊲` 给出.

## 穷尽 (判断)

"卡点只有跨层 (`kr` 与跨目标的状态)" 是判断. 已核对的行: `Run` 的结构行 (`n0`, `n1`, `⨾`, `nl`, `nw`) 与 `ValNewRun.Run-R` 同形; 闭包保留行 `RKk` 与 `mc` 的成对世界同形; 回灌行由 `RKa-step` 给出; 新种类回灌 `κc₁` 判断不出现 (`ΛF = up Λs` 不含新种类 $\Omega$-结点, 判断; 若出现, 否定一路 `NegValWReset.no-cell-≤` 说明只比 `d` 的状态关系不够). 没有逐行写成编译过的 `Run-R`.

## 界与读法 (全部是判断)

| 对象 | 界 | 依据 |
|---|---|---|
| `TL` 对 `TF` | `TL` $\le$ `TF` (判断) | 两者只在 `RKa` 一行不同, 这一行逐格模拟 (`RKa-step`, 条件); 剩下的跨层情形里右边走更高的层. 没有定理 |
| 严格 | 不判断 | `strict-cell` (`NegLeanLvVal`): 即使逐格严格, 和也可以相等; 本路没有算任何一格的值 |
| `TF` 上界 | 沿用 `LeanFb` 的读法 (不超过 $\psi_0(\Omega_3)$ 量级, 判断) | 本路没有重算 |

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `Mx` 的 `m1`, `m⨾`, `ml`, `mw`, `mz`, `mr`, `me` | `ValNewRel.Mo` (已有), 状态 `⊕` 把输出接在右边 | 树逼出 (搬运) |
| `mw′` | 回灌格的前缀是 `nw` 套 (`κcF` 的 `coA`) | 树逼出 |
| `mlₙ` (任一项) | `sum` 对 `nl` 取 `pt` 的上确界 | 树逼出 (第 0 项放宽) |
| `mi` 的跨层证据 $k_1\lhd k_2$ | $\Omega_L$ 的 $\Omega$-行在世界 $W'$ 里过第 $g(\mathrm{top}\,\kappa\,W')$ 层 | 树逼出 |
| `mi`, `mc` 的成对世界 $W_1'\le W_2'$ | 回灌格的世界在右边当前世界之上 (`qA`) | 树逼出 |
| `Valid` (上升带 $t\lhd k$) | `rkT` 的两行 (`cmpB` 的 `inj₁`, `rkS hself`) | 树逼出 |
| `TopMono` | `Ωd` 的 $\Omega$-行取顶 | 树逼出 (前提) |
| `RunH`, `DfM`, `StM`, `IgM` | 第 4 层的验收工具 | 脚手架 (验收), 不进成品 |

归类 (判断): **提供信息**. 没有新构造子或结点字段, 不改树、折叠、合法性, 没有 `Lab`, 没有序数值验收 (只有第 0 层的值序). 新用到的折叠字段: `RKa` 的两行, `κcF` 的 `qA`, `coA`, `SA`, `cv`, `tg↑`, `rkT`/`rkS`, `Ωd` 的 $\Omega$-行. 信息是: 回灌行是一步定理, 障碍在层对世界的依赖迫使的跨层模拟, 其中结点决定的分裂恰好是 `kr` 一种 (R2). 第 4 层没有逼出改前 3 层.

## 文件

| 文件 | 内容 |
|---|---|
| `ValWIf` | 接口 (定稿 2026-11-05 23:43): 律 R1, R2, X1, X2, 目标 X3 (`RunPres`), `Cross0` |
| `ValWRk` | R1 `rk-agree`, R2 `rk-cross` |
| `ValWRel` | `Mx`, `x-sum`, `Ωd-self` (条件) |
| `ValWRow` | 回灌格三件事, `RKa-step` (条件) |
| `ValW` | 入口 (本文件): `kr-occurs`, R1/R2 实例, 目标陈述 |

## 接手清单

1. **`kr` 的律.** 写 "第 $t$ 层的结点 (指向 $k_1$) 被 '在 $k_2\rhd k_1$ 上跑状态再读到 $t$' 的链模拟" 的关系构造子, 并证 `Run` 消费时保持. 先把它加进接口 (只增), 配对否定一路对准 "这样的构造子与 X1 相容但 `Run` 不保持".
2. **跨目标层的状态.** `rs` 情形要 $\Omega_{t_1}$ 对 $\Omega_{t_2}$ ($t_1\lhd t_2$) 相关, 含 "结点对闭包" ($t_1$ 后继, $t_2$ 是 $\Omega$-结点). 这是 `TpMono` 的 `ChangeHs`; 否定一路 `Forced.mono` 是它的边界.
3. **`κc₁` 不出现的不变式.** 把 "最高层不含新种类 $\Omega$-结点 ⇒ 折叠的一切数据不含 `nc (inj₂ _)`" 写成对折叠全程的定理 (仿 `ValNewRel.NI`), 让 "状态只比 `d`" 有依据.
4. **`TopMono` 对 `SLs`.** 逐种类证 (头由 `rz` 升, 其余不动).
5. 1, 2 做完后, `RunH` 由 `RKa-step` 与其余各行拼出, 读到第 0 层得 `TL ≤ᵥ TF`; 严格要另算一格的值并绕开 `strict-cell`.

## 审计 (2026-11-05)

- **从头编译.** 删本路自己的 `.agdai` (逐个写精确路径 `probes/_build/2.8.0.2/agda/OCF/Lean/ValWIf.agdai`, `ValWRk`, `ValWRel`, `ValWRow`, `ValW`), 依赖用共享接口, 从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Lean/ValW.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 4 秒, 峰值常驻约 0.6G.
- **禁用构造.** 五个文件的代码块里 `postulate`, 洞, `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY`, `trustMe`, `Funext`, `REWRITE`, `--with-K` 都是 0; 选项都是 `--safe --without-K --lossy-unification`.
- **导入闭包** (`importclosure.py OCF.Lean.ValW`): 禁用表命中 0, OK. 闭包经 `LeanFbTest` (测试文件, 只为 `TL`) 进来.
- **代码行** (agda 块里非空非注释) / 文件行: `ValWIf` 67/137, `ValWRk` 47/85, `ValWRel` 81/124, `ValWRow` 85/134, 入口 31/约 160; 合计代码 311. 其中关系 (`Mx`, `RelA`) 约 30 行, 定理 (R1, R2, `x-sum`, `Ωd-self`, `drp-M`, 回灌格三件事, `RKa-step`, `kr-occurs`) 约 200 行.
- **生成文件**: 无 (全部手写; 没有建 `probes/Survey/scripts/valw/`).
