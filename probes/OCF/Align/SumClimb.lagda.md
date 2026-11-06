# 和形式, 层取三位: 过 $\psi_0(\Omega_{\Omega^2+1})$, $\psi_0(\Omega_{\Omega^2\cdot2})$, $\psi_0(\Omega_{\Omega^2\cdot\omega})$, $\psi_0(\Omega_{\Omega^3})$

> 入口. **判决: PARTIAL.** 到 $\psi_0(\Omega_{\Omega^3})$ HOLDS: 合法性由形状给出 (`Lg-sum`), 定义里没有 `HS`, `Goodᴺ`, `WF`, `ψW`, 没有证书参数; 每站严格增长是定理. 比上一轮多一类定理: **闭包站严格高于前一族任意可数多个站的上确界** (`SupN`, `SupR`, `Sup3`). $\psi_0(\Omega_{\Omega^\omega})$ 未走通 (见第一个障碍), 没有否定定理.
>
> **这一步是加深翻译:** 层从 $(p,a)$ 加一维成 $(r,p,a)$, 节点种类多一种 `lr`, 都照 $\Omega^2\cdot r+\Omega\cdot p+a$ 的算术写; 再往上每一级还要加一维. 这一模式交给摆脱侧 (`HtGen`, 高度由回灌生成). 第 4 层没有做, 读法都是判断.
>
> 全文 `--safe --without-K --lossy-unification` (工程的 `.agda-lib` 另加 `--cubical-compatible`), 无公设, 无洞, 无停机或正性编译指示, 不开 K, 没有 `next`, `cumA`, ⊞, u+. 定义不读记号, 没有验收文件. 不改已有文件 (从 `SumHtTree` 只导入路径的两条算律与 `NZ` 一类小引理).

## 最小改动

上一轮说 "$\Omega^2+1$ 起要顶层能当目标, 再往上要加维". 实际取的最小改动是**直接加一维**: 只让顶层当目标, 只得到 $\Omega_{\Omega^2+1}$ 一层 (节点 $\sum_{z:\mathrm{top}}1$); $\Omega^2+2$ 起要顶层之上的下标, $\Omega^2+\Omega$ 起要顶层之上的高度, 那就是 $(r,p,a)$. 所以第三位一次加上, 顶层改读 $\Omega^3$.

| 改动 | 文件 | 行数 (定义级切片, 与 `SumHt` 比) |
|---|---|---|
| 节点种类 `KQ`: `sm`, `lo` 照旧, 多 `lr` ($g\lhd r$, $h,k\sqsubseteq W$); 分支类型多一个按 $r$ 递归的 `LowR` | [SumClimbTree](SumClimbTree.lagda.md) | 284 (`SumHtTree` 249) |
| `mkOf` 从 4 种情形到 9 种; `AccY` 多一层递归; `Ωd` 多一段 `DifR` (第一位的一步是闭包 `stepR`) | SumClimbTree | (含在上面) |
| 目标 `Tg W r q t m`; `rkT` 三级字典序 (`rkT` → `rkH` → `rkI`); `nκ` 只在 $(0,0,0)$ 回灌 | [SumClimbFold](SumClimbFold.lagda.md) | 185 (`SumHtFold` 173) |
| 顶层 `KT`: 三位都在世界之下 | SumClimbTree | — |

折叠 `SumClimbFold` 与 `SumHtFold` 逐字相同, 只换了层的位数 (由脚本改写, 见文件头).

## 站

都是顶层在世界 $\omega$ 上的输入的折叠 ([SumClimbClosed](SumClimbClosed.lagda.md)), 积木 `nd r n m`, `B r n`, `BR r`, `κ3`, 闭包都由 `κN` 造出.

    X r n a = 1 ⨾ BR 0 ⨾ … ⨾ BR (r-1) ⨾ B r 0 ⨾ … ⨾ B r (n-1) ⨾ nd r n 0 ⨾ … ⨾ nd r n (a-1)   Ω_{Ω²·r+Ω·n+a}
    XRω r   = 1 ⨾ BR 0 ⨾ … ⨾ BR (r-1) ⨾ nl (B r)                                            Ω_{Ω²·r+Ω·ω}
    Xω      = 1 ⨾ nl BR                                                                       Ω_{Ω²·ω}
    X³      = 1 ⨾ (nl BR ⨾ κ3)                                                                Ω_{Ω³}

另有 `TΩ r p a`: 一切合法 $(r,p,a)$ 的层自己的 $\Omega$ 的折叠.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `T`, `TNω`, `TRω`, `Tω`, `T³`, `TΩ`, `Lg-T`, `Lg-Tω`, `Lg-T³`, `Lg-TΩ`, `fgh` | SumClimbClosed | 闭项, 无参数; 合法性各是 `Lg-sum` 的一次调用 | 定义; 合法性是定理 |
| `L1`, `L1b`, `ptF≡pt` (模块 `P`) | SumClimbGrow | 右结合前缀的折叠是 `nl` 的部分和 | 定理 |
| `L2`, `L3` | SumClimbGrow | 分支为 1 的节点在 $(0,0,0)$ 上非零 | 定理 |
| `W.L4`, `nz-κ` | SumClimbGrow | **任何** `κN` 闭包在满足 `Inv`, `IZ` 的状态上非零 (对 `ρ` 一条) | 定理 |
| `S1` | SumClimbGrow | `asuc (T r n a) ≤ T r n (suc a)` | 定理 |
| `S2`, `S3`, `S4`, `S5`, `S6` | SumClimbGrow | 第二位后继, 第一位后继, 到 `Tω`, `asuc Tω ≤ T³` | 定理 |
| `T≤TNω`, `T≤TRω`, `T≤Tω` | SumClimbGrow | 前一族都在 `nl` 段的极限之下 | 定理 |
| **`SupN r n g`** | SumClimbGrow | $\forall g:\mathbb N\to\mathbb N$: `asuc (sup_k T r n (g k)) ≤ T r (suc n) 0` | 定理 |
| **`SupR r g`** | SumClimbGrow | $\forall g:\mathbb N\to\mathbb N^2$: `asuc (sup_k T r (g k)) ≤ T (suc r) 0 0` | 定理 |
| **`Sup3 g`** | SumClimbGrow | $\forall g:\mathbb N\to\mathbb N^3$: `asuc (sup_k T (g k)) ≤ T³` | 定理 |
| `Ω²<Ω²+1`, `Ω²+1<Ω²·2`, `Ω²·2<Ω²·ω`, `Ω²·ω<Ω³`, `Ω²·2>sup` | SumClimbGrow | 要求的各站 | 定理 |

## 每站严格增长

| 站 (读法是判断) | 闭项 | 严格高于 | 定理 |
|---|---|---|---|
| $\psi_0(\Omega_{\Omega^2+1})$ | `T 1 0 1` | `T 1 0 0` ($\psi_0(\Omega_{\Omega^2})$) | `Ω²<Ω²+1` |
| $\psi_0(\Omega_{\Omega^2\cdot2})$ | `T 2 0 0` | `T 1 0 1`; 也高于 $\{$`T 1 n a`$\}$ 任意可数族的上确界 | `Ω²+1<Ω²·2`, `Ω²·2>sup` (=`SupR 1`) |
| $\psi_0(\Omega_{\Omega^2\cdot\omega})$ | `Tω` | `T 2 0 0`; 也高于一切 `T r n a` | `Ω²·2<Ω²·ω`, `T≤Tω` |
| $\psi_0(\Omega_{\Omega^3})$ | `T³` | `Tω`; 也高于 $\{$`T r n a`$\}$ 任意可数族的上确界 | `Ω²·ω<Ω³`, `Sup3` |

**分辨力.** 上一轮的 `S1`–`S4` 只说后一站比前一站多一格. 这一轮的 `SupR` 说: $\Omega^2\cdot(r+1)$ 的闭项高于第一位为 $r$ 的**整族**站 (任意可数子族) 的上确界, 而不只高于它的某一个成员; `Sup3` 对 $\Omega^3$ 与整个三位族同理. 证法是: 整族都在 `nl` 段的极限 (`TRω r`, `Tω`) 之下 (`T≤TRω`, `T≤Tω`, 都是字面的部分和), 闭包节点 `κR r`, `κ3` 在其后的回灌输出非零 (`nz-κ`, 对一切 `ρ`, 一条定理). **到此为止:** 多出的是 "整族的上确界之上一段非零", 不是 "高于前一族的某个闭包点" (例如 `T 2 0 0` 高于映射 α ↦ ψ₀(Ω_{Ω²+α}) 的不动点). 后者要在超限下标 $\alpha\ge\omega$ 上的站与回灌格子 (在更大的世界里) 之间比较, 要折叠对世界单调, 没有做.

## 翻译账 (硬交付)

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 第三位 $r$, 层 $(r,p,a)$ | 读法 $\Omega_{\Omega^2\cdot r+\Omega\cdot p+a}$ | **读自记号的算术** (同 README 翻译账里 `CumHtBase` 的 $(r,p,a)$) |
| 节点种类 `lr`: $g\lhd r$ | 照 `lo` 的形状上移一位 | 读自记号的序 |
| `lr` 的 $h,k$ 在世界之下 | 不这样就没有字面公共上界 | 树逼的 (壁垒) |
| 顶层三位都在世界之下 | 同上 | 树逼的; 顶层放在 $\Omega^3$ 是选站 |
| `rkT` 三级字典序 | $\Omega^2 g+\Omega h+k<\Omega^2 r+\Omega q+t$ | 读自记号的序 |
| `stepR`: 第一位一步是 $\sum_{d}\sum_{z:(c,d,0)}1$ | 与 `stepH` 同形; 用 $(c,d,0)$ 是值的选择 | 树侧, 值不变是判断 |
| `mkOf` 9 种情形, `LowR`, `accYr` | 由前几行机械推出 | 树逼的 (从前几行) |
| `κN` (一切闭包一个造法), `nz-κ` (一条定理对一切 `ρ`) | 为了不按站写 | 树侧 |

**按 `AGENTS.md` 归类: 加深翻译.** 没有新构造子, 唯一的合法性 `Lg-sum` 无前提, 没有 `Lab`. 但出现了 "每升一级加一维" 的模式: 层的位数照 $\Omega$ 的幂写, 节点种类每级多一种, 比较每级多一级, 而且到 $\Omega^\omega$ 正卡在位数上 (见下). 这比 `SumHt` 的 "提供信息, 形状受记号影响" 更深一档. **交给摆脱侧 `HtGen`** (高度由回灌生成), 这一路不再往上加维. 提供信息的一面: `nz-κ` 是对闭包形状参数 `ρ` 的一条定理, 每站新用到的字段是 `lr` (从 $\Omega^2\cdot2$ 起), `stepR` (状态里的 $\Omega_{(r,\cdot,\cdot)}$), 顶层三位 (`κ3`).

## 账 (层 1–3, `locslice_l12.py` 口径)

实测, 定义级切片, 计 agda 非空非注释行, 记号模块除外 (脚本在临时目录 `sumht/locslice_climb.py`).

| 路线 | 层 1 (`D₊`, `D`, `D̂`, `Dl`) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) | 加严格增长 |
|---|---|---|---|---|
| SumHt, 到 $\Omega^2$ | 75 | 628 (去共用 545) | 645 (去共用 562) | 865 (净增 220) |
| SumClimb, 到 $\Omega^3$ | 84 | 700 (去共用 617) | 721 (去共用 638) | 1005 (净增 284) |

- 加一维的代价: 层 2 多 72 行, 层 3 多 76 行. 层 2 按模块: SumClimbTree 284, SumClimbFold 185, Free.Level 56, SumClimbClosed 56, CumReadCF 42, BTBO 27, TLOpsW 27, SumHtTree 23.
- 每站增量 (都在同一组定义上, 只多积木): `κN` 9 行; `κB` +6, `B` +4; `κR`, `BR` +6; `X` (一切 $\Omega^2 r+\Omega n+a$) 30 行合计; `Xω` 再 +2; `κ3`, `X³` 再 +4. 即 $\Omega^2+1$, $\Omega^2\cdot2$ 共用 30 行, $\Omega^2\cdot\omega$ 多 2 行, $\Omega^3$ 多 4 行.
- 严格增长 (在层 3 之上): `Ω²<Ω²+1` +136, `Ω²+1<Ω²·2` +253, `Ω²·2<Ω²·ω` +264, `Ω²·ω<Ω³` +165, `SupN` +222, `SupR` +248, `Sup3` +260; 合计净增 284 (SumClimbGrow 239, TLRuleSpec 24, 其余 21).

## 第一个障碍: $\psi_0(\Omega_{\Omega^\omega})$

要一个折叠里有一切位数的层. 位数固定时 (这里是 3) 分支的类型 `D r p a` 三个参数分开写, 停机检查看得见字典序. 位数可变时, 层是一个列表, 字典序的下降可以落在任何一位, 停机检查看不见. 临时目录里的试验 (`sumht/SumClimbVarRank.agda`, 不进仓库, 层 `a ∷ L` 读 $\Omega\cdot L+a$, 节点种类按尾部递归) 的报错原文:

    SumClimbVarRank.agda:18.1-29.45: error: [TerminationIssue]
    Termination checking failed for the following functions:
      D, VL
    Problematic calls:
      VL L
        (at SumClimbVarRank.agda:22.47-49)
      D (k ∷ L′) W′
        (at SumClimbVarRank.agda:24.44-45)

改用可达性证明作 `D` 的下标, 类型会依赖证明: 链的起点 (状态在节点层的差, 类型 `D L′`) 与节点分支的类型 (`D L′` 带由节点取出的可达性) 对不上 (判断, 没有试). sized types 不在 `--safe` 里. 这是未走通, 不是否定. 判断: 它与 "每升一级加一维" 是同一个问题, 应由摆脱侧 (`HtGen`) 回答.

## 有限测试

没有做新的计值 (上一轮 `G 1` 在 `SumHt` 的 $\Omega_\Omega$ 站已超 90 秒, 这里只会更慢).

## 审计

- `importclosure.py`: `SumClimbTree`, `SumClimbFold`, `SumClimbClosed`, `SumClimbGrow` 都 OK (禁用表命中 0).
- `depslice.py` (到达块 / 记号块 / 词命中): `SumClimbClosed:fgh` 174/0/0, `SumClimbClosed:Lg-T³` 158/0/0, `SumClimbClosed:TΩ` 136/0/0, `SumClimbGrow:Sup3` 243/0/0, `SumClimbGrow:SupR` 231/0/0, `SumClimbGrow:Ω²·ω<Ω³` 203/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用.
- 禁用构造: 五个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumClimb where

open import OCF.Align.SumClimbClosed using (T; TNω; TRω; Tω; T³; TΩ; Lg-T; Lg-Tω; Lg-T³; Lg-TΩ; TΩ²+1; TΩ²·2; TΩ²·ω; TΩ³; fgh; G) public
open import OCF.Align.SumClimbGrow using (S1; S2; S3; S4; S5; S6; SupN; SupR; Sup3; nz-κ; Ω²<Ω²+1; Ω²+1<Ω²·2; Ω²·2<Ω²·ω; Ω²·ω<Ω³; Ω²·2>sup) public
```
