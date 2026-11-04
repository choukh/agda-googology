# 和形式, 高度取 $A$: 过 $\psi_0(\Omega_{\Omega+2})$, $\psi_0(\Omega_{\Omega\cdot2})$, $\psi_0(\Omega_{\Omega\cdot\omega})$, $\psi_0(\Omega_{\Omega^2})$

> 入口. **判决: HOLDS (本路的四项要求), 强度读法未验收.** 定义 HOLDS: 层是 $(p,a)$, $p,a$ 都是字面合法的 $A$, 加一个顶层; 合法性由形状给出 (`Lg-sum`), 定义里没有 `HS`, `Goodᴺ`, `WF`, `ψW`, 没有证书参数. 闭项: 一切 $(p,a)$ 的 `TΩ p a`; 站 `T n a` (一切 $n,a\in\mathbb N$), `Tω`, `T²`. 严格增长 HOLDS, 是布劳威尔树上的定理, 四条对一切 $n,a$ (`S1`–`S4`), 无前提. **严格增长只说明站不塌缩** (后一站的折叠字面含前一站的折叠, 再多一段非零), 不说明增长的量级; 各站与对照树之间既没有上界也没有下界, 读法 $\psi_0(\Omega_{\Omega\cdot n+a})$ 等是判断.
>
> 全文 `--safe --without-K --lossy-unification` (工程的 `.agda-lib` 另加 `--cubical-compatible`), 无公设, 无洞, 无停机或正性编译指示, 不开 K, 没有 `next`, `cumA`, ⊞, u+. 定义不读记号; 记号只在 [SumHtAccept](SumHtAccept.lagda.md) (读 `Value`).

## 定义

    data D L W: n0 | n1 | x ⨾ y | nl d | ni r u | nκ _ u | nw p x      (与 SumOne 相同, 没有新构造子)
    层: lay p a  (Ω_{Ω·p+a}),  top  (Ω_{Ω²})

- 层 $(p,a)$ 的节点种类 `KP p a W h k` ([SumHtTree](SumHtTree.lagda.md)): `sm` 同高度, $k$ 严格低于 $a$ (不看世界); `lo` 低高度 $h\lhd p$, $k\sqsubseteq W$. 分支的类型按 $a$ 或 $p$ 结构递归 (与 [TLOpsW](TLOpsW.lagda.md) 的 `Vs`, `Low` 同形).
- 顶层 `KT`: 节点的高度和下标都在世界之下. 这是 `SumOne` 顶层 (下标在世界之下) 多一维. 顶层不是任何节点的层, 也不是目标, 所以从不与别的层比较.
- `nκ` ($\sum_{c\ge W}u(c)$) 在除 $(0,0)$ 外的每一层都允许 (`ZP`); 折叠时目标是 $(0,0)$ 就回灌, 否则保留 (同 `SumOne`).
- 折叠 ([SumHtFold](SumHtFold.lagda.md)) 与 `SumOneFold` 逐个对应. 改的三件: 目标是 $(q,t)$ 加字面世界 $m$ (`Tg W q t m`); 节点与目标先在 $m$ 内比高度再比下标 (`rkT`); 没有单独的顶层目标.

**为什么取 $A$, 不取 `Hg`.** `Hg` (`ht a | tφ f`) 只为一个顶 $\Omega^2$ 加了一个高度类型和证据 `HO` (`f ≡ ht`). 这里高度就是 $A$, 层 $(p,a)$ 覆盖 $\Omega\cdot p+a$ 的一切 $p<\omega_1$; 顶 $\Omega^2$ 不做成高度, 做成一个层 `top`, 与 `SumOne` 的顶层同一种做法, 只在节点上要高度在世界之下. 被比较的高度与下标总有字面公共上界 $m$ (`cmpF`), 高度上没有全局三歧. 壁垒 (`Barrier`): 下标类型 $A$ 没有 $\Omega$-共尾元; `top` 是层不是下标, 不参与比较. 这是判断, 没有定理说明这样就不触犯壁垒以外的东西.

**站的输入** ([SumHtClosed](SumHtClosed.lagda.md)): 都是顶层在世界 $\omega$ 上的元素, 用同一组积木: `nd n m` $=\sum_{z:(n,m)}1$, `B n` $=\sum_{m<\omega}$`nd n m` $+\ \sum_{d\ge\omega}\sum_{z:(n,d)}1$, `κH` $=\sum_{c\ge\omega}\sum_{z:(c,0)}1$, 右结合的前缀 `Pfx`.

    Xna n a = 1 ⨾ B 0 ⨾ … ⨾ B (n-1) ⨾ nd n 0 ⨾ … ⨾ nd n (a-1)     Ω_{Ω·n+a}
    Xω      = 1 ⨾ nl B                                              Ω_{Ω·ω}
    X²      = 1 ⨾ (nl B ⨾ κH)                                       Ω_{Ω²}

闭包节点放在运行的世界 $\omega$ 上, $\omega$ 之前的部分写成 ℕ-和. 与 `SumOne` 的 `Ω̂₀` (闭包在世界 $0$ 上, 由 `nw` 抬升) 值相同 (判断). `κH` 用 $(c,0)$ 而不用整段: $\sup_c\Omega_{\Omega\cdot c+1}=\Omega_{\Omega^2}$, 值相同 (判断).

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `TΩ`, `Lg-TΩ` | SumHtClosed | 一切合法 $(p,a)$ 与世界 $m\sqsupseteq p,a$: 层 $(p,a)$ 的 $\Omega$ 的折叠, 合法 | 定义; 合法性是定理 |
| `T`, `Tω`, `T²`, `Lg-T`, `Lg-Tω`, `Lg-T²`, `fgh` | SumHtClosed | 站的闭项, 无参数 | 定义; 合法性是定理 |
| `L1`, `L1b`, `ptF≡pt` | SumHtGrow | 右结合前缀的折叠就是 `nl` 的部分和 (字面, 对一切 $F$) | 定理 |
| `L2`, `L3` | SumHtGrow | 分支为 $1$ 的节点在目标 $(0,0)$ 上输出非零, 只要状态在各目标上非零 | 定理 |
| `L4` (模块 `W`) | SumHtGrow | 回灌第一格走的路非零 (按 `sum-fst` 的形状) | 定理 |
| **`S1`** | SumHtGrow | `asuc (T n a) ≤ T n (suc a)`, 一切 $n,a$ | 定理 |
| **`S2`** | SumHtGrow | `T n a ≤ T (suc n) 0`, 一切 $n,a$ | 定理 |
| **`S3`** | SumHtGrow | `T n 0 ≤ Tω`, 一切 $n$ | 定理 |
| **`S4`** | SumHtGrow | `asuc Tω ≤ T²` | 定理 |
| `Ω+1<Ω+2`, `Ω+2<Ω·2`, `Ω·2<Ω·ω`, `Ω·ω<Ω²`, `lt-up`, `lt-ω` | SumHtGrow | 要求的各站一站严格高过一站 | 定理 |
| `v-…` | SumHtAccept | 同上, 搬到 `Value` 的 `_≼_` | 定理 |

## 每站严格增长

| 站 (读法是判断) | 闭项 | 严格高于 | 定理 | 档 |
|---|---|---|---|---|
| $\psi_0(\Omega_{\Omega+1})$ | `TΩ+1 = T 1 1` | `T 1 0` ($\psi_0(\Omega_\Omega)$) | `Ω<Ω+1` | 定理 ($\le$ 与 $\preccurlyeq$) |
| $\psi_0(\Omega_{\Omega+2})$ | `TΩ+2 = T 1 2` | `TΩ+1` | `Ω+1<Ω+2` | 定理 |
| $\psi_0(\Omega_{\Omega\cdot2})$ | `TΩ·2 = T 2 0` | `TΩ+2`, 也高于一切 `T 1 a` | `Ω+2<Ω·2`, `lt-up` | 定理 |
| $\psi_0(\Omega_{\Omega\cdot\omega})$ | `TΩ·ω = Tω` | `TΩ·2`, 也高于一切 `T n a` | `Ω·2<Ω·ω`, `lt-ω` | 定理 |
| $\psi_0(\Omega_{\Omega^2})$ | `TΩ² = T²` | `Tω` | `Ω·ω<Ω²` | 定理 |

**这些定理说的是什么, 不说什么.** 每站的输入字面地以前一站的输入为前缀 (或以它为 `nl` 的一个部分和), 折叠逐项相同 (`L1`), 再多出的一段在目标 $(0,0)$ 上非零 (`L2`, `L4`). 所以严格增长与折叠强不强无关: 任何不把非零输入折成零的折叠都会满足. 它们说明站不塌缩, 不说明 `T 2 0` 高过 `T 1` 的不动点, 也不说明 `T²` 高过 `T n 0` 的对角. 量级只能靠序数值验收, 这里没有.

## 翻译账 (硬交付)

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 层是一对 $(p,a)$ | 读法 $\Omega_{\Omega\cdot p+a}$; 壁垒不许 $A$ 里有 $\Omega$-共尾元, 所以超过 $\Omega_\Omega$ 只能加一维 | 一维是壁垒逼的; 写成 $\Omega\cdot p+a$ 的两维是读法 (记号的算术) |
| 节点种类 `sm`/`lo` | 照 `TLOpsW` 的 `oi`/`od` | 形状受旧树影响 (`TLOpsW` 的折叠形状受 Buchholz 影响, 见 README 翻译账) |
| `lo` 的下标要在世界之下 | 不这样, 节点下标与目标下标没有字面公共上界 | 树逼的 (壁垒) |
| 顶层 `KT`: 高度也在世界之下 | 高度闭包 `κH` 的分支高度任意, 要能比较 | 树逼的; 顶层放在 $\Omega^2$ 是选站 |
| 目标带字面世界 `Tg W q t m` | 两维都在 $W$ 之上时没有公共上界去取 max | 树逼的 (编译时 `SumOne` 的 `Tg t W` 推不广) |
| `rkT` 的字典序: 先高度后下标 | $\Omega\cdot h+k<\Omega\cdot q+t$ | 读法 (记号的序); 保留/上升的规则本身沿用 `SumOne` |
| `ZP`: 除 $(0,0)$ 外都允许 `nκ`, 只在 $(0,0)$ 回灌 | `SumOne` 的 `NZ L` 推广 | 形状受旧树影响 |
| `Ωd`: 高度的后继一步是闭包 `stepH` | `SumOne` 的 `Ω̂₀` 换一个高度 | 树侧 (沿用) |
| `S = ω⋅` | 抄自旧折叠 | 同 `SumOne` |
| 站的积木 (闭包在运行世界上, 之前写成 ℕ-和; `κH` 用 $(c,0)$) | 为了站字面相接 | 选择; 值不变是判断 |

**按 `AGENTS.md` 归类: 提供信息, 形状受记号影响; 没有加深的标志.**
- 加深的三个标志: 新构造子或节点字段读自基本列规则: **没有** (构造子与 `SumOne` 相同; `sm`/`lo` 是层的种类, 不是基本列规则; 没读任何基本列); 闭包定理新增专属前提: **没有** (唯一的合法性是 `Lg-sum`, 无前提; `S1`–`S3` 对一切 $n,a$, 没有按站定制); 只能用 `Lab` 验收: **不是** (没有用 `Lab`).
- 提供信息的三个标志只有第一条: 对结构参数的一步定理 (`S1`, `S2`, `S3` 对 $n,a$), 每站新用到的字段: $\Omega+a$ 用到层 $(1,a)$ 的 `sm` (`DifI`), $\Omega\cdot2$ 用到层 $(2,0)$ 的 `lo` 与 `H.suc` 路径 (`stepH` 在高度 $0,1$), $\Omega\cdot\omega$ 用到一切有限高度, $\Omega^2$ 用到顶层 `KT` 与高度 $\ge\omega$ 的层 $(c,0)$. 序数值验收与基本列的差: **没有**. 划出不能有的字段的否定定理: **没有**.
- 所以这一步的贡献是信息 (两维的层在和形式里写得出, 合法性仍由形状给出, 定义只多 93 行), 不是摆脱翻译: 层的形状照 $\Omega\cdot p+a$ 写, 字典序照记号的序写.

## 账

实测, 定义级切片, 口径同 `locslice_l12.py` 与 `sumone/locslice_sumone.py` (计 agda 非空非注释行, 记号模块除外; 脚本在临时目录 `sumht/locslice_sumht.py`, 读 `agda --html` 的输出).

| 路线 | 层 1 (类型) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) | 加严格增长 |
|---|---|---|---|---|
| SumOne, 到 $\Omega+1$ | 21 (含 `D`, `D̂`, `Dl`: 53) | 535 (去共用 452) | 537 (去共用 454) | — |
| SumHt, 一切 $(p,a)$ 与 $\Omega^2$ | 21 (含 `D`, `D̂`, `Dl`: 75) | 628 (去共用 545) | 645 (去共用 562) | 865 (净增 220) |

- 层 2 净增按模块: SumHtTree 249, SumHtFold 173, Free.Level 56, SumHtClosed 45, CumReadCF 30, BTBO 27, TLOpsW 27.
- 层 3 只多 17 行 (`Lg-T`, `Lg-Tω`, `Lg-T²`, `Lg-TΩ` 各是 `Lg-sum` 的一次调用); `Lg-sum` 的切片 97 行, SumHtTree 内 73 行.
- 严格增长净增 220 行: SumHtGrow 182, TLRuleSpec 24, 其余 14.
- 与 `SumOne` 比: 层 2 多 93 行, 层 3 多 108 行, 从 $\Omega+1$ 到 $\Omega^2$.

## 有限测试

慢增长 `G n` 沿第 $n$ 项走到底 (`SumHtClosed.G`), 用 `agda --interaction` 的 `Cmd_compute_toplevel` 计值, 每条限 90 秒. **只是测试**, 盲区: 单路径, 小参数, 超时没有结果, 看不出量级.

| 项 | 结果 |
|---|---|
| `G 0` 于 `T 0 0`, `T 1 0`, `T 1 1`, `T 1 2`, `T 2 0`, `Tω`, `T²` | 都是 1 |
| `G 1 (T 0 1)` | 4 |
| `G 1 (T 0 2)`, `G 1 (T 1 0)`, `G 1 (T 1 1)` | >90 s |
| `G 2 (T 0 2)` | 堆耗尽 (8G) |

`G 0` 全是 1: 第 0 条路径只走到第一个 `Step`, 不分辨站. 这一栏没有分辨力.

## 第一个障碍

**序数值验收.** 没有任何一站与对照树有定理. `SumOne` 的 `T₀≈` 靠 `SumOneRel`, `SumOneSim`, `SumOneTop` (约 450 行) 把折叠对上旧树, 只对没有 `nκ` 的片段; 这里的折叠改了目标的形状 (`Tg W q t m`), 那些对应要重写, 而且带 `nκ` 的片段 `SumOne` 本身就没有对应 (第一支对不上, 见 `SumOne` 的第一个障碍). 没有否定定理, 是未走通.

**严格增长之外的量级.** 要说 `T 2 0` 真正高过 $\psi_0(\Omega_{\Omega+\alpha})$ 的不动点, 需要折叠对世界单调 (回灌的格子在大世界里重走分支), 这件没有做. 判断: 它与序数值验收是同一类工作, 规模在 `CumVal` 的估计 (超 3000 行) 那一档. 未走通.

**$\psi_0(\Omega_{\Omega^2+1})$ 起.** 顶层不是目标也不是节点的层; 要往上, 顶层要能当目标 (像 `SumOne` 的 `ŷ`), 再往上 ($\Omega^2\cdot2$) 层要多一维, 那就是 `CumHt` 的 $(r,p,a)$ 那一步. 没有做.

## 审计

- `importclosure.py`: `SumHtTree`, `SumHtFold`, `SumHtClosed`, `SumHtGrow` OK (禁用表命中 0); `SumHtAccept` FAIL (经 `Value`, `TLRuleVar`, 验收文件, 18 个命中), 这是验收文件.
- `depslice.py` (到达块 / 记号块 / 词命中): `SumHtClosed:fgh` 160/0/0, `SumHtClosed:Lg-T²` 144/0/0, `SumHtClosed:TΩ` 128/0/0, `SumHtFold:Run` 111/0/0, `SumHtGrow:S4` 182/0/0, `SumHtGrow:lt-ω` 190/0/0, `SumHtAccept:v-Ω·ω<Ω²` 244/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发 (见翻译账).
- 禁用构造: 五个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`.

**时间线.** 写定义前读过 `SumOne*`, `TLRuleSum`, `TLOpsW`, `WorldTHW`, `CumReadCF` 与 `TLRuleSpec` 的陈述. 没有打开 `EBO`, `Correspond`, `Label`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumHt where

open import OCF.Align.SumHtClosed using (TΩ; Lg-TΩ; T; Tω; T²; Lg-T; Lg-Tω; Lg-T²; TΩ+1; TΩ+2; TΩ·2; TΩ·ω; TΩ²; fgh; G) public
open import OCF.Align.SumHtGrow using (S1; S2; S3; S4; Ω<Ω+1; Ω+1<Ω+2; Ω+2<Ω·2; Ω·2<Ω·ω; Ω·ω<Ω²; lt-up; lt-ω) public
open import OCF.Align.SumHtTree using (sum-fst; Lg-sum) public
```
