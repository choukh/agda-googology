# 和形式过 $\psi_0(\Omega_{\Omega+1})$

> 入口. **判决: PARTIAL.** 定义 HOLDS, 严格下界 HOLDS, 序数值验收的上界和 $\psi_0(\Omega_\Omega)$ 之上的下界未走通 (没有否定定理). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 定义不读记号; 记号相关只在 [SumOneAccept](SumOneAccept.lagda.md), 而且只读 `BTBOᴵ` 与 `BTBOFull`.
>
> 一句话: 回灌闭包写成和上的一个节点 `nκ`, 闭项 `T₁` 带 `Lg-T₁`, 定义里没有 `HS`, `Goodᴺ`, `WF`, `ψW`, 只有讲和的那十几行. `T₀ ≈ᵛ BTBOᴵ`, `suc BTBOᴵ ≼ T₁` 都是定理. $T_1$ 与 $\psi_0(\Omega_{\Omega+1})$ 的对照树之间没有定理, 卡在闭包第一项对不上: 和形式的链从当前输出读层, 对照树从第一支读.

## 定义

    data D L W: n0 | n1 | x ⨾ y | nl d | ni R u | nκ _ u | nw p x

- `W` 是世界: 字面合法的上界, 比较都在它之内. `ni`, `nκ` 的分支只在更大的世界上有.
- `nκ _ u`: $\sum_{c\ge W}u(c)$. $\Omega_\Omega=1+\sum_{c\ge0}\sum_{z:c}1$, 这就是回灌闭包 (`Ω̂₀`). **没有第一支, 没有 `oc` 的两支:** 一个闭包只有一个分支函数.
- 折叠 `RunK`:
  - 目标是第 0 层: 取层 $v_0=W+z$ ($z$: 从世界 $W$ 起第 0 层输出长了多少), 走到 $v_0$; 再取 $v_1=v_0+\Delta_0$, 走到 $v_1$; 输出 $\sum_n\Delta_n$. $v_n\lhd v_{n+1}$ 是字面的 (`sum-fst`), 不用证, 也不用比两条链.
  - 目标是别的层: 走到当前世界, 节点保留 (`Kp`, `Kb`).
- 高度只有两档: 可数层 `D t` 和顶层 `D̂` ($\Omega_\Omega$ 这一层). $\Omega_{\Omega+1}$ 不是一个节点, 是 `Chŷ`: 顶层上的链, 坐标是状态在顶层的差. **这只到 $\Omega+1$, 不是 $(p,a)$ 的一般形状.** $\Omega+2$ 要再加一档, 没有做.

## 尺: 合法性证明多少行, 定义依不依赖证书

- 单独的合法性证明: `sum-fst`, `Lg-sum`, `Lg-pt`. `Lg-sum` 的切片 71 行, 其中 `SumOneTree` 里 52 行, 其余是 `CumReadCF` 的 `⊲-tr` 一类. 无前提, 不提折叠, 对一切第 0 层的和成立.
- 定义不依赖证书: `T₁` 的定义里没有 `HS`, `Goodᴺ`, `WF`, `ψW`, `toLevel`, 也没有 `force` 读证书. 层是 `sum W z`, 合法性 `Lg-sum` 在定义里被用到 (回灌的层要 `Lg` 才能比较), 这是唯一用到的证明.
- 对照: `Om1Hn` 的证书 2551 行 (定义 359 加证书 2192), 定义依赖证书 (`force` 读 `G`); `Om1Cum` 证书 2019 行.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `T₁`, `Lg-T₁`, `T₀`, `Lg-T₀` | SumOneFold | 闭项, 无证书参数 | 定义, 合法性是定理 |
| `RS` | SumOneSim | 没有 `nκ` 的项上, 折叠的差就是旧折叠在两端之间走过的路, 对被积函数和世界参数化 | 定理 |
| `Wk-Rel`, `CIs` | SumOneTop | 走层对上 $\Omega$; 回灌的每一格对上 $\psi(\Omega_a)$ | 定理 |
| `coS` | SumOneAccept | 相邻层对上旧折叠 | 定理 |
| **`T₀≈`** | SumOneAccept | `T₀` 与 `BTBOᴵ` 互相 $\preccurlyeq$ | 定理, 序数值验收 |
| **`step-T₁`** | SumOneAccept | `suc BTBOᴵ ≼ T₁`, 严格下界 | 定理 |
| `T₀<T₁` | SumOneAccept | `asuc T₀ ≤ T₁` | 定理 |
| `gap₀`, `T₀≇` | SumOneAccept | 第 0 项就低于对照树, 所以不 $\cong$ | 定理 |
| `step≈` | SumOneAccept | $u_{n+1}\approx\psi_0(\Omega_{u_n})$: 部分和的值就是折叠 | 定理 |

**上界: 没有. $\psi_0(\Omega_\Omega)$ 之上的下界: 没有.** 这两条都是未走通, 不是否定.

## 账

实测, 定义级切片, 口径同 `locslice_tlrule.py` (脚本 `probes/Survey/scripts/sumone/locslice_sumone.py`, 计 agda 非空非注释行, 记号模块除外).

| 路线 | 定义 | 加证书 (第 3 层) | 加第 4 层 | 第 4 层净增 |
|---|---|---|---|---|
| SumOne, $\psi_0(\Omega_\Omega)$ (`T₀≈`) | 471 | 473 | 5643 | 5170 |
| SumOne, $\psi_0(\Omega_{\Omega+1})$ 严格下界 (`step-T₁`) | 471 (同一声明块) | 473 | 5680 | 5207 |
| TLRule, $\psi_0(\Omega_\Omega)$ (`TΣ≈`) | 266 | 266 | 4502 | 4236 |
| 累加 `Tψ`, $\psi_0(\Omega_{\Omega+1})$ 严格下界 (`Om1Cum.step-Ω+1`) | 393 | 2019 | 6382 | 4363 |
| 不累加 (p,a) `Om1Hn.T₁`, 只到非严格下界 | 359 | 2551 | 6284 | 3733 |

- 第 3 层: SumOne 只多 2 行 (`Lg-T₁` 是 `Lg-sum` 的一次调用); 累加 1626 行, `Om1Hn` 2192 行.
- 第 4 层, 两条严格下界比: 公共 3872 行 (标签与对照树). 只在 SumOne: 1335 行 (`CumReadCFEq` 231, `SumOneRel` 162, `TLRuleAccept` 157, `SumOneSim` 150, `SumOneTop` 137, `TLRuleRel` 132, `SumOneAccept` 116, 其余). 只在累加: 491 行 (`CumUpAcceptVal` 148, `CumValZ` 143, `Om1CumGrow` 92, `CumVal` 67, 其余). 
- 读法: SumOne 把证书的代价挪进了第 4 层 (对应关系 `Rel`, `RS`), 净增多 844 行; 第 3 层与第 4 层合计 5680 对 6382, 少 702 行. 序数值验收两边都只到严格下界.

## 毛刺

**定理.** 和形式 `T₀` 的第 0 项 `u 0` 是 $\omega$ (`u0≤ω`, `u₀≈ω`), 对照树 `BTBOᴵ` 第 0 项是 $\psi_0(\Omega_1)$: **第 0 项就不同**, 差严格 (`gap₀`), 所以不 $\cong$ (`T₀≇`). 之后每项 $u_{n+1}\approx\psi_0(\Omega_{u_n})$ (`step≈`, 值层定理): **每个部分和的值就是上一项的折叠, 没有多出的值.** 所以基本列是错开一位, 不是 `Cumsum.overshoot` 那样改值. 依这条, 部分和在 $\psi_0(\Omega_\Omega)$ 这一站不算累加 (判断, 依据是 `step≈` 与 `T₀≈`).

**$\Omega+1$ 这一站.** `T₁` 第 0 项就是 `T₀`, 与对照树 `TF 1` 第 0 项同值 (两边都 $\approx$ `BTBOᴵ`: `T₀≈`, `Om1HnAccept.term₀`). 第 1 项起没有值层定理.

**有限测试** (慢增长 `G n`, 沿第 $n$ 项走到底; 盲区: 单路径, 小参数; 超时没有结果; 编译成 Haskell 也在 20 秒内算不出 `G 1 T₀`):

| 项 | 和形式 `T₁` | `TF 1` (标签) | `Om1Hn.T₁` | 累加 `TΩ+1` |
|---|---|---|---|---|
| 第 0 项, `G 0` | 1 | 0 | 0 | 0 |
| 第 0 项, `G 1` | >90s | 1 | 1 | >90s |
| 第 1 项, `G 1` | >90s | >90s | >90s | >90s |

$G_0$ 上和形式多 1, 来自部分和从 $\Omega_0=1$ 起 (`one`). 这只是第 0 条路径, 不能推值.

## 这些定理在不在前提里

| 定理 | 否定的是 | 在这个写法里 |
|---|---|---|
| `no-⊞-left` (`CumReadBase`) | 世界的加法左边保第一位置 | **不在.** `sum` 与 `⊞` 同形, 这个写法从不比 `sum a x` 与 `sum a′ x`: 下一个层总是接在当前层后面 (`sum-fst`), 只动右边 |
| `no-cum-⊲` (`CumReadBase`) | 累加保第一位置 | **不在, 而且相反.** 没有 `cumA`; `sum` 保第一位置是定理, 无前提 |
| `no-Root` (`Om1HnNeg`) | 对字面任意的 $a$ 有根上的 `Sees` | **不在.** 没有 `Sees`, `Root`, 也没有证书. 但这个写法的 $a$ 只到 $1$, 所以这也没有回答 $a$ 任意 |
| `no-Hn-b` (`NoCumHnNeg`) | 闭包的世界 $w=\lim 2n$ 是第一支读出的第一位置 | **不在**: 层是 $W+z$, 不读第一支. 代价写明: 世界不是当前输出时, 层多一个前缀 $W$. 闭项里世界都由链产生; 第 0 项这一点是定理 (`T₀-pt`), `T₁` 的其余项是判断 |
| `chain-stuck` (`DomFoldNeg`) | 第一路径守卫放得过带链的闭包 | **不在.** 没有守卫. 同类情形在这里不报错: 差为零时链停住, 输出少 (判断: 闭项里不发生) |

**两条链字面不可比.** 不比. 一次折叠只有一条链: 第 0 层的输出本身. 所有节点的层都是这条链的第一位置, 比较在世界内. 同一个闭包在两个世界的两次展开是两次不同的折叠, 互不比较. 代价在验收: 见下.

## 第一个障碍 (验收)

和形式的链只能从 $W$ 开始: 差要字面地接在前面, 而节点的分支只在 $c\ge W$ 上有. 对照树 (`OCF.Free.Tree` 的 `oclo`, `Goodᴺ.gc`) 从第一支起: $y_0=\psi_0(X+\Omega_1)$, $y_{m+1}=\psi_0(X+\Omega_{y_m})$; 这里 $v_0=\psi_0(X)$, $v_{n+1}=\psi_0(X+\Omega_{v_n})$. 第一支到 $g(c)$ 的第一位置在对照树是证书给的 (`Goodᴺ` 的 `mo₀`), 在这里没有差可写. 所以每个闭包的链都错开, 关系 `Rel` 在 `nκ` 上不可能逐项成立 (判断, 没有否定定理).

要接上, 需要: 上下文里的层的单调 $a\preccurlyeq b\Rightarrow\psi_0(X+\Omega_a)\preccurlyeq\psi_0(X+\Omega_{\mathrm{next}\,b})$, 这是 `Bump` 带上下文的版本, 在带闭包的项上. `T₀≈` 能过是因为这一站 $X$ 为空, `Bump` 现成. `Om1Cum` 对累加估计的 2400 到 4300 行里, 这一件的毛刺部分这里不会更少 (判断).

## 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `SumOneTree` | $\Omega_\Omega=\sum_{c}\sum_{z:c}1$ 是 $\Omega_\eta$ 的和形式, 不读基本列; 世界照 `TLOpsW` (`𝓞 p a u`) 的 Kripke 形状, 是壁垒要的 | 提供信息 |
| `SumOneFold` | `S = ω⋅` 抄自旧折叠 (同 `TLRule`); 回灌 "读当前输出" 是规则 6 的 $\gamma_1=\psi_0(X)$; 没有第一支, 与记号的基本列不同 | 提供信息, 形状受旧树影响 |

**时间线.** 写定义前读过 `Om1Cum`, `Om1Hn`, `TLOps*`, `NoCum*`, `OCF.Free.Tree`, `Force` 的陈述. 没有打开 `EBO`, `Correspond`, `Label`.

## 审计

`importclosure.py`: `SumOne`, `SumOneTree`, `SumOneFold`, `SumOneClosed`, `SumOneRel`, `SumOneSim`, `SumOneTop` OK; `SumOneAccept` FAIL (经 `Value`, `BTBOValNeg`, 验收文件). `depslice.py` (到达/记号块/词命中): `SumOneFold:T₀` 119/0/0, `SumOneFold:Lg-T₁` 120/0/0, `SumOneFold:RunK` 98/0/0, `SumOneTop:CIs` 309/0/0, `SumOneSim:RS` 236/0/0, `SumOneAccept:step-T₁` 925/0/0 (只读旧树). 正对照 `Om1HnAccept:label-term₀` 见报告. 只保证不引用.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOne where

open import OCF.Align.SumOneClosed using (T₀; T₁; Lg-T₀; Lg-T₁; fgh; G) public
open import OCF.Align.SumOneTop using (CIs; Wk-Rel) public
open import OCF.Align.SumOneTree using (sum-fst; Lg-sum) public
```
