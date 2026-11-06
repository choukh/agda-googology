# `T-Ω` 的序数值验收: 高度树一族的第一条值定理

> 入口. 不读记号, 不是验收文件 (本组没有读记号的文件). 目标 (作者 2026-11-05 派): `BTBOᴵ ≼ ⟪ T-Ω ⟫`, 能做到就再证反方向; 照 `SumOneRel`/`Sim`/`Top`/`Accept` 为 `HtFeedFold` 重写, 不用 nκ 的值语义, 不用共用的单调引理.
>
> **判决: 未走通 (暂停).** `BTBOᴵ ≼ ⟪ T-Ω ⟫` 没有证出来, 反方向也没有. 编译过的是两条否定, 它们划出第一个障碍: **高度树的可数层 $\Omega_L$ 的写法.**
>
> 1. **`EndLowTNeg.no-Rel`, `no-Relˡ`** (定理): `SumOne` 一路用的精确对应 `TLRuleRel.Rel` 里, 差树 `n1 ⨾ ni r u` (节点的层 $k\ne0$) 对任何底, 任何终点都没有像. 高度树的 $\Omega_{b+1}$ = `n1 ⨾ ni (ss hself) (λ _ _ _ → n1)` 正是这个形状 (`HtFeedTree.Ωd` 只看最外构造子); `TLRuleSum`, `SumOne` 的 $\Omega_{a+1}$ = `n1 ⨾ Dif (a+1)`, 节点之前先走完 `Dif`, 底是 $\Omega_a$, 所以有像 (正对照 `pos` = `Ω-Rel`). 实例: `no-Ω₂` (层 2), `no-Ωω+1` (层 $\omega+1$).
> 2. **`EndLowTShape.T-Ω≇T₀`** (定理): `HtFeedClosed.T-Ω` 与 `SumOneClosed.T₀` 不 $\cong$ (`OCF.Free.Level` 第 0 层). 沿 ℕ-分支 $[1,2,1,0,0,1,0,0,0,0,0]$ 走到的节点构造子不同. 所以 `SumOneAccept.T₀≈` 不能经 $\cong$ 搬到 `T-Ω`. 有限测试 (测试档): 宽 2 到深度 16 相同, 宽 3 在深度 12 之内分开; 判断: 第一个分开的位置是第 1 段回灌的第 2 个坐标, 即层 `emb 2` 的节点, 与第 1 条一致 (层 1 上两种写法只差一个 `n0`: `SumOne` 的 $\Omega_1$ 是 `n1 ⨾ (n0 ⨾ ni …)`, 节点之前的 `Dif 0` 是空的; 从层 2 起 `Dif` 里有节点).
>
> **所以 "照 `SumOne` 的模式重写" 不能逐字照写**: 那套对应要求每个可数层的 $\Omega_L$ 对上参照的 $\dot\Omega_L$, 高度树的 $\Omega_L$ ($L\ge2$) 在那套关系里根本没有像 (不只是对不上 $\dot\Omega_L$). 剩下的路 (判断, 都没有试):
>
> - (a) 改主线: 高度树的可数层 $\Omega_L$ 改回 `n1 ⨾ Dif` 的写法 (只改 `Ωd` 在 `hs`, `hl` 上的两行; $\Omega$-极限层不动). 判断: 那样 `T-Ω` 在可数层上与 `SumOne` 同形, `SumOneRel`/`Sim`/`Top` 可以照写, 估计 600 到 900 行. 代价: 加回 `Dif` (README 翻译账里 `HtFeedTree` 记的 "不从 0 走到 L, 所以没有 `Dif`" 要撤回), 而 `Dif` 是坐标的写法, 加深翻译还是提供信息要另算. 改定义由作者定.
> - (b) 不改主线: 换参照的读法. 高度树的节点紧跟在底 $1$ 之后, 分支的读数只能从 $0$ 起计 ($H(z)=1+z$ 一类), 参照树不再是 $\dot\Omega$; 与 `CumReadCF` 的 $\psi$ 或 `BTBOᴵ` 的比较只能在值上 (而 `Value.ψ⁰-not-cong` 说 $\psi^0$ 对高层参数不是值同余). 这就是第 4 层的值语义, 正是本次要避开的; 判断不比 nκ 的值语义省.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 没有用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EndLowT where

open import OCF.Align.EndLowTNeg using (Hd; hd; ≈-hd; n1-hd; ni-hd; ni-hdˡ; no-Rel; no-Relˡ; Ωht₂; no-Ω₂; Ωht-ω+1; no-Ωω+1; pos) public
open import OCF.Align.EndLowTShape using (walk; walk-≅; path; T-Ω≇T₀) public
```

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `≈-hd` | EndLowTNeg | 结构等价保最外构造子 (懒嵌入透明) | 定理 |
| `n1-hd`, `ni-hd`, `ni-hdˡ` | EndLowTNeg | `Rel` 里 `n1` 之后是后继; 层非零的节点之前是节点或极限 (由 `ContF`) | 定理 |
| **`no-Rel`, `no-Relˡ`** | EndLowTNeg | `n1 ⨾ ni r u` (层 $k\ne0$) 对一切底, 终点, 分支都没有 `Rel` | 否定, 定理 |
| `no-Ω₂`, `no-Ωω+1` | EndLowTNeg | 高度树的 $\Omega_2$, $\Omega_{\omega+1}$ 的形状搬进 `TLRuleSum` 的差树, 没有 `Rel` | 否定, 定理 |
| `pos` | EndLowTNeg | 正对照: `TLRuleSum` 的 $\Omega_2$ 有 `Rel` | 定理 |
| `walk-≅` | EndLowTShape | $\cong$ 保沿路径看到的构造子 | 定理 |
| **`T-Ω≇T₀`** | EndLowTShape | `T-Ω` 与 `SumOne.T₀` 不 $\cong$ | 否定, 定理 |
| 宽 2 深度 16 相同, 宽 3 深度 12 之内分开 | (临时目录的测试, 不在仓库) | `same d w (ord T-Ω) (ord T₀)` | 有限测试 |
| `BTBOᴵ ≼ ⟪ T-Ω ⟫`, 反方向 | — | 没有做出来 | 未走通 |

**否定的范围.** `no-Rel` 只否定 `TLRuleRel.Rel` 这一种精确对应 (也就是 `SumOne` 一路的模式), 不否定值层的验收, 也不否定换一种参照读法的精确对应. `T-Ω≇T₀` 只否定结构互模拟, 不否定 `T-Ω` 与 `T₀` (从而与 `BTBOᴵ`) 值相等; 读法 (判断) 两者都读 $\psi_0(\Omega_\Omega)$.

## 第一个障碍

高度树 `HtFeedTree.Ωd` 在可数层 (`hs`, `hl`) 上只看最外构造子, 节点紧跟在底 $1$ 之后. `SumOne` 一路的精确对应要节点之前的底是 $\Omega_k$ (`Dif` 给的), 所以在高度树上没有像 (`no-Rel`). 绕过它要么改 `Ωd` 的两行 (上面的 (a), 由作者定), 要么做值层的比较 ((b), 第 4 层的值语义).

## 翻译账

| 新增 | 来源 | 类 |
|---|---|---|
| 没有新定义进主线; 两条否定与一条形状引理 | `no-Rel` 划出 "节点紧跟 `n1`" 这个字段不能有 (对精确对应); `T-Ω≇T₀` 给出树与 `SumOne` 的树在哪里不同 | 提供信息 |
| (a) 若采纳: `Ωd` 在可数层改回 `n1 ⨾ Dif` | 由 `no-Rel` 逼出 (对精确对应的验收); `Dif` 本身是 `TLRuleSum` 的坐标写法 | 未做; 由作者定 |

## 审计

- **导入闭包**: `EndLowTNeg`, `EndLowTShape`, `EndLowT` 过 `importclosure.py`, `--only` 列表 `OCF.Align.CumReadCF OCF.Align.TLRule OCF.Align.HtFeed OCF.Align.HtGen OCF.Align.SumOne OCF.Align.EndLowT OCF.BTBO OCF.Free.Level` (前缀匹配): 闭包 18 / 21 / 28 个模块 (本地 8 / 11 / 17), 禁用表 0, `--only` 之外 0, 退出码都是 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `no-Rel` 76/0/0, `no-Relˡ` 76/0/0, `pos` 106/0/0, `T-Ω≇T₀` 281/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 三个文件无 `postulate`, 无洞, 无停机或正性编译指示, 无 `trustMe`, 没有 `Funext`.
- **行数** (代码块里非空非注释行): `EndLowTNeg` 109, `EndLowTShape` 41, 入口 4.
- **编译**: 不要归档. 从仓库根 `agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes probes/OCF/Align/EndLowT.lagda.md +RTS -M6G -RTS` (退出码 0, 峰值约 0.5G).
