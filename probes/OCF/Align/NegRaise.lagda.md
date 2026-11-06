# NegRaise: "一起升" 的升界算子, 否定一路 (入口与判决)

> 不含记号. 本路 (前缀 `NegRaise`) 是接口 [RaiseIf](RaiseIf.lagda.md) ("接口定稿 2026-11-05 (主审写, 首次编译通过后定稿)", 变更记录: 无; 本路没有改它, 没有在末尾加节) 的**否定**一路, 与构造一路 [RaiseC](RaiseC.lagda.md) 配对. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FEA` (只对 $\mathbb N\to$ `A`) 只在标 "条件" 的定理里作前提.
>
> **判决: PARTIAL. `RaiseA → WLPO` (或 LPO, 分离子) 未走通; `¬ RaiseA` 不可证 (元层, 判断, 见下).** 编译过的是: 五条边界否定, 一条选择子 ⇒ LPO, 一个部分的构造 (下界可判定相等时), 以及把 `RaiseA` 夹在 "WLPO 加外延" 之下的条件定理.
>
> **对纲领与目标.** 纲领 2 (无公理): 本路的构造 (`deq→at`, `raiseFin`, `fbaDec`, `fbaFin`) 无条件、停机, 但只覆盖有限数的下界; 对 ℕ-极限的下界, 已知的写法都要一个非构造原则 (`dec→Raise` 要 LPO 档, `wlpo→raise` 要 WLPO 加外延). 纲领 3 (壁垒): 本路的否定都是壁垒影子 (手册 §3.1) 的又一例, 落在 `no-joinA` 上: 要 $R$ 在不可比的一对上 "同时含两边" 的任何性质都不行. 目标 "让树自足": 给出一条树侧的判据: **升界只能依赖输入是否 "字面地出现" 在 $v$ 里, 这对有限的下界可半判定 (对角搜索), 对极限的下界是 $\Pi$ 型.** 这与构造一路 "回灌值要带字面公共上界" 的判据同向; 本路补上: 不带上界时, 有限下界仍可构造, 难处精确地在 "等于一个 ℕ-极限" 上.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRaise where

import OCF.Align.NegRaiseBnd
import OCF.Align.NegRaiseFin
import OCF.Align.NegRaiseSel
import OCF.Align.NegRaiseFba
import OCF.Align.NegRaiseCheck
```

## 定理表

| 名字 | 陈述 (白话) | 文件 | 档 |
|---|---|---|---|
| `no-mono0` | `RaiseA` 加 $R\,0\,v\lhd R\,a\,v$ (合法时) 矛盾 | Bnd | 定理 (否定) |
| `no-mono-a` | `RaiseA` 加 "对 $a$ 单调" 矛盾 | Bnd | 定理 (否定) |
| `no-cont0` | `RaiseA` 加 $R\,(f\,0)\,v\lhd R\,(\mathrm{alim}\,f)\,v$ 矛盾 | Bnd | 定理 (否定) |
| `no-flip` | `RaiseA` 加 $R\,v\,a\lhd R\,a\,v$ 矛盾 | Bnd | 定理 (否定) |
| `UpAll.no-tp-rs-upAll` | 积世界上 `upAll` 读分量 $i_0$, 无前提的 `tp-rs` 与 `RaiseA` 矛盾 | Bnd | 定理 (否定; 与 `RaiseCFba.no-fba-upAll` 同一结论, 以那里为主) |
| `UpAll.rs≤-upAll`, `rsLg-upAll`, `tp-rs-cond` | `upAll` 满足 `rs≤`, `rsLg`, 带前提的 `tp-rs` | Bnd | 定理 (给定 `RaiseA`) |
| `raise-up`, `inflate`, `head-suc`, `head-lim` | 律对输出向上封闭; 有一个 `RaiseA` 就有输出头恒为后继的, 也有恒为极限的 | Bnd | 定理 (盲) |
| `sel1→LPO`, `sel→LPO` | `RaiseA` 在 $a=1$ 处是选择子 ($R\,1\,v\equiv 1$ 或 $\equiv v$) ⇒ LPO | Sel | 定理 |
| `OnS.selᴮ1→LPO` | 高度版, 对一切 `S` 与一个合法世界 | Sel | 定理 |
| `OnS.no-alwaysᴮ`, `OnS.no-mono0ᴮ` | 高度版两条边界, 对一切 `S` 与一个合法世界 | Sel | 定理 (否定) |
| `inflateᴮ`, `head-sucᴮ` | 高度版的盲 | Sel | 定理 (盲) |
| `deq→at` | `DecAt a` (判定 "树 $=a$") ⇒ 对这个 $a$ 的升界算子 `RaiseAt a` (对一切合法 $v$) | Fin | 构造 |
| `raiseFin` | 有限数 $a$ 的 `RaiseAt`, 无条件 | Fin | 构造 |
| `ex-m0`, `ex-m2` | $a=1$, $v=\omega$: 第 0 项是 $1$, 第 2 项是 $\omega$ (`refl`) | Fin | 定理 |
| `deq→raise` | `A` 上处处可判定相等 ⇒ `RaiseA` | Fin | 条件 (前提: 处处可判定相等) |
| `deqω-sep` | `DecLgAt ω` ⇒ 分离子 `Sepω` | Fin | 定理 |
| `deqω→WLPO` | `DecLgAt ω` ⇒ WLPO | Fin | 条件 (`FEA`) |
| `wlpo→deq`, `wlpo→raise` | WLPO ⇒ 处处可判定相等 ⇒ `RaiseA` | Fin | 条件 (`FEA`, WLPO) |
| `deqω→deq` | `DecLgAt ω` ⇒ 处处可判定相等 | Fin | 条件 (`FEA`) |
| `fbaDec`, `fbaFin` | `DecAt c₀` ⇒ `tpA` 读第 $c_0$ 分量的 `FBA SA (c₀ , tt)`; 有限 $c_0$ 无条件 | Fba | 构造 |
| `Up.fba-up`, `Up.Fsuc`, `Up.fba-suc` | 读第 $c_0$ 分量的 `FBA` 对输出向上封闭 | Fba | 定理 (盲) |
| `decR-sel`, `decR-no-mono0`, `decR-no-cont0`, `decR-no-flip` | 构造一路的条件实例 `dec→Raise d` 是选择子, 不满足三条边界性质 | Check | 定理 |
| `fin-not-1`, `fin-not-ω` | `raiseFin 1` 在 $v=\omega$ 处的输出既不是 $1$ 也不是 $\omega$ (不是选择子) | Check | 定理 |

条件定理缺的前提的 Agda 类型: `FEA = ∀ (f g : ℕ → A) → (∀ n → f n ≡ g n) → f ≡ g`; `WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)` (`ColimWNeg`); `DecAt a = ∀ t → Dec (t ≡ a)`; `DecLgAt a = ∀ t → Lg t → Dec (t ≡ a)`.

## 前提实例 (每条否定的每个前提可满足)

- `no-mono0`, `no-mono-a`, `no-cont0`, `no-flip`, `no-tp-rs-upAll`: 前提是 `RaiseA` 加一条性质. 去掉 `R-hi`: `Rfst` ($R\,a\,v=a$) 满足 `R-lo`, `R-lg` 与 `Mono0`, `MonoA`, `Cont0` (`fst-mono0`, `fst-mono-a`, `fst-cont0`). 去掉 `R-lo`: `Rsnd` ($R\,a\,v=v$) 满足 `R-hi`, `R-lg` 与 `Mono0`, `Cont0`, 无前提的 `tp-rs` (`snd-mono0`, `snd-cont0`, `snd-tp-rs`). `Flip` 与 `R-lg`: 常值 $0$ (`zero-flip`). 去掉附加性质: `RaiseA` 本身经典地可满足 (`RaiseCBd.dec→Raise`, 前提 LPO 档; 本路 `wlpo→raise`, 前提 WLPO 加外延).
- `sel1→LPO`: 选择子与 `R-lo`, `R-lg` (`Rfst`, `fst-sel1`); 与 `R-hi`, `R-lg` (`Rsnd`, `snd-sel1`); 与三条律一起: `dec→Raise d` (`decR-sel`, 前提 LPO 档, 经典地成立). 族 `vA α` 每一棵合法 (`Lg-vA`).
- `OnS.*`: 合法世界的实例 `lw-S₀` (`S₀` 的世界 $0$).
- 条件定理的 `FEA`, WLPO, `DecAt ω`: 经典地成立, Agda 里证不出也否证不了 (判断).

## 只否定什么, 不否定什么

- **只否定:** 三条律同时成立时的五条附加性质 (`Mono0`, `MonoA`, `Cont0`, `Flip`, `upAll` 上无前提的 `tp-rs`); 选择子形状 (推出 LPO); 在 $a=\omega$ 处 "用判定相等构造 $R$" (条件 `FEA` 下推出 WLPO).
- **不否定:** `RaiseA` 本身; `RaiseAt ω`; `RaiseB S` (对任何 `S`); 一般 $c_0$ (如 $\omega$) 上读第 $c_0$ 分量的 `FBA SA (c₀ , tt)`; 带前提的 `tp-rs`; 对 $v$ 单调 (经典取大满足它, 判断); 构造一路的有界版 `Rᵇ`, `upAllᵇ`. 路线状态: 本路没有关闭任何路线.
- **`¬ RaiseA` 不可证 (判断, 元层):** `wlpo→raise` 给出 "`FEA` 与 WLPO ⇒ `RaiseA`", 两个前提经典地成立, 而 Agda 与排中律相容. 同理 `RaiseA → LPO` 若可证, 则 "`FEA` 加 WLPO ⇒ LPO" 可证; 我判断这不可能 (WLPO 严格弱于 LPO, 有外延的模型里也如此; 元层, 未编译). 所以对 `RaiseA` 能指望的最强否定是 WLPO 这一档.

## 第一个障碍 (`RaiseA → WLPO` 为什么没走通)

**[判断]** 三条律都是下界: 输出含 $a$; 可比时含 $v$ (构造一路 `R-in→cmp`: 输出含 $v$ 当且仅当可比). 泄露信息要一个可判定的观察. `NegGenFoldUpd.upd₁-sep` 的观察 (分量的头是不是 $0$) 来自 "留" 这条**上界**律; 本接口与 `FBA` 都没有上界律. `raise-up`, `inflate`, `head-suc`, `head-lim` 说明输出的头形状不被律决定: 任何只读输出有限部分的观察都能被 "外包一层" 改掉. 用 `cmpF` 比较输出里的两个元素也不行: 能放进同一个输出的两个元素, 它们可比这件事在调用 $R$ 之前就已知道. 我试过的族 (都没有得到可判定观察): $a=\omega$, $v_\alpha=\lim_n(\omega_\alpha+n)$ ($\omega_\alpha$ 是在 $\alpha$ 第一个真处偏离 $\omega$ 的树); $a=$ `alim odA`, $v_\alpha$ 在 $\alpha$ 第一个真处从偶数跳到 $\omega_o+n$; 高度版 $a=1$, $v=\Omega$ 在世界 $c_\alpha=\lim(0,\dots,0,1,1,\dots)$ 里. 最后一个说明: 经典的 `RaiseB S₀` 实例要对坐标判定 "$1\lhd c$" (LPO 型), 但我没能从 `RaiseB S₀` 读出这个判定.

**[判断] 连续性.** 我认为在一切函数都连续的模型里 `RaiseAt ω` 不存在 (输出要恰在 $\omega$ 字面出现于 $v$ 时含 $v$, 而这是 $\Pi$ 型), 但没有写成定理; 它是元层论证, 不能当否定用.

## 翻译账

本路不读记号. 新增的定义: `RaiseAt` (接口 `RaiseA` 固定 $a$), `Search` (对角搜索, 树逼出: 合法链只能在有字面证据时从 $a$ 跳到 $v$), `PtDec` (可判定下标上的点更新, 推广 `RaiseCFba.fba₀`), 测试族 `vA`, `vB`, `tω` (否定用的脚手架). 归类 (判断): 提供信息 (否定定理划出不能有的性质; `deq→at` 与 `deqω→WLPO` 把构造的难处钉在 "等于一个 ℕ-极限" 上). 没有改前 3 层.

## 审计

- **编译.** 六个模块各自从仓库根编译, 退出码 0: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegRaise.lagda.md +RTS -M6G -RTS` (冷编译: 先删本路六个模块自己的 `.agdai`, 写精确路径, 依赖用共享接口), 约 4 秒, 峰值常驻约 0.68G.
- **导入闭包.** `python3 probes/Survey/scripts/importclosure.py OCF.Align.NegRaise` (不加 `--only`): 退出码 0, 禁用表命中 0.
- **禁用构造.** 代码块里无 `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `NON_TERMINATING`, `trustMe`, `--cubical`, `--with-K`; 选项行都是 `--safe --without-K --lossy-unification`. `FEA` 只作条件定理的前提.
- **导入.** 只导入 `CumReadCF`, `HtTowerTy`, `HtTowerNeg`, `RaiseIf`, `GenFoldIf` (只用 `FBA`), `RaiseCFba` (只用 `SA`), `RaiseCBd` (只在 `NegRaiseCheck` 对照用), `ColimWNeg` (只用 `WLPO`), `OCF.Barrier` (只用 `LPO`), 与 stdlib.
