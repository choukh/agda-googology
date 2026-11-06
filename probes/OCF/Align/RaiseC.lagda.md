# RaiseC: "一起升" 的升界算子, 构造一路 (入口与判决)

> 不含记号. 本路 (前缀 `RaiseC`) 是 [NewTwr](NewTwr.lagda.md) 第一个障碍 3 (ii) 与接手清单第 2 条的**构造**一路, 与否定一路 `NegRaise` 配对, 共用接口 [RaiseIf](RaiseIf.lagda.md) ("接口定稿 2026-11-05 (主审写, 首次编译通过后定稿)"; 本路没有改它, 没有在末尾加节). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **判决: PARTIAL.**
>
> - **`RaiseA` (无界): 未找到构造性实例; 经典实例是条件定理.** `RaiseCBd.dec→Raise : (∀ a v → Dec (a ⊲ v)) → RaiseA`, 前提推出 LPO (`CumUpClean.dec⊲→LPO`). 编译过的否定只杀写明的候选形状 (下表 §B); **没有** `¬ RaiseA` 的定理, 也没有 `RaiseA → LPO/WLPO`. 所以只能写 "未找到".
> - **`RaiseB S₀`: 同上.** 条件实例 `RaiseCB.DecB.decᴮ→RaiseB₀` (按世界分支的 $\Omega$-结点), 前提推出 LPO (`decᴮ→LPO`). 对一般 `S` (`step`, `sup`): 未找到, 也没有条件实例 (判断: 一般 `S` 的世界不是某个种类的坐标, 上面的 $\Omega$-结点写不出).
> - **有界版 (构造, 无条件).** 律的定义域带字面公共上界时, `A` 上 `RaiseCBd.Rᵇ`, 一切 `S` 上 `RaiseCB.Rᴮᵇ` 都是 "取大", 两条下界律无前提成立, 合法, 仍在上界之下. 在积世界上一起升 (`RaiseCFba.ProdBd.upAllᵇ`) 满足不降, 合法, 保上界, **每个**分量含 $v$, 且是最小的; 具体实例在 `SA` 的世界上 (`exᵇ`, 值用 `refl` 算出).
> - **`upAll` 形状与 `FBA` 的字面律不相容, 对一切 $R$ (定理).** `RaiseCFba.no-fba-upAll`: 在以 `A` 为下标的积世界 `SA = Lev (hΩ tt (λ _ → hz))` 上, 对每个种类 $(c_0,\mathrm{tt})$, 没有 `FBA` 的实例取 `upAll` 的形状. 原因是 `FBA.tp-rs` 无条件. 所以 "一起升" 要用, 就得把 `tp-rs` 换成带前提 $\mathrm{tpA}\,w\lhd v$ 的形状 (`UpLaws.tp-rsᶜ`); 接口 `RaiseA` 恰好是这个带前提的形状所需要的.
> - **有公共上界的世界保不住上界 (定理).** `no-bounded-raise`: 若 $v$ 不在世界的公共上界之下, 任何 (不只 `upAll` 形状的) 升界都不能同时不降, 让第 $c_0$ 个分量含 $v$, 并保有公共上界. 三条两两可满足.
>
> **对纲领与目标.** 纲领 1, 2: 本路只有树上的算子与关于它们的定理, 没有新的闭项, 不产生 $\psi_0(\Omega_x)$ 的强度 (本路的交付 (a) 是有界算子 `Rᵇ`, `Rᴮᵇ`, `upAllᵇ` 与实例 `exᵇ`, 交付 (b) 是它们的值定理与上面的否定). 纲领 3 (壁垒): 本路的结果正是壁垒影子的又一例: 无界的升界要判定 "$a\lhd v$" (`R-in→cmp`: 输出含 $v$ 当且仅当 $a, v$ 可比), 带字面公共上界就可构造 (`Rᵇ`). 纲领 4: 不读记号, 导入闭包与切片见审计. 目标 "让树自足": 本路给出一条树侧的判据: **回灌值 $v$ 必须带着与世界各分量的字面公共上界进来**, 否则 "一起升" 既不能满足 `FBA`, 也保不住上界. 这是对下一版折叠的设计约束 (判断: 折叠的回灌值是否天然在某个上界之下, 未检查).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RaiseC where

import OCF.Align.RaiseCBase
import OCF.Align.RaiseCBd
import OCF.Align.RaiseCFba
import OCF.Align.RaiseCB
```

## 一个基本事实

`A` 的 `⊲` 是自反的子项关系 (`self`, `suc`, `lim` 恰好走进前驱与每一个分支). 所以 $v\lhd R\,a\,v$ 说的是 $v$ 字面地是输出的一棵子树; 合法的树的一切子树两两可比 (`cmpF`). 由此 (`R-in→cmp`, `R-cmp→in`): 对任一 `RaiseA`, 输出含 $v$ 当且仅当 $a, v$ 可比. 也就是说, $R$ 必须**恰好在可比时**把 $v$ 字面地放进输出, 而 "$a, v$ 可比" 不可判定 (判断; `dec⊲→LPO` 是对一切 `A`, 不只是合法的).

## 定理表

### A. 基本事实与 `no-joinA` 的关系 (`RaiseCBase`)

| 名字 | 陈述 | 档 |
|---|---|---|
| `⊲-antisym` | $a\lhd b\to b\lhd a\to a\equiv b$ (经 `irrS : ¬ Strict a a`) | 定理 |
| `R-in→cmp` | `(ρ : RaiseA) → Lg a → Lg v → v ⊲ R ρ a v → (v ⊲ a) ⊎ (a ⊲ v)` | 定理 |
| `R-cmp→in` | 反方向 | 定理 |
| `R-out-evod` | `(ρ : RaiseA) → ¬ (alim odA ⊲ R ρ (alim evA) (alim odA))` | 定理 |

**与 `no-joinA` 的关系 (任务 3).** [定理] `R-out-evod`: 对 `no-joinA` 的那一对, $R$ 的输出一定不含 $v$; 接口只在 $a\lhd v$ 时要 $v\lhd R\,a\,v$, 所以 $R$ 不撞 `no-joinA`. 代价是 `R-in→cmp`: $R$ 必须分辨可比与不可比. [定理] `no-always`: 要求 "总含 $v$" 就撞. [定理] 有界版 `Rᵇ` 的 `Rᵇ-hi` 无前提 (总含 $v$) 也不撞, 因为它要公共上界的证据, 而 `no-joinA` 正是说那一对没有.

### B. 杀掉的候选形状 (`RaiseCBase`, 全部是编译过的否定, 只否定写明的形状)

| 名字 | 被杀的形状 | 违反哪条律 | 实例 |
|---|---|---|---|
| `fst-fails` | $R\,a\,v=a$ | `R-hi` | $a=0$, $v=1$ |
| `snd-fails` | $R\,a\,v=v$ | `R-lo` | $a=1$, $v=0$ |
| `no-on-a` | $R\,a\,v=a\oplus G\,a\,v$ (任意 $G$) | `R-hi` | $a=1$, $v=\omega=\lim(0,1,2,\dots)$ (`ω∉one⊞`) |
| `add-hi-fails` | $a\oplus v$ | `R-hi` | 同上 |
| `no-on-v` | $R\,a\,v=v\oplus G\,a\,v$ ($G$ 保合法) | `R-lo` | `no-joinA` 的一对 |
| `swap-lo-fails` | $v\oplus a$ | `R-lo` | 同上 |
| `no-always` | 满足 `R-lo`, `R-lg` 且总含 $v$ | (三条合起来) | 同上 |
| `no-only-a` | $R\,a\,v=G\,a$ ($G$ 保合法) | `R-hi` | $a=0$, 两个 $v$ |
| `no-only-v` | $R\,a\,v=H\,v$ ($H$ 保合法) | `R-lo` | $v=0$, 两个 $a$ |

正面的半条: `fst-lo`, `snd-hi`, `add-lo`, `swap-hi` (各候选满足的那条律).

### C. 有界版与条件实例 (`RaiseCBd`, `RaiseCB`)

| 名字 | 陈述 | 档 |
|---|---|---|
| **`Rᵇ`** | `a ⊲ Λ → v ⊲ Λ → Lg Λ → A`, 由 `cmpF` 取大 | 构造 |
| `Rᵇ-lo`, **`Rᵇ-hi`**, `Rᵇ-lg`, `Rᵇ-Λ` | $a\lhd R^b$, $v\lhd R^b$ (无前提), 合法, $R^b\lhd\Lambda$ | 定理 |
| `Rᵇ-cases` | $(R^b\equiv a\times v\lhd a)\uplus(R^b\equiv v\times a\lhd v)$ | 定理 (值) |
| `Rᵇ-least` | $a\lhd c\to v\lhd c\to R^b\lhd c$ (字面最小公共上界) | 定理 (值) |
| `Rᵇ-mono`, `Rᵇ-monoa` | 对 $v$, 对 $a$ 单调 | 定理 (值) |
| `Rᵇ-irr`, `Rᵇ-idem` | 与证据无关; 再升一次不动 | 定理 (值) |
| **`R⊵Rᵇ`** | 任一 `RaiseA` 在有界输入上: $R^b\lhd R\,a\,v$ | 定理 (值) |
| `dec→Raise` | `(∀ a v → Dec (a ⊲ v)) → RaiseA` | 条件 (前提推出 LPO, `dec→LPO`) |
| `R-in→cmpᴮ`, `R-out-evodᴮ`, `no-alwaysᴮ` | `HB S` 上同 A 的三条, 对一切 `S` 与合法世界 | 定理 |
| `dW`, `lg-dW`, `lgW-S₀`, `lgW-step` | 合法世界的实例 (每一级 `Lev x`) | 定理 |
| **`Rᴮᵇ`**, `Rᴮᵇ-lo`, `Rᴮᵇ-hi`, `Rᴮᵇ-lg`, `Rᴮᵇ-Λ`, `Rᴮᵇ-least` | 一切 `S`: 带 $w$, $\Lambda$ 证据取大; 在一切 $w'\ge w$ 里两条下界律无前提成立 | 构造; 定理 |
| `DecB.decᴮ→RaiseB₀` | `(∀ a v c → Dec (a ⊲[ c ] v)) → RaiseB S₀`; 输出是 $\Omega$-结点 $c\mapsto(v$ 若 $a\lhd_c v$ 否则 $a)$ (`decᴮ-head`) | 条件 (前提推出 LPO, `decᴮ→LPO`) |

### D. 一起升与 `FBA` (`RaiseCFba`)

| 名字 | 陈述 | 档 |
|---|---|---|
| `SA`, `WdSA`, `≤SA`, `LgSA`, `BdSA` | `SA = Lev {S₀} (hΩ tt (λ _ → hz))`; 世界 `A → A`, 逐分量 | 定义; `refl` |
| `UpLaws.upAll-≤`, `upAll-lg`, `upAll-tp`, `rs≤ᶜ`, `tp-rsᶜ` | 给定 `ρ : RaiseA`: `upAll` 不降 (要合法前提), 合法, $W\,i\lhd v$ 时含 $v$ | 条件 (`RaiseA`, 只经典地可满足) |
| **`no-fba-upAll`** | `∀ c₀ (F : FBA SA (c₀ , tt)) G → (∀ w → tpA F w ≡ w c₀) → (∀ w v c → rsA F w v c ≡ G (w c) v) → ⊥` | 定理 (否定) |
| `fba₀` | `FBA SA (azero , tt)` 的实例 (在可判定的点 $0$ 上点更新): `no-fba-upAll` 否定的是形状, 不是 `FBA` | 定理 (前提实例) |
| **`no-bounded-raise`** | `∀ c₀ rs → Le c₀ rs → Tp c₀ rs → Bk c₀ rs → ⊥` (不降, 含 $v$, 保公共上界) | 定理 (否定) |
| `pair-12`, `pair-23`, `pair-13` | 三条两两可满足 | 定理 (前提实例) |
| `fixed-bound-no-tp` | `tpA` 总在固定 $\Lambda$ 之下时无条件 `tp-rs` 不成立 | 定理 (否定; 前提 `W` 有元素, 例如 `SA` 的任一世界) |
| **`ProdBd.upAllᵇ`**, `upᵇ-≤`, `upᵇ-lg`, `upᵇ-bd`, **`upᵇ-tp`**, `upᵇ-least` | 有界的一起升: 不降, 合法, 保上界, 每个分量含 $v$ (无前提), 最小 | 构造; 定理 |
| **`exᵇ`**, `exᵇ-0`, `exᵇ-1`, `exᵇ-ω`, `exᵇ-≥`, `exᵇ-lg`, `exᵇ-tp` | `SA` 的世界 `sepW azero ωe`, $\Lambda=\omega_e$, $v=2$: 升后第 $0$ 个分量 $=2$, 其余 $=\omega_e$ (`refl`); 比原世界大, 合法, 种类 $(0,\mathrm{tt})$ 的界含 $2$ | 构造; 定理 |

**`tp-rs` 的差别 (照实写).** `FBA.tp-rs : v ⊲ tpA (rsA w v)` 无条件. `upAll` 给的是 `tp-rsᶜ`: 要 $w\,c_0\lhd v$ 与合法. `no-fba-upAll` 说这一差别不能靠选 $R$ 消掉. 有界版 `upᵇ-tp` 无条件, 但要 $v\lhd\Lambda$; `fixed-bound-no-tp` 说固定上界下无条件的 `tp-rs` (对一切 $v$) 不成立, `no-bounded-raise` 说上界也不能随 $v$ 移动.

## 前提实例 (前提要可满足)

- `no-always`, `no-on-v`, `no-only-a`, `no-only-v`: 各前提单独可满足 (例如 `add-lo` 与 `Lg-⊞` 满足 `Lo`, `Gd`; `snd-hi` 的 $R=v$ 满足 "总含 $v$" 与 `Gd`).
- `no-fba-upAll`: `FBA SA (azero , tt)` 有实例 `fba₀`; `tpA` 读第 $c_0$ 个分量是 `fba₀` 的形状; `rsA` 取 `upAll` 形状的单独可满足 (例如 $G\,a\,v=a$ 满足 `rs≤`, `rsLg`).
- `no-bounded-raise`: `pair-12`, `pair-23`, `pair-13`.
- `UpLaws` 与 `R⊵Rᵇ` 的前提 `RaiseA`: 只有条件实例 `dec→Raise` (前提推出 LPO). [判断] 因为排中律与 MLTT 相容, `RaiseA` 不能被否定成 `⊥`; 这些条件定理不是空真, 但在 Agda 里取不到实例.
- `decᴮ→RaiseB₀`, `dec→Raise`: 前提推出 LPO, 经典地可满足 (判断, 元层).

## 判断 (单列)

1. `RaiseA` 没有构造性实例 (判断). 依据: `R-in→cmp` 让 $R$ 恰在 $a,v$ 可比时把 $v$ 字面放进输出; 子树的字面相等不可判定也不半可判定; 连续性的直觉论证 (输入 $v_\alpha$ 在 $\alpha$ 某处为真时才含 $a$, 输出要在极限处突变). 没有编译的 `RaiseA → LPO` 或 `→ WLPO`; 我试过的族 ($a=1$, $v_\alpha=\lim(\mathrm{bit}(\exists k\le n.\,\alpha k))$, 或 $a=\omega_e$, $v_\alpha$ 在命中后越过 $\omega_e$) 都只把 "$\exists k$" 化成 "$v_\alpha\lhd R\,a\,v_\alpha$", 而后者从输出读不出. 交否定一路.
2. 一般 $c_0$ 上的 `FBA SA (c₀ , tt)` (不限 `upAll` 形状): 未否定, 未构造. 它要一个 $G(c, a, v)$, $c=c_0$ 时含 $v$, $c\ne c_0$ 时含 $a$, 合法; 取 $(a,v)$ 为 `no-joinA` 的一对, "$v\lhd G(c,a,v)$" 恰在 $c\equiv c_0$ 时成立 (由 `no-joinA` 与 `cmpF`, 未编译), 与 `NegGenFoldUpd` 的 "留" 同型. 交否定一路.
3. `RaiseB S` 对 `step`, `sup` 的经典实例: 未写. `S₀` 的构造用到 "世界就是坐标"; 一般 `S` 没有以世界为坐标的种类.
4. 有界版的读法: `Rᵇ`, `Rᴮᵇ` 的值就是 $\max(a,v)$ (`Rᵇ-cases`, 定理); `decᴮ→RaiseB₀` 的输出是 $\Omega$-结点, 序数值远大于 $\max(a,v)$ (判断, 没有 `ord` 的比较).

## 穷尽是判断

"无界的 $R$ 只剩 '恰在可比时放 $v$' 这一种, 而它要判定可比" 是判断: `R-in→cmp` 是定理, 但 "因此不可构造" 不是. 我检查过的候选族只有表 B 的那些形状与 "按 $v$ 的结构逐点递归" ($R\,a\,(\lim f)=\lim(R\,a\circ f)$, 纸面上: 若 $R\,a\,w\equiv w$ 在 $a\lhd w$ 时成立, 则在 $\lim f$ 的前几项 $a\not\lhd f\,n$ 处矛盾; 未编译). 下一路先挑战这一判断: 例如找一个不在表 B 里的 $R$ 形状, 或者编译 `RaiseA → WLPO` 一类.

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `Rᵇ` (取大), `Rᴮᵇ` | 律的定义域带字面公共上界 (手册 §3.1), `cmpF`/`cmpB` | 树逼出 |
| `upAllᵇ` | 接口 `ProdA.upAll` 的有界版 | 树逼出 |
| `SA`, `sepW`, `other` | 以坐标为下标的积世界 (`Lev`), 下标的头可判定 | 树侧 (实例与否定用) |
| `dec→Raise`, `decᴮ→RaiseB₀` | 经典的 "取大" | 条件构造 (说明否定只能是非构造原则) |
| `irrS`, `⊲-antisym` | `Strict` 不自反 | 脚手架 (值定理用) |

归类 (判断): 提供信息. 没有新的构造子或节点, 没有读自基本列规则的字段, 不用 `Lab`. 信息是: (i) `FBA` 的 `tp-rs` 无条件与 "一起升" 不相容 (`no-fba-upAll`), (ii) 带上界即可构造且是最小的 (`Rᵇ-least`, `R⊵Rᵇ`), (iii) 上界不能随回灌值移动 (`no-bounded-raise`). 第 4 层没有改前 3 层.

## 审计

- **编译.** 删掉本路五个模块自己的 `.agdai` (逐个写精确路径), 依赖用共享接口, 从仓库根编译入口: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/RaiseC.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 3.9 秒, 峰值常驻约 0.74G (五个模块都重新检查).
- **禁用构造**: `probes/Survey/scripts/raisec/forbid.py` 扫描五个文件的 agda 代码块 (`postulate`, `{!`, `?` 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, `--cubical `, `--with-K`, `Funext`, `funext`).
- **禁用构造结果**: 五个文件命中都是 0 (脚本退出码 0).
- **导入闭包** (`importclosure.py`, 不加 `--only`): 五个模块都退出码 0, 禁用表命中 0. 直接导入只有 `CumReadCF`, `CumReadBase`, `CumUpClean`, `HtTowerTy`, `HtTowerNeg`, `GenFoldIf`, `RaiseIf`, `OCF.Barrier` 与 stdlib.

## 文件

| 文件 | 内容 |
|---|---|
| `RaiseC` | 入口, 判决, 定理表 |
| `RaiseCBase` | 子项的反对称; 可比当且仅当含 $v$; 候选形状的否定 |
| `RaiseCBd` | 有界的 `Rᵇ` 与值定理; `dec→Raise`; `R⊵Rᵇ` |
| `RaiseCFba` | `SA`; `upAll` 的条件律; `no-fba-upAll`, `fba₀`; `no-bounded-raise`; `fixed-bound-no-tp`; `upAllᵇ` 与实例 `exᵇ` |
| `RaiseCB` | `HB S` 上的同形否定; `Rᴮᵇ`; `S₀` 的条件实例与 `decᴮ→LPO` |
| `probes/Survey/scripts/raisec/forbid.py` | 禁用构造扫描 |

## 接手清单

1. **否定一路对准判断 1.** 试编译 `RaiseA → WLPO` (或 LPO, 或 `Sep`); 可以从 `R-in→cmp` 出发 (它把 "可比" 化成 "输出含 $v$"). 若做不到, 照规则写 "未走通".
2. **改回灌的律, 不改折叠的定义.** 若下一版折叠要 "一起升", 把 `FBA.tp-rs` 换成带前提 $\mathrm{tpA}\,w\lhd v$ 的形状 (`tp-rsᶜ`) 或带公共上界的形状 (`upᵇ-tp`). 先查 `GenFoldRun` 里 `tp-rs` 用在哪里, 回灌值 $v$ 那时是否已在世界的某个公共上界之下 (判断 4 的设计约束). 这一步改的是接口, 要作者定 (第 4 层不改前 3 层).
3. **一般 $c_0$ 上的 `FBA SA (c₀ , tt)`** (判断 2): 写成 `NegGenFoldUpd` 的同型否定, 或者找到构造.
4. **`RaiseB` 对 `step`, `sup`**: 有界版 `Rᴮᵇ` 已对一切 `S`; 无界版若要经典实例, 需要以世界为坐标的种类 (判断 3).
