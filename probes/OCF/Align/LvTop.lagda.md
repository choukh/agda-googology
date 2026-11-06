# 整座塔加对角 (入口与判决): 部分和塔, 极限站, 对角, ψ₀Λ 候选闭项的骨架

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项". 作者此前选定的方向原话: "A3: 读回包 + 第 ω+1 级折叠"; 本路是它的续作 (单路, 前缀 `LvTop`): 把 [LvRd](LvRd.lagda.md) 的逐站构造合成整座塔加对角. 接口 [LvTopIf](LvTopIf.lagda.md) (接口定稿, 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提. 截断版闭项与证书无模块参数; 全塔版以 `FoldAll` 为模块参数 (条件).
>
> **判决: 骨架成立 (构造); 截断版闭项无条件; 全塔版闭项是条件的; 读法 (判断) 全塔版低于 ψ₀Λ. 不是 ψ₀Λ 已写出.**
>
> 1. **接口 `FoldAt Cov` (定义).** "在码目标 $c$ 上的一级折叠": 输入界 $b$, 码 $c$ (`Code 0 b`), 覆盖证据, $c$ 所在的世界 (界之下每个码一个槽, 槽类型 `Lev (tgt k)`); 输出级顶的读回 `rt` 与回灌输出 `H : Ht`, 两条律只说输出合法. 每条律只含一个码, 码自带字面的界 (定义域写在接口文件头).
> 2. **整座塔 (构造 + 合法由形状给出, 以 `FoldAt` 为前提).** [LvTopTower](LvTopTower.lagda.md) `Tower`: $B_0=b_0$; 第 $s+1$ 站在 $B_s$ 的顶码上折叠得 $H_s$; $B_{s+1}=B_s\boxplus\sigma(H_s)$ (`lvShapeδ` 的形状; 第 $s+1$ 站的码在新界之下目标是旧界, `κ-tgt`). 极限站: 极限界 `Bω = hl psum` (W1 的部分和, `psum≡B`); 各站的码经 `NegLvRdWk.Canon.canon` 进极限, 相干 (`stageω-coh`), 保目标 (`stageω-tgt`); 极限码的槽是各站读回从出生的那一站 (`ι s`) 直接进极限再取部分和 (`slotω`, `lslotω`). 对角 `Λ∞ = hl cum` (各站输出累加, 对照 `FamFoldAll.Λ∞`), 闭项 `TΛ∞ = T⁺ Λ∞ _`, 加极限站 `TΛ∞ω = T⁺ (Λ∞ ⊞ Hω) _`; 合法 (`Lg-TΛ∞`, `Lg-TΛ∞ω`) 只用 `FoldAt` 的两条律与 `Lg-⊞`, `⊞-fst`, `Lg-ι`.
> 3. **截断版 (无条件闭项).** [LvTopInst](LvTopInst.lagda.md): `foldFin` (码目标字面地是 `fin n`; `LvRdFold.FF`), `foldω` (码目标是 `hl f`, 逐项 `f n ≡ fin n`; `LvRdFold.FΩ`), 合并 `foldTr`. 读法取常数 $1$ 时各站的界是 `fin s` (`B-fin`), 极限界在 ω 码的覆盖之内 (`covL`). 塔走到: 一切有限站 (第 $1,2,\dots$ 级), 对角, 再加极限站 (第 $\omega+1$ 级). 闭项 `Ttr`, 证书 `Lg-Ttr`, FGH `fghTr`; 只有有限站的对角 `Ttr∞`. 这一版 "层号由回灌给出" 是空的 (常数读法).
> 4. **全塔版 (条件闭项).** `FullΛ F b₀ lb₀` (读法 `σ₀`): 闭项 `TΛ∞`, `TΛ∞ω`, 证书, FGH. 缺的前提是 `F : FoldAll`.
> 5. **值 (b).** [LvTopVal](LvTopVal.lagda.md): 输入一侧定理 (`cum-strict`, `lim-fst`, `B-fst`); 值一侧只有条件定理 (`val-cum`, `val-cum<`, `val-lim`, 前提 `FstMono T⁺` / `FstMono< T⁺`); 盲定理 `foldTriv`, `triv-Hs` (接口不决定值). **没有无条件的值定理, 没有序数值验收.** 有限测试 [LvTopTest](LvTopTest.lagda.md): `σ₀` 把第 1 级的级顶读成 ℕ-极限, 测到的支 ($0,1,2,3,5$) 都是 $0$.
> 6. **读法 (判断, 下文 "读法").** 截断版 `Ttr` 读 $\psi_0(\Omega_{\Omega_{\omega+1}})$ 量级 (同 `T∞ω1`, 粗界). 全塔版: 即使 `FoldAt` 对一切码成立, 层号是 `HB S₀` 的树, 判断读法 $<\psi_0(\Omega_{\Omega_2})$, **低于 ψ₀Λ**. 层号逐站换类型的写法 `Kt (s+1) = Lev (Ωtop (Kt s))`, `KΛ = sup ℕ Kt` 已编译 (只是定义).
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` (布劳威尔树) 的元素, FGH 在树上算. 纲领 2: 无公理; 塔对站号结构递归 (界, 合法性, 覆盖, 输出同时递归), 折叠沿用 `LvRd` 的结构递归. 纲领 3: 判定只有码的数据判定 (对码的构造子分情形, `canon` 的 `prefix?`); 不比较不同世界里的值; 极限是对象层的 ℕ-极限 (`hl psum`, `hl U`, `hl cum`). 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 塔与对角对结构参数 (`FoldAt`, 读法 `σ`) 写一次, 合法由形状给出, 新用到的字段是 `FoldAt.lrt`, `FoldAt.lgH`; 判断 "全塔版低于 ψ₀Λ" 来自树侧的类型 (`Lev` 对层号树形递归), 不看记号的基本列.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvTop where

import OCF.Align.LvTopIf
import OCF.Align.LvTopTower
import OCF.Align.LvTopInst
import OCF.Align.LvTopVal
import OCF.Align.LvTopTest
```

## 接口 `FoldAt` 原文

```text
Cod : HB S₀ → Set
Cod b = Code azero b

Wb : HB S₀ → Set
Wb b = (k : Cod b) → HB (Lev (tgt k))

LgWb : ∀ {b} → Wb b → Set
LgWb w = ∀ k → LgB (w k)

record FoldAt (Cov : HB S₀ → Set) : Set where
  field
    rt  : ∀ {b} → LgB b → (c : Cod b) → Cov (tgt c) → (w : Wb b) → LgWb w → HB (Lev (tgt c))
    lrt : ∀ {b} (lb : LgB b) c (cv : Cov (tgt c)) w (lw : LgWb w) → LgB (rt lb c cv w lw)
    H   : ∀ {b} → LgB b → (c : Cod b) → Cov (tgt c) → (w : Wb b) → LgWb w → Ht
    lgH : ∀ {b} (lb : LgB b) c (cv : Cov (tgt c)) w (lw : LgWb w) → LgB (H lb c cv w lw)

FoldAll : Set
FoldAll = FoldAt (λ _ → ⊤)
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Cod`, `Wb`, `LgWb`, **`FoldAt`**, `FoldAll` | LvTopIf | 码, 世界, 在码目标上的一级折叠 | 定义 |
| `top`, `w₀`, `tpL`, `lg-tpL` | LvTopTower §0 | 顶码, 全 0 世界, 逐元素搬运 | 定义; 定理 |
| **`Tower.B`, `Tower.Hs`, `Tower.rts`**, `lB`, `cB`, `lHs`, `lrts` | LvTopTower §1 | 塔: 界, 输出, 读回, 合法, 覆盖 (同时递归) | 定义; 定理 (前提 `FoldAt`) |
| `Tower.κ`, **`κ-tgt`**, `B-fst` | LvTopTower §1 | 第 $s+1$ 站的码在新界之下, 目标是旧界; 界逐站是第一位置 | 定理 |
| `psum≡B`, `Bω`, `lBω`, `stageω`, **`stageω-tgt`**, **`stageω-coh`** | LvTopTower §2 | W1 的极限界; 各站的码经 `canon` 进极限, 保目标, 相干 | 定理 |
| `rtP`, `U`, `slotω`, **`lslotω`**, `Wω`, `lWω` | LvTopTower §2 | 极限码的槽: 各站读回从出生的那一站进极限的部分和 | 定义; 合法是定理 |
| `cum`, `Λ∞`, **`TΛ∞`**, **`Lg-TΛ∞`**, `fghΛ∞` | LvTopTower §3 | 对角与闭项 | 定义; 合法是定理 (前提 `FoldAt`) |
| `Lim.Hω`, `Λ∞ω`, **`TΛ∞ω`**, **`Lg-TΛ∞ω`**, `fghΛ∞ω` | LvTopTower §3 | 极限站与闭项 | 同上 (前提再加一个覆盖 `Bω` 的 `FoldAt`) |
| `Full` | LvTopTower §4 | 一切码上的折叠给出的塔 | 定义 (前提 `FoldAll`) |
| `levFin`, `tK`, `bE`, `fE`, `bW`, …, **`Cvt.cvt`**, **`Cvt.Lg-cvt`** | LvTopInst §1 | 第 $n$ 级的两种写法之间的搬运 (不要外延) | 定理 |
| **`foldFin`**, **`foldω`**, `foldTr` | LvTopInst §2 | 有限码, ω 码上的 `FoldAt` | 构造 |
| `covS1`, **`B-fin`**, `covL`, **`Ttr`**, **`Lg-Ttr`**, `fghTr`, `Ttr∞`, `Lg-Ttr∞` | LvTopInst §3 | 截断版 | 构造; 定理; 无条件 |
| `FullΛ` (`TΛ∞`, `TΛ∞ω`, `Lg-…`, `fgh…`) | LvTopInst §4 | 全塔版 | 条件 (`F : FoldAll`) |
| **`cum-strict`**, `lim-fst` | LvTopVal §1 | 对角严格高于各部分和; 加极限站不降 | 定理 (对任一 `FoldAt`) |
| `val-cum`, `val-cum<`, `val-lim` | LvTopVal §1 | 值一侧 | 条件 (`FstMono T⁺`, `FstMono< T⁺`) |
| `tr-H0` | LvTopVal §2 | 截断版第 0 站的输出就是 `Hn 0` | 定理 (计算) |
| **`foldTriv`**, **`triv-Hs`** | LvTopVal §3 | 接口不决定值 | 定理 (盲) |
| `Kt`, `KΛ`, `Kt1` | LvTopVal §4 | 层号逐站换类型的种类结构 | 定义; `Kt1` 是定理 (计算) |
| `t-head`, `t-br0`…`t-br5`, `t-H1` | LvTopTest | $\sigma_0$ 在第 1, 2 级级顶上的输出的结构 | 有限测试 |

## 闭项与 FGH 的类型原文

**截断版 (无条件, 无模块参数):**

```text
LvTopInst.Ttr    : A              -- TrL.TΛ∞ω = T⁺ (Λ∞ ⊞ Hω) _ ; 有限站对角加极限站 (码目标 ω, 第 ω+1 级)
LvTopInst.Lg-Ttr : Lg Ttr
LvTopInst.fghTr  : ℕ → ℕ          -- FL.FGH (ord Ttr)
LvTopInst.Ttr∞   : A              -- Tr.TΛ∞ = T⁺ Λ∞ _ ; 只有有限站的对角
LvTopInst.Lg-Ttr∞ : Lg Ttr∞
```

**全塔版 (条件, 模块参数 `F : FoldAll`, 起点 `b₀`):**

```text
LvTopInst.FullΛ.TΛ∞     : FoldAll → (b₀ : HB S₀) → LgB b₀ → A
LvTopInst.FullΛ.Lg-TΛ∞  : (F : FoldAll) (b₀ : HB S₀) (lb₀ : LgB b₀) → Lg (FullΛ.TΛ∞ F b₀ lb₀)
LvTopInst.FullΛ.fghΛ∞   : FoldAll → (b₀ : HB S₀) → LgB b₀ → ℕ → ℕ
LvTopInst.FullΛ.TΛ∞ω    : FoldAll → (b₀ : HB S₀) → LgB b₀ → A        -- 加极限站
LvTopInst.FullΛ.Lg-TΛ∞ω, FullΛ.fghΛ∞ω                                -- 同上
```

## 前提实例

- `Tower` 的参数: 截断版 `CovF`, `foldFin`, 读法常数 $1$, $b_0=0$, `covS1`; 全塔版 `λ _ → ⊤`, `F`, `σ₀`, `lσ₀` (`LvRdWk`), $b_0$ 任意 (实例 $b_0=0$, `tt`).
- `Lim` 的参数: 截断版 `CovΩ`, `foldω`, `covL` (定理); 全塔版 `F`, `tt`.
- **`F : FoldAll` 可满足**: `foldTriv` 是实例 (所以全塔版不空真). 但 `foldTriv` 给出的塔每站输出都是 $0$ (`triv-Hs`): 前提可满足不说明值; 全塔版的读法要求 `F` 是真正的折叠 (判断, 下文).
- `FstMono T⁺`, `FstMono< T⁺`: 同 `LvRdVal`, 对 `T⁺` 未证也未否定; 律的形状对别的函数可满足 (`NegTpMonoBlind.rk-laws`).

## 读法 (全部是判断)

记 $|t|$ 为层号树 $t$ 的树形序数. 依据 (都是判断): (R1) `Lev t` 的级由 $t$ 的构造子逐个给出 (`hs` ↦ `step`, `hl` ↦ `sup ℕ`, `hΩ` ↦ `sup A`), 所以第 `tgt c` 级之上的级顶 `Ωtop (Lev t)` 读 $\Omega_{|t|+1}$; 这与 `LvRd` 的读法表一致 (`Hn n` 的部分和读 $\Omega_\omega$, `Hω1` 读 $\Omega_{\omega+1}$). (R2) `T⁺ h` 读 $\psi_0(\Omega_{1+|h|})$, $|h|$ 是 $h$ 作为下标的读法 (`HtTowerFClosed` 的读法).

| 闭项 | 读法 (判断) | 依据, 测到哪里 |
|---|---|---|
| `Ttr∞` | $\psi_0(\Omega_{\Omega_\omega})$ | 第 0 站就是 `Hn 0` (`tr-H0`); 第 $m+1$ 站与 `Hn (m+1)` 同一个折叠, 只差世界写成 `raise v₀ (kfin (m+1)) 0` (在具体的码上计算与 `v₀` 相同, 作为函数不定义相等); 与 `LvRdFold.T∞F` 的读法同. 没有比较两者的定理 |
| `Ttr` | $\psi_0(\Omega_{\Omega_{\omega+1}})$ 量级 (粗界) | 极限站是 `LvRdFold.FΩ` 在码 `kω` 上的折叠, 槽是各站读回的部分和 (同 `V∞` 的写法, 多一个第 0 项 `ι 0 0`); 与 `T∞ω1` 的读法同 |
| `FullΛ.TΛ∞` ($F$ 是一切码上的真折叠) | $<\psi_0(\Omega_{\Omega_2})$; **不是 ψ₀Λ** | 层号 $B_s$ 是 `HB S₀` 的树 (类型 `Tower.B : ℕ → HB S₀`; 码的界也是 `HB S₀`), $|B_s|<\Omega_2$, 可数个的上确界仍 $<\Omega_2$; 由 (R1) 各站输出读 $\Omega_{|B_s|+1}$, 对角读 $\Omega_{\sup|B_s|}$, 由 (R2) 闭项 $<\psi_0(\Omega_{\Omega_2})$. 这条上界与 `F`, `σ-of` 的选择无关. 下界依赖 `F` 与 `σ` (`foldTriv` 给 $0$); 用 `σ₀` 且 $b_0=0$ 时, 第 1 站的增量在测到的支上是 $0$ (`LvTopTest`) |
| `FullΛ.TΛ∞ω` | 比 `TΛ∞` 多一个 $\Omega_{\sup|B_s|+1}$, 仍 $<\psi_0(\Omega_{\Omega_2})$ | 同上 |

**ψ₀Λ 要什么 (判断).** $\Lambda=\sup\{\Omega_1,\Omega_{\Omega_1},\dots\}$ 要层号本身越过 $\Omega_2,\Omega_{\Omega_2},\dots$; 层号若是 `HB S₀` 的树就做不到 (R1). 树侧的写法是层号逐站换类型: 第 $s+1$ 站的层号取第 $s$ 站那一级的高度, `Kt (s+1) = Lev (Ωtop (Kt s))` (第 1 站 `Kt 1 = Lev (Ωtop S₀)` 就是以 `HB S₀` 的一切层号为下标的各级之并, 本路的整座塔都在它的分量里, `Kt1`), `KΛ = sup ℕ Kt`. 读法 (判断): `HB (Kt s)` 的级读到 $\Omega_{\Omega_{\cdots}}$ ($s$ 层), `KΛ` 的级数读 $\Lambda$. `Kt`, `KΛ` 已编译, 没有在它们上面折叠.

## 第一个障碍

1. **层号的类型 (结构, 判断).** 接口 `FoldAt` 的码是 `Code 0 b`, $b$ 在 `HB S₀` 里 (沿用 `LvFbCode`, `LvRdIf.Stages`, `LvShape` 的类型); 所以整座塔的层号都 $<\Omega_2$ (读法 R1). 要以 ψ₀Λ 为目标, 码与世界要对一般种类结构的界写 (界在 `HB (Kt s)` 里), 塔要按 `Kt` 换类型. `LvFbCode` 的码与 `vB`, `tB`, `pB` 只对 `HB S₀` (坐标 `A`) 写; 推广到 `HB K` (坐标是 `E K κ`) 是下一步. 报错原文: 无 (是没写的东西).
2. **`FoldAll` 本身 (条件定理缺的那一条).** 本路只有码目标字面地是 `fin n` 或 (逐项是 `fin n` 的) `hl f` 的折叠. 缺: (a) 码目标含 $\Omega$-结点 (`A`-分支) 的坐标上的折叠, 那里读回包的层证据要带世界 (`NegLvRdLay.no-unifΩ`), 就是 `LvOm` 一路在做的; (b) 只有后继与 ℕ-极限的一般坐标上的折叠 (对坐标递归: 后继用 `GF` 的形状, 极限用 `dω` 的求值下降与 W1 的槽), 本路没写.
3. **读法 `σ₀` 在第 1 站 (有限测试).** $b_0=0$ 时 $\sigma_0(\Omega_{\mathrm{top}}S_0)$ 测到的支都是 $0$; $\sigma_0(H_1)$ 的第 3 支非零. 这只影响下界, 不影响第 1 条的上界.
4. **值.** 没有无条件的值定理; 卡在 `FstMono T⁺` (同 `LvRd`).

## 四层行数表

`probes/Survey/scripts/lvtop/locslice_lvtop.py` (与 `lvrd/locslice_lvrd.py` 同口径: 定义级切片, agda 块非空非注释行; 模块应用的实参与塔的模块内定义手工列为根, 见脚本头). "本路新增" 是 `LvTop*` 模块的行, "树侧全部" 含依赖.

| 层 | 截断版 `Ttr`: 本路新增 / 树侧全部 / 记号 | 全塔版 `FullΛ.TΛ∞`: 本路新增 / 树侧全部 / 记号 |
|---|---|---|
| 1 定义 (码, 世界, 接口; 截断版含 `LvRd` 的码世界与读回包类型) | 12 / 409 / 0 | 14 / 290 / 0 |
| 2 折叠 (塔, 极限站, 实例, 闭项, FGH) | 211 / 1663 / 0 | 77 / 1338 / 0 (一切码上的折叠是前提, 不计) |
| 3 证书 | 221 / 1679 / 0 | 99 / 1387 / 0 |
| 4 律, 形状, 值, 测试 | 307 / 2021 / 0 | 无新增 |

对照 (同口径, `LvRd` 入口): `LvRdFold.T∞ω1` 树侧前 3 层 1443. 截断版 `Ttr` 前 3 层 1679 (+236): 塔与极限站对一般 `FoldAt` 写 (约 100 行), `Cvt` 搬运脚手架与两个实例 (约 110 行). 两者读法相同 (判断), 所以这 236 行是 "对结构参数写一次" 与 "两种写法的搬运" 的代价, 不是强度.

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `FoldAt` (级顶 → 折叠 → 读回 → 下降) | `LvRdFold` 的 `FF`, `FΩ`, `dnF`, `dω1` 的共同形状 | 树侧, 抽象 (沿用 `LvRd` 的回灌形状) |
| `Tower` ($B_{s+1}=B_s\boxplus\sigma(H_s)$) | `LvRdWk.lvShapeδ`, `St` | 树侧; $\sigma_0$ 的选择是判断 (沿用) |
| 极限站: `hl psum`, `canon`, `ι s` 的部分和 | `LvFbFac.Lim.Inc.U`, `NegLvRdWk.Canon` | 树侧 (W1 与 W2 的极限站) |
| 对角 `cum`, `Λ∞` | `FamFoldAll.Λ∞`, `LvRdFold.ΛF` | 树侧, 沿用 |
| `Cvt`, `levFin`, `toS`, `eF`, `tpL` | `Lev (fin n)` 对 `Sk n` 只命题相等 | 脚手架 (序数值不需要; 两种写法不一致带来, 不来自记号) |
| `CovF`, `CovΩ` | 截断版要说清覆盖到哪里 | 脚手架 (全塔版是 `⊤`) |
| `Kt`, `KΛ` | 目标序数 Λ 的不动点形状 (x ↦ Ω_x) 与 `Lev`, `Ωtop` | 树侧的类型; 形状受目标序数的定义启发, 不来自任何基本列规则 (如实说明) |

归类 (判断): 提供信息. 塔, 极限站, 对角写成对结构参数 (`FoldAt`, 读法) 的一次定义, 合法由形状给出, 新用到的字段只有 `lrt`, `lgH`; 没有新增读自记号规则的字段. 新的信息是一条结构判断: 层号在 `HB S₀` 里的塔读不到 ψ₀Λ, 下一步要换的是层号的类型 (`Kt`), 不是再加一种结点. 加深翻译的地方: 无新增; `FoldAt` 的实例沿用 `GF` 的回灌形状 (照搬 `FK`, 同 `LvRd`).

## 审计

- **编译.** 删本路 6 个模块的 `.agdai` (精确模块名 `OCF.Align.LvTop`, `OCF.Align.LvTopIf`, `OCF.Align.LvTopTower`, `OCF.Align.LvTopInst`, `OCF.Align.LvTopVal`, `OCF.Align.LvTopTest`), 依赖用共享接口, 入口 `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/LvTop.lagda.md +RTS -M6G -RTS`; 退出码见交回报告.
- **导入闭包** (`importclosure.py`, 不加 `--only`): `LvTop`, `LvTopIf`, `LvTopTower`, `LvTopInst`, `LvTopVal`, `LvTopTest` 都退出码 0, 禁用表命中 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `LvTopInst:Ttr` 275/0/0, `Lg-Ttr` 280/0/0, `fghTr` 293/0/0, `Ttr∞` 241/0/0, `foldFin` 349/0/0, `foldω` 358/0/0, `covL` 111/0/0, `foldTr` 394/0/0; `LvTopTower:TΛ∞` 239/0/0, `Lg-TΛ∞` 243/0/0, `fghΛ∞` 257/0/0, `TΛ∞ω` 273/0/0, `Lg-TΛ∞ω` 277/0/0, `Wω` 114/0/0, `stageω-coh` 157/0/0; `LvTopVal:val-cum<` 251/0/0, `triv-Hs` 102/0/0, `KΛ` 65/0/0; `LvTopTest:t-H1` 312/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用的实参 (`Tr`, `TrL`, `FullΛ`): `Ttr` 的切片不经过 `foldFin`, `foldω`, `covL`, 所以它们单列为根 (都是 0).
- **禁用构造**: 六个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延; 没有 UIP 作前提 (`LvRdWorld.at` 的码上 UIP 由 Hedberg 给出, 本路不用 `at`).

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `LvTopIf` | 21 / 61 | 接口 |
| `LvTopTower` | 135 / 230 | 塔, 极限站, 对角, 闭项 (以 `FoldAt` 为参数) |
| `LvTopInst` | 150 / 238 | 搬运, 实例, 截断版, 全塔版 |
| `LvTopVal` | 48 / 96 | 值, 盲, 层号的类型 |
| `LvTopTest` | 41 / 68 | 有限测试 |
| `LvTop` | 7 / 178 | 入口 |
| `probes/Survey/scripts/lvtop/locslice_lvtop.py` | — | 行数脚本 |

## 接手清单

1. **层号换类型.** 把码 (`LvFbCode` 的 `RB`, `vB`, `tB`, `pB`) 推广到一般种类结构 `K` 的界 (`HB K`, 坐标 `E K κ`), 写 `FoldAt` 的 `Kt`-版 (界在 `HB (Kt s)` 里), 塔按 `Kt (s+1) = Lev (Ωtop (Kt s))` 换类型, 对角到 `KΛ`. 这是读法 (判断) 走向 ψ₀Λ 的必要一步; 本路的 `Tower` 与极限站的写法 (部分和, `canon`, `ι s`) 不依赖层号类型的具体形状, 可以照搬 (判断).
2. **`FoldAll` 的两半.** (a) Ω-结点坐标: 等 `LvOm` 的带世界的层证据, 实例化 `FoldAt` 后代入 `FullΛ`; (b) 只有后继与 ℕ-极限的一般坐标: 对坐标递归写 `FoldAt`, 后继用 `GF`, ℕ-极限用 `dω` 式的求值下降, 槽用本路极限站的写法.
3. **去掉搬运脚手架.** 把 `LvRd` 的折叠直接写在 `Lev (tgt c)` 上 (不经 `Sk`, `Gω`), `Cvt` 就不需要.
4. **读法 σ.** `σ₀` 在第 1 站测到 $0$; 换起点 ($b_0=\mathrm{fin}\,1$) 或换读法, 先写有限测试.
5. **值.** `FstMono T⁺` 落地后 `val-cum`, `val-cum<`, `val-lim` 成为无条件定理.
