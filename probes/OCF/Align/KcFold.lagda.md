# 种类塔上的一级折叠 (入口与判决): `FoldTower` 的有内容实例, 只缺下降

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项". 本路 (前缀 `KcFold`) 是 [LvKt](LvKt.lagda.md) 的续作的**构造**一路: 给出 `LvKtIf.FoldTower` 的有内容的实例, 让条件版 `FullK.TΛ∞` 成为无条件闭项. 否定一路前缀 `NegKcFold`, 共用接口 [KcFoldIf](KcFoldIf.lagda.md) (接口定稿 2026-11-05 15:44, 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提. 无条件闭项与证书无模块参数.
>
> **判决: PARTIAL. (a) 交了: 无条件闭项 `Tkc` (经 `LvKtTower.FullK`), 合法由形状给出, 它的 `FoldTower` 实例的读回有内容 (每站真回灌整个读回, 读回含新种类结点, 分支是坐标原样嵌入). (b) 值: 只有逐站的定义相等; 无条件闭项每站的回灌输出就是 `LvKt` 截断版的输出 (`Hs-trunc`), 读回进了层号, 没有进闭项. s = 1 的 "一级折叠" (塌缩: 级顶经数据树折叠, 读回降到 `Ht`) 未走通**: 读回用第 $B_s$ 级的级顶代替 (不是折叠), 回灌输出要的下降 `HB (Lev B₁) → Ht` 没有写. 条件版 `KD dn dnL` 的前提只剩下降 (`DnTower`, `DnLim`). **不是 ψ₀Λ 已写出.**
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` (布劳威尔树) 的元素, FGH 在树上算. 纲领 2: 无公理; 级顶对层号的构造子结构递归, 塔沿用 `LvKtTower` (对站号结构递归). 纲领 3: 本路的定义里没有判定 (级顶不读外层世界, 不进 $\Omega$-分支选支); 接口的可入判定带公共上界 (`BDecK`), 实例来自否定一路 (`NegKcFoldDec.bdecTower`). 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 读回写成对层号构造子的一条定义 (`top`), 对一切种类结构, 对一切站; 这一站新用到的字段是 `step` 的新种类本身 (`Ωtop (Lev c)`: 坐标取遍第 $c$ 级的一切高度). 这是**便宜的增长** (手册 §3.3): 层号塔变高 (读法, 判断), 但闭项只经下降看见它 (`Hs-def`), 无条件实例的下降是常数.

## 接口 (`KcFoldIf`, 只有类型)

```text
LvW a c        : KS           -- LvOm 的 Lv a c 推广到 Wd K: hΩ κ g ↦ sup (Σ x. Bd K κ x a) (step ∘ LvW a ∘ g ∘ proj₁); 极限每支取后继
BDecK K        = ∀ {κ x a W} → Bd K κ x W → a ≤w W → LgW K W → Dec (Bd K κ x a)     ; BDecTower = ∀ s → BDecK (Kc s)
DnK S          = Σ (HB S → Ht) (保合法)     ; DnTower = ∀ s (b : HB (Kc s)) → LgB b → DnK (Lev b) ; DnLim (极限站)
LayK K = HB (step K) ; lyK c = hs (up c)    -- 数据树的层推广到 HB (step K) (只有类型, 未用)
FoldAtKW K ck Cov  (rtW : … → HB (LvW a (tgt c)) ; lrtW ; HW : … → Ht ; lgHW)   ; FoldAllKW, FoldTowerW, FoldLimKW
ForgetK K      = ∀ a → LgW K a → (c : HB K) → Σ (HB (LvW a c) → HB (Lev c)) (保合法)
GrowW K        (embW : a ≤w a′ → LgW K a′ → HB (LvW a c) → HB (LvW a′ c) ; lgEmbW)
WTower         (aW : ∀ s → Wd (Kc s) ; laW ; grow : aW s ≤w aW (s+1) (inj₁ tt))
```

律的定义域写在接口文件头 (每条律至多一对下标, 都带公共上界的证据). 变更: 无. 接口里有而本路没用的: `LvW`/`FoldAtKW` 的桥 `ForgetK` (否定一路: 不能逐结点嵌入, `NegKcFoldForget.no-embForget`, `no-embForgetΩ`; 有限层号上两者逐字相同, `fin-same`), `GrowW` (未实例化), `LayK` (未用).

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `toH`, `sumι`, `Ω₀`, **`top`**, **`Lg-top`** | KcFoldTop §1 | 第 $c$ 级的级顶, 对一切 `K`, 一切 $c$; 合法由形状给出 | 定义; 定理 |
| **`top-above`**, `top-branch` | KcFoldTop §1 | 后继层号的级顶以第 $c$ 级界内的每个高度 (嵌入后) 为字面第一位置; 分支单调 | 定理 |
| `topW`, `Lg-topW` | KcFoldTop §2 | 同一定义在 `LvW a c` 上 | 定义; 定理 |
| **`foldTop`**, `foldTopW`, **`foldTower`**, **`foldLim`** | KcFoldTop §3 | 下降给出折叠: 读回 `hs (top (tgt c))`, 输出 = 下降 (读回); `DnTower → FoldTower`, `DnLim → FoldLimK` | 构造 |
| `KD` | KcFoldTower §1 | 条件版, 前提只有下降 | 条件 (`DnTower`, `DnLim`) |
| `rts-def`, **`Hs-def`**, `X`, **`B-suc-shape`**, **`rts-suc`**, **`B-new`**, **`coord-new`**, `rts-above` | KcFoldTower §2 | 对一切下降, 一切站: 读回是层号的级顶; 输出只经下降看见读回; $B_{s+1}$ 的头是后继; 第 $s+1$ 站读回是新种类结点; $B_{s+2}$ 的头是种类 `(inj₂ B_{s+1}, inj₂ tt)` 的 $\Omega$-结点, 坐标类型是 `HB (Lev X_s)` | 定理 (`refl`) |
| **`B1-shape`**, `X₁`, `comp`, `s1-above`, **`s1-sees`**, `s1-sees-lg`, **`no-covF1`**, **`no-covΩ1`** | KcFoldTower §3 | 第 1 站: 层号头是种类 `(inj₂ 1, inj₂ tt)` 的 $\Omega$-结点; 对每个坐标 $y$ (不只底坐标) 那一支的级顶都在读回之下; 不在现有折叠的覆盖之内 | 定理 |
| `dn₀`, `dnL₀`, `FT₀`, `FL₀`, **`Tkc`**, **`Lg-Tkc`**, **`fghKc`**, `Tkc∞`, `Lg-Tkc∞` | KcFoldTower §4 | 无条件闭项 | 构造; 定理; 无条件 |
| **`Hs-trunc`**, `Hω-trunc` | KcFoldTower §4 | 无条件实例各站与极限站的输出与 `LvKtInst` 截断版定义相等 | 定理 (`refl`) |
| `ftW`, `flW`, `rtW-def`, `bdecS₀` | KcFoldTower §5 | 带世界版的实例; 底上的可入判定 | 构造; 定理 |
| `ht-coords` | KcFoldTower §6 | `Ht` 的种类的坐标类型只有 `A`, `HB S₀` | 定理 |
| `wt₀`, `wtω`, `wtω-sees` | KcFoldTower §7 | 世界塔的实例 (不进闭项) | 构造 |
| `bdecT`, `bdecL`, `bdecLv` | KcFoldBdec | 接口 §2 在一切站, 极限, 一切 `Lev x` 的实例 (导入 `NegKcFoldDec`) | 定理 (否定一路证, 主审复核) |
| `t-cell2`, `t-rt-idx` | KcFoldTest | 在 `LvKtTest.B₁` 上: 第 2 支头是 $\Omega$-结点; 读回第 2 个部分和的头在第 2 分量 | 有限测试 |

## 闭项与 FGH 的类型原文

**无条件 (无模块参数):**

```text
KcFoldTower.Tkc     : A          -- KU.TΛ∞ω, KU = FullK (foldTower dn₀) (foldLim dnL₀) (hs hz) tt
KcFoldTower.Lg-Tkc  : Lg Tkc
KcFoldTower.fghKc   : ℕ → ℕ      -- FLv.FGH (ord Tkc)
KcFoldTower.Tkc∞    : A          -- KU.TΛ∞ (只有有限站)
KcFoldTower.Lg-Tkc∞ : Lg Tkc∞
KcFoldTower.FT₀     : FoldTower  -- foldTower dn₀ ; FL₀ : FoldLimK
```

**条件版 (前提只有下降):** `KcFoldTower.KD (dn : DnTower) (dnL : DnLim)` 是 `FullK (foldTower dn) (foldLim dnL) (hs hz) tt`, 闭项 `KD.TΛ∞`, `KD.TΛ∞ω : A`, 证书 `KD.Lg-TΛ∞ω`, FGH `KD.fghΛ∞ω`.

## 每站真回灌了多少

- **进层号: 整个读回.** `B (s+1) = hs (emb (B s) ⊞ injL (B s) (top (B s)))` (`B-suc-shape`, 对一切下降). 第 $s+1$ 站起的读回是 `hs (Ωtop (Lev X_s))` (`rts-suc`): 新种类结点, 坐标取遍第 $X_s$ 级的一切高度, 坐标 $y$ 处的分支就是 $y$ (`up y`). 第 1 站: 对 `B 1` 的 $\Omega$-结点的每个坐标 $y$, 那一支的级顶都在读回之下 (`s1-sees`); 这是对否定一路 `base-only` (基世界里码只走底支) 的回答: 本路的读回不经码进 $\Omega$-分支, 层号的头是后继, 级顶的坐标类型装着各分支.
- **进闭项: 无条件实例里 $0$ 个读回结点.** 闭项只经下降看见读回 (`Hs-def`); `dn₀` 是常数, 各站输出就是截断版的输出 (`Hs-trunc`, `Hω-trunc`).

## 前提实例

- `DnTower`, `DnLim`: `dn₀`, `dnL₀` (常数, 合法). 所以条件版不空真; 有内容的下降没有.
- `FoldTowerW`, `FoldLimKW`: `ftW`, `flW`. `BDecTower`: `bdecT` (否定一路). `WTower`: `wt₀`, `wtω` (否定一路指出律太弱, `baseW`, `mixW` 也满足; 本路闭项不用世界塔). `GrowW`, `ForgetK`: 没有实例.

## 读法 (全部是判断)

依据沿用 `LvKt` 的 (R1) "第 $t$ 级之上的级顶读 $\Omega_{|t|+O(1)}$" 与 (R2) "`T⁺ h` 读 $\psi_0(\Omega_{1+|h|})$, $|h|$ 是下标读法".

| 对象 | 读法 (判断) | 依据, 测到哪里 |
|---|---|---|
| 层号塔 `KU.B s` | $|B_1|\approx\Omega_2$, $|B_{s+1}|\approx\Omega_{|B_s|}$, 上确界 $\Lambda$ | 形状定理 `B1-shape`, `rts-suc`, `B-new`, `coord-new` (第 $s+2$ 站层号的头的坐标是第 $X_s$ 级的一切高度) + (R1). 只证了形状, 没有值定理 |
| `Tkc∞`, `Tkc` | 与 `LvKtInst.Tkt∞`, `Tkt` 同: $\psi_0(\Omega_{\Omega_\omega})$, $\psi_0(\Omega_{\Omega_{\omega+1}})$ 量级 (粗界). **不读 ψ₀Λ** | 各站输出与截断版定义相等 (`Hs-trunc`, `Hω-trunc`, 定理); 闭项本身没有比较定理 (逐点相等推到 `hl` 要外延) |
| `KD dn dnL . TΛ∞` | `dn` 是忠实的下降 (第 $c$ 级级顶降到 `Ht` 后按 (R2) 读 $\Omega_{|c|}$ 量级) 时读 $\psi_0(\Lambda)$; 上界 $\psi_0(\Lambda)$; `TΛ∞ω` 上界 $\psi_0(\Omega_{\Lambda+1})$ | 层号塔的读法 + `Hs-def`. 依赖 `dn`; `dn₀` 给截断版 |

## 第一个障碍

1. **下降 (未走通).** 回灌输出要第 $B_s$ 级的高度降到 `Ht` (`DnK (Lev (B s))`). 已有的下降只覆盖有限层号与逐项有限的 ℕ-极限 (`dnF`, `dω`); `B 1` 不在它们的覆盖之内 (`no-covF1`, `no-covΩ1`, 定理). 否定一路: 下降不能是种类的嵌入 `Emb (Lev 2) S₁` (`NegKcFoldForget.no-embDn`, 一切站), 要么有损, 要么照 `LvRd.dω` 经 `Run` 求值. 经 `Run` 要数据树的层容得下层号: `Ht` 的种类的坐标只有 `A`, `HB S₀` (`ht-coords`), 而 $B_{s+2}$ 的头的坐标类型是 `HB (Lev X_s)` (`coord-new`); [判断] 第 1 站 (`B 1` 的 $\Omega$-结点坐标是 `HB S₀`) 可以试把 `LvOm` 从 `H₀` 推广到 `Ht` (加 κH 一行), 第 2 站起要数据树的层推广到 `HB (step K)` (`LayK`) 与在一般坐标类型上的走法 (`Cut₀`, `Cut₁` 只对 `A`, `HB S₀`).
2. **读回不是折叠.** `top` 是级顶, 不读槽, 不读外层世界; 真正的一级折叠的读回要数据树 (同上).
3. **值.** 没有无条件的值定理 (`FstMono T⁺`, 同 `LvKt`).

报错原文: 无 (障碍是没写的东西; 写成定理的是 `Hs-def`, `Hs-trunc`, `no-covF1`, `no-covΩ1`, `ht-coords`, `coord-new`).

## 四层行数表

`probes/Survey/scripts/kcfold/locslice_kcfold.py` (与 `lvkt/locslice_lvkt.py` 同口径; 模块应用 `KU`, `KD` 的实参与截断版的塔手工列为根, 见脚本头).

| 层 | 无条件 `Tkc`: 本路新增 / 树侧全部 / 记号 | 条件版 `KD.TΛ∞ω`: 本路新增 / 树侧全部 / 记号 |
|---|---|---|
| 1 定义 | 6 / 536 / 0 | 6 / 415 / 0 |
| 2 折叠 (含截断版的下降) | 68 / 1840 / 0 | 54 / 1334 / 0 (下降是前提, 不计) |
| 3 证书 | 72 / 1861 / 0 | 54 / 1344 / 0 |
| 4 律, 形状, 测试, 带世界版 | 243 / 2258 / 0 | 无新增 |

对照 (同口径): `LvKt` 截断版 `Tkt` 前 3 层 1781, 本路 `Tkc` 1861 (+80, 级顶与由下降给出的折叠); 两者的回灌输出逐站相同, 所以这 80 行没有进闭项的值. `LvKt` 条件版 `FullK.TΛ∞ω` 1251, 本路条件版 1344 (+93, 前提从 "每站一切码上的折叠" 缩到 "每站的下降").

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `top` (级顶) | (R1) 的 "级顶"; `Lev` 的构造子 | 树侧; 用级顶代替折叠的读回是选择 (判断: 同量级) |
| 读回后加 $1$ (`hs (top …)`) | 让层号的头是后继, 级顶的坐标装着各分支, 避开 $\Omega$-头的底支 (`code-botK`) | 选择 (脚手架) |
| `sumι` (部分和) | `diag-trap` | 树逼出 |
| `foldTop` 的 "输出 = 下降 (读回)" | `LvKtInst.foldFinK` 的形状 | 沿用 |
| `dn₀`, `dnL₀` (截断版输出) | 无条件闭项要一个下降 | 脚手架, 不提供值 |
| `LvW`, `BDecK`, `FoldAtKW`, `GrowW`, `WTower`, `ForgetK`, `DnK`, `LayK` | 简报点名的接口; `LvOm`, `bdec`, `LvRdIf.Dn` | 接口类型 |

归类 (判断): 提供信息, 但增长是便宜的. 提供信息的标志: 对结构参数的一步定理 (`rts-suc`, `B-new`, `coord-new`; 新用到 `step` 的新种类); 编译陈述把缺口缩到下降 (`Hs-def`, `Hs-trunc`; 条件版的前提从整个折叠缩到下降). 加深翻译的标志: 无. 手册 §3.3 的幽灵: 层号塔的增长没有进闭项, 已用 `Hs-trunc` 写明.

## 审计

- **编译.** `OCF.Align.KcFoldIf`, `KcFoldTop`, `KcFoldTower`, `KcFoldTest`, `KcFoldBdec`, `KcFold` 都从头编译过 (首次编译, 依赖用共享接口), `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/<文件> +RTS -M6G -RTS`, 退出码 0. 审计的 `--html` 由 scratch 模块 (导入 `OCF.Align.KcFold` 与 `OCF.Align.Om1HnAccept`) 生成, 退出码 0.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 六个模块都退出码 0, 禁用表命中 0.
- **切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `Tkc` 302/0/0, `Lg-Tkc` 307/0/0, `fghKc` 320/0/0, `Tkc∞` 287/0/0, `FT₀` 182/0/0, `FL₀` 193/0/0, `dn₀` 150/0/0, `dnL₀` 162/0/0, `foldTower` 157/0/0, `foldLim` 159/0/0, `Lg-top` 88/0/0, `wtω` 113/0/0, `bdecT` 126/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用的实参: `Tkc` 的数与 `LvKt` 的 `Tkt` 相同 (302), 实参 `FT₀`, `FL₀`, `dn₀`, `dnL₀` 单列为根 (都是 0).
- **禁用构造**: 六个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延, UIP 前提.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `KcFoldIf` | 61 / 136 | 接口 |
| `KcFoldTop` | 84 / 146 | 级顶, 由下降给出的折叠 |
| `KcFoldTower` | 125 / 235 | 条件版, 形状定理, 第 1 站, 无条件闭项, 带世界版, 障碍, 世界塔 |
| `KcFoldTest` | 26 / 44 | 有限测试 |
| `KcFoldBdec` | 12 / 25 | 可入判定的实例 (导入否定一路) |
| `KcFold` | 7 / 本文件 | 入口 |
| `probes/Survey/scripts/kcfold/locslice_kcfold.py` | — | 行数脚本 |

## 接手清单

1. **第 1 站的下降.** `B 1` 的 $\Omega$-结点坐标是 `HB S₀`: 把 `LvOm` (`Lv`, `Ly`, `rdW`, `pk`, `F1`, `Dc`) 从层号在 `H₀` 推广到层号在 `Ht` (加 κH 一行, 外层世界取 `A × H₀`, 可入用 `bdecLv`), 给出 `DnK (Lev (B 1))`, 代入 `KD`.
2. **第 2 站起的下降.** 数据树的层推广到 `HB (step K)` (`LayK`) 与对一般坐标类型的走法, 或照 `dω` 另写求值; 否定一路的 `no-embDn` 排除了逐结点嵌入.
3. **外层世界.** 若折叠要读外层世界, 世界塔要显式构造的、长高的那一个, 并用定理说明看见非底分支 (否定一路: `WTower` 的律满足于 `baseW`, `mixW`); 极限站可用 `limW`, `lim-emb`. 不要写 "读回分量恰好看见外层可入的分支" (`seeExact-sep`).
4. **值.** `FstMono T⁺` 落地后才有 `Tkc` 与 `Tkt` 的比较; 逐点相等推到闭项要外延 (只能作条件).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KcFold where

import OCF.Align.KcFoldIf
import OCF.Align.KcFoldTop
import OCF.Align.KcFoldTower
import OCF.Align.KcFoldTest
import OCF.Align.KcFoldBdec
```
