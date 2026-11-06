# 层号换类型 (入口与判决): 对一般种类结构的码与折叠接口, 换类型的塔, 对角, ψ₀Λ 候选闭项的骨架

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项". 作者此前选定的方向原话: "A3: 读回包 + 第 ω+1 级折叠"; 本路 (前缀 `LvKt`) 是 [LvTop](LvTop.lagda.md) 接手清单第 1 条 "层号换类型" 的构造一路; 否定一路前缀 `NegLvKt`, 共用接口 [LvKtIf](LvKtIf.lagda.md) (接口定稿 2026-11-05 15:21, 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提. 截断版闭项与证书无模块参数; 条件版以 `FoldTower`, `FoldLimK` 为模块参数.
>
> **判决: 构造成立 (PARTIAL).** 码与折叠接口推广到一般种类结构, 换类型的塔对一切站一条定义, 对角与闭项合法由形状给出. 截断版闭项无条件, 但层号都是 `finK s`, 没有用到新类型里的新种类, 走到与 `LvTop` 截断版同一处. 条件版闭项以 "每站一切码上的折叠" 为前提; 读法 (判断): 前提由真正的折叠给出时读 ψ₀Λ. **不是 ψ₀Λ 已写出.** 第一个障碍是编译过的定理: 真回灌一站之后, 第 1 站的层号不在现有折叠的覆盖之内.
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` (布劳威尔树) 的元素, FGH 在树上算. 纲领 2: 无公理; 塔对站号结构递归 (层号, 合法, 覆盖, 读回同时递归), 码与 `cdLev` 对高度结构递归. 纲领 3: 判定只有码 (数据 `RC`) 的相等, 在同一 (世界, 界) 之下; 嵌入是并的分量注入, 不判定; 不比较两站的值; 极限是对象层的 ℕ-极限 (`hl Bᴧ`, `hl cum`); 没有种类以自身的高度类型为坐标 (`no-retract` 的检查在接口文件头). 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 换类型的塔写成对结构参数 (`FoldAtK` 的族, 回灌部分 `φ`) 的一次定义, 合法由形状给出; 这一站新用到的字段是 `FoldAtK.rt` 作下一站层号的输入 (`LvTop` 里 `rt` 只进极限站的槽) 与 `CdK.w0`, `lw0` (基世界). 种类结构的塔 `Kc` 的形状受目标序数 Λ 的定义 (x ↦ Ω_x 的不动点) 启发, 不来自任何基本列规则 (如实说明).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKt where

import OCF.Align.LvKtCode
import OCF.Align.LvKtIf
import OCF.Align.LvKtTower
import OCF.Align.LvKtInst
import OCF.Align.LvKtVal
import OCF.Align.LvKtTest
```

## 接口原文 (节选, 全文在 `LvKtIf`)

```text
record CdK (S : KS) : Set₁ where          -- LvKtCode: 种类结构的坐标码
  vE : (κ : K S) → Wd S → RC → Set ; vE-prop ; tE ; pE : Bd S κ (tE …) a ; w0 : Wd S ; lw0 : LgW S w0

WbK ck a b = (k : Code a b) → HB (Lev (tgt k))          -- Code a b = Σ RC (vB a b), 界 b : HB K, 世界 a : Wd K

record FoldAtK (K : KS) (ck : CdK K) (Cov : HB K → Set) : Set where
  rt  : ∀ {a b} → LgW K a → LgB b → (c : Code a b) → Cov (tgt c) → (w : WbK ck a b) → LgWbK ck w → HB (Lev (tgt c))
  lrt : … → LgB (rt …)
  H   : ∀ {a b} → LgW K a → LgB b → (c : Code a b) → Cov (tgt c) → (w : WbK ck a b) → LgWbK ck w → Ht
  lgH : … → LgB (H …)

nxt K = sup (⊤ ⊎ HB K) (FN K)        -- FN K (inj₁ _) = K ; FN K (inj₂ c) = Lev c
Kc 0 = S₀ ; Kc (s+1) = nxt (Kc s) ; KΛc = sup ℕ Kc
emb = ι (inj₁ tt) : HB K → HB (nxt K) ; injL c = ι (inj₂ c) : HB (Lev c) → HB (nxt K) ; ιΛ s = ι s
FoldTower = ∀ s → FoldAllK (Kc s) (ckc s) ; FoldLimK = FoldAllK KΛc ckΛ
```

与 `LvTopVal.Kt` 的差别与理由: 见接口文件头 (读回的类型是 `HB (Lev c)` 不是 `HB (Lev (up c))`, 两者对变量 $c$ 不定义相等; 加分量 `K` 本身让嵌入成为分量注入). [判断] 不改变读法, 没有写成定理.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `RC`, `≟RC`, `CdK`, `Codes.vB/tB/pB`, **`Codes.code-≟`**, `Codes.top` | LvKtCode | 对一切种类结构的码; 同一 (世界, 界) 之下相等可判定 | 定义; 定理 |
| `cdS₀`, `cdStep`, `cdSup`, **`cdLev`** | LvKtCode | 码的实例; `Lev` 给出的一切种类结构都有码 | 定义 |
| **`FoldAtK`**, `FoldAllK`, `WbK`, `nxt`, **`Kc`**, `ckc`, `KΛc`, `ckΛ`, `emb`, `injL`, `ιΛ`, `FoldTower`, `FoldLimK` | LvKtIf | 接口 | 定义 |
| `emb-⊲`, `Lg-emb`, `injL-⊲`, `Lg-injL`, `Lg-ιΛ` | LvKtTower §1 | 嵌入保第一位置, 保合法 | 定理 |
| `rtTop`, `HTop`, `lrtTop`, `lgHTop` | LvKtTower §1 | 基世界里顶码上的折叠 | 定义; 合法是定理 |
| **`Two`** (`r0`, `H0`, `B1`, `lB1`, `B1-fst`, `r1`, `H1`, `B2`, `lB2`) | LvKtTower §2 | 两站 (s = 0, 1), 层号依次在 `HB S₀`, `HB (Kc 1)`, `HB (Kc 2)` | 定义; 合法是定理 (前提 `F0`, `F1`) |
| **`Tower`** (`B`, `lB`, `cB`, `rts`, `Hs`, `inc`, **`B-suc`**, **`B-fst`**) | LvKtTower §3 | 对一切站一条: `B (s+1) = emb (B s) ⊞ injL (B s) (φ … (rts s))` | 定义; 定理 (前提 `F`, `φ`) |
| `Bᴧ`, `ΛB`, **`lΛB`**, `cum`, `Λ∞`, **`TΛ∞`**, **`Lg-TΛ∞`**, `Lim.TΛ∞ω`, **`Lim.Lg-TΛ∞ω`** | LvKtTower §4 | 层号对角 (在 `KΛc`), 输出对角, 闭项, 极限站 | 定义; 合法是定理 |
| `FullK` | LvKtTower §5 | 条件版 | 条件 (`FoldTower`, `FoldLimK`) |
| `finK`, **`levFinK`**, `eFK`, `tpK`, `ι-fin`, **`foldFinK`**, **`foldωK`** | LvKtInst §1 | 有限码与 ω 码上的折叠, 对一切 `K` | 构造 |
| `ckt1`, `foldFinKt1`, `foldωKt1`, `foldFinKc1`, `foldωKc1`, `kfin2`, `kωK`, `rt-fin2`, `H-fin2`, `H-ωK` | LvKtInst §2 | `K = Kt 1` 与 `K = Kc 1` 的实例, 具体码上的折叠 | 构造 |
| `covSK`, **`B-finK`**, `Bᴧ-fin`, `covLK`, **`Tkt`**, **`Lg-Tkt`**, `fghKt`, `Tkt∞`, `Lg-Tkt∞` | LvKtInst §3 | 截断版 | 构造; 定理; 无条件 |
| **`Agree.two-B1`**, `two-B2`, `two-H0`, `two-H1` | LvKtVal §1 | 一切站的塔在 s = 0, 1 就是两站的写法 | 定理 (`refl`) |
| `Bᴧ-fst`, **`cum-strict`**, `lim-fst` | LvKtVal §2 | 输入一侧 | 定理 (对任一塔) |
| `val-cum`, `val-cum<`, `val-lim` | LvKtVal §2 | 值一侧 | 条件 (`FstMono T⁺`, `FstMono< T⁺`) |
| **`foldTrivK`**, `FAtriv`, `FLtriv`, **`Ttriv`**, `Lg-Ttriv`, `triv-Hs`, `triv-B1` | LvKtVal §3 | 前提可满足; 接口不决定值 | 定理 (盲) |
| `t-Hs0`, `t-Hs1`, `t-Hs2` | LvKtTest §1 | 截断版前三站与 `LvTopInst.Tr` 定义相等 | 有限测试 |
| `r₀`, `B₁`, `t-new`, `t-new-ne0`, `t-zero`, `t-cells` | LvKtTest §2, §4 | 真回灌一站后, 第 1 站层号里有第 1 级新种类结点 | 有限测试 |
| `ncΩ-fin`, **`no-covF₁`**, **`no-covΩ₁`** | LvKtTest §4 | 第一个障碍: 真回灌的第 1 站层号不在 `foldFinK`, `foldωK` 的覆盖之内 | 定理 (对这一个具体层号) |

## 闭项与 FGH 的类型原文

**截断版 (无条件, 无模块参数):**

```text
LvKtInst.Tkt     : A          -- TrKL.TΛ∞ω = T⁺ (Λ∞ ⊞ Hω) _ ; 各站层号 finK s (在 HB (Kc s)), 极限站层号 ΛB = hl Bᴧ (在 HB KΛc), 码目标 ω
LvKtInst.Lg-Tkt  : Lg Tkt
LvKtInst.fghKt   : ℕ → ℕ      -- FLv.FGH (ord Tkt)
LvKtInst.Tkt∞    : A          -- TrK.TΛ∞ = T⁺ Λ∞ _ ; 只有有限站
LvKtInst.Lg-Tkt∞ : Lg Tkt∞
```

**条件版 (模块参数 `FA : FoldTower`, `FL : FoldLimK`, 起点 `b₀ : HB S₀`, `lb₀ : LgB b₀`):**

```text
LvKtTower.FullK.TΛ∞      : FoldTower → FoldLimK → (b₀ : HB S₀) → LgB b₀ → A      -- 输出对角 (ψ₀Λ 的候选, 读法见下)
LvKtTower.FullK.Lg-TΛ∞   : (FA : FoldTower) (FL : FoldLimK) (b₀ : HB S₀) (lb₀ : LgB b₀) → Lg (FullK.TΛ∞ FA FL b₀ lb₀)
LvKtTower.FullK.fghΛ∞    : FoldTower → FoldLimK → (b₀ : HB S₀) → LgB b₀ → ℕ → ℕ
LvKtTower.FullK.TΛ∞ω, Lg-TΛ∞ω, fghΛ∞ω                                           -- 加极限站 (层号 ΛB : HB KΛc)
LvKtTower.FullK.B        : … → (s : ℕ) → HB (Kc s)                               -- 各站层号, 类型逐站换
LvKtTower.FullK.ΛB       : … → HB KΛc                                            -- 层号对角
```

## 前提实例

- `Tower` 的参数: 截断版 `CovFK`, `foldFinK (Kc s) (ckc s)`, `φ₁` (常数 1), $b_0=0$, `covSK` (定理); 条件版 `λ _ _ → ⊤`, `FA`, `φ = id`, $b_0$ 任意.
- `Lim` 的参数: 截断版 `CovΩK KΛc ckΛ`, `foldωK KΛc ckΛ`, `covLK` (定理); 条件版 `FL`, `tt`.
- **`FA : FoldTower`, `FL : FoldLimK` 可满足**: `FAtriv`, `FLtriv` 是实例, 给出合法闭项 `Ttriv` (所以条件版不空真). 但它们给出的各站输出与读回都是 $0$ (`triv-Hs`, `triv-B1`): 前提可满足不说明值; 条件版的读法要求 `FA` 是真正的折叠 (判断, 下文).
- `Two` 的参数: 实例是 `Agree` 里的 `F 0`, `F 1` (对任一塔).
- `FstMono T⁺`, `FstMono< T⁺`: 同 `LvTopVal`, 对 `T⁺` 未证也未否定.

## 读法 (全部是判断)

记 $|t|$ 为树 $t$ 的树形序数. 沿用 `LvTop` 的两条读法依据: (R1) `Lev t` 的级由 $t$ 的构造子逐个给出, 第 $t$ 级之上的级顶读 $\Omega_{|t|+O(1)}$, 第 $t$ 级的读回与它降到 `Ht` 的输出读同一量级; (R2) `T⁺ h` 读 $\psi_0(\Omega_{1+|h|})$, $|h|$ 是 $h$ 作为下标的读法 (不是 `Ht` 里的树形序数: `LvRd` 的 `T∞F` 读 $\psi_0(\Omega_{\Omega_\omega})$ 就依赖这一点). 有限偏移在下面都略去.

**层号类型的上确界.** `HB (Kc 0) = HB S₀` 的树读 $<\lambda_0=\Omega_2$. `Kc (s+1)` 的种类是 `Kc s` 的种类与一切 `Lev c` ($c$ 取遍 `HB (Kc s)`) 的种类, 后者的坐标读 $<\Omega_{\lambda_s}$; 所以 `HB (Kc (s+1))` 的树读 $<\lambda_{s+1}\approx\Omega_{\lambda_s+1}$. $\sup_s\lambda_s=\Lambda$ ($x\mapsto\Omega_x$ 的第一个不动点). `KΛc` 的树读 $<\Omega_{\Lambda+1}$, 层号对角 `ΛB` 读 $\le\Lambda$.

| 闭项 | 读法 (判断) | 依据, 测到哪里 |
|---|---|---|
| `Tkt∞` | $\psi_0(\Omega_{\Omega_\omega})$ | 前三站输出与 `LvTopInst.Tr` 定义相等 (`t-Hs0..2`, 测试); 各站层号 `finK s` (`B-finK`, 定理); 同 `LvTop` 的 `Ttr∞` 读法 |
| `Tkt` | $\psi_0(\Omega_{\Omega_{\omega+1}})$ 量级 (粗界) | 极限站是 `FΩ` 在 ω 码上的折叠; 与 `LvTop` 的 `Ttr` 不同, 极限站的世界是全 $0$ (没有 W1 的部分和槽); 没有比较两者的定理 |
| `FullK.TΛ∞` (`FA` 是每站一切码上的真折叠) | 上界 $\psi_0(\Omega_\Lambda)=\psi_0(\Lambda)$; 前提由真正的折叠给出且读回的新种类结点随坐标增长时, 读 $\psi_0(\Lambda)$. **不是 ψ₀Λ 已写出** | 上界: 层号 $B_s$ 在 `HB (Kc s)`, $|B_s|<\lambda_s$, 各站输出读 $\Omega_{|B_s|}$ 量级 (R1), 对角读 $\le\Lambda$, 由 (R2). 下界: `B (s+1) = emb (B s) ⊞ injL (B s) (rts s)` (`B-suc`, 定理), 读回 `rts s` 在第 $B_s$ 级, 若它含第 $B_s$ 级的新种类结点且分支沿坐标增长, 则 $|B_{s+1}|\ge\Omega_{|B_s|}$, $|B_s|$ 是 $s$ 层的 Ω-塔, 上确界 $\Lambda$. 测到的: $s=0$, $b_0=1$ 时第 0 站的读回里有新种类结点, 原样进了第 1 站层号 (`t-new`, 测试); 分支是否增长没有测. 这条下界依赖 `FA` (`foldTrivK` 给 $0$) |
| `FullK.TΛ∞ω` | 比 `TΛ∞` 多极限站 (层号 `ΛB`), 上界 $\psi_0(\Omega_{\Lambda+1})$ 量级 | 同上; 极限站的级顶读 $\Omega_{|ΛB|+O(1)}$ |

与 `LvTop` 的对照 (判断): `LvTop` 的全塔版层号在 `HB S₀` 里, 上界 $\psi_0(\Omega_{\Omega_2})$; 这里层号的类型逐站换, 上界升到 $\psi_0(\Lambda)$. 换类型只抬高了上界; 下界仍完全由前提给出.

## 第一个障碍

1. **[定理] 真回灌一站后, 第 1 站不在现有折叠的覆盖之内.** `LvKtTest.no-covF₁ : ∀ n → ¬ (B₁ ≡ finK n)`, `no-covΩ₁ : ¬ CovΩK (Kc 1) (ckc 1) B₁`, 其中 `B₁ = emb 1 ⊞ injL 1 r₀`, `r₀` 是第 0 站 (层号 1, `foldFinK`) 的读回. 原因 (测试 `t-cells`): $B_1$ 的第 2 支里有一个 $\Omega$-结点, 种类是 `(inj₂ 1, inj₂ tt)` (第 1 级的新种类, 坐标取遍 `HB S₀`). 只否定这一个层号在 `CovFK`, `CovΩK` 之内, 不否定别的折叠能覆盖它. 所以截断版只能用常数回灌 (`φ₁`), 层号停在 `finK s`.
2. **缺的折叠 (判断, 未写).** `FoldAtK (Kc 1) (ckc 1) Cov` 在码目标含 `Lev c` 的种类的 $\Omega$-结点 (坐标是高度) 的码上. 已知的相关材料 (主审转告, 本路读了接口, 未复核): `LvOm` 对 `S₀` (坐标 `A`) 写了带外层世界的层结构 `Lv a c` 与读回 `rdW`; 推广到 `Kc 1` 要 (a) 外层世界 $a$ 取 `Wd K` (本接口已把 $a$ 作参数), (b) 坐标是高度时的可入判定 (公共界之下的 `cmpB`), (c) 两种种类折叠的数据树 `D` 的层类型固定在 `Ht`, 坐标是高度的种类没有对应的结点位置; (d) 槽类型若是不带界的 `Lev`, 撞 `NegLvRdLay.no-unifΩ`, 要带外层世界. 本接口的槽类型是 `HB (Lev (tgt c))` ((d) 未处理); 若要带世界的槽, 以只增的方式另加记录.
3. **值.** 没有无条件的值定理; 卡在 `FstMono T⁺` (同 `LvTop`).

报错原文: 无 (第 1 条是编译过的否定, 第 2 条是没写的东西).

## 与否定一路 (`NegLvKt`, 主审转告已复核, 本路未读其代码) 的对照

- **`code-botK`/`code-botΛ` (基世界 `w0` 里码进 Ω-分支只走底支).** 本路一切折叠都在 `a = w0 ck` 里, 只用顶码 (`Codes.top`, 目标是界本身), 世界是全 $0$ (`w₀K`). 所以这条前提对本路的塔成立, 后果是: 层号的 $\Omega$-结构只经 "界本身" 进入折叠 (顶码的槽类型是 `HB (Lev (B s))`, 第 $B_s$ 级的种类取遍 $B_s$ 的一切坐标, 不受外层世界限制); 外层世界限制的只是**别的码**的槽 (回灌到界内部某个子目标的世界分量). 本路的塔不用那些槽, 所以 (判断) 读法的上界不受影响; 但若要像 `LvTop` 的极限站那样把各站读回放进界内部的码的槽, 或让折叠在含 $\Omega$-结点的子目标上回灌, 外层世界必须变大, 本路没有写 (接手清单第 1, 3 条). `LvTop` 的同一选择 (外层 `A`-世界取 $0$) 也落在这条前提上.
- **`no-two-nxt`.** 本路新层号 `emb (B s) ⊞ injL (B s) …` 是加法 (后者接在前者后面), 只声称 `emb (B s)` 是它的第一位置 (`B-fst`), 不撞.
- **`diag-trap`, `stage-not-below`.** 本路对角取部分和 `Bᴧ` (相邻项字面第一位置, `Bᴧ-fst`), 不取注入列 `ιΛ s (B s)`. 本路不声称各站增量是 `ΛB` 的字面第一位置; "层号越过每一站" 在读法里是判断, 不是定理.
- **`no-emb`/`no-copy`.** 本路极限站的世界是全 $0$, 不从各站世界限制而来, 不需要与 `emb` 相干.

## 四层行数表

`probes/Survey/scripts/lvkt/locslice_lvkt.py` (与 `lvtop/locslice_lvtop.py` 同口径: 定义级切片, agda 块非空非注释行; 模块应用的实参与塔的模块内定义手工列为根, 见脚本头). "本路新增" 是 `LvKt*` 模块的行, "树侧全部" 含依赖. 塔的 `B`, `lB`, `cB`, `rts`, `lrts` 是一个互递归块, 切片按块归属, 所以证书的大部分在层 2 已计入.

| 层 | 截断版 `Tkt`: 本路新增 / 树侧全部 / 记号 | 条件版 `FullK.TΛ∞ω`: 本路新增 / 树侧全部 / 记号 |
|---|---|---|
| 1 定义 (码, 世界, 接口, 种类结构的塔; 截断版含 `LvRd` 的码世界与读回包类型) | 185 / 524 / 0 | 191 / 409 / 0 |
| 2 折叠 (塔, 对角, 极限站, 实例, 闭项, FGH) | 338 / 1764 / 0 | 279 / 1241 / 0 (每站一切码上的折叠是前提, 不计) |
| 3 证书 | 349 / 1781 / 0 | 283 / 1251 / 0 |
| 4 律, 形状, 值, 测试 | 536 / 2088 / 0 | 无新增 |

对照 (同口径): `LvTop` 截断版 `Ttr` 前 3 层 1679, 本路截断版 `Tkt` 1781 (+102); 两者读法相近 (判断), 所以这 102 行是 "码对一般种类结构" (`LvKtCode` 的一般化, 约 200 代码行里闭包用到的部分) 与 "塔换类型" 的代价, 不是强度. `LvTop` 全塔版 `FullΛ.TΛ∞` 前 3 层 1387, 本路条件版 `FullK.TΛ∞ω` 1251 (本路不经 `σ₀`, `LvRdWk` 不在闭包里).

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `RC`, `CdK`, `Codes`, `cdS₀/Step/Sup/Lev` | `LvFbCode` 的码只对 `HB S₀`; 塔换类型后界在 `HB (Kc s)` | 树逼出 (界换类型); 一个原始码类型对一切种类结构是写法选择 |
| `FoldAtK` (外层世界作参数) | `LvTopIf.FoldAt` | 树侧, 一般化 |
| `nxt`, `Kc`, `KΛc` | `LvTopVal.Kt`, `HtTowerU.L`; 目标序数 Λ 的不动点形状 | 树侧的类型; 形状受目标序数的定义启发, 不来自任何基本列规则 (如实说明); 多出的分量 `K` 本身是为让嵌入成为分量注入 (脚手架, 判断不改读法) |
| `emb`, `injL` | 层号换类型 | 树逼出 (读回的类型就是下一站种类的坐标所在) |
| `Tower`, `Two` | `LvTopTower.Tower` 的形状, 回灌换成读回本身 | 树侧; `φ` 的选择 (常数 1 / 整个读回) 是判断 |
| `Bᴧ`, `ΛB` (层号在 `KΛc` 里另一列) | `ι s (B s)` 与 `ι (s+1) (B (s+1))` 在不同分量, 不是字面第一位置 (同 `HtTowerNeg.no-naive-diag` 的现象, 本路没有为 `Kc` 重证) | 脚手架 (合法性需要; 与 `B` 共用增量 `inc s`, 定义相等) |
| `levFinK`, `eFK`, `tpK`, `ι-fin` | `Lev (finK n)` 对 `Sk n` 只命题相等 | 脚手架 (两种写法不一致带来, 同 `LvTopInst.Cvt`) |
| `CovFK`, `CovΩK` | 截断版要说清覆盖到哪里 | 脚手架 (条件版是 `⊤`) |

归类 (判断): 提供信息. 换类型的塔写成对结构参数的一次定义, 合法由形状给出, 新用到的字段是 `rt` (作下一站层号) 与基世界; 没有新增读自记号规则的字段. 新的信息: (i) 一条编译过的否定把第一个障碍钉在 "坐标是高度的 $\Omega$-结点上的折叠" (`no-covΩ₁`); (ii) 换类型只抬高读法的上界 (判断), 下界仍全部来自前提. 加深翻译的地方: 无新增; 实例沿用 `LvRd` 的 `GF` 回灌形状 (照搬 `FK`).

## 审计

- **编译.** 七个模块 `OCF.Align.LvKtCode`, `LvKtIf`, `LvKtTower`, `LvKtInst`, `LvKtVal`, `LvKtTest`, `LvKt` 都从头编译过 (首次编译, 无旧接口), 依赖用共享接口, 命令 `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/<文件> +RTS -M6G -RTS`, 退出码都是 0. 审计用的 `--html` 由一个 scratch 模块 (导入 `OCF.Align.LvKt` 与 `OCF.Align.Om1HnAccept`) 生成, 退出码 0.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 七个模块都退出码 0, 禁用表命中 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `LvKtInst:Tkt` 302/0/0, `Lg-Tkt` 307/0/0, `fghKt` 320/0/0, `Tkt∞` 287/0/0, `foldFinK` 347/0/0, `foldωK` 355/0/0, `covLK` 154/0/0, `covSK` 119/0/0, `B-finK` 145/0/0; `LvKtTower:TΛ∞` 285/0/0, `Lg-TΛ∞` 289/0/0, `TΛ∞ω` 300/0/0, `Lg-TΛ∞ω` 304/0/0, `ΛB` 146/0/0, `B` 141/0/0; `LvKtVal:Ttriv` 302/0/0, `val-lim` 314/0/0; `LvKtTest:no-covΩ₁` 400/0/0; `LvKtIf:FoldAtK` 81/0/0; `LvKtCode:code-≟` 20/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用的实参 (`TrK`, `TrKL`, `FullK`, `FT`): `Tkt` 的切片不经过 `foldFinK`, `foldωK`, `covLK`, `covSK`, 所以它们单列为根 (都是 0).
- **禁用构造**: 七个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延; 没有 UIP 作前提.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `LvKtCode` | 202 / 284 | 对一般种类结构的码 |
| `LvKtIf` | 58 / 129 | 接口 |
| `LvKtTower` | 141 / 238 | 嵌入的律, 两站, 一切站, 对角, 闭项, 条件版 |
| `LvKtInst` | 125 / 204 | 有限码与 ω 码上的折叠 (一切 K), `Kt 1`/`Kc 1` 实例, 截断版 |
| `LvKtVal` | 64 / 115 | 两站与一切站一致, 值, 盲, 前提可满足 |
| `LvKtTest` | 65 / 118 | 有限测试, 第一个障碍的否定 |
| `LvKt` | 8 / 本文件 | 入口 |
| `probes/Survey/scripts/lvkt/locslice_lvkt.py` | — | 行数脚本 |

## 接手清单

1. **`Kc 1` 上含高度坐标 $\Omega$-结点的码上的折叠** (第一个障碍第 2 条). 照 `LvOm` 的 "读世界 + 公共上界之下判定" 的形状推广到 `Wd K`, 先对 `Kc 1` 写; 带外层世界的槽类型以只增的方式加进 `LvKtIf` (新记录, 不改 `FoldAtK`). 写出后用它替换 `Two` 的 `F1`, 第一站即可真回灌 (`no-covΩ₁` 说明现有折叠不行).
2. **数据树的层类型.** 两种种类折叠的数据树 `D` 的层固定在 `Ht`; 坐标是 `HB (Kc s)` 一类高度的种类要么有对应的层类型, 要么有从 `HB (Lev c)` ($c$ 在 `HB (Kc s)`) 到 `Ht` 的下降 (`LvRdIf.Dn` 的推广).
3. **极限站的世界.** 现在是全 $0$; 换成 `LvTop` 的 W1 部分和槽要先把各站读回 `rts s : HB (Lev (B s))` 搬到 `Lev (Bᴧ s)` 的分量里 (`B s` 与 `Bᴧ s` 不同类型; 可写 `ρ s : HB (Kc s) → HB KΛc` 的逐结点映射).
4. **`Kc` 与 `Kt`.** 多出的分量不改读法是判断; 若要定理, 写 `HB (Kt s)` 与 `HB (Kc s)` 之间的结构映射 (要 `Lev (up c)` 对 `Lev c` 的逐结点搬运, 同 `LvTopInst.Cvt`).
5. **值.** `FstMono T⁺` 落地后 `val-cum`, `val-cum<`, `val-lim` 成为无条件定理.
