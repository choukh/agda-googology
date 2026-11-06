# 种类结构的对应与新种类上的回灌

> 入口. 接 [HtTowerF](HtTowerF.lagda.md) 的第一个障碍. **判决: PARTIAL.** 三件事:
>
> 1. **种类与世界的对应 (摆脱侧, 定理与否定).** 对 `HtTowerU` 的塔 `L`, $k\ge2$ 的 `Need` 没有构造, 也没有否定 (坐标是两个不同的高度类型, 往返相等要对 $\Omega$-分支的函数相等; 判断它与函数外延相容, 所以给不出否定定理). 改塔 `L′ (k+1) = step (L′ k) ⊕ Lev (Ωtop (L′ k))` (下一级字面地含着上一级的 `step`) 之后, **`need′` 对一切 $j<k$ 成立, 世界的对应 `wmatch′` 也成立**, 一条对 $j<k$ 的证明递归的定理, 坐标映射是恒等, 界定义相等. **`no-wmatch`**: 逐分量的并 `U′ = sup ℕ (step ∘ L′)` (`HtTowerU.U` 的做法) 没有保界的世界对应 (同一个 `L′ 2` 的种类在 `U′` 里有两个独立的界). 前提各自可满足 (`sat₀`, `sat₁`).
> 2. **新种类上的回灌 (攀爬, 定理).** `Fb₂ h = rd₂ (h+1) (out₂ h)`: 两种种类的折叠在第 2 层目标上的输出读回 `HB S₁` (`rd₂`, 用 `toD₁ : H₀ → D₁`). `Λs₂ n = Fb₂ⁿ 0`, `Λω₂ = hl Λs₂`, 闭项 **`T-fb₂ω`**, 合法由形状给出; 高度只由新种类的回灌与 ℕ-对角生成, `Λs₂ 1` 的最外是新种类的 $\Omega$-极限 (`Λ₁-ΩH`, `refl`). 增长: 新种类闭包的站严格高于前缀站的任意可数子族 (`Supμ-fb`).
> 3. **一切级一个折叠, 对角闭项: 没有写, 未走通.** 依据第 1 条与 `LFRe` (协调者转来): `LFReTy.SL = sup LH (step ∘ Lv)` 与 `U′` 同形, 世界是独立分量的积; `no-wmatch` 与 `LFReNeg.no-canon` 同向: 在这种并上, 坐标里的种类不能读成大结构里对应的种类 (界对不上). 折叠的读回要的是**相干的世界** (下一级的世界装着上一级的世界, `step` 与 `L′` 的有限级就是这样, `wmatch′`). 所以没有照协调者的建议写 "对一切 `S` 加读回结构的折叠": 那个折叠在 `SL` 上实例化时, 读回结构里的保界一条正是 `no-wmatch` 否定的形状 (判断: 否定的是 `U′` 上的这一对种类; `SL` 上的同一现象由 `no-canon` 给出, 那是 LFRe 的定理).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签.

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 并 | `S ⊕ₖ S′ = sup Bool (two S S′)` | [HtTowerNStage](HtTowerNStage.lagda.md) |
| 带包含的塔 | `L′ 0 = S₀`, `L′ (k+1) = step (L′ k) ⊕ₖ Lev (Ωtop (L′ k))` | 同上 |
| 种类的对应 | `kmComp`, `kmStep`, `kmL`; **`need′ : ∀ k j → j < k → KMatch (step (L′ j)) (L′ k)`** (`KMatch` 用 `HtTowerFNeed` 的) | 同上 |
| 世界的对应 | 类型 `WMatch S S′ M` (`wm : Wd S′ → Wd S`, 界双向, 合法); **`wmatch′`** | 同上 |
| 并的反例 | `U′`, 种类 `κ0`, `κ1`, 共同的像 `K₀`; `no-wmatch`, `sat₀`, `sat₁` | 同上 |
| 读回第 2 层 | `toD₁ : H₀ → D₁`; `nbAᵗ` (旧种类上对 `A` 递归); `rd₂`, `rd₂-fst`, `Lg-rd₂` | [HtTowerNRead](HtTowerNRead.lagda.md) |
| 回灌 | `out₂`, `Fb₂`, `Λs₂`, `Λω₂`; 闭项 `T-fb₂`, `T-fb₂ω`, `fgh`; `ωSt₂` | [HtTowerNFb](HtTowerNFb.lagda.md) |
| 测试 | `same d 2` | [HtTowerNTest](HtTowerNTest.lagda.md) |

`WMatch` 的类型 (协调者要先写的那一个):

```text
record WMatch (S S′ : KS) (M : KMatch S S′) : Set where
  field wm  : Wd S′ → Wd S
        bd→ : ∀ {κ c w′} → Bd S′ (km M κ) (to M κ c) w′ → Bd S κ c (wm w′)
        bd← : ∀ {κ c w′} → Bd S κ c (wm w′) → Bd S′ (km M κ) (to M κ c) w′
        lgw : ∀ {w′} → LgW S′ w′ → LgW S (wm w′)
```

方向: 大结构的世界投影到小结构的世界 (读回时, 当前世界给出被读的高度所在的世界). 协调者写的 `Wd U → Wd (L k)` 是 `S′ = U` 的情形; `no-wmatch` 说 `S′ = U′` 时 (哪怕只要两个种类) 不存在.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| **`need′`** | HtTowerNStage | 对一切 $j<k$: `step (L′ j)` 的种类进 `L′ k`, 坐标恒等, 往返 `refl` | 定理 (对 $j<k$ 的证明递归) |
| **`wmatch′`** | HtTowerNStage | 对一切 $j<k$: 世界投影, 界双向保持 (定义相等), 合法保持 | 定理 |
| `same-kind`, `same-kind′` | HtTowerNStage | `U′` 的 `κ0`, `κ1` 在 `L′ 2` 里是同一个种类 | 定理 (`refl`) |
| **`no-wmatch`** | HtTowerNStage | 没有 `Wd U′ → Wd (L′ 2)` 同时保 `κ1` (一个方向) 与 `κ0` (另一个方向) 的界 | 否定, 定理 |
| `sat₀`, `sat₁` | HtTowerNStage | 只要一个种类时, 双向保界的对应存在 | 定理 (前提的见证) |
| `rd₂-fst`, **`Lg-rd₂`**, `Lg-nbAᵗ` | HtTowerNRead | 第 2 层的树读回成合法的 `HB S₁` 高度, 前提只有底合法 | 定理 |
| `Fb₂`, `fb₂-fst`, `fb₂-st`, `Λs₂`, `Λω₂`, `lΛω₂` | HtTowerNFb | 回灌算子与回灌高度 | 定义; 合法性是定理 |
| `Λ₁-ΩH` | HtTowerNFb | `Λs₂ 1` 的最外是新种类的 $\Omega$-极限 | 定理 (`refl`, 对具体项) |
| `T-fb₂`, **`T-fb₂ω`**, `Lg-T-fb₂ω`, `fgh` | HtTowerNFb | 闭项 | 定义; 合法性是定理 |
| **`Supμ-fb`**, `Sup-fb` | HtTowerNFb | 在 $1\boxplus\Lambda\omega_2$ 上, 新 / 旧种类闭包的站严格高于前缀站的任意可数子族 | 定理 |
| `a9` … `d12` | HtTowerNTest | 见下 | 有限测试 |

**否定的范围.** `no-wmatch` 只说 `U′` 的这两个种类, 只对 "`κ1` 的界推出 `K₀` 的界" 与 "`K₀` 的界推出 `κ0` 的界" 这两个方向同时成立; 不说别的种类映射 (把 `κ0`, `κ1` 送到不同的种类) 不行, 也不说相干世界上的并不行. 它不否定 "对一切级一个折叠" 这条路线, 只否定在独立分量的并上做世界对应.

**为什么不对旧塔 `L` 给否定.** 旧塔的 `Need` 要往返相等 (`fr-to`), 坐标是 `HB (L j)` 与 `HB (Lev (up y))`, 往返相等是两棵高度的相等, $\Omega$-分支处要函数相等. 判断: 有函数外延时可证, 所以在没有它的理论里不能否定; 不写否定, 只写未走通.

## 闭项与读法

**读法都是判断.**

| 闭项 | 高度 | 读法 (判断) |
|---|---|---|
| `T-fb₂ 1` | `Fb₂ 0` $=\mathrm{rd}_2(1,\text{第 2 层输出})$ | $\psi_0(\Omega_{x_1})$, $x_1$ 是 $\psi_2$ 的第一段 (按 `HtOut` 的读法高一级, $x_1\approx\Omega_2^2$) |
| `T-fb₂ (n+1)` | `Fb₂ⁿ⁺¹ 0` | $x_{n+1}\approx\psi_2(\Omega_{x_n})$ |
| `T-fb₂ω` | `hl Λs₂` | $\psi_0(\Omega_{x_\omega})$; 按 Buchholz 读法即 $\psi_0(\Omega_{\Omega_3})$ |

按读法 `T-fb₂ω` 高于 `HtTowerF` 的一切闭项 (那里最高读 $\psi_0(\Omega_{\Omega_2^2})$). 没有定理.

**有限测试** (`same d 2`): `T-fb₂ 1` 对 `T-Ω₂²` 深度 9 同, 10 不同; `T-Ω₂` 对 `T-fb₂ 1` 深度 9 同, 10 不同; `T-fb₂ 2` 对 `T-fb₂ω` 深度 4 同, 5 不同; `T-fb₂ 1` 对 `T-fb₂ 2` 深度 12 同 (没有分辨力).

## 第一个障碍

1. **对角要相干的并.** 有限级 `L′ k` 的世界是嵌套的, 读回所需的对应都有 (`need′`, `wmatch′`). 对角 ($k\to\omega$) 要一个装下一切级的种类结构, 它的世界必须相干: 第 $k+1$ 级的世界投影到第 $k$ 级 (`proj₁ (w true)`) 等于第 $k$ 级的分量. `sup` 的积世界做不到 (`no-wmatch`). 要自己写一个种类结构, 世界是相干的族 ($\Sigma$ 一个族与相干的证明, 或者只用 "从下往上一级一级扩张" 的世界). 没有写. 判断: 相干证明里有世界的相等, 世界里有函数 (`sup` 的分量), 要小心避开函数外延; 用 "扩张生成的世界" (定义相等) 可能避开.
2. **一切级一个折叠.** 在相干世界的结构上, 每个种类要一份 `Cut`/`Walk`/闭包折叠 (`HtTowerF` 对两种种类手写了), 要对种类结构的构造 (`step`, `⊕`, `Lev`) 递归. 没有写.
3. **新种类以上的回灌只到第 2 层.** `Fb₂` 是对 `step S₀` 手写的; 第 $k$ 层的 `rd_k`, `toD_{k-1}` 要上面第 2 条.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `L′` 显式含上一级的 `step` | 读回要坐标类型定义相等 (旧塔 `L` 的 `Need` 要函数外延) | **树逼的** (判断; 旧塔的坐标类型不同是编译事实: `need-1` 之外没有 `refl`) |
| `WMatch` 的投影方向 | 读回时从当前世界取被读高度的世界 | 树侧 |
| 相干世界 | 积世界上的对应不存在 | **树逼的** (`no-wmatch`) |
| `rd₂` 的第 1 层节点读成新种类的分支 | 第 1 层节点的分支吃第 1 层的树, 值是 $<\Omega_2$ 的, 即新种类的坐标 | 树侧, 形状沿用 `HtOutRead.rd` |
| `toD₁` 把 $\mathrm{h\Omega}$ 读成 `nκ` | 第 1 层的树里只有旧种类的闭包 | 选择 (值不忠实) |
| `nμ` 的读回: 界升到 $\mathrm{rd}(w_1,\mathrm{toD}_1\,x)$ | 分支要合法世界, 坐标 $x$ 不一定合法; 经读回一定合法 | **树逼的** (`Lg-rd` 无前提) |
| `top₂ h = 2 ⊞ h`, 第 2 层目标 | 目标要是最高层的第一位置 | 树逼的 (同 `HtOut.top⁺`) |
| `Fb₂` 的底取 $h+1$ | 新高度字面严格高于旧的 | 选择 (同 `HtOut.Fb`) |

**按 `AGENTS.md` 归类.** 第 1 件是摆脱侧 (结构): 一步定理 `need′`, `wmatch′` 对 $j<k$; 否定 `no-wmatch` 划出世界的形状. 第 2 件是攀爬, 提供信息: 加深的三个标志都没有 (没有新构造子, `rd₂` 由节点的层与闭包的种类机械给出; `Supμ` 无专属前提; 没有 `Lab`); 一步定理 `Lg-rd₂` 对一切第 2 层的树, 新用到的字段是第 1 层节点与 `nμ` 的读回.

## 账

**定义级切片** (口径同 `htfeed/locslice_htfeed.py`; 脚本在临时目录 `httower/locslice_httowern.py`).

| 路线 | 层 1 (类型) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) | 加增长 |
|---|---|---|---|---|
| HtOut (一种种类, 回灌), `T-fbω` | 51 | 643 (去共用 560) | 649 (去共用 566) | 892 |
| HtTowerF (两种种类), `T-Ω₂²` | 225 (去共用 202) | 988 (去共用 905) | 996 (去共用 913) | 1347 |
| **HtTowerN (两种种类, 新种类上的回灌), `T-fb₂ω`** | 225 (去共用 202) | 1054 (去共用 971) | 1062 (去共用 979) | 1379 (净增 317) |

- 层 2 按模块: HtTowerFFold 291, HtTowerFTree 264, HtTowerTy 141, HtTowerFRead 75, **HtTowerNRead 73**, Free.Level 56, CumReadCF 36, HtTowerCont 32, **HtTowerNFb 31**, HtTowerFClosed 28, BTBO 27. 与 `HtTowerF` 比, 本路新写的层 2 只有读回与回灌 104 行 (`T-fb₂ω` 不经 `Ω₂ᴴ` 等手写高度, 所以 `HtTowerFClosed` 少一些).
- 层 3 多 8 行. 增长净增 317 行 (HtTowerFGrow 279, TLRuleSpec 24, 本路 14).
- 种类与世界的对应 (`need′`, `wmatch′`, `no-wmatch`, `sat₀`, `sat₁`) 独立切片 287 行, 本路 65 行, 其余是 `HtTowerTy`.
- 文件级 (代码块里非空非注释行): `HtTowerNStage` 87, `HtTowerNRead` 85, `HtTowerNFb` 69, `HtTowerNTest` 21, 入口 5; 共 267.

## 审计

- **导入闭包** (`importclosure.py`, `--only` 表同 `HtTower`): `HtTowerN` (29 个模块, 本地 19), `HtTowerNStage` (17, 本地 8), `HtTowerNRead` (14, 本地 7), `HtTowerNFb` (24, 本地 14), `HtTowerNTest` (32, 本地 22) 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `HtTowerNStage:need′` 73/0/0, `wmatch′` 75/0/0, `no-wmatch` 74/0/0, `HtTowerNRead:Lg-rd₂` 114/0/0, `HtTowerNFb:T-fb₂ω` 232/0/0, `Lg-T-fb₂ω` 236/0/0, `fgh` 250/0/0, `Λ₁-ΩH` 224/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 五个文件无 `postulate`, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用 `--cubical`, 不用函数外延.
- **从头编译** (`--ignore-interfaces`, 堆上限 6G): 入口退出码 0 (32 秒, 1.3G); `HtTowerNTest` 退出码 0 (33 秒, 1.3G).

## 时间线

读过 `LFRe`, `LFReTy` 的 `Lv`, `lvl`, `rbl`, `E-rbl` 与 `LFRe` 入口的定理表 (协调者转来). 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerN where

open import OCF.Align.HtTowerNStage using (_⊕ₖ_; L′; kmComp; need′; WMatch; wmatch′; U′; κ0; κ1; K₀; same-kind; same-kind′; no-wmatch; sat₀; sat₁) public
open import OCF.Align.HtTowerNRead using (toD₁; D₂; rd₂; rd₂-fst; Lg-rd₂) public
open import OCF.Align.HtTowerNFb using (Fb₂; fb₂-st; Λs₂; Λω₂; lΛω₂; Λ₁-ΩH; T-fb₂; T-fb₂ω; Lg-T-fb₂ω; fgh; module ωSt₂) public
```
