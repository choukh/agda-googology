# 重开一次封闭的层号: 合法性由形状给出 (判决: PARTIAL)

> 摆脱侧 (结构), 没有攀爬. 入口. 文件: [LFReTy](LFReTy.lagda.md) (块, 种类结构, 读回层), [LFReTower](LFReTower.lagda.md) ($\Omega$, 塔, 不动点, 合法性), [LFReBr](LFReBr.lagda.md) (与 `HtFeed` 的高度互通, 链点, 闭项), [LFReNeg](LFReNeg.lagda.md) (否定). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 没有函数外延. 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签.
>
> **判决: PARTIAL.** 封存的 `LF` (Survey/RouteSeal.md 第 5 条) 用 `HtTower` 的语言重写之后, 一次封闭与形状合法可以同时有; 旧证书在 $\psi_0(\Omega_\Omega)$ 缺的字面合法由和的形状给出; 但 $\psi_0(\Lambda)$ 仍没有序数树, 卡在与 `HtTower` 相同的地方: 没有接受第 1 层以上种类的折叠.
>
> 1. **做到 (定理).** 一个归纳-递归块 `LH`, `Lv : LH → KS` 就是全部层号: `Lv` 是 `HtTowerTy.Lev` 的四行, 定义在层号自己身上. 高度 `HB SL`, `SL = sup LH (step ∘ Lv)`, 与 `HtTowerU.U = sup ℕ (step ∘ L)` 同形, 下标从 $\mathbb N$ 换成层号. 块里没有守卫; 第一位置、合法、比较是 `HtTowerTy` 对一切 `S` 的那一套, 一行没新写 (`cmpL = cmpB {SL}`). $x\mapsto\Omega_x$ 的合法性是一步定理 (`Lg-Ω̂`), 塔、$\Lambda$、$\Omega_{\Lambda+1}$、第 $n$ 个不动点都合法 (`Lg-Λ`, `Lg-ΩΛ+1`, `Lg-Λn`), 不按层, 不按阶段.
> 2. **旧障碍的去向.** `no-cp-Ω3-Ω2` (旧的第一位置只走第一支) 在这里不适用: $\Omega+3$ 是 $\Omega\cdot2$ 的第一位置, 由世界给出 (`cp-Ω3-Ω2`). 链点的字面合法: 第 0 层是 `sum` 的值 (`Lg-chain₀`, `fst-chain₀`), 第 1 层是 `HtOutFeed` 的回灌高度 (`Lg-chain`, `Lg-chainω`), 放进一次封闭的类型仍合法, 来自 `Lg-sum`, `Lg-rd`, 不经 `HS` (所以与 `no-HS→Lgl` 不冲突). 每个种类都有读回层 (`rbl`), 坐标类型就是读回层的值的类型 (`E-rbl`): `HtTower` 第一个障碍的 (iv) 在这里是一个定义加一条定理.
> 3. **过 $\psi_0(\Omega_\Omega)$ 的闭项.** 只用第 0 层新种类的层号 (`Fr`) 读回 `HtFeedTree.H` 保合法 (`Lg-toH`), 用 `HtFeedClosed.TΛ` 折叠: `ψ₀Ω₁`, `ψ₀Ω₁+1`, `ψ₀Ω₁·2`, `ψ₀-chainω` 是类型 `A` 的闭项 (布劳威尔树), 带合法 (`Lg-ψ₀ᴸ`) 与 FGH (`fgh`). 读法 $\psi_0(\Omega_\Omega)$, $\psi_0(\Omega_{\Omega+1})$, $\psi_0(\Omega_{\Omega\cdot2})$ 与 `T-fbω` 的那一个是判断. **折叠是旧的**, 所以这一条说的是 "一次封闭的层号能用现有折叠", 不是新强度.
> 4. **没做到.** $\psi_0(\Lambda)$ 的序数树. `Λ` 在 `HB SL` 里合法, 但现有折叠只接受 `H` (第 0 层的新种类); 第 1 层以上的种类 (坐标是 $\Omega_1$ 以上的值) 要 `HtTower` 第一个障碍的 (i)–(iii). `SL` 是 `KS` 的一个实例, 所以一个对一切 `S` 的折叠 (若有) 直接给 `TΛ_SL Λ Lg-Λ` (判断). **未走通, 不是否定.**

## 定义

| 件 | 定义 | 文件 |
|---|---|---|
| 层号 | `data LH = lz \| ls \| ll (ℕ → LH) \| lΩ (k : LH) (HB (Lv k) → LH)` | LFReTy |
| 种类结构 | `Lv lz = S⊥`, `Lv (ls x) = step (Lv x)`, `Lv (ll f) = sup ℕ (Lv ∘ f)`, `Lv (lΩ k g) = sup (⊤ ⊎ HB (Lv k)) [step (Lv k), Lv ∘ g]` | LFReTy |
| 高度 | `HB SL`, `SL = sup LH (λ k → step (Lv k))`; 新种类 `νL k = (k , inj₂ tt)` 是 $\Omega_{k+1}$ | LFReTy |
| 读回层 | `lvl`, `node`, `rbl`; `ofHB : HB SL → LH`, `toHB`, `upL` | LFReTy |
| $\Omega_x$ | `Ω̂ hz = 1`, `Ω̂ (hs h) = hΩ (νL (ofHB h)) (c ↦ Ω̂ h ⊞ ιL (ofHB h) (up c))`, 两种极限处连续 | LFReTower |
| 塔, 不动点 | `tw (n+1) = Ω̂ (tw n)`, `Λ = hl tw`; `fix b = hl (it b)`, `it b (n+1) = it b n ⊞ Ω̂ (it b n)`; `Λ₂`, `Λn` | LFReTower |
| 互通 | `ofA`, `toA` (第 0 层的值与 `A`), `ofH : H → HB SL`, `toH`, 片段 `Fr` | LFReBr |
| 闭项 | `ψ₀ᴸ h fr l = TΛ (toH h) (Lg-toH h fr l)` | LFReBr |

**布劳威尔树的 View** (AGENTS 纲领第 1 条的解释). `HB SL` 与 `LH` 本身就是布劳威尔树: 每个对象是零, 后继, ℕ-极限或 $\Omega$-极限, 部分在同一类型里. 这里没有差树式的数据层, 所以 View 是恒等, 不需要另写.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| 块 `LH`, `Lv` 过正性与停机检查 | LFReTy | 层号与以层号为下标的种类结构一次封闭 | 定理 (编译事实) |
| `E-rbl`, `E-lvl` | LFReTy | 每个种类的坐标类型 $\equiv$ 读回层的值的类型 | 定理 |
| `Ω̂-suc`, **`Ω̂-⊲`** | LFReTower | $\Omega_h\lhd\Omega_{h+1}$; $x\lhd y\Rightarrow\Omega_x\lhd\Omega_y$, 一切世界 | 定理 |
| **`Lg-Ω̂`** | LFReTower | `LgB h → LgB (Ω̂ h)`, 一切 $h$, 一步 | 定理 |
| `tw-st`, `Lg-tw`, **`Lg-Λ`**, `fix-form` | LFReTower | 塔相邻字面第一位置; $\Lambda$ 合法; $\Omega_\Lambda$ 是 `hl (tw ∘ suc)` | 定理 |
| `Lg-ΩΛ+1`, **`Lg-fix`**, `Lg-Λ₂`, `Lg-Λn` | LFReTower | $\Lambda$ 之上: 一切合法 $b$ 之上的下一个不动点合法 | 定理 |
| `cp-Ω3-Ω2` | LFReTower | 世界的第 0 层界 $\ge2$ 时 $\Omega+3\lhd\Omega\cdot2$ (旧 `no-cp-Ω3-Ω2` 的反面) | 定理 |
| `cmpL` | LFReTower | 一切层号的比较, 就是 `cmpB {SL}` | 定理 (实例) |
| `ofA-⊲`, `toA-⊲`, `Lg-ofA`, `Lg-toA`, `lift`, `liftO` | LFReBr | 第 0 层的值与 `A` 互通 | 定理 |
| `ofH-⊲`, **`Lg-ofH`** | LFReBr | `H` 的合法高度是 `SL` 的合法高度 | 定理 |
| **`Lg-chain`**, `Lg-chainω`, `Lg-chain₀`, `fst-chain₀` | LFReBr | 链点 (折叠输出经和读回) 在 `SL` 里字面合法, 底是第一位置 | 定理 |
| `Fr-⊲`, `toH-⊲`, **`Lg-toH`** | LFReBr | 片段读回 `H` 保第一位置与合法 | 定理 |
| `no-Fr-tw3`, `no-Fr-Λ` | LFReBr | $\Omega_\Omega$ 与 $\Lambda$ 不在现有折叠接受的片段里 | 定理 |
| `ψ₀ᴸ`, `Lg-ψ₀ᴸ`, `ψ₀Ω₁`, `ψ₀Ω₁+1`, `ψ₀Ω₁·2`, `ψ₀-chainω`, `fgh` | LFReBr | 片段层号的 $\psi_0(\Omega_h)$, 类型 `A`, 合法, FGH | 定义; 合法是定理; 读法是判断 |
| **`no-canon`** (`Lg-Wn`, `Lg-dup`) | LFReNeg | 坐标读成规范种类 (`rbl`) 的节点不合法; 前提的世界合法; 重复种类的同一节点合法 | 否定, 定理 (前提有见证) |
| **`no-bare`** | LFReNeg | 不带底的 $\Omega'$: 一切世界里 $\neg(\Omega'_1\lhd\Omega'_2)$ | 否定, 定理 |
| `no-retract-SL` | LFReNeg | `no-retract` 在 `SL` 上: 一次封闭只对层号, 不对坐标 | 否定, 定理 (实例) |

**否定的范围** (详见 [LFReNeg](LFReNeg.lagda.md)). `no-canon` 只对 "一切合法世界" 的 `LgB`, 不否定限制到相容世界后的规范读法 (没有试). `no-bare` 只对种类重复的嵌入. 两条合读: 后继处的底 $\Omega_h\boxplus$ 是逼出来的. 这些都不否定 "一次封闭的层号加形状合法" 这条路线; 它们否定的是写明的两种形状.

**有限测试.** 没有跑. 闭项只编译, 没有对 FGH 的值做 `refl` 测试.

## 第一个障碍

**$\psi_0(\Lambda)$ 要接受第 1 层以上种类的折叠.** `Λ = hl tw`, `tw 3 = Ω̂ Ω₁` ($\Omega_\Omega$) 在坐标 $1$ 处的分支是 `Ω̂ (hs (hs hz))`, 种类 `νL (ls lz)` ($\Omega_2$, 坐标是第 1 层的值), 所以 `tw 3` 与 $\Lambda$ 不在片段里 (`no-Fr-tw3`, `no-Fr-Λ`, 编译), `HtFeedClosed` 的折叠也只认一种闭包 (`HtTower` 第一个障碍 1 的原话: 闭包 `nκ` 的分支以 `A` 的世界为下标). 要的是 `HtTower` 第一个障碍的 (i) 世界换成 `Wd SL`, (ii) 保留时沿新种类坐标的路径走 (路径经过旧种类的 $\Omega$-极限), (iii) 回灌时读第 $\ell$ 层输出作新界. 一次封闭在这里帮到的只有 (iv): 读回层 `rbl` 是定义, 坐标类型对上是定理 (`E-rbl`); 不帮 (i)–(iii). **判断:** `SL` 是 `KS` 的实例, 若有对一切 `S` 的折叠就直接有 `ψ₀Λ`; 若折叠只对 `step S₀` 写 (另一路 `HtTowerF` 在写), 要再推广到 `sup`. 没有写, **未走通**.

旧障碍对照:

| 旧障碍 | 这里 |
|---|---|
| `Un` (名字回路) | 不出现: 块里没有守卫, 没有 `≡` 的索引 |
| `no-Lgl-Ωlim` (跨孩子的步进) | 不出现于高度: 一切层的新种类在同一个 `SL` 里, `Ω̂ (hl f) = hl (Ω̂ ∘ f)` 由 `Ω̂-⊲` 合法. 值这一层 (`HB (Lv (ll f))` 里跨分量的 ℕ-对角) 仍有 `HtTowerNeg.no-naive-diag` 那种现象, 这里没有重证; 这里的后继处不要 $\Omega_x$ 作值 (底是高度 $\Omega_h$), 所以旧的 `top` 不需要 |
| `no-cp-Ω3-Ω2` / `chain-stuck` | 第一位置进 $\Omega$-节点走世界界下的任一坐标 (`cp-Ω3-Ω2`) |
| `no-HS→Lgl` | 链点由和读回, 合法性是 `Lg-sum`, `Lg-rd` (形状), 不经 `HS` |
| `no-tn-ω⁺` (非自然数名字的链变自链) | 种类以层号为下标, 不以 $\mathbb N$ 编号; 链本身属于折叠, 没写, 不知道 |

## 与 `HtTower` 的比较

- **形状 (编译).** `Lv` 的四行就是 `Lev` 的四行 (只在 `lΩ` 多一个分量 `step (Lv k)`, 底换成没有种类的 `S⊥`); `SL` 与 `U` 都是 `sup _ (step ∘ _)`. 差别只在下标: `U` 以 $\mathbb N$ 为下标, 级 `L k` 逐个由 `Lev (Ωtop (L (k-1)))` 给出; `SL` 以层号 `LH` 为下标, `Lv` 在归纳-递归块里与层号一起定义.
- **一次封闭 (编译).** `SL` 是一个 `KS`; `cmpB {SL}`, `Lg-Ω̂`, `Lg-fix` 都是一条定理对一切层; 塔、$\Lambda$、$\Omega_{\Lambda+1}$、$\Lambda_n$ 都在 `HB SL` 里. `HtTowerU` 的 `U` 里没有以 `HB U` 为坐标的种类 (`HtTower` 的判断: 没有 "$\Lambda$ 之上的 $\Omega$"); 这里 `νL (ofHB Λ)` 就是 $\Omega_{\Lambda+1}$ 这个种类. `no-retract` 仍成立 (`no-retract-SL`): 一次封闭是对种类的下标, 坐标仍按层分开. 这回答了第二次路线审查的 R1/P2: 加数类的步骤 (`step`) 不逐级重做, 由 `Lv` 的一次递归给出; 每升一级不加定理, 不加维.
- **映射.** 没有编译 `HB U → HB SL` 的映射: 要一个下标映射 $j:\mathbb N\to$ `LH` 使 `L k` 与 `Lv (j k)` 定义相等, 两边的递归对象不同 (`Lev` 对 `HB S` 递归, `Lv` 对 `LH`), 只能命题相等, 而 `sup` 的字段里有函数, 要函数外延. 判断: 不便宜. 编译了的是第 0 层: `H` (`HtTowerU.toB` 下即 `HB S₀`) 经 `ofH` 合法地进 `SL`, 片段经 `toH` 回来.
- **旧 `LF` 与 `LH`.** 旧 `Raw k` 对应 `HB (Lv k)` (去掉守卫, `em`, `top`); 旧 `lc k c t g` 的下界 $c$ 与第一支 $t$ 对应这里分支的底 ($\Omega_h\boxplus$); 旧 `Pre`/`Low` 对应 `K (Lv k)`/`E (Lv k)`, 旧 `upN` 对应 `node`. 判断, 没有编译映射 (旧的守卫与 `em`, `top` 在这里没有对应物).

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `LH`, `Lv` 一次封闭 | 旧 `LF` 的归纳-递归块 + `HtTowerTy.Lev` | 树侧; `Lev` 的形状按 `HtTower` 的账受作者对下标塔的直觉启发 |
| `lΩ` 一行的分量 `step (Lv k)` | 旧 `Pre (lc …)` 的 `inj₁ (inj₁ _)` | 选择 (判断: 共尾度 $\Omega_{k+1}$ 的层上要有这一种分支); 没有定理 |
| 底 `S⊥` | 使第 $k$ 层的值低于 $\Omega_{k+1}$, 与旧 `Raw` 对齐 | 选择 |
| 去掉守卫, 用世界 | 旧守卫给 `Un`, `no-cp-Ω3-Ω2`; `HtTower` 的世界由壁垒逼出 | 树逼的 (旧否定), 世界照搬 `HtTowerTy` |
| `SL = sup LH (step ∘ Lv)`, 坐标嵌入走自己的分量 (种类重复) | 规范嵌入不合法 | **树逼的** (`no-canon`) |
| `Ω̂` 后继处的底 $\Omega_h\boxplus$ | 不带底塔不单调 | **树逼的** (`no-bare`, 与 `no-canon` 合读) |
| `Ω̂` 极限处连续 | 单调对路径归纳要它 | 树侧 (`HtTowerCont.cont-mono` 同形; 这里没有新证 `drop-Ω` 式的否定) |
| 函数 $x\mapsto\Omega_x$, 塔, $\Lambda$ 作为目标 | 终点 EBO 的下标是 $\Omega$-不动点 | **读自记号** (目标, 不是规则); 定义里没有记号 |
| `fix` 用 ⊞ | $b$ 不一定是 $\Omega_b$ 的字面第一位置 ($\Lambda+1$, $\Omega_\Lambda=\Lambda$) | 判断; 没有定理 |
| `rbl`, `lvl`, `node`, `E-rbl` | 对种类结构递归 | 树侧 |
| `ofH`, `toH`, `Fr`, 闭项 | 现有折叠 `HtFeedClosed` | 无新构造子; 折叠沿用 |

**按 `AGENTS.md` 归类: 提供信息; 摆脱侧 (结构), 没有攀爬.**
- 加深的三个标志: 新构造子或节点字段读自基本列规则: **没有** (没有读任何基本列规则; `LH`, `HB SL` 的构造子是布劳威尔树的四个). 闭包定理新增专属前提: **没有** (`Lg-Ω̂`, `Lg-fix`, `cmpL` 对任意合法参数). 只能用 `Lab` 验收: **不是** (没有验收).
- 提供信息的三个标志: 对结构参数的一步定理: **有** (`Lg-Ω̂` 对 $h$, 新用到的字段是 `sup` 的分量世界与 `step` 的新界; `Lg-fix` 对 $b$; `E-rbl` 对种类). 序数值验收: **没有**. 否定定理划出字段: **有** (`no-canon`, `no-bare`).
- 摆脱了什么: `HtTower` 的 "级以 $\mathbb N$ 为下标, 逐级 `Lev (Ωtop …)`"; 旧 `LF` 的守卫、`em`、`top`、`Un`. 没摆脱的: $\Omega_x$ 与 $\Lambda$ 是记号的目标; 折叠没写.

## 账

行数与审计数字见文件末 "审计" 一节.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LFRe where

open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv; FL; SL; ιL; νL; lvl; node; rbl; ofHB; toHB; upL; E-rbl; E-lvl) public
open import OCF.Align.LFReTower using (Ω̂; Ω̂-suc; Ω̂-⊲; Lg-Ω̂; tw; tw-st; Lg-tw; Λ; Lg-Λ; fix-form; ΩΛ+1; Lg-ΩΛ+1; it; fix; Lg-fix; Λ₂; Lg-Λ₂; Λn; Lg-Λn; Ω₁; cp-Ω3-Ω2; cmpL) public
open import OCF.Align.LFReBr using (no-Fr-tw3; no-Fr-Λ; ofA; toA; ofA-⊲; toA-⊲; Lg-ofA; Lg-toA; lift; liftO; ofH; ofH-⊲; Lg-ofH; chain; Lg-chain; chainω; Lg-chainω; Lg-chain₀; fst-chain₀; Fr; toH; Fr-⊲; toH-⊲; Lg-toH; ψ₀ᴸ; Lg-ψ₀ᴸ; ψ₀Ω₁; ψ₀Ω₁+1; ψ₀Ω₁·2; ψ₀-chainω; fgh) public
open import OCF.Align.LFReNeg using (cn₂; Wn; Lg-Wn; no-canon; Lg-dup; Ω′; no-bare; no-retract-SL) public
```

## 审计

- **导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.SumOne --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.HtOut --only OCF.Align.HtTower --only OCF.Align.LevelFix --only OCF.Align.LevelNoK --only OCF.Align.NoKCert --only OCF.Align.LFRe <模块>`): `LFRe`, `LFReTy`, `LFReTower`, `LFReBr`, `LFReNeg` 退出码都是 0, 禁用表 0, `--only` 之外 0. 入口闭包 27 个模块 (本地 18, 库 9); 本地模块是 `OCF.BTBO`, `OCF.Free.Level`, `CumReadCF`, `HtFeedTree`, `HtFeedHt`, `HtFeedFold`, `HtFeedClosed`, `HtOutRead`, `HtOutFeed`, `HtTowerTy`, `HtTowerCont`, `HtTowerU`, `HtTowerNeg` 与本路五个文件. **没有导入旧的 `LevelFix*`, `LevelNoK*`, `NoKCert*`** (只在讲解里引用).
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `LFReTy:LH` 60/0/0, `LFReTy:Lv` 60/0/0, `LFReTy:E-rbl` 66/0/0, `LFReTower:Lg-Ω̂` 83/0/0, `LFReTower:Lg-Λ` 88/0/0, `LFReTower:Lg-fix` 87/0/0, `LFReTower:cmpL` 64/0/0, `LFReTower:cp-Ω3-Ω2` 77/0/0, `LFReBr:Lg-ofH` 85/0/0, `LFReBr:Lg-chain` 203/0/0, `LFReBr:Lg-chainω` 207/0/0, `LFReBr:Lg-toH` 85/0/0, `LFReBr:ψ₀ᴸ` 180/0/0, `LFReBr:ψ₀Ω₁` 208/0/0, `LFReBr:ψ₀-chainω` 226/0/0, `LFReBr:fgh` 226/0/0, `LFReBr:no-Fr-Λ` 79/0/0, `LFReNeg:no-canon` 82/0/0, `LFReNeg:no-bare` 75/0/0, `LFReNeg:no-retract-SL` 72/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发 (见翻译账).
- **禁用构造**: 五个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`, 无函数外延; 都带 `--safe --without-K --lossy-unification`. 块 `LH`/`Lv` 是大的归纳-递归 (`Lv` 的值域是 `Set₁` 的记录 `KS`), 正性与停机检查直接通过.
- **编译**: 五个文件从源码检查, 入口退出码 0 (依赖用已有接口; 没有跑 `--ignore-interfaces`, 免得与并行的编译争写共享接口).

**分层行数** (定义级切片, 口径同 `htfeed/locslice_htfeed.py`; 脚本复制到临时目录 `lfre/locslice_lfre.py`, 读 `agda --html` 的输出; 计 agda 非空非注释行, 记号模块除外). 层 4 (标签定理) 为空.

| 切片 | 行数 (去共用) | 按模块 |
|---|---|---|
| 层 1 定义: `LH`, `Lv`, `SL`, `Ω̂`, `Λ`, `fix`, `Λn` | 254 (231) | HtTowerTy 155, LFReTy 58, BTBO 23, LFReTower 18 |
| 层 2 + 折叠, 闭项, FGH (`ψ₀ᴸ`, `ψ₀Ω₁…`, `fgh`) | 922 (839), 净增 668 | HtFeedTree 220, HtFeedFold 167, LFReBr 109, Free.Level 56, CumReadCF 36, HtTowerTy 35, HtFeedClosed 22, LFReTower 19, BTBO 4 |
| 层 3 + 合法 (`Lg-Λ`, `Lg-Λn`, `Lg-fix`, `cmpL`, `Lg-ψ₀ᴸ`, `Lg-toH`) | 943 (860), 净增 21 | LFReTower 15, HtFeedClosed 4, LFReBr 2 |
| 只有高度: 层 1 + 合法与比较, 不含折叠 | 321 (298), 净增 67 | HtTowerTy 35, LFReTower 32 |
| + 互通, 链点, `E-rbl` | 净增 184 | HtOutRead 82, LFReBr 53, HtOutFeed 27, LFReTy 22 |
| 否定 (独立切片) | 332 | HtTowerTy 170, LFReNeg 67, LFReTy 44, BTBO 23, HtTowerNeg 18, LFReBr 10 |

- 层 2 的净增几乎全是现有折叠 (`HtFeedTree`, `HtFeedFold`) 与互通 (`LFReBr` 109 行里 `toH`, `Lg-toH`, `Fr`, `ofA`, `toA`, `w₀` 是折叠的入参要的: 折叠的类型要 `LgH`, 所以高度的合法性在层 2, 同 `HtFeed`). 层 3 只多 21 行.
- 对照: `HtTower` 的类型层 (`KS`, `HB`, `step`, `sup`, `Lev`) 208 行, + 塔 243, + 合法 289. 这里 "层 1 + 高度的合法" 321 行, 含一次封闭的块与 $\Lambda$ 之上的不动点; 每升一级 (包括以层号为下标的一切级) 不加行.
- 文件级 (代码块里非空非注释行): `LFReTy` 99, `LFReTower` 75, `LFReBr` 206, `LFReNeg` 80, 入口 6; 共 466.

## 时间线

写定义前读过: `AGENTS.md`, `probes/README.md` 的 "主线与下一步" 与 "翻译账", `Survey/RouteSeal.md` 第 5 条, `LevelFix`, `LevelNoK`, `NoKCert` 的入口, `LevelFixCore`, `LevelFixVal`, `LevelFixNeg`, `SumOneTree`, `CumReadCF` 的定义, `HtFeed` 入口与 `HtFeedTree` 前半, `HtFeedClosed`, `HtOut` 入口与 `HtOutRead`/`HtOutFeed` 的签名, `HtTower` 入口, `HtTowerTy`, `HtTowerCont`, `HtTowerU`, `HtTowerNeg` 的 `no-retract`. 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则. 读法 ($\psi_0(\Omega_\Omega)$ 等) 是按 `HtFeed` 的读法手算的纸面判断.
