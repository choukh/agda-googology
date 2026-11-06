# 按级回灌 (入口与判决): 每个种类按自己的级回灌

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项". 本路 (前缀 `KindLv`) 是 [NewTwr](NewTwr.lagda.md) 接手清单第 1 条的**构造**一路 (作者选定 "R 与按级回灌一起派"; 原话: "先写 '层 c 的数据 ↔ `HB (Lev c)`' 的读回与写入 (对 c 的构造子递归), 在 `S₀` 与 `step S₀` 上与 `rd₁`/`toD₁` 对照; 再写一个折叠, 对每个旧种类 κ 在第 0 层目标下按 κ 的级回灌"). 否定一路前缀 `NegKindLv`, 共用接口 [KindLvIf](KindLvIf.lagda.md) (接口定稿 2026-11-05 18:33; 只增 §5, 变更记录见接口文件头). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提, 不用升界算子 (`RaiseIf`/`RaiseC`) 作前提. 闭项与证书无模块参数.
>
> **判决: PARTIAL.** 读回/写入与按级回灌的折叠对一切种类结构写出并编译; 无条件闭项 `TK` 编译, 其中**一个**种类 (第 1 站读回分量的头种类 $\kappa_1$, 坐标 `HB (step S₀)`) 在最终坍缩里按自己的级 (级层 2, 读回 `readL 1`) 回灌, 而它在 NewTwr 的 `TN` 里有损. 第 $s+1$ 站 ($s\ge1$) 的头种类仍有损: 让每站的级都是对角的字面第一位置要种类结构族与级互递归, 检查器不接受 (编译失败, 不是否定定理; 未走通). 值没有定理.
>
> - **(a) 交了.** 无条件闭项 `KindLvTw.TK : A`, 证书 `Lg-TK`, FGH `fghK`; 塔与层号对角是 NewTwr 的式子 (每站求值同 `evN`, 折叠走本路的 `KindLvRun`, 平凡级回灌时与 `GenFoldRun` 逐行同, 判断), 最终坍缩是按级回灌的折叠 `KindLvRun` 在 `step KΛc` 上折到第 0 层. 一般构造: 级读回/写入 `readL`, `wrL` (对一切 $T$, 对级 $c$ 的构造子递归), 折叠 `KindLvRun` (对一切 $T$ 与一切 `LvFb`), 坍缩 `collLv : CollLvFbTy`.
> - **(b) 值: 没有定理.** 只有形状定理 (下表 §5); 读法 (判断) 见下.
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` 的元素, FGH 在树上算. 纲领 2: 无公理; 读回/写入是一个对 (级, 数据) 字典序递归的 `mutual` 块, 折叠对数据结构递归 (`AccY`), 检查器接受. 纲领 3: 折叠里唯一的比较是 `cmpB` (公共上界 $\Lambda$); 升界只在可判定下标上做点更新 (ℕ 下标; `⊤ ⊎ HB S₀` 下标对**不含函数的闭项** $2$ 的模式判定); 没有 "升一份留别份" 的律 (`rs` 只说升后更大且顶是 $v$). 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 级读回的每一行都由级 $c$ 的构造子决定 (停在 $\mathrm{hs}\,c_1$ 是新种类, 停在 $0$ 是底种类, 停在极限有损), 不看记号; 这一站新用到的字段是 `Lev c` 的种类作为**读回的输出种类** (经嵌入 `Emb`), 以及 `step` 的第二分量作为单个种类的界 (升界只换它).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KindLv where

import OCF.Align.KindLvIf
import OCF.Align.KindLvEmb
import OCF.Align.KindLvRd
import OCF.Align.KindLvRun
import OCF.Align.KindLvEv
import OCF.Align.KindLvTw
import OCF.Align.KindLvCmp
```

## 接口 (`KindLvIf`, 只有类型)

```text
Emb S′ S : j, cv, vc, cv-vc, π, lgπ, bd→, bd←, pr→, lgE→
lyL c = hs (up c) ; RdLTy T = (c : HB T) → LgW (step T) W → HB (Lev c) → DK T (lyL c) W → HB (Lev c) ; WrLTy T
record KLv T tp Λ κ : ℓ, ℓ⊲ (∀ w, ℓ ⊲[w] Λ), rd, rd-fst, rd-lg, rs, rs≤ (前提 Pr κ w (top κ w) v), rsLg, rs-top
LvFb T tp Λ = (κ : K T) → KLv T tp Λ κ ⊎ ⊤ ; CollLvTy ; CollLvFbTy (只增, 带 FbLg)
```

律的定义域写在接口文件头: 每条律只有一个种类与一个世界, 或带字面公共上界的一对坐标 (`rd-fst`, `rs≤`, `pr→`); 不比较两个种类.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `idE`, `stepE`, `supE`, `_∘E_` | Emb §1 | 嵌入的三个构造与复合 | 定义 |
| **`nbJ`**, `nbJ-mono`, `nbJ-fst`, **`Lg-nbJ`**, `LgΩ` | Emb §2–3 | 沿嵌入的连续分支 (`nbᴮ` 的推广), 合法由形状给出 | 定义; 定理 |
| **`readL`**, `readLp`, `rdS`, **`wrL`**, `wrK` | Rd §1 | 级层数据 ↔ `HB (Lev c)`, 对 $c$ 的构造子递归, 对一切 $T$ | 定义 (停机由检查器) |
| `readL-fst`, **`Lg-readL`** | Rd §2–3 | 起点是第一位置; 合法由形状给出 (对一切数据) | 定理 |
| **`Run`** (`RKv`, `κcL` 新; 其余逐字同 `GenFoldRun`) | Run | 第 0 层目标下旧种类按 `lv κ` 的级回灌, 否则退回 `fbA` | 构造 |
| `ColL`, **`collLv`** | Tw §1 | 一般坍缩 (`CollLvFbTy`) | 构造; 合法是定理 |
| `EvK`, `out₂K`, **`evK`**, `lg-evK`, `ρK`, `lρK` | Ev | 每站求值 (同 `NewTwrEv.evN`, 折叠走 `KindLvRun`, 平凡级回灌) | 构造; 合法是定理 |
| `B`, `lB`, `inc`, **`Bᴧ`**, `lBᴧ`, `ΛB`, `Λ`, `lΛ`, `one⊲` | Tw §2 | NewTwr 的塔的式子 (起点 2, 部分和对角) | 定义; 合法是定理 |
| `IsTwo`, `isTwo`, `up₂`, `up₂≤`, `up₂Lg`, **`K1`**, **`lvΛ`** | Tw §3 | $\kappa_1$ 的级回灌; 其余退回 `fbA` | 构造 |
| **`TK`**, **`Lg-TK`**, **`fghK`** | Tw §4 | 无条件闭项 | 构造; 无条件 |
| `_≈_`, `≈-rf`, `nbA-cong`, **`rdL0≈rd₁`** | Cmp §1–2 | $T=S_0$: `readL 0` 与 `rd₁` 对一切数据结构等价 | 定理 |
| `wr0-z/s/l/Ω`, `toD₁-z/s/l/Ω` | Cmp §2 | `wrL 0` 与 `toD₁` 四行同形 | 定理 (`refl`) |
| **`nbJ≈nbᴮ`**, `rdL1-new`, `rdL1-old`, `rdL1-nc` | Cmp §3 | 第 1 级: 两种结点行与 `rd₂` 同形; 新种类闭包有损 (与 `rd₂` 的差) | 定理 |
| **`rdL1-notA`** | Cmp §4 | 级读回的输出不只含底种类 (对照 `onlyA-rd₁`) | 定理 |
| **`κ₁-in-Bᴧ`**, `lv-κ₁`, **`K1-ℓ`**, **`K1-rd`**, `K1-seen`, **`κ₁-was-lossy`** | Cmp §5 | $\kappa_1$ 是对角第 1 项的头种类; 级层 $=$ `lyL 1`, 读回 $=$ `readL 1`; 升界被看见; 在 NewTwr 的 `GΛ` 下有损 | 定理 (`refl`) |

## 与 `onlyA-rd₁`, `lossy-rd`, `keepΛ` 的对应陈述有何不同

- `NewTwrObs.onlyA-rd₁`: `rd₁` (第 1 层读进 `HB T`) 的输出只含底种类的结点. 本路的级读回 `readL c` 读进 `HB (Lev c)`, 输出的种类是 `Lev c` 里沿路径的种类; 第 1 级上过第 1 层的结点就是新种类 (`rdL1-notA`, 定理). 但 `readL c` 在极限级 (路径停在 `hl`, `hΩ`) 与闭包结点上仍有损 (文件头; 否定一路 `NegKindLvRdW` 钉成 `refl`).
- `NewTwrK.lossy-rd`: 读回分量的种类在 `GΛ` 下没有 A-回灌. 本路的 `lvΛ` 对其中一个 ($\kappa_1$) 给级回灌 (`lv-κ₁`, 对照 `κ₁-was-lossy`); 对 $s\ge1$ 的读回分量仍退回 `fbA`, 即仍有损 (定义, `lvΛ κ = inj₂ tt`).
- `NewTwrObs.keepΛ`: `GΛ` 的 A-回灌不动读回分量. 本路 `K1` 的 `rs` 恰好改读回分量 `inj₂ 2` 的界 (`K1-seen`); 别的读回分量 (下标不是字面的 $2$) 不动 (`sel … no`).

## 闭项与 FGH 的类型原文

```text
KindLvTw.TK    : A                 -- CK.Tψ, CK = ColL GΛ LdΛ flΛ Λ lΛ one⊲ lvΛ, Λ = up (hl Bᴧ)
KindLvTw.Lg-TK : Lg TK
KindLvTw.fghK  : ℕ → ℕ             -- FLv.FGH (ordK TK)
KindLvTw.lvΛ   : LvFb KΛc (tpK GΛ) Λ   -- κ₁ ↦ inj₁ K1 ; 其余 ↦ inj₂ tt
KindLvRd.readL : RdLTy T           -- (模块参数 T, Ld)
KindLvRun.Run  : FoldTy.RunTy T Λ  -- (模块参数 T G Ld fl Λ lΛ one⊲ lv)
```

## 前提实例

- `KindLvRun` 的参数: `GΛ`, `LdΛ`, `flΛ` (NewTwr 的实例), `Λ`, `lΛ`, `one⊲`, `lvΛ` (本路).
- `KLv` 的实例: `K1` (无条件). `LvFb` 的实例: `lvΛ`; 平凡实例 `λ _ → inj₂ tt` (此时折叠与 `GenFoldRun` 逐行相同).
- `rdL0≈rd₁` 的前提 `b ≈ b′`: `≈-rf b`.

## 读法 (全部是判断; 只从树形与回灌算, 不用 R2)

| 对象 | 读法 (判断) | 依据, 测到哪里 |
|---|---|---|
| `readL c` | 第 $c$ 级的高度; 在后继级的头上与 `rd₁` (级 0), `rd₂` (级 1, 除新种类闭包) 同形 | `rdL0≈rd₁`, `rdL1-*` |
| $\kappa_1$ 的结点在最终坍缩里 | 不再取底支: 坐标沿 $v_{n+1}=\mathrm{readL}_1(\mathrm{top},\Delta_n)$ 迭代 $\omega$ 次, $\Delta_n$ 是分支在升高的世界里折到第 2 层的输出 | `lv-κ₁`, `K1-*`, `KindLvRun` 的 `κcL` 定义; 对折叠全程的不变式没写 |
| `TK` | 对角第 1 项 ($\approx$ 第 1 站的读回, 一个 $\Omega_3$-共尾的结点) 的结构进了闭项; 第 2 站起的增量与 `TN` 一样只见底支. 所以 `TK` 与 `TN` 同量级 (远低于 ψ₀Λ); 两者没有 `ord` 的比较 | 上面两行; NewTwr 的读法表 |

**结论 (判断).** "按级回灌" 在折叠与读回的层面写成了对一切种类结构的构造, 并且在闭项里对一个读回分量的种类生效; 卡点从 "折叠不回灌" (C6 的前半) 移到 "级与对角的类型对不上": 每站的级 $X_s$ 在 `HB (Kc s)` 里, 对角在 `HB KΛc` 里, 级层既要是对角的第一位置又要读进 `HB (Lev X_s)`. 两者同时成立要求级就是对角的部分和, 即种类结构族与级互递归.

## 第一个障碍

1. **[编译失败, 不是定理] 互递归的塔.** 写成

   ```text
   mutual
     Cs : ℕ → KS ; Cs zero = S₀ ; Cs (suc s) = step (Lev (Ys s))
     Ys : (s : ℕ) → HB (sup ℕ Cs) ; Ys zero = ι 0 (hs hz) ; Ys (suc s) = hs (Ys s) ⊞ ι (suc s) (evN (Ys s))
   ```

   报错原文: `Termination checking failed for the following functions: Cs. Problematic calls: Cs (at …KindLvTw.lagda.md:77.28-30)` (`Ys` 的类型 `HB (sup ℕ Cs)`; `Cs (suc s)` 经 `Lev {sup ℕ Cs}` 的隐式参数调用未应用的 `Cs`, 不降). 日志 scratch `kindlv/tw-IR-termination.log`, 草稿 `kindlv/KindLvTw-IR-attempt.lagda.md`. 这条若能写成, 第 $s+1$ 个分量的头种类的坐标是 `HB (Lev Y_s)`, 级层 `up (Bᴧ s)` 是 $\Lambda$ 的字面第一位置, 升界是 ℕ 下标点更新加 `step` 第二分量, 全都不要升界算子 (草稿里 `KT s` 的形状, 没编译过).
2. **[判断] 不互递归的写法都把级与对角放进两个类型.** 嵌套的前缀并 (`sup (⊤ ⊎ ⊤) [U_s, step (Lev Y_s)]`) 在每一有限站内级是第一位置, 到 $\omega$ 的并又变成列 (`NegLvKtTrap.diag-trap`); 经 `ι`/`up` 搬运的级, `Lev` 不定义相等 (要 `Cvt` 一类的逐结构搬运, 骨架总审 C9 不要); 经 `mapE` 的复合不融合 (要函数外延). 没有写成否定定理.
3. **[判断] 下标判定.** $\kappa_1$ 能升界是因为下标 $2$ 是不含函数的闭项; $B_s$ ($s\ge1$) 含求值的函数分支, 只能在带公共上界时判 (`StallDxBdec.bdec`), 而世界是对一切下标的函数, 判定要对一切下标做. 否定一路 `NegKindLvUpd` 对 "升一份留别份" 已编译否定 (分离子), 本路的 `rs` 不要求留.

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `lyL c = hs (up c)` | `KcFoldIf.lyK` (已有) | 树侧 |
| `readL`/`wrL` 按路径停在 `hs c₁`/`0`/极限三类 | `Lev` 的构造子: 只有 `step` 加种类 | 树逼出 (哪一行出新种类由 `Lev` 定) |
| `Emb`, `nbJ` | 读回的 $\Omega$-结点要落在 `Lev c` 的深处种类上, 坐标连续 | 树逼出 (`nbᴮ` 对 `step` 的推广); `cv`/`vc` 是恒等的脚手架 |
| 极限级、闭包结点、写入经过 `hΩ` 的种类: 有损 | 没有对应的种类或没有界的证据 | 树逼出 (有损的位置由类型定) |
| `KLv` | `FBA` 推广到坐标类型任意的种类 | 树侧 |
| `KindLvRun.RKv`, `κcL` | `GenFoldRun.κcA` 的同形 (读回换成级读回) | 树侧 (拷贝 + 一行) |
| `isTwo`, `up₂` | 在 `⊤ ⊎ HB S₀` 下标上判定闭项 $2$ | 脚手架 (只对 $\kappa_1$ 一个种类; 来自起点取 $2$ 的选择) |
| 塔放进 `module NT₁` 再 `open public` | 否定一路 `NegKindLvInst` (对 18:49 版写) 用 `NT₁.Bᴧ`; 改版后保持它编译 | 脚手架 |
| `KindLvEv` (每站求值的第二份) | 让闭项只含一份折叠 (行数); 平凡级回灌时与 `NewTwrEv.evN` 逐行同 (判断) | 脚手架 |

归类 (判断): 提供信息. 新定义没有读自基本列规则的字段; 闭包定理没有专属前提; 不用 `Lab`. 信息是: 级读回本身对一切级都能写 (只在极限级与闭包结点有损), 折叠接上它也只要一行; 卡在 "级与对角同一类型" 这一个类型条件 (互递归), 第 4 层没有改前 3 层.

## 审计

- **编译.** 八个模块 `OCF.Align.KindLvIf`, `KindLvEmb`, `KindLvRd`, `KindLvRun`, `KindLvEv`, `KindLvTw`, `KindLvCmp`, `KindLv` 删自己的 `.agdai` (逐个写精确路径) 后从入口编译, 依赖用共享接口: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/KindLv.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 8 秒, 峰值常驻约 1G. 接口 `KindLvIf` 首次编译 18:33 退出码 0; 只增 §5 后重编退出码 0.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 八个模块都退出码 0, 禁用表命中 0. 闭包里有 `HtTowerFTree` (`Ht`) 等 (经 `GenFoldIf`), 同 NewTwr; "闭项不经 `Ht`" 看切片.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词; `--html` 由 scratch 模块 `KLSlice` (导入 `OCF.Align.KindLv` 与 `OCF.Align.Om1HnAccept`) 生成, 6G, 退出码 0, 峰值约 2.2G): `KindLvTw:TK` 249/0/0, `Lg-TK` 251/0/0, `fghK` 267/0/0, `lvΛ` 336/0/0, `K1` 334/0/0, `Bᴧ` 313/0/0, `collLv` 251/0/0, `KindLvEv:evK` 260/0/0, `KindLvRd:readL` 115/0/0, `Lg-readL` 129/0/0, `wrL` 115/0/0, `KindLvRun:Run` 164/0/0, `KindLvEmb:nbJ` 8/0/0, `KindLvIf:KLv` 59/0/0, `KindLvCmp:rdL0≈rd₁` 138/0/0, `rdL1-notA` 122/0/0, `κ₁-in-Bᴧ` 316/0/0, `κ₁-was-lossy` 184/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用 `CK = ColL …` 的实参, 行数脚本把它们手工列为根.
- **禁用构造**: 八个文件的代码块里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延, UIP 前提; 不用 `RaiseIf`/`RaiseC`.

## 四层行数表

`probes/Survey/scripts/kindlv/locslice_kindlv.py` (同 `newtwr/locslice_newtwr.py` 口径: 定义级切片, agda 块非空非注释行; 模块应用的实参与参数化模块的模块内定义手工列为根, 见脚本头).

| 层 | 无条件 `TK`: 本路新增 / 树侧全部 / 记号 |
|---|---|
| 1 定义 | 34 / 373 / 0 |
| 2 折叠 (级读回, 嵌入, 按级回灌的折叠, 每站求值, 塔, 对角, 闭项, FGH) | 491 / 1391 / 0 |
| 3 证书 | 512 / **1479** / 0 |
| 4 对照, 形状 | 593 / 1574 / 0 |

前 3 层树侧 1479, **低于标杆 1513**; NewTwr `TN` 1268 (同口径). 多出的 211 行是级读回 (`KindLvRd`, `KindLvEmb`), 级回灌一行 (`κcL`, `RKv`) 与每站求值的第二份入口 (`KindLvEv`); 前 3 层闭包里没有 `GenFoldRun` 的块 (只有一份折叠). 第一版把每站求值留在 `GenFoldRun` 上, 前 3 层 1689, 超标, 已改.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `KindLvIf` | 48 / 120 | 接口 |
| `KindLvEmb` | 54 / 87 | 嵌入, `nbJ` |
| `KindLvRd` | 110 / 156 | 级读回与写入 |
| `KindLvRun` | 236 / 319 | 按级回灌的折叠 (`GenFoldRun` 拷贝 + `RKv`, `κcL`) |
| `KindLvEv` | 38 / 58 | 每站求值 |
| `KindLvTw` | 123 / 194 | 一般坍缩, 塔, `K1`, `lvΛ`, 闭项 |
| `KindLvCmp` | 107 / 170 | 对照与形状定理 |
| `KindLv` | 9 / 本文件 | 入口 |
| `probes/Survey/scripts/kindlv/locslice_kindlv.py` | — | 行数脚本 |

## 否定一路 (`NegKindLv`) 的结果 (它的报告, 本路未复核)

`NegKindLvBlind.relevel` (任何 `KLv` 都能改成 $\ell=0$ 且读回不看数据: "按自己的级" 不是接口的律; 本路因此写了实例上的 `K1-ℓ`, `K1-rd`); `NegKindLvRdW` (极限级与写入的有损行钉成 `refl`, 写入无左逆); `NegKindLvUpd` (坐标是高度的种类上 "升 + 留" ⇒ 分离子; 本路 `rs` 不要求留); `NegKindLvInst` (`only-κ₁`: 只有 $\kappa_1$ 给级回灌; `head-lossy`: 第 $s+2$ 站头种类有损; `start-κ₁`: 起始世界里 $\kappa_1$ 的界是 $0$; `updHΛ-sep`: 把 $\kappa_1$ 的升界推广到含函数的下标族 ⇒ 分离子); `NegKindLvRaise.no-klv-upAllR` (`KLv.rs` 不能是同一个 $R$ 的 "一起升"). 主审转告 `RaiseC`: 无界 `RaiseA` 没有构造性实例, 有界版可用; 本路不用任何升界算子.

## 接手清单

1. **互递归的塔 (第一个障碍 1).** 先找一个检查器接受的写法: 例如把 `Lev` 换成只依赖坐标类型函数 (不经 `sup ℕ C` 的隐式参数) 的版本, 或把种类结构族写成归纳-递归的数据类型 (要先查正性); 写成后, 第 $s+1$ 个分量的头种类的 `KLv` 是草稿里的 `KT s` (ℕ 下标点更新 + `step` 第二分量, 不要升界算子). 交否定一路对准 "种类结构族与级互递归" 的形状.
2. **值.** 对 `TK` 与 `TN` 做 `ord` 的比较 (至少第 1 站的结点: $\kappa_1$ 的回灌是否让 `ord TK` 严格高于把 $\kappa_1$ 换成有损的同一折叠); 现在只有形状定理.
3. **写入与极限级的有损行.** `wrK` 经过 $\Omega$-结点时取底坐标, `readL` 停在极限级时读输入为 $0$ 的分支; 若级是对角的部分和 (第 1 条成立后), 这些行会在每站出现, 要先写 "写入时有界的证据从哪来" 的小实验.
4. **`KindLvRun` 与 `GenFoldRun` 的逐行相同** (平凡级回灌时) 现在是判断; 可以把 `GenFoldRun` 改成 `KindLvRun` 的实例 (第 4 层不改前 3 层, 要作者定), 或写一条结构等价的定理.
