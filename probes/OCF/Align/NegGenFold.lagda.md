# 对一般种类结构的数据树与折叠: 否定一路的入口

> 不含记号. 本路是 `GenFold` (构造一路) 的配对**否定**一路 (手册 §5.2), 前缀 `NegGenFold`. 对着接口 [GenFoldIf](GenFoldIf.lagda.md) ("接口定稿 2026-11-05 16:59 (首次编译通过)"; 变更记录: 只增 §6 `LgDn`, §7 `FbLgAt`/`FbLg`, 不改已有定义) 写, 导入它, 不另造接口. 分篇: [NegGenFoldUpd](NegGenFoldUpd.lagda.md) (并的世界里只升一个分量的界), [NegGenFoldBlind](NegGenFoldBlind.lagda.md) (回灌律不看种类, 钩子不看读回, `GenK (Lev x)` 的实例). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` 只在 `NegGenFoldUpd` 的两条条件定理里作前提.
>
> **判决: 接口没有被否定. 接口文件头自述的第一个障碍 (判断) 现在是定理, 范围是 "点更新"; 接口的回灌律与钩子是盲的 (反模型, 定理).**
>
> 1. **嫌疑 (ii) 成立于点更新, 不成立于接口的律 (定理).** 以高度为下标的并 (`K₁ = Kc 1` 的读回分量, 第 1 站下降的层所在的 `T₀ = Lev X₀`) 上, 一个对一切世界一致的操作若把分量 $i$ 的界升到给定值 ("升"), 又不升别的分量 $k\neq i$ 的界 ("留"), 就推出分离子 (`upd₁-sep`, `updT-sep`); 有 `FE₀` 时推出 WLPO (`upd₁→WLPO`, `updT→WLPO`). "留" 比较两个裸下标, 没有公共上界. 两半各自可满足, 下标可判定的分量上两半同时成立 (`upd∘`). 接口的 `FBA` 不含 "留", 不撞这一条.
> 2. **嫌疑 (iii): 接口没有 "读回进了闭项" 的陈述; 现有的钩子与回灌律是盲的 (定理, 反模型).** 定稿的接口 (含两次只增) 里没有这样的陈述, 本路没有对象可否定. `EvGenTy` 有常数实例, 数据取接口自己的 `DK` 时也是 (`evGenD`); `RunTy` 有平凡实例 (`runC`); `DnGenTy` 有实例, 每站回灌输出都是 $2$ (`dnGenC`, `HsGen`). 更要紧的是 **`FBA S κ` 的字段不出现 $\kappa$** (`fba-swap`): 在 `K₁` 上, 用可判定分量 `inj₁ tt` 的回灌给**每个**种类都填上 `fbA κ = inj₁ _` (`genK₁`, `fed-all`), 包括接口说 "只能有损" 的读回分量里的种类 `κ₁ f`; 这时回灌不碰 `κ₁ f` 的分量 (`fba₁-misses`), 闭包分支的坐标 `top κ W′` 不动 (`fba₁-top-fixed`). `genK₁` 满足接口 §6, §7 的只增结构 (`ldK₁`, `fbLg₁`), 可以作构造一路 `GenFoldRun` 的参数 (测试: scratch 里以 `genK₁` 实例化 `GenFoldRun` 编译通过, 退出码 0; 依赖构造一路 17:05 时的文件).
> 3. **嫌疑 (i) 不落在接口上 (判断, 依据定理).** 接口没有种类结构之间的世界映射: 数据树的种类就是 `step K` 的种类, 构造一路的读回 `GenFoldRd.rd₂` 把 `Ht` 的两种种类按**结点** (过哪一层) 给出, 不按闭包的种类给出. `no-wmatch`/`no-wmatch₀` 否定的是 "一个世界映射同时保两份拷贝的界", 这里没有这样的映射. 拷贝的问题换了个地方出现: 不在世界映射上, 而在**升高一份拷贝的界而不动别的拷贝** (第 1 条的 "留"). `T₀` 的 `κj f` 就是 `NegDnFoldCopy` 的 `k1`, `k2` 那一族底拷贝.
> 4. **嫌疑 (iv) 没有观察到停机或正性的错误 (观察 + 定理).** `genLev : ∀ x → GenK (Lev x)` 与 `ldLev` 对层号 $x$ 结构递归, 编译通过, 无编译指示. 接口 §1 的 `AccY` 对一切种类结构有定义. 构造一路没有写 "沿坐标走前缀" (`GenFoldTree` 文件头: "坐标类型是抽象的 `E κ`; 本路没有写"), 这不是停机检查的报错, 是 `KS`/`GenK` 的字段不给坐标的结构 (判断; 我起草的一条 "坐标序良基" 的否定因 `Pr` 本来就自反而不说明问题, 已删, 没有进仓库).
>
> **对纲领与目标.** 纲领 3 (壁垒): 本路推出分离子/WLPO 的只有点更新的 "留" (裸下标的比较), 条件定理的条件是 `FE₀`; 接口的律 (`TopG`, `FBA`, `GenK`, `LgDn`, `FbLg`) 都有实例, 不触壁垒. 纲领 1: 本路的定理都对 `HB`/`Lev`/`Kc`, 反模型 `dnGenC` 给出合法的闭项 (`KG.TΛ∞ω`), 回灌输出是常数. 目标 "让树自足": 第 1 条给出一条树侧判据: **以坐标为下标的并上, 回灌只能 "一起升" (`upAll₁`, 每份底拷贝换成新界) 或 "在可判定的下标上点更新" (`upd∘`), 不能 "只升这一份"**; 第 2 条说明接口的 `fbA` 不能当这条判据用.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegGenFold where

import OCF.Align.NegGenFoldUpd
import OCF.Align.NegGenFoldBlind
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `jx`, `jx-inj`, `eq→F`, `wdec→sep` | Upd §0 | 下标 `jx f` 单射; 弱判定 ⇒ 分离子 | 定理 |
| `F→eq`, `sep→WLPO` | Upd §0 | 分离子 ⇒ WLPO | 条件 (`FE₀`) |
| `PtUpd₁`, `PtUpdB₁`, `full→B₁`, `wdec₁`, **`upd₁-sep`**, `updB₁-sep` | Upd §1 | `K₁` 上点更新 (升 + 留) ⇒ 分离子 | 定理 (否定) |
| **`upd₁→WLPO`** | Upd §1 | 同上 ⇒ WLPO | 条件 (`FE₀`) |
| `rB`, `upAll₁`, `half₁R`, `half₁K`, `upAll₁-moves` | Upd §1 | 两半各自可满足; 只升的那一半把别的分量也升了 | 定理 (前提实例) |
| `upd∘`, `raise∘`, `keep∘` | Upd §1 | 可判定下标 `inj₁ tt` 上两半同时成立 | 定理 (前提实例) |
| `Fc`, `κj`, `PtUpdT`, `PtUpdBT`, `full→BT`, `wdecT`, **`updT-sep`** / `updT→WLPO` | Upd §2 | `T₀ = Lev X₀` 上同样 | 定理 (否定) / 条件 (`FE₀`) |
| `upAllT`, `halfTR`, `halfTK` | Upd §2 | 两半各自可满足 | 定理 (前提实例) |
| **`fba-swap`** | Blind §1 | `FBA S κ` 不看 $\kappa$ | 定理 |
| `fba₀`, `fba₁`, **`genK₁`**, **`fed-all`**, **`fba₁-misses`**, **`fba₁-top-fixed`** | Blind §1 | `K₁` 上每个种类都 "有回灌", 而 `κ₁ f` 的分量与分支坐标不动 | 定理 (反模型) |
| `fbLg₁`, `ldK₁`, `ldLev`, `toG` | Blind §1 | 接口 §6, §7 的结构在 `genK₁`, `Lev x` 上成立 | 定理 (前提实例) |
| **`evGenC`**, **`evGenD`**, `evGenD-const`, **`runC`**, **`dnGenC`**, **`HsGen`** | Blind §2 | 钩子的常数实例; 塔每站输出 $2$ | 定理 (反模型) |
| `aL`, `frL`, `frL-lg`, `frL-mono`, **`genLev`**, `genAll` | Blind §3 | 一切 `GenK (Lev x)` (对 $x$ 结构递归) | 定理 (前提实例) |

## 每条律为什么是构造一路需要的

- **点更新 (`PtUpd₁`, `PtUpdT`)**: 不在接口的律里, 在接口文件头的第一个障碍里 (原话: "升高分量 $i$ 的界要对下标 $i$ 判定 '是不是这个分量' (函数更新); 下标是坐标 (`A`, `HB _`) 时判定不了, 这些种类只能有损地回灌"). 构造一路的 `GenFoldRd.rd₁` 因此把第 1 层的旧种类闭包 "只读当前世界", `GenFoldRun` 对 `fbA κ = inj₂ tt` 的种类 "当前世界的分支, 重复 $\omega$ 次". 两种种类时 (`HtTowerFTree` 的 `nκ`: `D₊ (c , proj₂ W)`) 正是 "升一个, 留其余". 本路把这个判断换成定理, 并说清范围: 撞墙的是 "留", 不是 "升".
- **`FBA`, `GenK.fbA`** (接口 §3 原文): 构造一路 `GenFoldRun` 的 A-回灌一行 (`κcA`) 以 `fbA κ = inj₁ F` 为条件; 有内容的回灌要升 $\kappa$ 自己的界. `fba-swap`, `fba₁-top-fixed` 说接口的律不保证这一点.
- **`EvGenTy`, `RunTy`, `DnGenTy`** (接口 §4, §5 原文): 构造一路的交付 (`EvSysK K` 的实例, 塔上的下降) 的类型. 常数实例说明类型本身不说 "读回进了闭项".
- **`GenK (Lev x)`** (接口 §5 `DnGenTy` 的前提): `genLev` 说明前提可满足, 且对层号递归写得出.

## 前提实例

- `upd₁-sep`, `updT-sep`: 前提的两半各自可满足 (`half₁R`/`half₁K`, `halfTR`/`halfTK`); 下标可判定时两半同时成立 (`upd∘`, `raise∘`, `keep∘`). 分离子经典地成立 (判断), 所以前提经典地可满足; `FE₀` 在 Agda 里证不出也否证不了 (与 `ColimWNeg`, `NegDnFoldAdm` 同档).
- 接口记录: `TopG`, `GenK`, `LgDn`, `FbLg` (`genK₁`, `genLev`, `ldK₁`, `ldLev`, `fbLg₁`), `FBA` (`fba₀`), `EvGenTy` (`evGenC`, `evGenD`), `RunTy` (`runC`), `DnGenTy` (`dnGenC`). 所以接口的条件不空.

## 只否定什么, 不否定什么

- **否定** (编译的): 在 `K₁` 与 `T₀` 上, 对一切世界一致的点更新同时 "升" 分量 `jx f` 的底拷贝与 "留" 别的分量 `jx f′` 的底拷贝 (分离子; `FE₀` 下 WLPO). 反模型否定的推断: "`fbA κ = inj₁ _` 说明 $\kappa$ 的界被回灌"; "有 `EvGenTy`/`RunTy`/`DnGenTy` 的实例说明读回进了闭项".
- **不否定**: 接口的任何记录与定义 (都有实例); 只升不留的回灌 (`upAll₁`); 可判定下标上的点更新; 有损回灌; 有内容的折叠 (值的问题, 本路没有值定理). 路线状态: 本路**没有关闭任何路线**.

## 判断 (单列)

- **把 `FBA` 绑到 $\kappa$ 上.** 要让 `fbA κ = inj₁ _` 有意义, `FBA` 至少要有一条律把升高后的世界里 $\kappa$ 的顶坐标与 $v$ 连起来 (例如对底拷贝 `v ⊲ frE (top κ (rsA w v))`). 绑上并要求 "留" 就是第 1 条的分离子. 只绑不留: 本路没有编译出否定, 也没有在以高度为下标的分量上构造出实例. 草稿分析 (未编译): `rs≤` 要对一切分量 $c$ 有新界 $\ge$ 旧界, 绑定要分量 $i$ 的新界 $\ge v$ 且对一切 $w$, $v$ 成立 (`tp-rs` 无前提); 不判定 $c$ 是否 $=i$ 时, 统一的写法要 `A` 上的字面公共上界 (`a ⊞ v` 不以 $v$ 为第一位置: $1\oplus\omega$ 的第一位置里没有 $\omega$; `v ⊞ a` 不以 $a$ 为第一位置), 撞 `HtTowerNeg.no-joinA` 的形状. 这是下一条否定实验的对象.
- **读回的盲区.** 构造一路的 `GenFoldRd.rd₂` 对闭包结点 `nc κ z u` 只读当前世界的分支 (`rd₂ lW b (nc κ z u) = rd₂ lW b (u ≤rf lW)`), 对第 1 层的旧种类闭包 `rd₁` 同. 所以留到最后一层的闭包结点的其它世界的分支进不了 `Ht` (只读观察, 构造一路文件里是定义).
- **建议 (给构造一路).** "读回进了闭项" 写成值的陈述 (`ord` 下的界, 或与参照树的比较), 不要写成形状或 `fbA` 的分类; 回灌在以坐标为下标的分量上取 "一起升" (`upAll₁` 的形状) 时, 先算翻译账: 一起升把别的分量的底拷贝也升了 (`upAll₁-moves`), 值会变, 合法性要另证 (`rs≤` 不成立, 见上).

## 审计

- **编译.** 删本路三个模块的 `.agdai` (精确模块名 `OCF.Align.NegGenFold`, `OCF.Align.NegGenFoldUpd`, `OCF.Align.NegGenFoldBlind`) 后从入口编译, 依赖用共享接口, `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegGenFold.lagda.md +RTS -M6G -RTS`, 退出码 0, 峰值常驻约 0.67G, 用时约 4 秒. 对着的接口: `GenFoldIf` 含 §6, §7 两次只增的版本.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 三个模块都退出码 0, 禁用表命中 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词; `--html` 由导入本入口与 `OCF.Align.Om1HnAccept` 的 scratch 模块生成, 退出码 0): `upd₁-sep` 91/0/0, `updT-sep` 221/0/0, `upd₁→WLPO` 97/0/0, `upd∘` 66/0/0, `fba-swap` 10/0/0, `genK₁` 134/0/0, `fba₁-top-fixed` 139/0/0, `evGenD` 79/0/0, `runC` 65/0/0, `HsGen` 147/0/0, `genLev` 120/0/0, `ldK₁` 68/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 三个文件没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`; 函数外延 `FE₀` 只作 `F→eq`, `sep→WLPO`, `upd₁→WLPO`, `updT→WLPO` 的前提; 没有 UIP 前提.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `NegGenFoldUpd` | 194 / 296 | 点更新的分离子, 两半实例, 可判定下标上的实例 |
| `NegGenFoldBlind` | 108 / 184 | `FBA` 不看种类, 钩子的常数实例, `GenK (Lev x)` |
| `NegGenFold` | 4 / 本文件 | 入口 |
