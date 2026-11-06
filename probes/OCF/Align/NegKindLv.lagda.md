# 按级回灌: 否定一路的入口

> 不含记号. 本路是 `KindLv` (构造一路) 的配对**否定**一路 (手册 §5.2), 前缀 `NegKindLv`. 对着接口 [KindLvIf](KindLvIf.lagda.md) ("接口定稿 2026-11-05 18:33 (首次编译通过)"; 变更记录: 18:48 只增 §5 `CollLvFbTy`) 写, 导入它, 不另造接口. 分篇: 接口定稿前写的 [NegKindLvLev](NegKindLvLev.lagda.md) (种类的级; 读回不能无损地写回本级), [NegKindLvUpd](NegKindLvUpd.lagda.md) (坐标是高度的种类上的分离子), [NegKindLvW](NegKindLvW.lagda.md) (同一级两份拷贝的世界映射); 定稿后写的 [NegKindLvBlind](NegKindLvBlind.lagda.md) (接口的盲区), [NegKindLvRaise](NegKindLvRaise.lagda.md) ("一起升" 满足不了 `KLv`), [NegKindLvRdW](NegKindLvRdW.lagda.md) (构造一路的级读回与写入的有损行, 只读导入 `KindLvRd`), [NegKindLvInst](NegKindLvInst.lagda.md) (对构造一路实例 `KindLvTw` 18:49 版的检查, 只读导入). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` 只在五条条件定理 (`…→WLPO`) 里作前提.
>
> **判决: 接口没有被否定 (记录都有实例, 律不撞分离子). 接口不把 "按自己的级" 写成律 (`relevel`, 反模型); 接口的升界律排除 "一起升" (`no-klv-upAllR`, 定理); 构造一路的实例只给一个种类 (第 1 站读回分量的头, 级 $1$) 按级回灌, 后面各站的头没有 (`only-κ₁`, `head-lossy`, 定理); 把那一个种类的点更新推广到含函数的下标族推出分离子 (`updHΛ-sep`).**
>
> **对纲领与目标.** 纲领 3: 推出分离子/WLPO 的都是 "升一份留别份" 在**不可判定下标** (含函数的高度) 上的形状 (`updH₁-sep`, `updHT-sep`, `updHΛ⁺-sep`, `updHΛ-sep`), 条件 `FE₀`; 坐标是不是高度无关 (`upd-step`: `step` 的两个分量可判定时, 坐标是高度的种类上点更新是构造); 接口的律不含 "留", 不撞. 纲领 1: 一切定理对 `HB`/`Lev`/`Kc`/`KΛc`; 反模型 (`collC`, `collCFb`) 给合法闭项. 目标 "让树自足": 本路给出两条树侧判据: (a) **种类的级是树侧概念** (`lvK`, `coord-lv`: 每个种类的坐标是 `A` 或 `HB (Lev y)`, $y$ 是严格子项; `lv-not-self`: `Lev c` 没有级为 $c$ 的种类), 所以 "层 $c$ 的读回只能喂 `step (Lev c)` 的新种类" 是由 `no-retract` 逼出的; (b) **以含函数的高度为下标的并里, 升界只剩 "精确置自己的分量, 别处只增不减且按分量不同" 一种未被否定的形状**: "留" 撞分离子 (本路与 `NegGenFoldUpd`), "同一个 $R$ 一起升" 撞 `rs-top` + `rs≤` (`no-klv-upAllR`, 与 `RaiseC` 的 `no-fba-upAll` 同型). "只剩" 是判断 (手册 §3.9).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKindLv where

import OCF.Align.NegKindLvLev
import OCF.Align.NegKindLvUpd
import OCF.Align.NegKindLvW
import OCF.Align.NegKindLvBlind
import OCF.Align.NegKindLvRaise
import OCF.Align.NegKindLvRdW
import OCF.Align.NegKindLvInst
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Cd`, `lvK`, **`coord-lv`**, `lv-new`, `_⊏_`, **`lv-sub`** | Lev §1–2 | 每个种类的级; 坐标类型由级给出; 级是严格子项 | 定义; 定理 |
| **`no-desc-at`**, **`no-desc`**, **`lv-not-self`**, **`no-desc-step`**, `inst-new` | Lev §3 | `HB (Lev c)` 不是任何种类坐标的收缩; 没有种类的级是 $c$ (由 `no-retract`) | 定理 (否定) |
| `κH`, `PtUpdHv₁`, `PtUpdH₁`, `full→H₁`, **`updH₁-sep`**, `updHv₁-sep` | Upd §1 | `K₁`: 坐标是高度的种类上 "升到 1 + 留" ⇒ 分离子 | 定理 (否定) |
| `updH₁→WLPO`, `updHT→WLPO`, `updHΛ⁺→WLPO` | Upd | 同上 ⇒ WLPO | 条件 (`FE₀`) |
| `κhT`, `PtUpdHT`, **`updHT-sep`** | Upd §2 | `T₀ = Lev X₀` 上同 | 定理 (否定) |
| `κHΛ`, `PtUpdHΛ⁺`, **`updHΛ⁺-sep`** | Upd §3 | `step KΛc` 上同 | 定理 (否定) |
| `upOne₁`, `half₁R`, `half₁K`, `upOne₁-moves`, `upOneT`, `halfTR`, `halfTK`, `upOneΛ`, `halfΛR`, `halfΛK` | Upd | 两半各自可满足 | 定理 (前提实例) |
| `upd-step`, `raise-step`, `keep-step` | Upd §4 | 可判定下标上两半同时成立 | 定理 (对照) |
| **`no-wmatchΛH`**, **`no-wmatchΛ⁺H`**, **`no-wmatchΛA`** | W §3 | `KΛc` 里同一级的两份拷贝, 没有到该级世界的映射同时保两份界 | 定理 (否定) |
| `sat1H`, `sat2H`, `sat1A`, `sat2A` | W §4 | 只保一份拷贝的映射存在 | 定理 (前提实例) |
| `lossyAll`, `collC`, `collCFb` | Blind §1 | `LvFb`, `CollLvTy`, `CollLvFbTy` 的平凡实例 | 定理 (反模型) |
| **`relevel`**, `relevel-ℓ`, **`relevel-blind`**, `relevel-rs` | Blind §2 | 任何 `KLv` 都能改成级层 $0$, 读回不看数据, 升界不变 | 定理 (反模型) |
| `constRd`, `prRefl` | Blind §3 | 读回恒取起点也是 `KLv` (第一位置自反时; `Lev c` 处处自反) | 定理 (反模型) |
| `rBR`, `upAllR`, `top-κ₁`, **`no-upAllR`**, **`no-klv-upAllR`** | Raise §1–2 | 对任何 $R$, 底拷贝 `κ₁ f` 的 `KLv.rs` 不能是 "一起升" | 定理 (否定) |
| `half-top`, `half-≤`, `refl-rBR` | Raise §3 | 两半各自可满足 | 定理 (前提实例) |
| `WΩ.wr-Ω-drop`, `WΩ.wr-y₁`, **`WΩ.wr-no-ret`**, `WΩ.rdwr-drop` | RdW §1 | 级是 $\Omega$-头时 `wrL` 丢掉种类的 $\Omega$-结点; 写入无左逆 | 定理 (`refl`; 否定) |
| `rd-lim-drop`, `rd-limΩ-drop`, `rd-nc-drop` | RdW §2–3 | 极限级与闭包结点在 `readL` 里只读一支 | 定理 (`refl`) |
| **`only-κ₁`**, **`κ₁-occ`**, `K1-own`, `lv-κ₁`, `Lev-agree`, `E-κ₁`, **`head-lossy`**, `head-lossy-fb`, `start-κ₁` | Inst §1–5 | `KindLvTw.lvΛ` 只对一个种类有级回灌; 它在最终层里; 级层是它的级; 后面各站的头有损; 起始世界里它的界是 $0$ | 定理 |
| `PtUpdHΛ`, **`updHΛ-sep`** / `updHΛ→WLPO` | Inst §6 | `K1` 的点更新推广到第 1 站含函数的下标族 ⇒ 分离子 | 定理 (否定) / 条件 (`FE₀`) |

## 每条律为什么是构造一路需要的

- **`KLv.rs`, `rs≤`, `rs-top`** (接口 §3): `KindLvRun` 的按级回灌一行每格用 `rs` 升界, 用 `rs≤` 证世界变大. `no-klv-upAllR` 说在以含函数的高度为下标的并里, 它不能是 "一起升"; `updH*-sep` 说它若再加 "留" 就是分离子. 构造一路在闭下标 $2$ 上写了 "升 + 留" (`KindLvTw.up₂`, 不撞), 推广到后面的站撞 `updHΛ-sep` (判断: 后面各站的下标 $B_s$ 含求值的函数分支).
- **`KLv.ℓ`, `rd`** (接口 §3): "按自己的级" 的落点. `relevel` 说接口不绑; 实例里绑上了的只有 `κ₁` (`K1-own`, `only-κ₁`).
- **`RdLTy`, `WrLTy`** (接口 §2) 与构造文件的 `readL`, `wrL`: `no-desc`, `lv-not-self` 说读回进 `HB (Lev c)` 的类型选择是被逼的 (不能写回本级); `wr-no-ret`, `rd-*-drop` 说有损的行在哪里.
- **`LvFb`, `CollLvTy`, `CollLvFbTy`** (接口 §3–5): 平凡实例 (`lossyAll`, `collC`, `collCFb`) 说类型不决定值.
- `no-wmatchΛ*` 对着的是 "先把世界投到第 $y$ 级再读回" 的写法; 接口与构造一路都没有这样做 (读回在折叠自己的世界里), 所以它是划界, 不打实例.

## 前提实例

- `updH₁-sep` 等: 两半各自可满足 (`half*`); 下标可判定时两半同时成立 (`upd-step`, `KindLvTw.up₂`). 分离子经典地成立 (判断); `FE₀` 在 Agda 里证不出也否证不了.
- `no-upAllR`: 两半 `half-top` ($R\,a\,v=v$), `half-≤` ($R\,a\,v=a$).
- `no-wmatchΛ*`: `sat1H`, `sat2H`, `sat1A`, `sat2A`.
- `no-desc`: 任意 $c$ 与种类; `inst-new` (`Lev (hs c)` 的新种类).
- `WΩ.wr-no-ret`: 参数 $T$, `LgDn T`, $\kappa_0$, $h$ 任意 (例: $T=S_0$, `ldS₀`).
- 接口记录: `KLv` (`KindLvTw.K1`; `relevel K1`, `constRd`), `LvFb` (`lossyAll`, `KindLvTw.lvΛ`), `CollLvTy`/`CollLvFbTy` (`collC`, `collCFb`, `KindLvTw.collLv`).

## 只否定什么, 不否定什么

- **否定** (编译的): 以含函数的高度为下标的分量里, 坐标是高度的种类上一致的 "升 + 留" (`K₁`, `T₀`, `KΛc`, `step KΛc`; 分离子, `FE₀` 下 WLPO); 底拷贝上 "一起升" 形状的 `KLv.rs` (`rs-top` + `rs≤`); 高一级的高度无损地写进本级或更低级的坐标 (`no-desc`); 级为 $\Omega$-头时 `wrL` 有左逆; 同一级两份拷贝的双向保界世界映射. 反模型否定的推断: "有 `KLv` 实例 ⇒ 按自己的级回灌"; "有 `LvFb`/`CollLvTy` 实例 ⇒ 读回进了闭项".
- **不否定**: 接口的任何记录; 按级回灌这条路线; 构造一路的闭项 `TK` 的值 (没有 `ord` 定理); 精确置自己分量而别处按分量不同地只增的 `rs` (未构造, 未否定); 级与种类结构互递归的塔 (构造一路编译报停机失败, 那不是否定定理, 本路没有对它写否定). 本路**没有关闭任何路线**.

## 判断 (单列)

- **实例的强度.** `KindLvTw` 相对 `NewTwr.TN` 只多了一个种类 (`κ₁`, 级 $1$) 的按级回灌, 读回是 `readL 1` (与 `rd₂` 同型, 构造文件头). 后面各站的头种类 (坐标 `HB (Lev B_s)`, 承载层号塔的高度) 全有损 (`head-lossy`). 所以 GenFold/NewTwr 的第一个障碍 (C6) 在实例上只在第 1 站解除. 没有值定理.
- **推广的墙.** 后面各站的头的下标 $B_{s}$ 含函数, 不能按模式判定; `K1` 式的 "升 + 留" 撞 `updHΛ-sep`; 不留而 "一起升" 撞 `no-klv-upAllR` (只对底拷贝证了; 对坐标是高度的种类, 类型随级变, "一起升" 连形状都要逐结构搬运, 见 `NegKindLvUpd` §5). 剩下的形状只有 "精确置自己的分量, 别处只增" 且依赖分量; 这是否可写, 本路没有结论. "只剩这一种" 是判断, 下一路应先挑战它.
- **互递归的塔.** 构造一路把级与种类结构互递归 (`C (s+1) = step (Lev (Y s))`, `Y s : HB (sup ℕ C)`) 时报 `TerminationIssue`. 若写成, 头种类的下标就是 ℕ 与 `step` 的第二分量 (可判定), `KLv.rs` 可逐字写 (构造一路的草稿 `KT s`); 那时深种类 (经过 $Y_s$ 的 $\Omega$-结点的) 仍有损 (`WΩ.wr-Ω-drop` 的形状). 这是判断.

## 审计

- **编译.** 删本路八个模块的 `.agdai` (精确模块名) 后从入口编译, 依赖用共享接口: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegKindLv.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 4 秒, 峰值常驻约 0.75G. 对着的构造文件: `KindLvIf` (18:48 版, 含 §5 只增), `KindLvRd` (18:36), `KindLvTw` (18:49).
- **导入闭包** (`importclosure.py`, 不加 `--only`): 八个模块都退出码 0, 禁用表命中 0.
- **禁用构造**: 八个文件没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`; `FE₀` 只作 `…→WLPO` 的前提; 没有 UIP 前提.

## 文件

| 文件 | 内容 |
|---|---|
| `NegKindLvLev` | 种类的级, `no-desc` |
| `NegKindLvUpd` | 坐标是高度的种类上的分离子 |
| `NegKindLvW` | 同一级两份拷贝的世界映射 |
| `NegKindLvBlind` | 接口的盲区 |
| `NegKindLvRaise` | "一起升" 满足不了 `KLv` |
| `NegKindLvRdW` | `readL`/`wrL` 的有损行 |
| `NegKindLvInst` | 对 `KindLvTw` 实例的检查 |
| `NegKindLv` | 入口 |
