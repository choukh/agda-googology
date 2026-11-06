# 分层互递归塔: 否定一路的入口

> 不含记号. 本路是 `StratTw` (构造一路) 的配对**否定**一路 (手册 §5.2), 前缀 `NegStratTw`. 对着接口 [StratTwIf](StratTwIf.lagda.md) ("接口定稿 2026-11-05 19:13 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 分篇: 接口定稿前写的 [NegStratTwCyc](NegStratTwCyc.lagda.md) (草稿的互递归是不是真循环); 定稿后写的 [NegStratTwBlind](NegStratTwBlind.lagda.md) (接口的盲区与接口逼出的东西), [NegStratTwInst](NegStratTwInst.lagda.md) (对构造一路实例 `StratTwTw` 19:20 版的检查, 只读导入), [NegStratTwDeep](NegStratTwDeep.lagda.md) (深种类上的边界, 级的拷贝). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` 只在一条条件定理 (`updD→WLPO`) 里作前提.
>
> **判决: 接口没有被否定; 构造一路的实例做到了 "每站头种类按自己的级回灌" (无穷多个两两不同的种类, `hd-inj-U`), 深种类全部有损 (`deep-lossy`, `deep-noA`); 把头种类的点更新推广到深种类撞分离子 (`updD-sep`), 级的拷贝与头种类的界不能由一个世界映射统一 (`no-wmatch-cp`). 草稿的互递归作为规格可满足, 依赖只向下 (`strat`); "真循环" 只在定义形式上.**
>
> **对纲领与目标.** 纲领 1: 一切定理对 `HB`/`Lev`/`StratTwTw.U`; 反模型 `trivSt` 是合法的 `StratTw`. 纲领 3: 撞分离子的仍是 "升一份留别份" 在**以含函数的高度为下标**的一族种类上 (`updD-sep`, 条件 `FE₀` 下 WLPO); 构造一路的升界只在 ℕ 下标上, 不撞. 目标 "让树自足": 本路给出两条树侧事实: (a) `OwnHd` 的级层绑定 (`ℓ L ≡ lyL (Y s)`) 加上对角的字面第一位置 (`Yfst`) 就逼出头种类两两不同 (`hd-inj`, 只用高度的良基), 不需要看记号; (b) 级的和 `Lev (a ⊞ b)` 里低一级的种类以拷贝出现 (`Cp.kup`, 对一切 `S`), 分层塔里这些拷贝以坐标为下标, 回灌墙从 KindLv 的 "后面各站的头" 移到 "每站级里的深种类".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegStratTw where

import OCF.Align.NegStratTwCyc
import OCF.Align.NegStratTwBlind
import OCF.Align.NegStratTwInst
import OCF.Align.NegStratTwDeep
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `TwEq`, **`solZ`**, **`solFin`**, `solFin-fst`, `Lev-fin` | Cyc §1–2 | 草稿的两条递推作为命题等式的规格有解 (常数级; 严格增长的有限级) | 定理 |
| `KBn`, `Draft`, **`strat`**, `draftFin` | Cyc §3 | 草稿形状的任何解, $Y_s$ 只用分量 $\le s$ 的种类; 前提实例 | 定理 |
| `trivSt`, `KTf`, `lvTriv`, **`ownTriv`**, `blind-rd`, `blind-P`, `blind-X` | Blind §1 | `StratTw` + `OwnHd` 的平凡实例: 前缀不增长, 级是有限数, 读回不看数据 | 定理 (反模型) |
| `no-up`, `⊲→⊑`, `noLoop` | Blind §2 | $\mathrm{hs}\,a\not\lhd a$ (对一切 `S`) | 定理 |
| **`Y-inj`**, **`hd-inj`**, `hd-inj-inst` | Blind §3 | 对角两两不同; `OwnHd` 下头种类两两不同 | 定理 |
| **`no-total`** | Blind §4 | 级的高度类型不是总结构的高度类型 (`no-retract`) | 定理 (否定) |
| `X-head`, `Y-head` | Inst §1 | $X_{s+1}$, $Y_{s+1}$ 的头是 $\Omega$-结点, 后者的种类是 `hd s` | 定理 (`refl`) |
| **`fed-exactly`**, **`deep-lossy`**, **`hd-inj-U`** | Inst §2 | 按级回灌的种类恰是 $(0,\mathrm{tt})$ 与头种类; 深种类无级回灌; 头种类两两不同 | 定理 |
| **`deep-noA`**, `deep1-A`, `deep1-H` | Inst §3 | 分量 $\ge2$ 的深种类也没有 A-回灌; 分量 1 只有底拷贝有 | 定理 (`refl`) |
| `KT-rd`, `start-hd` | Inst §4 | 头种类的读回是 `readS (sim s)`; 起始世界里头种类的界是 $0$ | 定理 (`refl`) |
| `Cp.kup`, `cE`, `cE⁻`, `cE-cE⁻`, `wpr`, `wins`, `wpr-wins`, `bd→`, `bd←`, `w₀-pr` | Deep §1 | `Lev (a ⊞ b)` 里 `Lev a` 的种类的拷贝 (对一切 `S`) | 定义; 定理 |
| `X1≡`, `κd`, `slot0` | Deep §2 | 分量 2 里第 1 站级的新种类的一族拷贝 (每个坐标 $c$ 一份) | 定理 (`refl`) |
| `PtUpdD`, **`updD-sep`** / `updD→WLPO` | Deep §3 | 这一族上一致的 "升一份留别份" ⇒ 分离子 | 定理 (否定) / 条件 (`FE₀`) |
| `halfK`, `halfR`, `halfR-moves` | Deep §3 | 两半各自可满足 (只升的一半整族一起升) | 定理 (前提实例) |
| **`no-wmatch-cp`**, `sat-hd`, `sat-cp` | Deep §4 | 拷贝 `κd c` 与头种类 `hd 0`: 没有双向保两份界的世界映射; 只保一份的存在 | 定理 (否定; 前提实例) |

## 前提实例

- `strat`: `draftFin` (`solFin` 是草稿形状, $z_s=0$).
- `hd-inj`: `hd-inj-inst` (`trivSt`, `ownTriv`, 世界 `w₀ GTf`); 构造一路实例 `hd-inj-U` (`StU`, `ownU`, `w₀ GU`).
- `no-total`: 任何 `StratTw` (`trivSt`, `StratTwTw.StU`).
- `updD-sep`: 两半 `halfR` (只升), `halfK` (只留). 分离子经典地成立 (判断); `FE₀` 在 Agda 里证不出也否证不了.
- `no-wmatch-cp`: `sat-hd` (只保头种类), `sat-cp c` (只保拷贝).

## 只否定什么, 不否定什么

- **否定** (编译的): 在 `StratTwTw.U` 分量 2 的拷贝族 `κd` 上一致的 "升一份留别份" (分离子; `FE₀` 下 WLPO); 双向保 `κd c` 与 `hd 0` 的界的世界映射; 级的高度类型等于总结构的高度类型. 反模型否定的推断: "有 `StratTw`/`OwnHd` 实例 ⇒ 前缀增长 / 级带 $\Omega$-结点 / 读回读了数据". `Cyc` 否定的推断: "停机失败 ⇒ 方程无解或依赖循环".
- **不否定**: 接口的任何记录; 构造一路的 `KT` (ℕ 下标点更新); 分层路线; 闭项 `TS` 的值 (没有 `ord` 定理); 拷贝族上 "一起升" (`halfR` 的形状, 未被否定, 未在折叠里用); 用折叠自己的读回升深种类的界. 本路**没有关闭任何路线**.

## 判断 (单列)

- **真循环.** 草稿的循环在定义形式 (类型 `HB (sup ℕ C)` 要整个族), 不在依赖 (`strat`); 分层把 "对角的项就是级" 换成 "前缀里的级 + 总结构里的同形项 + `Sim`" (`StratTwIf` 头说两者的 `Lev` 一般不相等). 是否有不经拷贝、检查器接受、级带 $\Omega$-结点的写法: 未定.
- **实例的强度.** 相对 KindLv (`only-κ₁`) 多了每站头种类的按级回灌 (读回是沿同形的 `readS`, 不是常数). 深种类全部有损 (`deep-lossy`, `deep-noA`), 第 $s+2$ 站的级读回经深种类 (拷贝) 看第 $s+1$ 级的高度, 那些拷贝的界只在基世界 (`slot0`) 或折叠自己升. 没有值定理; 读法不写.
- **推广.** `updD-sep` 只在分量 2 的一族上证明; 推到一切 $s$ 的论证相同 (`X-head` 对一切 $s$ 是定理), 没写. "深种类只剩一起升或折叠自升两种办法" 是判断 (穷尽), 下一路应先挑战它.

## 审计

- **编译.** 删本路五个模块的 `.agdai` (精确路径) 后从入口编译, 依赖用共享接口: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegStratTw.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 7 秒, 峰值常驻约 0.86G. 对着的构造文件: `StratTwIf` (19:13), `StratTwTw` (19:20).
- **导入闭包** (`importclosure.py`, 不加 `--only`): 五个模块都退出码 0, 禁用表命中 0.
- **禁用构造**: 五个文件的代码块里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`; `FE₀` 只作 `updD→WLPO` 的前提; 没有 UIP 前提.

## 文件

| 文件 | 内容 |
|---|---|
| `NegStratTwCyc` | 草稿的规格可满足, 依赖只向下 |
| `NegStratTwBlind` | 平凡实例; 对角与头种类两两不同; `no-total` |
| `NegStratTwInst` | 对 `StratTwTw` 实例的检查 |
| `NegStratTwDeep` | 级的拷贝, 分离子, 世界映射 |
| `NegStratTw` | 入口 |
