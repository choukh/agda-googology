# `SL` 上带证据的回灌: 否定一路的入口

> 不含记号. 本路 (前缀 `NegSLFb`) 是 `SLFb` (构造一路) 的配对**否定**一路 (手册 §5.2). 作者本轮选定 (原话): "SL 上写带证据的回灌". 对着接口 [SLFbIf](SLFbIf.lagda.md) ("接口定稿 2026-11-05 20:06 (首次编译通过)"; 变更记录: 一条, 只改文字, 按 `akConst` 更正 `AK` 的盲区说明) 写, 导入它, 不另造接口. 分篇: 接口定稿前写的 [NegSLFbSep](NegSLFbSep.lagda.md) (一个含函数的站号上 "升一份留别份" 是分离子), [NegSLFbSh](NegSLFbSh.lagda.md) ("同级同界" 的世界证据); 定稿后写的 [NegSLFbBlind](NegSLFbBlind.lagda.md) (接口的盲区), [NegSLFbBd](NegSLFbBd.lagda.md) (接口 §4 各形状的边界与条件实例), [NegSLFbInst](NegSLFbInst.lagda.md) (对构造一路 `SLFbTm`, `SLFbKit`, `SLFbRd` 20:08–20:13 版的检查, 只读导入). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP 作前提; 函数外延 `FEΩ` 只在标 "条件" 的 `…→WLPO` 里作前提; `DecLH` (层号相等可判定) 只在标 "条件" 的实例里作前提.
>
> **判决: 接口没有被否定; 构造一路的出口 (站号 $\mathbb N$ 作证据, `SNᵢ`) 不撞本路任何一条否定. 它确实让每站头种类 (坐标是高度, 含第 $n\ge2$ 站的含函数层号) 有精确的、各自独立的回灌; 但读回喂进去的值只含第 0 层种类的结点 (`onlyA-rdQ`, `head-ak-lz`), 经坐标下标的深种类 (含头种类的同级拷贝) 仍有损 (`cp1-lossy`, `cp1-not-moved`). 在 `SL` 本身上: 任何形状加 "留别的分量" 都撞分离子 (头是 `lΩ` 的下标; 只要一个下标) 或在同界证据下直接是 $\bot$; 不加 "留" 时, 形状本身要 "插入" (对一切层号写出新世界, 在目标处含 $v$), 本路既未构造也未否定 (未走通).**
>
> **对纲领与目标.** 纲领 3 (壁垒): 推出分离子/WLPO 的都是 "在含函数的层号与裸下标之间判等" (`updP-sep`, `rsK+keep-sep`, `rsUp+keep-sep`, `rsEv+keep-sep`); `RsEv` 的字面公共上界证据只在目标下标上, "留" 比较的另一个下标没有证据, 所以仍撞墙 (这是律的定义域问题, 手册 §3.1). 构造一路把证据换成站号 (下标类型 $\mathbb N$), 不比较层号, 不撞. 纲领 1, 2: 本路不交新闭项; 构造一路的 `TF` 合法 (不在本路否定之列). 目标 "让树自足": 两条树侧事实 (定理): (a) **"同级同界" 就是 "世界是以层号为下标的截面"** (`shL-wG`, `sh→pair`, `pair→sh`), 在这种世界里同级的种类分不开 (`sh-νcp`, `fed-indist`), 回灌的内容只是截面在一点的值 (`inv→ext`), 而 "别的分量原样" 与之矛盾 (`no-inv-keep`); (b) **在 `SL` 上精确地升一个层号的界, 难处在 "插入" 本身, 不在 "留"**: 去掉 "留" 后没有可读出判定的信息 (判断), 而插入在 `DecLH` 下是构造 (`decLH→RsSL`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSLFb where

import OCF.Align.NegSLFbSep
import OCF.Align.NegSLFbSh
import OCF.Align.NegSLFbBlind
import OCF.Align.NegSLFbBd
import OCF.Align.NegSLFbInst
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `kα`, `patch`, **`eq→F`**, `wdec→sep` | Sep §1 | 一个 `lΩ k g` 旁的一族补丁层号; 补丁等于原层号 ⇒ $\alpha$ 全假 (不用外延) | 定理 |
| `F→eq`, `sep→WLPO` | Sep §1 | 反方向; 分离子 ⇒ WLPO | 条件 (`FEΩ`) |
| `PtUpdP`, **`updP-sep`**, `upd-sep`, **`updVP-sep`** | Sep §2 | 一个固定的 `lΩ k g` 上 "升 `νL s` 到 $\ge1$ + 不升裸下标 $k'\ne s$ 的 `νL k′`" ⇒ 分离子; 世界可带任一含基世界的证据 | 定理 (否定) |
| `updP→WLPO`, `stage-sep→WLPO` | Sep | 同上 ⇒ WLPO | 条件 (`FEΩ`) |
| **`tw-hΩ`**, **`stage-lΩ`**, **`stage-sep`**, `stage0`, `stage1` | Sep §3 | 第 $n+2$ 站的层号是 `lΩ lz g`; 其上的点更新 ⇒ 分离子 | 定理 |
| `halfR`, `halfK`, `upAllL-moves`, **`PtLz`**, **`PtLs`**, `p₀⊤` | Sep §4 | 两半各自可满足; 第 0, 1 站上点更新是构造 | 定理 (前提实例) |
| `wLv`, `wG`, `top-wG`, `top-wb`, **`shL-wG`**, **`shL-wb`**, **`sh→pair`**, **`pair→sh`** | Sh §1–2 | 同级同界的证据对一切截面可满足; 两种写法等价 | 定理 |
| `cpL`, `νL≢cp`, **`sh-νcp`** | Sh §3 | 可判定地不同的两个同级种类同界 | 定理 |
| **`sh-moves`**, `sh-moves-cp`, **`fed-indist`**, **`inv→ext`** | Sh §3 | 精确置一个就置了整级; 回灌哪个读出相同; 回灌是截面的一个值 | 定理 (盲) |
| **`no-inv-keep`**, `hs-nofix` | Sh §4 | 同界证据 + `RsInv` + 别的分量原样 ⇒ $\bot$, 对一切 $s$ | 定理 (否定) |
| **`sh-upd-sep`** | Sh §4 | 同界证据上留别的级 ⇒ 分离子 | 定理 (否定) |
| `Pw`, `Pw→ShL`, `pw-inst`, **`rsLz`**, `rsLz-moves`, `stayKeep`, `rsLz-no-keep` | Sh §5 | `lz` 上带截面证据的 `RsInv` (构造), 它动了别的分量 | 定理 (前提实例) |
| **`akConst`** | Blind §1 | `AK` 被常数读法满足, 对一切 `Q`, κ (接口已据此在变更记录里更正一句判断) | 定理 (盲) |
| **`kcTriv`** | Blind §2 | `KC` 被 `ad b a = b` 满足 | 定理 (盲) |
| **`hdTriv`**, **`hd-rd-blind`**, `hd-ℓ0`, `deep-lossy` | Blind §3 | `HdFb` 被读回恒取起点, 级层 0 的实例满足 (对一切 `ix`, $\Lambda$) | 定理 (盲) |
| **`rsSLᴾ-empty`**, `rkLz`, **`rsEv-hz`** | Blind §4 | 空证据; $\Lambda^*=0$ 时 `RsEv` 有实例 | 定理 (盲) |
| `rsK→pt`, `rsUp→pt`, `rsK→rsUp` | Bd §1, §3 | 形状 + 留 ⇒ 点更新; 精确升界 ⇒ 一起抬高 | 定理 |
| **`rsK+keep-sep`**, **`rsSL+keep-sep`**, **`rsUp+keep-sep`**, **`rsEv+keep-sep`** | Bd §2 | 接口 §4 每个形状 + 裸下标的 "留" ⇒ 分离子 | 定理 (否定) |
| `rsEv+keep→WLPO` | Bd §2 | 同上 ⇒ WLPO | 条件 (`FEΩ`) |
| **`rsSLᴾ+keep-⊥`**, `shL-inst` | Bd §2 | `RsSLᴾ` + 同界证据 + 别的分量原样 ⇒ $\bot$ | 定理 (否定) |
| **`rkLz-keep`** | Bd §3 | `lz` 上 `RsK` 与 "留" 同时成立 | 定理 (前提实例) |
| **`decLH→RsSL`**, **`decLH→keep`**, `decLH→RsSL⊵`, `decLH→sep` | Bd §3 | 层号可判定时 `RsSL`, `RsSL⊵` 与 "留" 同时成立 (UIP 由 Hedberg 得出) | 条件 (`DecLH`) |
| **`onlyA-rdQ`**, **`head-rd-onlyA`** | Inst §1 | 级层 1 的读回只产出一个种类的 $\Omega$-结点 | 定理 |
| **`akV-lz`**, `akSt-lz`, **`head-ak-lz`** | Inst §2 | 第 $m+1$ 站头的读回用的种类级是 `lz` | 定理 |
| `cp1`, `cp1-lvl`, `cp1-coord`, `cp1≢head1`, **`cp1-lossy`**, **`cp1-not-moved`**, `head1-moved`, `rs1-other` | Inst §3 | 第 3 站里第 1 站头的同级拷贝有损, 头的回灌不传给它; 各站头的升界互不影响 | 定理 |

## 前提实例 (逐条)

- `updP-sep` / `updVP-sep` / `stage-sep`: `PtUpdP` 的两半 `halfR` (只升), `halfK` (只留) 各自可满足; 下标可判定处 (`lz`, `ls lz`) 整个前提成立 (`PtLz`, `PtLs`); 证据类 $P$ 含基世界的实例: $P=\top$ (`p₀⊤`), $P=$ `ShL` (`shL-wb`).
- `no-inv-keep` / `rsSLᴾ+keep-⊥`: 证据类 `Pw` ⊆ `ShL` 且非空 (`Pw→ShL`, `pw-inst`); `RsInv` 存在 (`rsLz`, 在 `lz`); `KeepC` 单独由不动的操作满足 (`stayKeep`). 两者合起来不可满足, 这正是定理.
- `rsK+keep-sep`, `rsSL+keep-sep`, `rsUp+keep-sep`: `RsK` 与 `Keep` 在 `lz` 同时成立 (`rkLz`, `rkLz-keep`); 在一切层号上同时成立的条件实例 `decLH→RsSL`, `decLH→keep`, `decLH→RsSL⊵` (前提 `DecLH`, 经典地成立, 判断).
- `rsEv+keep-sep`: `RsEv` 的前提 (世界 $w^*$, $\Lambda$) 任取; 站带证据由 `FabLFReGen.stage-fst` 给出 (对一切世界). `RsEv tpL w* Λ` 本身的无条件实例本路没有 (`decLH→RsSL` 给条件实例); $\Lambda^*=0$ 时有 (`rsEv-hz`).
- `sh-upd-sep`: `ShL` 含基世界 (`shL-wb`).

## 只否定什么, 不否定什么

- **只否定**: (1) 在 `SL` 的世界 (或含基世界的子类) 上, 对头是 `lΩ` 的层号 $s$, "升 `νL s`" 与 "对裸下标 $k'\ne s$ 不升 `νL k′`" 同时成立 (分离子; 加 `FEΩ` 得 WLPO); 接口 §4 的四个形状加上这条 "留" 都落在这里. (2) 同界证据类上精确升界与 "别的分量原样" 同时成立 ($\bot$, 对一切 $s$).
- **不否定**: 接口 `SLFbIf` 的任何记录 (都有实例, 见 Blind); 构造一路的闭项 `TF` 与站号证据的出口 `SNᵢ`; `RsSL`, `RsSLᴾ`, `RsSL⊵`, `RsEv` 本身 (不加 "留"; 未走通, 也未否定); 同界证据本身 (可满足); 有损回灌.

## 判断 (单列)

- 分离子 `SepAt` 与 `DecLH` 经典地成立; `FEΩ`, `DecLH` 在 Agda 里证不出也否证不了 (与 `FE₀` 同档).
- 不加 "留" 时, §4 的形状要 "插入": 对一切层号 $k'$ 写出新世界并在 $k'\equiv s$ 处含 $v$. 插入单独不含可读出判定的信息, 所以本路认为它推不出分离子 (未写定理). 一条候选是逐结构的搬运 `HB (Lv s) → HB (Lv k′)`, 在 $k'\equiv s$ 时恒等要函数外延; 未写.
- 起点为 $0$ 时, 折叠喂给 `TF` 的头种类的值只含第 0 层种类的结点: 由 `onlyA-rdQ`, `head-ak-lz` 加 "折叠只把读回值写进界" 得出, 后者未写成定理. 头种类的同级拷贝在以后每站都有, 只验了一个 (`cp1`). `TF` 的值没有定理.
