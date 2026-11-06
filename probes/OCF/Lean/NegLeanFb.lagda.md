# 级回灌参数 `Fb` 与接口 `LeanFbIf`: 否定一路 (入口)

> 不含记号. 与构造一路 `LeanFb` 配对; 接口 [LeanFbIf](LeanFbIf.lagda.md) ("接口定稿 2026-11-05 21:23", 22:00 只改文字). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 (`FEℕL`, `FEΩL`) 只在标 "条件" 的定理里作前提.
>
> **判决: 没有关闭任何路线.** 否定定理只杀写明的形状 (各文件头的 "只否定什么"). 构造一路的实例 `TF` 的回灌行在闭项的计算里出现 (定理), 新种类的回灌不出现 (定理加一行读法), 剩下有损的种类包括含函数下标的整族 (定理).

## 对纲领与目标

- **纲领第 3 条 (壁垒) 的影子.** "升一份留别份" 在以层号为下标的世界上是分离子 (`NegLeanFbPre.wdec1`, `cross-sep`, `stage-sep`; `NegLeanFbBlind.upPt-sep`): 只要**一个**世界只升一个含函数层号的界而别处不动. 构造一路的出路 (站以 $\mathbb N$ 为下标, 同级拷贝在数字层号上一起升) 不撞这条, 代价是数字层号以外的深种类有损 (`NegLeanFbInst.lossy-hl`).
- **目标 (让树自足) 的读法 [判断].** 接口 `LeanFbIf` 的律都带字面上界 (一个成员, 一个世界), 不比较两个下标, 这一点按手册 §3.1 写对了. 但接口本身不逼回灌读数据 (`rdConst`), 不逼成员是不同的种类 (`upCopies`), 一个 `Up` 不能跨级 (`no-up-co`, `no-ι-co`); 所以 "按级回灌" 是否成立只能在实例上查, 查的结果是: 第 $n\ge2$ 站的头的回灌只按一个级 0 种类增长 (`rdX-one-kind`).

## 文件

| 文件 | 内容 | 依赖 |
|---|---|---|
| [NegLeanFbPre](NegLeanFbPre.lagda.md) | 接口之前: `Fb` 的盲区 (`stayFb`, `relevelFb`, `stay-wA`, `relevel-u`); 执行条件 (`exec-old`, `hd-target`); `Λ′` 里的跨级族 (`cross-tg`, `dep-kc`, `kc-*-not-station`); 一个只升一层的世界 ⇒ 弱判定 ⇒ 分离子 (`wdec1`, `cross-sep`, `stage-sep`, `fb-cross-sep`; 条件 WLPO); 前提实例与 `allFb` | `LeanT*` |
| [NegLeanFbKD](NegLeanFbKD.lagda.md) | 折叠的数据不变式: 闭包结点的种类满足 $P$ 被一切折叠行保持 (`kd-Run` 等 15 条); `TΛ′-old` | `LeanT*`, Pre |
| [NegLeanFbBlind](NegLeanFbBlind.lagda.md) | 接口的盲区 (`rdConst`, `upCopies`, `planStep`, `const-u`); 成员分不开 (`same-stays`, `same-iter`); 边界 (`no-up-co`, `no-ι-co`, `upPt-sep`, `upPt-sepLΩ`; 实例 `upPtLz`) | `LeanFbIf`, Pre |
| [NegLeanFbInst](NegLeanFbInst.lagda.md) | 对构造一路实例 `TF` 的检查: `exec-TF0/1/2` (回灌在闭项里出现), `ctrl-TL0`; `TF-old`; `lossy-hl`, `lossy-hl-target`; `rdX-one-kind`; `slot-start`, `slot-merge` | `LeanFb*` (只读), KD, Blind |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanFb where

import OCF.Lean.NegLeanFbPre
import OCF.Lean.NegLeanFbKD
import OCF.Lean.NegLeanFbBlind
import OCF.Lean.NegLeanFbInst
```

## 定理表 (按档)

**[定理, 盲] (只说接口或记录不逼什么)**

- `NegLeanFbPre.stay-wA`: 用 `stayFb` 时级回灌每一格的世界 ≡ 当前世界 (一切 $T,\Lambda$, `bk`, `fb`).
- `NegLeanFbPre.relevel-u`: 任一 `Fb` 改成级层 $0$ 且升界不看数据后, 每一格的 (世界, 合法) 与分支, 动作, 累计, 状态无关.
- `NegLeanFbBlind.rdConst`: `LvRd` 被 "级层 $0$, 读回恒为 $1$" 满足 (一切 $T,\Lambda,Q$). 接口原文 "`δ-n1` 排除不看数据" 因此更正 (构造一路 22:00 改文字).
- `NegLeanFbBlind.upCopies`, `copies-same`, `planStep`, `const-u`.
- `NegLeanFbBlind.same-iter`: 同一个 `Up` 的两成员读数相同, 经它任意次升界后仍相同; `NegLeanFbInst.slot-start`, `slot-merge`: 构造一路的 `slotUp j` 在基世界里一切成员读数为 $0$, 所以只经它升界时读数恒相等.

**[定理, 否定]**

- `NegLeanFbPre.wdec1`: 在 `SL` 的世界里, 一个世界 $W$ 把 `νL s` 的界升到 $\ge1$, 别的 `νL k` 在 $W$ 里不高于基世界 ⇒ $\forall k.\ \neg(k\equiv s)\vee\neg\neg(k\equiv s)$. 推论 `cross-sep` ($s$ = `kc (hl f)` ⇒ `SepLl`), `stage-sep` ($s$ = 第 $n+2$ 站 ⇒ `SepLΩ`), `fb-cross-sep`. **[条件 `FEℕL`/`FEΩL`]** `cross-WLPO`, `stage-WLPO`.
- `NegLeanFbBlind.no-up-co`: `Up T (step S′)` 的成员读数经 `up` 进来, 有一个世界 ⇒ ⊥. `no-ι-co`: `Q = sup I F`, 成员经 `ι i`, 另有 $i'\ne i$ 的种类 ⇒ ⊥.
- `NegLeanFbBlind.upPt-sep`, `upPt-sepLΩ`: 单成员 `Up` 加 "留别份" 在 `ll`/`lΩ` 层号上 ⇒ 分离子.

**[定理, 形状与执行]**

- `NegLeanFbPre.exec-old` (局部), `hd-target`; `NegLeanFbKD.kd-Run` (闭包结点种类被保持), `TΛ′-old`.
- `NegLeanFbPre.cross-tg`: `Λ′` (LeanT) 对每个合法 $c$ 有目标层头为 `inj₁ (νL (kc c))`; 层号两两不同, $c\ne0$ 时不是站.
- `NegLeanFbInst.exec-TF0`, `exec-TF1`, `exec-TF2`: 构造一路闭项 `TF` 的第 0 层数据沿显式路径的子项字面地是 `RKa _ (fb (νS n)) …` ($n=0,1,2$, 三种回灌). `ctrl-TL0`: 同一路径在全有损折叠上是常值序列.
- `NegLeanFbInst.TF-old`; `lossy-hl` (∀ $f$), `lossy-hl-target`; `rdX-one-kind`.

**[判断]** (各文件结论段单列)

- "回灌行在 $\kappa$ 上执行 ⇒ $\kappa$ 在 $\Lambda$ 里出现" 与 "`TΛ′`/`TF` 不执行新种类的回灌": 定理 `kd-Run` 加 `Run` 的 `nc` 子句一行读法.
- `lossy-hl-target` 的目标是否在 `TF` 的计算里被走到: 未证; 由 `rdX-one-kind` 判断可能走不到.
- 不带留别份律的单成员 `Up` 在含函数层号上是否存在: 没构造, 没否定.
- `SepLl`, `SepLΩ` 经典地成立; `FEℕL`, `FEΩL` 在 Agda 里证不出也否证不了.

## 前提实例 (否定与条件定理的每个前提)

| 定理 | 前提 | 实例 |
|---|---|---|
| `wdec1`, `cross-sep`, `stage-sep` | `Raise s W` | `raise-all` (`wAll`) |
| 同上 | `Keep s W` | `keep-wb` (`wb`) |
| 同上 (两半同时, 可判定层号) | — | `raise-Ls`, `keep-Ls` (`ls lz`) |
| `cross-tg` | `LgB c` | 一切有限 $c$ (例如 `hz`: `tt`) |
| `no-up-co` | `Up T (step S′)`; 一个世界 | `upCopies (step S′) J`; `w₀ T` |
| `no-ι-co` | `Up T (sup I F)`; $i'\ne i$ 有种类 | `upCopies (sup I F) J`; 例如 $I=\mathbb N$ 的 `SLs` |
| `upPt-sep` | `UpPt s` | `upPtLz` (在 `lz` 上可构造; 在 `ll`/`lΩ` 上被定理否定) |
| `same-iter` | 两成员读数相同 | `same-copies`, `slot-start` |
| `TΛ′-old`, `TF-old` | `AllK OldK Λ` | `old→all … old-Λ′`, `old→all … (old-up Λs)` |
| 条件定理 | `FEℕL`, `FEΩL` | 不可在 Agda 里给出, 也不矛盾 (判断) |
