# 补四条正面判据, 否定一路: 新判据确定了什么, 没确定什么

> 不含记号. 作者选定原话: "补四条正面判据". 本路前缀 `NegTL2` (否定), 与构造一路 [TL2](TL2.lagda.md) 配对, 共用接口 [TL2If](TL2If.lagda.md) ("接口定稿 2026-11-05 21:12 (首次编译通过)", 变更记录: 无); 导入它, 不另造接口, 不改它与构造一路的文件. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP. 本路没有条件定理.
>
> **判决.** 四条判据各自排除了上一对指出的候选 (构造一路的定理, 本路的 `diag-not-cross-id`, `pz-no-bdF` 等与之一致), 但**仍被明显不同的定义同时满足**:
>
> 1. **(i) 不定世界里的界 ([NegTL2Pre](NegTL2Pre.lagda.md), [NegTL2Ord](NegTL2Ord.lagda.md)).** 候选 `LevP P`: 与 `Lev` 同一递归, 只是后继一步的世界高度分量取自 $\Sigma\,b.\,P\,b$. 对一切 `P` 满足 `LvCrit`, `LvUpper`, `OrdCrit` (`ordP`), 种类与 `Lev` 逐个对应保级 (`kmP`), 有合法的非常值 Ω-分支 (`Lg-upΩP`). 但 `P = (≡ hz)` 时新种类的 Ω-结点在第一位置上塌成第 0 支 (`pz-coll`; `blind-i`: `Lev` 里 $1\lhd\mathrm{h\Omega}\,\mathrm{up}$, `LevP Pz` 里对一切世界不是); `P = NatH` 时只经过有限坐标 (`blind-iω`). 比上一对的平的候选 `Fl` 难排除: `Fl` 被 (i) 排除 (构造一路 `no-ord-Fl`), 这些不被.
> 2. **(ii)–(iv) 约束框架, 不约束候选 ([NegTL2Raise](NegTL2Raise.lagda.md)).** 接口的框架 (`RaiseFrame`, `DFrame`, `HKey`, `OrdFrame`) 与 `LvRule` 之间没有字段相连. `all4`: 任一满足 `LvCrit`, `LvUpper`, `OrdCrit` 的候选都满足全部四条, 框架部分用同一组非平凡实例 (`Pos` 框架, 真的 $\le$ 序, 截面升界). 所以 `Lev`, `LevP Pz`, `LevP Pn`, `LevD` 同时满足全部判据 (`all-Lev`, `all-Pz`, `all-Pn`, `all-D`). 分条的盲: (ii) `Cross F H` 取决于框架自选的 `HKey`: 上一对 "一起升" 的 `supD` 对恒等键不满足 (`diag-not-cross-id`, 与构造一路 `no-cross-diag` 一致), 对另一个合法的键 `tagH` 满足 (`diag-cross`, `blind-ii`); (iii) 序由框架自选: 平凡序下任一升界都是 `RaiseUp`, 降值照样 (`triv-lowers`).
> 3. **绑到候选自己的世界上就分开 `LevP`, 但分不开重数 ([NegTL2Raise](NegTL2Raise.lagda.md) §4, [NegTL2Bd](NegTL2Bd.lagda.md)).** 读数取候选第 1 层世界的界, 序取种类结构自己的 `≤w` 与 `⊲`: `Lev` 有 `RaiseUp` (`lev-own-up`), `LevP Pz`, `LevP Pn` 没有 (`pz-own-no-up`, `pn-own-no-up`); 构造一路的界框架 `TL2Raise.BdF` 上, **对一切** `top`, `LevP Pz`/`Pn` 都没有 `RaiseUp` (`pz-no-bdF`, `pn-no-bdF`). 但 `LevD` (后继一步加两个同形的新种类) 与 `Lev` 一样满足全部判据加界框架 (`blind-final`), 而第 1 层级为 0 的种类 `Lev` 只有一个, `LevD` 有两个 (`one-at-0`, `two-at-0`).
> 4. **(iv) 的边界 ([NegTL2Raise](NegTL2Raise.lagda.md) §5).** 跨级族: 相邻两级可以同在一个截面框架里 (`adj-ok`; 上一对的 `raise-adj` 在 (iv) 下不成立, 与构造一路 `Adj.adj-free` 一致). 新的墙: 定义域含自身对且有截面扩张的成员, 其读数类型是世界的收缩 (`d-ret`); 所以世界不能收缩到低一级的坐标 (`d-adj`, 由 `no-retract`): 共享槽 (`NegSlotWall.slot-ret` 的形状) 在 (iv) 下仍被排除, 积世界不受影响. 截面升界不容 "真拷贝" (同键同读数的两个成员, `d-nocopy`, `copies-split`: 同一框架上 `Raise` 有, `DRaise` 没有). 读数不变时 `DRaise` ⇒ `Raise` (`draise→raise`), 所以 `Lev` 裸坐标积世界上的截面升界也推出分离子 (`dsup-bare→Sep`).
>
> **对纲领与目标.** 纲领 1–4 不受影响: 本路只有种类结构与框架上的定理, 不读记号, 无公理, 律都带证据 (`Cross` 的前提是字面公共上界). 目标 "让树自足" (判断): 四条判据是**验收**现有形状的判据, 不是**写出**定义的判据. 它们确定了种类的第一位置是坐标的 `⊲` (i), 共界成员上升界唯一 (ii, 构造一路 `cross-unique`), 界框架上界够多 (iii, 构造一路 `up→rich`); 但 (a) 接口里框架与候选没有字段相连, (ii)–(iv) 对候选是盲的 (`all4`); (b) 即使绑上 (界框架), 重数不定 (`blind-final`). 若要判据写出定义, 下一步要的判据 (判断): "框架由候选给出" 的字段 (世界取候选每一层的世界, 键取候选的高度, 序取 `≤w` 与 `⊲`, 每个新种类配一个界框架); 一条关于重数的判据 (例如 "同级同形的种类只有一个", 或拷贝相干). 写进判据前都要算翻译账: 前者读自 `step`/`sup`/`RsK`, 后者针对 `LevD`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTL2 where

open import OCF.Align.NegTL2Pre public
  using (stepP; LevP; Pz; Pn; Lg-upΩP; upP-nc; pz-coll; pn-coll; pz-noreach; pn-noreach; lev-reach; lev-reach-lim;
         stepD; LevD; two-at-0; one-at-0; PrSup; PrSub; BdAt; Rich; fl-sup; fl-not-sub; pz-not-rich; pn-not-rich; lev-rich; D-all)
open import OCF.Align.NegTL2Ord public
  using (ordP; ordLev; ordD; kmP; kmP⁻; kmP-lv; blind-i; blind-iω; blind-D)
open import OCF.Align.NegTL2Raise public
  using (tagH; diag-cross; diag-not-cross-id; tag-inst; blind-ii; trivO; triv-grow; raise→up; triv-lowers; grow-pos;
         All4; all4; all-Lev; all-Pz; all-Pn; all-D; lev-own-up; pz-own-no-up; pn-own-no-up;
         adj-ok; d-ret; d-adj; d-nocopy; copies-split; draise→raise; dsup-bare→Sep; adj-half; slot-half)
open import OCF.Align.NegTL2Bd public
  using (pz-no-bdF; pn-no-bdF; pz-top; pn-top; levD-up; blind-final)
```

## 定理表 (按档)

| 名字 | 陈述 (简) | 文件 | 档 |
|---|---|---|---|
| `stepP`, `LevP`, `stepD`, `LevD` | 合法的 `KS` (对一切 `P`) | Pre | 构造 |
| `CP`, `UP`, `same-levelsP→/←`; `CD`, `UD`, `same-levelsD→/←` | `LevP P`, `LevD` 满足 `LvCrit`+`LvUpper`, 级集合与 `Lev` 相等 | Pre | 定理 (前提实例, 盲) |
| `Lg-upΩP`, `upP-nc` | `LevP P` 有合法非常值 Ω-分支 | Pre | 定理 |
| `pz-coll`, `pz-noreach`, `pn-coll`, `pn-noreach`; `lev-reach`, `lev-reach-lim` | `Pz`/`Pn` 的 Ω-结点第一位置塌缩/只经有限坐标; `Lev` 不 | Pre | 定理 |
| `fl-sup`, `fl-not-sub`, `P-sup`, `P-sub`, `P-bd`, `pz-not-rich`, `pn-not-rich`, `lev-*`, `D-all` | "顺序一致" 四种写法各被谁满足 | Pre | 定理 |
| `two-at-0`, `one-at-0` | 重数: `LevD` 第 1 层两个级-0 种类, `Lev` 一个 | Pre | 定理 |
| `ordP`, `ordLev`, `ordD` | 三族候选满足 `OrdCrit` | Ord | 定理 (前提实例) |
| `kmP`, `kmP⁻`, `kmP⁻kmP`, `kmPkmP⁻`, `kmP-lv` | `LevP P` 与 `Lev` 种类逐个对应保级 | Ord | 定理 |
| `blind-i`, `blind-iω`, `blind-D` | 同时满足 (i) 与上一对判据, Ω-结点第一位置不同 | Ord | 定理 (盲) |
| `tagH`, `tag-key`, `diag-cross`, `diag-not-cross-id`, `tag-inst`, `blind-ii` | `Cross` 取决于 `HKey`; `supD` 对 `tagH` 满足 | Raise | 定理 (盲) |
| `trivO`, `triv-grow`, `raise→up`, `triv-lowers` | 平凡序下任一升界是 `RaiseUp`, 仍降值 | Raise | 定理 (盲) |
| `ordN`, `grow-pos`, `upPos`, `dposR`, `dgrow-pos`, `crossPos`, `dcrossPos` | 真的序下 `Pos` 框架的实例 | Raise | 定理 (实例) |
| `All4`, `all4`, `all-Lev`, `all-Pz`, `all-Pn`, `all-D` | 满足 (i) 与上一对判据的候选都满足全部四条 | Raise | 定理 (盲) |
| `lev-own-up`, `pz-own-no-up`, `pn-own-no-up` | 绑到自己的世界: `Lev` 有 `RaiseUp`, `LevP Pz/Pn` 没有 | Raise | 定理 |
| `adj-ok` | 相邻两级同在一个截面框架, 有 `DRaise` | Raise | 定理 |
| `dset-onto`, `d-ret`, `d-adj`; 实例 `adj-half`, `slot-half`, `extF` | 读数是世界的收缩; 世界收缩到低一级坐标 ⇒ ⊥ | Raise | 定理 (边界) |
| `d-nocopy`, `copies-split` | 截面升界不容真拷贝; `Raise` 容 | Raise | 定理 (边界) |
| `draise→raise`, `dsup-bare→Sep` | 读数不变时 `DRaise` ⇒ `Raise`; 裸积世界 ⇒ 分离子 | Raise | 定理 |
| `pz-no-bdF`, `pn-no-bdF`; `pz-top`, `pn-top` | 构造一路的界框架: 对一切 `top`, `LevP Pz/Pn` 无 `RaiseUp`; 前提可满足 | Bd | 定理 |
| `levD-up`, `blind-final` | `Lev` 与 `LevD` 满足全部判据与界框架, 重数不同 | Bd | 定理 (盲) |

## 只否定什么, 不否定什么

- **否定 (编译过的定理):** 推断 "四条判据 (连同上一对的 `LvCrit`, `LvUpper`) 确定了定义"; 推断 "(i) 排除了 Ω-结点塌缩的候选"; 推断 "(ii) 排除了一起升" (对框架自选的 `HKey`); 推断 "(iii) 排除了降值" (对框架自选的序); 一个截面框架里 "世界收缩到低一级的坐标" 与 "高一级可升" 并存; 截面升界与真拷贝并存.
- **不否定:** 构造一路的任何定理 (`no-ord-Fl`, `ord-dec`, `ord-antisym`, `ord-mono`, `no-cross-diag`, `cross-unique`, `lower-blocked`, `DPos.dR`, `adj-free`, `up→rich`, `no-up-frozen`; 本路的结果与它们一致, 本路用到的 `BdF.no-up-pred` 编译通过); 四条判据本身; 判据路线; 给接口加 "框架由候选给出" 与重数判据之后的唯一性 (未写, 未否定). 本路没有关闭任何路线.
- **前提可满足:** 每条否定的前提都有实例: `pz-top`, `pn-top` (`pz-no-bdF` 的 `top`, `tb`, `tm`); `adj-half`, `slot-half` (`d-adj` 的两半, 各自可满足, 合起来正是被否定的); `copies-split` 的框架有 `Raise`; `tag-inst` (`Cross` 对 `tagH` 的前提非空: 合法世界, 合法高度, 共界的对); `lev-reach`, `lev-reach-lim` (对照的前提是合法世界).

## 判断 (单列)

1. 接口的四条判据是验收现有形状的判据; 它们与候选之间缺 "框架由候选给出" 的字段. 依据 `all4` (证明不看候选).
2. 重数的自由度不被 "对每个种类/每个框架" 形式的判据看见. 依据 `blind-final`, 只对第 1 层写成定理.
3. `LevD` 与 `Lev` 的序数值相同 (判断, 两个拷贝共用同一个界); 未写定理.
4. 穷尽是判断: 上面列的 "下一步要的判据" 不是唯一的办法.
