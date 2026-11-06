# 种类塔上的一级折叠: 否定一路的入口

> 不含记号. 本路是 `KcFold` (构造一路) 的配对**否定**一路 (手册 §5.2), 前缀 `NegKcFold`. 对着接口 [KcFoldIf](KcFoldIf.lagda.md) ("接口定稿 2026-11-05 15:44 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 分篇: [NegKcFoldDec](NegKcFoldDec.lagda.md) (可入判定), [NegKcFoldForget](NegKcFoldForget.lagda.md) (桥与下降不能是嵌入), [NegKcFoldTower](NegKcFoldTower.lagda.md) (世界塔, 读回分量的世界, 极限站). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延只在两条条件定理里作前提 (`FE₀` 在 `NegKcFoldDec.bare→WLPO`, `FEA` 在 `NegKcFoldTower.seeExact→WLPO`).
>
> **判决: 接口没有被否定; 接口的可入判定 `BDecTower` 是定理.** 四个嫌疑:
>
> 1. **嫌疑 (i) 推翻 (构造, 定理).** 高度坐标的可入判定在公共上界之下对一切站, 一切 `Lev c`, 极限 `KΛc` 都写得出 (`bdecTower : BDecTower`, `bdecΛ`, `bdecLev`). 外层世界长高后旧证据的判定就是以新世界为公共上界的同一条判定. 关键是每个种类在世界里有一个**顶坐标** (界本身, `TopK`), 合法的 $\Omega$-结点在小世界里的第一位置都经过顶坐标那一支, 于是 "大世界里的第一位置在小世界里是否仍是" 对高度结构递归可判 (`Shr.shr`), 不搜索坐标. 对照: 不带公共上界的判定撞分离子 (`bare-sep`; 条件 `FE₀` 到 WLPO).
> 2. **嫌疑 (ii) 不成立于接口, 落在接口没管的地方 (定理).** `WTower.grow` 只把旧站的 `inj₁ tt` 分量放在前一站之上, 嵌入拷贝的界因此一个方向相干 (`lim-emb`), 不撞 `no-emb`. 读回注入的 `inj₂ c` 分量没有律: 它可以是基世界 (`mixW`, 不是基世界的世界塔), 那时读回种类只剩底坐标 (`mix-inj`, `mix-LvW`). 要读回分量 "恰好看见外层可入的分支", 就是在裸坐标上判定, 撞分离子 (`seeExact-sep`; 条件 `FEA` 到 WLPO).
> 3. **嫌疑 (iii) 不成立 (判断, 有一条定理).** 接口没有跨种类的比较: `BDecK` 逐种类, `cmpB` 对一切种类结构一条; 不触壁垒. 但把高度降到 `Ht` 的下降, 与把带世界的层搬回 `Lev` 的桥, **不能逐结点嵌入** (`no-embDn`: 一切站的第 2 级; `no-embForget`, `no-embForgetΩ`: 极限与 $\Omega$-结点, 因为 `LvW` 每支多一层 `step`), 必须压掉高度坐标的 $\Omega$-结点.
> 4. **嫌疑 (iv) 不是接口的后果 (定理).** 极限站的世界由世界塔逐站给出 (`limW`, 合法, 相干一个方向). 撞 `code-botK` 的是基世界塔 (`baseW`, 它满足接口, `base-only`), 不是 "对一切站一条".
>
> **对纲领与目标.** 纲领 3 (壁垒): 唯一推出 WLPO 的两条定理判定的是裸坐标 (`bare→WLPO`) 或以裸坐标为下标的世界分量 (`seeExact→WLPO`); 带公共上界的判定是定理. 纲领 1: 本路的定理都对 `HB`/`Lev`/`LvW`, 不碰闭项. 目标 "让树自足": `TopK` (每个种类在世界里的顶坐标就是界) 是对一切种类结构一行一个构造子的树侧判据, 它把可入判定变成对高度的结构递归; 这一站新用到的字段是 `Bd κ c w → Pr κ w c (top κ w)` (`bdTop`, 由 `S₀`, `step`, `sup` 的定义直接给出).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKcFold where

open import OCF.Align.NegKcFoldDec public
open import OCF.Align.NegKcFoldForget public
open import OCF.Align.NegKcFoldTower public
  hiding (one)
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `TopK`, `topS₀`, `topStep`, `topSup`, `topLev`, `topNxt`, `topKc`, `topΛ` | Dec §1 | 每个种类的顶坐标 (界本身), 一切站与极限 | 定义; 定理 |
| `cyc`, **`Shr.shr`** | Dec §2 | 大世界里的第一位置在小世界里是否仍是: 可判定 (一切 `S` 带 `TopK`) | 定理 |
| `DecK`, `decStep`, `decSup`, `decLev`, `decKc`, `decΛ`, **`admKc`**, `admΛ`, `admLev`, `shrKc`, `shrΛ` | Dec §3 | 种类坐标的可入判定 (外层世界合法) | 定理 |
| `noLimFin`, `allFα`, **`bare-sep`** / `bare→WLPO` | Dec §4 | 裸坐标上判定 $x\lhd_{[0]}\omega$ ⇒ 分离子 / WLPO | 定理 (否定) / 条件 (`FE₀`) |
| `LgDown`, `dwKc`, `dwΛ`, `dwLev`, `toBDec`, **`bdecTower : BDecTower`**, `bdecΛ`, `bdecLev` | Dec §5 | 接口 §2 的 `BDecK` 对一切站, 极限, 一切 `Lev c` | 定理 (构造, 推翻嫌疑 i) |
| `cℓ`, `lg-cℓ`, **`no-embForget`**, `cΩ`, **`no-embForgetΩ`**, `botAdm`, `fin-same` | Forget §1 | 桥不能是 `Emb (LvW a c) (Lev c)` (极限, $\Omega$-结点); 有限层号上逐字相同 | 定理 (否定); 前提实例; 对照 |
| **`no-embDn`** | Forget §2 | 一切站: 没有 `Emb (Lev 2) S₁` | 定理 (否定) |
| **`baseW`**, `base-only` | Tower §1 | 基世界是 `WTower`; 其上 `LvW` 只剩底支 | 定理 (接口的盲区) |
| `wNx`, `aM`, **`mixW`**, `oneK`, `mix-sees`, `injBase-only`, **`mix-inj`**, **`mix-LvW`** | Tower §2 | 旧站分量长高、读回分量为基世界的 `WTower`; 读回种类只剩底坐标 | 定理 (接口的盲区) |
| `limW`, `lg-limW`, **`lim-emb`** | Tower §3 | 极限站的世界由世界塔给出, 嵌入拷贝相干一个方向 | 定理 (出口) |
| `SeeExact`, `nn-allF`, **`seeExact-sep`** / `seeExact→WLPO`, `see⁺`, `see⁻` | Tower §4 | 读回分量的世界恰好看见可入分支 ⇒ 分离子 / WLPO; 两半各自可满足 | 定理 (否定) / 条件 (`FEA`) |

## 每条律为什么是构造一路需要的

- **`BDecK`/`BDecTower`**: 接口 §2 原文. 带世界的读回过 $\Omega$-层第 $x$ 支的结点时要判定 $x$ 在外层世界里可入 (`LvOmRd.PΩ.ndS-Ω` 的形状); 坐标是高度时就是本篇 `admKc`. 构造一路目前只给了 `bdecS₀` (底上); 本路给出一切站.
- **`ForgetK`**: 接口 §5 "有了它, `FoldAllKW` 给出 `FoldAllK` 的读回". 读回要原样进下一站的层号 (`injL`), 所以有内容的桥是逐结点搬种类 (`Emb`). `no-embForget` 说这在极限与 $\Omega$-结点处不行.
- **`DnTower`**: 接口 §3; 构造一路的塔 (`KcFoldTower` §2, 只读观察) 的回灌输出**只经下降**看见读回 (`Hs-def`), 所以下降的形状决定值. `no-embDn` 说第 2 级起下降不能逐结点嵌入.
- **`WTower`**: 接口 §6 原文 ("`WTower` 要的是不取 `w0` 的、随站长高的外层世界"). 接口文字的意图没有进律: `baseW`, `mixW` 满足律.
- **`SeeExact`**: 不在接口里. 填 `WTower` 的读回分量时, "看见外层可入的分支, 别的不看" 是最直接的写法 (`LvKt` 接手清单第 3 条: 把读回搬进极限站的分量); 它要在裸坐标上判定.

## 前提实例

- `Shr.shr`, `admKc`: 实例世界 `w0 (ckc s)` (`lw0`), 任一合法世界 $W\ge a$ (`≤w-rf`). `bdecTower` 无前提.
- `bare-sep`: 判定的前提经典地可满足 (判断); `Lg-yα` 给出合法输入.
- `no-embForget`: 一切 `K`, 一切 $a$; `cℓ` 合法 (`lg-cℓ`). `no-embForgetΩ`: 可入坐标 `bot` 对一切世界存在 (`botAdm`). `no-embDn`: 一切站.
- `injBase-only`: `mixW` 的读回分量 (定义相等, `mix-inj`).
- `seeExact-sep`: 两半各自可满足 (`ρ⁺`, `ρ⁻`); 整体经典地可满足 (判断: 经典地 $x\lhd\omega$ 可判).
- `FE₀`, `FEA` 在 Agda 里证不出也否证不了 (与 `ColimWNeg`, `NegLvRdLay` 同档).

## 只否定什么, 不否定什么

- **否定** (编译的): 裸坐标上的可入判定 (分离子; `FE₀` 下 WLPO); 桥由 `Emb (LvW a c) (Lev c)` 给出 ($c=c_\ell$ 或 $\mathrm{h\Omega}\,\kappa\,(x\mapsto0)$); 下降由 `Emb (Lev 2) S₁` 给出 (一切站); 读回分量的世界恰好看见外层可入的分支 (分离子; `FEA` 下 WLPO).
- **不否定**: 接口的任何记录与定义. `BDecTower` 是定理; `ForgetK`, `DnTower`, `DnLim`, `GrowW`, `WTower`, `FoldTowerW`, `FoldLimKW` 都有实例 (常数实例; 构造一路的 `ftW`, `flW`; 本路的 `baseW`, `mixW`). 不否定有损的桥与下降 (把高度坐标的 $\Omega$-结点压成 ℕ-极限或限制到 `A` 的像, 判断: 可写); 不否定读回分量取不判定可入的非基世界 (`ρ⁺` 的形状). 路线状态: 本路**没有关闭任何路线**.

## 判断 (单列)

- **`GrowW` 的有内容的写法.** 种类方向 $(x,e)\mapsto(x,\mathrm{Bd}{\uparrow}\,q\,e)$ 是单射; 但 `step` 的新种类的坐标是 `HB (LvW a y)`, 在 `LvW a′` 里是 `HB (LvW a′ y)`, 逐结点搬要一个**反方向**的坐标映射 `HB (LvW a′ y) → HB (LvW a y)` (把大世界里的种类判回小世界: `bdecTower` 给得出, 以 $a'$ 为公共上界), 不可入的结点要压掉. 往返 (`cv ∘ vc = id`) 要判定给回原来的证据; `A` 上的证据是路径数据, 去后缀可判 (判断, 没有写). 没有找到否定.
- **读法.** `mixW` 上 `LvW` 在读回种类处只剩底支: 由 (R1) 的读法, 下一站的级顶 (`topW`) 在这些结点上读不到读回的增长. 这只是读法.
- **构造一路的现状 (只读观察).** `KcFoldTop` 的级顶在 $\Omega$-结点处只走底支 (它自己写了 "同 `code-botK` 的现象"); 读回不读外层世界 $a$. 所以本路关于世界的定理 (Tower) 目前不影响它的闭项; 影响的是它把 `KcFoldTop` 换成真正读世界的折叠的那一步.

## 审计

- **编译.** 四个模块 `OCF.Align.NegKcFoldDec`, `OCF.Align.NegKcFoldForget`, `OCF.Align.NegKcFoldTower`, `OCF.Align.NegKcFold` 删四个模块的 `.agdai` (精确模块名) 后从入口编译, 依赖用共享接口, `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegKcFold.lagda.md +RTS -M6G -RTS`, 退出码 0, 峰值常驻约 0.6G.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 四个模块退出码 0, 禁用表命中 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词; `--html` 由导入本入口与 `Om1HnAccept` 的 scratch 模块生成, 退出码 0): `bdecTower` 124/0/0, `bdecΛ` 126/0/0, `admKc` 113/0/0, `bare-sep` 83/0/0, `no-embForget` 73/0/0, `no-embForgetΩ` 73/0/0, `no-embDn` 77/0/0, `mixW` 112/0/0, `mix-LvW` 118/0/0, `base-only` 117/0/0, `lim-emb` 68/0/0, `seeExact-sep` 83/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 四个文件没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`; 函数外延只作两条条件定理的前提; 没有 UIP 前提.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `NegKcFoldDec` | 207 / 304 | 顶坐标, 缩世界的判定, 种类的可入判定, 裸判定的分离子, `BDecTower` |
| `NegKcFoldForget` | 34 / 75 | 桥与下降不能是 `Emb` |
| `NegKcFoldTower` | 93 / 164 | 基世界塔, `mixW`, 极限站的世界, `SeeExact` 的分离子 |
| `NegKcFold` | 6 / 本文件 | 入口 |
