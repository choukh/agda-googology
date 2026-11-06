# 局部 UIP 与 "只升 $c_0$" (入口): 构造一路

> 不含记号. 作者选定原话: "两条小引理先判定". 本篇是构造一路; 否定一路前缀 `LocUipNeg`, 共用接口 [LocUipIf](LocUipIf.lagda.md) (定稿 2026-11-05 10:45). 依赖 [AdmW](AdmW.lagda.md) 一族 (`SupB`, `Slot`, `raise₀ᴮ`, `Coh≡`) 与 [StallDiagnosis](../../Survey/StallDiagnosis.md) §2–§3. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 函数外延只在 [LocUipHed](LocUipHed.lagda.md) §5 作前提 (条件).
>
> **判决.**
>
> 1. **第一条引理 (局部 UIP): 在要求的形式下未走通; 它等价于合法高度上的 K (定理).** 主审的思路 "由 `bdec` 做局部 Hedberg" 编译出来是一个等价, 不是证明: `LocUIP w ⇔ DiagCst w lo` (`diag→loc`, `loc→diag`), 而 `DiagCst` 要判定在**同一坐标的两个不同证据**上给字面的 `refl`, 这本身就是一条局部 UIP. "局部" 也不比全局弱: 对一切合法世界的 `LocUIP` ⇔ `UIPᴸ` (`loc→uipᴸ`, `uipᴸ→loc`; 界自己就是可入坐标). 简报的另一写法 "`toLt` 在环上给 `refl`" ⇔ `UIPᴴ` (`loop→uip`, `uip→loop`). 够用这一半是定理: `LocUIP ⇒ IncIrr ⇒ Lemma1` (`loc→lemma1`), 有函数外延时成立 (`fe→lemma1`, 条件). 无条件的 `Lemma1` 未证, 也未否 (否定一路的事).
> 2. **证据无关的写法过了 (定理).** 把增量写成坐标的族 `Inc`, 更新只用判定的是/否, 不用它给的相等证明: `raiseFᴮ : RaiseF` 的五条律与 `OffF` 无条件成立, 其中 `cohF` 就是保 `Coh≡`; 合起来 `dirAᶠ` (保相干的更新 + 相干世界上的坐标比较) 无条件, 这是 `AdmWCoh.dirA-cond` 去掉 `UIPᴴ` 的族版本 ([LocUipFam](LocUipFam.lagda.md)). 并且 `raise₀ᴮ` 本身对 "族在 $c_0$ 处的值" 是相干的 (`fam→coh₀`); $c_0$ 是有限数时一切增量都是族的值, 所以 `raise₀ᴮ` 在有限坐标上无条件保 `Coh≡` (`fin-coh₀`).
> 3. **第二条引理 (只升 $c_0$ 够不够): 对读的那个界够, 对拷贝不够 (都是定理).** 回灌一步要的律写成 `Feed` ([LocUipFeed](LocUipFeed.lagda.md) §1): 只升 $c_0$ 满足它 (`feed-free` 无相干; `feedᶠ` 族增量带相干, 无条件; `irr→feed` 单个增量带相干, 条件 `IncIrr`). 但 `hs c₀` 的分量里有 $c_0$ 槽种类的拷贝; **一切只改槽的更新都不保拷贝相干** (`slotOnly→¬copy`; `raiseᴮ`, `raise₀ᴮ` 都只改槽). 同时升拷贝的族更新 `raiseFCᴮ` 写得出, 五条律加 `copyFC` 无条件. 所以 "回灌要不要拷贝相干" 决定答案: 要, 就必须升 $c_0$ 之上 (至少 `hs c₀`) 的分量. 回灌要不要它是**判断** (依据 `HtTowerNStage.no-wmatch`: 对角要的并, 同一种类只能有一个界); 本篇没有折叠, 没有定理.
> 4. **一级回灌与 κ₂ (构造 + 定理).** 在族更新上写了一级回灌 (读回作参数 `R`, `Chain`): 每格的世界合法, 相干, 单调, 第 $n$ 格有界, 链的 ℕ-极限有界. 实例 `K₂` ($c_0 = 1$, 分量与 `ChainZNeg` 的 `κ₂` 所在种类结构定义地相同, 读回取 `Ωtop S₀`): **含新种类节点的格在合法相干的世界里有界** (`κ₂-yes`, `κ₂-all`). 这与 `ChainZNeg.no-chain` (`growL′` 生成的世界里从不有界) 不矛盾: 世界不同族; 它说明可入下标上的选择性更新绕开了 `no-chain` 杀掉的那一族.
>
> **对纲领与目标.** 不触壁垒: 没有序, 没有全局三歧, 一切判定都在同一个界之下 (`dD` 只吃两个可入证据). 第一条引理的结果是信息: 拷贝墙在 `raise₀ᴮ` 处的确切形状是 "合法高度上的 K", 它不是禁忌, 但 `--safe --without-K` 给不出; 族的写法绕开它, 代价是回灌的读回要对一切坐标一致地给出 (第一个障碍). 第二条引理把 `no-wmatch` 那一线落成了一条定理 (只改槽不保拷贝) 与一条构造 (`hs` 这一步可以保).
>
> **交付拆成两条.** (a) 构造: `raiseFᴮ`, `raiseFCᴮ` (族更新, 律无条件), `Chain` (一级回灌, 读回作参数), 实例 `K₂`. 没有新的闭项 (没有折叠, 没有 FGH). (b) 值: **没有序数值定理.** 有的只是结构上的: `κ₂-strict` (第 $n$ 格是第 $n+1$ 格的严格子项, 子项序, 不是序数值; 手册 §3.3: 不当作强度), `cell-in-ω` (每格是极限格的第一位置). 读法 (判断): 一级回灌在第 1 级给出 κ₂ 处含新节点的格, 这是 `DiagK3`/`ChainZ` 停住的地方; 它到哪一站, 没有界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LocUip where

open import OCF.Align.LocUipIf public
open import OCF.Align.LocUipHed public
open import OCF.Align.LocUipFam public
open import OCF.Align.LocUipFeed public
```

## 接口

[LocUipIf](LocUipIf.lagda.md), 只有类型: `Lemma1` (= `RaiseCoh Coh≡ raise₀ᴮ`), `IncIrr` (卡住的那一步), `LocUIP`, `DiagCst`, `LoopRefl`, `UIPᴸ`; 族增量 `Inc`, 记录 `RaiseF` (`raiseF`, `atF`, `belowF`, `monoF`, `legalF`, `cohF`), `OffF`; 回灌律 `Feed`, `Feedᶠ`; 拷贝 `CopyCoh`, `SlotOnly`, `RaiseCopy`. 律里的每一对坐标都带同一外层世界的可入证据; `UIPᴸ`, `LoopRefl` 是对照用的全局陈述. 变更: 无 (定稿后只加了文件头的定稿时间).

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `diag→loc` | LocUipHed | 局部 Hedberg: `DiagCst w lo → LocUIP w` | 定理 |
| `loc→diag` | LocUipHed | `LocUIP w → DiagCst w lo` | 定理 |
| `uipᴸ→loc`, `loc→uipᴸ` | LocUipHed | 一切合法世界的 `LocUIP` ⇔ `UIPᴸ` | 定理 |
| `loop→uip`, `uip→loop` | LocUipHed | `LoopRefl` ⇔ `UIPᴴ` | 定理 |
| `loc→irr`, `irr→lemma1`, `loc→lemma1` | LocUipHed | `LocUIP` (一切合法世界) ⇒ `IncIrr` ⇒ `Lemma1` | 定理 (蕴含) |
| `fe→uipᴸ`, `fe→lemma1` | LocUipHed | `Funext → UIPᴸ`, `Funext → Lemma1` | 条件定理 (Funext) |
| `raiseFᴮ`, `offF` | LocUipFam | 族更新, 五条律 (含保 `Coh≡`) 与 `OffF`, 无条件 | 定理 |
| `dirAᶠ` | LocUipFam | 保相干的族更新 × `CmpKᶜ Coh≡` | 定理 |
| `raise₀≡F`, `fam→coh₀` | LocUipFam | `raise₀` 在族的值上与 `rF` 逐分量相等, 故保 `Coh≡` | 定理 |
| `extF-at`, `fin-coh₀` | LocUipFam | 有限坐标的增量延成族; `raise₀` 在 `fin n` 处保 `Coh≡` | 定理 |
| `feed-free` | LocUipFeed | `Feed (λ _ → ⊤)`, 由 `raise₀ᴮ` | 定理 |
| `feedᶠ` | LocUipFeed | `Feedᶠ Coh≡`, 由 `raiseFᴮ` | 定理 |
| `irr→feed` | LocUipFeed | `IncIrr → Feed Coh≡` | 定理 (蕴含) |
| `slotOnly→¬copy` | LocUipFeed | 满足 `at` 且只改槽的 `RaiseB` 不保 `CopyCoh` | 定理 (否定, 只否定只改槽的更新) |
| `¬copy-raiseᴮ`, `¬copy-raise₀ᴮ` | LocUipFeed | 同上的两个实例 | 定理 (否定) |
| `raiseFCᴮ`, `copyFC` | LocUipFeed | 同时升 `hs c₀` 拷贝的族更新, 五条律, 保 `CopyCoh` | 定理 |
| `Chain.*` | LocUipFeed | 一级回灌: `legal-n`, `legal-ω`, `coh-n`, `coh-ω`, `step-≤`, `lim-≤`, `cell-bd`, `cellω-bd`, `cell-in-ω` | 定理 (读回作参数) |
| `same-κ₂`, `coord-κ₂` | LocUipFeed | 坐标 1 的分量 = `Lev (up 2)`, 槽坐标 `HB S₁` | 定理 (`refl`) |
| `κ₂-yes`, `κ₂-all` | LocUipFeed | 合法相干世界里含新种类节点的 κ₂-格有界 | 定理 |
| `κ₂-strict` | LocUipFeed | 格在子项序里严格增长 | 定理 (结构, 不是序数值) |

## 前提实例

- `DiagCst`: 对角 $q=p_0$ 处成立 (`AdmWCmp.dec₀-diag`); 全体在 Funext 下成立 (`fe→uipᴸ` 推 `UIPᴸ`, 再 `uipᴸ→loc`, `loc→diag`).
- `LocUIP`, `UIPᴸ`, `LoopRefl`, `IncIrr`: 在 Funext 下成立 (`fe→uipᴸ`, `uip→loop ∘ AdmWUip.fe→uip`, `loc→irr`); 函数外延在立方模型中成立, 在本仓库只作前提.
- `slotOnly→¬copy` 的前提: `raiseᴮ`, `raise₀ᴮ` 都满足 `SlotOnly` (`refl`), 都满足 `at` (`AdmWRaise`, `AdmWCoh`); 世界 `(wO, v₀)` 合法 (`lgW₀`), 拷贝相干 (`copy₀`), 证据 `p₃`, `p₄` 是闭项, 增量 `δ₃` 合法.
- `Chain` 的参数: 实例 `K₂` (`wO`, `lo₀`, `v₀`, $c_0 = 1$, 证据 `p₁`, 读回 `famΩ`, 合法 `Lg-Ωtop S₀`); 基世界合法相干 (`lgW₀`, `coh≡₀`).

## 第一个障碍

**族的读回.** 族的写法要回灌的读回对**一切坐标**给出 (`R n u : Inc`), 只用 $c$ 本身 (不用证据). 回灌的读回在 $c_0$ 处算出 (输出树在第 $c_0$ 级的种类上). 化成族有三条路, 都没走通 (判断):
(i) 沿判定给的相等搬 (`incD`): 回到 `IncIrr`, 即 `UIPᴸ` (定理 `LocUipHed`).
(ii) 按构造子匹配坐标 (`extF`): 只对有限坐标 (`fin-coh₀`); 对有函数分支的 $c_0$ (如 $\omega$), 匹配 `hl g` 得到 `hl f ≡ hl g` 要 $f\equiv g$, 是外延.
(iii) 对坐标一致的读法 (`DiagK3Grow.embL` 一类): 只用底种类, 有损 (`DiagK3One.noNew-emb`).
所以 "穷尽" 这三条是判断; 下一路先挑战它. 第二处: 极限坐标的拷贝 (`hl f` 的分量 `sup ℕ`, 每个 $n$ 一份; `raise-splits` 的现象) 在 `raiseFCᴮ` 里没有处理, `CopyCoh` 只写了 `hs` 一步.

报错原文: 无 (各文件一次编译通过; 障碍是没有可写的项, 不是报错).

## 翻译账

本路不读记号. 新定义及来源:

- `LocUIP`, `DiagCst`, `LoopRefl`, `UIPᴸ`: 类型论的陈述, 不来自记号. 由 `--without-K` 下的 "两个证据" 逼出 (诊断 §3.3 义务 2).
- `Inc` 与 `raiseFᴮ` (族增量): 由 `Lemma1 ⇔ UIPᴸ` 逼出的换写法, 树侧 (类型论) 的要求; 序数值不需要它, 是脚手架.
- `CopyCoh`, `raiseFCᴮ`: 来自 `HtTowerNStage.no-wmatch` (树侧: 同一种类一个界); 字段形状由 `step` 的定义读出, 不读自基本列规则.
- `Feed`, `Chain`: 回灌形状 "读界, 升一个槽" 仍来自 `HtTowerFFold.RunM` (诊断 §4 第 4 条 (i) 记为翻译痕迹); 读回值取 "旧界接增量" (第 0 层 `sum W (z Y)` 的形式), 不取第 1 层 `rd b z` 的 "在旧界上读". 二者的关系 (在外延下相等) 是判断, 未证.

这一步: 摆脱侧为主 (两条否定/等价定理划出不能要的东西: 证据之间的相等证明; 只改槽的更新), 攀爬侧一小步 (一级回灌到 κ₂). 不加深翻译: 没有新构造子, 闭包定理没有新专属前提, 验收不用 `Lab`.
