# 树的语言, 否定一路: 判据确定了什么, 没确定什么

> 不含记号. 与构造一路 [TreeLang](TreeLang.lagda.md) 配对, 共用接口 [TreeLangIf](TreeLangIf.lagda.md) ("接口定稿 2026-11-05 20:27 (首次编译通过)", 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延只在一条条件定理 (`NegTreeLangPre.pt-SL→WLPO`, 前提 `FEL`) 里作前提.
>
> **判决.** 构造一路的形状定理 (`TreeLangLv.exact→`, `exactL→`, `TreeLangRaise.shape`, `unique`, `sup-bare→Sep`, `pos-unique`) 都对, 前提都有实例. 但它们确定的是**级集合**与**定义域里的读数**, 不是定义: 判据被明显不同的定义同时满足, 其中一个在值上退化.
>
> 1. **今天的否定性判据单独给不出正面指引** ([NegTreeLangPre](NegTreeLangPre.lagda.md), 接口定稿之前). `crit₄`: `no-retract`, `no-inflate`, `lv-not-self` 的一般形, `no-slot-adj` 写成种类结构上的谓词, 对一切种类结构成立 (筛子不排除任何定义). `null-crit`: 全有损的回灌对一切种类结构满足全部五条 (含分离子一族的筛子 `NoPt`). `blind-pair`: 没有种类的 `S⊥`, 只有一个精确种类的 `step S⊥`, 与今天候选闭项用的 `SL` + 全有损, 三者都满足. 新的一般定理 `pt-wdec` ("精确 + 留别份" + 标记 ⇒ 下标弱判定), 实例 `pt-SL-sep` (`SL` 的一切新种类精确且留别份 ⇒ 分离子).
> 2. **级集合定死了, 定义没有定死** ([NegTreeLangFlat](NegTreeLangFlat.lagda.md)). 平的候选 `Fl` (`LH` 上 `FlL`) 满足 `LvCrit` + `LvUpper` (`LvCritL` + `LvUpperL`), 由构造一路的定理它的级集合与 `Lev` (`Lv`) 相等 (`same-levels→/←`, `same-levelsL→/←`), 种类逐个对应 (`km`); 但它的一切合法 Ω-结点的分支是常函数 (`fl-const`, `flL-const`), 而 `Lev`, `Lv` 有合法的非常值分支 (`contrast`, `contrastL`).
> 3. **`Raise` 的盲区与边界** ([NegTreeLangRaise](NegTreeLangRaise.lagda.md)). 盲: `Raise` 对定义域 `Ev` 向下封闭 (`shrink`, `empty-raise`); `Lev` 的裸坐标积世界只把 `Ev` 改成 "同一成员" 就有实例, 且一起升 (`diag-raise`, `diag-moves`, `bare-vs-diag`); `Raise` 没有世界变大的律, 构造一路的实例框架上任一合法升界都把读数从 $1$ 改成 $0$ (`any-lowers`). 边界: 单一读数类型的框架装不下相邻两级 (`raise-iso`, `raise-adj`, `no-frame-SL01`), 带标签的读数也不行 (`raise-tag`).
>
> **对纲领与目标 (判断).** "让树自足" 要树侧判据能写出下一步定义. 今天的判据有两类: 否定性的 (向下封闭: 做得更少永远不违反) 与构造一路新加的正面的 (`feed`, `inherit`, `cof`: 向上封闭). 正面的一类确实把**级集合**推出来了 (构造一路的定理, 本篇复核其前提可满足且结论成立), 这是进展. 但判据不说世界, 界与第一位置, 所以被一个 Ω-极限全部退化的候选满足; `Raise` 不说定义域至少多大, 也不说世界变大, 所以被 "一起升" 与 "降值" 满足; 而且单一读数的 `Raise` 装不下跨级成员, C6 (各级新种类各自升界) 不在它能表达的范围里. 下一步需要的正面判据 (判断): 第一位置与坐标高度的 `⊲` 一致; 定义域含哪些异键对; 升界保世界的序; 读数随成员变的框架. 每一条写进判据前要算翻译账 (前一条读自 `HtTowerTy.step`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTreeLang where

open import OCF.Align.NegTreeLangPre public
  using (crit₄; pt-wdec; pt-SL-sep; pt-SL→WLPO; ptB; null-crit; blind⊥; blind1; blindSL; blind-pair; low⊥)
open import OCF.Align.NegTreeLangFlat public
  using (RFl; CFl; UFl; same-levels→; same-levels←; fl-const; contrast; RFlL; CFlL; UFlL; same-levelsL→; same-levelsL←; flL-const; contrastL)
open import OCF.Align.NegTreeLangRaise public
  using (shrink; empty-raise; diag-raise; diag-moves; bare-vs-diag; raise-iso; raise-adj; no-frame-SL01; raise-tag; any-lowers)
```

## 定理表 (按档)

| 名字 | 陈述 (简) | 文件 | 档 |
|---|---|---|---|
| `crit₄` | 四条否定作为 `T` 上的谓词对一切 `T` 成立 | Pre | 定理 |
| `pt-wdec` | `PtFam` (精确 `RsK` + 顶上的 `keep`) + `Mk` ⇒ `WDec J` | Pre | 定理 |
| `pt-SL-sep` | `PtFam tpL LH νL` ⇒ 分离子 `SepC codeL` | Pre | 定理 |
| `pt-SL→WLPO` | 同上 ⇒ WLPO | Pre | 条件 `FEL` |
| `ptB` | 可判定子族 (`lz`, `ls lz`) 上 `PtFam` 成立 | Pre | 前提实例 |
| `null-crit`, `blind⊥`, `blind1`, `blindSL`, `blind-pair` | 三个候选都满足全部五条 | Pre | 定理 (盲) |
| `CFl`, `UFl`, `CFlL`, `UFlL` | 平的候选满足 `LvCrit`/`LvUpper` (`LvCritL`/`LvUpperL`) | Flat | 前提实例 |
| `same-levels→/←`, `same-levelsL→/←` | 平的候选的级集合与 `Lev`/`Lv` 相等 (用构造一路的 `exact`) | Flat | 定理 (盲) |
| `fl-const`, `flL-const` | 平的候选里合法 Ω-结点的分支是常函数 | Flat | 定理 |
| `contrast`, `contrastL` | `Lev`/`Lv` 有合法非常值分支, 平的没有 | Flat | 定理 |
| `shrink`, `empty-raise` | `Raise` 对 `Ev` 向下封闭 | Raise | 定理 (盲) |
| `diag-raise`, `diag-moves`, `bare-vs-diag` | `Lev` 裸坐标积世界: `Ev` 恒真推出分离子, `Ev` 取对角有实例且一起升 | Raise | 定理 (盲) |
| `any-lowers` | 构造一路实例框架上任一合法升界降值 | Raise | 定理 (盲) |
| `raise-iso`, `raise-adj`, `no-frame-SL01`, `raise-tag` | 单一读数框架装不下相邻两级 / 固定标签 | Raise | 定理 (边界) |
