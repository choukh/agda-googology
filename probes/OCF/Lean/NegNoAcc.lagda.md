# 去累加, 否定一路 (入口)

> 不含记号. 与构造一路 NoAcc 配对, 共用接口 [NoAccIf](NoAccIf.lagda.md) (定稿 2026-11-06 01:40). 作者本轮 (原话) "去累加: 证书读输入合法". 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延. 只新建 `NegNoAcc*` 文件, 不改别的文件.
>
> **判决 (只对写明的形状).**
>
> 1. **去累加逼出读输入合法** ([NegNoAccPt](NegNoAccPt.lagda.md), 定理). `pt-no-total`: ℕ-极限子句逐点的折叠**没有**对一切输入的证书 (只要证书的 ℕ-极限要求步进: `LgB`, CRw 的 `Sh`). 由 `no-up` ($\lim(x,x,\dots)\not\lhd x$). 这比 `NegCRwAcc.pt-shape→chain` 强 (不要像不可比). 作者选的组合 (逐点 + 证书读输入合法) 在逐点子句下是唯一可能的.
> 2. **第三种 ℕ-极限写法** (同篇). 穿界写法 `Fᵗ` (界穿过序列, 无 `⊞`) 不逐点 (`thr-not-pt`), 有对一切输入的证书 (`Fᵗ-lg`), 但在合法输入 $\lim(0,1,1,\dots)$ 上不保第一位置 (`thr-not-mono`, 由一般化三值引理 `ThrNM`; 部分和是特例). "只有两种写法" 被挑战: 有第三种, 但它在这个输入上与部分和逐项同值 (`dS-hz`). "只有三种" 仍是判断.
> 3. **`Mo` 推不出 `LgB`** ([NegNoAccMo](NegNoAccMo.lagda.md), 定理). `Mo-triv`: 第 0 层 `Mo` 恒真; `mo⇏lgB`: 值合法且值严格递增的 ℕ-极限可以不 `LgB`. 若证书用 `Mo`, 闭项的 `LgB` 证书要另给.
> 4. **接口的盲与边界** ([NegNoAccIf](NegNoAccIf.lagda.md), 定理). 实例 `I⊞` 满足全部律 (前提可满足); `constShN`, `stayN` 也满足 (回灌可以与坐标无关, 世界可以不动); `feed-incomp`, `no-cmp`: 回灌之后的世界里两个回灌进来的层可以不可比, 比较它们要读坐标合法; `split⊞`, `cmp-feed`: 回灌层与旧界之下的目标可比, 不读合法; **`pt-blind`**: `PtFold` 的契约可被一个把 $\Omega_1$ 折成 $1$ 的折叠满足, 契约不说强度, 且 `F-mono` 只在相容世界里成立是实质限制.
> 5. **对构造一路折叠的检查** ([NegNoAccX](NegNoAccX.lagda.md), 定理). 构造一路的 `NoAccFold.Φᴾ` (01:55 版) 的 ℕ-极限子句确实逐点 (`Φᴾ-pt`, refl, 它的定理); 但跨底留下 $\Omega_1$ 结点时, 合法带路径的输入给出不 `LgB` 的输出 (**`kept-world-Φᴾ`**; 核心 `KeptW.kept-world`): 相邻坐标的分支在不同世界里折, 里层回灌 $W\boxplus d$ 读世界, 而 `⊞` 对左边不单调 (`⊞-not-monoˡ`). 同一输入在 CRw 的累加折叠下也不 `LgB` (`kept-world-Φ`), 所以与 ℕ-极限子句无关. `Φᴾ` 的跨底回灌仍是 `I₁` 的 `leg` (部分和, `leg-not-pt`); `no-CRwIf-⊞`: `CRwIf` 加 "进入保留坐标合法" 时回灌不能是 $1\boxplus c$. 构造一路的同底卡点 (它的 `NoAccStuck`) 由它自己证, 本路不重复. 构造一路尚无闭项与证书, 所以 "证书是否标准 `LgB`", "读法是否与 `TU2` 相同" 两项**未检查** (没有对象).
>
> **只否定什么 (汇总).** 只否定: 逐点子句 + 对一切输入的 (步进型) 证书; 穿界写法保第一位置; `Mo ⇒ LgB`; 接口的律迫使回灌依赖坐标或世界变大; 不读合法也能比较两个回灌层; `PtFold` 蕴含强度. **不否定**: 构造一路的路线 (逐点 + 读输入合法) 本身, 它的接口; 换一种世界移动 (分支在同一世界里折, 或回灌对世界单调) 的跨底折叠; 第 0 层闭项的证书 (中间层不合法是否传到第 0 层, 未证). 本路没有关闭任何路线.
>
> **对纲领与目标.** 纲领不受影响 (都是对合法项或具体反例的陈述, 无公理). 目标 "树侧的合法性标准": 1 说读输入合法是由树的要求 (ℕ-极限步进) 逼出的, 不是选择; 3 说值合法不能代替字面合法; 4 说读合法可能还要进折叠定义 (两个回灌层相比时). 翻译账: 本路没有新增来自记号的字段.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegNoAcc where

open import OCF.Lean.NegNoAccPt public using (no-up; module PtNoTotal; pt-no-LgB; pt-no-Sh; Fᵗ; Fᵗ-lg; thr-not-pt; module ThrNM; thr-not-mono)
open import OCF.Lean.NegNoAccMo public using (Mo-triv; mo⇏lgB)
open import OCF.Lean.NegNoAccIf public using (I⊞; constShN; stayN; feed-incomp; no-cmp; split⊞; cmp-feed; P₀; pt-blind)
open import OCF.Lean.NegNoAccX public using (⊞-not-monoˡ; module KeptW; kept-world-Φᴾ; kept-world-Φ; leg-not-pt; no-CRwIf-⊞)
```

## 结论 (按档)

- **[定理]** 见各篇 "结论". 主要: `no-up`, `PtNoTotal.pt-no-total`, `pt-no-LgB`, `pt-no-Sh`; `Fᵗ-lg`, `thr-not-pt`, `ThrNM.not-mono`, `thr-not-mono`; `Mo-triv`, `mo⇏lgB`; `I⊞`, `constShN`, `stayN`, `feed-incomp`, `no-cmp`, `split⊞`, `cmp-feed`, `pt-blind`; `⊞-not-monoˡ`, `KeptW.kept-world`, `kept-world-Φᴾ`, `kept-world-Φ`, `leg-not-pt`, `no-CRwIf-⊞`.
- **[判断]** ℕ-极限写法 "只有逐点, 部分和, 穿界"; 读输入合法要进折叠定义 (构造一路同意, 它的 `NoAccFold` 因此沿用 `CRwIf`); 跨底中间层的不合法是否传到第 0 层输出, 未证; 出路方向 (分支在同一世界里折, 或回灌对世界单调) 未写.
