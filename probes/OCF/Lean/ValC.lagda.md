# ValC: CRw 的值 (第 4 层): 关系、路线引理、单调、闭项的第一条值定理 (入口)

> 不含记号. 构造一路 ValC (配对否定一路 NegValC), 2026-11-06. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不开 K, 不用函数外延 (只作前提). 不改任何已有文件 (第 4 层: 只新增关系与定理, 不改 CRw 的树、折叠、合法性). 导入闭包: stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValC*`, 第 0 层的标准前序 `OCF.Align.TLRuleSpec` 与它的 `CumReadCF` (只作锚, 已有的值验收用的就是它).
>
> **任务** (作者本轮选定, 原话 "值: Fab5 的路线引理搬到 CRw"; 说明 "第 4 层 (构造+否定): 证 '在上' 处两种折法可比, 把 Fab5 的单调定理推到 CRw 的 Φ (累加的 sup 层), 目标是 TU2 一类闭项的第一条值定理").

| 文件 | 内容 |
|---|---|
| [ValCIf](ValCIf.lagda.md) | 接口 (定稿 01:41): `ValC⊥` (§2); 追加 `ValC⊥ᵖ` (§3, 路线引理只对真第一位置) |
| [ValCRel](ValCRel.lagda.md) | 可数层号上的值关系 `LeAt`, 值合法 `MoAt`; 种类的层 `lvK`; 没有真回路 `nl` |
| [ValCBase](ValCBase.lagda.md) | 累加与链的单调, 地板值合法 `Mo-top`, `one≤`, 留下的结点, 层号的结构可达性 `AP` |
| [ValCMono](ValCMono.lagda.md) | **`monoΦ`, `route`, `MoΦ`** (条件: `Cd` 上的 UIP) |
| [ValCUip](ValCUip.lagda.md) | `fe→uipC`: 函数外延推出 `Cd` 上的 UIP (条件: Funext) |
| [ValCTm](ValCTm.lagda.md) | 接口实例 `valC⊥ᵖ`, `infl`, 闭项 `TC`, **`grow`**, `growᴬ` |
| 本篇 | 前提实例; 汇总 |

## 对纲领与目标

- **纲领 1, 2, 4.** 值关系 `LeAt t` 就是 "两棵第 $t$ 层的树按构造子比较值", 第 0 层推出此前值验收用的标准前序 (`sound₀`, 定理). 不读记号. 一切定义无公理, 由检查器保证停机.
- **目标 "树侧的合法性标准".** 这一轮逼出两条关于值关系**本身**的树侧要求, 都不来自记号:
  1. **ℕ-极限在左边只能对严格增子列** (`l≤l σ`). CRw 的折叠在 ℕ-极限处取部分和, $\lim(0,0,\dots)$ 与 $0$ 值相同, 折出 $\omega$ 与 $1$ (否定一路 `NegValCInst.acc-not-mono≤`, 定理). 部分和对严格增子列单调 (`Σ-sub`), 所以关系只留这一种. Fab5 的 `l≤` 不能搬 (`NegValCBound.fab5-port-excluded`, 定理).
  2. **Ω-结点按种类的层比较, 不按路径** (`Ω≤Ω` 只要求 `lvK` 相等, 坐标经 `subst` 搬运). 两种折法留下的种类是 `along q` 与 `along q₂`, $q, q_2$ 是 `cmpB` 沿不同路线算出的第一位置路径 (判断: 一般字面不同, 因为合法证明 `LgB` 带数据, 不同路线下取到的 `LgB` 证明不同).
- **`Cd` 上的 UIP (条件).** 两个独立算出的 "同层" 决定 ($t$ 与种类的层 $k$ 由合一等同) 要在 `--without-K` 下同时化简, 第二次要消去自反方程 $k=k$; 这里以 `Cd` 上的 UIP 为前提 (`selfLoop`: $r : k\lhd k$ 字面是 `hself`). 只在这一处用到. 前提可满足: 函数外延推出它 (`fe→uipC`). **所以本轮的单调、路线引理与闭项定理都是条件定理 (条件: `Cd` 上的 UIP, 可由 Funext 推出).** 不用前提的出路 (判断, 未做): 证 `cmpB` 的路径相干性, 让两种折法用同一个比较结果.
- **"在上" 处两种折法.** 路线引理 `route` 证的方向是 $\Phi_{m\to t,b}\,x\le\Phi_{j\to t,b'}(\Phi_{m\to j,\mathrm{top}\,j}\,y)$ (直接折不高于经中间层折), 只对 $t$ 是 $j$ 的**真**第一位置. 定稿接口 §2 对一切 $t\lhd j$ (含 $t=j$) 陈述, 被否定一路 `NegValCRoute.route-hself` (定理) 否定; 本路追加 §3 记录 `ValC⊥ᵖ` 并给出实例. 反方向 ($\ge$) 没有证; 判断它对后继不成立 (两步折叠在第 $j$ 层先作部分积, 再折, 比直接的 $\cdot\omega$ 大).

## 主要定理 (陈述见各文件)

- **`ValCMono.monoΦ`** (条件: UIP): 对一切 `I : CRwIf`, 可数层号 $m$, 目标 $t\lhd m$ (两边的目标证据、合法证明、可达性证明可不同): $x\le y$ (第 $m$ 层, 都值合法), 界 $\mathrm{top}\,t\le b\le b'$ (都值合法) ⟹ $\Phi_{m\to t,b}\,x\le\Phi_{m\to t,b'}\,y$. 这是 Fab5 `Ψ-mono≤` 在 CRw 的累加 sup 层上的对应.
- **`ValCMono.route`** (条件: UIP): 另有层号 $j\lhd m$ ($j$ 的可达性由 `Pp j m` 取出), $t$ 是 $j$ 的真第一位置 (`Pp t j`), 同样的前提 ⟹ $\Phi_{m\to t,b}\,x\le\Phi_{j\to t,b'}(\Phi_{m\to j,\mathrm{top}\,j}\,y)$.
- **`ValCMono.MoΦ`** (条件: UIP): 折叠保值合法.
- **`ValCTm.valC⊥ᵖ`** (条件: UIP): 接口 §3 的实例.
- **`ValCTm.grow`** (条件: UIP): 闭项 `TC t` (第 $t+1$ 层地板 $\Omega$ 以界 0 折到第 0 层) 满足 `hs (TC t) ≤ TC (t+1)`, 对一切合法可数树 $t$; `growᴬ` 落到 `TLRuleSpec._≤_`. **严格只是 "多一个后继" 档**: 定理只给出 $+1$, 没有给两站之间的定量差 (读法上差很大, 是判断).
- 无条件: `sound₀`, `infl` (嵌入再折回不降值), `one≤`, `Mo-top`, `nl`/`nos` (没有真回路), `fe→uipC` (条件 Funext).

## 前提实例

`uipC` 由函数外延给出 (条件 Funext). `LgB t`: 例如有限树 (`LgB` 是 `⊤`) 与一切 `CRw` 的合法闭项. `I`: CRw 的实例 `I₁`. 下面把条件写到 Funext 上, 并在 $t=0,1,2$ 上写出实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ValC where

open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.ValCUip using (Funext; fe→uipC)
import OCF.Lean.ValCTm as Tm
import OCF.Lean.ValCRel as Rl
import OCF.Lean.ValCIf as If
import OCF.Align.TLRuleSpec as TL
open import OCF.Align.CumReadCF using (asuc)

module _ (fe : Funext) where
  open Tm I₁ (fe→uipC fe)

  -- 接口 §3 的实例 (条件 Funext)
  inst : If.ValC⊥ᵖ I₁
  inst = valC⊥ᵖ

  -- 闭项的第一条值定理, 前三站 (条件 Funext)
  grow₀ : asuc (If.toA I₁ (TC hz tt)) TL.≤ If.toA I₁ (TC (hs hz) tt)
  grow₀ = growᴬ hz tt

  grow₁ : asuc (If.toA I₁ (TC (hs hz) tt)) TL.≤ If.toA I₁ (TC (hs (hs hz)) tt)
  grow₁ = growᴬ (hs hz) tt

  -- 一切合法的可数层号 (例如 CRw 的闭项本身作层号)
  growAll : ∀ t (lt′ : LgB t) → asuc (If.toA I₁ (TC t lt′)) TL.≤ If.toA I₁ (TC (hs t) lt′)
  growAll = growᴬ
```

## 文件, 编译, 检查

编译 (从仓库根, 每个文件单独, 退出码不经管道): `agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes probes/OCF/Lean/<文件> +RTS -M6G -RTS`. 2026-11-06 结果见汇报. 禁用构造: 全部 `ValC*` 无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 无 `--with-K`.

## 翻译账

- **新定义来自哪里.** 没有新的树、折叠或合法性 (第 4 层). 新的是值关系 `LeAt` 与值合法 `MoAt` (Fab5 的形状), 改了两处, 都由树侧逼出: `l≤l σ` (CRw 折叠的部分和, 否定一路的编译定理), Ω-结点按层比较 (折叠留下的种类依赖 `cmpB` 的路径, 判断). 记号没有参与.
- **脚手架.** `DV` (决定的视图), `AP` (层号的结构可达性: 折叠的 `Acc` 让停机检查看不清, 换成对真第一位置的结构可达性), `selfLoop` 与 `uipC` (两次 "同层" 决定). 这些是值的证明需要的, 不是翻译带来的.
- **攀爬侧.** 读法不升. **摆脱侧.** 第一次在 CRw 的累加 sup 层上有值定理; 它说明值关系必须自己处理部分和与路径, 这两条要求写成了关系的形状.

## 接手清单

1. **跨底 (`cx`) 与 `TX`, `TU`, `TU2`.** 本轮的关系与单调只覆盖底 `b⊥` 的塔 (可数层号). `TU m` 要 `XS` 底的塔 (`inU`) 与跨底折叠 (世界移动、路径 `PH`). 要做: (a) 把 `Low`/`lvK` 推广到底 `bX` (底种类 `bas` 按 `XS` 的种类比较); (b) 跨底折叠的单调: 回灌 $B\boxplus\mathrm{leg}\,c$ 与世界 `nxt₀` 的单调 (否定一路 `NegValCInst.sh-not-mono≤`: `sh₀ B lim(1,1,…) ≰ sh₀ B 1`, 在 `l≤l` 关系下这一对不再相关, 判断), Ω₁ 本身 (`poΩ`) 与各分量里 Ω₁ 的拷贝 (`poF`) 不能只按层比较 (否定一路的提醒, 判断: 要按 (层, 策略) 比较, 或只允许 "拷贝 ≤ 本身"). 做成后 "TX ≤ TU 1" 的证明草图: `topL + 1 ≤ inU 1` (链第 0 点 $\ge$ `topL` 由同底 `infl`) 再用跨底单调.
2. **去掉 UIP 前提.** 证 `cmpB` 的路径相干性 (否定一路判断两种折法的路径命题相等), 让两种折法共用一个比较结果; 或证明只在 "同层" 时需要的那一条: 两个 `cmpB` 结果同为 `inj₁ (hsuc r)` 时 $r$ 相同.
3. **定量的严格.** `grow` 只有 $+1$. 两站之间的定量差 (例如 `TC (t+1)` 不低于 `TC t` 的 $\omega$ 倍) 要把回灌链的第 $n$ 点与 `TC t` 的 $n$ 倍比较; `NegLeanLvVal.strict-cell` 提醒: 每格多一个后继推不出闭项严格大, 要对实例算.
4. **层号单调** (不同层号 $t\lhd t'$ 的 `TC t ≤ TC t'`): 要比较从不同层出发的折叠 (嵌入引理: 嵌入的树在两层上的决定相同). 未做.

## 结论 (按档)

- **[条件定理, 条件 `Cd` 上的 UIP; 再由 Funext 推出]** `monoΦ`, `route` (真第一位置), `MoΦ`, `valC⊥ᵖ`, `grow`, `growᴬ`; 本篇 `inst`, `grow₀`, `grow₁`, `growAll` (条件 Funext).
- **[定理, 无条件]** `sound₀`, `infl`, `one≤`, `Mo-top`, `nl`, `nos`, `nos′`, `noPP`, `apWf`, 累加与链的引理, 接口 `ValCIf` (两个记录).
- **[判断]** 读法 `TC t` 是 ψ₀(Ω_{t+1}) 一类 (同 TySup 的塔); 两种折法留下的种类字面不同; 反方向的路线引理对后继不成立; 接手清单的方向.
