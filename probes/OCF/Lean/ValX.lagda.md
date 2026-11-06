# ValX: CRw 的跨底折叠的值 (第 4 层): 关系、单调、卡点、`TX + 1 ≤ TU 1` 的归约 (入口)

> 不含记号. 构造一路 ValX (配对否定一路 NegValX), 2026-11-06. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不开 K, 函数外延只作前提. 不改任何已有文件 (第 4 层: 只新增关系与定理, 不改 CRw 的树、折叠、合法性). 导入闭包: stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValC*`, `OCF.Lean.ValX*`, 第 0 层的标准前序 `OCF.Align.TLRuleSpec` 与 `CumReadCF` (只作锚).
>
> **任务** (作者本轮选定, 原话 "值: 跨底单调与 TU2/Tω 值定理"; 说明 "第 4 层 (构造+否定): 把 ValC 推到跨底折叠 (回灌不保值关系要处理), 拿 TU2 或 RecB 的 Tω 的第一条值定理; 顺带试去掉 UIP 条件").

| 文件 | 内容 |
|---|---|
| [ValXIf](ValXIf.lagda.md) | 接口 (定稿 08:05): `ValX` (§2), 目标陈述 `Goal₁` (§4); 追加 `ValX⁻` (§5, 锚换成 $\Omega_1$ 结点) |
| [ValXRel](ValXRel.lagda.md) | $\Omega_1$ 层的值关系 `_≤X_` (同分量同层的 `Ω≤Ω`), 值合法 `MoX`; 回灌律的记录 `ShLaw` |
| [ValXObs](ValXObs.lagda.md) | **卡点** `floor-block`, `¬MoX-topL` |
| [ValXBase](ValXBase.lagda.md) | 记法, 回灌与新世界, 坐标数据 `KD`/`KC`, `oneX` (不用 UIP) |
| [ValXMono](ValXMono.lagda.md) | **`monoX`, `routeX`, `brX`, `MoXΦ`** (条件: UIP 与 `ShLaw`) |
| [ValXTm](ValXTm.lagda.md) | `I₁` 的回灌律 `shLaw₁`; `MoX-Ω₁`; **`TU2-above`**; 接口实例 `Inst.valX⁻` (条件 UIP) |
| [ValXGoal](ValXGoal.lagda.md) | **`goal-if`**: `Hyp` ⟹ `TX + 1 ≤ TU 1` (不用 UIP) |
| [ValXP1](ValXP1.lagda.md) | `MoX-gt`, `U-infl`; **`P1`**, **`goal-P2`** (条件 UIP) |
| 本篇 | 条件写到 Funext 上的实例; 汇总 |

## 对纲领与目标

- **纲领 1, 2, 4.** 关系 `_≤X_` 比较 $\Omega_1$ 层的两棵布劳威尔式高度, 输出比较落在 ValC 的 `LeAt` 上, 第 0 层推出此前值验收用的标准前序 (`sound₀`). 不读记号. 一切定义无公理, 由检查器保证停机.
- **纲领 3 (壁垒).** 跨底折叠里一切比较的公共上界是世界的界 $B$; 接口的律两边同一世界. 证明内部两边世界不同 (进入 $\Omega_1$ 分支后换成 $\mathrm{nxt}_0(\mathrm{sh}_0\,B_i\,c_i)$), 只按第 0 层的值比较, 不作判定.
- **目标 "树侧的合法性标准".** 这一轮逼出两条关于值关系的树侧要求, 都不来自记号:
  1. **$\Omega_1$ 层的 `Ω≤Ω` 只在同一分量内比较** (同层还不够, ValC 只要求同层). $\Omega_1$ 本身与别的分量里的拷贝同层, 但跨底折叠对前者回灌并换世界, 对后者不动 (否定一路的 `self≰copy`, 本路未复核). 同一分量内又必须允许不同种类 (`MoX-gt` 要它).
  2. **地板不值合法** (`floor-block`, 定理). 地板 `topL` 的分支 `gt C` 的种类落在由坐标 $C$ 的**结构**决定的分量里; 两个值相关而结构不同的坐标 ($1+\omega$ 的两种基本列) 给出无公共分量的两组种类. 对一切 "层反射" 的关系 (只能把一个 $\Omega$-结点比到同层的结点), 地板的分支都不单调. 这说明: 跨底的值比较若要覆盖闭项, 必须**跨层比较** $\Omega$-结点 (把第 $c$ 层的高度搬到值不小的第 $c'$ 层), 这是 ValC 接手清单第 4 条 (层号单调) 的跨结构版本.
- **对闭项.** 跨底单调 (`monoX`) 对值合法的输入成立, 地板不在其中; 所以闭项的值比较停在根上. 本路把 `TX + 1 ≤ TU 1` 归约成**一条第 0 层的陈述** `P2`: `TU 1` 的回灌链第 0 点的分支族 $k_R$ 对坐标值单调 (`goal-P2`, 条件 UIP). 这是一个只关于可数树输出的陈述, 不再涉及 $\Omega_1$ 层的关系.

## 主要定理 (陈述见各文件)

- **`ValXObs.floor-block`** (定理, 对一切 `I`): 对一切满足 `LvRefl` 的关系 $R$ ($R(\Omega_\kappa\,g, y)$ ⟹ $y$ 含层 `lvX κ` 的结点), $\neg R(\mathrm{gt}(1+\omega_1), \mathrm{gt}(1+\omega_2))$, 而 $1+\omega_1\le1+\omega_2$ (`le₁₂`, 第 0 层的值关系; $\omega_1=\lim n$, $\omega_2=\lim(n+1)$). 推论 **`¬MoX-topL`**.
- **`ValXMono.monoX`** (条件: `Cd` 上的 UIP, `ShLaw I`): 对一切 `I`, 世界 $B_1\le B_2$, 目标 $t$ (两边对 $B_i$ 的证据), 界 $\mathrm{top}\,t\le b\le b'$ (值合法), 输入 $x\le_X y$ (都 `MoX`, 各带世界 $B_i$ 里的路径) ⟹ 跨底折叠 $\Phi^\times_{B_1,b}\,x\le\Phi^\times_{B_2,b'}\,y$. 同时 `routeX` (跨底路线引理, 目标是中间层的真第一位置), `brX`, `MoXΦ`.
- **`ValXTm.shLaw₁`** (定理): `I₁` 满足 `ShLaw` (`leg` 对第 0 层的值关系单调: 在严格增子列的关系下部分和保序).
- **`ValXTm.TU2-above`** (定理, 不用 UIP): 对一切 $n$, $\mathrm{TU}(y_n+1)+1\le\mathrm{TU2}$, 落到 `TLRuleSpec._≤_` (`TU2-aboveᴬ`). **结构的**: 只用对角的定义与 `oneX` (跨底折叠输出 $\ge1$), 不用跨底单调. 严格只是 "多一个后继" 档.
- **`ValXGoal.goal-if`** (定理, 不用 UIP): `Hyp` ⟹ $\mathrm{TX}+1\le\mathrm{TU}\,1$ (`goal₁-if`: 接口 §4 的 `Goal₁`). `Hyp`: 对 $b_1\le b_2$, $k_L\,b_1\le k_R\,b_2$.
- **`ValXP1.P1`** (条件 UIP): 对一切 $b$, $k_L\,b\le k_R\,b$. **`ValXP1.goal-P2`** (条件 UIP): `P2` ⟹ $\mathrm{TX}+1\le\mathrm{TU}\,1$.
- **`ValXTm.Inst.valX⁻`** (条件 UIP): 接口 §5 `ValX⁻` 对 `I₁` 的实例.

## 前提实例

- `uipC`: 函数外延推出 (`ValCUip.fe→uipC`, 条件 Funext). 下面把条件写到 Funext 上.
- `ShLaw I₁`: 定理 `shLaw₁`.
- `MoX` 的输入: `gt C` (一切 $C$, `MoX-gt`), `U b (gt C)` (`MoX-U`), $\Omega_1$ 结点 `gt 1` (`MoX-Ω₁`). 路径: `CRw` 的 `PH-topL`, `PH-inU`.
- `P2`, `Hyp`: 未证, 未否定 (判断: 不知道真假).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ValX where

open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; TX; TU1; TU2; TU; yU; lg-yU)
open import OCF.Lean.ValCUip using (Funext; fe→uipC)
open import OCF.Lean.ValCIf I₁ using (toA)
open import OCF.Lean.ValXIf I₁ using (ValX⁻)
import OCF.Lean.ValXObs as Obs
open import OCF.Lean.ValXRel I₁ using (MoX)
open import OCF.Lean.ValCRel I₁ using (LeAt)
open import OCF.Lean.CRwFold I₁ using (topL)
import OCF.Lean.ValXTm as Tm
import OCF.Lean.ValXGoal as Gl
import OCF.Lean.ValXP1 as P1m
open import OCF.Align.CumReadCF using (asuc)
import OCF.Align.TLRuleSpec as TL
open import Relation.Nullary using (¬_)

-- 卡点 (定理, 不用条件)
noTopL : ¬ MoX topL
noTopL = Obs.¬MoX-topL I₁

-- TU2 高于每个对角点 (定理, 不用条件)
tu2 : ∀ n → asuc (toA (TU (hs (yU n)) (lg-yU n))) TL.≤ toA TU2
tu2 = Tm.TU2-aboveᴬ

-- 归约 (定理, 不用条件)
goal-if : Gl.Hyp → asuc (toA TX) TL.≤ toA TU1
goal-if = Gl.goal-ifᴬ

module _ (fe : Funext) where
  -- 接口实例 (条件 Funext)
  inst : ValX⁻
  inst = Tm.Inst.valX⁻ (fe→uipC fe)

  -- 同坐标比较与只差 P2 (条件 Funext)
  p1 : ∀ b → LeAt hz (Gl.kL b) (Gl.kR b)
  p1 = P1m.P1 (fe→uipC fe)

  goal-P2 : P1m.P2 (fe→uipC fe) → asuc (toA TX) TL.≤ toA TU1
  goal-P2 = P1m.goal-P2 (fe→uipC fe)
```

## 文件, 编译, 检查

编译 (从仓库根, 每个文件单独, 退出码不经管道): `agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes probes/OCF/Lean/<文件> +RTS -M6G -RTS`; 冷编脚本 `probes/Survey/scripts/valx/verify.sh`. 2026-11-06 结果见汇报. 禁用构造: 全部 `ValX*` 无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 无 `--with-K`. 工程: `ValXGoal` 的 `Fn` 放在 `opaque` 里 (透明时 6G 内堆耗尽, 251).

## 翻译账

- **新定义来自哪里.** 没有新的树、折叠或合法性 (第 4 层). 新的是 $\Omega_1$ 层的值关系 `_≤X_` 与 `MoX` (ValC 的形状), 改了一处: `Ω≤Ω` 只在同一分量内 (由跨底折叠对 $\Omega_1$ 本身与拷贝的不同处理逼出). 记号没有参与.
- **脚手架.** `ShLaw` (回灌与新世界的值律, 实例的性质), 坐标数据 `KD`/`KC` 与 `pickTr` (同分量不同种类的比较), `kcC` 里分量 0 的 UIP. 这些是值的证明需要的, 不是翻译带来的.
- **攀爬侧.** 读法不升. **摆脱侧.** 第一次在跨底折叠上有值定理; 它逼出两条关于值关系本身的要求 (同分量; 地板要跨层比较), 写成了关系的形状与一条否定定理.

## 接手清单

1. **`P2` (层号的值搬运).** `TX + 1 ≤ TU 1` 只差 `P2`: $k_R\,b$ = 在世界 $\mathrm{nxt}_0(W_0\boxplus\mathrm{leg}\,b)$ 里以界 $b$ 折 $U(\mathrm{gt}(W_0\boxplus\mathrm{leg}\,b))$, 要对 $b$ 值单调. 经 $\Omega_1$ 层的值合法证它被 `floor-block` 挡住. 出路 (判断): (a) 在 $\Omega_1$ 层的关系里加跨层的 `Ω≤Ω` (第 $c$ 层的高度沿 $c\le c'$ 的推导搬到第 $c'$ 层; `LeAt hz c c′` 的推导本身给出一个嵌入, 见 `ValXObs` 的读法), 那时折叠的决定可能不一致 (同层对在上, 要跨层的路线引理); (b) 直接在第 0 层对 `gt` 的累加结构归纳, 比较 $\Phi(\Omega_{c+1})$ 与 $\Phi(\Omega_{c'+1})$ (ValC 接手清单第 4 条: 同底折叠对层号单调, 现在要对值相关而结构不同的层号).
2. **`TU m` 对 $m$ 单调, `TU2` 高于一切 `TU m`, RecB 的 `TD n`.** 都要先过第 1 条 (根都是 $\Omega_1$ 结点, 回灌链的点要对坐标单调). `TU2-above` 只给对角点.
3. **去掉 UIP.** 没有做到. 用到 UIP 的地方: ValC 的 `sameR` (两次 "同层" 决定), `monoΦ`, `route`; 本路 `kcC` 的分量 0 ($e : 0\equiv0$ 换成 `refl`). 否定一路报告 `NegValXUip`: `selfLoop` 与 UIP 等价 (本路未复核); 若成立, 经 `selfLoop` 去 UIP 不会更弱. 剩下的出路 (判断): 让两边共用一次 `cmpB` 的结果 (证 `cmpB` 的路径相干性), 或把 "同层" 的决定改成带等式而不合一的视图.
4. **定量的严格.** `TU2-above` 与 `goal-P2` 都只有 $+1$.

## 结论 (按档)

- **[定理, 无条件]** `floor-block`, `¬MoX-topL`, `refl≤X`; `shLaw₁`, `leg-mono`, `leg-infl`; `oneX`, `one≤TU`, **`TU2-above`**, `TU2-aboveᴬ`; `MoX-Ω₁`, **`MoX-gt`**, `U-infl`, `U-mono`, `MoX-U`; `Ω₁-same`, **`goal-if`**, `goal₁-if`; 接口 `ValXIf` (三个记录与 `Goal₁`); 本篇 `noTopL`, `tu2`, `goal-if`.
- **[条件定理, 条件 `Cd` 上的 UIP (由 Funext 推出) 与 `ShLaw I` (对 `I₁` 是定理)]** **`monoX`**, `routeX`, `brX`, `MoXΦ` (对一切 `I`); `kcC`; `Inst.valX⁻`; **`P1`**, **`goal-P2`**; 本篇 `inst`, `p1`, `goal-P2` (条件 Funext).
- **[判断]** `P2` 的真假; 接手清单的出路; 读法 (`TX` ψ₀(Ω_Ω), `TU 1` ψ₀(Ω_{Ω+1}), `TU2` ψ₀(Ω_{Ω·2}), 同 CRw, 无定理).
