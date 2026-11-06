# SameV: 同值不同结构的坐标, 跨层的值关系, `TX + 1 ≤ TU 1` (入口)

> 不含记号. 构造一路 SameV (配对否定一路 NegSameV), 2026-11-06. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不开 K, 函数外延只作前提. 第 4 层: 只新增关系与定理, 不改 CRw 的树、折叠、合法性; 不改任何已有文件. 导入闭包: stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValC*`, `OCF.Lean.ValX*`, `OCF.Lean.SameV*`, 第 0 层的标准前序 `OCF.Align.TLRuleSpec`, `CumReadCF` (只作锚).
>
> **任务** (作者本轮选定, 原话 "核心: 同值不同结构"; 说明 "构造+否定: 值与摆脱两侧共同的墙: 同值不同写法的树经折叠不保值序. 试跨层的 Ω≤Ω (对 c ≤ c′ 的推导给嵌入) 或直接在第 0 层证 P2; 要么给出不可能的定理").

| 文件 | 内容 |
|---|---|
| [SameVIf](SameVIf.lagda.md) | 接口 (定稿 21:03): `LvMor`, `res`, `CrossV`, 目标 `P2`, `P2L`, `Goal`, `TU-mono` |
| [SameVRel](SameVRel.lagda.md) | 配对 `Match`, 跨层关系 `LE`, `tr≼`, `⊞≼`, `Σ≼`, 链 `chX`, `keepX` (不用 UIP) |
| [SameVMono](SameVMono.lagda.md) | **`crossΦ`**: 同底折叠沿配对单调 (条件 UIP, 地板律) |
| [SameVX](SameVX.lagda.md) | 关系 `_≼X_`; **`crossX`**: 跨底折叠沿配对单调 (条件 UIP, `ShLaw`, 地板律) |
| [SameVLeg](SameVLeg.lagda.md) | 前缀 `Pf`; **`Pr`**: 由 `LeAt hz a b` 的任意推导给出的配对; `M.match` (不用 UIP) |
| [SameVGoal](SameVGoal.lagda.md) | 地板律 `tp`, **`gtP`**, `UX`, **`P2-thm`**, `P2L-thm`, **`goal`** (条件 UIP) |
| [SameVObs](SameVObs.lagda.md) | **`¬Mo-u₀`**: `TU 1` 的回灌链第 0 点不是 `MoX` (下一个卡点) |
| 本篇 | `LvMor` 到 `Match`; 实例; 条件写到 Funext 上; 汇总 |

## 对纲领与目标

- **对 "同值不同结构的墙".** 这堵墙在 CRw 上过去了 (条件 Funext): **对第 0 层值关系 `LeAt hz` 下的一切 $a\le b$, 折叠后 $k_R\,a\le k_R\,b$, $k_L\,a\le k_L\,b$** (`P2`, `P2L`), 两个方向都相关的坐标 ($1+\omega_1$, $1+\omega_2$) 折出互相 $\le$ 的值 (`ex₁₂`, `ex₂₁`). 前提是 `LeAt`, 不能放宽到标准前序 (否定一路 `NegSameVKr.P2ᵀᴸ-false`, 本路未复核).
- **闭项.** $\mathrm{TX}+1\le\mathrm{TU}\,1$ (`goal`), $\mathrm{TX}+2\le\mathrm{TU2}$ (`goal2`), 落到 `TLRuleSpec._≤_`, 条件 Funext. 这是 ψ₀(Ω_Ω) 这一档的闭项第一次被证明严格低于 ψ₀(Ω_{Ω+1}) 这一档 (读法是判断; 定理只说 "加 1 之后 ≤", 严格只是 "多一个后继" 档).
- **纲领 3 (壁垒).** 律里成对的两个层号没有合法的字面公共上界 (否定一路 `NegSameVSpine.no-common`, 本路未复核). 替代的证据是配对 `Match`: 每个层号内部的比较仍在各自的字面公共上界之下 (`cmpB`), 两边之间只传 "这一层配那一层", 没有裸的跨层比较, 也不判定 $a,b$ 是否同值. `k ≤ k′` 严格与否这里不用知道: 配对可以把值较低的层配给值较高的层, 只要单值且保序.
- **目标 "树侧的合法性标准".** 这一轮的发现都是树侧的:
  1. **决定不变只要配对的三条律** (`~fun`, `~s`, `~pp`): 单值, 保后继位置, 保真第一位置. 不要 "配对的层值相等", 也不要 $k\le k'$ 这一条.
  2. **累加在值的证明里起了正面作用.** 对 $a,b$ 本身, `l≤l σ h` 的各项 `h n` 互不协调, 给不出单值的配对. 但闭项用到的层号都是 $1\boxplus\mathrm{leg}\,b$, `leg` 把 ℕ-极限换成部分和, 第 $n{+}1$ 项的层放在前面所有项之后, 各项的层不相交 (`SameVLeg.gap`), 所以**任意**推导都给出单值的配对. 之前否定一路 (`acc-not-mono≤`, `col-acc`, `gl-TΩ1`) 记的都是累加的代价; 这是第一条记在收益一侧的定理. 这只说这一处, 不改变累加的毛刺 (记忆: 累加不等于自然).
  3. **关系不层反射, 左边不要值合法.** `floor-block` 对层反射的关系成立; `_≼X_` 的 `Ω≼Ω` 配对不同分量不同层的结点, 分支写成逻辑关系 (对一切相关的坐标), 不要坐标的搬运 (反方向的映射不存在).
- **没有做到.** `TU m` 对 $m$ 单调 (`SameVIf.TU-mono`) 与 "`TU2` 高于一切 `TU m`": 未证. 卡点见接手清单第 1 条. 接口的记录 `CrossV` 本路没有给实例 (证明走 `Match`, 见下).

## `LvMor` 给出 `Match`; 实例

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.SameV where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; TX; TU1; TU2; yU; lg-yU; TU)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁ hiding (ap)
open import OCF.Lean.ValCUip using (Funext; fe→uipC)
open import OCF.Lean.ValCIf I₁ using (toA)
open import OCF.Lean.ValXGoal using (kL; kR; Hyp; goal-if)
open import OCF.Lean.ValXTm using (TU2-above; sound₀)
open import OCF.Lean.ValXObs I₁ using (ω₁; ω₂; nat; le₁₂)
open import OCF.Align.CumReadCF using (asuc)
import OCF.Align.TLRuleSpec as TL
open import OCF.Lean.SameVIf using (LvMor; im; im-irr; im-s; im-pp)
open import OCF.Lean.SameVRel I₁ using (Match)
import OCF.Lean.SameVGoal as SG
import OCF.Lean.ValXP1 as P1m
import OCF.Lean.SameVObs as SO

-- 接口的搬运 (函数) 的图是配对
lv→match : ∀ {m m′} → LvMor m m′ → Match
lv→match {m} M = record
  { _~_ = λ a b → Σ (a ⊲ m) (λ q → im M q ≡ b)
  ; ~fun = λ { (q , refl) (q′ , refl) → im-irr M q q′ }
  ; ~s = λ { (q , refl) (r , refl) c → im-s M q r c }
  ; ~pp = λ { (q , refl) (r , refl) c → im-pp M q r c } }

-- 反方向的值关系 (同值不同结构的另一半)
le₂₁ : LeAt hz (hs ω₂) (hs ω₁)
le₂₁ = Rel.s≤s (Rel.l≤l suc (λ n → n<1+n (suc n)) (λ n → L.≤-refl hz (nat (suc n))))
```

## 条件写到 Funext 上

```agda
module _ (fe : Funext) where
  private
    uip = fe→uipC fe
    module G = SG uip

  -- ValXP1 的 P2 与它对 k_L 的版本
  P2 : P1m.P2 uip
  P2 = G.P2-thm

  P2L : ∀ b₁ b₂ → LeAt hz b₁ b₂ → LeAt hz (kL b₁) (kL b₂)
  P2L = G.P2L-thm

  -- floor-block 的那一对: 两个方向都相关
  ex₁₂ : LeAt hz (kR (hs ω₁)) (kR (hs ω₂))
  ex₁₂ = P2 _ _ le₁₂

  ex₂₁ : LeAt hz (kR (hs ω₂)) (kR (hs ω₁))
  ex₂₁ = P2 _ _ le₂₁

  ¬Mo-u₀ = SO.¬Mo-u₀ uip

  hyp : Hyp
  hyp b₁ b₂ le = L.≤-trans hz (P1m.P1 uip b₁) (P2 b₁ b₂ le)

  -- 闭项
  goal₀ : LeAt hz (hs TX) TU1
  goal₀ = goal-if hyp

  goal : asuc (toA TX) TL.≤ toA TU1
  goal = sound₀ goal₀

  goal2₀ : LeAt hz (hs (hs TX)) TU2
  goal2₀ = L.≤-trans hz (Rel.s≤s goal₀) (TU2-above 0)

  goal2 : asuc (asuc (toA TX)) TL.≤ toA TU2
  goal2 = sound₀ goal2₀
```

## 证明的结构

1. **配对** `Match` ([SameVRel](SameVRel.lagda.md)): 层号上的关系, 单值, 保后继位置, 保真第一位置. 由接口的 `LvMor` 得到 (`lv→match`), 证明本身只用这三条.
2. **跨层关系** `LE m m′`: 左第 $m$ 层, 右第 $m'$ 层. 同 ValC 的形状, `Ω≼Ω` 要层配对, 分支是逻辑关系. 只在右边要值合法.
3. **`crossΦ`, `crossX`** ([SameVMono](SameVMono.lagda.md), [SameVX](SameVX.lagda.md)): 目标成对 $(t,t')$, $t\sim t'$. 左边的决定决定右边的决定, 不一致的组合由没有真回路排除. "在上" 走到配对的层 $(k,k')$. `≼Ω` 走 "归纳假设 + 右边同层的 `monoΦ` 或 `brX`", 没有跨层的路线引理. 这两个定理的跨层部分不用 UIP; UIP 只经 ValC, ValX 的同层定理进来.
4. **`Pr`** ([SameVLeg](SameVLeg.lagda.md)): 配对对推导递归. `s≤s` 添一对顶; `l≤l` 是各项的并; 不同项由上下界分开 (`gap`). 这里用到 `leg` 的部分和.
5. **地板律 `tp` 与 `gtP`** ([SameVGoal](SameVGoal.lagda.md)): 沿同一个推导逐构造子. `top` 对第一位置右移 (`topR`), `gt` 同 (`gtR`). 世界 $\ge1$ 保护分量 0: 本身只配本身 (`G1`, `nodeN`), 与否定一路 `self≰copy` 不冲突 (`Wl` 对本身配拷贝给不出).

## 文件, 编译, 检查

编译 (从仓库根, 退出码不经管道): `agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes probes/OCF/Lean/SameV.lagda.md +RTS -M6G -RTS`; 脚本 `probes/Survey/scripts/samev/verify.sh`. 2026-11-06 结果见汇报. 禁用构造: 全部 `SameV*` 无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 无 `--with-K`.

## 翻译账

- **新定义来自哪里.** 没有新的树、折叠或合法性 (第 4 层). 新的是配对、跨层关系、前缀. 都由树逼出: 配对的三条律是 `pick` 的三种决定要的; 逻辑关系的分支是因为坐标没有反方向的映射; 前缀是因为 $\boxplus$ 的结合律对 ℕ-极限要函数外延. 记号没有参与.
- **脚手架.** `Pf`, `Pr`, `tp`, `gtP` 是值的证明需要的, 随 `leg` 的形状写, 不是翻译带来的. 若换掉 `leg` (例如改回灌), `SameVLeg` 与 `SameVGoal` §3, §4 要重做, `SameVRel`, `SameVMono`, `SameVX` 不动 (它们对一切配对).
- **摆脱侧.** 第一次在闭项上跨过 "同值不同结构": 读法之外的第一条跨档值定理.
- **攀爬侧.** 读法不升.

## 接手清单

1. **`TU m` 对 $m$ 单调, `TU2` 高于一切 `TU m`.** 未证. 三个卡点 ((b) 是定理, 其余判断). (a) `TU m` 的输入是塔 `Lev bX m` 的折叠, 这一层没有同层的值理论 (ValC 只在空底的塔上): `crossΦ` 的 `≼Ω` 一侧要右边同层的 `monoΦ`, 所以先要 "底是 `XS` 的塔上的 ValC" (`monoΦ`, `route`, `MoΦ`), 底种类一律留; 再要 `SameVRel`, `SameVMono` 的底是 `XS` 的版本. 量: 估计 1500 行. (b) `crossX` 的右边要 `MoX`, 而 `TU 1` 的回灌链第 0 点不是 `MoX` (`SameVObs.¬Mo-u₀`, 定理): `inU 1` 放不到右边, 值合法也要换成跨层的版本, 或在根上再拆一次 (`goal` 就是这样绕开的). (c) `TU m` 的 $m$ 是裸的合法树, 不经 `leg`, 对 $m\le m'$ 的任意推导没有部分和保护, `Pr` 的单值不成立; 要么只取字面 $m\lhd m'$ (配对是恒等, `TU2` 的 $y_n$ 是这种), 要么要求推导协调.
2. **去掉 UIP.** 跨层部分不用; 同层的 `monoΦ`, `route`, `monoX` 用 (`selfLoop`). 否定一路 `NegValXUip`: `selfLoop` 与 UIP 等价 (本路未复核).
3. **接口的 `CrossV`.** 本路没有实例. `Match` 版的 `crossΦ` 相当于对一个 $M$ 的版本; 要 `CrossV` 的形状 (关系随 `res M q` 变) 需要 `Le` 对限制的不变性 (判断: 对 $M$ 的像相同的两个搬运, 关系等价). 否定一路 `NegSameVBlind.crossV` 给了无跨层内容的实例并指出字段不够 (本路未复核).
4. **定量的严格.** `goal` 只有 $+1$. 看 `P1` 能否加强成 $k_R$ 高于 $k_L$ 的某个极限.
5. **`P2` 的逆.** `leg` 上任意推导给配对, 用到部分和; 若把 `leg` 去掉 (回灌用别的办法), 否定一路的 `kR-not-val` 一类结果要重查.

## 结论 (按档)

- **[定理, 无条件]** `lv→match`, `le₂₁`; [SameVRel](SameVRel.lagda.md) 全部; [SameVLeg](SameVLeg.lagda.md) 全部 (`Pr`, `fun`, `smP`, `M.match`).
- **[定理]** `SameVObs.¬Mo-u₀` (模块参数 `uipC` 只是命名空间).
- **[条件定理, 条件 `Cd` 上的 UIP (由 Funext 推出) 与地板律]** `crossΦ`, `crossX` (对一切配对, `crossX` 另要 `ShLaw`).
- **[条件定理, 条件 Funext]** 本篇 **`P2`**, **`P2L`**, `ex₁₂`, `ex₂₁`, `hyp`, **`goal₀`**, **`goal`**: $\mathrm{TX}+1\le\mathrm{TU}\,1$; **`goal2₀`**, `goal2`: $\mathrm{TX}+2\le\mathrm{TU2}$. 另 `SameVGoal.Core.tp`, `gtP`, `UX` (条件 UIP).
- **[判断]** 读法 (`TX` ψ₀(Ω_Ω), `TU 1` ψ₀(Ω_{Ω+1}), `TU2` ψ₀(Ω_{Ω·2}), 同 CRw, 无定理); 接手清单的路线与估计.
