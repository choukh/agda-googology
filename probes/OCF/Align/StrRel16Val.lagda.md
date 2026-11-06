# 结构关系, 第十六轮 (二): 决定性实验: `xL` 在目标对 $(0,1)$ 上的两个输出再折叠一次

> 不读记号. 入口 [StrRel16](StrRel16.lagda.md). 接口 [StrRel16If](StrRel16If.lagda.md).
>
> **(定理, 值) `valLK`: 通过.** `xL` 在目标对 $(0,1)$ 上的两个输出 (链的极限 `OutL`, 节点 `OutR`; `StrRel15Bar.¬semXLL` 的那一对) 各按自己的层以 `Act`, `n0`, $Y_1$ 再折叠, 读第 $0$ 层: $\Sigma_0(\mathrm{LaterL})\le\Sigma_0(\mathrm{LaterR})$. 结构形 `valLK⁺`: `RelX⁺ hz hz LaterL LaterR`, 由 `in⁺` (左边在右边的一个分量之下). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel16Val where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.CumReadCF using (azero)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl; ≤-trans)
open import OCF.Align.HtFeedTree using (hz; hs; hself; hsuc; ss; z⊲ᴴ; D; D₀; n0; n1; accL; sum)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel15Node as Nd
open import OCF.Align.StrRel14NegNode using (module G)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; xL; cp00)
open import OCF.Align.StrRel15Sem Λ₂ tt using (semX0)
open import OCF.Align.StrRel15Fin using (module FinΛ; T₁)
open import OCF.Align.StrRel16If Λ₂ tt using (In; here; inL; inR; inE)
open import OCF.Align.StrRel16Lem using (inSum; Lp; here; left; module Pf)

open Rk Λ₂ tt using (s∞)
open If Λ₂ tt using (RelX; n0ˣ)
open FinΛ Λ₂ tt tt using (stepOA²; Y₁; hY₁)
open Pf Λ₂ tt using (jPfx)
module P = At Λ₂ tt
open P using (Tg; τ₀; St; Df; yc; Run; Act)
```

## 1 两个输出与它们的再折叠

`ΔL`: `xL` (层 $2$, 坐标层 $0$, 分支 `n1`) 在世界 $0$, 路径 `self`, 动作 `Act`, 上下文 `n0`, 状态 $Y_1$ 上的运行. 在第 $0$ 层目标上它上升 (`OutL` 是链的极限), 在第 $1$ 层目标上它保留 (`OutR` 是节点). 这正是 `StrRel15Bar.¬semXLL` 的那一对. 再折叠: 各按自己的层, 同一组参数 (`Act`, `n0`, $Y_1$), 读第 $0$ 层目标.

```agda
ΔL : Df azero
ΔL = Run (accL Λ₂) xL C.self tt hself Act n0 (Y₁ tt)

OutL : D hz azero
OutL = yc ΔL (τ₀ tt)

OutR : D (hs hz) azero
OutR = yc ΔL T₁

LaterL LaterR : D₀ azero
LaterL = yc (Run (accL hz) OutL C.self tt (z⊲ᴴ Λ₂) Act n0 (Y₁ tt)) (τ₀ tt)
LaterR = yc (Run (accL (hs hz)) OutR C.self tt (hsuc hself) Act n0 (Y₁ tt)) (τ₀ tt)
```

## 2 结论: 左边的再折叠是右边的再折叠的一个分量之下

证明的路线 (每一步是一个已编译的定理):

1. 右边的再折叠在第 $0$ 层目标上上升 (坐标层 $0$), 是一条链, 动作是 `OutR` 的分支动作; 链的第一项是 $Y_1$ 在第 $0$ 层的读数 $0⨾\omega\cdot(1⨾0)$ 的运行, 其中第一个 `n1` 调用分支动作, 分支是 $\omega\cdot(\Omega_1⨾\ldots)$ (`OutR` 的分支是 `BNi`, 它在常数 `n1` 的分支上就是 `Step`). 这里的 $\Omega_1=1⨾\mathrm{ni}\ldots$ 含一个坐标层 $0$ 的节点 (记作 $N$); 它的第一份 ($N_0$) 与第二份 ($N_1$) 在第 $0$ 层目标上都上升.
2. **`OutL` 与 $N_0$ 的上升输出 `RelX hz hz` 相关**: `StrRel15Node.Zero.oblRR` (左 `xL`, 右 $N$, 两个坐标层都是 $0$, 分支动作都化成 `Step`), 状态前提 `J² Y₁ S°` 由 `hY₁` 与 `jPfx` 给出 ($S^\circ$ 是 $Y_1$ 向右延长两次).
3. **$N_1$ 的链的第一项里, $N_0$ 的上升输出又被运行一次**; 由 `StrRel15Sem.semX0` (左层为 $0$), `OutL` 的再折叠 (`LaterL`) 与这次运行的输出 `RelX hz hz` 相关, 状态前提 `J² Y₁ S*` 同样由 `jPfx` 给出 ($S^*$ 是 $Y_1$ 向右延长五次).
4. 这次运行的输出是 `LaterR` 的一个分量 (`In`, 十二步); 由 `in⁺` 得 `RelX⁺ hz hz LaterL LaterR` (**`valLK⁺`**), 再由 `vsum⁺` 得值 (**`valLK`**).

```agda
open import OCF.Align.StrRel16If Λ₂ tt using (RelX⁺; in⁺)
open import OCF.Align.StrRel16Lem using (module V0)
open V0 Λ₂ tt using (embX00; vsum⁺)

valLK⁺ : RelX⁺ hz hz tt tt LaterL LaterR
valLK⁺ =
  in⁺
    (embX00
      (semX0
        (Nd.Zero.oblRR Λ₂ tt {lV = tt} {lV′ = tt} r₀ (ss hself) (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt (accL Λ₂) (accL hz) _ _
           C.self _ hself _ Act _ n0 _ (Y₁ tt) _
           cp00 (λ p p′ l l′ cp z₁ z₁′ hz₁ Y Y′ hY → stepOA² hY)
           (jPfx (hY₁ tt tt) ((λ T → left (left here)) , left (left here)))
           (τ₀ tt) _ (cp00 , s∞) refl refl)
        tt tt (accL hz) _ (z⊲ᴴ Λ₂) _ C.self _ cp00 Act _ (λ p p′ l l′ cp w w′ hw Y Y′ hY → stepOA² hY) n0 _ n0ˣ (Y₁ tt) _
        (jPfx (hY₁ tt tt) ((λ T → left (left (left (left (left here))))) , left (left (left (left (left here))))))
        (τ₀ tt) (τ₀ tt) (cp00 , s∞)))
    (inE 0 (inR (inE 0 (inL (inE 1 (inL (inR (inE 0 (inL (inR (inL (inR here))))))))))))

valLK : sum azero LaterL ≤ sum azero LaterR
valLK = vsum⁺ valLK⁺ (≤-refl azero)
```

**范围.** `valLK` 是关于这一对输出、这一组再折叠参数 (动作 `Act`, 上下文 `n0`, 状态 $Y_1$, 即与产生它们时相同的状态) 的值的定理. 它不是 `RkSound₀ (hs hz)` (接口 §6: 一切 `J²⁺` 的再折叠状态、一切 `HAW²⁺` 动作、一切目标对). 证明用到的关键一步 (第 2 步) 是: 右边再折叠时内部的状态 $S^\circ$ 是产生 `OutL` 时的状态 $Y_1$ 向右延长; 一般的再折叠状态与产生时的状态之间没有这样的关系 (判断, 见入口 §2).
