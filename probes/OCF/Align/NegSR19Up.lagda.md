# 第十九轮的否定 (五): `up` 的产生时动作限为 `ActS`, 不带时间条件仍不可靠

> 不读记号. 入口 [NegSR19](NegSR19.lagda.md). 对着接口 [StrRel19If](StrRel19If.lagda.md) (定稿 2026-11-05 16:01) §5 的 `UpSoundS` 写. 实例 $\Lambda_2=2$, 节点、分支、状态同 [NegSR19Rk](NegSR19Rk.lagda.md) (节点 `r₀`, 分支 `nκ`, 产生时动作 `Act`, 产生状态 $Y_P$).
>
> **(否定, 值) `¬UpSoundS-Any`**: `UpSoundS (λ _ _ → Any)` 不成立. 左边 $x$ 取上升输出 `OLof YP` 的一个分量 `AiOut YP` (链的第一个 `n1` 调用分支动作的输出, 分支的 `nκ` 回灌, 读到 $z_P$). 前提 `SemS x (OLof YP)` 由 `NegSR19Sem.sem-in` 与 `semS00` 无条件得到. `UpSoundS` 把它变成 `SemS x (ORof YP)`; 两边以 $Y_0$, `Act` 再折叠: 左 $>\Sigma\,\mathrm{RefR}$ (`lowAi`, `RKA.ge`), 右就是 `RefR` (`ORof YP` 与 `ORof Y0` 定义性地相同). 矛盾.
>
> **对任务 (i) 的回答.** 接口 "范围 (iii)": `up` 的产生时动作要 `ActS`, 为的是排除 `NegSR18Up.¬UpSoundR` 的反例 (`Az`). `Az` 确实被排除 (`NegSR19Good.¬ActS-Az`), 但 `¬UpSoundR` 的**机制** (上升输出在产生时读累计, 保留输出的分支在 `cv` 之后运行) 在 `ActS` 下重现: 读累计的是分支里的 `nκ`, `ActS` 管不到. 所以 `UpSoundZ` 若成立, 靠的是 `DomZ` 的累计分量 (本反例的再折叠被它挡住: `NegSR19Rk.¬domZ-Y0`, 同一对状态).
>
> **构造一路为什么需要这条律.** `up` 是 `RelX⁺⁺` 的新构造子, 以 `RelX⁺⁺` 为输出关系的语义要它的可靠性 `UpSoundS Ok` (接口 §5, `Ok = DomZ` 时就是 `UpSoundZ`).
>
> **只否定什么.** 只否定 `UpSoundS (λ _ _ → Any)` (条件恒真). **不否定 `UpSoundZ`** (判断: `DomZ` 下右边再折叠状态的读数支配 $z_P$, 右边的链从这个读数起, `Act` 每次也读它, 对称; 未比较值). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `UpSoundS` 的参数: 节点 `r₀`, 分支 `uK`, `sAct`, 种类 `refl`/`refl` (同 `NegSR19Rk.kL`, `kR` 的计算), 前提 `semL` (定理). 再折叠: `cp00`, `hawS hz (hs hz)`, `n0⁺⁺`, `jYs⁺⁺ n0⁺⁺`, 条件 `tt`, 目标对 `(cp00 , s∞)`. 全部是定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR19Up where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (azero; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (≤-refl; ≤-trans; irr)
open import OCF.Align.HtFeedTree using (hz; hs; hself; hsuc; z⊲ᴴ; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; drp; accL; sum)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel15Fin using (T₁)
open import OCF.Align.StrRel16If Λ₂ tt using (module P)
open import OCF.Align.StrRel17If Λ₂ tt using (Any)
open import OCF.Align.StrRel19If Λ₂ tt
open import OCF.Align.NegSR17RkT using (rk1)
open import OCF.Align.NegSR19Lem using (module V0⁺⁺; module Fin⁺⁺)
open import OCF.Align.NegSR19Sem Λ₂ tt using (sem-in; semS00)
open import OCF.Align.NegSR19Rk using (uK; OLof; ORof; Y0; YP; RefR; AiOut; inAi; lowAi; module G)

open Rk Λ₂ tt using (s∞)
open V0⁺⁺ Λ₂ tt using (vsum⁺⁺)
open Fin⁺⁺ Λ₂ tt tt using (hawS; jYs⁺⁺)
open P using (τ₀; Run; Act)
```

```agda
reflDrp⁺⁺ : ∀ {V V′ W} {lV : Lg V} {lV′ : Lg V′} (x : D₀ W) → RelX⁺⁺ hz hz lV lV′ (drp x) (drp x)
reflDrp⁺⁺ n0 = n0⁺⁺
reflDrp⁺⁺ n1 = n1⁺⁺
reflDrp⁺⁺ (x ⨾ y) = ⨾⁺⁺ (reflDrp⁺⁺ x) (reflDrp⁺⁺ y)
reflDrp⁺⁺ (nl e) = nl⁺⁺ (λ n → reflDrp⁺⁺ (e n))
reflDrp⁺⁺ (nw p x) = reflDrp⁺⁺ x
reflDrp⁺⁺ (ni () u)
reflDrp⁺⁺ (nκ () u)

-- AiOut YP 是 nκ 回灌的输出: nl (λ n → drp …)
reflAi : RelX⁺⁺ hz hz {azero} {azero} tt tt (AiOut YP) (AiOut YP)
reflAi = nl⁺⁺ (λ n → reflDrp⁺⁺ _)

semL : SemS hz hz {azero} {azero} tt tt Any (AiOut YP) (OLof YP)
semL = sem-in (semS00 reflAi) inAi

LRefX : D₀ azero
LRefX = P.yc (Run (accL hz) (AiOut YP) C.self tt (z⊲ᴴ Λ₂) Act n0 Y0) (τ₀ tt)

¬UpSoundS-Any : ¬ UpSoundS (λ _ _ → Any)
¬UpSoundS-Any h =
  irr (sum azero RefR)
    (≤-trans lowAi (≤-trans (G.ge (accL hz) (AiOut YP) C.self (z⊲ᴴ Λ₂) n0 Y0 (τ₀ tt) azero) (vsum⁺⁺ rel (≤-refl azero))))
  where
  rel : RelX⁺⁺ hz hz {azero} {azero} tt tt LRefX RefR
  rel = h {x = AiOut YP} r₀ {u = uK} tt (accL Λ₂) (accL hz) C.self hself Act n0 YP (τ₀ tt) T₁ rk1 sAct refl refl semL
          tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 Act Act (hawS hz (hs hz))
          n0 n0 n0⁺⁺ Y0 Y0 (jYs⁺⁺ n0⁺⁺) tt (τ₀ tt) (τ₀ tt) (cp00 , s∞)
```
