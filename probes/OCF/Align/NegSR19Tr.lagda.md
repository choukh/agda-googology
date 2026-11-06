# 第十九轮的否定 (一): `up` 补上了 `¬trans⁺` 的那一对, 但 `RelX⁺⁺` 仍不是跨层传递的

> 不读记号. 入口 [NegSR19](NegSR19.lagda.md). 对着接口 [StrRel19If](StrRel19If.lagda.md) (定稿 2026-11-05 16:01) §1–§2 的 `ActS`, `RelX⁺⁺`, `up`, `rk⁺⁺` 写. 实例 $\Lambda_2=2$.
>
> 1. **(定理) `oneK⁺⁺`**: `NegSR18Up.¬trans⁺` 的那一对现在在关系里: `n1 ≤ Lr` (`in⁺⁺`), 而 `Lr` 与 `Kr` 是同一节点 (`r₀`, 分支 `n1`, 产生时动作 `Act`, 状态 $Y_1$) 在 $\tau_0$ 上的上升输出与在 $T_1$ 上的保留输出, 所以 `up` (带 `sAct`) 给出 `n1 ≤ Kr`. 旧的反例不再分开.
> 2. **(定理) `noN1`**: 对 `RelX⁺⁺ hz L′` 的推导求逆 (对一切右层): 左边是 `n1`, 右边是节点 `ni R u′` 时, 右边分支在 (`self`, 输入 `n0`) 上的值一定 "好" (`NegSR19Good.Good`, 不是 `… ⨾ n1`). 理由: 以节点为右边的规则只有 `n0⁺⁺`, `ni⁺⁺` (左边要是第 $0$ 层的节点, 不存在), `in⁺⁺` (节点的分量只有它自己), `rk⁺⁺` (左边是 `nl`, 不是 `n1`), `up` (右边是 `ActS` 动作的保留输出, 分支是 `ActS` 的分支动作的输出, `NegSR19Good.goodActS`).
> 3. **(否定) `¬trans⁺⁺`**: `RelX⁺⁺` 的跨层传递性 (第 $0$, $0$, $1$ 层) 不成立. 实例是 `NegSR17RkT` 的那一对 (节点 `r₀`, 分支 `n1`, 产生时动作 `Az`, 状态 $Y_P$): `n1 ≤ OLof YP` (`in⁺⁺`), `OLof YP ≤ ORof YP` (`rk⁺⁺`, 前提 `NegSR17RkT.preP`, 旧关系, 不要 `ActS`), 而 `n1 ≤ ORof YP` 推不出 (`¬n1Kr`): 右边分支的值字面是 `lift (累计) ⨾ n1`, 不好.
>
> **构造一路为什么需要这条律.** 接手清单 (`StrRel17`, `StrRel18` 第 2 项) 把传递性列为 `Up` 的可靠性的一个来源; 本轮的 `up` 是为了补上 "`rk⁺` 加传递" 缺的实例 (`NegSR18Up.¬trans⁺`). 第 1 条说旧实例补上了; 第 3 条说补完之后跨层传递性仍不成立, 缺口换成了 "`rk⁺⁺` 不要 `ActS`, `up` 要": 若跨层传递成立, `up` 的 `ActS` 前提在 `rk⁺⁺` 联结的那一对上就是多余的 (对 `Az` 也给出 `x ≤ 保留输出`), 而 `Az` 正是 `NegSR18Up.¬UpSoundR` 的产生时动作.
>
> **只否定什么.** 只否定 `Trans⁺⁺` (三个层都任意的传递性). 不否定第 $0$ 层的 `Trans00⁺⁺` (`StrRel18Tr.trans00⁺` 对 `RelX⁺` 证明了它; 对 `RelX⁺⁺` 本文没有试; 判断: 右层为 $0$ 时 `up` 与 `rk⁺⁺` 都不出现, 证明可以照搬). 不否定 "只对 `ActS` 的产生时动作" 的传递性 (判断: 若 `rk⁺⁺` 也要求两边动作 `ActS`, 本文的实例消失, 未试). 反例用的 `rk⁺⁺` 实例的可靠性另见 `NegSR17RkT` (它在 `DomL` 下不可靠); 本文只看可推导性. 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `oneK⁺⁺`: `sAct`, 种类 `refl`/`refl`. `¬trans⁺⁺` 的两段: `in⁺⁺ n1⁺⁺ (路径)`, `rk⁺⁺ … preP (cp00 , u∞ s∞) refl refl`, 都是定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR19Tr where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; ss; StH; Vs; D; n0; n1; _⨾_; nl; ni; nκ; accL; inS)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel15Fin using (T₁)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16If Λ₂ tt using (module P; In; here; inL; inR; inE)
open import OCF.Align.StrRel19If Λ₂ tt
open import OCF.Align.NegSR19Good Λ₂ tt using (Good; Bad; good→¬bad; goodActS)
open import OCF.Align.NegSR17RkT using (Az; uN; rk1; OLof; ORof; YP; preP)

open Rk Λ₂ tt using (s∞; u∞)
open FinΛ⁺ Λ₂ tt tt using (Y₁)
open P using (τ₀; RKi; Act; rise; keep)
```

## 1 旧的实例补上了

```agda
Lr : D hz azero
Lr = RKi (accL Λ₂) (accL hz) r₀ (λ _ _ _ → n1) C.self tt hself Act n0 (Y₁ tt) (τ₀ tt) rise

Kr : D (hs hz) azero
Kr = RKi (accL Λ₂) (accL hz) r₀ (λ _ _ _ → n1) C.self tt hself Act n0 (Y₁ tt) T₁ (keep (ss hself))

oneL⁺⁺ : RelX⁺⁺ hz hz {azero} {azero} tt tt n1 Lr
oneL⁺⁺ = in⁺⁺ (n1⁺⁺ {V = azero} {V′ = azero} {lV = tt} {lV′ = tt}) (inE 0 (inR (inE 0 (inL (inE 0 (inL here))))))

oneK⁺⁺ : RelX⁺⁺ hz (hs hz) {azero} {azero} tt tt n1 Kr
oneK⁺⁺ = up r₀ {u = λ _ _ _ → n1} tt (accL Λ₂) (accL hz) C.self hself Act n0 (Y₁ tt) (τ₀ tt) T₁ (ss hself) sAct refl refl oneL⁺⁺
```

## 2 求逆: 左边 `n1`, 右边节点

```agda
-- 右边是节点时: 它的分支在 (self, 输入 n0) 上的值是坏的
Q : ∀ {L′ V′} → Lg V′ → D L′ V′ → Set
Q lV′ (ni R u′) = Bad (u′ C.self lV′ (inS R n0))
Q lV′ _ = ⊥

qIn : ∀ {L′ V′} {lV′ : Lg V′} {y′ x′ : D L′ V′} → In y′ x′ → Q lV′ x′ → Q lV′ y′
qIn here q = q

noN1 : ∀ {L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x : D hz V} {x′ : D L′ V′} → RelX⁺⁺ hz L′ lV lV′ x x′ → x ≡ n1 → Q lV′ x′ → ⊥
noN1 n0⁺⁺ () q
noN1 n1⁺⁺ e ()
noN1 (⨾⁺⁺ h h′) () q
noN1 (nl⁺⁺ h) () q
noN1 (pr⁺⁺ h) e ()
noN1 (nw⁺⁺ ap h) () q
noN1 (ni⁺⁺ {r = ()} _ _) e q
noN1 (κ⁺⁺ {zz = ()} _) e q
noN1 (in⁺⁺ h p) e q = noN1 h e (qIn p q)
noN1 (rk⁺⁺ r r′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ R′ pre tx eL eR) () q
noN1 (nκ⁺⁺ {r = ()} _) e q
noN1 (up r {u} lW ac ac₁ q₀ ll A₀ w Y T T′ R′ sA eL eR h) e q =
  good→¬bad (goodActS (sAi ac ac₁ r u q₀ (P.kk r q₀ ll) ll w sA) _ _ _ _ _) q
```

## 3 跨层传递性不成立

```agda
-- n1 是 OLof YP 的链的第 0 段里 Az 的输出 (lift zP ⨾ n1) 的右分量
oneAz : RelX⁺⁺ hz hz {azero} {azero} tt tt n1 (OLof YP)
oneAz = in⁺⁺ (n1⁺⁺ {V = azero} {V′ = azero} {lV = tt} {lV′ = tt}) (inE 0 (inE 0 (inL (inR here))))

rkAz : RelX⁺⁺ hz (hs hz) {azero} {azero} tt tt (OLof YP) (ORof YP)
rkAz = rk⁺⁺ r₀ r₀ {u = uN} {u′ = uN} tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Az Az n0 n0 YP YP
         (τ₀ tt) T₁ rk1 preP (cp00 , u∞ s∞) refl refl

¬n1Kr : ¬ RelX⁺⁺ hz (hs hz) {azero} {azero} tt tt n1 (ORof YP)
¬n1Kr h = noN1 h refl (_ , refl)

Trans⁺⁺ : Set
Trans⁺⁺ = ∀ {L L′ L″ V V′ V″} {lV : Lg V} {lV′ : Lg V′} {lV″ : Lg V″} {x : D L V} {y : D L′ V′} {x″ : D L″ V″} →
          RelX⁺⁺ L L′ lV lV′ x y → RelX⁺⁺ L′ L″ lV′ lV″ y x″ → RelX⁺⁺ L L″ lV lV″ x x″

¬trans⁺⁺ : ¬ Trans⁺⁺
¬trans⁺⁺ tr = ¬n1Kr (tr oneAz rkAz)
```
