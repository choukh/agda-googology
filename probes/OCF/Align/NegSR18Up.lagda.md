# 第十八轮的否定 (三): `Up` 不可靠 (带时间条件也一样); 跨层的传递性不成立

> 不读记号. 入口 [NegSR18](NegSR18.lagda.md). 对着接口 [StrRel18If](StrRel18If.lagda.md) (定稿 2026-11-05 14:22) §3 的 `UpSound`, `SemR`, `OAR` 写. 实例 $\Lambda_2=2$, 沿用 [NegSR17RkT](NegSR17RkT.lagda.md) 的节点 `r₀` (分支 `n1`), 产生时的动作 `Az`, 产生状态 `YP`.
>
> 1. **(否定, 值) `¬UpSoundR`**: 对一切关系族 $R$, 只要 (一) 它含 `RelX⁺` (`EmbR`), (二) 它在第 $0$ 层值可靠 (`VS0R`: $R\,0\,0\,x\,y$ ⇒ $\Sigma_0 x\le\Sigma_0 y$), 对一切在 $(Y_P,Y_P)$ 上成立的条件 `Ok`, `UpSound R Ok` 都不成立. 推论 **`¬UpSound-DomL`**: `UpSound RelX⁺ (DomL tt YP)` 不成立 (时间条件就是这个节点的产生状态); **`¬UpSound-Any`**: 不带条件也不成立.
>
>    构造: $x$ 取上升输出 `OLof YP` 的一个分量 `xU` (链的第一段的第一个 `n1` 调用分支动作的输出, 字面是 `lift zP ⨾ n1`). `xU ≤ OLof YP` 由 `in⁺` 得到, 第 $0$ 层的语义无条件成立 (`StrRel16Sem.semX00⁺`), 于是 `SemR R … xU (OLof YP)` 对一切 `Ok` 成立. `UpSound` 把它变成 `SemR R … xU (ORof YP)` (同一节点在 $T_1$ 上的保留输出). 两边都以 `YP`, 动作 `C1` 再折叠: 左边 $\ge \Sigma z_P+1$, 右边与 `NegSR17RkT` 的 `RefR₀` 同值 ($z_P$ 由它定义, 比它大), 矛盾.
> 2. **(否定) `¬trans⁺`**: `RelX⁺` 的跨层传递性 (第 $0$ 层, 第 $0$ 层, 第 $1$ 层) 不成立: `n1 ≤ Lr` (`in⁺`), `Lr ≤ Kr` (`StrRel16Kr.rkAt`, 即 `rk⁺`), 而 `n1 ≤ Kr` 推不出 (`¬oneK`: 右边是节点时, 左边只能是 `n0` 或字面的上升输出). `Up` 加的正是这一类实例 (`Lr` 与 `Kr` 是同一节点同一组参数的两个输出).
>
> **构造一路为什么需要这些.** `StrRel17` 的接手清单与接口 §3: `Up` 是 "`rk⁺` = 升升义务 + `Up`" 的后一半, 要把它加进关系, 就要它的可靠性 `UpSound`; 可靠性的一个来源是传递性 (`Trans00`). 第 1 条说: `UpSound` 本身是假的, 与传递性无关, 与 `Ok` 取哪个时间条件无关 (只要它在产生状态自己身上成立; `DomL` 是这样). 机制同 `NegSR17RkT`: 上升输出在产生时运行链, 读到累计 $z_P$; 保留输出的分支在 `cv` 之后运行, 累计被清掉. `Up` 允许左边是上升输出的**任何**下界, 所以只要上升输出比保留输出 "多读了" 产生时的累计, `Up` 就把这个差带过去. 第 2 条说: 不加 `Up` 时 `RelX⁺` 缺的正是这一类传递的实例.
>
> **只否定什么.** 第 1 条否定 `UpSound R Ok` 对一切满足 (一) (二) 的 $R$ 与一切在 $(Y_P,Y_P)$ 上成立的 `Ok`. 产生时的动作 `Az` 读累计 (`UpSound` 不限动作). 不否定把 `Up` 限制为产生时动作满足 `NoZ` 的版本 (判断: 那时左边要读累计只能经分支里的 `nκ`, 而保留输出的分支里同样有 `nκ` 在再折叠时读再折叠状态的累计, 见 `NegSR18Z.brK`; 未比较值). 第 2 条否定的是跨层的传递性, **不是**接口的 `Trans00` (三个第 $0$ 层的树): `Trans00` 本文没有否定, 也没有证明 (构造一路的 `StrRel18Tr.trans00⁺` 声称证明了它, 本路未复核). 又, 第 1 条说明 `UpSound` 不能由 `Trans00` 推出, 除非同时用到某个假的前提 (例如 `rk⁺` 对这一对的可靠性). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `EmbR RelX⁺` 是 `id`, `VS0R RelX⁺` 是 `V0.vsum⁺`; `DomL tt YP` 在 $(Y_P,Y_P)$ 上由 `NegSR17RkT.jYP` 给出, `Any` 由 `tt`. `UpSound` 的其余参数都是闭项, 种类 `refl`. 第 2 条: `oneL`, `LK` 是定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR18Up where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤-refl; ≤-trans; ≤-suc; irr)
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; ss; z⊲ᴴ; StH; Vs; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; accL; sum)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel15Fin using (T₁)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Lem using (module V0)
open import OCF.Align.StrRel16If Λ₂ tt
open import OCF.Align.StrRel16Sem Λ₂ tt using (semX00⁺)
open import OCF.Align.StrRel16Kr using (rkAt)
open import OCF.Align.StrRel17If Λ₂ tt using (Cond; Any; DomL)
open import OCF.Align.StrRel18If Λ₂ tt using (RelT; OAR; SemR; UpSound)
open import OCF.Align.NegSR17Rk using (C1; hawC1⁺; module RK)
open import OCF.Align.NegSR17RkT using (Az; uN; rk1; OLof; ORof; RefRof; RefR₀; zP; YP; refR≈; jYP; lift; sum≈; sumDrp; sumLift)

open Rk Λ₂ tt using (s∞; u∞)
open FinΛ⁺ Λ₂ tt tt using (Y₁)
open V0 Λ₂ tt using (vsum⁺)
open P using (Tg; τ₀; St; yc; Run; RKi; Act; rise; keep)
```

## 1 `Up` 的左边: 上升输出的一个分量

```agda
-- lift 之后的第 0 层树与自己相关 (lift 去掉了 nw)
reflLift⁺ : ∀ {V V′ W} {lV : Lg V} {lV′ : Lg V′} (x : D₀ W) → RelX⁺ hz hz lV lV′ (lift {hz} {V} x) (lift {hz} {V′} x)
reflLift⁺ n0 = n0⁺
reflLift⁺ n1 = n1⁺
reflLift⁺ (x ⨾ y) = ⨾⁺ (reflLift⁺ x) (reflLift⁺ y)
reflLift⁺ (nl e) = nl⁺ (λ n → reflLift⁺ (e n))
reflLift⁺ (nw p x) = reflLift⁺ x
reflLift⁺ (ni () u)
reflLift⁺ (nκ () u)

-- 链的第一段的第一个 n1 调用分支动作 (分支 n1, 动作 Az): 输出 lift zP ⨾ n1
xU : D₀ azero
xU = lift {hz} {azero} zP ⨾ n1

relXU : RelX⁺ hz hz tt tt xU (OLof YP)
relXU = in⁺ (⨾⁺ (reflLift⁺ zP) (n1⁺ {V = azero} {V′ = azero} {lV = tt} {lV′ = tt})) (inE 0 (inE 0 (inL here)))

semXU : SemX²⁺ hz hz tt tt xU (OLof YP)
semXU = semX00⁺ relXU
```

## 2 `UpSound` 的否定

```agda
EmbR : RelT → Set
EmbR R = ∀ {t t′ V V′} {lV : Lg V} {lV′ : Lg V′} {x : D t V} {x′ : D t′ V′} → RelX⁺ t t′ lV lV′ x x′ → R t t′ lV lV′ x x′

VS0R : RelT → Set
VS0R R = ∀ {x y : D₀ azero} → R hz hz tt tt x y → sum azero x ≤ sum azero y

semRXU : ∀ (R : RelT) → EmbR R → ∀ (Ok : Cond) → SemR R hz hz tt tt Ok xU (OLof YP)
semRXU R emb Ok lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w w′ hw Y Y′ hY ok T T′ tx =
  emb (semXU lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w w′ hw Y Y′ hY T T′ tx)

module RL = RK {azero} tt C1 (λ w Y T → refl)

XRef : D₀ azero
XRef = yc (Run (accL hz) xU C.self tt (z⊲ᴴ Λ₂) C1 n0 YP) (τ₀ tt)

¬UpSoundR : ∀ (R : RelT) → EmbR R → VS0R R → ∀ (Ok : Cond) → Ok {azero} {azero} tt tt YP YP → ¬ UpSound R Ok
¬UpSoundR R emb vs Ok ok h =
  irr (sum azero RefR₀)
    (≤-trans (s≤ (sumDrp RefR₀ azero))
    (≤-trans (sumLift zP azero)
    (≤-trans (≤-suc (≤-refl _))
    (≤-trans (RL.ge (accL hz) xU C.self (z⊲ᴴ Λ₂) n0 YP (τ₀ tt) azero)
    (≤-trans (vs rel)
             (sum≈ refR≈ azero))))))
  where
  rel : R hz hz tt tt XRef (RefRof YP)
  rel = h {L₀ = hz} {x = xU} r₀ {u = uN} tt (accL Λ₂) (accL hz) C.self hself Az n0 YP (τ₀ tt) T₁ rk1 refl refl (semRXU R emb Ok)
          tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 C1 C1 (hawC1⁺ hz (hs hz))
          n0 n0 n0⁺ YP YP jYP ok (τ₀ tt) (τ₀ tt) (cp00 , s∞)

¬UpSound-DomL : ¬ UpSound RelX⁺ (DomL tt YP)
¬UpSound-DomL = ¬UpSoundR RelX⁺ (λ r → r) (λ r → vsum⁺ r (≤-refl azero)) (DomL tt YP) jYP

¬UpSound-Any : ¬ UpSound RelX⁺ Any
¬UpSound-Any = ¬UpSoundR RelX⁺ (λ r → r) (λ r → vsum⁺ r (≤-refl azero)) Any tt
```

## 3 跨层的传递性不成立

`Lr`, `Kr`: `StrRel16Kr.rkAt` 的那一对 (节点 `r₀`, 分支 `n1`, 动作 `Act`, 状态 $Y_1$; 左在 $\tau_0$ 上升, 右在 $T_1$ 保留).

```agda
Lr : D hz azero
Lr = RKi (accL Λ₂) (accL hz) r₀ (λ _ _ _ → n1) C.self tt hself Act n0 (Y₁ tt) (τ₀ tt) rise

Kr : D (hs hz) azero
Kr = RKi (accL Λ₂) (accL hz) r₀ (λ _ _ _ → n1) C.self tt hself Act n0 (Y₁ tt) T₁ (keep (ss hself))

oneL : RelX⁺ hz hz tt tt n1 Lr
oneL = in⁺ (n1⁺ {V = azero} {V′ = azero} {lV = tt} {lV′ = tt}) (inE 0 (inR (inE 0 (inL (inE 0 (inL here))))))

LK : RelX⁺ hz (hs hz) tt tt Lr Kr
LK = rkAt

-- 右边是节点时, 左边的 n1 推不出
¬oneK : ∀ {L′ V V′ k′} {lV : Lg V} {lV′ : Lg V′} {R : StH V′ k′ L′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ R W′ → D L′ W′} →
        ¬ RelX⁺ hz L′ lV lV′ n1 (ni R u′)
¬oneK (in⁺ h here) = ¬oneK h

Trans⁺ : Set
Trans⁺ = ∀ {L L′ L″ V V′ V″} {lV : Lg V} {lV′ : Lg V′} {lV″ : Lg V″} {x : D L V} {y : D L′ V′} {x″ : D L″ V″} →
         RelX⁺ L L′ lV lV′ x y → RelX⁺ L′ L″ lV′ lV″ y x″ → RelX⁺ L L″ lV lV″ x x″

¬trans⁺ : ¬ Trans⁺
¬trans⁺ tr = ¬oneK (tr oneL LK)
```
