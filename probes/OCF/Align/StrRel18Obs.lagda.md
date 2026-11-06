# 结构关系, 第十八轮 (二): (a) 与 (c) 碰不到第一个障碍; (c) 的三个变体各自的位置

> 不读记号. 入口 [StrRel18](StrRel18.lagda.md). 接口 [StrRel18If](StrRel18If.lagda.md) §1–§2. 实例 $\Lambda_2=2$ (没有 $\Omega$-极限), 用 `StrRel17Obs` 的 `rkAt` 那一对 (节点 `r₀`, 分支 `n1`, 动作 `Act`, 上下文 `n0`, 产生状态 $Y_1$, 左在 $\tau_0$ 上升, 右在 $T_1$ 保留).
>
> 1. **(定理) `chkKSt`**: 接口的 `KSt` 就是 `BNi` 传给分支动作的状态 (一切 $\Lambda$, `refl`).
> 2. **(定理, 约化) `obsZ`**: `RkSoundTᶻ hz (hs hz)` ⇒ `RkLeft tt ReL`. `Act` 满足 `NoZ` (`noZΛ₂`), 所以 (a) 的限制不排除 `rkAt` 那一对; 右边保留的再折叠目标对 $(\tau_0,T_1)$ 上, 结论 `RelX⁺ hz (hs hz) … (ni …)` 只能来自字面的 `rk⁺` (`StrRel17Obs.invNi`). 与 `StrRel17Obs.obsRkT` 同.
> 3. **(否定, 定理) `¬domKJ`**: (c) 的变体 `kJ` (`DomK`: 右边保留分支运行时的状态 `J²⁺` 支配左边产生时的状态) 在 `rkAt` 那一对上不成立: 输入 `n0` 时分支运行的状态的累计是 `n0 ⨾ n0` (`cv` 清零), 而 $Y_1$ 的累计是 $0⨾\omega\cdot(1⨾0)$. 所以 `kJ` 排除了闭项自己的那一对 (`StrRel16Val.valLK` 在它的上升目标对上值是对的).
> 4. **(定理) `domKD₁`, `domKZ₁`; (约化) `obsKD`, `obsKZ`**: 变体 `kD` (只比差分量) 与 `kZ` (左边的累计 $\le$ 右边分支状态在第 $0$ 层的读数) 在 `rkAt` 那一对上成立, 所以 `RkSoundTK kD`, `RkSoundTK kZ` 都推出 `RkLeft tt ReL`.
> 5. **(否定, 定理, 值) `¬RkSoundTKD`**: `RkSoundTK kD hz (hs hz)` 不成立. `NegSR17RkT` 的反例 (产生时动作 `Az` 读累计, 产生状态 `YP`) 满足 `kD` (`domKD-P`: 差分量不被 `cv` 清掉), 值的不等式原样成立.
>
> **读法 (判断).** (a) 与 (c) 都只约束动作或状态, 第一个障碍 (`StrRel17Obs`: 右边在再折叠时保留的目标对上, `RelX⁺` 里 "… ≤ 节点" 只有字面的 `rk⁺`) 在结论关系的形状上, 三条修补都碰不到它 (第 2, 4 条). (c) 的三个变体分处三个位置: `kJ` 太强 (排除闭项的那一对), `kD` 太弱 (留下 `Az` 的反例), `kZ` 在两者之间 (含闭项的那一对; 是否排除 `Az` 的反例本文没有证, 判断: 反例的累计 $z_P$ 超过右边的读数 $\omega$, 应被排除).
>
> **只否定什么.** `¬domKJ`: 只说 `kJ` 在这一组参数上不成立. `¬RkSoundTKD`: 只否定变体 `kD` 下的 `RkSoundTK hz (hs hz)` 的字面陈述, 反例的产生时动作读累计. `obsZ`, `obsKD`, `obsKZ` 是约化, 不是否定 (`RkLeft tt ReL` 本文没有否定). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `preY₁` (`RkPre`, 同 `StrRel17Obs.obsRkT`), `noZΛ₂`, `domKD₁`, `domKZ₁`, `domKD-P`, `NegSR17RkT.preP`, `jYP` 都是定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel18Obs where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; ≤-refl; ≤-trans; ≤-suc; irr)
open import OCF.Align.HtFeedTree using (H; LgH; hz; hs; hself; hsuc; ss; z⊲ᴴ; StH; Vs; D; D₀; n0; n1; accL; AccY; sum; ⊲ᴴ↑)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
open import OCF.Align.StrRel14J Λ₂ tt using (here; left; rgt0)
open import OCF.Align.StrRel15Fin using (T₁; fin⊲; module FinΛ)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Lem using (module V0)
open import OCF.Align.StrRel16If Λ₂ tt using (RelX⁺; n0⁺; n1⁺; ⨾⁺; nl⁺; pr⁺)
open import OCF.Align.StrRel14If Λ₂ tt using (n1ˣ; n0ˣ)
open import OCF.Align.StrRel16Val using (OutL; OutR)
open import OCF.Align.StrRel17If Λ₂ tt using (DomL)
open import OCF.Align.StrRel17Obs using (ReL; RkLeft; invNi; pick; obsT)
open import OCF.Align.StrRel18If Λ₂ tt using (NoZ; SemTᶻ; RkSoundTᶻ; KSt; KV; kJ; kD; kZ; DomKv; RkSoundTK)
import OCF.Align.StrRel18If as If⁵
import OCF.Align.StrRel16If as If³

open Rk Λ₂ tt using (s∞; u∞)
open FinΛ Λ₂ tt tt using (hawAct²; hY₁)
open FinΛ⁺ Λ₂ tt tt using (hawAct²⁺; Y₁; hY₁⁺; ΩRX²⁺)
open V0 Λ₂ tt using (vsum⁺)
module P = At Λ₂ tt
open P using (Tg; tg; tm; τ₀; St; st; d; z; yc; Run; Act; Ig; LW; RKi; kk; rise; keep)
```

## 1 `KSt` 就是 `BNi` 的状态 (一切 $\Lambda$)

```agda
module Gen (Λ : H) (lΛ : LgH Λ) where
  open If³ Λ lΛ using () renaming (module P to Q)
  open If⁵ Λ lΛ using () renaming (KSt to KStΛ)

  chkKSt : ∀ {ly W₀ W k W₁} (ac : AccY ly) (ac₁ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′)
             (q₀ : W₀ ⊲ W) (ll : Q.LW ly W) (A₀ : Q.Ig ly W) (w : D ly W) (Y : Q.St W) (hk : Q.LW k W) (p : W ⊲ W₁) (lW₁ : Lg W₁) (y : D k W₁) →
           Q.BNi ac ac₁ r u q₀ ll A₀ w Y hk p lW₁ y ≡ Q.Ai ac ac₁ r u q₀ hk ll A₀ w p lW₁ y (KStΛ ac ac₁ r u q₀ ll A₀ w Y hk p lW₁ y)
  chkKSt ac ac₁ r u q₀ ll A₀ w Y hk p lW₁ y = refl
```

## 2 前提: `rkAt` 那一对

```agda
u₁ : ∀ {W₁} → azero ⊲ W₁ → Lg W₁ → Vs Λ₂ r₀ W₁ → D Λ₂ W₁
u₁ _ _ _ = n1

T₀ : Tg azero hz azero
T₀ = τ₀ tt

Y1 : St azero
Y1 = Y₁ tt

preY₁ : If³.RkPre Λ₂ tt {lW₀ = tt} {lW₀′ = tt} r₀ r₀ u₁ u₁ tt tt C.self C.self Act Act n0 n0 Y1 Y1
preY₁ = cp00 , (s∞ , ((λ p p′ lc lc′ cp y y′ b → n1ˣ) , (hawAct² Λ₂ Λ₂ , (n0ˣ , hY₁ tt tt))))

noZΛ₂ : ∀ {L W} (lW : Lg W) → NoZ {L} {W} lW Act
noZΛ₂ lW p lW₁ w Y z′ T = refl
```

## 3 (a): `obsZ`

```agda
obsTᶻ : SemTᶻ hz (hs hz) tt tt (DomL tt Y1) OutL OutR → RkLeft tt ReL
obsTᶻ s = pick (invNi (s tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 Act Act
                         (hawAct²⁺ hz (hs hz) , (noZΛ₂ tt , noZΛ₂ tt))
                         n0 n0 n0⁺ Y1 Y1 (hY₁⁺ tt tt) (hY₁⁺ tt tt) (τ₀ tt) T₁ (cp00 , u∞ s∞)))

obsZ : RkSoundTᶻ hz (hs hz) → RkLeft tt ReL
obsZ h = obsTᶻ (h r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Act Act n0 n0 Y1 Y1
                  T₀ T₁ (ss hself) preY₁ (cp00 , u∞ s∞) refl refl (noZΛ₂ tt) (noZΛ₂ tt))
```

## 4 (c): 三个变体在 `rkAt` 那一对上

```agda
-- kJ: 输入 n0 时, 右边分支运行的状态的累计是 n0 ⨾ n0, 支配不了 Y₁ 的累计 0 ⨾ ω⋅(1 ⨾ 0)
¬domKJ : ¬ DomKv kJ tt Y1 (accL Λ₂) (accL hz) r₀ u₁ C.self hself Act n0 Y1 T₁
¬domKJ h = irr azero (≤-trans (≤l 1 (≤-refl (asuc azero))) (vsum⁺ (proj₂ (proj₁ (h C.self tt n0))) (≤-refl azero)))

-- kD: 差分量成立
domKD₁ : DomKv kD tt Y1 (accL Λ₂) (accL hz) r₀ u₁ C.self hself Act n0 Y1 T₁
domKD₁ p lW₁ y =
  (λ T T′ tx → pr⁺ (⨾⁺ n0⁺ (nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺)))) ,
  ((λ T → n0 , rgt0 here) , (λ T → n0 , left (rgt0 here)))

-- kZ: 累计 ≤ 右边分支状态在第 0 层的读数
domKZ₁ : DomKv kZ tt Y1 (accL Λ₂) (accL hz) r₀ u₁ C.self hself Act n0 Y1 T₁
domKZ₁ p lW₁ y = pr⁺ (⨾⁺ n0⁺ (nl⁺ (λ _ → ⨾⁺ n1⁺ n0⁺)))

obsK : ∀ (v : KV) → DomKv v tt Y1 (accL Λ₂) (accL hz) r₀ u₁ C.self hself Act n0 Y1 T₁ → RkSoundTK v hz (hs hz) → RkLeft tt ReL
obsK v dom h =
  obsT (DomL tt Y1) (hY₁⁺ tt tt)
    (h r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Act Act n0 n0 Y1 Y1
       T₀ T₁ (ss hself) preY₁ (cp00 , u∞ s∞) refl refl dom)

obsKD : RkSoundTK kD hz (hs hz) → RkLeft tt ReL
obsKD = obsK kD domKD₁

obsKZ : RkSoundTK kZ hz (hs hz) → RkLeft tt ReL
obsKZ = obsK kZ domKZ₁
```

## 5 `kD` 留下 `NegSR17RkT` 的反例

```agda
open import OCF.Align.NegSR17Rk using (C1; hawC1⁺)
open import OCF.Align.NegSR17RkT using (Az; uN; rk1; YP; jYP; preP; RefR₀; RefRof; RefLP; zP; lowOL; sumDrp; sumLift; sum≈; refR≈; module RL)

domKD-P : DomKv kD tt YP (accL Λ₂) (accL hz) r₀ uN C.self hself Az n0 YP T₁
domKD-P p lW₁ y =
  (λ T T′ tx → pr⁺ (nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺))) ,
  ((λ T → n0 , here) , (λ T → n0 , left here))

relRefD : RkSoundTK kD hz (hs hz) → RelX⁺ hz hz tt tt RefLP (RefRof YP)
relRefD h =
  h r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Az Az n0 n0 YP YP (τ₀ tt) T₁ rk1 preP (cp00 , u∞ s∞) refl refl
    domKD-P
    tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 C1 C1 (hawC1⁺ hz (hs hz))
    n0 n0 n0⁺ YP YP jYP jYP (τ₀ tt) (τ₀ tt) (cp00 , s∞)

¬RkSoundTKD : ¬ RkSoundTK kD hz (hs hz)
¬RkSoundTKD h =
  irr (sum azero RefR₀)
    (≤-trans (s≤ (sumDrp RefR₀ azero))
    (≤-trans (sumLift zP azero)
    (≤-trans (≤-suc (≤-refl _))
    (≤-trans (lowOL azero)
    (≤-trans (RL.ge (accL hz) _ C.self (z⊲ᴴ Λ₂) n0 YP (τ₀ tt) azero)
    (≤-trans (vsum⁺ (relRefD h) (≤-refl azero))
             (sum≈ refR≈ azero)))))))
```
