# 第十八轮的否定 (二): 时间条件 (c) 的三个变体

> 不读记号. 入口 [NegSR18](NegSR18.lagda.md). 对着接口 [StrRel18If](StrRel18If.lagda.md) (定稿 2026-11-05 14:22) §2 的 `KSt`, `DomKv`, `RkSoundTK` 写. 实例 $\Lambda_2=2$ (没有 $\Omega$-极限), 沿用 [NegSR17RkT](NegSR17RkT.lagda.md) 的那一对: 节点 `r₀` (层 $2$, 坐标层 $0$, 分支 `n1`), 产生时的动作 `Az` (输出 "累计 ⨾ 1"), 产生状态 `YP` (差是 `dN`: 每个目标上读 $\omega\cdot(\Omega_t⨾0)$; 累计 $z_P$ 很大), 左在 $\tau_0$ 上升, 右在 $T_1$ 保留.
>
> 1. **(否定, 值) `¬RkSoundTK-kD`: `RkSoundTK kD hz (hs hz)` 不成立.** 只比差分量的变体 `kD` 在这一对上成立 (`dK`: `KSt` 的差是 `cv` 之后 `YP` 的读数再向右加一段, `pr⁺`), 而 `RkSoundTK` 的结论与 `RkSoundT` 相同, 所以 `NegSR17RkT` 的值的反例原样适用 (再折叠: 两边都以 `YP`, 动作 `C1`, 时间条件 `DomL` 由 `jYP` 给出).
> 2. **(定理) `¬domKJ`, `¬domKJ-Y₁`**: 变体 `kJ` (`J²⁺ Y (KSt …)`, 对一切输入 $y$) 推出 "产生时的累计 `RelX⁺ hz hz` 低于 `n0 ⨾ n0`": 取 $y=$ `n0`, 这时 `KSt` 的累计字面地是 `n0 ⨾ n0` (`cv` 清零, 再加 `Run n0` 的输出 `n0`). 闭项的状态 $Y_1=Y_0\oplus\mathrm{Step}\,Y_0$ 的累计是 `n0 ⨾ ω⋅(1⨾0)`, 不低于 `n0 ⨾ n0` (`¬low00`), 所以 **`kJ` 在 $Y_1$ 上对一切右边的节点都不成立** (`¬domKJ-Y₁`).
> 3. **(定理) `kJ0`, `¬kJ⊕`**: `kJ` 可满足 (累计为 `n0` 的 `Y0`, `kJ0`), 但不对 `⊕` 封闭: `Y0 ⊕ Step Y0` 不满足 (`¬kJ⊕`).
> 4. **(定理, 正面) `kZY₁`**: 变体 `kZ` 在闭项的状态 $Y_1$ 上成立 (`rkAt` 那一对的右边): $Y_1$ 的累计与它在第 $0$ 层目标上的读数字面相同.
>
> **构造一路为什么需要这些.** `RkSoundTK v` 是 (c) 修补后的 `rk⁺` 可靠性 (接口 §2). 构造一路要在折叠里用它, 就要 (一) 它成立, (二) 它的前提 `DomKv v` 能从折叠的字面关系得到. 第 1 条否定 (一) 对 `kD`. 第 2, 3 条说 `kJ` 的前提在闭项的状态 $Y_1$ 上不成立, 且不经 `⊕` 传下去; 折叠里的产生状态都由 `⊕` (`Rpt`, `Chn`) 从更早的状态延长而来, 累计一旦非零 (第一段输出在第 $0$ 层目标上非零) 就失去 `kJ`. 所以 `RkSoundTK kJ` 在折叠里只能用在累计为零的状态上.
>
> **只否定什么.** 第 1 条只否定 `RkSoundTK kD hz (hs hz)` (产生时动作取遍旧 `HAW²`, 不限 `NoZ`; 反例的 `Az` 读累计). 第 2, 3 条不否定 `RkSoundTK kJ` 本身 (它可能成立, 本文没有比较值), 只说它的前提的范围. **`kZ` 没有否定**: 它要求产生时的累计被 `KSt` 在第 $0$ 层目标上的**读数**支配, 读数就是产生状态的差 (经 `cv`) 再加一段; 再折叠的时间条件 `DomL` 又要求再折叠状态的差支配产生状态的差. 判断 (未编译): `Az` 的机制在这里两边对称 (左边读到的累计, 右边在再折叠时从差里读到), 本文的构造给不出反例. 闭项的状态 $Y_1$ 满足 `kZ` (第 4 条, 定理). `kZ` 对 `cv` (产生状态的累计变成 `n0`, `n0⁺`) 显然封闭; 对 `⊕` 的封闭要第 $0$ 层目标上运行输出在不同世界的目标上互相 `RelX⁺` (判断: 第 $0$ 层的输出只经 `RKy` 的 `hz` 句与动作的读数依赖目标, 很可能成立; 未编译). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** 第 1 条: `NegSR17RkT.preP` (`RkPre`), `TX` 对 `(cp00 , u∞ s∞)`, 种类 `refl`, `dK` (`DomKv kD`), 再折叠一侧 `cp00`, `hawC1⁺`, `n0⁺`, `jYP` (两次: 状态关系与时间条件), 目标对 `(cp00 , s∞)`; 全部是定理. 第 2 条的结论是 "前提不成立", 它对一切右边的节点参数成立; 第 3 条的 `kJ0` 是可满足的见证.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR18K where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤-refl; ≤-trans; ≤-suc; irr)
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; z⊲ᴴ; StH; Vs; D; D₀; n0; n1; _⨾_; nl; accL; AccY; sum)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14J as J14

open import OCF.Align.StrRel15Fin using (fin⊲; T₁)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Lem using (module V0)
open import OCF.Align.StrRel16If Λ₂ tt
open import OCF.Align.NegSR17Rk using (C1; hawC1⁺; module RK)
open import OCF.Align.NegSR17RkT using (Az; uN; rk1; OLof; RefRof; RefR₀; zP; YP; Ys; refR≈; jYP; preP; lowOL; RefLP; sum≈; sumDrp; sumLift)
open import OCF.Align.StrRel18If Λ₂ tt using (KSt; KV; kJ; kD; kZ; DomKv; RkSoundTK)

open Rk Λ₂ tt using (s∞; u∞)
open FinΛ⁺ Λ₂ tt tt using (ΩRX²⁺; Y₁)
open V0 Λ₂ tt using (vsum⁺)
open P using (Tg; tg; wm; tm; lm; τ₀; St; st; Df; d; z; yc; Step; _⊕⟨_⟩_; Ig; LW)
```

## 1 `kD` 在 `NegSR17RkT` 的那一对上成立, `RkSoundTK kD` 不成立

```agda
-- 差为 dN 的状态都满足 NE
neN : ∀ {W} (zz : D₀ W) → J14.NE Λ₂ tt (Ys zz)
neN zz T = n0 , J14.here

-- 只比差分量: KSt 的差是 cv 之后的读数再向右加一段
dK : DomKv kD tt YP (accL Λ₂) (accL hz) r₀ uN C.self hself Az n0 YP T₁
dK p lW₁ y =
  (λ T T′ tx → pr⁺ (nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺))) ,
  (neN zP , (λ T → n0 , J14.left J14.here))

module RL = RK {azero} tt C1 (λ w Y T → refl)

relRefK : RkSoundTK kD hz (hs hz) → RelX⁺ hz hz tt tt RefLP (RefRof YP)
relRefK h =
  h r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Az Az n0 n0 YP YP (τ₀ tt) T₁ rk1 preP (cp00 , u∞ s∞) refl refl dK
    tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 C1 C1 (hawC1⁺ hz (hs hz))
    n0 n0 n0⁺ YP YP jYP jYP (τ₀ tt) (τ₀ tt) (cp00 , s∞)

¬RkSoundTK-kD : ¬ RkSoundTK kD hz (hs hz)
¬RkSoundTK-kD h =
  irr (sum azero RefR₀)
    (≤-trans (s≤ (sumDrp RefR₀ azero))
    (≤-trans (sumLift zP azero)
    (≤-trans (≤-suc (≤-refl _))
    (≤-trans (lowOL azero)
    (≤-trans (RL.ge (accL hz) (OLof YP) C.self (z⊲ᴴ Λ₂) n0 YP (τ₀ tt) azero)
    (≤-trans (vsum⁺ (relRefK h) (≤-refl azero))
             (sum≈ refR≈ azero)))))))
```

## 2 `kJ` 推出 "产生时的累计低于 `n0 ⨾ n0`"

```agda
-- 第 0 层: ω 次和不低于 n0; 以它结尾的树也不
¬nl0 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {e : ℕ → D₀ V} → ¬ RelX⁺ hz hz lV lV′ (nl e) (n0 {W = V′})
¬nl0 (in⁺ h here) = ¬nl0 h

¬nlP : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {e : ℕ → D₀ V} → ¬ RelX⁺ hz hz lV lV′ (n0 ⨾ nl e) (n0 {W = V′})
¬nlP (in⁺ h here) = ¬nlP h

¬low00 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {e : ℕ → D₀ V} → ¬ RelX⁺ hz hz lV lV′ (n0 ⨾ nl e) (n0 {W = V′} ⨾ n0)
¬low00 (⨾⁺ h₁ h₂) = ¬nl0 h₂
¬low00 (pr⁺ h) = ¬nlP h
¬low00 (in⁺ h here) = ¬low00 h
¬low00 (in⁺ h (inL here)) = ¬nlP h
¬low00 (in⁺ h (inR here)) = ¬nlP h

-- kJ 在输入 y = n0 上: KSt 的累计字面是 n0 ⨾ n0
domKJ→low : ∀ {W ly′ W₀′ W′ k′ t′ m′} {lW : Lg W} {Y : St W} {ac′ : AccY ly′} {ac₁′ : AccY k′} {r′ : StH W₀′ k′ ly′}
              {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁} {q₀′ : W₀′ ⊲ W′} {ll′ : LW ly′ W′} {A₀′ : Ig ly′ W′}
              {w′ : D ly′ W′} {Y′ : St W′} (T′ : Tg W′ t′ m′) →
            DomKv kJ lW Y ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′ → RelX⁺ hz hz lW (lm T′) (z Y) (n0 {W = m′} ⨾ n0)
domKJ→low T′ h = proj₂ (proj₁ (h C.self (lm T′) n0))

¬domKJ : ∀ {W ly′ W₀′ W′ k′ t′ m′} {lW : Lg W} {Y : St W} {e : ℕ → D₀ W} (ac′ : AccY ly′) (ac₁′ : AccY k′) (r′ : StH W₀′ k′ ly′)
           (u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁) (q₀′ : W₀′ ⊲ W′) (ll′ : LW ly′ W′) (A₀′ : Ig ly′ W′)
           (w′ : D ly′ W′) (Y′ : St W′) (T′ : Tg W′ t′ m′) →
         z Y ≡ n0 ⨾ nl e → ¬ DomKv kJ lW Y ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′
¬domKJ {lW = lW} {Y = Y} ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′ eq h =
  ¬low00 (subst (λ x → RelX⁺ hz hz lW (lm T′) x (n0 ⨾ n0)) eq (domKJ→low T′ h))

-- 闭项的状态 Y₁ = Y₀ ⊕ Step Y₀: 对一切右边的节点, kJ 都不成立
¬domKJ-Y₁ : ∀ {ly′ W₀′ W′ k′ t′ m′} (ac′ : AccY ly′) (ac₁′ : AccY k′) (r′ : StH W₀′ k′ ly′)
              (u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁) (q₀′ : W₀′ ⊲ W′) (ll′ : LW ly′ W′) (A₀′ : Ig ly′ W′)
              (w′ : D ly′ W′) (Y′ : St W′) (T′ : Tg W′ t′ m′) →
            ¬ DomKv kJ tt (Y₁ {azero} tt) ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′
¬domKJ-Y₁ ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′ = ¬domKJ ac′ ac₁′ r′ u′ q₀′ ll′ A₀′ w′ Y′ T′ refl
```

## 3 `kJ` 可满足, 但不对 `⊕` 封闭

```agda
Y0 : St azero
Y0 = Ys n0

-- 累计为 n0 的 Y0 满足 kJ (右边: 同一节点, 同一状态)
kJ0 : DomKv kJ tt Y0 (accL Λ₂) (accL hz) r₀ uN C.self hself Az n0 Y0 T₁
kJ0 p lW₁ y =
  ((λ T T′ tx → pr⁺ (nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺))) , n0⁺) ,
  (neN n0 , (λ T → n0 , J14.left J14.here))

-- 向右加一段 Step Y0 之后, kJ 不再成立 (对同一个右边)
¬kJ⊕ : ¬ DomKv kJ tt (Y0 ⊕⟨ tt ⟩ Step Y0) (accL Λ₂) (accL hz) r₀ uN C.self hself Az n0 Y0 T₁
¬kJ⊕ = ¬domKJ (accL Λ₂) (accL hz) r₀ uN C.self hself Az n0 Y0 T₁ refl
```

## 4 (正面) `kZ` 在闭项的状态 $Y_1$ 上成立

`StrRel16Kr.rkAt` 那一对 (节点 `r₀`, 分支 `n1`, 动作 `Act`, 状态 $Y_1$): $Y_1$ 的累计与它在第 $0$ 层目标上的读数字面相同 (`n0 ⨾ ω⋅(1⨾0)`), `KSt` 的读数是它再向右加一段, 所以 `kZ` 由 `pr⁺` 给出. 与第 2 条对照: 同一个状态, `kJ` 不成立, `kZ` 成立.

```agda
kZY₁ : DomKv kZ tt (Y₁ {azero} tt) (accL Λ₂) (accL hz) r₀ (λ _ _ _ → n1) C.self hself P.Act n0 (Y₁ tt) T₁
kZY₁ p lW₁ y = pr⁺ (⨾⁺ n0⁺ (nl⁺ (λ _ → ⨾⁺ n1⁺ n0⁺)))
```
