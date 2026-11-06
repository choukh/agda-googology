# 第十八轮的否定 (四): 限制 (a) 下 `rk⁺` 的那一对: 累计经分支里的 `nκ` 被读, 时间条件是挡住它的唯一一环

> 不读记号. 入口 [NegSR18](NegSR18.lagda.md). 对着接口 [StrRel18If](StrRel18If.lagda.md) (定稿 2026-11-05 14:22) §1 的 `NoZ`, `HAWᶻ`, `SemTᶻ`, `RkSoundTᶻ` 写. 实例 $\Lambda_2=2$.
>
> 设定: 节点 `r₀` (层 $2$, 坐标层 $0$), **分支是 `nκ`** (`uK`, 每个值 `n1`; 层 $2$ 不是零层, `nκ` 是合法的树), 产生时两边的动作都是常数 `C1` (满足 `NoZ`, `noZC1`), 上下文 `n0`; 产生状态 `YP` (差是 `dN`, 累计 $z_P$). 左在 $\tau_0$ 上升 (`OLof`), 右在 $T_1$ 保留 (`ORof`). `RkPre` 全部成立 (`preK`, 旧关系; 分支对 `κˣ`).
>
> 1. **(定理, 值) `lowAi`, `lowL`**: 左边链的第一段的第一个 `n1` 调用分支动作 `Ai`, 分支的 `nκ` 在第 $0$ 层目标上回灌, 第 $0$ 格从世界 $0$ 走到 $\Sigma z_P$ (`NegSR18Walk.walkLow`), 所以左边 (以及它以**任意**状态、动作 `C1` 的再折叠) 的值 $\ge\Sigma z_P$. 产生时的动作不读累计, 读累计的是分支里的 `nκ`.
> 2. **(定理) `orEq`**: 右边的保留输出不依赖产生时的累计 (`refl`; `BNi` 先 `cv`). 取 $z_P$ 为 "右边以累计为 `n0` 的 `Y0` 再折叠的值 $+1$" (不循环).
> 3. **(否定, 值) `¬RkSoundᶻ-Any`**: 去掉时间条件的 (a) 版本 `RkSoundᶻ-Any` (下面定义: `RkSoundTᶻ` 的 `DomL` 换成恒真的 `Any`) 不成立: 两边都以 `Y0` (累计 `n0`, 正是 `cv` 之后的状态) 再折叠, 左 $>$ 右 (`¬relGap`).
> 4. **(定理) `¬domY0`**: 这个再折叠正是被时间条件 `DomL` 挡住的: `J²⁺ YP Y0` 不成立 (累计 $z_P\not\le$ `n0`).
> 5. **(定理) `keptK`, `brK`**: 右边的保留输出是一个节点, 它的分支**字面地**是 `n0 ⨾ nκ tt κ1`, 不依赖产生状态 (连差也不依赖): 原分支里的 `nκ` 原样留在保留输出的分支里. 所以右边再折叠时, 这个 `nκ` 在再折叠状态上回灌, 读再折叠状态的累计.
>
> **读法 (判断, 依据第 1–5 条).** 限制 (a) 管不到分支里的 `nκ` (第 1 条; `NegSR18Ai` 是同一机制在 $\Omega$-极限处的节点上). 对 `RkSoundTᶻ` (时间条件 `DomL` 保留) 本文**没有**找到值的反例: 第 5 条说保留输出把 `nκ` 带到再折叠里, `DomL` 要求再折叠状态的累计支配 $z_P$, 两边读到的累计对称. 所以在 (a) 下, 挡住 `cv` 机制的是时间条件 `DomL`, 而不是 (a); 而 `DomL` 在经过 `cv` 的再折叠上不成立 (`NegSR17Time.¬domCv`). 不带时间条件时 (a) 不够 (第 3 条).
>
> **构造一路为什么需要这些.** 作者选的 B1 修补是 (a) 加 (c). 第 3 条说 (a) 不能代替时间条件; 第 1, 5 条说明 `RkSoundTᶻ` 若成立, 靠的是 `DomL`, 而构造一路要在 `cv` 之后的再折叠里用它 (`BNi`, `Kp`, `Kb`, `κc` 都先 `cv`), 那里 `DomL` 不成立 (第 4 条是本实例上的形式).
>
> **只否定什么.** 只否定 `RkSoundᶻ-Any hz (hs hz)` (本文定义的变体, 不是接口的律). **不否定接口的 `RkSoundTᶻ`.** 不涉及右边保留的再折叠目标对 (`StrRel17Obs` 的障碍). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `preK` (`RkPre`: `cp00`, `s∞`, 分支 `κˣ`, `hawC1`, `n0ˣ`, `hYP`), `TX` 对 `(cp00 , u∞ s∞)`, 种类 `refl` (`kL`, `kR`), `noZC1` 两次; 再折叠一侧 `cp00`, `(hawC1⁺ , noZC1 , noZC1)`, `n0⁺`, `jY0`, 条件 `tt`, 目标对 `(cp00 , s∞)`. 全部是定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR18Z where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; irr)
open import OCF.Align.HtFeedTree using (H; Vs; outS; ⊲ᴴ↑; hz; hs; hself; hsuc; ss; z⊲ᴴ; StH; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; Ωd; accL; AccY; sum; pt; drp)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel14J as J14
import OCF.Align.StrRel15If as If²
open import OCF.Align.StrRel15Fin using (fin⊲; T₁; module FinΛ)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Lem using (sum-mono; module V0; inSum)
open import OCF.Align.StrRel16If Λ₂ tt
open import OCF.Align.StrRel17If Λ₂ tt using (Cond; Any; DomL)
open import OCF.Align.StrRel18If Λ₂ tt using (NoZ; HAWᶻ; SemTᶻ)
open import OCF.Align.NegSR17Rk using (C1; hawC1; hawC1⁺; module RK)
open import OCF.Align.NegSR17RkT using (Ys; rk1; sumDrp; reflDrp)
open import OCF.Align.NegSR18Walk using (module WL)

open Rk Λ₂ tt using (s∞; u∞)
open If Λ₂ tt using (RelX; n0ˣ; n1ˣ; ⨾ˣ; nlˣ; κˣ)
open If² Λ₂ tt using (J²; HAW²; TX)
open FinΛ Λ₂ tt tt using (ΩRX²)
open FinΛ⁺ Λ₂ tt tt using (ΩRX²⁺)
open V0 Λ₂ tt using (vsum⁺)
open WL Λ₂ tt using (κ1; walkLow)
open P using (Tg; tg; wm; tm; lm; τ₀; St; st; Df; df; yc; d; z; Run; Ig; Ai; Chn; LW; RKi; rise; keep; kk; _⊕⟨_⟩_; κΔ; κc; lv; rkT)
```

## 1 实例与左边的下界

```agda
-- C1 不读累计
noZC1 : ∀ {L W} (lW : Lg W) → NoZ {L} {W} lW C1
noZC1 lW p lW₁ w Y z′ T = refl

-- 分支含 nκ 的节点 r₀ (层 2, 坐标层 0); 产生时动作 C1 (不读状态)
uK : ∀ {W₁} → azero ⊲ W₁ → Lg W₁ → Vs Λ₂ r₀ W₁ → D Λ₂ W₁
uK _ _ _ = nκ tt κ1

hk : LW hz azero
hk = kk r₀ C.self hself

OLof : St azero → D hz azero
OLof Y = RKi (accL Λ₂) (accL hz) r₀ uK C.self tt hself C1 n0 Y (τ₀ tt) rise

ORof : St azero → D (hs hz) azero
ORof Y = RKi (accL Λ₂) (accL hz) r₀ uK C.self tt hself C1 n0 Y T₁ (keep rk1)

Y0 : St azero
Y0 = Ys n0

-- 右边以 Y0 (累计 n0) 再折叠
RefR : D₀ azero
RefR = yc (Run (accL (hs hz)) (ORof Y0) C.self tt (hsuc hself) C1 n0 Y0) (τ₀ tt)

zP : D₀ azero
zP = drp RefR ⨾ n1

YP : St azero
YP = Ys zP

orEq : ORof YP ≡ ORof Y0
orEq = refl

-- 左边: 链的第 0 段的第一个 n1 调用分支动作, 分支是 nκ, 回灌的第 0 格从 0 走到 Σ zP
AiOut : St azero → D₀ azero
AiOut Y = yc (Ai (accL Λ₂) (accL hz) r₀ uK C.self hk hself C1 n0 C.self tt n0 Y) (τ₀ tt)

inAi : In (AiOut YP) (OLof YP)
inAi = inE 0 (inE 0 (inL here))

llK : LW Λ₂ azero
llK = ⊲ᴴ↑ C.self hself

c0 : P.Cl azero azero Λ₂
c0 = κc (accL Λ₂) κ1 C.self tt llK (P.Ig↾ C.self C1) (nw C.self n0 ⨾ n0) YP 0

cell0 : D₀ (P.v c0)
cell0 = yc (κΔ (accL Λ₂) κ1 llK (P.Ig↾ C.self C1) c0) (τ₀ (lv c0))

lowCell : sum azero zP ≤ sum azero cell0
lowCell = walkLow (accL Λ₂) (P.v c0) (P.av c0) (P.ap c0) (lv c0) C.self (lv c0) (⊲ᴴ↑ (P.wv c0) llK) (P.Ig↾ (P.wv c0) (P.Ig↾ C.self C1))
            (P.co c0) (P.Sv c0) (λ w Y′ β → ≤-refl (asuc β)) azero z≤

lowAi : asuc (sum azero RefR) ≤ sum azero (AiOut YP)
lowAi = ≤l 1 (≤-trans (s≤ (sumDrp RefR azero)) (≤-trans lowCell (sumDrp cell0 azero)))

```

## 2′ 左边的再折叠与值的缺口

```agda
-- 左边以任意状态、C1 再折叠: 值不小于 OLof YP 的值
module RL = RK {azero} tt C1 (λ w Y T → refl)

LRef : St azero → D₀ azero
LRef Y₂ = yc (Run (accL hz) (OLof YP) C.self tt (z⊲ᴴ Λ₂) C1 n0 Y₂) (τ₀ tt)

lowL : ∀ Y₂ → asuc (sum azero RefR) ≤ sum azero (LRef Y₂)
lowL Y₂ = ≤-trans lowAi (≤-trans (inSum Λ₂ tt inAi azero) (RL.ge (accL hz) (OLof YP) C.self (z⊲ᴴ Λ₂) n0 Y₂ (τ₀ tt) azero))

gap : ∀ Y₂ → ¬ (sum azero (LRef Y₂) ≤ sum azero RefR)
gap Y₂ h = irr (sum azero RefR) (≤-trans (lowL Y₂) h)

¬relGap : ∀ Y₂ → ¬ RelX⁺ hz hz tt tt (LRef Y₂) RefR
¬relGap Y₂ r = gap Y₂ (vsum⁺ r (≤-refl azero))

```

## 2 前提

```agda
-- 前提 (旧关系)
hYP : J² {azero} {azero} tt tt YP YP
hYP = ((λ T T′ tx → nlˣ (λ _ → ⨾ˣ (ΩRX² (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0ˣ)) , ⨾ˣ (reflDrp RefR) n1ˣ) ,
      ((λ T → n0 , J14.here) , (λ T → n0 , J14.here))

preK : RkPre {lW₀ = tt} {lW₀′ = tt} r₀ r₀ uK uK tt tt C.self C.self C1 C1 n0 n0 YP YP
preK = cp00 , s∞ , (λ p p′ lc lc′ cp y y′ b → κˣ (λ _ _ _ _ _ → n1ˣ)) , hawC1 Λ₂ Λ₂ , n0ˣ , hYP

kL : P.rkT (⊲ᴴ↑ (wm (τ₀ {azero} tt)) hk) (tm (τ₀ {azero} tt)) tt ≡ rise
kL = refl

kR : P.rkT (⊲ᴴ↑ (wm T₁) hk) (tm T₁) (P.lm T₁) ≡ keep rk1
kR = refl

-- 右边的再折叠状态 Y0 满足 J²⁺ (与左边的再折叠状态 Y0)
jY0 : J²⁺ {azero} {azero} tt tt Y0 Y0
jY0 = ((λ T T′ tx → nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺)) , n0⁺) ,
      ((λ T → n0 , J14.here) , (λ T → n0 , J14.here))

```

## 3 去掉时间条件的 (a) 版本不成立

`RkSoundᶻ-Any`: 接口 `RkSoundTᶻ` 的结论里把时间条件 `DomL lW Y` 换成恒真的 `Any` (本文的变体, 不进接口).

```agda
RkSoundᶻ-Any : H → H → Set
RkSoundᶻ-Any L L′ =
  ∀ {ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
    (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
    (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
    (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) (R′ : StH m′ k′ L′) →
  RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ keep R′ →
  NoZ lW A₀ → NoZ lW′ A₀′ →
  SemTᶻ L L′ (lm T) (lm T′) Any
    (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ (keep R′))

¬RkSoundᶻ-Any : ¬ RkSoundᶻ-Any hz (hs hz)
¬RkSoundᶻ-Any h =
  ¬relGap Y0
    (h r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself C1 C1 n0 n0 YP YP (τ₀ tt) T₁ rk1 preK (cp00 , u∞ s∞)
       kL kR (noZC1 tt) (noZC1 tt)
       tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 C1 C1 (hawC1⁺ hz (hs hz) , (noZC1 tt , noZC1 tt))
       n0 n0 n0⁺ Y0 Y0 jY0 tt (τ₀ tt) (τ₀ tt) (cp00 , s∞))
```

## 4 时间条件挡住的正是这一步

```agda
¬⨾≤0 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {a b : D₀ V} → ¬ RelX⁺ hz hz lV lV′ (a ⨾ b) (n0 {W = V′})
¬⨾≤0 (in⁺ h here) = ¬⨾≤0 h

¬domY0 : ¬ DomL tt YP {azero} {azero} tt tt Y0 Y0
¬domY0 ((_ , rz) , _) = ¬⨾≤0 rz
```

## 5 保留输出的分支: 原分支里的 `nκ` 原样留下

```agda
BRK : St azero → ∀ {W′} → azero ⊲ W′ → Lg W′ → Vs (hs hz) rk1 W′ → D (hs hz) W′
BRK Y p lW′ y = yc (P.BNi (accL Λ₂) (accL hz) r₀ uK C.self hself C1 n0 Y (kk r₀ C.self hself) (⊲-tr (wm T₁) p) lW′ (outS rk1 y))
                   (tg C.self (⊲ᴴ↑ p (tm T₁)) lW′)

keptK : ∀ (Y : St azero) → ORof Y ≡ ni rk1 (BRK Y)
keptK Y = refl

brK : ∀ (Y : St azero) {W′} (p : azero ⊲ W′) (l : Lg W′) y → BRK Y p l y ≡ n0 ⨾ nκ tt κ1
brK Y p l y = refl
```
