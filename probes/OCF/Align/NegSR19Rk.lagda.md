# 第十九轮的否定 (二): 产生时动作限为 `ActS` 挡不住 `cv` 的机制; 挡住它的只有时间条件 `DomZ`

> 不读记号. 入口 [NegSR19](NegSR19.lagda.md). 对着接口 [StrRel19If](StrRel19If.lagda.md) (定稿 2026-11-05 16:01) §3–§5 的 `HAWS`, `SemS`, `DomZ`, `RkSoundZ` 写. 实例 $\Lambda_2=2$.
>
> 设定 (同 `NegSR18Z`, 只把产生时的常数动作 `C1` 换成闭项的动作 `Act`, 它属于 `ActS`): 节点 `r₀` (层 $2$, 坐标层 $0$), 分支是 `nκ` (每个值 `n1`), 产生时两边的动作都是 `Act` (`sAct`), 上下文 `n0`, 产生状态 $Y_P$ (差 `dN`, 累计 $z_P$). 左在 $\tau_0$ 上升, 右在 $T_1$ 保留. 再折叠两边都用 `Act` (`HAWS`), 状态都是 $Y_0$ (差 `dN`, 累计 `n0`, 即 `cv` 之后的状态的样子).
>
> 1. **(定理, 值) `lowAi`, `lowL`**: 左边的链的第一个 `n1` 调用分支动作, 分支的 `nκ` 在第 $0$ 层目标上回灌, 第 $0$ 格从世界 $0$ 走到 $\Sigma z_P$, 所以左边以 $Y_0$, `Act` 再折叠的值 $>\Sigma\,\mathrm{RefR}$.
> 2. **(定理) `orEq`**: 右边的保留输出不依赖产生时的累计 (`refl`, `BNi` 先 `cv`, `Act` 只读差). $z_P$ 取 "右边以 $Y_0$, `Act` 再折叠的值 `RefR`" 之上 (不循环).
> 3. **(否定, 值) `¬RkSoundS-Any`**: 去掉时间条件的 `RkSoundZ` (下面定义的 `RkSoundS-Any`, 结论的条件取恒真的 `Any`) 不成立, 产生时两边动作都是 `ActS`.
> 4. **(定理) `¬domZ-Y0`**: 这一次再折叠正是 `DomZ` 挡住的: $z_P$ 的和大于 $Y_0$ 在 $\tau_0$ 上的读数 $\omega\cdot(1⨾0)$ 的和, `DomZ YP` 在 $(Y_0,Y_0)$ 上不成立.
>
> **读法 (判断, 依据第 1–4 条).** 接口 "范围 (iii)" 说 `up` 要 `ActS` 是为了排除读累计的 `Az`. `ActS` 的确排除 `Az` (`NegSR19Good.¬ActS-Az`), 但排除不了 "产生时读累计": 读累计的是分支里的 `nκ`, 不是动作 (`NegSR19Act`: `ActS` 里有读累计的动作). 所以在 `RkSoundZ` 里, 与 `NegSR18Z` 对 `RkSoundTᶻ` 一样, 挡住 `cv` 机制的只有时间条件 (这里是 `DomZ`), 不是动作的限制. `DomZ` 只要求再折叠状态的第 $0$ 层**读数**支配 $z_P$, 而读数经 `cv` 保留; 本文对带 `DomZ` 的 `RkSoundZ` 没有找到值的反例 (判断: `DomZ` 下右边的链从读数起, `Act` 每次也读这个读数, 读到的不少于 $z_P$; 未比较值).
>
> **构造一路为什么需要这些.** `RkSoundZ` 是接口 §5 为 `rk⁺⁺` 写的可靠性, 产生时动作限为 `ActS`. 第 3 条说: 证明它时 `DomZ` 是必须用到的前提 (动作限制单独不够), 并且必须用到它的累计分量 (`¬domZ-Y0`: 本反例的再折叠满足 `DomZ` 的差分量与 `NE`, 只违反累计分量).
>
> **只否定什么.** 只否定 `RkSoundS-Any hz (hs hz)` (本文的变体, 不是接口的律). **不否定接口的 `RkSoundZ`.** `up` 的同一机制见 [NegSR19Up](NegSR19Up.lagda.md) (`¬UpSoundS-Any`). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `preK` (`RkPre`, 旧关系: `cp00`, `s∞`, 分支 `κˣ`, `hawAct²`, `n0ˣ`, `hYP`), `TX` 对 `(cp00 , u∞ s∞)`, 种类 `refl`/`refl`, `sAct`/`sAct`; 再折叠一侧 `cp00`, `hawS hz (hs hz)`, `n0⁺⁺`, `jYs⁺⁺ n0⁺⁺`, 条件 `tt`, 目标对 `(cp00 , s∞)`. 全部是定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR19Rk where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; ≤-refl; ≤-trans; irr; ⊲→≤)
open import OCF.Align.HtFeedTree using (H; Vs; hz; hs; hself; hsuc; z⊲ᴴ; StH; D; D₀; n0; n1; _⨾_; nl; nκ; nw; accL; AccY; sum; sum-fst; drp; ⊲ᴴ↑)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel14J as J14
import OCF.Align.StrRel15If as If²
open import OCF.Align.StrRel15Fin using (fin⊲; T₁; module FinΛ)
open import OCF.Align.StrRel16Lem using (sum-mono; inSum)
open import OCF.Align.StrRel16If Λ₂ tt using (module P; RkPre; In; here; inL; inR; inE)
open import OCF.Align.StrRel17If Λ₂ tt using (Cond; Any)
open import OCF.Align.StrRel19If Λ₂ tt
open import OCF.Align.NegSR17RkT using (rk1; sumDrp; reflDrp)
open import OCF.Align.NegSR18Walk using (module WL)
open import OCF.Align.NegSR19Lem using (module V0⁺⁺; module Fin⁺⁺; module RKA)

open Rk Λ₂ tt using (s∞; u∞)
open If Λ₂ tt using (RelX; n0ˣ; n1ˣ; ⨾ˣ; nlˣ; κˣ)
open If² Λ₂ tt using (J²; TX)
open FinΛ Λ₂ tt tt using (ΩRX²; hawAct²)
open V0⁺⁺ Λ₂ tt using (vsum⁺⁺)
open Fin⁺⁺ Λ₂ tt tt using (hawS; jYs⁺⁺; Ys; dN)
open WL Λ₂ tt using (κ1; walkLow; hAct)
open P using (Tg; tg; wm; tm; lm; τ₀; St; yc; d; z; Run; Ig; Ai; LW; RKi; rise; keep; kk; κΔ; κc; lv; rkT)
```

## 1 实例

```agda
-- 分支含 nκ 的节点 r₀ (层 2, 坐标层 0); 产生时动作 Act (ActS)
uK : ∀ {W₁} → azero ⊲ W₁ → Lg W₁ → Vs Λ₂ r₀ W₁ → D Λ₂ W₁
uK _ _ _ = nκ tt κ1

hk : LW hz azero
hk = kk r₀ C.self hself

OLof : St azero → D hz azero
OLof Y = RKi (accL Λ₂) (accL hz) r₀ uK C.self tt hself P.Act n0 Y (τ₀ tt) rise

ORof : St azero → D (hs hz) azero
ORof Y = RKi (accL Λ₂) (accL hz) r₀ uK C.self tt hself P.Act n0 Y T₁ (keep rk1)

Y0 : St azero
Y0 = Ys n0

-- 右边以 Y0 (累计 n0), Act 再折叠
RefR : D₀ azero
RefR = yc (Run (accL (hs hz)) (ORof Y0) C.self tt (hsuc hself) P.Act n0 Y0) (τ₀ tt)

-- Y0 在 τ₀ 上的读数
ωR : D₀ azero
ωR = nl (λ _ → n1 ⨾ n0)

zP : D₀ azero
zP = drp RefR ⨾ (ωR ⨾ n1)

YP : St azero
YP = Ys zP

orEq : ORof YP ≡ ORof Y0
orEq = refl

zBig : asuc (sum azero RefR) ≤ sum azero zP
zBig = s≤ (≤-trans (sumDrp RefR azero) (⊲→≤ (sum-fst _ ωR)))

zBigω : asuc (sum azero ωR) ≤ sum azero zP
zBigω = s≤ (sum-mono ωR z≤)
```

## 2 左边的下界

```agda
AiOut : St azero → D₀ azero
AiOut Y = yc (Ai (accL Λ₂) (accL hz) r₀ uK C.self hk hself P.Act n0 C.self tt n0 Y) (τ₀ tt)

inAi : In (AiOut YP) (OLof YP)
inAi = inE 0 (inE 0 (inL here))

llK : LW Λ₂ azero
llK = ⊲ᴴ↑ C.self hself

c0 : P.Cl azero azero Λ₂
c0 = κc (accL Λ₂) κ1 C.self tt llK (P.Ig↾ C.self P.Act) (nw C.self n0 ⨾ n0) YP 0

cell0 : D₀ (P.v c0)
cell0 = yc (κΔ (accL Λ₂) κ1 llK (P.Ig↾ C.self P.Act) c0) (τ₀ (lv c0))

lowCell : sum azero zP ≤ sum azero cell0
lowCell = walkLow (accL Λ₂) (P.v c0) (P.av c0) (P.ap c0) (lv c0) C.self (lv c0) (⊲ᴴ↑ (P.wv c0) llK) (P.Ig↾ (P.wv c0) (P.Ig↾ C.self P.Act))
            (P.co c0) (P.Sv c0) (λ w Y′ β → hAct (lv c0) w Y′ β) azero z≤

lowAi : asuc (sum azero RefR) ≤ sum azero (AiOut YP)
lowAi = ≤l 1 (≤-trans zBig (≤-trans lowCell (sumDrp cell0 azero)))

-- 左边以 Y0, Act 再折叠: 值不小于 OLof YP 的值
module G = RKA.Ge Λ₂ tt {azero} tt P.Act (RKA.hActT Λ₂ tt tt)

LRef : D₀ azero
LRef = yc (Run (accL hz) (OLof YP) C.self tt (z⊲ᴴ Λ₂) P.Act n0 Y0) (τ₀ tt)

lowL : asuc (sum azero RefR) ≤ sum azero LRef
lowL = ≤-trans lowAi (≤-trans (inSum Λ₂ tt inAi azero) (G.ge (accL hz) (OLof YP) C.self (z⊲ᴴ Λ₂) n0 Y0 (τ₀ tt) azero))
```

## 3 前提 (旧关系) 与否定

```agda
reflZ : RelX hz hz {azero} {azero} tt tt zP zP
reflZ = ⨾ˣ (reflDrp RefR) (⨾ˣ (nlˣ (λ _ → ⨾ˣ n1ˣ n0ˣ)) n1ˣ)

hYP : J² {azero} {azero} tt tt YP YP
hYP = ((λ T T′ tx → nlˣ (λ _ → ⨾ˣ (ΩRX² (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0ˣ)) , reflZ) ,
      ((λ T → n0 , J14.here) , (λ T → n0 , J14.here))

preK : RkPre {lW₀ = tt} {lW₀′ = tt} r₀ r₀ uK uK tt tt C.self C.self P.Act P.Act n0 n0 YP YP
preK = cp00 , s∞ , (λ p p′ lc lc′ cp y y′ b → κˣ (λ _ _ _ _ _ → n1ˣ)) , hawAct² Λ₂ Λ₂ , n0ˣ , hYP

-- RkSoundZ, 结论的条件换成恒真的 Any (本文的变体)
RkSoundS-Any : H → H → Set
RkSoundS-Any L L′ =
  ∀ {ly ly′ W₀ W₀′ k k′ W W′ m m′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
    {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁} {u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁}
    (lW : Lg W) (lW′ : Lg W′) (ac : AccY ly) (ac₁ : AccY k) (ac′ : AccY ly′) (ac₁′ : AccY k′)
    (q₀ : W₀ ⊲ W) (q₀′ : W₀′ ⊲ W′) (ll : LW ly W) (ll′ : LW ly′ W′) (A₀ : Ig ly W) (A₀′ : Ig ly′ W′)
    (w : D ly W) (w′ : D ly′ W′) (Y : St W) (Y′ : St W′) (T : Tg W L m) (T′ : Tg W′ L′ m′) (R′ : StH m′ k′ L′) →
  RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ lW lW′ q₀ q₀′ A₀ A₀′ w w′ Y Y′ → TX lW lW′ T T′ →
  rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) ≡ rise → rkT (⊲ᴴ↑ (wm T′) (kk r′ q₀′ ll′)) (tm T′) (lm T′) ≡ keep R′ →
  ActS A₀ → ActS A₀′ →
  SemS L L′ (lm T) (lm T′) Any
    (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise) (RKi ac′ ac₁′ r′ u′ q₀′ lW′ ll′ A₀′ w′ Y′ T′ (keep R′))

¬RkSoundS-Any : ¬ RkSoundS-Any hz (hs hz)
¬RkSoundS-Any h = irr (sum azero RefR) (≤-trans lowL (vsum⁺⁺ rel (≤-refl azero)))
  where
  rel : RelX⁺⁺ hz hz {azero} {azero} tt tt LRef RefR
  rel = h r₀ r₀ {u = uK} {u′ = uK} tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself P.Act P.Act n0 n0 YP YP
          (τ₀ tt) T₁ rk1 preK (cp00 , u∞ s∞) refl refl sAct sAct
          tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 P.Act P.Act (hawS hz (hs hz))
          n0 n0 n0⁺⁺ Y0 Y0 (jYs⁺⁺ n0⁺⁺) tt (τ₀ tt) (τ₀ tt) (cp00 , s∞)
```

## 4 `DomZ` 挡住的正是这一次再折叠

```agda
¬domZ-Y0 : ¬ DomZ tt YP {azero} {azero} tt tt Y0 Y0
¬domZ-Y0 ((_ , rz) , _) = irr (sum azero ωR) (≤-trans zBigω (vsum⁺⁺ rz (≤-refl azero)))
```
