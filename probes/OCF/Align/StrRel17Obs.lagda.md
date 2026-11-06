# 结构关系, 第十七轮 (三): 第一个障碍的编译形式: 右边保留的再折叠目标对, 与时间条件无关

> 不读记号. 入口 [StrRel17](StrRel17.lagda.md). 接口 [StrRel17If](StrRel17If.lagda.md).
>
> `rk⁺` 的可靠性 (带不带时间条件都一样) 要对**一切** `TX` 再折叠目标对给出 `RelX⁺`. 在 `StrRel16Kr.rkAt` 那一对 (左 `OutL`, `xL` 以 $Y_1$ 在第 $0$ 层目标上上升的链极限; 右 `OutR`, `xL` 以 $Y_1$ 在第 $1$ 层目标上保留的节点) 上, 取再折叠目标对 $(\tau_0, T_1)$ (层 $0$ 对层 $1$): 左边是 "链极限的再运行" (`nl …`), 右边的节点 (坐标层 $0$) 在第 $1$ 层目标上**再次保留**, 是 `ni …`.
>
> 1. **(定理) `invNi`: `RelX⁺ hz L′ x (ni R u′)` ⇒ $x$ 字面是 `n0`, 或 $x$ 字面是某个节点的 `RKi … rise`** (`RkLeft`, 即 `rk⁺` 的左边的形状). 理由: 以 `ni` 为右边的规则只有 `n0⁺`, `ni⁺` (左边要是第 $0$ 层的节点, 不存在), `in⁺` (`ni` 的分量只有它自己), `rk⁺`.
> 2. **(定理) `obsT`: 对任意条件 `Ok`, 只要 `Ok` 在 $(Y_1, Y_1)$ 上成立, `SemT hz (hs hz) … Ok OutL OutR` ⇒ `RkLeft ReL`**, 其中 `ReL` 是 `OutL` 以 $Y_1$ 再运行在 $\tau_0$ 上的输出. 推论 **`obsRkT`**: `RkSoundT hz (hs hz)` ⇒ `RkLeft ReL` (时间条件 `DomL` 在 $(Y_1,Y_1)$ 上由 `hY₁⁺` 给出); **`obsRk16`**: `StrRel16If.RkSound₀ (hs hz)` ⇒ `RkLeft ReL`.
>
> 3. **(定理) `chkL`, `chkRise`, `chkKeep`, `upFix`** (§4): 障碍的那一对 (`ReL`, `ReR`) 与 `StrRel16Val.valLK` 的那一对 (`LaterL`, `LaterR`) 左边相同, 右边是同一个节点同一组参数在 $\tau_0$ (上升) 与 $T_1$ (保留) 上的 `RKi` (`refl`); 所以对任何含 `RelX⁺ hz hz` 且有 `Up` 封闭性 (同一节点: $\le$ 低目标上的上升输出 ⇒ $\le$ 高目标上的保留输出) 的关系族, 障碍的那一对成立. `Up` 是前提, 没有实例.
>
> **读法 (判断).** `RkLeft ReL` 要求 "链极限的再运行" 在字面上 (命题相等) 是某个节点的上升输出. 本文没有证明它不成立, 也没有给出实例: `rk⁺` 的参数 (节点, 分支, 动作, 状态) 是存在量化的, 动作可以任意, 本文不对它求逆. 所以这里**没有否定** `RkSoundT`; 编译的结论是: 时间条件只约束状态, 而右边保留的那些再折叠目标对上的困难在结论关系的形状上 (`RelX⁺` 里 "某物 ≤ 节点" 只有字面的 `rk⁺`), 时间条件碰不到它. 这是本轮的第一个障碍.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel17Obs where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; ss; z⊲ᴴ; StH; Vs; D; D₀; n0; n1; ni; accL; AccY)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
open import OCF.Align.StrRel15Fin using (T₁; module FinΛ)
open import OCF.Align.StrRel16If Λ₂ tt using (RelX⁺; LeX⁺; n0⁺; ni⁺; in⁺; rk⁺; here; RkSound₀)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Val using (OutL; OutR)
open import OCF.Align.StrRel17If Λ₂ tt using (Cond; SemT; RkSoundT; DomL; Any)
open import OCF.Align.StrRel14If Λ₂ tt using (n1ˣ; n0ˣ)

open Rk Λ₂ tt using (s∞; u∞)
open FinΛ Λ₂ tt tt using (hawAct²; hY₁)
open FinΛ⁺ Λ₂ tt tt using (hawAct²⁺; Y₁; hY₁⁺)
module P = At Λ₂ tt
open P using (Tg; tm; lm; τ₀; St; yc; Run; Act; Ig; LW; RKi; rise)
```

## 1 左边是链极限的再运行, 右边是节点

```agda
ReL : D hz azero
ReL = yc (Run (accL hz) OutL C.self tt (z⊲ᴴ Λ₂) Act n0 (Y₁ tt)) (τ₀ tt)

ReR : D (hs hz) azero
ReR = yc (Run (accL (hs hz)) OutR C.self tt (hsuc hself) Act n0 (Y₁ tt)) T₁
```

`RkLeft lV x`: $x$ 字面是某个节点在某个目标上的 `RKi … rise` (`rk⁺` 的左边).

```agda
data RkLeft {L : H} {V : A} : Lg V → D L V → Set where
  rkl : ∀ {ly W₀ k W} {lW₀ : Lg W₀} (r : StH W₀ k ly) {u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁}
          (lW : Lg W) (ac : AccY ly) (ac₁ : AccY k) (q₀ : W₀ ⊲ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
          (T : Tg W L V) → RkLeft (lm T) (RKi ac ac₁ r u q₀ lW ll A₀ w Y T rise)
```

## 2 以 `ni` 为右边的 `RelX⁺ hz L′` 的反演

```agda
invNi : ∀ {L′ V V′ k′} {lV : Lg V} {lV′ : Lg V′} {x : D hz V} {R : StH V′ k′ L′}
          {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ R W′ → D L′ W′} →
        RelX⁺ hz L′ lV lV′ x (ni R u′) → (x ≡ n0) ⊎ RkLeft lV x
invNi n0⁺ = inj₁ refl
invNi (ni⁺ {r = ()} _ _)
invNi (in⁺ h here) = invNi h
invNi (rk⁺ {lW₀ = lW₀} r r′ {u = u} lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ R′ pre tx eL eR) =
  inj₂ (rkl {lW₀ = lW₀} r {u = u} lW ac ac₁ q₀ ll A₀ w Y T)
```

## 3 约化: 任意条件下的语义都要求 `RkLeft ReL`

```agda
pick : (ReL ≡ n0) ⊎ RkLeft tt ReL → RkLeft tt ReL
pick (inj₁ ())
pick (inj₂ h) = h

obsT : ∀ (Ok : Cond) → Ok {azero} {azero} tt tt (Y₁ tt) (Y₁ tt) → SemT hz (hs hz) tt tt Ok OutL OutR → RkLeft tt ReL
obsT Ok ok s = pick (invNi (s tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 Act Act (hawAct²⁺ hz (hs hz))
                             n0 n0 n0⁺ (Y₁ tt) (Y₁ tt) (hY₁⁺ tt tt) ok (τ₀ tt) T₁ (cp00 , u∞ s∞)))
```

推论: 带时间条件的 `RkSoundT`, 与 `StrRel16` 的 `RkSound₀`, 在 `rkAt` 的参数上都给出 `RkLeft ReL`.

```agda
T₀ : Tg azero hz azero
T₀ = τ₀ tt

obsRkT : RkSoundT hz (hs hz) → RkLeft tt ReL
obsRkT rkS =
  obsT (DomL tt (Y₁ tt)) (hY₁⁺ tt tt)
    (rkS r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Act Act n0 n0 (Y₁ tt) (Y₁ tt) T₀ T₁ (ss hself)
       (cp00 , (s∞ , ((λ p p′ lc lc′ cp y y′ b → n1ˣ) , (hawAct² Λ₂ Λ₂ , (n0ˣ , hY₁ tt tt))))) (cp00 , u∞ s∞) refl refl)

obsRk16 : RkSound₀ (hs hz) → RkLeft tt ReL
obsRk16 rkS =
  obsT Any tt
    (λ lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w w′ hw Y Y′ hY _ →
       rkS r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Act Act n0 n0 (Y₁ tt) (Y₁ tt) T₀ T₁ (ss hself)
         (cp00 , (s∞ , ((λ p p′ lc lc′ cp y y′ b → n1ˣ) , (hawAct² Λ₂ Λ₂ , (n0ˣ , hY₁ tt tt))))) (cp00 , u∞ s∞) refl refl
         lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w w′ hw Y Y′ hY)
```

## 4 障碍的那一对是 `valLK` 那一对的 "保留版"

`ReR` 与 `StrRel16Val.LaterR` 是**同一个节点** (`OutR`, 分支 `brR`), 同一组再折叠参数 ($Y_1$, `Act`, `n0`), 在两个目标上的 `RKi`: $T_1$ 上保留 (`keepO`), $\tau_0$ 上上升 (`riseO`); `ReL` 就是 `StrRel16Val.LaterL`. 所以若结论关系有一条 "同一节点: 某物 $\le$ 它在低目标上的上升输出 ⇒ 某物 $\le$ 它在高目标上的保留输出" 的规则 (`Up`, 下面只写成对一个关系族的封闭性), 障碍的那一对就由 `valLK⁺` 得到 (`upFix`). `Up` 不是接口的一部分, 它的可靠性没有证 (判断: 要 `RelX⁺` 的传递性, 或同一节点上的 `RkSoundT`; 见入口 §3).

```agda
open import OCF.Align.StrRel16Val using (LaterL; LaterR; valLK⁺)
open import OCF.Align.StrRel17Time using (module Core)
open P using (keep)

module CY = Core (Y₁ tt)

riseO : D hz azero
riseO = RKi (accL (hs hz)) (accL hz) (ss hself) CY.brR C.self tt (hsuc hself) Act n0 (Y₁ tt) (τ₀ tt) rise

keepO : D (hs hz) azero
keepO = RKi (accL (hs hz)) (accL hz) (ss hself) CY.brR C.self tt (hsuc hself) Act n0 (Y₁ tt) T₁ (keep (ss hself))

chkL : ReL ≡ LaterL
chkL = refl

chkRise : LaterR ≡ riseO
chkRise = refl

chkKeep : ReR ≡ keepO
chkKeep = refl

RelT2 : Set₁
RelT2 = ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set

Up : RelT2 → Set
Up R = ∀ {x : D hz azero} → R hz hz tt tt x riseO → R hz (hs hz) tt tt x keepO

upFix : ∀ (R : RelT2) → (∀ {x y : D hz azero} → RelX⁺ hz hz tt tt x y → R hz hz tt tt x y) → Up R → R hz (hs hz) tt tt ReL ReR
upFix R emb up = up (emb valLK⁺)
```
