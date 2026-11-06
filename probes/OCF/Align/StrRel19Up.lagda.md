# 结构关系, 第十九轮 (三): `up` 让障碍的那一对可推导; 再折叠目标对 $(T_1,T_1)$ 是新的第一个障碍

> 不读记号. 入口 [StrRel19](StrRel19.lagda.md). 接口 [StrRel19If](StrRel19If.lagda.md). 实例 $\Lambda_2=2$, `StrRel16Kr.rkAt` 那一对 (节点 `xL`: 层 $2$, 坐标层 $0$, 分支 `n1`, 动作 `Act`, 上下文 `n0`, 产生状态 $Y_1$; 左 `OutL` 在 $\tau_0$ 上升, 右 `OutR` 在 $T_1$ 保留).
>
> 1. **(定理) `emb00`, `back00`**: 第 $0$ 层对第 $0$ 层, `RelX⁺` 与 `RelX⁺⁺` 互相包含 (`up` 的结论的右层不是 $0$).
> 2. **(定理) `obs⁺⁺`: `StrRel17Obs` 的障碍那一对 (`ReL`, `ReR`) 在 `RelX⁺⁺` 里可推导**: `up` (产生时动作 `Act`, `sAct`) 作用在 `StrRel16Val.valLK⁺` 上. 这是 `StrRel18Up.upX` 说 "只能由新关系给出" 的那一步.
> 3. **(定理) `noNi0`**: 左边含节点 (`HasNi`, 沿 `⨾` 与 `nl` 的第 $n$ 项可达一个 `ni`) 时, 它在 `RelX⁺⁺` 里不低于任何第 $0$ 层的树. **(定理) `riseLe`**: 节点在目标上上升 ⇒ 目标的层在节点的坐标层之下 (第一位置).
> 4. **(定理) `invNi⁺⁺`**: 右边是坐标层为 $0$ 的节点, 左边是含节点的链极限 (`nl e`, `HasNi`) 时, `RelX⁺⁺` 的推导只能是字面的 `rk⁺⁺` (`RkLeft`). 理由: `up` 要左边低于同一节点在某个上升目标上的输出; 坐标层 $0$ 的节点只在第 $0$ 层目标上上升 (`riseLe`), 那个输出是第 $0$ 层的树, 而左边含节点 (`noNi0`).
> 5. **(定理, 约化) `obsUpTT`: `UpSoundZ` ⇒ `RkLeft tt StepT₁`**, `StepT₁` = $\omega\cdot(\Omega_1⨾\text{读数})$ (`n1` 以 `Act`, $Y_1$ 在 $T_1$ 上的输出). 取 `up` 的左边 $x=$ `n1` ($\le$ `OutL`, 由 `in⁺⁺`; 第 $0$ 层的语义由 `semS00`), 在再折叠目标对 $(T_1,T_1)$ 上: 左边是 `StepT₁` (链极限, 含 $\Omega_1$ 的节点), 右边是 `OutR` 的节点**再次保留** (坐标层 $0<1$), `invNi⁺⁺` 给出 `RkLeft`. **(定理, 约化) `obsRkTT`: `RkSoundZ hz (hs hz)` ⇒ `RkLeft tt LeftT₁`** (`LeftT₁` = `OutL` 以 `Act`, $Y_1$ 在 $T_1$ 上的再折叠), 同一机制; `HasNi LeftT₁` 由 `posNi` (`Act` 在第 $\ge1$ 层目标上把每个 `n1` 变成含节点的 `Step`) 与 `OutL` 的一个 `Pos0` 证明 (由有限搜索 `pos?` 在类型检查时算出).
>
> **读法 (判断).** `up` 解决了 `StrRel17Obs` 的障碍目标对 $(\tau_0,T_1)$ (左边的层 $0$ 不高于右边节点的坐标层 $0$); 但在再折叠目标对 $(T_1,T_1)$ 上, 左边的层 $1$ 高于右边节点的坐标层 $0$, 右边节点再次保留, 而同一节点在第 $1$ 层上没有上升的目标, 所以 `up` 用不上. `RelX⁺⁺` 里 "某物 $\le$ 节点" 只剩字面的 `rk⁺⁺` 与 `up`; `up` 的语义闭包要求在 "左边的层高于节点的坐标层" 的目标对上也能比到节点, 这一类规则 `RelX⁺⁺` 里没有. 所以 `UpSoundZ` 与 `RkSoundZ hz (hs hz)` 都约化到 `RkLeft` (字面地是某个节点的上升输出), 与 `StrRel17Obs` 的第一个障碍同形, 位置从 $(\tau_0,T_1)$ 移到 $(T_1,T_1)$.
>
> **只否定什么.** 本文没有否定: `obsUpTT`, `obsRkTT` 是约化; `RkLeft tt StepT₁` 与 `RkLeft tt LeftT₁` 没有证, 也没有否定 (`RkLeft` 对节点、分支、动作、状态存在量化). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `obs⁺⁺`: `sAct`, `refl`, `valLK⁺`. `obsUpTT` 给 `UpSoundZ` 的参数: 节点参数是闭项, `sAct`, `refl`, `refl`, 前提 `SemS hz hz … n1 OutL` 由 `semS00` (`domZmono`); 再折叠一侧 `hawsAct`, `n0⁺⁺`, `hY₁⁺⁺`, `domZY₁`, 目标对 `(cp00 , s∞)`; 都是定理. `obsRkTT`: `StrRel18Obs.preY₁` (`RkPre`), `(cp00 , u∞ s∞)`, `refl`, `refl`, `sAct`, `sAct`, 再折叠一侧同上.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel19Up where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; from-just)
import Data.Maybe as M
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; hlim; hLim; ss; z⊲ᴴ; _⊲[_]_; StH; Vs; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw;
  accL; AccY; cmpH; ⊲ᴴ↑)
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
open import OCF.Align.StrRel15Fin using (T₁)
open import OCF.Align.StrRel16If Λ₂ tt using (RelX⁺; n0⁺; n1⁺; ⨾⁺; nl⁺; pr⁺; nw⁺; ni⁺; κ⁺; in⁺; rk⁺; nκ⁺; module P; In; here; inL; inR; inE)
open import OCF.Align.StrRel16Val using (OutL; OutR; LaterL; valLK⁺)
open import OCF.Align.StrRel17If Λ₂ tt using (Pos0; p1; pL; pR; pE; pW)
open import OCF.Align.StrRel17Obs using (ReL; ReR; keepO; RkLeft; rkl; module CY)
open import OCF.Align.StrRel18Obs using (preY₁)
open import OCF.Align.StrRel19If Λ₂ tt
open import OCF.Align.StrRel19Sem Λ₂ tt using (module Sem00; domZmono; module FinΛ⁺⁺)

open Rk Λ₂ tt using (s∞; u∞)
open FinΛ⁺⁺ tt using (hawsAct; Y₁; hY₁⁺⁺; domZY₁)
open P using (Tg; tg; wm; tm; lm; τ₀; St; yc; Run; Act; Step; Ig; LW; RKi; rkT; rkS; kk; rise; keep)
```

## 1 第 $0$ 层: 两个关系相同

```agda
emb00 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → RelX⁺ hz hz lV lV′ x x′ → RelX⁺⁺ hz hz lV lV′ x x′
emb00 n0⁺ = n0⁺⁺
emb00 n1⁺ = n1⁺⁺
emb00 (⨾⁺ a b) = ⨾⁺⁺ (emb00 a) (emb00 b)
emb00 (nl⁺ f) = nl⁺⁺ (λ n → emb00 (f n))
emb00 (pr⁺ a) = pr⁺⁺ (emb00 a)
emb00 (nw⁺ ap a) = nw⁺⁺ ap (emb00 a)
emb00 (ni⁺ {r = ()} _ _)
emb00 (κ⁺ {zz = ()} _)
emb00 (in⁺ a i) = in⁺⁺ (emb00 a) i
emb00 (rk⁺ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ () _ _ _ _)
emb00 (nκ⁺ {r = ()} _)

back00 : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → RelX⁺⁺ hz hz lV lV′ x x′ → RelX⁺ hz hz lV lV′ x x′
back00 n0⁺⁺ = n0⁺
back00 n1⁺⁺ = n1⁺
back00 (⨾⁺⁺ a b) = ⨾⁺ (back00 a) (back00 b)
back00 (nl⁺⁺ f) = nl⁺ (λ n → back00 (f n))
back00 (pr⁺⁺ a) = pr⁺ (back00 a)
back00 (nw⁺⁺ ap a) = nw⁺ ap (back00 a)
back00 (ni⁺⁺ {r = ()} _ _)
back00 (κ⁺⁺ {zz = ()} _)
back00 (in⁺⁺ a i) = in⁺ (back00 a) i
back00 (rk⁺⁺ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ () _ _ _ _)
back00 (nκ⁺⁺ {r = ()} _)
back00 (up _ _ _ _ _ _ _ _ _ _ _ () _ _ _ _)
```

## 2 障碍的那一对在 `RelX⁺⁺` 里可推导

```agda
Y1 : St azero
Y1 = Y₁ tt

obs⁺⁺ : RelX⁺⁺ hz (hs hz) tt tt ReL ReR
obs⁺⁺ = up {x = LaterL} (ss hself) {u = CY.brR} tt (accL (hs hz)) (accL hz) C.self (hsuc hself) Act n0 Y1
           (τ₀ tt) T₁ (ss hself) sAct refl refl (emb00 valLK⁺)
```

## 3 含节点的树不低于第 $0$ 层的树; 上升的目标在坐标层之下

```agda
data HasNi {L : H} {V : A} : D L V → Set where
  hN : ∀ {k} {r : StH V k L} {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} → HasNi (ni r u)
  hL : ∀ {a b} → HasNi a → HasNi (a ⨾ b)
  hR : ∀ {a b} → HasNi b → HasNi (a ⨾ b)
  hE : ∀ {e : ℕ → D L V} n → HasNi (e n) → HasNi (nl e)

noNi0 : ∀ {L V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {y : D₀ V′} → RelX⁺⁺ L hz lV lV′ x y → HasNi x → ⊥
noNi0 n0⁺⁺ ()
noNi0 n1⁺⁺ ()
noNi0 (⨾⁺⁺ a b) (hL h) = noNi0 a h
noNi0 (⨾⁺⁺ a b) (hR h) = noNi0 b h
noNi0 (nl⁺⁺ f) (hE n h) = noNi0 (f n) h
noNi0 (pr⁺⁺ a) h = noNi0 a h
noNi0 (nw⁺⁺ ap a) ()
noNi0 (ni⁺⁺ {r′ = ()} _ _) h
noNi0 (κ⁺⁺ {zz′ = ()} _) h
noNi0 (in⁺⁺ a i) h = noNi0 a h
noNi0 (rk⁺⁺ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ () _ _ _ _) h
noNi0 (nκ⁺⁺ {zz′ = ()} _) h
noNi0 (up _ _ _ _ _ _ _ _ _ _ _ () _ _ _ _) h

rkS→ : ∀ {k t m} (p : k ⊲[ m ] t) → rkS p ≡ rise → t ⊲[ m ] k
rkS→ hself e = hself
rkS→ (hsuc p) ()
rkS→ (hlim n p) ()
rkS→ (hLim e p) ()

riseLe : ∀ {k t m} (km : k ⊲[ m ] Λ₂) (tm′ : t ⊲[ m ] Λ₂) (lm′ : Lg m) → rkT km tm′ lm′ ≡ rise → t ⊲[ m ] k
riseLe km tm′ lm′ with cmpH km tm′ lm′ tt
... | inj₁ t⊲k = λ _ → t⊲k
... | inj₂ k⊲t = rkS→ k⊲t
```

## 4 右边是坐标层 $0$ 的节点, 左边是含节点的链极限

```agda
invNi⁺⁺ : ∀ {L L′ V V′} {lV : Lg V} {lV′ : Lg V′} {e : ℕ → D L V} {R : StH V′ hz L′}
            {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ R W′ → D L′ W′} →
          RelX⁺⁺ L L′ lV lV′ (nl e) (ni R u′) → HasNi (nl e) → RkLeft lV (nl e)
invNi⁺⁺ (in⁺⁺ d here) h = invNi⁺⁺ d h
invNi⁺⁺ (rk⁺⁺ {lW₀ = lW₀} r r′ {u = u} lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ R′ pre tx eL eR) h =
  rkl {lW₀ = lW₀} r {u = u} lW ac ac₁ q₀ ll A₀ w Y T
invNi⁺⁺ (up r lW ac ac₁ q₀ ll A₀ w Y T T′ R′ s eL eR d) h = upCase (riseLe (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T) eL) d h
  where
  upCase : ∀ {t L V V′ m} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {y : D t V′} → t ⊲[ m ] hz → RelX⁺⁺ L t lV lV′ x y → HasNi x → RkLeft lV x
  upCase hself d h = ⊥-elim (noNi0 d h)
```

## 5 实例: $(T_1,T_1)$

```agda
-- n1 ≤ OutL (n1 是链的第一项里的一个分量)
oneL⁺⁺ : RelX⁺⁺ hz hz tt tt n1 OutL
oneL⁺⁺ = in⁺⁺ (n1⁺⁺ {V = azero} {V′ = azero} {lV = tt} {lV′ = tt}) (inE 0 (inR (inE 0 (inL (inE 0 (inL here))))))

module S = Sem00 (DomZ tt Y1) (domZmono tt Y1)

semN1 : SemS hz hz tt tt (DomZ tt Y1) n1 OutL
semN1 = S.semS00 oneL⁺⁺

StepT₁ : D (hs hz) azero
StepT₁ = yc (Step Y1) T₁

RightT₁ : D (hs hz) azero
RightT₁ = yc (Run (accL (hs hz)) OutR C.self tt (hsuc hself) Act n0 Y1) T₁

hasStep : HasNi StepT₁
hasStep = hE 0 (hL (hR hN))

-- UpSoundZ 在 xL 上: n1 ≤ OutL ⇒ n1 ≤ OutR (语义); 再折叠目标对 (T₁, T₁)
-- (h 直接应用, 不作为参数传递: 接口 UpSoundS 的隐式参数 lW₀ 不出现在类型的其余部分, 传递时 Agda 推不出它)
obsUpTT : UpSoundZ → RkLeft tt StepT₁
obsUpTT h = invNi⁺⁺ {L = hs hz} {L′ = hs hz} {lV = tt} {lV′ = tt} rel hasStep
  where
  rel : RelX⁺⁺ (hs hz) (hs hz) tt tt StepT₁ RightT₁
  rel = h {L₀ = hz} {x = n1} {lW₀ = tt} r₀ {u = λ _ _ _ → n1} tt (accL Λ₂) (accL hz) C.self hself Act n0 Y1 (τ₀ tt) T₁ (ss hself) sAct refl refl semN1
          tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 Act Act (hawsAct hz (hs hz))
          n0 n0 n0⁺⁺ Y1 Y1 (hY₁⁺⁺ tt tt) (domZY₁ tt tt) T₁ T₁ (cp00 , s∞)
```

`RkSoundZ` 在 `rkAt` 那一对上, 同一个再折叠目标对. 左边 `LeftT₁` 是 `OutL` 的再折叠; 它含节点: `Act` 在第 $\ge 1$ 层的目标上把每个 `n1` 变成 `Step`, 而 `Step` 在那里以 $\Omega$ 的节点开头 (`posNi`); `OutL` 里有 `n1` (`posOutL`, 有限搜索).

```agda
posNi : ∀ {V W b m} {x : D₀ V} → Pos0 x → (ac : AccY hz) (q : V ⊲ W) (lW : Lg W) (ll : LW hz W) (w : D₀ W) (Y : St W)
          (S : Tg W (hs b) m) → HasNi (yc (Run ac x q lW ll Act w Y) S)
posNi p1 ac q lW ll w Y S = hE 0 (hL (hR hN))
posNi (pL h) ac q lW ll w Y S = hL (posNi h ac q lW ll w Y S)
posNi (pR h) ac q lW ll w Y S = hR (posNi h ac q lW ll _ _ S)
posNi (pE h) ac q lW ll w Y S = hE 0 (posNi h ac q lW ll w Y S)
posNi (pW h) ac q lW ll w Y S = posNi h ac _ lW ll w Y S

pos? : ∀ {W} (x : D₀ W) → Maybe (Pos0 x)
pos? n0 = nothing
pos? n1 = just p1
pos? (a ⨾ b) with pos? a
... | just h = just (pL h)
... | nothing = M.map pR (pos? b)
pos? (nl e) = M.map pE (pos? (e 0))
pos? (nw p x) = M.map pW (pos? x)
pos? (ni () u)
pos? (nκ () u)

posOutL : Pos0 OutL
posOutL = from-just (pos? OutL)

LeftT₁ : D (hs hz) azero
LeftT₁ = yc (Run (accL hz) OutL C.self tt (z⊲ᴴ Λ₂) Act n0 Y1) T₁

relRk : RkSoundZ hz (hs hz) → RelX⁺⁺ (hs hz) (hs hz) tt tt LeftT₁ RightT₁
relRk h =
  h r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Act Act n0 n0 Y1 Y1 (τ₀ tt) T₁ (ss hself)
    preY₁ (cp00 , u∞ s∞) refl refl sAct sAct
    tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 Act Act (hawsAct hz (hs hz))
    n0 n0 n0⁺⁺ Y1 Y1 (hY₁⁺⁺ tt tt) (domZY₁ tt tt) T₁ T₁ (cp00 , s∞)

obsRkTT : RkSoundZ hz (hs hz) → RkLeft tt LeftT₁
obsRkTT h = invNi⁺⁺ {L = hs hz} {L′ = hs hz} {lV = tt} {lV′ = tt} (relRk h) (posNi posOutL (accL hz) C.self tt (z⊲ᴴ Λ₂) n0 Y1 T₁)
```
