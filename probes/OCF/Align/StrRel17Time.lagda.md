# 结构关系, 第十七轮 (二): 带时间条件的再折叠: `xL` 的一对输出, 一切产生状态, 一切再折叠状态

> 不读记号. 入口 [StrRel17](StrRel17.lagda.md). 接口 [StrRel17If](StrRel17If.lagda.md).
>
> 设定: $\Lambda_2=2$, 节点 `xL` (层 $2$, 坐标层 $0$, 分支 `n1`), 世界 $0$, 路径 `self`, 动作 `Act`, 上下文 `n0`. **产生状态 $Y$ 任意.** `xL` 以 $Y$ 运行, 第 $0$ 层目标上的输出 `OutLY` (链极限), 第 $1$ 层目标上的输出 `OutRY` (节点), 即 `rk⁺` 的那一对 (`StrRel16Kr.rkAt` 在 $Y=Y_1$ 时). 再折叠: 左边以 $Y_2$, 右边以 $Y_2'$, 都用 `Act`, `n0`, 读第 $0$ 层目标.
>
> 1. **(条件定理) `Core.valC`**: 若 `J²⁺ Y₂ Y₂′`, 且 "右边再折叠时内部第一个节点处的状态 $S_0\oplus\mathrm{Step}\,S_0$ 支配产生状态 $Y$" (前提 `hS`, 对一切晚于 $Y_2'$ 的非空 $S_0$), 则两次再折叠的输出 `RelX⁺ hz hz` 相关.
> 2. **(定理) `valT`: 时间条件 `DomL` 足够.** `J²⁺ Y₂ Y₂′` 且 `J²⁺ Y Y₂′` (接口的 `DomL`: 右边再折叠的状态支配左边产生时的状态) ⇒ 相关. 推论 **`valLater`**: `J²⁺ Y Y` 且 `Later Y Y₂′` (字面的时间关系) ⇒ 相关. 推论 **`valLaterV`**: 第 $0$ 层的和 $\le$.
> 3. **(定理) `valY₁`: 产生状态是 $Y_1$ 时, 不要时间条件**: 一切 `J²⁺ Y₂ Y₂′` ⇒ 相关 (`StrRel17Val.domY₁`). `StrRel17Val.valLKN` 是 $Y_2=Y_2'=$ `YN` 的特例.
>
> 4. **(定理, 前提实例) `hYB`, `exBig`**: 比 $Y_1$ 大的产生状态 $Y_B=Y_1\oplus\mathrm{Step}\,Y_1$ 满足 `valLaterV` 的前提, 值的结论成立.
>
> **范围.** 一对具体的节点 (`xL` 对自己), 有限的 $\Lambda_2$, 动作与上下文固定 (`Act`, `n0`), 一个目标对 $(\tau_0,\tau_0)$. 这是 `RkSoundT 0 1` 的一个实例在**右边上升**的那个再折叠目标对上的结论. 不是 `RkSoundT`: 一般的分支、动作、目标对没有处理; 右边**保留**的再折叠目标对见 `StrRel17Obs`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel17Time where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl)
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; ss; z⊲ᴴ; StH; Vs; D; D₀; n0; n1; _⨾_; nl; ni; nw; Ωd;
  accL; AccY; sum; outS; ⊲ᴴ↑)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel13Val using (Λ₂; r₀; xL; cp00)
open import OCF.Align.StrRel14J Λ₂ tt using (NE; Lf; here; left; rgt0; ne⊕)
open import OCF.Align.StrRel15Fin using (T₁)
open import OCF.Align.StrRel16Lem using (Lp; here; left; module V0; module Pf)
open import OCF.Align.StrRel16If Λ₂ tt using (RelX⁺; J²⁺; n0⁺; in⁺; In; here; inL; inR; inE)
open import OCF.Align.StrRel16Sem Λ₂ tt using (jPfx⁺; ext⁺; semX00⁺; module RunIn)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Node Λ₂ tt using (module Z00)
open import OCF.Align.StrRel17If Λ₂ tt using (Later)
open import OCF.Align.StrRel17Val using (domY₁)

open Rk Λ₂ tt using (s∞)
open FinΛ⁺ Λ₂ tt tt using (stepOA²⁺; Y₁)
open V0 Λ₂ tt using (vsum⁺)
open Pf Λ₂ tt using (lp-lf)
module P = At Λ₂ tt
open P using (Tg; tg; wm; tm; τ₀; St; Df; d; z; yc; Run; Rpt; Act; Step; _⊕⟨_⟩_; Ig; LW; kk; BNi; Ai)
```

## 1 小引理: 左脊是分量; 分量的传递; 左前缀的传递

```agda
lf→in : ∀ {t m} {s x : D t m} → Lf s x → In s x
lf→in here = here
lf→in (left h) = inL (lf→in h)
lf→in (rgt0 h) = inR (lf→in h)

in-tr : ∀ {L V} {a b c : D L V} → In a b → In b c → In a c
in-tr p here = p
in-tr p (inL q) = inL (in-tr p q)
in-tr p (inR q) = inR (in-tr p q)
in-tr p (inE n q) = inE n (in-tr p q)

lp-tr : ∀ {t m} {a b c : D t m} → Lp a b → Lp b c → Lp a c
lp-tr p here = p
lp-tr p (left q) = left (lp-tr p q)

later-tr : ∀ {W} {Y₀ Y₁′ Y : St W} → Later Y₀ Y₁′ → Later Y₁′ Y → Later Y₀ Y
later-tr (p , pz) (q , qz) = (λ T → lp-tr (p T) (q T)) , lp-tr pz qz

later⊕ : ∀ {W} {lW : Lg W} (Y : St W) (Δ : Df W) → Later Y (Y ⊕⟨ lW ⟩ Δ)
later⊕ Y Δ = (λ T → left here) , left here

later-refl : ∀ {W} (Y : St W) → Later Y Y
later-refl Y = (λ T → here) , here

ne-later : ∀ {W} {Y S : St W} → NE Y → Later Y S → NE S
ne-later ne (p , _) T = proj₁ (ne T) , lp-lf (proj₂ (ne T)) (p T)
```

`RunIn.pos` 走到的状态晚于起点 (只经 `⊕` 与 `Rpt`).

```agda
module PosLater {L′ V′ W′} (lW′ : Lg W′) (ac′ : AccY L′) (q′ : V′ ⊲ W′) (ll′ : LW L′ W′) (A₀′ : Ig L′ W′) where
  module R = RunIn {L = hz} {L′ = L′} {W = azero} {lW = tt} lW′ ac′ q′ ll′ A₀′

  rptLater : ∀ (e : ℕ → D L′ V′) w Y n → Later Y (proj₂ (Rpt ac′ e q′ lW′ ll′ A₀′ w Y n))
  rptLater e w Y zero = later-refl Y
  rptLater e w Y (suc n) = later-tr (rptLater e w Y n) (later⊕ _ _)

  posLater : ∀ {y′ x′ : D L′ V′} (h : In y′ x′) w Y → Later Y (proj₂ (R.pos h w Y))
  posLater here w Y = later-refl Y
  posLater (inL h) w Y = posLater h w Y
  posLater {x′ = a ⨾ b} (inR h) w Y = later-tr (later⊕ Y _) (posLater h _ _)
  posLater {x′ = nl e} (inE n h) w Y = later-tr (rptLater e w Y n) (posLater h _ _)
```

## 2 产生与再折叠

```agda
module Core (Y : St azero) where
  ΔLY : Df azero
  ΔLY = Run (accL Λ₂) xL C.self tt hself Act n0 Y

  OutLY : D hz azero
  OutLY = yc ΔLY (τ₀ tt)

  OutRY : D (hs hz) azero
  OutRY = yc ΔLY T₁

  -- OutRY 的分支 (RKi 的 keep 句的字面)
  brR : ∀ {W′} → azero ⊲ W′ → Lg W′ → Vs (hs hz) (ss {W = azero} {k = hz} hself) W′ → D (hs hz) W′
  brR p lW′ y = yc (BNi (accL Λ₂) (accL hz) r₀ (λ _ _ _ → n1) C.self hself Act n0 Y (kk r₀ C.self hself) (⊲-tr C.self p) lW′ (outS (ss {W = azero} {k = hz} hself) y))
                   (tg C.self (⊲ᴴ↑ p (hsuc hself)) lW′)

  chkR : OutRY ≡ ni (ss hself) brR
  chkR = refl

  hk : LW hz azero
  hk = kk (ss {W = azero} {k = hz} hself) C.self (hsuc hself)

  A²R : Ig hz azero
  A²R = Ai (accL (hs hz)) (accL hz) (ss hself) brR C.self hk (hsuc hself) Act n0

  Tc : Tg azero hz azero
  Tc = tg C.self hk tt

  module Re (Y₂ Y₂′ : St azero) (hY₂ : J²⁺ tt tt Y₂ Y₂′) where
    LaterLY LaterRY : D₀ azero
    LaterLY = yc (Run (accL hz) OutLY C.self tt (z⊲ᴴ Λ₂) Act n0 Y₂) (τ₀ tt)
    LaterRY = yc (Run (accL (hs hz)) OutRY C.self tt (hsuc hself) Act n0 Y₂′) (τ₀ tt)

    neY₂′ : NE Y₂′
    neY₂′ = proj₂ (proj₂ hY₂)

    -- 右边链的第一项 (Y₂′ 在坐标层上的读数) 的左脊上的 ω⋅(1 ⨾ y)
    h₀ : In (nl (λ _ → n1 ⨾ proj₁ (neY₂′ Tc))) (yc (d Y₂′) Tc)
    h₀ = lf→in (proj₂ (neY₂′ Tc))

    module R = RunIn {L = hz} {L′ = hz} {W = azero} {lW = tt} tt (accL hz) C.self hk A²R
    module PL = PosLater {L′ = hz} tt (accL hz) C.self hk A²R

    S₀ : St azero
    S₀ = proj₂ (R.pos h₀ n0 Y₂′)

    laterS₀ : Later Y₂′ S₀
    laterS₀ = PL.posLater h₀ n0 Y₂′

    neS₀ : NE S₀
    neS₀ = ne-later neY₂′ laterS₀

    jS₀ : J²⁺ tt tt Y₂ S₀
    jS₀ = proj₂ (R.posOK h₀ n0 Y₂′ n0⁺ hY₂)

    -- 证明: 与 StrRel16Val 相同的四步, 只是第一段路径来自 NE (h₀), 第 2 步的状态前提是参数 hS
    valC : J²⁺ {azero} {azero} tt tt Y (S₀ ⊕⟨ tt ⟩ Step S₀) → RelX⁺ hz hz tt tt LaterLY LaterRY
    valC hS =
      in⁺
        (semX00⁺
          (Z00.rr00 {lV = tt} {lV′ = tt} r₀ (ss hself) (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt (accL Λ₂) (accL hz) _ _
             C.self _ hself _ Act _ n0 _ Y _
             cp00 (λ p p′ l l′ cp z₁ z₁′ hz₁ Y Y′ hY → stepOA²⁺ hY)
             hS
             (τ₀ tt) _ (cp00 , s∞) refl refl)
          tt tt (accL hz) _ (z⊲ᴴ Λ₂) _ C.self _ cp00 Act _ (λ p p′ l l′ cp w w′ hw Y Y′ hY → stepOA²⁺ hY) n0 _ n0⁺ Y₂ _
          (jPfx⁺ jS₀ ((λ T → left (left (left (left here)))) , left (left (left (left here)))))
          (τ₀ tt) (τ₀ tt) (cp00 , s∞))
        (inE 0 (in-tr (inE 0 (inL (inE 1 (inL (inR (inE 0 (inL (inR (inL (inR here)))))))))) (R.runIn h₀ n0 Y₂′ (τ₀ tt))))
```

## 3 三个推论

```agda
-- 时间条件 DomL: 右边再折叠的状态支配左边产生时的状态
valT : ∀ (Y Y₂ Y₂′ : St azero) (hY₂ : J²⁺ tt tt Y₂ Y₂′) → J²⁺ tt tt Y Y₂′ → RelX⁺ hz hz tt tt (Core.Re.LaterLY Y Y₂ Y₂′ hY₂) (Core.Re.LaterRY Y Y₂ Y₂′ hY₂)
valT Y Y₂ Y₂′ hY₂ dom = R.valC (ext⁺ (jPfx⁺ dom R.laterS₀) (Step R.S₀))
  where module R = Core.Re Y Y₂ Y₂′ hY₂

-- 字面的时间关系: 右边再折叠的状态晚于产生时的状态
valLater : ∀ (Y Y₂ Y₂′ : St azero) (hY₂ : J²⁺ tt tt Y₂ Y₂′) → J²⁺ tt tt Y Y → Later Y Y₂′ →
           RelX⁺ hz hz tt tt (Core.Re.LaterLY Y Y₂ Y₂′ hY₂) (Core.Re.LaterRY Y Y₂ Y₂′ hY₂)
valLater Y Y₂ Y₂′ hY₂ hY lt = valT Y Y₂ Y₂′ hY₂ (jPfx⁺ hY lt)

valLaterV : ∀ (Y Y₂ Y₂′ : St azero) (hY₂ : J²⁺ tt tt Y₂ Y₂′) → J²⁺ tt tt Y Y → Later Y Y₂′ →
            sum azero (Core.Re.LaterLY Y Y₂ Y₂′ hY₂) ≤ sum azero (Core.Re.LaterRY Y Y₂ Y₂′ hY₂)
valLaterV Y Y₂ Y₂′ hY₂ hY lt = vsum⁺ (valLater Y Y₂ Y₂′ hY₂ hY lt) (≤-refl azero)

-- 产生状态 Y₁: 不要时间条件
valY₁ : ∀ (Y₂ Y₂′ : St azero) (hY₂ : J²⁺ tt tt Y₂ Y₂′) →
        RelX⁺ hz hz tt tt (Core.Re.LaterLY (Y₁ tt) Y₂ Y₂′ hY₂) (Core.Re.LaterRY (Y₁ tt) Y₂ Y₂′ hY₂)
valY₁ Y₂ Y₂′ hY₂ = R.valC (domY₁ R.S₀ R.neS₀)
  where module R = Core.Re (Y₁ tt) Y₂ Y₂′ hY₂
```

## 4 前提可满足: 比 $Y_1$ 大的产生状态

$Y_1\oplus\mathrm{Step}\,Y_1$ (闭项在第二个 `n1` 之后的状态) 与自己 `J²⁺` 相关 (`hYB`, 由 `law⊕⁺`); 以它产生, 以它自己 (`later-refl`) 或它的任何向右延长再折叠, `valLaterV` 给出值的结论. 实例 `exBig` 取再折叠状态 = 产生状态.

```agda
open import OCF.Align.StrRel16Sem Λ₂ tt using (law⊕⁺)
open FinΛ⁺ Λ₂ tt tt using (hY₁⁺)

YB : St azero
YB = Y₁ tt ⊕⟨ tt ⟩ Step (Y₁ tt)

hYB : J²⁺ tt tt YB YB
hYB = law⊕⁺ cp00 (Y₁ tt) (Y₁ tt) (Step (Y₁ tt)) (Step (Y₁ tt)) (hY₁⁺ tt tt) (stepOA²⁺ (hY₁⁺ tt tt))

exBig : sum azero (Core.Re.LaterLY YB YB YB hYB) ≤ sum azero (Core.Re.LaterRY YB YB YB hYB)
exBig = valLaterV YB YB YB hYB hYB (later-refl YB)
```
