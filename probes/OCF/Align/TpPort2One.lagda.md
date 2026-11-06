# 两种种类的 Ω-极限一步 (三): 一个世界里的一个节点

> 入口 [TpPort2](TpPort2.lagda.md). 不含记号. 手写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 不改树、折叠、合法性.
>
> 照 `MonoPort9One` §2–§3 (`Node.low`) 与 `MonoPort8Fin` §1 (`HasPfx`, `pfxRun`), 搬到两种种类的折叠 `HtTowerFFold`. 对一切合法实例 $\Lambda$ (以第 1 层为第一位置), 一切合法世界 $U$ 与 $X_1:(1,0)\le U$:
>
> - `Pfx Y`: 状态 $Y$ 在世界 $U$ 的每个目标上的读数, 沿 `⨾` 左脊以字面的起始段 $Z_0=\mathrm{cv}\,X_1\,(Y_0\oplus\mathrm{Stp}\,Y_0)$ 的读数开头. 回灌格的起始状态就是 $Z_0$ (`Sv`, `Sv₁` 的字面), 格内只往右接.
> - **`Node.low`**: 节点 `ni r (λ _ _ _ → n1)` (任意种类的位置 $r$, 节点层 $k$ 不含 Ω-极限), 状态自洽 (`Good`, 单世界关系 `TpPortRel`) 且 `Pfx`, 底 $\beta\ge1$ ⇒ $T_k <$ 节点在第 0 层的和. 四步: 换世界换实例 (`TpPort2Cross.changeW`); 同一世界 $U$ 里比两次 $\Omega_k$ 的折叠 (`TpPortNode.ΩdObs`); 起始段 $\omega\cdot(\Omega_k⨾0)$ 的第二份非零 (`strict`); 前缀 (`pfxRun`) 与节点在第 0 层上升 (`rk0`).
>
> 与 `MonoPort9One.Node` 的差别: 实例是任一种类的 $\mathrm{h\Omega}\,\kappa\,g'$, 节点的位置是 `sL e hself`, 界的证据 $e$ 是参数 (原文固定为 `C.self`), 因为两种种类的回灌第一个节点的界在 `κA` (`C.self`) 与 `κH` (`hself`) 下写法不同. 位置取 `sL e hself` 而不是任意 $r$: 折叠在节点处用 `accK r`, 只有这一形状它定义地化成 `accL k` (`ΩdObs` 要的形状).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPort2One where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; z⊲)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; _⊲[_]_; hself; LgB; z⊲ᴮ; ⊲ᴮ↑; K; E; Bd)
open import OCF.Align.HtTowerFTree using (S₁; sL; Ht; Wd₂; LgW₂; D; StH; AccY; accᴸ; accL; n0; n1; _⨾_; ni; nw; Ωd; sum; ≤rf) renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerFClosed using (module At; TΛ; one; W₁)
open import OCF.Align.HtTowerFGrow using (nzL; nz≤; sum≥; nz-Ωd; module G)
open import OCF.Align.TpPortSim using (Free)
open import OCF.Align.TpPort2Cross using (changeW; w₀)
import OCF.Align.TpPortRel as RelP
import OCF.Align.TpPortNode as NodeP
```

## §1 前缀

`HasPfx s z`: $s$ 是 $z$ 沿 `⨾` 左脊的一段. 折叠在左脊上先走左边, 状态与上下文不变, 所以和不低于 $s$ 的折叠的和.

```agda
data HasPfx {k : Ht} {V : Wd₂} (s : D k V) : D k V → Set where
  here : HasPfx s s
  left : ∀ {x y} → HasPfx s x → HasPfx s (x ⨾ y)

module Pf (Λ : Ht) (l : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) where
  module P = At Λ l o
  pfxRun : ∀ {k V₀ W} {s z : D k V₀} → HasPfx s z → ∀ (ac : AccY k) (q : V₀ ≤ʷ W) (lW : LgW₂ W) (ll : k ⊲[ W ] Λ) (A₀ : P.Ig k W) w Y
           (T : P.Tg W hz W) β → sum β (P.yc (P.Run ac s q lW ll A₀ w Y) T) ≤ sum β (P.yc (P.Run ac z q lW ll A₀ w Y) T)
  pfxRun here ac q lW ll A₀ w Y T β = ≤-refl _
  pfxRun (left h) ac q lW ll A₀ w Y T β = ≤-trans (pfxRun h ac q lW ll A₀ w Y T β) (sum≥ _ _)
```

## §2 一个世界

```agda
module One (κ : K S₁) (g′ : E S₁ κ → Ht) (l : LgB (hΩ κ g′)) (o : ∀ {w} → hs hz ⊲[ w ] hΩ κ g′) (U : Wd₂) (lU : LgW₂ U) (X₁ : W₁ ≤ʷ U) where
  Λ : Ht
  Λ = hΩ κ g′

  module P = At Λ l o
  module GG = G Λ l o
  open Pf Λ l o using (pfxRun)
  module R7 = RelP Λ l o {U} lU (z⊲ᴮ Λ)
  module N7 = NodeP Λ l o {U} lU (z⊲ᴮ Λ)

  τ : P.Tg U hz U
  τ = P.τ₀ lU

  qU : w₀ ≤ʷ U
  qU = z⊲ (proj₁ U) , z⊲ᴮ (proj₂ U)

  rk0 : ∀ {k m} (x : P.Rk k hz m) → x ≡ P.rise
  rk0 (P.keep ())
  rk0 P.rise = refl

  Free→Fin : ∀ k → Free k → R7.Fin k
  Free→Fin hz _ = tt
  Free→Fin (hs b) x = Free→Fin b x
  Free→Fin (hl f) x = λ n → Free→Fin (f n) (x n)
  Free→Fin (hΩ _ _) ()

  -- 字面的起始段: Y₀ ⊕ Stp Y₀ 搬进世界 U
  Y₁ : P.St W₁
  Y₁ = P._⊕⟨_⟩_ P.Y₀ (tt , tt) (P.Stp P.Y₀)

  Z₀ : P.St U
  Z₀ = P.cv X₁ Y₁

  Pfx : P.St U → Set
  Pfx Y = ∀ {t} (T : P.Tg U t U) → HasPfx (P.yc (P.d Z₀) T) (P.yc (P.d Y) T)

  pZ₀ : Pfx Z₀
  pZ₀ T = here

  pfx⊕ : ∀ {Y} (Δ : P.Df U) → Pfx Y → Pfx (P._⊕⟨_⟩_ Y lU Δ)
  pfx⊕ Δ h T = left (h T)

  z≼ : ∀ Δ → R7._≼_ P.zeroD Δ
  z≼ Δ {t} tm = R7.r0 t

  g0 : R7.Good (P.Y₀ {U})
  g0 {t} tm = R7.r0 t

  g⊕ : ∀ {Y Δ} → R7.Good Y → R7._≼_ Δ Δ → R7.Good (P._⊕⟨_⟩_ Y lU Δ)
  g⊕ {Y} {Δ} gy r = R7.⨾≼ {P.d Y} {Δ} {P.d Y} {Δ} gy gy gy r

  g⊕0 : ∀ {Y} → R7.Good Y → R7.Good (P._⊕⟨_⟩_ Y lU P.zeroD)
  g⊕0 {Y} gy = g⊕ {Y} {P.zeroD} gy (z≼ P.zeroD)

  gZ₀ : R7.Good Z₀
  gZ₀ {t} tm = R7.r⨾ t (R7.r0 t) (R7.r0 t) (R7.r0 t) (R7.rnl t (λ _ → x) (λ _ → x) (λ _ → x))
    where
    x = R7.r⨾ t (R7.rΩ t) (R7.rΩ t) (R7.rΩ t) (R7.r0 t)
```

## §3 一个节点

```agda
  module Node {W₀ c} (e : Bd S₁ κ c W₀) (fk : Free (g′ c)) (q₀ : W₀ ≤ʷ U) (w : D Λ U) (Y : P.St U) (gY : R7.Good Y) where
    k : Ht
    k = g′ c

    r : StH W₀ k Λ
    r = sL e hself

    N : P.Df U
    N = P.Run accᴸ (ni r (λ _ _ _ → n1)) q₀ lU hself P.Act w Y

    kk : k ⊲[ U ] Λ
    kk = P.kk r q₀ hself

    A² : P.Ig k U
    A² = P.Ai accᴸ (accL k) r (λ _ _ _ → n1) q₀ kk hself P.Act w

    Y′ : P.St U
    Y′ = P._⊕⟨_⟩_ Y lU P.zeroD

    w′ : D k U
    w′ = n0 ⨾ nw ≤rf n0

    L R : P.Df U
    L = P.Run accᴸ (Ωd k {w₀}) qU lU kk P.Act n0 P.Y₀
    R = P.Run (accL k) (Ωd k {U}) ≤rf lU kk A² w′ Y′

    Tk : P.Tg U k U
    Tk = P.tg ≤rf kk lU

    S0 C0 : P.Df U
    S0 = P.Run (accL k) (P.yc (P.d Z₀) Tk) ≤rf lU kk A² n0 Y
    C0 = P.Run (accL k) (P.yc (P.d Y) Tk) ≤rf lU kk A² n0 Y

    RK : P.Rk k hz U → D hz U
    RK x = P.RKi accᴸ (accL k) r (λ _ _ _ → n1) q₀ lU hself P.Act w Y τ x

    gY′ : R7.Good Y′
    gY′ = g⊕0 {Y} gY

    hA² : GG.NZA A² lU τ
    hA² = GG.na (λ w Y → GG.nz-Step Y τ)

    -- 起始段 ω·(Ω_k ⨾ 0) 的第二份 (Rpt 的第 1 项) 在第 0 层非零: 严格
    w₂ : D k U
    w₂ = w′ ⨾ nw ≤rf (Ωd k ⨾ n0)

    Y₂′ : P.St U
    Y₂′ = P._⊕⟨_⟩_ Y′ lU (P.Run (accL k) (Ωd k ⨾ n0) ≤rf lU kk A² w′ Y′)

    strict : ∀ β → asuc (sum β (R7.o₀ R)) ≤ sum β (R7.o₀ S0)
    strict β = ≤-trans (nz≤ (sum β (R7.o₀ R)) {P.yc (P.Run (accL k) (Ωd k ⨾ n0) ≤rf lU kk A² w₂ Y₂′) τ}
                         (nzL (GG.L3 (accL k) ≤rf lU kk A² τ hA² (nz-Ωd k) w₂ Y₂′)))
                       (≤l 2 (≤-refl _))

    selfN : R7._≼_ N N
    selfN = N7.nodeSelf r (Free→Fin k fk) q₀ hself P.Act (N7.hSt Λ) w Y gY

    low : Pfx Y → ∀ β → one ≤ β → ∀ (lk : LgB k) (ok : ∀ {w} → hs hz ⊲[ w ] k) → asuc (TΛ k lk ok) ≤ sum β (P.yc N τ)
    low pY β oβ lk ok =
      ≤-trans (s≤ (≤-trans (proj₁ (changeW k lk ok fk Λ l o lU qU kk))
                   (proj₁ (N7.ΩdObs k (Free→Fin k fk) kk N7.aᴸ N7.aᴷ qU ≤rf P.Act A² (N7.hSt k) (N7.hSt k) (N7.hSt k)
                             n0 w′ one β P.Y₀ Y′ g0 gY′ (z≤ , z≼ (P.d Y′)) oβ))))
      (≤-trans (strict β)
      (≤-trans (pfxRun (pY Tk) (accL k) ≤rf lU kk A² n0 Y τ β)
               (subst (λ x → sum β (R7.o₀ C0) ≤ sum β (RK x))
                  (sym (rk0 (P.rkT (⊲ᴮ↑ ≤rf kk) (z⊲ᴮ Λ) lU))) (≤l 1 (≤-refl _)))))
```
