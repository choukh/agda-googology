# Ω-极限高度 (五): 一个世界里沿 `Walk` 的路径归纳

> 入口 [MonoPort9](MonoPort9.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 实例 $\Lambda=\mathrm{h\Omega}\,g$ (分支都不含 Ω-极限), 一个固定的世界 $U$. 回灌的一格是 `Walk accᴸ u b p …`: 沿坐标的路径 $p : a \lhd b$ 走, 每遇到一个后继 $c+1$ 就折叠一个节点 $u(c)$ (层 $g(c)$). 这里对 `Walk` 的路径归纳 (节点、`suc`、`lim` 三句, `WRp` 的状态; 与 `Walk` 同一个停机度量: 坐标 $b$ 的结构):
>
> - `Walked b p lb c`: 坐标 $c$ 被这次 `Walk` 走过 (四个构造子, 照 `Walk` 的三句).
> - `WG`: 状态自洽 (`MonoPort7Rel.Good`, 世界 $U$) ⇒ `Walk` 的输出与自己相关. 每个节点用 `MonoPort7Node.nodeSelf`.
> - `Node.low`: 一个节点 (坐标 $c$, 层 $g(c)$), 状态自洽且以字面的起始段 $Z_0=\mathrm{cv}\,X_1\,Y_1$ 的读数为最左一段 (`Pfx`) ⇒ $T_{g(c)} <$ 节点在第 0 层的和 (底 $\beta\ge 1$ 任意). 与 `MonoPort8Fin.Fn.Low` 同四步, 只是状态、上下文、底是变量; 严格不靠下一个节点, 而靠起始段 $\omega\cdot(\Omega_{g(c)}⨾0)$ 的第二份 (`strict`).
> - **`WL`**: 对一切走过的 $c$, $T_{g(c)} <$ 这次 `Walk` 在第 0 层的和.
>
> 世界只有一个 ($U$), 不跨世界. 跨世界的部分在 [MonoPort9Walk](MonoPort9Walk.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort9One where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (module At; TΛ; one)
open import OCF.Align.HtFeedGrow using (NZ₀; nzL; nz≤; sum≥; nz-Ωd; module G)
open import OCF.Align.HtCrossVSim using (Free)
open import OCF.Align.MonoPort8Sim using (changeW)
open import OCF.Align.MonoPort8Om using (module Om)
open import OCF.Align.MonoPort8Fin using (HasPfx; here; left; module Pf)
import OCF.Align.MonoPort7Rel as Rl
import OCF.Align.MonoPort7Node as Nd
```

## 1 走过的坐标

照 `Walk` 的三句: `self` 不走; `suc p` 先走 $p$ 再走 $c$ 本身; `lim n p` 先走 $p$, 再走第 $m$ 段 (`stp (m + n)`).

```agda
data Walked : ∀ b {a} → a ⊲ b → Lg b → A → Set where
  wHere  : ∀ {c a} {p : a ⊲ c} {lb : Lg c} → Walked (asuc c) (C.suc p) lb c
  wThere : ∀ {c a c₀} {p : a ⊲ c} {lb : Lg c} → Walked c p lb c₀ → Walked (asuc c) (C.suc p) lb c₀
  wPre   : ∀ {f a n c₀} {p : a ⊲ f n} {stp : ∀ n → f n ⊲ f (suc n)} {wl : ∀ n → Lg (f n)} →
          Walked (f n) p (wl n) c₀ → Walked (alim f) (C.lim n p) (stp , wl) c₀
  wSub   : ∀ {f a n c₀} {p : a ⊲ f n} {stp : ∀ n → f n ⊲ f (suc n)} {wl : ∀ n → Lg (f n)} m →
          Walked (f (suc (m + n))) (stp (m + n)) (wl (suc (m + n))) c₀ → Walked (alim f) (C.lim n p) (stp , wl) c₀
```

## 2 一个世界

```agda
module One (g : A → H) (l : LgH (hΩ g)) (fg : ∀ c → Free (g c)) (U : A) (lU : Lg U) (X₁ : one ⊲ U) where
  open Om g l using (Λ; module P; module GG; u; Y₁; rk0; Free→Fin)
  open Pf g l using (pfxRun)

  module R7 = Rl Λ l {U} lU (z⊲ᴴ Λ)
  module N7 = Nd Λ l {U} lU (z⊲ᴴ Λ)

  τ : P.Tg U hz U
  τ = P.τ₀ lU

  -- 字面的起始段: Y₁ = Y₀ ⊕ Step Y₀ 搬进世界 U
  Z₀ : P.St U
  Z₀ = P.cv X₁ Y₁

  Pfx : P.St U → Set
  Pfx Y = ∀ {t} (T : P.Tg U t U) → HasPfx (P.yc (P.d Z₀) T) (P.yc (P.d Y) T)

  pfx⊕ : ∀ {Y} (Δ : P.Df U) → Pfx Y → Pfx (P._⊕⟨_⟩_ Y lU Δ)
  pfx⊕ Δ h T = left (h T)

  z≼ : ∀ Δ → R7._≼_ P.zeroD Δ
  z≼ Δ {t} tm = R7.r0 t

  g0 : R7.Good (P.Y₀ {U})
  g0 {t} tm = R7.r0 t

  g⊕ : ∀ {Y Δ} → R7.Good Y → R7._≼_ Δ Δ → R7.Good (P._⊕⟨_⟩_ Y lU Δ)
  g⊕ {Y} {Δ} gy r = R7.⨾≼ {P.d Y} {Δ} {P.d Y} {Δ} gy gy gy r

  gZ₀ : R7.Good Z₀
  gZ₀ {t} tm = R7.r⨾ t (R7.r0 t) (R7.r0 t) (R7.r0 t) (R7.rnl t (λ _ → x) (λ _ → x) (λ _ → x))
    where
    x = R7.r⨾ t (R7.rΩ t) (R7.rΩ t) (R7.rΩ t) (R7.r0 t)

  hSΛ = N7.hSt Λ
```

## 3 一个节点

```agda
  module Node {c : A} (q₀ : c ⊲ U) (w : D Λ U) (Y : P.St U) (gY : R7.Good Y) where
    k : H
    k = g c

    r : StH c k Λ
    r = sL C.self hself

    N : P.Df U
    N = P.Run accᴸ (ni r (λ _ _ _ → n1)) q₀ lU hself P.Act w Y

    kk : k ⊲[ U ] Λ
    kk = P.kk r q₀ hself

    A² : P.Ig k U
    A² = P.Ai accᴸ (accL k) r (λ _ _ _ → n1) q₀ kk hself P.Act w

    Y′ : P.St U
    Y′ = P._⊕⟨_⟩_ Y lU P.zeroD

    w′ : D k U
    w′ = n0 ⨾ nw C.self n0

    L R : P.Df U
    L = P.Run accᴸ (Ωd k {azero}) (z⊲ U) lU kk P.Act n0 P.Y₀
    R = P.Run (accL k) (Ωd k {U}) C.self lU kk A² w′ Y′

    Tk : P.Tg U k U
    Tk = P.tg C.self kk lU

    S0 C0 : P.Df U
    S0 = P.Run (accL k) (P.yc (P.d Z₀) Tk) C.self lU kk A² n0 Y
    C0 = P.Run (accL k) (P.yc (P.d Y) Tk) C.self lU kk A² n0 Y

    RK : P.Rk k hz U → D₀ U
    RK x = P.RKi accᴸ (accL k) r (λ _ _ _ → n1) q₀ lU hself P.Act w Y τ x

    gY′ : R7.Good Y′
    gY′ = g⊕ {Y} {P.zeroD} gY (z≼ P.zeroD)

    hA² : GG.NZA A² lU τ
    hA² = GG.na (λ w Y → GG.nz-Step Y τ)

    -- 起始段 ω·(Ω_k ⨾ 0) 的第二份在第 0 层非零: 严格
    -- 第二份的上下文与状态 (Rpt 的第 1 项)
    w₂ : D k U
    w₂ = w′ ⨾ nw C.self (Ωd k ⨾ n0)

    Y₂′ : P.St U
    Y₂′ = P._⊕⟨_⟩_ Y′ lU (P.Run (accL k) (Ωd k ⨾ n0) C.self lU kk A² w′ Y′)

    strict : ∀ β → asuc (sum β (R7.o₀ R)) ≤ sum β (R7.o₀ S0)
    strict β = ≤-trans (nz≤ (sum β (R7.o₀ R)) {P.yc (P.Run (accL k) (Ωd k ⨾ n0) C.self lU kk A² w₂ Y₂′) τ}
                         (nzL (GG.L3 (accL k) C.self lU kk A² τ hA² (nz-Ωd k) w₂ Y₂′)))
                       (≤l 2 (≤-refl _))

    selfN : R7._≼_ N N
    selfN = N7.nodeSelf r (Free→Fin k (fg c)) q₀ hself P.Act hSΛ w Y gY

    low : Pfx Y → ∀ β → one ≤ β → ∀ (lk : LgH k) → asuc (TΛ k lk) ≤ sum β (P.yc N τ)
    low pY β oβ lk =
      ≤-trans (s≤ (≤-trans (proj₁ (changeW k lk (fg c) Λ l lU (z⊲ U) kk))
                   (proj₁ (N7.ΩdObs k (Free→Fin k (fg c)) kk N7.aᴸ N7.aᴷ (z⊲ U) C.self P.Act A² (N7.hSt k) (N7.hSt k) (N7.hSt k)
                             n0 w′ one β P.Y₀ Y′ g0 gY′ (z≤ , z≼ (P.d Y′)) oβ))))
      (≤-trans (strict β)
      (≤-trans (pfxRun (pY Tk) (accL k) C.self lU kk A² n0 Y τ β)
               (subst (λ x → sum β (R7.o₀ C0) ≤ sum β (RK x))
                  (sym (rk0 (P.rkT (⊲ᴴ↑ C.self kk) (z⊲ᴴ Λ) lU))) (≤l 1 (≤-refl _)))))
```

## 4 `Walk` 的自洽与路径归纳

```agda
  WK : ∀ b {a} → a ⊲ b → azero ⊲ a → Lg b → b ⊲ U → D Λ U → P.St U → P.Df U
  WK b p ap lb bV co Y = P.Walk accᴸ u b p ap lb bV lU hself P.Act co Y

  WRK : ∀ (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} → a ⊲ f n → azero ⊲ a → (∀ m → f m ⊲ U) →
        D Λ U → P.St U → ℕ → D Λ U × P.St U
  WRK f stp wl p ap fV co Y = P.WRp accᴸ u f stp wl p ap fV lU hself P.Act co Y

  WG  : ∀ b {a} (p : a ⊲ b) (ap : azero ⊲ a) (lb : Lg b) (bV : b ⊲ U) co Y → R7.Good Y → R7._≼_ (WK b p ap lb bV co Y) (WK b p ap lb bV co Y)
  WRG : ∀ (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} (p : a ⊲ f n) (ap : azero ⊲ a) (fV : ∀ m → f m ⊲ U) co Y →
        R7.Good Y → ∀ m → R7.Good (proj₂ (WRK f stp wl p ap fV co Y m))

  WG b C.self ap lb bV co Y gY = z≼ P.zeroD
  WG (asuc c) (C.suc p) ap lb bV co Y gY =
    R7.⨾≼ {W₁} {N₁} {W₁} {N₁} gW gW gW
      (Node.selfN (⊲-tr (C.suc C.self) bV) (co ⨾ Cut u c p ap lb (⊲-tr (C.suc C.self) bV)) (P._⊕⟨_⟩_ Y lU W₁) (g⊕ {Y} {W₁} gY gW))
    where
    W₁ = WK c p ap lb (⊲-tr (C.suc C.self) bV) co Y
    gW = WG c p ap lb (⊲-tr (C.suc C.self) bV) co Y gY
    N₁ = Node.N (⊲-tr (C.suc C.self) bV) (co ⨾ Cut u c p ap lb (⊲-tr (C.suc C.self) bV)) (P._⊕⟨_⟩_ Y lU W₁) (g⊕ {Y} {W₁} gY gW)
  WG (alim f) {a} (C.lim n p) ap (stp , wl) bV co Y gY =
    R7.⨾≼ {W₁} {P.nlᴰ F} {W₁} {P.nlᴰ F} gW gW gW (R7.nl≼ {F} {F} (λ m → gF m) (λ m → gF m) (λ m → gF m))
    where
    W₁ = WK (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) co Y
    gW = WG (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) co Y gY
    co₁ = co ⨾ Cut u (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV)
    Y₁′ = P._⊕⟨_⟩_ Y lU W₁
    fV = λ m₁ → ⊲-tr (C.lim m₁ C.self) bV
    F : ℕ → P.Df U
    F m = WK (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bV)
            (proj₁ (WRK f stp wl p ap fV co₁ Y₁′ m)) (proj₂ (WRK f stp wl p ap fV co₁ Y₁′ m))
    gF : ∀ m → R7._≼_ (F m) (F m)
    gF m = WG (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bV)
             (proj₁ (WRK f stp wl p ap fV co₁ Y₁′ m)) (proj₂ (WRK f stp wl p ap fV co₁ Y₁′ m))
             (WRG f stp wl p ap fV co₁ Y₁′ (g⊕ {Y} {W₁} gY gW) m)

  WRG f stp wl p ap fV co Y gY zero = gY
  WRG f stp wl {n = n} p ap fV co Y gY (suc m) =
    g⊕ {proj₂ (WRK f stp wl p ap fV co Y m)} {Δ} (WRG f stp wl p ap fV co Y gY m)
      (WG (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n)))
          (proj₁ (WRK f stp wl p ap fV co Y m)) (proj₂ (WRK f stp wl p ap fV co Y m)) (WRG f stp wl p ap fV co Y gY m))
    where
    Δ = WK (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n)))
           (proj₁ (WRK f stp wl p ap fV co Y m)) (proj₂ (WRK f stp wl p ap fV co Y m))

  WRP : ∀ (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} (p : a ⊲ f n) (ap : azero ⊲ a) (fV : ∀ m → f m ⊲ U) co Y →
        Pfx Y → ∀ m → Pfx (proj₂ (WRK f stp wl p ap fV co Y m))
  WRP f stp wl p ap fV co Y pY zero = pY
  WRP f stp wl p ap fV co Y pY (suc m) T = left (WRP f stp wl p ap fV co Y pY m T)
```

**路径归纳.** 对一切走过的 $c$, $T_{g(c)}$ 严格低于这次 `Walk` 的和.

```agda
  WL : ∀ b {a} (p : a ⊲ b) (ap : azero ⊲ a) (lb : Lg b) (bV : b ⊲ U) co Y → R7.Good Y → Pfx Y → ∀ β → one ≤ β →
       ∀ {c} → Walked b p lb c → ∀ (lk : LgH (g c)) → asuc (TΛ (g c) lk) ≤ sum β (P.yc (WK b p ap lb bV co Y) τ)
  WL (asuc c) (C.suc p) ap lb bV co Y gY pY β oβ wHere lk =
    Node.low (⊲-tr (C.suc C.self) bV) (co ⨾ Cut u c p ap lb (⊲-tr (C.suc C.self) bV)) (P._⊕⟨_⟩_ Y lU W₁) (g⊕ {Y} {W₁} gY gW) (λ T → left (pY T))
      (sum β (P.yc W₁ τ)) (≤-trans oβ (sum≥ β (P.yc W₁ τ))) lk
    where
    W₁ = WK c p ap lb (⊲-tr (C.suc C.self) bV) co Y
    gW = WG c p ap lb (⊲-tr (C.suc C.self) bV) co Y gY
  WL (asuc c) (C.suc p) ap lb bV co Y gY pY β oβ (wThere h) lk =
    ≤-trans (WL c p ap lb (⊲-tr (C.suc C.self) bV) co Y gY pY β oβ h lk) (sum≥ _ _)
  WL (alim f) (C.lim n p) ap (stp , wl) bV co Y gY pY β oβ (wPre h) lk =
    ≤-trans (WL (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) co Y gY pY β oβ h lk) (≤l 0 (≤-refl _))
  WL (alim f) {a} (C.lim n p) ap (stp , wl) bV co Y gY pY β oβ (wSub m h) lk =
    ≤-trans (WL (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bV)
               (proj₁ (WRK f stp wl p ap fV co₁ Y₁′ m)) (proj₂ (WRK f stp wl p ap fV co₁ Y₁′ m))
               (WRG f stp wl p ap fV co₁ Y₁′ (g⊕ {Y} {W₁} gY gW) m) (WRP f stp wl p ap fV co₁ Y₁′ (λ T → left (pY T)) m)
               (pt β₁ E m) (≤-trans oβ (≤-trans (sum≥ β (P.yc W₁ τ)) (ptβ m))) h lk)
            (≤l (suc m) (≤-refl _))
    where
    W₁ = WK (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) co Y
    gW = WG (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) co Y gY
    co₁ = co ⨾ Cut u (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV)
    Y₁′ = P._⊕⟨_⟩_ Y lU W₁
    fV = λ m₁ → ⊲-tr (C.lim m₁ C.self) bV
    β₁ = sum β (P.yc W₁ τ)
    E : ℕ → D₀ U
    E m = P.yc (WK (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bV)
                  (proj₁ (WRK f stp wl p ap fV co₁ Y₁′ m)) (proj₂ (WRK f stp wl p ap fV co₁ Y₁′ m))) τ
    ptβ : ∀ m → β₁ ≤ pt β₁ E m
    ptβ zero = ≤-refl β₁
    ptβ (suc m) = ≤-trans (ptβ m) (sum≥ (pt β₁ E m) (E m))
```
