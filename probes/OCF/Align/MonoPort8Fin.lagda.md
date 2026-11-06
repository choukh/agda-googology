# Ω-极限高度 (三): 回灌第一格的每个坐标

> 入口 [MonoPort8](MonoPort8.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> [MonoPort8Om](MonoPort8Om.lagda.md) 只用了第 $0$ 格的第一个节点 (坐标 $0$). 这里对第 $0$ 格的**每个**坐标 $f(m)$ ($V_0=\lim_m f(m)$, $f(m)=1+m$ 的字面) 做同一件事. 新的只有一件: 节点 $m$ 的状态 `WR m` 里含前 $m$ 个节点的折叠输出 (分支读坐标的 `ni`), 它的自洽由 `MonoPort7Node.nodeSelf` 逐段给出 (`gWR`), 世界都是 $V_0$, 不跨世界. 链的第 $0$ 项里的第一次 $\Omega_{g(f(m))}$ 仍在状态读数的最左边 (`HasPfx`, `pfxY`), 前缀引理 `pfxRun` 把它取出来.
>
> 结论 `growΩf`: $g$ 的分支都不含 Ω-极限 ⇒ 对一切 $m$, $T_{g(f(m))} < T_{\mathrm{h\Omega}\,g}$. 特例 `growΩᴴf`: 对 $\Omega$ 本身无前提; 因为 `emb (f m)` 就是有限高度 $m+1$ (`embf`), 合上 `MonoPort8Om.growΩᴴ₀` 得 `growΩᴴN`: 一切有限 $n$, $T_n < T_\Omega$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort8Fin where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (module At; TΛ; one)
open import OCF.Align.HtFeedGrow using (NZ₀; nz≤; sum≥; nzR; module G)
open import OCF.Align.HtFeedHt using (emb; Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtCrossVSim using (Free)
open import OCF.Align.HtCrossVInst using (free-emb)
open import OCF.Align.MonoPort8Sim using (changeW)
open import OCF.Align.MonoPort8Om using (module Om; drp≤; growΩᴴ₀)
open import OCF.Align.MonoPort6Chain using (N; lgN)
```

## 1 前缀

`HasPfx s z`: $s$ 是 $z$ 沿 `⨾` 左脊的一段. 折叠在左脊上先走左边, 状态与上下文不变, 所以和不低于 $s$ 的折叠的和.

```agda
data HasPfx {k : H} {V : A} (s : D k V) : D k V → Set where
  here : HasPfx s s
  left : ∀ {x y} → HasPfx s x → HasPfx s (x ⨾ y)

module Pf (g : A → H) (l : LgH (hΩ g)) where
  module P = At (hΩ g) l
  pfxRun : ∀ {k V₀ W} {s z : D k V₀} → HasPfx s z → ∀ (ac : AccY k) (q : V₀ ⊲ W) (lW : Lg W) (ll : k ⊲[ W ] hΩ g) (A₀ : P.Ig k W) w Y
           (T : P.Tg W hz W) β → sum β (P.yc (P.Run ac s q lW ll A₀ w Y) T) ≤ sum β (P.yc (P.Run ac z q lW ll A₀ w Y) T)
  pfxRun here ac q lW ll A₀ w Y T β = ≤-refl _
  pfxRun (left h) ac q lW ll A₀ w Y T β = ≤-trans (pfxRun h ac q lW ll A₀ w Y T β) (sum≥ _ _)
```

## 2 第 0 格的坐标与状态

```agda
module Fn (g : A → H) (l : LgH (hΩ g)) (fg : ∀ c → Free (g c)) where
  open Om g l hiding (k; lk; kk₀; A²; w′; Y′; L; R; z₀; C0; module Low; growΩ₀; gY′; strict)
  open Pf g l using (pfxRun)

  f : ℕ → A
  f = pt {one} one (λ _ → n1 ⨾ n0)

  stp : ∀ n → f n ⊲ f (suc n)
  stp = proj₁ lV₀

  wl : ∀ n → Lg (f n)
  wl = proj₂ lV₀

  fV : ∀ m → f m ⊲ V₀
  fV m = ⊲-tr (C.lim m C.self) C.self

  -- 坐标 0 那一段 (Walk (f 0)), 之后 WRp 的起点
  W0 : P.Df V₀
  W0 = P.Walk accᴸ u (f 0) (C.suc C.self) C.self (wl 0) (fV 0) lV₀ hself A₀ (P.co c₀) (P.Sv c₀)

  co₁ : D Λ V₀
  co₁ = P.co c₀ ⨾ Cut u (f 0) (C.suc C.self) C.self (wl 0) (fV 0)

  WR : ℕ → D Λ V₀ × P.St V₀
  WR = P.WRp {n = 0} accᴸ u f stp wl (C.suc C.self) C.self fV lV₀ hself A₀ co₁ (P._⊕⟨_⟩_ (P.Sv c₀) lV₀ W0)

  -- 坐标 f (m + 0) 那一段与它的节点
  cm : ℕ → A
  cm m = f (m + 0)

  Em : ℕ → P.Df V₀
  Em m = P.Walk accᴸ u (f (suc (m + 0))) (stp (m + 0)) (⊲-tr C.self (tailP f stp (C.suc C.self) m)) (wl (suc (m + 0)))
           (fV (suc (m + 0))) lV₀ hself A₀ (proj₁ (WR m)) (proj₂ (WR m))

  rm : ∀ m → StH (cm m) (g (cm m)) Λ
  rm m = sL C.self hself

  qm : ∀ m → cm m ⊲ V₀
  qm m = C.lim (suc (m + 0)) (C.suc C.self)

  wm : ℕ → D Λ V₀
  wm m = proj₁ (WR m) ⨾ n0

  Ym : ℕ → P.St V₀
  Ym m = P._⊕⟨_⟩_ (proj₂ (WR m)) lV₀ P.zeroD

  Nm : ℕ → P.Df V₀
  Nm m = P.Run accᴸ (ni (rm m) (λ _ _ _ → n1)) (qm m) lV₀ hself A₀ (wm m) (Ym m)

  -- 第 0 格的读数: 坐标 0 一段, 再接 E m
  β : A
  β = sum b (P.yc W0 τ)

  E : ℕ → D₀ V₀
  E m = P.yc (Em m) τ

  cell≡ : sum b (P.yc (P.κΔ accᴸ u hself P.Act c₀) τ) ≡ alim (pt β E)
  cell≡ = refl

  Em≡ : ∀ m → E m ≡ (n0 ⨾ P.yc (Nm m) τ)
  Em≡ m = refl
```

## 3 状态: 自洽, 非零, 前缀

```agda
  hSΛ = N7.hSt Λ

  gW0 : R7._≼_ W0 W0
  gW0 = R7.⨾≼ {P.zeroD} {N0} {P.zeroD} {N0} (z≼ P.zeroD) (z≼ P.zeroD) (z≼ P.zeroD)
          (N7.nodeSelf r₀ (Free→Fin (g azero) (fg azero)) q₀ hself A₀ hSΛ w₀ Y₂ (g⊕0 {P.Sv c₀} gSv))

  gE : ∀ m → R7.Good (proj₂ (WR m)) → R7._≼_ (Em m) (Em m)
  gE m gy = R7.⨾≼ {P.zeroD} {Nm m} {P.zeroD} {Nm m} (z≼ P.zeroD) (z≼ P.zeroD) (z≼ P.zeroD)
              (N7.nodeSelf (rm m) (Free→Fin (g (cm m)) (fg (cm m))) (qm m) hself A₀ hSΛ (wm m) (Ym m) (g⊕0 {proj₂ (WR m)} gy))

  gWR : ∀ m → R7.Good (proj₂ (WR m))
  gWR zero = R7.⨾≼ {P.d (P.Sv c₀)} {W0} {P.d (P.Sv c₀)} {W0} gSv gSv gSv gW0
  gWR (suc m) = R7.⨾≼ {P.d (proj₂ (WR m))} {Em m} {P.d (proj₂ (WR m))} {Em m} (gWR m) (gWR m) (gWR m) (gE m (gWR m))

  iWR : ∀ m → GG.Inv (proj₂ (WR m))
  iWR zero = GG.inv⊕ lV₀ W0 (GG.invcv (P.wv c₀) iY₁)
  iWR (suc m) = GG.inv⊕ lV₀ (Em m) (iWR m)

  nzE : ∀ m → NZ₀ (E m)
  nzE m = nzR (GG.L2 accᴸ (rm m) (qm m) lV₀ hself A₀ (wm m) (Ym m) τ hA (GG.inv⊕ lV₀ P.zeroD (iWR m)))

  -- 状态的读数以 Sv 的读数为最左一段
  pfxY : ∀ m {t} (T : P.Tg V₀ t V₀) → HasPfx (P.yc (P.d (P.Sv c₀)) T) (P.yc (P.d (proj₂ (WR m))) T)
  pfxY zero T = left here
  pfxY (suc m) T = left (pfxY m T)

  ptβ : ∀ m → β ≤ pt β E m
  ptβ zero = ≤-refl β
  ptβ (suc m) = ≤-trans (ptβ m) (sum≥ (pt β E m) (E m))

  oneβ : ∀ m → one ≤ pt β E m
  oneβ m = ≤-trans one≤b (≤-trans (sum≥ b (P.yc W0 τ)) (ptβ m))
```

## 4 坐标 $f(m)$ 的下界

同 `MonoPort8Om` §4, 状态换成 `Ym m`, 底换成第 $m$ 段之前的部分和 `pt β E m`, 前缀多走 $m$ 步 (`pfxRun`).

```agda
  module Low (m : ℕ) where
    k : H
    k = g (cm m)

    kk : k ⊲[ V₀ ] Λ
    kk = P.kk (rm m) (qm m) hself

    A² : P.Ig k V₀
    A² = P.Ai accᴸ (accL k) (rm m) (λ _ _ _ → n1) (qm m) kk hself A₀ (wm m)

    Y′ : P.St V₀
    Y′ = P._⊕⟨_⟩_ (Ym m) lV₀ P.zeroD

    w′ : D k V₀
    w′ = n0 ⨾ nw C.self n0

    L R : P.Df V₀
    L = P.Run accᴸ (Ωd k {azero}) (z⊲ V₀) lV₀ kk P.Act n0 P.Y₀
    R = P.Run (accL k) (Ωd k {V₀}) C.self lV₀ kk A² w′ Y′

    Tk : P.Tg V₀ k V₀
    Tk = P.tg C.self kk lV₀

    S0 C0 : P.Df V₀
    S0 = P.Run (accL k) (P.yc (P.d (P.Sv c₀)) Tk) C.self lV₀ kk A² n0 (Ym m)
    C0 = P.Run (accL k) (P.yc (P.d (Ym m)) Tk) C.self lV₀ kk A² n0 (Ym m)

    gY′ : R7.Good Y′
    gY′ = g⊕0 {Ym m} (g⊕0 {proj₂ (WR m)} (gWR m))

    RK : P.Rk k hz V₀ → D₀ V₀
    RK x = P.RKi accᴸ (accL k) (rm m) (λ _ _ _ → n1) (qm m) lV₀ hself A₀ (wm m) (Ym m) τ x

    low : ∀ (lk : LgH k) → TΛ k lk ≤ sum (pt β E m) (P.yc (Nm m) τ)
    low lk =
      ≤-trans (proj₁ (changeW k lk (fg (cm m)) Λ l lV₀ (z⊲ V₀) kk))
      (≤-trans (proj₁ (N7.ΩdObs k (Free→Fin k (fg (cm m))) kk N7.aᴸ N7.aᴷ (z⊲ V₀) C.self P.Act A² (N7.hSt k) (N7.hSt k) (N7.hSt k)
                         n0 w′ one (pt β E m) P.Y₀ Y′ g0 gY′ (z≤ , z≼ (P.d Y′)) (oneβ m)))
      (≤-trans (≤l 1 (≤-refl (sum (pt β E m) (R7.o₀ R))))
      (≤-trans (pfxRun (left (pfxY m Tk)) (accL k) C.self lV₀ kk A² n0 (Ym m) τ (pt β E m))
               (subst (λ x → sum (pt β E m) (R7.o₀ C0) ≤ sum (pt β E m) (RK x))
                  (sym (rk0 (P.rkT (⊲ᴴ↑ C.self kk) (z⊲ᴴ Λ) lV₀))) (≤l 1 (≤-refl _))))))
```

## 5 结论

```agda
  growΩf′ : ∀ m (lk : LgH (g (cm m))) → asuc (TΛ (g (cm m)) lk) ≤ TΛ Λ l
  growΩf′ m lk =
    ≤-trans (s≤ (Low.low m lk))
    (≤-trans (nz≤ (pt β E (suc m)) (nzE (suc m)))
    (≤-trans (≤l (suc (suc m)) (≤-refl (pt β E (suc (suc m)))))
    (≤-trans (drp≤ (≤-refl b) (P.yc (P.κΔ accᴸ u hself P.Act c₀) τ)) (≤l 1 (≤-refl _)))))

  growΩf : ∀ m (lk : LgH (g (f m))) → asuc (TΛ (g (f m)) lk) ≤ TΛ Λ l
  growΩf m = subst (λ j → ∀ (lk : LgH (g (f j))) → asuc (TΛ (g (f j)) lk) ≤ TΛ Λ l) (+-identityʳ m) (growΩf′ m)

-- Ω 本身: 第 0 格的每个坐标, 无前提
growΩᴴf : ∀ m (lk : LgH (emb (Fn.f emb Lg-Ωᴴ (λ c → free-emb c) m))) →
          asuc (TΛ (emb (Fn.f emb Lg-Ωᴴ (λ c → free-emb c) m)) lk) ≤ TΛ Ωᴴ Lg-Ωᴴ
growΩᴴf = Fn.growΩf emb Lg-Ωᴴ (λ c → free-emb c)

-- f m 是 1 + m 的字面: emb (f m) 就是有限高度 m + 1
embf : ∀ m → emb (Fn.f emb Lg-Ωᴴ (λ c → free-emb c) m) ≡ N (suc m)
embf zero = refl
embf (suc m) = cong hs (embf m)

-- 一切有限高度 n: T_n < T_Ω, 无前提
growΩᴴN : ∀ n → asuc (TΛ (N n) (lgN n)) ≤ TΛ Ωᴴ Lg-Ωᴴ
growΩᴴN zero = growΩᴴ₀
growΩᴴN (suc m) = subst (λ h → ∀ (lk : LgH h) → asuc (TΛ h lk) ≤ TΛ Ωᴴ Lg-Ωᴴ) (embf m) (growΩᴴf m) (lgN (suc m))
```
