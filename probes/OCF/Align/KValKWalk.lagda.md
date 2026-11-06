# 单层 `nκ` (一): 回灌的一格就是一个区间和

> 不含记号. 入口 [KValK](KValK.lagda.md). `nκ` 在目标第 0 层的一格是 `SumOneFold.Walk`: 沿路径 $a\lhd b$ 逐层走分支. 本文证它与把区间和 `Cut u b p` (一棵第 1 层树, [KValCut](KValCut.lagda.md)) 当输入走一次**值相同** (两个方向 `WCf`, `WCb`), 以及 `Walk` 的输出路径一致 (`cohW`).
>
> 证法: 两边按路径平行展开 (`Walk` 与 `Run (Cut …)` 的子句一一对应), 每一格一次 `snd-lo` 的自比 (分支对层单调 `KMono`, 取 $c\le c$). 坐标两边不同 (`Walk` 带 `co ⨾ Cut …`, `Run` 带 `w ⨾ nw self …`), `lo` 档的语义不读第 1 层坐标, 所以无关. 极限一段, `Walk` 的状态由 `WRp` 推进, `Run` 由 `Rpt` 推进, 两者逐项平行.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValKWalk where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nw; sum; pt; cnt; Cut; tailP)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree
open import OCF.Align.KValSem
open import OCF.Align.KValSound
```

## §1 记号

```agda
module W {V : A} (u : Bk V) (mono : KMono u) (s : Sd) (o : Ok s s) where
  κ : C.Tg azero (W s)
  κ = inj₁ (κ₀ (ll s))

  DLe : F.Df (W s) → F.Df (W s) → Set
  DLe Δ Δ′ = ∀ c c′ → c ≤ c′ → sum c (F.yc Δ κ tt) ≤ sum c′ (F.yc Δ′ κ tt)

  Wk : ∀ b {a} (p : a ⊲ b) (ap : V ⊲ a) (lb : Lg b) (bV : b ⊲ W s) → D one (W s) → F.St (W s) → F.Df (W s)
  Wk b p ap lb bV co Y = F.Walk ac₁ u b p ap lb bV (lW s) (ll s) (act s) co Y

  RC : ∀ b {a} (p : a ⊲ b) (ap : V ⊲ a) (lb : Lg b) (bV : b ⊲ W s) → D one (W s) → F.St (W s) → F.Df (W s)
  RC b p ap lb bV w Y = Rn s (Cut u b p ap lb bV) C.self w Y

  fV : ∀ {f : ℕ → A} → alim f ⊲ W s → ∀ m → f m ⊲ W s
  fV bV m = ⊲-tr (C.lim m C.self) bV

  -- 一格的自比 (跨两个状态)
  cell : ∀ {c} (p : V ⊲ c) (l : Lg c) (X : c ⊲ W s) w w′ Y Y′ → Cx lo s s Y Y′ → DLe (Rn s (u p l) X w Y) (Rn s (u p l) X w′ Y′)
  cell {c} p l X w w′ Y Y′ k = snd-lo (mono p p l l (≤-refl c)) s s o X X w w′ Y Y′ k
```

## §2 `Walk` 的输出路径一致

```agda
  cohW : ∀ b {a} (p : a ⊲ b) (ap : V ⊲ a) (lb : Lg b) (bV : b ⊲ W s) co Y → CohY Y → CohD (Wk b p ap lb bV co Y)
  cohW b C.self ap lb bV co Y cY = cohZ
  cohW (asuc c) (C.suc p) ap lb bV co Y cY =
    coh⨾ cP (coh₁ (u (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bV) (lW s) (ll s) (act s) _ _ (c0 o) (coh⊕ cY cP))
    where cP = cohW c p ap lb (⊲-tr (C.suc C.self) bV) co Y cY
  cohW (alim f) {a} (C.lim n p) ap (stp , wl) bV co Y cY = coh⨾ cP (cohNl (λ m → cohW _ (stp (m + n)) _ (wl (suc (m + n))) _ _ _ (cRw m)))
    where
    cP = cohW (f n) p ap (wl n) (fV bV n) co Y cY
    R′ = F.WRp ac₁ u f stp wl p ap (fV bV) (lW s) (ll s) (act s) (co ⨾ Cut u (f n) p ap (wl n) (fV bV n)) (Y F.⊕ Wk (f n) p ap (wl n) (fV bV n) co Y)
    cRw : ∀ m → CohY (proj₂ (R′ m))
    cRw zero = coh⊕ cY cP
    cRw (suc m) = coh⊕ (cRw m) (cohW _ (stp (m + n)) _ (wl (suc (m + n))) _ _ _ (cRw m))
```

## §3 两个方向

```agda
  WCf : ∀ b {a} (p : a ⊲ b) (ap : V ⊲ a) (lb : Lg b) (bV : b ⊲ W s) co w Y Y′ → Cx lo s s Y Y′ →
        DLe (Wk b p ap lb bV co Y) (RC b p ap lb bV w Y′)
  WCf b C.self ap lb bV co w Y Y′ k e e′ eb = eb
  WCf (asuc c) (C.suc p) ap lb bV co w Y Y′ k e e′ eb =
    cell (⊲-tr ap p) lb X _ _ _ _ nk _ _ (IH e e′ eb)
    where
    X = ⊲-tr (C.suc C.self) bV
    IH = WCf c p ap lb X co w Y Y′ k
    nk = cx (coh⊕ (cL k) (cohW c p ap lb X co Y (cL k))) (cR₁ s (c0 o) (Cut u c p ap lb X) C.self w Y′ (cR k)) (IH _ _ (vle k)) tt
  WCf (alim f) {a} (C.lim n p) ap (stp , wl) bV co w Y Y′ k e e′ eb = l≤ (λ m → ≤l m (proj₁ (go m)))
    where
    IH = WCf (f n) p ap (wl n) (fV bV n) co w Y Y′ k
    R′ = F.WRp ac₁ u f stp wl p ap (fV bV) (lW s) (ll s) (act s) (co ⨾ Cut u (f n) p ap (wl n) (fV bV n)) (Y F.⊕ Wk (f n) p ap (wl n) (fV bV n) co Y)
    Fi = λ m → Cut u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV bV (suc (m + n)))
    P′ = F.Rpt ac₁ Fi C.self (lW s) (ll s) (act s) (w ⨾ nw C.self (Cut u (f n) p ap (wl n) (fV bV n))) (Y′ F.⊕ RC (f n) p ap (wl n) (fV bV n) w Y′)
    it : ∀ m co₁ w₁ Y₁ Y₁′ → Cx lo s s Y₁ Y₁′ → DLe (Wk _ (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV bV (suc (m + n))) co₁ Y₁)
                                                    (RC _ (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV bV (suc (m + n))) w₁ Y₁′)
    it m = WCf _ (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV bV (suc (m + n)))
    go : ∀ m → (pt (sum e (F.yc (Wk (f n) p ap (wl n) (fV bV n) co Y) κ tt))
                   (λ j → F.yc (Wk _ (stp (j + n)) (⊲-tr ap (tailP f stp p j)) (wl (suc (j + n))) (fV bV (suc (j + n))) (proj₁ (R′ j)) (proj₂ (R′ j))) κ tt) m
                ≤ pt (sum e′ (F.yc (RC (f n) p ap (wl n) (fV bV n) w Y′) κ tt))
                   (λ j → F.yc (Rn s (Fi j) C.self (proj₁ (P′ j)) (proj₂ (P′ j))) κ tt) m) ×
               Cx lo s s (proj₂ (R′ m)) (proj₂ (P′ m))
    go zero = IH e e′ eb ,
              cx (coh⊕ (cL k) (cohW (f n) p ap (wl n) (fV bV n) co Y (cL k)))
                 (cR₁ s (c0 o) (Cut u (f n) p ap (wl n) (fV bV n)) C.self w Y′ (cR k)) (IH _ _ (vle k)) tt
    go (suc m) = let (gb , gk) = go m
                     H = it m (proj₁ (R′ m)) (proj₁ (P′ m)) (proj₂ (R′ m)) (proj₂ (P′ m)) gk
                 in H _ _ gb ,
                    cx (coh⊕ (cL gk) (cohW _ (stp (m + n)) _ (wl (suc (m + n))) _ _ _ (cL gk)))
                       (cR₁ s (c0 o) (Fi m) C.self _ _ (cR gk)) (H _ _ (vle gk)) tt

  WCb : ∀ b {a} (p : a ⊲ b) (ap : V ⊲ a) (lb : Lg b) (bV : b ⊲ W s) co w Y Y′ → Cx lo s s Y Y′ →
        DLe (RC b p ap lb bV w Y) (Wk b p ap lb bV co Y′)
  WCb b C.self ap lb bV co w Y Y′ k e e′ eb = eb
  WCb (asuc c) (C.suc p) ap lb bV co w Y Y′ k e e′ eb =
    cell (⊲-tr ap p) lb X _ _ _ _ nk _ _ (IH e e′ eb)
    where
    X = ⊲-tr (C.suc C.self) bV
    IH = WCb c p ap lb X co w Y Y′ k
    nk = cx (cR₁ s (c0 o) (Cut u c p ap lb X) C.self w Y (cL k)) (coh⊕ (cR k) (cohW c p ap lb X co Y′ (cR k))) (IH _ _ (vle k)) tt
  WCb (alim f) {a} (C.lim n p) ap (stp , wl) bV co w Y Y′ k e e′ eb = l≤ (λ m → ≤l m (proj₁ (go m)))
    where
    IH = WCb (f n) p ap (wl n) (fV bV n) co w Y Y′ k
    R′ = F.WRp ac₁ u f stp wl p ap (fV bV) (lW s) (ll s) (act s) (co ⨾ Cut u (f n) p ap (wl n) (fV bV n)) (Y′ F.⊕ Wk (f n) p ap (wl n) (fV bV n) co Y′)
    Fi = λ m → Cut u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV bV (suc (m + n)))
    P′ = F.Rpt ac₁ Fi C.self (lW s) (ll s) (act s) (w ⨾ nw C.self (Cut u (f n) p ap (wl n) (fV bV n))) (Y F.⊕ RC (f n) p ap (wl n) (fV bV n) w Y)
    it : ∀ m co₁ w₁ Y₁ Y₁′ → Cx lo s s Y₁ Y₁′ → DLe (RC _ (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV bV (suc (m + n))) w₁ Y₁)
                                                    (Wk _ (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV bV (suc (m + n))) co₁ Y₁′)
    it m = WCb _ (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV bV (suc (m + n)))
    go : ∀ m → (pt (sum e (F.yc (RC (f n) p ap (wl n) (fV bV n) w Y) κ tt))
                   (λ j → F.yc (Rn s (Fi j) C.self (proj₁ (P′ j)) (proj₂ (P′ j))) κ tt) m
                ≤ pt (sum e′ (F.yc (Wk (f n) p ap (wl n) (fV bV n) co Y′) κ tt))
                   (λ j → F.yc (Wk _ (stp (j + n)) (⊲-tr ap (tailP f stp p j)) (wl (suc (j + n))) (fV bV (suc (j + n))) (proj₁ (R′ j)) (proj₂ (R′ j))) κ tt) m) ×
               Cx lo s s (proj₂ (P′ m)) (proj₂ (R′ m))
    go zero = IH e e′ eb ,
              cx (cR₁ s (c0 o) (Cut u (f n) p ap (wl n) (fV bV n)) C.self w Y (cL k))
                 (coh⊕ (cR k) (cohW (f n) p ap (wl n) (fV bV n) co Y′ (cR k))) (IH _ _ (vle k)) tt
    go (suc m) = let (gb , gk) = go m
                     H = it m (proj₁ (R′ m)) (proj₁ (P′ m)) (proj₂ (P′ m)) (proj₂ (R′ m)) gk
                 in H _ _ gb ,
                    cx (cR₁ s (c0 o) (Fi m) C.self _ _ (cL gk))
                       (coh⊕ (cR gk) (cohW _ (stp (m + n)) _ (wl (suc (m + n))) _ _ _ (cR gk))) (H _ _ (vle gk)) tt
```
