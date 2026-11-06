# 新闭项的值 (四): 严格

> 不含记号. 入口 [ValNew](ValNew.lagda.md). 第 4 层: 只新增定理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提.
>
> [ValNewTw](ValNewTw.lagda.md) 的两步把 $T(h)$ 放在链的第 0 项之下. 严格只要链的**第 1 项**在第 0 层读数非零. 做法: 在**同一个实例**里 (`Two` 的两个实例取同一个) 用 `Run-R`, 左边的数据取 $1$, 左边的动作取常数 $1$ (`Kn1`, 对每个目标输出 $1$). 动作相关 (`hK`): 右边的动作 $A^2$ 在目标 $t$ 上输出 $\omega\cdot(\Omega_t⨾\ldots)$, 而 $1\preceq\Omega_t$ 对一切层 $t$ (`n1≼Ωd`). 两次 `Run-R` (链的第 0 项 → 第 1 项的数据 → 第 1 项的读数) 得到 $1\preceq$ 第 1 项, 于是 `sum` 至少加 $1$. 不需要关系的传递性.
>
> 结论: **`TΛn< : asuc (TΛn n) ≤ TΛn (suc n)`**, `TΛ<TΛ₂`, 以及一步定理 `HsS.hs-strict` ($T(h)<T(h+1)$), `HlS.hl-strict` ($T(f\,n)<T(\mathrm{hl}\,f)$).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValNewStr where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (s≤; ≤l; ≤-refl; ≤-trans) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (tpK; n0; n1; _⨾_; nl)
open import OCF.Align.GenFoldTree using (module Tree; topStepG; accL)
open import OCF.Align.LFReTy using (SL)
open import OCF.Align.LFReTower using (tw; Lg-tw; Λ; Lg-Λ; Λn; Lg-Λn; it)
open import OCF.Align.NewTwrIf using (col)
open import OCF.Align.FabLFReGen using (GL; collL; TΛ; TΛ₂; TΛn)
open import OCF.Align.ValNewRel
open import OCF.Align.ValNewTw using (module R; module Hs; module Hl; W₁; lW₁)

open Tree SL using (D; D₀; ≤rf; sum; pt; module Om)
open Rel SL
open Om (topStepG (tpK GL)) using (Ωd)

n1≼Ωd : ∀ t {W} → Rl t n1 (Ωd t {W})
n1≼Ωd hz = m1
n1≼Ωd (hs b) = mr m1
n1≼Ωd (hl f) = mr m1
n1≼Ωd (hΩ κ g) = mr m1
```

## §1 后继一步, 严格

```agda
module HsS (h : HB (step SL)) (lh lh′ : LgB h) (nh : NI h) where
  open Hs h lh lh′ nh

  module TP = R.Two (hs L) lL′ oL′ (hs L) lL′ oL′ nL

  ch : ℕ → D L W₁ × (D L W₁ × TW.T₂.St W₁)
  ch = F₂.Chn (accL L) hk lW₁ A² Y₁ᴾ

  item : ℕ → D₀ W₁
  item j = F₂.yc (F₂.Run (accL L) (proj₁ (proj₂ (ch j))) ≤rf lW₁ hk A² (proj₁ (ch j)) (proj₂ (proj₂ (ch j)))) (F₂.τ₀ lW₁)

  RK≡ : RK F₂.rise ≡ nl item
  RK≡ = refl

  Kn1 : TP.T₁.Ig L W₁
  Kn1 _ _ _ _ = TP.T₁.df (λ _ → n1)

  hK : TP.IgR {L} {W₁} Kn1 A²
  hK = TP.igr (λ p lW′ hw hY → TP.dfr (λ {t} wm tm₁ tm₂ lm → ml0 (mr (n1≼Ωd t))))

  c1 : Rl L n1 (proj₁ (proj₂ (ch 1)))
  c1 = TP.at (TP.Run-R (accL L) (accL L) {n1} {proj₁ (proj₂ (ch 0))} (me (ml0 (mr (n1≼Ωd L)))) ≤rf lW₁ hk hk
                 {Kn1} {A²} hK {n0} {n0} mz {P.Y₀} {Y₁ᴾ} (TP.str TP.zero-R))
             ≤rf hk hk lW₁

  i1 : Rl hz n1 (item 1)
  i1 = TP.at (TP.Run-R (accL L) (accL L) {n1} {proj₁ (proj₂ (ch 1))} c1 ≤rf lW₁ hk hk
                 {Kn1} {A²} hK {n0} {proj₁ (ch 1)} mz {P.Y₀} {proj₂ (proj₂ (ch 1))} (TP.str TP.zero-R))
             ≤rf (z⊲ᴮ (hs L)) (z⊲ᴮ (hs L)) lW₁

  hs-strict : asuc (col collL h lh) ≤ᴬ col collL (hs h) lh′
  hs-strict = ≤-trans (s≤ T≤X)
    (subst (λ y → asuc (sum b₀ X) ≤ᴬ sum b₀ y) (sym dd≡) (≤l 2 (sum-M acc⁺ i1 (≤-refl (sum b₀ X)))))
```

## §2 极限一步, 严格

```agda
module HlS (f : ℕ → HB (step SL)) (lf : LgB (hl f)) (nf : NI (hl f)) (n : ℕ) (lfn : LgB (f n)) where
  open Hl f lf nf n lfn

  module TP = R.Two Λb lb ob Λb lb ob (λ j → NI-⊞ (hs hz) (f j) tt (nf j))

  ch : ℕ → D L W₁ × (D L W₁ × TW.T₂.St W₁)
  ch = F₂.Chn (accL L) hk lW₁ A² (proj₂ (Rp n))

  item : ℕ → D₀ W₁
  item j = F₂.yc (F₂.Run (accL L) (proj₁ (proj₂ (ch j))) ≤rf lW₁ hk A² (proj₁ (ch j)) (proj₂ (proj₂ (ch j)))) (F₂.τ₀ lW₁)

  RK≡ : RK F₂.rise ≡ nl item
  RK≡ = refl

  Kn1 : TP.T₁.Ig L W₁
  Kn1 _ _ _ _ = TP.T₁.df (λ _ → n1)

  hK : TP.IgR {L} {W₁} Kn1 A²
  hK = TP.igr (λ p lW′ hw hY → TP.dfr (λ {t} wm tm₁ tm₂ lm → ml0 (mr (n1≼Ωd t))))

  -- 链第 0 项的数据里有 Ω_L, 因而有 1
  c0 : ∀ m → Rl L n1 (F₂.yc (F₂.d (proj₂ (Rp m))) Tk)
  c0 zero = me (ml0 (mr (n1≼Ωd L)))
  c0 (suc m) = mr (c0 m)

  c1 : Rl L n1 (proj₁ (proj₂ (ch 1)))
  c1 = TP.at (TP.Run-R (accL L) (accL L) {n1} {proj₁ (proj₂ (ch 0))} (c0 n) ≤rf lW₁ hk hk
                 {Kn1} {A²} hK {n0} {n0} mz {P.Y₀} {proj₂ (Rp n)} (TP.str TP.zero-R))
             ≤rf hk hk lW₁

  i1 : Rl hz n1 (item 1)
  i1 = TP.at (TP.Run-R (accL L) (accL L) {n1} {proj₁ (proj₂ (ch 1))} c1 ≤rf lW₁ hk hk
                 {Kn1} {A²} hK {n0} {proj₁ (ch 1)} mz {P.Y₀} {proj₂ (proj₂ (ch 1))} (TP.str TP.zero-R))
             ≤rf (z⊲ᴮ Λb) (z⊲ᴮ Λb) lW₁

  hl-strict : asuc (col collL (f n) lfn) ≤ᴬ col collL (hl f) lf
  hl-strict = ≤-trans (s≤ T≤X)
    (≤l (suc n) (subst (λ y → asuc (sum β X) ≤ᴬ sum β y) (sym dn≡) (≤l 2 (sum-M acc⁺ i1 (≤-refl (sum β X))))))
```

## §3 闭项, 严格

```agda
TΛn< : ∀ n → asuc (TΛn n) ≤ᴬ TΛn (suc n)
TΛn< n =
  ≤-trans (HsS.hs-strict (up (Λn n)) (Lg-up (Λn n) (Lg-Λn n)) (Lg-up (Λn n) (Lg-Λn n)) (NI-up (Λn n)))
          (Hl.hl-step (λ m → up (it (hs (Λn n)) m)) (Lg-up (Λn (suc n)) (Lg-Λn (suc n))) (NI-up (Λn (suc n))) 0
                      (Lg-up (Λn n) (Lg-Λn n)))

TΛ<TΛ₂ : asuc TΛ ≤ᴬ TΛ₂
TΛ<TΛ₂ = TΛn< 0

-- 塔的每一站严格低于对角
stage< : ∀ n → asuc (col collL (up (tw n)) (Lg-up (tw n) (Lg-tw n))) ≤ᴬ TΛ
stage< n = HlS.hl-strict (λ m → up (tw m)) (Lg-up Λ Lg-Λ) (NI-up Λ) n (Lg-up (tw n) (Lg-tw n))
```
