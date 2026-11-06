# 新闭项的值 (五): $\Omega$-一步, 与对第 1 层坍缩的公共下界

> 不含记号. 入口 [ValNew](ValNew.lagda.md). 第 4 层: 只新增定理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提.
>
> **`HΩ.Ω-strict`**: 对旧种类 $\kappa$ 的 $\Omega$-层 $h=\mathrm{hΩ}\,(\mathrm{inj}_1\,\kappa)\,g$, $T(g\,c_0)<T(h)$, 其中 $c_0$ 是基世界里 $\kappa$ 的顶坐标. `Ω-strict-bot`: 由 `FabLFReGen.top-base` ($c_0=\bot$) 换成 $T(g\,\bot)<T(h)$. 证明与后继一步同形, 只多一层: 第 0 层目标上闭包结点有损 (`ω⋅ (drp …)`), 取第 0 份, `drp` 不减 `sum` (`drp≤`), 里面是节点在 $g(c_0)$ 上上升的链.
>
> **`base≤`**: 对一切合法且 `NI` 的层 $h$, $T(0)\le T(h)$ (对 $h$ 结构归纳, 用后继、极限、$\Omega$ 三步). $T(0)$ 是第 1 层的坍缩 `col collL hz tt`, 本身也是一个闭项. 这是 `TΛ` 族的一个公共下界, 但 $T(0)$ 的值没有对参照树的定理 (读法见入口, 判断).
>
> 读法 (判断): 这一步只看 $g$ 在基世界顶坐标 (就是 $\bot$) 上的分支; 它与入口 "界与读法" 一节的影子论证一致, 但不是那个论证的证明 (那要反方向的关系).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValNewOm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (s≤; ≤l; l≤; ≤-refl; ≤-trans) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (tpK; w₀; top; topBd; StH; sL; n0; n1; _⨾_; nl; ni; nc; nw)
open import OCF.Align.GenFoldTree using (module Tree; topStepG; accᴸ; accL)
open import OCF.Align.LFReTy using (SL)
open import OCF.Align.NewTwrIf using (col)
open import OCF.Align.NewTwrColl using (module At; one⊞)
open import OCF.Align.FabLFReGen using (GL; LdL; flL; collL; top-base)
open import OCF.Align.ValNewRel
open import OCF.Align.ValNewTw using (module R; module Hs; module Hl; W₁; lW₁)
open import OCF.Align.ValNewStr using (n1≼Ωd)

open Tree SL using (D; D₀; ≤rf; sum; pt; drp; module Om)
open Rel SL
open OmM (topStepG (tpK GL))
open Om (topStepG (tpK GL)) using (Ωd)
```

## §1 `drp` 不减 `sum`

```agda
drp≤  : ∀ {W W′} (x : D₀ W) {b b′} → b ≤ᴬ b′ → sum b x ≤ᴬ sum b′ (drp {W} {W′} x)
drpt≤ : ∀ {W W′} (d : ℕ → D₀ W) {b b′} → b ≤ᴬ b′ → ∀ n → pt b d n ≤ᴬ pt b′ (λ j → drp {W} {W′} (d j)) n
drp≤ n0 h = h
drp≤ n1 h = s≤ h
drp≤ (x ⨾ y) h = drp≤ y (drp≤ x h)
drp≤ (nl d) h = l≤ (λ n → ≤l n (drpt≤ d h n))
drp≤ (ni () u) h
drp≤ (nc (inj₁ _) () u) h
drp≤ (nc (inj₂ _) () u) h
drp≤ (nw p x) h = drp≤ x h
drpt≤ d h zero = h
drpt≤ d h (suc n) = drp≤ (d n) (drpt≤ d h n)
```

## §2 $\Omega$-一步

```agda
module HΩ (κ : K SL) (g : E SL κ → HB (step SL)) (lh : LgB (hΩ (inj₁ κ) g)) (nh : NI (hΩ (inj₁ κ) g)) where
  tp = topStepG (tpK GL)

  c₀ : E SL κ
  c₀ = top (tpK GL) κ (w₀ GL)

  Λb : HB (step SL)
  Λb = one⊞ (hΩ (inj₁ κ) g)

  lb : LgB Λb
  lb = Lg-⊞ (hs hz) (hΩ (inj₁ κ) g) tt lh

  ob : ∀ {w} → hs hz ⊲[ w ] Λb
  ob = ⊞-fst (hs hz) (hΩ (inj₁ κ) g)

  nb : NI Λb
  nb = λ c → NI-⊞ (hs hz) (g c) tt (nh c)

  k : HB (step SL)
  k = one⊞ (g c₀)

  nk : NI k
  nk = NI-⊞ (hs hz) (g c₀) tt (nh c₀)

  module P = At GL LdL flL Λb lb ob
  module TP = R.Two Λb lb ob Λb lb ob nb
  module F₂ = TP.F₂

  r : StH W₁ k Λb
  r = sL {κ = inj₁ κ} {c = c₀} (topBd tp (inj₁ κ) W₁) hself

  wᴾ : D Λb W₁
  wᴾ = n0 ⨾ nw ≤rf n1

  Y₁ᴾ : TP.T₂.St W₁
  Y₁ᴾ = F₂._⊕⟨_⟩_ P.Y₀ lW₁ (F₂.Stp P.Y₀)

  hk : k ⊲[ W₁ ] Λb
  hk = F₂.kk r ≤rf hself

  A² : TP.T₂.Ig k W₁
  A² = F₂.Ai accᴸ (accL k) r (λ _ _ _ → n1) ≤rf hk hself P.Act wᴾ

  Tk : TP.T₂.Tg W₁ k W₁
  Tk = TP.T₂.tg ≤rf hk lW₁

  b₀ : A
  b₀ = sum (asuc azero) (F₂.yc (F₂.Stp P.Y₀) (F₂.τ₀ lW₁))

  RK : F₂.Rk k hz W₁ → D₀ W₁
  RK x = F₂.RKi accᴸ (accL k) r (λ _ _ _ → n1) ≤rf lW₁ hself P.Act wᴾ Y₁ᴾ (F₂.τ₀ lW₁) x

  rk0 : ∀ {k′ m} (x : F₂.Rk k′ hz m) → x ≡ F₂.rise
  rk0 (F₂.keep ())
  rk0 F₂.rise = refl

  dd : D₀ W₁
  dd = F₂.yc (F₂.Run accᴸ (ni r (λ _ _ _ → n1)) ≤rf lW₁ hself P.Act wᴾ Y₁ᴾ) (F₂.τ₀ lW₁)

  dd≡ : dd ≡ RK F₂.rise
  dd≡ = cong RK (rk0 _)

  ch : ℕ → D k W₁ × (D k W₁ × TP.T₂.St W₁)
  ch = F₂.Chn (accL k) hk lW₁ A² Y₁ᴾ

  item : ℕ → D₀ W₁
  item j = F₂.yc (F₂.Run (accL k) (proj₁ (proj₂ (ch j))) ≤rf lW₁ hk A² (proj₁ (ch j)) (proj₂ (proj₂ (ch j)))) (F₂.τ₀ lW₁)

  X : D₀ W₁
  X = item 0

  -- 有损行的第 0 份, drp, 节点上升, 链的第 0 项
  Ω-unfold : sum b₀ X ≤ᴬ col collL (hΩ (inj₁ κ) g) lh
  Ω-unfold = ≤l 1 (≤-trans (subst (λ y → sum b₀ X ≤ᴬ sum b₀ y) (sym dd≡) (≤l 1 (≤-refl _))) (drp≤ dd (≤-refl b₀)))

  module Lo (lgc : LgB (g c₀)) where
    lk : LgB k
    lk = Lg-⊞ (hs hz) (g c₀) tt lgc

    ok : ∀ {w} → hs hz ⊲[ w ] k
    ok = ⊞-fst (hs hz) (g c₀)

    module Q = At GL LdL flL k lk ok
    module TW = R.Two k lk ok Λb lb ob nk

    hA : TW.IgR {k} {W₁} Q.Act A²
    hA = TW.igr (λ p lW′ hw hY → TW.Step-R hY)

    T≤X : col collL (g c₀) lgc ≤ᴬ sum b₀ X
    T≤X = TW.cross {k} {W₁} accᴸ (accL k) {Ωd k {W₁}} {F₂.yc (F₂.d Y₁ᴾ) Tk} (me (ml0 (mr (Ωd-M k nk acc⁺)))) lW₁ hself hk
            {Q.Act} {A²} hA {n0} {n0} mz {Q.Y₀} {Y₁ᴾ} (TW.str TW.zero-R) (sum≥ (asuc azero) (F₂.yc (F₂.Stp P.Y₀) (F₂.τ₀ lW₁)))

  Ω-step : ∀ (lgc : LgB (g c₀)) → col collL (g c₀) lgc ≤ᴬ col collL (hΩ (inj₁ κ) g) lh
  Ω-step lgc = ≤-trans (Lo.T≤X lgc) Ω-unfold

  -- 严格: 链的第 1 项非零 (同 ValNewStr)
  Kn1 : TP.T₁.Ig k W₁
  Kn1 _ _ _ _ = TP.T₁.df (λ _ → n1)

  hK : TP.IgR {k} {W₁} Kn1 A²
  hK = TP.igr (λ p lW′ hw hY → TP.dfr (λ {t} wm tm₁ tm₂ lm → ml0 (mr (n1≼Ωd t))))

  c1 : Rl k n1 (proj₁ (proj₂ (ch 1)))
  c1 = TP.at (TP.Run-R (accL k) (accL k) {n1} {proj₁ (proj₂ (ch 0))} (me (ml0 (mr (n1≼Ωd k)))) ≤rf lW₁ hk hk
                 {Kn1} {A²} hK {n0} {n0} mz {P.Y₀} {Y₁ᴾ} (TP.str TP.zero-R))
             ≤rf hk hk lW₁

  i1 : Rl hz n1 (item 1)
  i1 = TP.at (TP.Run-R (accL k) (accL k) {n1} {proj₁ (proj₂ (ch 1))} c1 ≤rf lW₁ hk hk
                 {Kn1} {A²} hK {n0} {proj₁ (ch 1)} mz {P.Y₀} {proj₂ (proj₂ (ch 1))} (TP.str TP.zero-R))
             ≤rf (z⊲ᴮ Λb) (z⊲ᴮ Λb) lW₁

  Ω-strict : ∀ (lgc : LgB (g c₀)) → asuc (col collL (g c₀) lgc) ≤ᴬ col collL (hΩ (inj₁ κ) g) lh
  Ω-strict lgc = ≤-trans (s≤ (Lo.T≤X lgc))
    (≤l 1 (≤-trans (subst (λ y → asuc (sum b₀ X) ≤ᴬ sum b₀ y) (sym dd≡) (≤l 2 (sum-M acc⁺ i1 (≤-refl (sum b₀ X)))))
                   (drp≤ dd (≤-refl b₀))))

  -- 基世界的顶坐标就是底
  Ω-strict-bot : ∀ (lgb : LgB (g (bot SL κ))) → asuc (col collL (g (bot SL κ)) lgb) ≤ᴬ col collL (hΩ (inj₁ κ) g) lh
  Ω-strict-bot = subst (λ c → (l : LgB (g c)) → asuc (col collL (g c) l) ≤ᴬ col collL (hΩ (inj₁ κ) g) lh) (top-base κ) Ω-strict
```

## §3 公共下界: 第 1 层的坍缩

```agda
base≤ : ∀ h (lh : LgB h) → NI h → col collL hz tt ≤ᴬ col collL h lh
base≤ hz lh nh = ≤-refl _
base≤ (hs b) lh nh = ≤-trans (base≤ b lh nh) (Hs.hs-step b lh lh nh)
base≤ (hl f) lh nh = ≤-trans (base≤ (f 0) (proj₂ lh 0) (nh 0)) (Hl.hl-step f lh nh 0 (proj₂ lh 0))
base≤ (hΩ (inj₁ κ) g) lh nh =
  ≤-trans (base≤ (g (HΩ.c₀ κ g lh nh)) (lgc′) (nh (HΩ.c₀ κ g lh nh))) (HΩ.Ω-step κ g lh nh lgc′)
  where
  lgc′ : LgB (g (HΩ.c₀ κ g lh nh))
  lgc′ = proj₂ lh (HΩ.c₀ κ g lh nh) (lgBd (step SL) {κ = inj₁ κ} (topBd (topStepG (tpK GL)) (inj₁ κ) W₁) lW₁)
base≤ (hΩ (inj₂ _) g) lh ()
```
