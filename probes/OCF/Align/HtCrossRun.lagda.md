# 跨高度 (二): 两个实例的折叠相关

> 不含记号. 入口 [HtCross](HtCross.lagda.md). 两个折叠实例 $(\Lambda_1, l_1)$, $(\Lambda_2, l_2)$ ([HtFeedFold](HtFeedFold.lagda.md), $S=\cdot\omega$), **最高层与合法性证明都可以不同**. 输入在 [HtCrossSim](HtCrossSim.lagda.md) 的关系 `Rl` 下相关, 层到最高层的路径两边各给 ($ll_1 : ly\lhd\Lambda_1$, $ll_2 : ly\lhd\Lambda_2$), 状态、上下文、动作都相关, 则输出在一切**两边共有的目标**上相关 (`Run-R`, 与折叠的十六个函数逐个对应).
>
> - 目标的关系 `DfR`: 同一个目标层 $t$, 同一个世界 $m$, 同一个世界路径与合法性证明, **目标到最高层的路径两边各取** ($t\lhd\Lambda_1$, $t\lhd\Lambda_2$).
> - 判定 (`rk-rel`): 两个实例对同一对 (节点层 $k$, 目标 $t$) 的比较给出同一个判定 (保留或上升), 不论路径与最高层. 这一条不用 `Funext`: 保留说 $k\lhd t$ 严格, 上升说没有严格的 $k\lhd t$ (`Valid`), 两者矛盾由层的非自反 (`irrS`) 给出.
> - 第 0 层的输出两边**相等** (`StR` 的 `zR`), 因为回灌的世界是它的和. 这一步用 `eq0`, 前提 `Funext`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 停机: 与折叠同一个度量 (先比节点层的可达性, 再比输入的关系推导).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtCrossRun where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (ω⋅)
import OCF.Align.HtFeedFold as Fold
open import OCF.Align.HtCrossSim
```

## §1 判定的有效性 (一个实例)

```agda
module Val (Λ : H) (lΛ : LgH Λ) where
  open Fold ω⋅ Λ lΛ

  Valid : ∀ {k t m} → Rk k t m → Set
  Valid (keep R) = ⊤
  Valid {k} {t} {m} rise = StH m k t → ⊥

  rkS-valid : ∀ {k t m} (p : k ⊲[ m ] t) → Valid (rkS p)
  rkS-valid hself = λ R → irrS (accL _) R
  rkS-valid (hsuc p) = tt
  rkS-valid (hlim n p) = tt
  rkS-valid (hLim e p) = tt

  rk-valid : ∀ {k t m} (km : k ⊲[ m ] Λ) (tm : t ⊲[ m ] Λ) (lm : Lg m) → Valid (rkT km tm lm)
  rk-valid km tm lm with cmpH km tm lm lΛ
  ... | inj₁ t⊲k = λ R → irrS (accL _) (Sk R t⊲k)
  ... | inj₂ k⊲t = rkS-valid k⊲t
```

## §2 两个实例

```agda
module Two (fe : Funext) (Λ₁ : H) (l₁ : LgH Λ₁) (Λ₂ : H) (l₂ : LgH Λ₂) where
  module F₁ = Fold ω⋅ Λ₁ l₁
  module F₂ = Fold ω⋅ Λ₂ l₂
  module V₁ = Val Λ₁ l₁
  module V₂ = Val Λ₂ l₂

  record DfR {W : A} (Δ₁ : F₁.Df W) (Δ₂ : F₂.Df W) : Set where
    constructor dfr
    field
      at : ∀ {t m} (wm : W ⊲ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : Lg m) →
           Rl t (F₁.yc Δ₁ (F₁.tg wm tm₁ lm)) (F₂.yc Δ₂ (F₂.tg wm tm₂ lm))
  open DfR public

  record StR {W : A} (Y₁ : F₁.St W) (Y₂ : F₂.St W) : Set where
    constructor str
    field
      dR : DfR (F₁.d Y₁) (F₂.d Y₂)
      zR : F₁.z Y₁ ≡ F₂.z Y₂
  open StR public

  record IgR {ly : H} {W : A} (A₁ : F₁.Ig ly W) (A₂ : F₂.Ig ly W) : Set where
    constructor igr
    field
      ig : ∀ {W′} (p : W ⊲ W′) (lW′ : Lg W′) {w₁ w₂ : D ly W′} → Rl ly w₁ w₂ →
           {Y₁ : F₁.St W′} {Y₂ : F₂.St W′} → StR Y₁ Y₂ → DfR (A₁ p lW′ w₁ Y₁) (A₂ p lW′ w₂ Y₂)
  open IgR public

  zero-R : ∀ {W} → DfR (F₁.zeroD {W}) (F₂.zeroD {W})
  zero-R = dfr (λ wm tm₁ tm₂ lm → s0)

  ⨾-R : ∀ {W} {a₁ b₁ : F₁.Df W} {a₂ b₂ : F₂.Df W} → DfR a₁ a₂ → DfR b₁ b₂ → DfR (a₁ F₁.⨾ᴰ b₁) (a₂ F₂.⨾ᴰ b₂)
  ⨾-R ha hb = dfr (λ wm tm₁ tm₂ lm → s⨾ (at ha wm tm₁ tm₂ lm) (at hb wm tm₁ tm₂ lm))

  nl-R : ∀ {W} {G₁ : ℕ → F₁.Df W} {G₂ : ℕ → F₂.Df W} → (∀ n → DfR (G₁ n) (G₂ n)) → DfR (F₁.nlᴰ G₁) (F₂.nlᴰ G₂)
  nl-R h = dfr (λ wm tm₁ tm₂ lm → sl (λ n → at (h n) wm tm₁ tm₂ lm))

  ⊕-R : ∀ {W} (lW : Lg W) {Y₁ : F₁.St W} {Y₂ : F₂.St W} {Δ₁ : F₁.Df W} {Δ₂ : F₂.Df W} → StR Y₁ Y₂ → DfR Δ₁ Δ₂ →
        StR (F₁._⊕⟨_⟩_ Y₁ lW Δ₁) (F₂._⊕⟨_⟩_ Y₂ lW Δ₂)
  ⊕-R lW hY hΔ = str (⨾-R (dR hY) hΔ) (cong₂ _⨾_ (zR hY) (eq0 fe accᴸ (at hΔ C.self (z⊲ᴴ Λ₁) (z⊲ᴴ Λ₂) lW)))

  cv-R : ∀ {W W′} (q : W ⊲ W′) {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ → StR (F₁.cv q Y₁) (F₂.cv q Y₂)
  cv-R q hY = str (dfr (λ wm tm₁ tm₂ lm → at (dR hY) (⊲-tr q wm) tm₁ tm₂ lm)) refl

  Step-R : ∀ {W} {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ → DfR (F₁.Step Y₁) (F₂.Step Y₂)
  Step-R hY = dfr (λ {t} wm tm₁ tm₂ lm → sl (λ _ → s⨾ (Ωd-R t accᴸ) (at (dR hY) wm tm₁ tm₂ lm)))

  Ig↾-R : ∀ {ly W W′} (p : W ⊲ W′) {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → IgR (F₁.Ig↾ p A₁) (F₂.Ig↾ p A₂)
  Ig↾-R p hA = igr (λ p′ → ig hA (⊲-tr p p′))

  data RkR {k t : H} {m : A} : F₁.Rk k t m → F₂.Rk k t m → Set where
    kp : ∀ {R R′} → RkR (F₁.keep R) (F₂.keep R′)
    rs : RkR F₁.rise F₂.rise

  rk-rel : ∀ {k t m} (x₁ : F₁.Rk k t m) (x₂ : F₂.Rk k t m) → V₁.Valid x₁ → V₂.Valid x₂ → RkR x₁ x₂
  rk-rel (F₁.keep R) (F₂.keep R′) _ _ = kp
  rk-rel (F₁.keep R) F₂.rise _ v = ⊥-elim (v R)
  rk-rel F₁.rise (F₂.keep R) v _ = ⊥-elim (v R)
  rk-rel F₁.rise F₂.rise _ _ = rs

  -- 两个实例对同一对 (k, t) 判定相同, 路径与最高层任取
  rkT-rel : ∀ {k t m} (km₁ : k ⊲[ m ] Λ₁) (tm₁ : t ⊲[ m ] Λ₁) (km₂ : k ⊲[ m ] Λ₂) (tm₂ : t ⊲[ m ] Λ₂) (lm : Lg m) →
            RkR (F₁.rkT km₁ tm₁ lm) (F₂.rkT km₂ tm₂ lm)
  rkT-rel km₁ tm₁ km₂ tm₂ lm = rk-rel _ _ (V₁.rk-valid km₁ tm₁ lm) (V₂.rk-valid km₂ tm₂ lm)

  data ClR {W W₀ : A} {ly : H} : F₁.Cl W W₀ ly → F₂.Cl W W₀ ly → Set where
    clr : ∀ {v lv wv a ap av} {S₁ : F₁.St v} {S₂ : F₂.St v} {co₁ co₂ : D ly v} → StR S₁ S₂ → Rl ly co₁ co₂ →
          ClR (F₁.mkCl v lv wv a ap av S₁ co₁) (F₂.mkCl v lv wv a ap av S₂ co₂)

  Br : ∀ {ly W₀ k} (r : StH W₀ k ly) → Set
  Br {ly} {W₀} r = ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′

  HU : ∀ {ly W₀ k} (r₁ r₂ : StH W₀ k ly) → Br r₁ → Br r₂ → Set
  HU {ly} {W₀} r₁ r₂ u₁ u₂ = ∀ {W′} (p : W₀ ⊲ W′) (l : Lg W′) y₁ y₂ → RelA (accK r₁) (outS r₁ y₁) (outS r₂ y₂) → Rl ly (u₁ p l y₁) (u₂ p l y₂)

  HK : ∀ {ly W₀} → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → Set
  HK {ly} {W₀} u₁ u₂ = ∀ {c} (p : W₀ ⊲ c) (l : Lg c) → Rl ly (u₁ p l) (u₂ p l)
```

## §3 折叠, 逐个对应

```agda
  Run-R   : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {x₁ x₂ : D ly W₀} → Rl ly x₁ x₂ → (q₀ : W₀ ⊲ W) (lW : Lg W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            DfR (F₁.Run ac₁ x₁ q₀ lW ll₁ A₁ w₁ Y₁) (F₂.Run ac₂ x₂ q₀ lW ll₂ A₂ w₂ Y₂)
  Rpt-R   : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {G₁ G₂ : ℕ → D ly W₀} → (∀ n → Rl ly (G₁ n) (G₂ n)) → (q₀ : W₀ ⊲ W) (lW : Lg W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ → ∀ n →
            Rl ly (proj₁ (F₁.Rpt ac₁ G₁ q₀ lW ll₁ A₁ w₁ Y₁ n)) (proj₁ (F₂.Rpt ac₂ G₂ q₀ lW ll₂ A₂ w₂ Y₂ n)) ×
            StR (proj₂ (F₁.Rpt ac₁ G₁ q₀ lW ll₁ A₁ w₁ Y₁ n)) (proj₂ (F₂.Rpt ac₂ G₂ q₀ lW ll₂ A₂ w₂ Y₂ n))
  RunNi-R : ∀ {ly W₀ W k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ⊲ W) (lW : Lg W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            DfR (F₁.RunNi ac₁ ac′₁ r₁ u₁ q₀ lW ll₁ A₁ w₁ Y₁) (F₂.RunNi ac₂ ac′₂ r₂ u₂ q₀ lW ll₂ A₂ w₂ Y₂)
  Ai-R    : ∀ {ly W₀ W k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ⊲ W) (hk₁ : F₁.LW k W) (hk₂ : F₂.LW k W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ →
            IgR (F₁.Ai ac₁ ac′₁ r₁ u₁ q₀ hk₁ ll₁ A₁ w₁) (F₂.Ai ac₂ ac′₂ r₂ u₂ q₀ hk₂ ll₂ A₂ w₂)
  Chn-R   : ∀ {k W} (ac′₁ ac′₂ : AccY k) (hk₁ : F₁.LW k W) (hk₂ : F₂.LW k W) (lW : Lg W) {A₁ : F₁.Ig k W} {A₂ : F₂.Ig k W} → IgR A₁ A₂ →
            {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ → ∀ n →
            Rl k (proj₁ (F₁.Chn ac′₁ hk₁ lW A₁ Y₁ n)) (proj₁ (F₂.Chn ac′₂ hk₂ lW A₂ Y₂ n)) ×
            (Rl k (proj₁ (proj₂ (F₁.Chn ac′₁ hk₁ lW A₁ Y₁ n))) (proj₁ (proj₂ (F₂.Chn ac′₂ hk₂ lW A₂ Y₂ n))) ×
             StR (proj₂ (proj₂ (F₁.Chn ac′₁ hk₁ lW A₁ Y₁ n))) (proj₂ (proj₂ (F₂.Chn ac′₂ hk₂ lW A₂ Y₂ n))))
  RKi-R   : ∀ {ly W₀ W k t m} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ⊲ W) (lW : Lg W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            (wm : W ⊲ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : Lg m) {x₁ : F₁.Rk k t m} {x₂ : F₂.Rk k t m} → RkR x₁ x₂ →
            Rl t (F₁.RKi ac₁ ac′₁ r₁ u₁ q₀ lW ll₁ A₁ w₁ Y₁ (F₁.tg wm tm₁ lm) x₁) (F₂.RKi ac₂ ac′₂ r₂ u₂ q₀ lW ll₂ A₂ w₂ Y₂ (F₂.tg wm tm₂ lm) x₂)
  BNi-R   : ∀ {ly W₀ W k W′} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ⊲ W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            (hk₁ : F₁.LW k W) (hk₂ : F₂.LW k W) (p : W ⊲ W′) (lW′ : Lg W′) {z₁ z₂ : D k W′} → Rl k z₁ z₂ →
            DfR (F₁.BNi ac₁ ac′₁ r₁ u₁ q₀ ll₁ A₁ w₁ Y₁ hk₁ p lW′ z₁) (F₂.BNi ac₂ ac′₂ r₂ u₂ q₀ ll₂ A₂ w₂ Y₂ hk₂ p lW′ z₂)
  Walk-R  : ∀ {ly W₀ V₁} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            ∀ b {a} (P : a ⊲ b) (ap : W₀ ⊲ a) (lb : Lg b) (bV : b ⊲ V₁) (lV : Lg V₁) (ll₁ : F₁.LW ly V₁) (ll₂ : F₂.LW ly V₁)
            {A₁ : F₁.Ig ly V₁} {A₂ : F₂.Ig ly V₁} → IgR A₁ A₂ → {co₁ co₂ : D ly V₁} → Rl ly co₁ co₂ → {Y₁ : F₁.St V₁} {Y₂ : F₂.St V₁} → StR Y₁ Y₂ →
            DfR (F₁.Walk ac₁ u₁ b P ap lb bV lV ll₁ A₁ co₁ Y₁) (F₂.Walk ac₂ u₂ b P ap lb bV lV ll₂ A₂ co₂ Y₂)
  WRp-R   : ∀ {ly W₀ V₁ a n} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) (P : a ⊲ f n) (ap : W₀ ⊲ a) (fV : ∀ m → f m ⊲ V₁) (lV : Lg V₁)
            (ll₁ : F₁.LW ly V₁) (ll₂ : F₂.LW ly V₁)
            {A₁ : F₁.Ig ly V₁} {A₂ : F₂.Ig ly V₁} → IgR A₁ A₂ → {co₁ co₂ : D ly V₁} → Rl ly co₁ co₂ → {Y₁ : F₁.St V₁} {Y₂ : F₂.St V₁} → StR Y₁ Y₂ → ∀ m →
            Rl ly (proj₁ (F₁.WRp ac₁ u₁ f stp wl P ap fV lV ll₁ A₁ co₁ Y₁ m)) (proj₁ (F₂.WRp ac₂ u₂ f stp wl P ap fV lV ll₂ A₂ co₂ Y₂ m)) ×
            StR (proj₂ (F₁.WRp ac₁ u₁ f stp wl P ap fV lV ll₁ A₁ co₁ Y₁ m)) (proj₂ (F₂.WRp ac₂ u₂ f stp wl P ap fV lV ll₂ A₂ co₂ Y₂ m))
  RunK-R  : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            (q₀ : W₀ ⊲ W) (lW : Lg W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            DfR (F₁.RunK ac₁ u₁ q₀ lW ll₁ A₁ w₁ Y₁) (F₂.RunK ac₂ u₂ q₀ lW ll₂ A₂ w₂ Y₂)
  RKy-R   : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            (q₀ : W₀ ⊲ W) (lW : Lg W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            ∀ t {m} (wm : W ⊲ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : Lg m) →
            Rl t (F₁.RKy ac₁ u₁ q₀ lW ll₁ A₁ w₁ Y₁ t (F₁.tg wm tm₁ lm)) (F₂.RKy ac₂ u₂ q₀ lW ll₂ A₂ w₂ Y₂ t (F₂.tg wm tm₂ lm))
  RKk-R   : ∀ {ly W₀ W t m} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            (q₀ : W₀ ⊲ W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            (wm : W ⊲ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : Lg m) (zz₁ zz₂ : NZ t) →
            Rl t (F₁.RKk ac₁ u₁ q₀ ll₁ A₁ w₁ Y₁ (F₁.tg wm tm₁ lm) zz₁) (F₂.RKk ac₂ u₂ q₀ ll₂ A₂ w₂ Y₂ (F₂.tg wm tm₂ lm) zz₂)
  Kp-R    : ∀ {ly W₀ W W⁺} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            (q₀ : W₀ ⊲ W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            (wu : W ⊲ W⁺) (lW⁺ : Lg W⁺) →
            DfR (F₁.Kp ac₁ u₁ q₀ ll₁ A₁ w₁ Y₁ wu lW⁺) (F₂.Kp ac₂ u₂ q₀ ll₂ A₂ w₂ Y₂ wu lW⁺)
  Kb-R    : ∀ {ly W₀ W W⁺ c} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            (q₀ : W₀ ⊲ W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            (wu : W ⊲ W⁺) (lW⁺ : Lg W⁺) (p : W⁺ ⊲ c) (lc : Lg c) →
            DfR (F₁.Kb ac₁ u₁ q₀ ll₁ A₁ w₁ Y₁ wu lW⁺ p lc) (F₂.Kb ac₂ u₂ q₀ ll₂ A₂ w₂ Y₂ wu lW⁺ p lc)
  κc-R    : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            (q₀ : W₀ ⊲ W) (lW : Lg W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ → ∀ n →
            ClR (F₁.κc ac₁ u₁ q₀ lW ll₁ A₁ w₁ Y₁ n) (F₂.κc ac₂ u₂ q₀ lW ll₂ A₂ w₂ Y₂ n)
  κs-R    : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W) {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ →
            {c₁ : F₁.Cl W W₀ ly} {c₂ : F₂.Cl W W₀ ly} → ClR c₁ c₂ →
            ClR (F₁.mkCl (sum (F₁.v c₁) (F₁.yc (F₁.κΔ ac₁ u₁ ll₁ A₁ c₁) (F₁.τ₀ (F₁.lv c₁)))) (Lg-sum (F₁.v c₁) (F₁.yc (F₁.κΔ ac₁ u₁ ll₁ A₁ c₁) (F₁.τ₀ (F₁.lv c₁))) (F₁.lv c₁))
                   (⊲-tr (F₁.wv c₁) (sum-fst (F₁.v c₁) (F₁.yc (F₁.κΔ ac₁ u₁ ll₁ A₁ c₁) (F₁.τ₀ (F₁.lv c₁))))) (F₁.v c₁) (⊲-tr (F₁.ap c₁) (F₁.av c₁))
                   (sum-fst (F₁.v c₁) (F₁.yc (F₁.κΔ ac₁ u₁ ll₁ A₁ c₁) (F₁.τ₀ (F₁.lv c₁))))
                   (F₁.cv (sum-fst (F₁.v c₁) (F₁.yc (F₁.κΔ ac₁ u₁ ll₁ A₁ c₁) (F₁.τ₀ (F₁.lv c₁)))) (F₁._⊕⟨_⟩_ (F₁.Sv c₁) (F₁.lv c₁) (F₁.κΔ ac₁ u₁ ll₁ A₁ c₁)))
                   (nw (sum-fst (F₁.v c₁) (F₁.yc (F₁.κΔ ac₁ u₁ ll₁ A₁ c₁) (F₁.τ₀ (F₁.lv c₁)))) (F₁.co c₁ ⨾ Cut u₁ (F₁.v c₁) (F₁.av c₁) (F₁.ap c₁) (F₁.lv c₁) C.self)))
                (F₂.mkCl (sum (F₂.v c₂) (F₂.yc (F₂.κΔ ac₂ u₂ ll₂ A₂ c₂) (F₂.τ₀ (F₂.lv c₂)))) (Lg-sum (F₂.v c₂) (F₂.yc (F₂.κΔ ac₂ u₂ ll₂ A₂ c₂) (F₂.τ₀ (F₂.lv c₂))) (F₂.lv c₂))
                   (⊲-tr (F₂.wv c₂) (sum-fst (F₂.v c₂) (F₂.yc (F₂.κΔ ac₂ u₂ ll₂ A₂ c₂) (F₂.τ₀ (F₂.lv c₂))))) (F₂.v c₂) (⊲-tr (F₂.ap c₂) (F₂.av c₂))
                   (sum-fst (F₂.v c₂) (F₂.yc (F₂.κΔ ac₂ u₂ ll₂ A₂ c₂) (F₂.τ₀ (F₂.lv c₂))))
                   (F₂.cv (sum-fst (F₂.v c₂) (F₂.yc (F₂.κΔ ac₂ u₂ ll₂ A₂ c₂) (F₂.τ₀ (F₂.lv c₂)))) (F₂._⊕⟨_⟩_ (F₂.Sv c₂) (F₂.lv c₂) (F₂.κΔ ac₂ u₂ ll₂ A₂ c₂)))
                   (nw (sum-fst (F₂.v c₂) (F₂.yc (F₂.κΔ ac₂ u₂ ll₂ A₂ c₂) (F₂.τ₀ (F₂.lv c₂)))) (F₂.co c₂ ⨾ Cut u₂ (F₂.v c₂) (F₂.av c₂) (F₂.ap c₂) (F₂.lv c₂) C.self)))
  κd-R    : ∀ {ly W₀ W m} (ac₁ ac₂ : AccY ly) {u₁ u₂ : ∀ {c} → W₀ ⊲ c → Lg c → D ly c} → HK u₁ u₂ →
            (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W) {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ →
            {c₁ : F₁.Cl W W₀ ly} {c₂ : F₂.Cl W W₀ ly} → ClR c₁ c₂ →
            Rl hz (drp {_} {m} (F₁.yc (F₁.κΔ ac₁ u₁ ll₁ A₁ c₁) (F₁.τ₀ (F₁.lv c₁)))) (drp {_} {m} (F₂.yc (F₂.κΔ ac₂ u₂ ll₂ A₂ c₂) (F₂.τ₀ (F₂.lv c₂))))
```

**情形.** 每一条都照折叠的一个子句写. `si` 处两边各匹配可达性证明; 节点的分支参数经 `conv` 搬过去.

```agda
  Run-R ac₁ ac₂ s0 q₀ lW ll₁ ll₂ hA hw hY = zero-R
  Run-R ac₁ ac₂ s1 q₀ lW ll₁ ll₂ hA hw hY = ig hA C.self lW hw hY
  Run-R ac₁ ac₂ (s⨾ hx hy) q₀ lW ll₁ ll₂ hA hw hY =
    ⨾-R (Run-R ac₁ ac₂ hx q₀ lW ll₁ ll₂ hA hw hY)
        (Run-R ac₁ ac₂ hy q₀ lW ll₁ ll₂ hA (s⨾ hw (sw hx)) (⊕-R lW hY (Run-R ac₁ ac₂ hx q₀ lW ll₁ ll₂ hA hw hY)))
  Run-R ac₁ ac₂ (sl h) q₀ lW ll₁ ll₂ hA hw hY =
    nl-R (λ n → Run-R ac₁ ac₂ (h n) q₀ lW ll₁ ll₂ hA (proj₁ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)) (proj₂ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)))
  Run-R ac₁ ac₂ (sw {p = p} hx) q₀ lW ll₁ ll₂ hA hw hY = Run-R ac₁ ac₂ hx (⊲-tr p q₀) lW ll₁ ll₂ hA hw hY
  Run-R (acc f₁) (acc f₂) (si {R = r₁} {R′ = r₂} h) q₀ lW ll₁ ll₂ hA hw hY =
    RunNi-R (acc f₁) (acc f₂) (f₁ r₁) (f₂ r₂) r₁ r₂ h q₀ lW ll₁ ll₂ hA hw hY
  Run-R ac₁ ac₂ (sκ h) q₀ lW ll₁ ll₂ hA hw hY = RunK-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY

  Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY zero = hw , hY
  Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY (suc n) =
    s⨾ (proj₁ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)) (sw (h n)) ,
    ⊕-R lW (proj₂ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n))
      (Run-R ac₁ ac₂ (h n) q₀ lW ll₁ ll₂ hA (proj₁ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)) (proj₂ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)))

  RunNi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY =
    dfr (λ wm tm₁ tm₂ lm →
      RKi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm
        (rkT-rel (⊲ᴴ↑ wm (F₁.kk r₁ q₀ ll₁)) tm₁ (⊲ᴴ↑ wm (F₂.kk r₂ q₀ ll₂)) tm₂ lm))

  Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ hk₁ hk₂ ll₁ ll₂ hA hw =
    igr (λ p lW′ {z₁} {z₂} rz hY′ →
      Run-R ac₁ ac₂ (hu (⊲-tr q₀ p) lW′ (inS r₁ z₁) (inS r₂ z₂) (conv (accK r₁) r₁ r₂ rz)) C.self lW′ (⊲ᴴ↑ p ll₁) (⊲ᴴ↑ p ll₂) (Ig↾-R p hA)
        (s⨾ (sw hw) (Int-R ac′₁ ac′₂ rz C.self lW′ (NZ-S r₁) (NZ-S r₂) (mkOf r₁ (⊲-tr q₀ p)) (mkOf r₂ (⊲-tr q₀ p))
                       (λ p′ l′ r′ → hu (⊲-tr (⊲-tr q₀ p) p′) l′ _ _ (conv (accK r₁) r₁ r₂ r′)) s0))
        hY′)

  Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY zero = s0 , (at (dR hY) C.self hk₁ hk₂ lW , hY)
  Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY (suc n) =
    s⨾ (proj₁ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)) (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))) ,
    (at (Run-R ac′₁ ac′₂ (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))) C.self lW hk₁ hk₂ hA
              (proj₁ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)) (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))))
        C.self hk₁ hk₂ lW ,
     ⊕-R lW (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)))
       (Run-R ac′₁ ac′₂ (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))) C.self lW hk₁ hk₂ hA
              (proj₁ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)) (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)))))

  RKi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm (kp {R} {R′}) =
    si (λ p lW′ y₁ y₂ r →
      at (BNi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ ll₁ ll₂ hA hw hY (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) (⊲-tr wm p) lW′ (toRl (accK R) r))
         C.self (⊲ᴴ↑ p tm₁) (⊲ᴴ↑ p tm₂) lW′)
  RKi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm rs =
    sl (λ n →
      at (Run-R ac′₁ ac′₂ (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) lW (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw) hY n)))
                C.self lW (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw)
                (proj₁ (Chn-R ac′₁ ac′₂ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) lW (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw) hY n))
                (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) lW (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw) hY n))))
         wm tm₁ tm₂ lm)

  BNi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ ll₁ ll₂ hA hw hY hk₁ hk₂ p lW′ rz =
    ig (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ hk₁ hk₂ ll₁ ll₂ hA hw) p lW′ rz
      (⊕-R lW′ (cv-R p hY)
         (Run-R ac′₁ ac′₂ rz C.self lW′ (⊲ᴴ↑ p hk₁) (⊲ᴴ↑ p hk₂) (Ig↾-R p (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ hk₁ hk₂ ll₁ ll₂ hA hw)) s0 (cv-R p hY)))

  Walk-R ac₁ ac₂ hu b C.self ap lb bV lV ll₁ ll₂ hA hco hY = zero-R
  Walk-R ac₁ ac₂ hu (asuc c) (C.suc p) ap lb bV lV ll₁ ll₂ hA hco hY =
    ⨾-R (Walk-R ac₁ ac₂ hu c p ap lb (⊲-tr (C.suc C.self) bV) lV ll₁ ll₂ hA hco hY)
        (Run-R ac₁ ac₂ (hu (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bV) lV ll₁ ll₂ hA (s⨾ hco (Cut-R hu c p ap lb (⊲-tr (C.suc C.self) bV)))
           (⊕-R lV hY (Walk-R ac₁ ac₂ hu c p ap lb (⊲-tr (C.suc C.self) bV) lV ll₁ ll₂ hA hco hY)))
  Walk-R ac₁ ac₂ hu (alim f) (C.lim n p) ap (stp , wl) bV lV ll₁ ll₂ hA hco hY =
    ⨾-R (Walk-R ac₁ ac₂ hu (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) lV ll₁ ll₂ hA hco hY)
        (nl-R (λ m → Walk-R ac₁ ac₂ hu (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bV) lV ll₁ ll₂ hA
           (proj₁ (WRp-R ac₁ ac₂ hu f stp wl p ap (λ m₁ → ⊲-tr (C.lim m₁ C.self) bV) lV ll₁ ll₂ hA
                     (s⨾ hco (Cut-R hu (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV)))
                     (⊕-R lV hY (Walk-R ac₁ ac₂ hu (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) lV ll₁ ll₂ hA hco hY)) m))
           (proj₂ (WRp-R ac₁ ac₂ hu f stp wl p ap (λ m₁ → ⊲-tr (C.lim m₁ C.self) bV) lV ll₁ ll₂ hA
                     (s⨾ hco (Cut-R hu (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV)))
                     (⊕-R lV hY (Walk-R ac₁ ac₂ hu (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) lV ll₁ ll₂ hA hco hY)) m))))

  WRp-R ac₁ ac₂ hu f stp wl p ap fV lV ll₁ ll₂ hA hco hY zero = hco , hY
  WRp-R {n = n} ac₁ ac₂ hu f stp wl p ap fV lV ll₁ ll₂ hA hco hY (suc m) =
    s⨾ (proj₁ (WRp-R ac₁ ac₂ hu f stp wl p ap fV lV ll₁ ll₂ hA hco hY m))
       (Cut-R hu (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n)))) ,
    ⊕-R lV (proj₂ (WRp-R ac₁ ac₂ hu f stp wl p ap fV lV ll₁ ll₂ hA hco hY m))
      (Walk-R ac₁ ac₂ hu (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) lV ll₁ ll₂ hA
         (proj₁ (WRp-R ac₁ ac₂ hu f stp wl p ap fV lV ll₁ ll₂ hA hco hY m)) (proj₂ (WRp-R ac₁ ac₂ hu f stp wl p ap fV lV ll₁ ll₂ hA hco hY m)))

  RunK-R ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA hw hY =
    dfr (λ {t} wm tm₁ tm₂ lm → RKy-R ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA hw hY t wm tm₁ tm₂ lm)

  RKy-R ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA hw hY hz wm tm₁ tm₂ lm =
    sl (λ n → κd-R ac₁ ac₂ hu ll₁ ll₂ hA (κc-R ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA hw hY n))
  RKy-R ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA hw hY (hs b) wm tm₁ tm₂ lm = RKk-R ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm tt tt
  RKy-R ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA hw hY (hl f) wm tm₁ tm₂ lm = RKk-R ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm tt tt
  RKy-R ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA hw hY (hΩ g) wm tm₁ tm₂ lm = RKk-R ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm tt tt

  RKk-R ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm zz₁ zz₂ =
    s⨾ (at (Kp-R ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wm lm) C.self tm₁ tm₂ lm)
       (sκ (λ p lc → at (Kb-R ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wm lm p lc) C.self (⊲ᴴ↑ p tm₁) (⊲ᴴ↑ p tm₂) lc))

  Kp-R {W⁺ = W⁺} ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wu lW⁺ =
    Walk-R ac₁ ac₂ hu W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self lW⁺ (⊲ᴴ↑ wu ll₁) (⊲ᴴ↑ wu ll₂) (Ig↾-R wu hA) (sw hw) (cv-R wu hY)

  Kb-R {W⁺ = W⁺} {c = c} ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wu lW⁺ p lc =
    Run-R ac₁ ac₂ (hu (⊲-tr q₀ (⊲-tr wu p)) lc) C.self lc (⊲ᴴ↑ (⊲-tr wu p) ll₁) (⊲ᴴ↑ (⊲-tr wu p) ll₂) (Ig↾-R (⊲-tr wu p) hA)
      (s⨾ (sw (s⨾ (sw hw) (Cut-R hu W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self))) (Cut-R hu c p (⊲-tr q₀ wu) lc C.self))
      (⊕-R lc (cv-R p (⊕-R lW⁺ (cv-R wu hY) (Kp-R ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wu lW⁺)))
         (Walk-R ac₁ ac₂ hu c p (⊲-tr q₀ wu) lc C.self lc (⊲ᴴ↑ (⊲-tr wu p) ll₁) (⊲ᴴ↑ (⊲-tr wu p) ll₂) (Ig↾-R (⊲-tr wu p) hA)
            (sw (s⨾ (sw hw) (Cut-R hu W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self)))
            (cv-R p (⊕-R lW⁺ (cv-R wu hY) (Kp-R ac₁ ac₂ hu q₀ ll₁ ll₂ hA hw hY wu lW⁺)))))

  κc-R {ly} {W₀} {W} ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA {w₁} {w₂} hw {Y₁} {Y₂} hY zero = κ0 (zR hY)
    where
    κ0 : ∀ {ζ₁ ζ₂ : D₀ W} → ζ₁ ≡ ζ₂ →
         ClR (F₁.mkCl (sum W ζ₁) (Lg-sum W ζ₁ lW) (sum-fst W ζ₁) W₀ C.self (⊲-tr q₀ (sum-fst W ζ₁)) (F₁.cv (sum-fst W ζ₁) Y₁) (nw (sum-fst W ζ₁) w₁))
             (F₂.mkCl (sum W ζ₂) (Lg-sum W ζ₂ lW) (sum-fst W ζ₂) W₀ C.self (⊲-tr q₀ (sum-fst W ζ₂)) (F₂.cv (sum-fst W ζ₂) Y₂) (nw (sum-fst W ζ₂) w₂))
    κ0 {ζ₁} refl = clr (cv-R (sum-fst W ζ₁) hY) (sw hw)
  κc-R ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA hw hY (suc n) = κs-R ac₁ ac₂ hu ll₁ ll₂ hA (κc-R ac₁ ac₂ hu q₀ lW ll₁ ll₂ hA hw hY n)

  κs-R {ly} ac₁ ac₂ {u₁} {u₂} hu ll₁ ll₂ {A₁} {A₂} hA (clr {v} {lv} {wv} {a} {ap} {av} {S₁} {S₂} {co₁} {co₂} hS hco) =
    κ1 (eq0 fe accᴸ (at hΔ C.self (z⊲ᴴ Λ₁) (z⊲ᴴ Λ₂) lv))
    where
    hΔ : DfR (F₁.κΔ ac₁ u₁ ll₁ A₁ (F₁.mkCl v lv wv a ap av S₁ co₁)) (F₂.κΔ ac₂ u₂ ll₂ A₂ (F₂.mkCl v lv wv a ap av S₂ co₂))
    hΔ = Walk-R ac₁ ac₂ hu v av ap lv C.self lv (⊲ᴴ↑ wv ll₁) (⊲ᴴ↑ wv ll₂) (Ig↾-R wv hA) hco hS
    κ1 : ∀ {δ₁ δ₂ : D₀ v} → δ₁ ≡ δ₂ →
         ClR (F₁.mkCl (sum v δ₁) (Lg-sum v δ₁ lv) (⊲-tr wv (sum-fst v δ₁)) v (⊲-tr ap av) (sum-fst v δ₁)
                (F₁.cv (sum-fst v δ₁) (F₁._⊕⟨_⟩_ S₁ lv (F₁.κΔ ac₁ u₁ ll₁ A₁ (F₁.mkCl v lv wv a ap av S₁ co₁))))
                (nw (sum-fst v δ₁) (co₁ ⨾ Cut u₁ v av ap lv C.self)))
             (F₂.mkCl (sum v δ₂) (Lg-sum v δ₂ lv) (⊲-tr wv (sum-fst v δ₂)) v (⊲-tr ap av) (sum-fst v δ₂)
                (F₂.cv (sum-fst v δ₂) (F₂._⊕⟨_⟩_ S₂ lv (F₂.κΔ ac₂ u₂ ll₂ A₂ (F₂.mkCl v lv wv a ap av S₂ co₂))))
                (nw (sum-fst v δ₂) (co₂ ⨾ Cut u₂ v av ap lv C.self)))
    κ1 {δ₁} refl = clr (cv-R (sum-fst v δ₁) (⊕-R lv hS hΔ)) (sw (s⨾ hco (Cut-R hu v av ap lv C.self)))

  κd-R ac₁ ac₂ hu ll₁ ll₂ hA (clr {v} {lv} {wv} {a} {ap} {av} hS hco) =
    drp-R accᴸ (at (Walk-R ac₁ ac₂ hu v av ap lv C.self lv (⊲ᴴ↑ wv ll₁) (⊲ᴴ↑ wv ll₂) (Ig↾-R wv hA) hco hS) C.self (z⊲ᴴ Λ₁) (z⊲ᴴ Λ₂) lv)
```
