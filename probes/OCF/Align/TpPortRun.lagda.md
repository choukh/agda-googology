# 两种种类的单调 (二): 两个实例里的折叠

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [HtCrossVRun](HtCrossVRun.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. `Val`, `Two` 多实例的 `oΛ` (`o₁`, `o₂`); `Ai-R` 里内层 `Int-R` 多 `NZ₁-S` 两个参数. 关系里没有 `nκ`, `nμ` 的构造子, 所以折叠的 `nκ`, `nμ` 两句不出现.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPortRun where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; LgB; ⊲ᴮ↑; cmpB)
open import OCF.Align.HtTowerFTree renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerFClosed using (ω⋅)
import OCF.Align.HtTowerFFold as Fold
open import OCF.Align.TpPortSim

```
```agda
module Val (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) where
  open Fold ω⋅ Λ lΛ oΛ

  Valid : ∀ {k t m} → Rk k t m → Set
  Valid (keep R) = ⊤
  Valid {k} {t} {m} rise = StH m k t → ⊥

  rkS-valid : ∀ {k t m} (p : k ⊲[ m ] t) → Valid (rkS p)
  rkS-valid hself = λ R → irrS (accL _) R
  rkS-valid (hsuc p) = tt
  rkS-valid (hlim n p) = tt
  rkS-valid (hLim e p) = tt

  rk-valid : ∀ {k t m} (km : k ⊲[ m ] Λ) (tm : t ⊲[ m ] Λ) (lm : LgW₂ m) → Valid (rkT km tm lm)
  rk-valid km tm lm with cmpB km tm lm lΛ
  ... | inj₁ t⊲k = λ R → irrS (accL _) (Sk R t⊲k)
  ... | inj₂ k⊲t = rkS-valid k⊲t
```
```agda
module Two (Λ₁ : Ht) (l₁ : LgB Λ₁) (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ₁) (Λ₂ : Ht) (l₂ : LgB Λ₂) (o₂ : ∀ {w} → hs hz ⊲[ w ] Λ₂) (fr : ∀ {t m} → t ⊲[ m ] Λ₁ → t ⊲[ m ] Λ₂ → Free t) where
  module F₁ = Fold ω⋅ Λ₁ l₁ o₁
  module F₂ = Fold ω⋅ Λ₂ l₂ o₂
  module V₁ = Val Λ₁ l₁ o₁
  module V₂ = Val Λ₂ l₂ o₂

  record DfR {W : Wd₂} (Δ₁ : F₁.Df W) (Δ₂ : F₂.Df W) : Set where
    constructor dfr
    field
      at : ∀ {t m} (wm : W ≤ʷ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : LgW₂ m) →
           Rl t (F₁.yc Δ₁ (F₁.tg wm tm₁ lm)) (F₂.yc Δ₂ (F₂.tg wm tm₂ lm))
  open DfR public

  -- 只有差; 第 0 层的部分不比
  record StR {W : Wd₂} (Y₁ : F₁.St W) (Y₂ : F₂.St W) : Set where
    constructor str
    field
      dR : DfR (F₁.d Y₁) (F₂.d Y₂)
  open StR public

  record IgR {ly : Ht} {W : Wd₂} (A₁ : F₁.Ig ly W) (A₂ : F₂.Ig ly W) : Set where
    constructor igr
    field
      ig : ∀ {W′} (p : W ≤ʷ W′) (lW′ : LgW₂ W′) {w₁ w₂ : D ly W′} → Rl ly w₁ w₂ →
           {Y₁ : F₁.St W′} {Y₂ : F₂.St W′} → StR Y₁ Y₂ → DfR (A₁ p lW′ w₁ Y₁) (A₂ p lW′ w₂ Y₂)
  open IgR public

  zero-R : ∀ {W} → DfR (F₁.zeroD {W}) (F₂.zeroD {W})
  zero-R = dfr (λ wm tm₁ tm₂ lm → s0)

  ⨾-R : ∀ {W} {a₁ b₁ : F₁.Df W} {a₂ b₂ : F₂.Df W} → DfR a₁ a₂ → DfR b₁ b₂ → DfR (a₁ F₁.⨾ᴰ b₁) (a₂ F₂.⨾ᴰ b₂)
  ⨾-R ha hb = dfr (λ wm tm₁ tm₂ lm → s⨾ (at ha wm tm₁ tm₂ lm) (at hb wm tm₁ tm₂ lm))

  nl-R : ∀ {W} {G₁ : ℕ → F₁.Df W} {G₂ : ℕ → F₂.Df W} → (∀ n → DfR (G₁ n) (G₂ n)) → DfR (F₁.nlᴰ G₁) (F₂.nlᴰ G₂)
  nl-R h = dfr (λ wm tm₁ tm₂ lm → sl (λ n → at (h n) wm tm₁ tm₂ lm))

  -- 原文这里要第 0 层的相等 (eq0); 现在不要
  ⊕-R : ∀ {W} (lW : LgW₂ W) {Y₁ : F₁.St W} {Y₂ : F₂.St W} {Δ₁ : F₁.Df W} {Δ₂ : F₂.Df W} → StR Y₁ Y₂ → DfR Δ₁ Δ₂ →
        StR (F₁._⊕⟨_⟩_ Y₁ lW Δ₁) (F₂._⊕⟨_⟩_ Y₂ lW Δ₂)
  ⊕-R lW hY hΔ = str (⨾-R (dR hY) hΔ)

  cv-R : ∀ {W W′} (q : W ≤ʷ W′) {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ → StR (F₁.cv q Y₁) (F₂.cv q Y₂)
  cv-R q hY = str (dfr (λ wm tm₁ tm₂ lm → at (dR hY) (≤tr q wm) tm₁ tm₂ lm))

  Step-R : ∀ {W} {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ → DfR (F₁.Stp Y₁) (F₂.Stp Y₂)
  Step-R hY = dfr (λ {t} wm tm₁ tm₂ lm → sl (λ _ → s⨾ (Ωd-R t (fr tm₁ tm₂) accᴸ) (at (dR hY) wm tm₁ tm₂ lm)))

  Ig↾-R : ∀ {ly W W′} (p : W ≤ʷ W′) {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → IgR (F₁.Ig↾ p A₁) (F₂.Ig↾ p A₂)
  Ig↾-R p hA = igr (λ p′ → ig hA (≤tr p p′))

  data RkR {k t : Ht} {m : Wd₂} : F₁.Rk k t m → F₂.Rk k t m → Set where
    kp : ∀ {R R′} → RkR (F₁.keep R) (F₂.keep R′)
    rs : RkR F₁.rise F₂.rise

  rk-rel : ∀ {k t m} (x₁ : F₁.Rk k t m) (x₂ : F₂.Rk k t m) → V₁.Valid x₁ → V₂.Valid x₂ → RkR x₁ x₂
  rk-rel (F₁.keep R) (F₂.keep R′) _ _ = kp
  rk-rel (F₁.keep R) F₂.rise _ v = ⊥-elim (v R)
  rk-rel F₁.rise (F₂.keep R) v _ = ⊥-elim (v R)
  rk-rel F₁.rise F₂.rise _ _ = rs

  rkT-rel : ∀ {k t m} (km₁ : k ⊲[ m ] Λ₁) (tm₁ : t ⊲[ m ] Λ₁) (km₂ : k ⊲[ m ] Λ₂) (tm₂ : t ⊲[ m ] Λ₂) (lm : LgW₂ m) →
            RkR (F₁.rkT km₁ tm₁ lm) (F₂.rkT km₂ tm₂ lm)
  rkT-rel km₁ tm₁ km₂ tm₂ lm = rk-rel _ _ (V₁.rk-valid km₁ tm₁ lm) (V₂.rk-valid km₂ tm₂ lm)

  Br : ∀ {ly W₀ k} (r : StH W₀ k ly) → Set
  Br {ly} {W₀} r = ∀ {W′} → W₀ ≤ʷ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′

  HU : ∀ {ly W₀ k} (r₁ r₂ : StH W₀ k ly) → Br r₁ → Br r₂ → Set
  HU {ly} {W₀} r₁ r₂ u₁ u₂ = ∀ {W′} (p : W₀ ≤ʷ W′) (l : LgW₂ W′) y₁ y₂ → RelA (accK r₁) (outS r₁ y₁) (outS r₂ y₂) → Rl ly (u₁ p l y₁) (u₂ p l y₂)
```
```agda
  Run-R   : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {x₁ x₂ : D ly W₀} → Rl ly x₁ x₂ → (q₀ : W₀ ≤ʷ W) (lW : LgW₂ W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            DfR (F₁.Run ac₁ x₁ q₀ lW ll₁ A₁ w₁ Y₁) (F₂.Run ac₂ x₂ q₀ lW ll₂ A₂ w₂ Y₂)
  Rpt-R   : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {G₁ G₂ : ℕ → D ly W₀} → (∀ n → Rl ly (G₁ n) (G₂ n)) → (q₀ : W₀ ≤ʷ W) (lW : LgW₂ W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ → ∀ n →
            Rl ly (proj₁ (F₁.Rpt ac₁ G₁ q₀ lW ll₁ A₁ w₁ Y₁ n)) (proj₁ (F₂.Rpt ac₂ G₂ q₀ lW ll₂ A₂ w₂ Y₂ n)) ×
            StR (proj₂ (F₁.Rpt ac₁ G₁ q₀ lW ll₁ A₁ w₁ Y₁ n)) (proj₂ (F₂.Rpt ac₂ G₂ q₀ lW ll₂ A₂ w₂ Y₂ n))
  RunNi-R : ∀ {ly W₀ W k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ≤ʷ W) (lW : LgW₂ W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            DfR (F₁.RunNi ac₁ ac′₁ r₁ u₁ q₀ lW ll₁ A₁ w₁ Y₁) (F₂.RunNi ac₂ ac′₂ r₂ u₂ q₀ lW ll₂ A₂ w₂ Y₂)
  Ai-R    : ∀ {ly W₀ W k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ≤ʷ W) (hk₁ : F₁.LW k W) (hk₂ : F₂.LW k W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ →
            IgR (F₁.Ai ac₁ ac′₁ r₁ u₁ q₀ hk₁ ll₁ A₁ w₁) (F₂.Ai ac₂ ac′₂ r₂ u₂ q₀ hk₂ ll₂ A₂ w₂)
  Chn-R   : ∀ {k W} (ac′₁ ac′₂ : AccY k) (hk₁ : F₁.LW k W) (hk₂ : F₂.LW k W) (lW : LgW₂ W) {A₁ : F₁.Ig k W} {A₂ : F₂.Ig k W} → IgR A₁ A₂ →
            {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ → ∀ n →
            Rl k (proj₁ (F₁.Chn ac′₁ hk₁ lW A₁ Y₁ n)) (proj₁ (F₂.Chn ac′₂ hk₂ lW A₂ Y₂ n)) ×
            (Rl k (proj₁ (proj₂ (F₁.Chn ac′₁ hk₁ lW A₁ Y₁ n))) (proj₁ (proj₂ (F₂.Chn ac′₂ hk₂ lW A₂ Y₂ n))) ×
             StR (proj₂ (proj₂ (F₁.Chn ac′₁ hk₁ lW A₁ Y₁ n))) (proj₂ (proj₂ (F₂.Chn ac′₂ hk₂ lW A₂ Y₂ n))))
  RKi-R   : ∀ {ly W₀ W k t m} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ≤ʷ W) (lW : LgW₂ W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            (wm : W ≤ʷ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : LgW₂ m) {x₁ : F₁.Rk k t m} {x₂ : F₂.Rk k t m} → RkR x₁ x₂ →
            Rl t (F₁.RKi ac₁ ac′₁ r₁ u₁ q₀ lW ll₁ A₁ w₁ Y₁ (F₁.tg wm tm₁ lm) x₁) (F₂.RKi ac₂ ac′₂ r₂ u₂ q₀ lW ll₂ A₂ w₂ Y₂ (F₂.tg wm tm₂ lm) x₂)
  BNi-R   : ∀ {ly W₀ W k W′} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ≤ʷ W) (ll₁ : F₁.LW ly W) (ll₂ : F₂.LW ly W)
            {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : F₁.St W} {Y₂ : F₂.St W} → StR Y₁ Y₂ →
            (hk₁ : F₁.LW k W) (hk₂ : F₂.LW k W) (p : W ≤ʷ W′) (lW′ : LgW₂ W′) {z₁ z₂ : D k W′} → Rl k z₁ z₂ →
            DfR (F₁.BNi ac₁ ac′₁ r₁ u₁ q₀ ll₁ A₁ w₁ Y₁ hk₁ p lW′ z₁) (F₂.BNi ac₂ ac′₂ r₂ u₂ q₀ ll₂ A₂ w₂ Y₂ hk₂ p lW′ z₂)
  Run-R ac₁ ac₂ s0 q₀ lW ll₁ ll₂ hA hw hY = zero-R
  Run-R ac₁ ac₂ s1 q₀ lW ll₁ ll₂ hA hw hY = ig hA ≤rf lW hw hY
  Run-R ac₁ ac₂ (s⨾ hx hy) q₀ lW ll₁ ll₂ hA hw hY =
    ⨾-R (Run-R ac₁ ac₂ hx q₀ lW ll₁ ll₂ hA hw hY)
        (Run-R ac₁ ac₂ hy q₀ lW ll₁ ll₂ hA (s⨾ hw (sw hx)) (⊕-R lW hY (Run-R ac₁ ac₂ hx q₀ lW ll₁ ll₂ hA hw hY)))
  Run-R ac₁ ac₂ (sl h) q₀ lW ll₁ ll₂ hA hw hY =
    nl-R (λ n → Run-R ac₁ ac₂ (h n) q₀ lW ll₁ ll₂ hA (proj₁ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)) (proj₂ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)))
  Run-R ac₁ ac₂ (sw {p = p} hx) q₀ lW ll₁ ll₂ hA hw hY = Run-R ac₁ ac₂ hx (≤tr p q₀) lW ll₁ ll₂ hA hw hY
  Run-R (acc f₁) (acc f₂) (si {R = r₁} {R′ = r₂} h) q₀ lW ll₁ ll₂ hA hw hY =
    RunNi-R (acc f₁) (acc f₂) (f₁ r₁) (f₂ r₂) r₁ r₂ h q₀ lW ll₁ ll₂ hA hw hY
  Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY zero = hw , hY
  Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY (suc n) =
    s⨾ (proj₁ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)) (sw (h n)) ,
    ⊕-R lW (proj₂ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n))
      (Run-R ac₁ ac₂ (h n) q₀ lW ll₁ ll₂ hA (proj₁ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)) (proj₂ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)))

  RunNi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY =
    dfr (λ wm tm₁ tm₂ lm →
      RKi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm
        (rkT-rel (⊲ᴮ↑ wm (F₁.kk r₁ q₀ ll₁)) tm₁ (⊲ᴮ↑ wm (F₂.kk r₂ q₀ ll₂)) tm₂ lm))

  Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ hk₁ hk₂ ll₁ ll₂ hA hw =
    igr (λ p lW′ {z₁} {z₂} rz hY′ →
      Run-R ac₁ ac₂ (hu (≤tr q₀ p) lW′ (inS r₁ z₁) (inS r₂ z₂) (conv (accK r₁) r₁ r₂ rz)) ≤rf lW′ (⊲ᴮ↑ p ll₁) (⊲ᴮ↑ p ll₂) (Ig↾-R p hA)
        (s⨾ (sw hw) (Int-R ac′₁ ac′₂ rz ≤rf lW′ (NZ-S r₁) (NZ-S r₂) (NZ₁-S r₁) (NZ₁-S r₂) (mkOf r₁ (≤tr q₀ p)) (mkOf r₂ (≤tr q₀ p))
                       (λ p′ l′ r′ → hu (≤tr (≤tr q₀ p) p′) l′ _ _ (conv (accK r₁) r₁ r₂ r′)) s0))
        hY′)

  Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY zero = s0 , (at (dR hY) ≤rf hk₁ hk₂ lW , hY)
  Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY (suc n) =
    s⨾ (proj₁ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)) (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))) ,
    (at (Run-R ac′₁ ac′₂ (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))) ≤rf lW hk₁ hk₂ hA
              (proj₁ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)) (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))))
        ≤rf hk₁ hk₂ lW ,
     ⊕-R lW (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)))
       (Run-R ac′₁ ac′₂ (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))) ≤rf lW hk₁ hk₂ hA
              (proj₁ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)) (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)))))

  RKi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm (kp {R} {R′}) =
    si (λ p lW′ y₁ y₂ r →
      at (BNi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ ll₁ ll₂ hA hw hY (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) (≤tr wm p) lW′ (toRl (accK R) r))
         ≤rf (⊲ᴮ↑ p tm₁) (⊲ᴮ↑ p tm₂) lW′)
  RKi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm rs =
    sl (λ n →
      at (Run-R ac′₁ ac′₂ (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) lW (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw) hY n)))
                ≤rf lW (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw)
                (proj₁ (Chn-R ac′₁ ac′₂ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) lW (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw) hY n))
                (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) lW (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw) hY n))))
         wm tm₁ tm₂ lm)

  BNi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ ll₁ ll₂ hA hw hY hk₁ hk₂ p lW′ rz =
    ig (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ hk₁ hk₂ ll₁ ll₂ hA hw) p lW′ rz
      (⊕-R lW′ (cv-R p hY)
         (Run-R ac′₁ ac′₂ rz ≤rf lW′ (⊲ᴮ↑ p hk₁) (⊲ᴮ↑ p hk₂) (Ig↾-R p (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ hk₁ hk₂ ll₁ ll₂ hA hw)) s0 (cv-R p hY)))
```
