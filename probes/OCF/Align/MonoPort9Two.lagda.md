# Ω-极限高度 (四): 只在不含 Ω-极限的目标上比的两世界互模拟

> 入口 [MonoPort9](MonoPort9.lagda.md). 不含记号. 由 `probes/Survey/scripts/monoport9/mk_two.py` 从 [MonoPort8Sim](MonoPort8Sim.lagda.md) 的 §6–§7 生成 (逐字节可重生成). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> `MonoPort8Sim.Two` 的前提 `fr` 要一切目标层不含 Ω-极限. 实例 $\Lambda=\mathrm{h\Omega}\,g$ 自己就是一个目标层 (`hself`), 所以 `Two` 用不到 $\Lambda=\mathrm{h\Omega}\,g$ 上. `MonoPort8` §3 的判断是 "把 `fr` 放宽成只在不含 Ω-极限的目标上比". 本文照做, 与 `Two` 只差:
>
> - `DfE` 的字段 `at` 多一个前提 `Free t` (目标层不含 Ω-极限); 一切 `dfe`/`at` 把它传下去; `StepE` 与判定一致 `rkT-rel` 用它代替 `fr tm₁ tm₂`.
> - 读状态的另一处是链 `Chn-E` 在节点层 $k$ 上读 (`at (dE hY) … hk₁ hk₂`). 节点层严格低于实例, 用模块参数 `frk : StH W₀ k ly → ly ⊲[ W ] Λ₁ → Free k` 给出 (对 $\mathrm{h\Omega}\,g$, 分支都不含 Ω-极限时成立, 见 [MonoPort9Walk](MonoPort9Walk.lagda.md) 的 `frkΩ`).
>
> 其余每一句与 `MonoPort8Sim` 相同. 本组不比 $\Lambda$ 这一层上的读数: 单世界关系 `MonoPort7Rel.Rel` 在 $\mathrm{h\Omega}\,g$ 层上本来就是 $\top$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort9Two where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (ω⋅)
import OCF.Align.HtFeedFold as Fold
open import OCF.Align.HtCrossVSim using (Free)
open import OCF.Align.HtCrossVRun using (module Val)
open import OCF.Align.MonoPort8Sim using (SimE; e0; e1; e⨾; el; ei; ew; RelE; Re; toE; ofE; convE; ΩdE; IntE; reS)
```

## 1 两个实例, 两个世界, 只比不含 Ω-极限的目标

```agda
module TwoF (Λ₁ : H) (l₁ : LgH Λ₁) (Λ₂ : H) (l₂ : LgH Λ₂) (frk : ∀ {W₀ W k ly} → StH W₀ k ly → ly ⊲[ W ] Λ₁ → Free k) where
  module F₁ = Fold ω⋅ Λ₁ l₁
  module F₂ = Fold ω⋅ Λ₂ l₂
  module V₁ = Val Λ₁ l₁
  module V₂ = Val Λ₂ l₂

  record DfE {W W′ : A} (Δ₁ : F₁.Df W) (Δ₂ : F₂.Df W′) : Set where
    constructor dfe
    field
      at : ∀ {t m m′} (ft : Free t) (wm : W ⊲ m) (wm′ : W′ ⊲ m′) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m′ ] Λ₂) (lm : Lg m) (lm′ : Lg m′) →
           Re t (F₁.yc Δ₁ (F₁.tg wm tm₁ lm)) (F₂.yc Δ₂ (F₂.tg wm′ tm₂ lm′))
  open DfE public

  record StE {W W′ : A} (Y₁ : F₁.St W) (Y₂ : F₂.St W′) : Set where
    constructor ste
    field
      dE : DfE (F₁.d Y₁) (F₂.d Y₂)
  open StE public

  record IgE {ly : H} {W W′ : A} (A₁ : F₁.Ig ly W) (A₂ : F₂.Ig ly W′) : Set where
    constructor ige
    field
      ig : ∀ {V V′} (p : W ⊲ V) (p′ : W′ ⊲ V′) (lV : Lg V) (lV′ : Lg V′) {w₁ : D ly V} {w₂ : D ly V′} → Re ly w₁ w₂ →
           {Y₁ : F₁.St V} {Y₂ : F₂.St V′} → StE Y₁ Y₂ → DfE (A₁ p lV w₁ Y₁) (A₂ p′ lV′ w₂ Y₂)
  open IgE public

  zeroE : ∀ {W W′} → DfE (F₁.zeroD {W}) (F₂.zeroD {W′})
  zeroE = dfe (λ ft wm wm′ tm₁ tm₂ lm lm′ → e0)

  ⨾E : ∀ {W W′} {a₁ b₁ : F₁.Df W} {a₂ b₂ : F₂.Df W′} → DfE a₁ a₂ → DfE b₁ b₂ → DfE (a₁ F₁.⨾ᴰ b₁) (a₂ F₂.⨾ᴰ b₂)
  ⨾E ha hb = dfe (λ ft wm wm′ tm₁ tm₂ lm lm′ → e⨾ (at ha ft wm wm′ tm₁ tm₂ lm lm′) (at hb ft wm wm′ tm₁ tm₂ lm lm′))

  nlE : ∀ {W W′} {G₁ : ℕ → F₁.Df W} {G₂ : ℕ → F₂.Df W′} → (∀ n → DfE (G₁ n) (G₂ n)) → DfE (F₁.nlᴰ G₁) (F₂.nlᴰ G₂)
  nlE h = dfe (λ ft wm wm′ tm₁ tm₂ lm lm′ → el (λ n → at (h n) ft wm wm′ tm₁ tm₂ lm lm′))

  ⊕E : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) {Y₁ : F₁.St W} {Y₂ : F₂.St W′} {Δ₁ : F₁.Df W} {Δ₂ : F₂.Df W′} → StE Y₁ Y₂ → DfE Δ₁ Δ₂ →
       StE (F₁._⊕⟨_⟩_ Y₁ lW Δ₁) (F₂._⊕⟨_⟩_ Y₂ lW′ Δ₂)
  ⊕E lW lW′ hY hΔ = ste (⨾E (dE hY) hΔ)

  cvE : ∀ {W W′ U U′} (q : W ⊲ U) (q′ : W′ ⊲ U′) {Y₁ : F₁.St W} {Y₂ : F₂.St W′} → StE Y₁ Y₂ → StE (F₁.cv q Y₁) (F₂.cv q′ Y₂)
  cvE q q′ hY = ste (dfe (λ ft wm wm′ tm₁ tm₂ lm lm′ → at (dE hY) ft (⊲-tr q wm) (⊲-tr q′ wm′) tm₁ tm₂ lm lm′))

  StepE : ∀ {W W′} {Y₁ : F₁.St W} {Y₂ : F₂.St W′} → StE Y₁ Y₂ → DfE (F₁.Step Y₁) (F₂.Step Y₂)
  StepE hY = dfe (λ {t} ft wm wm′ tm₁ tm₂ lm lm′ → el (λ _ → e⨾ (ΩdE t ft accᴸ) (at (dE hY) ft wm wm′ tm₁ tm₂ lm lm′)))

  Ig↾E : ∀ {ly W W′ U U′} (p : W ⊲ U) (p′ : W′ ⊲ U′) {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W′} → IgE A₁ A₂ → IgE (F₁.Ig↾ p A₁) (F₂.Ig↾ p′ A₂)
  Ig↾E p p′ hA = ige (λ p₁ p₂ → ig hA (⊲-tr p p₁) (⊲-tr p′ p₂))

  data RkE {k t : H} {m m′ : A} : F₁.Rk k t m → F₂.Rk k t m′ → Set where
    kp : ∀ {R R′} → RkE (F₁.keep R) (F₂.keep R′)
    rs : RkE F₁.rise F₂.rise

  -- 判定一致: 目标层不含 Ω-极限, 节点种类可以换世界
  rk-rel : ∀ {k t m m′} → Free t → (x₁ : F₁.Rk k t m) (x₂ : F₂.Rk k t m′) → V₁.Valid x₁ → V₂.Valid x₂ → RkE x₁ x₂
  rk-rel ft (F₁.keep R) (F₂.keep R′) _ _ = kp
  rk-rel ft (F₁.keep R) F₂.rise _ v = ⊥-elim (v (reS ft R))
  rk-rel ft F₁.rise (F₂.keep R) v _ = ⊥-elim (v (reS ft R))
  rk-rel ft F₁.rise F₂.rise _ _ = rs

  rkT-rel : ∀ {k t m m′} → Free t → (km₁ : k ⊲[ m ] Λ₁) (tm₁ : t ⊲[ m ] Λ₁) (lm : Lg m) (km₂ : k ⊲[ m′ ] Λ₂) (tm₂ : t ⊲[ m′ ] Λ₂) (lm′ : Lg m′) →
            RkE (F₁.rkT km₁ tm₁ lm) (F₂.rkT km₂ tm₂ lm′)
  rkT-rel ft km₁ tm₁ lm km₂ tm₂ lm′ = rk-rel ft _ _ (V₁.rk-valid km₁ tm₁ lm) (V₂.rk-valid km₂ tm₂ lm′)

  Br : ∀ {ly W₀ k} (r : StH W₀ k ly) → Set
  Br {ly} {W₀} r = ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′

  HU : ∀ {ly V V′ k} (r₁ : StH V k ly) (r₂ : StH V′ k ly) → Br r₁ → Br r₂ → Set
  HU {ly} {V} {V′} r₁ r₂ u₁ u₂ = ∀ {U U′} (p : V ⊲ U) (p′ : V′ ⊲ U′) (l : Lg U) (l′ : Lg U′) y₁ y₂ →
                                 RelE (accK r₁) (outS r₁ y₁) (outS r₂ y₂) → Re ly (u₁ p l y₁) (u₂ p′ l′ y₂)
```

## 2 折叠, 逐个对应

七条, 与 `HtCrossVRun` 的同名函数一一对应; 每处 "同一条路径" 换成两条, "同一个世界" 换成两个.

```agda
  Run-E   : ∀ {ly V₁ V₂ W₁ W₂} (ac₁ ac₂ : AccY ly) {x₁ : D ly V₁} {x₂ : D ly V₂} → Re ly x₁ x₂ →
            (q₁ : V₁ ⊲ W₁) (q₂ : V₂ ⊲ W₂) (lW₁ : Lg W₁) (lW₂ : Lg W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ →
            DfE (F₁.Run ac₁ x₁ q₁ lW₁ ll₁ A₁ w₁ Y₁) (F₂.Run ac₂ x₂ q₂ lW₂ ll₂ A₂ w₂ Y₂)
  Rpt-E   : ∀ {ly V₁ V₂ W₁ W₂} (ac₁ ac₂ : AccY ly) {G₁ : ℕ → D ly V₁} {G₂ : ℕ → D ly V₂} → (∀ n → Re ly (G₁ n) (G₂ n)) →
            (q₁ : V₁ ⊲ W₁) (q₂ : V₂ ⊲ W₂) (lW₁ : Lg W₁) (lW₂ : Lg W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ → ∀ n →
            Re ly (proj₁ (F₁.Rpt ac₁ G₁ q₁ lW₁ ll₁ A₁ w₁ Y₁ n)) (proj₁ (F₂.Rpt ac₂ G₂ q₂ lW₂ ll₂ A₂ w₂ Y₂ n)) ×
            StE (proj₂ (F₁.Rpt ac₁ G₁ q₁ lW₁ ll₁ A₁ w₁ Y₁ n)) (proj₂ (F₂.Rpt ac₂ G₂ q₂ lW₂ ll₂ A₂ w₂ Y₂ n))
  RunNi-E : ∀ {ly V₁ V₂ W₁ W₂ k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ : StH V₁ k ly) (r₂ : StH V₂ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₁ : V₁ ⊲ W₁) (q₂ : V₂ ⊲ W₂) (lW₁ : Lg W₁) (lW₂ : Lg W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ →
            DfE (F₁.RunNi ac₁ ac′₁ r₁ u₁ q₁ lW₁ ll₁ A₁ w₁ Y₁) (F₂.RunNi ac₂ ac′₂ r₂ u₂ q₂ lW₂ ll₂ A₂ w₂ Y₂)
  Ai-E    : ∀ {ly V₁ V₂ W₁ W₂ k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ : StH V₁ k ly) (r₂ : StH V₂ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₁ : V₁ ⊲ W₁) (q₂ : V₂ ⊲ W₂) (hk₁ : F₁.LW k W₁) (hk₂ : F₂.LW k W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            IgE (F₁.Ai ac₁ ac′₁ r₁ u₁ q₁ hk₁ ll₁ A₁ w₁) (F₂.Ai ac₂ ac′₂ r₂ u₂ q₂ hk₂ ll₂ A₂ w₂)
  Chn-E   : ∀ {k W₁ W₂} (fk : Free k) (ac′₁ ac′₂ : AccY k) (hk₁ : F₁.LW k W₁) (hk₂ : F₂.LW k W₂) (lW₁ : Lg W₁) (lW₂ : Lg W₂)
            {A₁ : F₁.Ig k W₁} {A₂ : F₂.Ig k W₂} → IgE A₁ A₂ → {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ → ∀ n →
            Re k (proj₁ (F₁.Chn ac′₁ hk₁ lW₁ A₁ Y₁ n)) (proj₁ (F₂.Chn ac′₂ hk₂ lW₂ A₂ Y₂ n)) ×
            (Re k (proj₁ (proj₂ (F₁.Chn ac′₁ hk₁ lW₁ A₁ Y₁ n))) (proj₁ (proj₂ (F₂.Chn ac′₂ hk₂ lW₂ A₂ Y₂ n))) ×
             StE (proj₂ (proj₂ (F₁.Chn ac′₁ hk₁ lW₁ A₁ Y₁ n))) (proj₂ (proj₂ (F₂.Chn ac′₂ hk₂ lW₂ A₂ Y₂ n))))
  RKi-E   : ∀ {ly V₁ V₂ W₁ W₂ k t m m′} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ : StH V₁ k ly) (r₂ : StH V₂ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₁ : V₁ ⊲ W₁) (q₂ : V₂ ⊲ W₂) (lW₁ : Lg W₁) (lW₂ : Lg W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ →
            (ft : Free t) (wm : W₁ ⊲ m) (wm′ : W₂ ⊲ m′) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m′ ] Λ₂) (lm : Lg m) (lm′ : Lg m′)
            {x₁ : F₁.Rk k t m} {x₂ : F₂.Rk k t m′} → RkE x₁ x₂ →
            Re t (F₁.RKi ac₁ ac′₁ r₁ u₁ q₁ lW₁ ll₁ A₁ w₁ Y₁ (F₁.tg wm tm₁ lm) x₁) (F₂.RKi ac₂ ac′₂ r₂ u₂ q₂ lW₂ ll₂ A₂ w₂ Y₂ (F₂.tg wm′ tm₂ lm′) x₂)
  BNi-E   : ∀ {ly V₁ V₂ W₁ W₂ k U₁ U₂} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ : StH V₁ k ly) (r₂ : StH V₂ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₁ : V₁ ⊲ W₁) (q₂ : V₂ ⊲ W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ →
            (hk₁ : F₁.LW k W₁) (hk₂ : F₂.LW k W₂) (p : W₁ ⊲ U₁) (p′ : W₂ ⊲ U₂) (lU₁ : Lg U₁) (lU₂ : Lg U₂) {z₁ : D k U₁} {z₂ : D k U₂} → Re k z₁ z₂ →
            DfE (F₁.BNi ac₁ ac′₁ r₁ u₁ q₁ ll₁ A₁ w₁ Y₁ hk₁ p lU₁ z₁) (F₂.BNi ac₂ ac′₂ r₂ u₂ q₂ ll₂ A₂ w₂ Y₂ hk₂ p′ lU₂ z₂)

  Run-E ac₁ ac₂ e0 q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY = zeroE
  Run-E ac₁ ac₂ e1 q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY = ig hA C.self C.self lW₁ lW₂ hw hY
  Run-E ac₁ ac₂ (e⨾ hx hy) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY =
    ⨾E (Run-E ac₁ ac₂ hx q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY)
       (Run-E ac₁ ac₂ hy q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA (e⨾ hw (ew hx)) (⊕E lW₁ lW₂ hY (Run-E ac₁ ac₂ hx q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY)))
  Run-E ac₁ ac₂ (el h) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY =
    nlE (λ n → Run-E ac₁ ac₂ (h n) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA (proj₁ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n))
                 (proj₂ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n)))
  Run-E ac₁ ac₂ (ew {p = p} {p′ = p′} hx) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY = Run-E ac₁ ac₂ hx (⊲-tr p q₁) (⊲-tr p′ q₂) lW₁ lW₂ ll₁ ll₂ hA hw hY
  Run-E (acc f₁) (acc f₂) (ei {R = r₁} {R′ = r₂} h) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY =
    RunNi-E (acc f₁) (acc f₂) (f₁ r₁) (f₂ r₂) r₁ r₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY

  Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY zero = hw , hY
  Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY (suc n) =
    e⨾ (proj₁ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n)) (ew (h n)) ,
    ⊕E lW₁ lW₂ (proj₂ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n))
      (Run-E ac₁ ac₂ (h n) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA (proj₁ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n))
         (proj₂ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n)))

  RunNi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY =
    dfe (λ ft wm wm′ tm₁ tm₂ lm lm′ →
      RKi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY ft wm wm′ tm₁ tm₂ lm lm′
        (rkT-rel ft (⊲ᴴ↑ wm (F₁.kk r₁ q₁ ll₁)) tm₁ lm (⊲ᴴ↑ wm′ (F₂.kk r₂ q₂ ll₂)) tm₂ lm′))

  Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ hk₁ hk₂ ll₁ ll₂ hA hw =
    ige (λ p p′ lV lV′ {z₁} {z₂} rz hY′ →
      Run-E ac₁ ac₂ (hu (⊲-tr q₁ p) (⊲-tr q₂ p′) lV lV′ (inS r₁ z₁) (inS r₂ z₂) (convE (accK r₁) r₁ r₂ rz)) C.self C.self lV lV′
        (⊲ᴴ↑ p ll₁) (⊲ᴴ↑ p′ ll₂) (Ig↾E p p′ hA)
        (e⨾ (ew hw) (IntE ac′₁ ac′₂ rz C.self C.self lV lV′ (NZ-S r₁) (NZ-S r₂) (mkOf r₁ (⊲-tr q₁ p)) (mkOf r₂ (⊲-tr q₂ p′))
                       (λ p₁ p₂ l₁ l₂ r′ → hu (⊲-tr (⊲-tr q₁ p) p₁) (⊲-tr (⊲-tr q₂ p′) p₂) l₁ l₂ _ _ (convE (accK r₁) r₁ r₂ r′)) e0))
        hY′)

  Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY zero = e0 , (at (dE hY) fk C.self C.self hk₁ hk₂ lW₁ lW₂ , hY)
  Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY (suc n) =
    e⨾ (proj₁ (Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)) (proj₁ (proj₂ (Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n))) ,
    (at (Run-E ac′₁ ac′₂ (proj₁ (proj₂ (Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n))) C.self C.self lW₁ lW₂ hk₁ hk₂ hA
              (proj₁ (Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)) (proj₂ (proj₂ (Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n))))
        fk C.self C.self hk₁ hk₂ lW₁ lW₂ ,
     ⊕E lW₁ lW₂ (proj₂ (proj₂ (Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)))
       (Run-E ac′₁ ac′₂ (proj₁ (proj₂ (Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n))) C.self C.self lW₁ lW₂ hk₁ hk₂ hA
              (proj₁ (Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)) (proj₂ (proj₂ (Chn-E fk ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)))))

  RKi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY ft wm wm′ tm₁ tm₂ lm lm′ (kp {R} {R′}) =
    ei (λ p p′ l l′ y₁ y₂ r →
      at (BNi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ ll₁ ll₂ hA hw hY (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) (⊲-tr wm p) (⊲-tr wm′ p′) l l′ (toE (accK R) r))
         ft C.self C.self (⊲ᴴ↑ p tm₁) (⊲ᴴ↑ p′ tm₂) l l′)
  RKi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY ft wm wm′ tm₁ tm₂ lm lm′ rs =
    el (λ n →
      at (Run-E ac′₁ ac′₂ (proj₁ (proj₂ (Chn-E (frk r₁ ll₁) ac′₁ ac′₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) lW₁ lW₂ (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) ll₁ ll₂ hA hw) hY n)))
                C.self C.self lW₁ lW₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) ll₁ ll₂ hA hw)
                (proj₁ (Chn-E (frk r₁ ll₁) ac′₁ ac′₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) lW₁ lW₂ (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) ll₁ ll₂ hA hw) hY n))
                (proj₂ (proj₂ (Chn-E (frk r₁ ll₁) ac′₁ ac′₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) lW₁ lW₂ (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) ll₁ ll₂ hA hw) hY n))))
         ft wm wm′ tm₁ tm₂ lm lm′)

  BNi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ ll₁ ll₂ hA hw hY hk₁ hk₂ p p′ lU₁ lU₂ rz =
    ig (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ hk₁ hk₂ ll₁ ll₂ hA hw) p p′ lU₁ lU₂ rz
      (⊕E lU₁ lU₂ (cvE p p′ hY)
         (Run-E ac′₁ ac′₂ rz C.self C.self lU₁ lU₂ (⊲ᴴ↑ p hk₁) (⊲ᴴ↑ p′ hk₂)
            (Ig↾E p p′ (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ hk₁ hk₂ ll₁ ll₂ hA hw)) e0 (cvE p p′ hY)))
```

