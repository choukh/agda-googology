# 新闭项的值 (二): 两个实例里的一般折叠保持 `Mo`

> 不含记号. 入口 [ValNew](ValNew.lagda.md). 第 4 层: 只新增关系与定理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提.
>
> 模块参数: 种类结构 $T$, `GenK T`, `LgDn T`, `FbLg`, 以及**一切旧种类的 A-回灌都有损** (`lossy : ∀ κ → fbA G κ ≡ inj₂ tt`). [FabLFReGen](FabLFReGen.lagda.md) 的 `GL` 满足它 (`fb-lossy`, `refl`). 这是前提, 不是假设: 对 `GL` 它有实例, 对 `NewTwrColl.GΛ` 没有 (那里有 A-回灌).
>
> **`Two`**: 两个实例 [GenFoldRun](GenFoldRun.lagda.md) `T G Ld fl Λ₁ l₁ o₁` 与 `… Λ₂ l₂ o₂` (最高层不同, 合法性证明不同; 同一个 `G`, 同一个世界类型). 前提 `NI Λ₁` (实例 1 的最高层没有新种类的 $\Omega$-结点). 结论 `Run-R` (定理): 相关的数据, 相关的前缀, 相关的状态, 相关的动作 ⇒ 两个实例的折叠在两边共有的每一个目标上输出相关. 由 `ValNewRel.sum-M` 读到第 0 层: **`cross`**, 实例 1 的第 0 层读数 $\le$ 实例 2 的.
>
> **与 [TpPortRun](TpPortRun.lagda.md) 的 `Two` 的差.** 那里是两种种类的折叠 `HtTowerFFold`, 关系是互模拟, 前提是两边共有的目标不含 $\Omega$-极限 (`Free`). 这里: (1) 折叠换成一般折叠 `GenFoldRun`; (2) 关系多了 "右边多出一段" (`mz`, `mr`, `me`, `ml0`), 所以一条定理同时管 "换实例" 与 "状态, 前缀变大"; (3) 旧种类的闭包结点有构造子 `mc`: 第 0 层目标上它**有损** (当前世界的分支重复 $\omega$ 次, 不改世界), 第 $\ge1$ 层目标上保留, 两边都对同一个世界取分支, 所以**含旧种类 $\Omega$-极限的层也覆盖了**; 前提从 "不含 $\Omega$-极限" 放宽到 "不含新种类的 $\Omega$-极限" (`NI`). 新种类的回灌 (`κc₁`) 把输出读成世界, 两个实例的世界会不同 (异质世界), 本篇不碰, 关系里没有它的构造子.
>
> **律的定义域.** 两个实例只在 "两边共有的目标" 上比 (`DfR.at` 要两条到最高层的路径); 节点上 "保留还是上升" 两边一致, 由 `rk-valid` (上升当且仅当没有结点证据) 给出, 不比较两个实例的 `cmpB` 结果; 闭包结点两边取同一个世界的分支. 没有异质世界, 没有全局比较 (判断: 不碰壁垒).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy using (KS; HB; hs; hz; step; _⊲[_]_; LgB)
open import OCF.Align.GenFoldIf using (GenK; LgDn; FbLg; fbA)
module OCF.Align.ValNewRun (T : KS) (G : GenK T) (Ld : LgDn T) (fl : FbLg G) (lossy : ∀ κ → fbA G κ ≡ inj₂ tt) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.TLRuleSpec using () renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy hiding (KS; HB; hs; hz; step; _⊲[_]_; LgB)
open import OCF.Align.HtTowerTy using (KS; HB; hs; hz; step; _⊲[_]_; LgB)
open import OCF.Align.GenFoldIf hiding (GenK; LgDn; FbLg; fbA)
open import OCF.Align.GenFoldIf using (GenK; LgDn; FbLg; fbA)
open import OCF.Align.GenFoldTree
import OCF.Align.GenFoldRun as GR
open import OCF.Align.ValNewRel
open Tree T
open Rel T
open OmM (topStepG (tpK G))
```

## §1 保留还是上升: 两个实例一致

```agda
irrS : ∀ {W k} → AccY {L₀} k → StH W k k → ⊥
irrS (acc g) R = irrS (g R) R

module Val (Λ : HB (step T)) (lΛ : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) where
  open GR T G Ld fl Λ lΛ o

  Valid : ∀ {k t m} → Rk k t m → Set
  Valid (keep R) = ⊤
  Valid {k} {t} {m} rise = StH m k t → ⊥

  rkS-valid : ∀ {k t m} (p : k ⊲[ m ] t) → Valid (rkS p)
  rkS-valid hself = λ R → irrS (accL _) R
  rkS-valid (hsuc p) = tt
  rkS-valid (hlim n p) = tt
  rkS-valid (hLim e p) = tt

  rk-valid : ∀ {k t m} (km : k ⊲[ m ] Λ) (tm : t ⊲[ m ] Λ) (lm : LgW L₀ m) → Valid (rkT km tm lm)
  rk-valid km tm lm with cmpB km tm lm lΛ
  ... | inj₁ t⊲k = λ R → irrS (accL _) (Sk {S = L₀} R t⊲k)
  ... | inj₂ k⊲t = rkS-valid k⊲t
```

## §2 两个实例

```agda
module Two (Λ₁ : HB (step T)) (l₁ : LgB Λ₁) (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ₁)
           (Λ₂ : HB (step T)) (l₂ : LgB Λ₂) (o₂ : ∀ {w} → hs hz ⊲[ w ] Λ₂) (ni₁ : NI Λ₁) where
  module F₁ = GR T G Ld fl Λ₁ l₁ o₁
  module F₂ = GR T G Ld fl Λ₂ l₂ o₂
  module V₁ = Val Λ₁ l₁ o₁
  module V₂ = Val Λ₂ l₂ o₂
  module T₁ = FoldTy T Λ₁
  module T₂ = FoldTy T Λ₂

  record DfR {W : Wd L₀} (Δ₁ : T₁.Df W) (Δ₂ : T₂.Df W) : Set where
    constructor dfr
    field
      at : ∀ {t m} (wm : W ≤ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : LgW L₀ m) →
           Rl t (F₁.yc Δ₁ (T₁.tg wm tm₁ lm)) (F₂.yc Δ₂ (T₂.tg wm tm₂ lm))
  open DfR public

  -- 只比差 (第 0, 1 层的累计读数只喂回灌, 这里没有回灌)
  record StR {W : Wd L₀} (Y₁ : T₁.St W) (Y₂ : T₂.St W) : Set where
    constructor str
    field
      dR : DfR (F₁.d Y₁) (F₂.d Y₂)
  open StR public

  record IgR {ly : HB L₀} {W : Wd L₀} (A₁ : T₁.Ig ly W) (A₂ : T₂.Ig ly W) : Set where
    constructor igr
    field
      ig : ∀ {W′} (p : W ≤ W′) (lW′ : LgW L₀ W′) {w₁ w₂ : D ly W′} → Rl ly w₁ w₂ →
           {Y₁ : T₁.St W′} {Y₂ : T₂.St W′} → StR Y₁ Y₂ → DfR (A₁ p lW′ w₁ Y₁) (A₂ p lW′ w₂ Y₂)
  open IgR public

  zero-R : ∀ {W} {Δ₂ : T₂.Df W} → DfR (F₁.zeroD {W}) Δ₂
  zero-R = dfr (λ wm tm₁ tm₂ lm → mz)

  ⨾-R : ∀ {W} {a₁ b₁ : T₁.Df W} {a₂ b₂ : T₂.Df W} → DfR a₁ a₂ → DfR b₁ b₂ → DfR (a₁ F₁.⨾ᴰ b₁) (a₂ F₂.⨾ᴰ b₂)
  ⨾-R ha hb = dfr (λ wm tm₁ tm₂ lm → m⨾ (at ha wm tm₁ tm₂ lm) (at hb wm tm₁ tm₂ lm))

  nl-R : ∀ {W} {G₁ : ℕ → T₁.Df W} {G₂ : ℕ → T₂.Df W} → (∀ n → DfR (G₁ n) (G₂ n)) → DfR (F₁.nlᴰ G₁) (F₂.nlᴰ G₂)
  nl-R h = dfr (λ wm tm₁ tm₂ lm → ml (λ n → at (h n) wm tm₁ tm₂ lm))

  ⊕-R : ∀ {W} (lW : LgW L₀ W) {Y₁ : T₁.St W} {Y₂ : T₂.St W} {Δ₁ : T₁.Df W} {Δ₂ : T₂.Df W} → StR Y₁ Y₂ → DfR Δ₁ Δ₂ →
        StR (F₁._⊕⟨_⟩_ Y₁ lW Δ₁) (F₂._⊕⟨_⟩_ Y₂ lW Δ₂)
  ⊕-R lW hY hΔ = str (⨾-R (dR hY) hΔ)

  -- 右边的状态多接一段
  ⊕-r : ∀ {W} (lW : LgW L₀ W) {Y₁ : T₁.St W} {Y₂ : T₂.St W} {Δ₂ : T₂.Df W} → StR Y₁ Y₂ → StR Y₁ (F₂._⊕⟨_⟩_ Y₂ lW Δ₂)
  ⊕-r lW hY = str (dfr (λ wm tm₁ tm₂ lm → mr (at (dR hY) wm tm₁ tm₂ lm)))

  cv-R : ∀ {W W′} (q : W ≤ W′) {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ → StR (F₁.cv q Y₁) (F₂.cv q Y₂)
  cv-R q hY = str (dfr (λ wm tm₁ tm₂ lm → at (dR hY) (≤tr q wm) tm₁ tm₂ lm))

  Step-R : ∀ {W} {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ → DfR (F₁.Stp Y₁) (F₂.Stp Y₂)
  Step-R hY = dfr (λ {t} wm tm₁ tm₂ lm → ml (λ _ → m⨾ (Ωd-M t (NI-⊲ tm₁ ni₁) acc⁺) (at (dR hY) wm tm₁ tm₂ lm)))

  Ig↾-R : ∀ {ly W W′} (p : W ≤ W′) {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → IgR (F₁.Ig↾ p A₁) (F₂.Ig↾ p A₂)
  Ig↾-R p hA = igr (λ p′ → ig hA (≤tr p p′))

  data RkR {k t : HB L₀} {m : Wd L₀} : F₁.Rk k t m → F₂.Rk k t m → Set where
    kp : ∀ {R R′} → RkR (F₁.keep R) (F₂.keep R′)
    rs : RkR F₁.rise F₂.rise

  rk-rel : ∀ {k t m} (x₁ : F₁.Rk k t m) (x₂ : F₂.Rk k t m) → V₁.Valid x₁ → V₂.Valid x₂ → RkR x₁ x₂
  rk-rel (F₁.keep R) (F₂.keep R′) _ _ = kp
  rk-rel (F₁.keep R) F₂.rise _ v = ⊥-elim (v R)
  rk-rel F₁.rise (F₂.keep R) v _ = ⊥-elim (v R)
  rk-rel F₁.rise F₂.rise _ _ = rs

  rkT-rel : ∀ {k t m} (km₁ : k ⊲[ m ] Λ₁) (tm₁ : t ⊲[ m ] Λ₁) (km₂ : k ⊲[ m ] Λ₂) (tm₂ : t ⊲[ m ] Λ₂) (lm : LgW L₀ m) →
            RkR (F₁.rkT km₁ tm₁ lm) (F₂.rkT km₂ tm₂ lm)
  rkT-rel km₁ tm₁ km₂ tm₂ lm = rk-rel _ _ (V₁.rk-valid km₁ tm₁ lm) (V₂.rk-valid km₂ tm₂ lm)

  Br : ∀ {ly W₀ k} (r : StH W₀ k ly) → Set
  Br {ly} {W₀} r = ∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′

  HU : ∀ {ly W₀ k} (r₁ r₂ : StH W₀ k ly) → Br r₁ → Br r₂ → Set
  HU {ly} {W₀} r₁ r₂ u₁ u₂ = ∀ {W′} (p : W₀ ≤ W′) (l : LgW L₀ W′) y₁ y₂ → RelA (accK r₁) (outS r₁ y₁) (outS r₂ y₂) → Rl ly (u₁ p l y₁) (u₂ p l y₂)

  BuT : HB L₀ → Wd L₀ → Set
  BuT ly W₀ = ∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → D ly W′
```

## §3 折叠保持关系

```agda
  Run-R   : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {x₁ x₂ : D ly W₀} → Rl ly x₁ x₂ → (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
            {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ →
            DfR (F₁.Run ac₁ x₁ q₀ lW ll₁ A₁ w₁ Y₁) (F₂.Run ac₂ x₂ q₀ lW ll₂ A₂ w₂ Y₂)
  Rpt-R   : ∀ {ly W₀ W} (ac₁ ac₂ : AccY ly) {G₁ G₂ : ℕ → D ly W₀} → (∀ n → Rl ly (G₁ n) (G₂ n)) → (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
            {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ → ∀ n →
            Rl ly (proj₁ (F₁.Rpt ac₁ G₁ q₀ lW ll₁ A₁ w₁ Y₁ n)) (proj₁ (F₂.Rpt ac₂ G₂ q₀ lW ll₂ A₂ w₂ Y₂ n)) ×
            StR (proj₂ (F₁.Rpt ac₁ G₁ q₀ lW ll₁ A₁ w₁ Y₁ n)) (proj₂ (F₂.Rpt ac₂ G₂ q₀ lW ll₂ A₂ w₂ Y₂ n))
  RunNi-R : ∀ {ly W₀ W k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
            {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ →
            DfR (F₁.RunNi ac₁ ac′₁ r₁ u₁ q₀ lW ll₁ A₁ w₁ Y₁) (F₂.RunNi ac₂ ac′₂ r₂ u₂ q₀ lW ll₂ A₂ w₂ Y₂)
  Ai-R    : ∀ {ly W₀ W k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ≤ W) (hk₁ : T₁.LW k W) (hk₂ : T₂.LW k W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
            {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ →
            IgR (F₁.Ai ac₁ ac′₁ r₁ u₁ q₀ hk₁ ll₁ A₁ w₁) (F₂.Ai ac₂ ac′₂ r₂ u₂ q₀ hk₂ ll₂ A₂ w₂)
  Chn-R   : ∀ {k W} (ac′₁ ac′₂ : AccY k) (hk₁ : T₁.LW k W) (hk₂ : T₂.LW k W) (lW : LgW L₀ W) {A₁ : T₁.Ig k W} {A₂ : T₂.Ig k W} → IgR A₁ A₂ →
            {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ → ∀ n →
            Rl k (proj₁ (F₁.Chn ac′₁ hk₁ lW A₁ Y₁ n)) (proj₁ (F₂.Chn ac′₂ hk₂ lW A₂ Y₂ n)) ×
            (Rl k (proj₁ (proj₂ (F₁.Chn ac′₁ hk₁ lW A₁ Y₁ n))) (proj₁ (proj₂ (F₂.Chn ac′₂ hk₂ lW A₂ Y₂ n))) ×
             StR (proj₂ (proj₂ (F₁.Chn ac′₁ hk₁ lW A₁ Y₁ n))) (proj₂ (proj₂ (F₂.Chn ac′₂ hk₂ lW A₂ Y₂ n))))
  RKi-R   : ∀ {ly W₀ W k t m} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
            {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ →
            (wm : W ≤ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : LgW L₀ m) {x₁ : F₁.Rk k t m} {x₂ : F₂.Rk k t m} → RkR x₁ x₂ →
            Rl t (F₁.RKi ac₁ ac′₁ r₁ u₁ q₀ lW ll₁ A₁ w₁ Y₁ (T₁.tg wm tm₁ lm) x₁) (F₂.RKi ac₂ ac′₂ r₂ u₂ q₀ lW ll₂ A₂ w₂ Y₂ (T₂.tg wm tm₂ lm) x₂)
  BNi-R   : ∀ {ly W₀ W k W′} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ r₂ : StH W₀ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₀ : W₀ ≤ W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
            {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ →
            (hk₁ : T₁.LW k W) (hk₂ : T₂.LW k W) (p : W ≤ W′) (lW′ : LgW L₀ W′) {z₁ z₂ : D k W′} → Rl k z₁ z₂ →
            DfR (F₁.BNi ac₁ ac′₁ r₁ u₁ q₀ ll₁ A₁ w₁ Y₁ hk₁ p lW′ z₁) (F₂.BNi ac₂ ac′₂ r₂ u₂ q₀ ll₂ A₂ w₂ Y₂ hk₂ p lW′ z₂)
  RKc-R   : ∀ {ly W₀ W κ} (ac₁ ac₂ : AccY ly) {v₁ v₂ : BuT ly W₀} → (∀ {W′} (p : W₀ ≤ W′) (l : LgW L₀ W′) → Rl ly (v₁ p l) (v₂ p l)) →
            (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
            {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ →
            ∀ t {m} (wm : W ≤ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : LgW L₀ m) →
            Rl t (F₁.RKc ac₁ (inj₁ κ) v₁ q₀ lW ll₁ A₁ w₁ Y₁ t (T₁.tg wm tm₁ lm)) (F₂.RKc ac₂ (inj₁ κ) v₂ q₀ lW ll₂ A₂ w₂ Y₂ t (T₂.tg wm tm₂ lm))
  RKk-R   : ∀ {ly W₀ W κ t m} (ac₁ ac₂ : AccY ly) {v₁ v₂ : BuT ly W₀} → (∀ {W′} (p : W₀ ≤ W′) (l : LgW L₀ W′) → Rl ly (v₁ p l) (v₂ p l)) →
            (q₀ : W₀ ≤ W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
            {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ →
            (wm : W ≤ m) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m ] Λ₂) (lm : LgW L₀ m) (zt : ZK T t (inj₁ κ)) →
            Rl t (F₁.RKk ac₁ (inj₁ κ) v₁ q₀ ll₁ A₁ w₁ Y₁ (T₁.tg wm tm₁ lm) zt) (F₂.RKk ac₂ (inj₁ κ) v₂ q₀ ll₂ A₂ w₂ Y₂ (T₂.tg wm tm₂ lm) zt)
  RKa-R   : ∀ {ly W₀ W κ m} (ac₁ ac₂ : AccY ly) (s : FBA T κ ⊎ ⊤) (tl : FbLgAt {T} {κ} s) → s ≡ inj₂ tt →
            {v₁ v₂ : BuT ly W₀} → (∀ {W′} (p : W₀ ≤ W′) (l : LgW L₀ W′) → Rl ly (v₁ p l) (v₂ p l)) →
            (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
            {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ →
            (wm : W ≤ m) (tm₁ : hz ⊲[ m ] Λ₁) (tm₂ : hz ⊲[ m ] Λ₂) (lm : LgW L₀ m) →
            Rl hz (F₁.RKa ac₁ s tl v₁ q₀ lW ll₁ A₁ w₁ Y₁ (T₁.tg wm tm₁ lm)) (F₂.RKa ac₂ s tl v₂ q₀ lW ll₂ A₂ w₂ Y₂ (T₂.tg wm tm₂ lm))

  Run-R ac₁ ac₂ m1 q₀ lW ll₁ ll₂ hA hw hY = ig hA ≤rf lW hw hY
  Run-R ac₁ ac₂ (m⨾ hx hy) q₀ lW ll₁ ll₂ hA hw hY =
    ⨾-R (Run-R ac₁ ac₂ hx q₀ lW ll₁ ll₂ hA hw hY)
        (Run-R ac₁ ac₂ hy q₀ lW ll₁ ll₂ hA (m⨾ hw (mw hx)) (⊕-R lW hY (Run-R ac₁ ac₂ hx q₀ lW ll₁ ll₂ hA hw hY)))
  Run-R ac₁ ac₂ (ml h) q₀ lW ll₁ ll₂ hA hw hY =
    nl-R (λ n → Run-R ac₁ ac₂ (h n) q₀ lW ll₁ ll₂ hA (proj₁ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)) (proj₂ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)))
  Run-R ac₁ ac₂ (mw {p = p} hx) q₀ lW ll₁ ll₂ hA hw hY = Run-R ac₁ ac₂ hx (≤tr p q₀) lW ll₁ ll₂ hA hw hY
  Run-R (acc f₁) (acc f₂) (mi {R = r₁} {R′ = r₂} h) q₀ lW ll₁ ll₂ hA hw hY =
    RunNi-R (acc f₁) (acc f₂) (f₁ r₁) (f₂ r₂) r₁ r₂ h q₀ lW ll₁ ll₂ hA hw hY
  Run-R ac₁ ac₂ (mc h) q₀ lW ll₁ ll₂ hA hw hY =
    dfr (λ {t} wm tm₁ tm₂ lm → RKc-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY t wm tm₁ tm₂ lm)
  Run-R ac₁ ac₂ mz q₀ lW ll₁ ll₂ hA hw hY = zero-R
  Run-R ac₁ ac₂ (mr hx) q₀ lW ll₁ ll₂ hA hw hY =
    dfr (λ wm tm₁ tm₂ lm → mr (at (Run-R ac₁ ac₂ hx q₀ lW ll₁ ll₂ hA hw hY) wm tm₁ tm₂ lm))
  Run-R ac₁ ac₂ (me hx) q₀ lW ll₁ ll₂ hA hw hY =
    dfr (λ wm tm₁ tm₂ lm → me (at (Run-R ac₁ ac₂ hx q₀ lW ll₁ ll₂ hA (mr hw) (⊕-r lW hY)) wm tm₁ tm₂ lm))
  Run-R ac₁ ac₂ (ml0 hx) q₀ lW ll₁ ll₂ hA hw hY =
    dfr (λ wm tm₁ tm₂ lm → ml0 (at (Run-R ac₁ ac₂ hx q₀ lW ll₁ ll₂ hA hw hY) wm tm₁ tm₂ lm))

  Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY zero = hw , hY
  Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY (suc n) =
    m⨾ (proj₁ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)) (mw (h n)) ,
    ⊕-R lW (proj₂ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n))
      (Run-R ac₁ ac₂ (h n) q₀ lW ll₁ ll₂ hA (proj₁ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)) (proj₂ (Rpt-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY n)))

  RunNi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY =
    dfr (λ wm tm₁ tm₂ lm →
      RKi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm
        (rkT-rel (⊲ᴮ↑ wm (F₁.kk r₁ q₀ ll₁)) tm₁ (⊲ᴮ↑ wm (F₂.kk r₂ q₀ ll₂)) tm₂ lm))

  Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ hk₁ hk₂ ll₁ ll₂ hA hw =
    igr (λ p lW′ {z₁} {z₂} rz hY′ →
      Run-R ac₁ ac₂ (hu (≤tr q₀ p) lW′ (inS r₁ z₁) (inS r₂ z₂) (conv (accK r₁) r₁ r₂ rz)) ≤rf lW′ (⊲ᴮ↑ p ll₁) (⊲ᴮ↑ p ll₂) (Ig↾-R p hA)
        (m⨾ (mw hw) (Int-M ac′₁ ac′₂ rz ≤rf lW′ (zkS {T} r₁) (zkS {T} r₂) (mkOf r₁ (≤tr q₀ p)) (mkOf r₂ (≤tr q₀ p))
                       (λ p′ l′ r′ → hu (≤tr (≤tr q₀ p) p′) l′ _ _ (conv (accK r₁) r₁ r₂ r′)) mz))
        hY′)

  Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY zero = mz , (at (dR hY) ≤rf hk₁ hk₂ lW , hY)
  Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY (suc n) =
    m⨾ (proj₁ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)) (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))) ,
    (at (Run-R ac′₁ ac′₂ (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))) ≤rf lW hk₁ hk₂ hA
              (proj₁ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)) (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))))
        ≤rf hk₁ hk₂ lW ,
     ⊕-R lW (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)))
       (Run-R ac′₁ ac′₂ (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n))) ≤rf lW hk₁ hk₂ hA
              (proj₁ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)) (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ hk₁ hk₂ lW hA hY n)))))

  RKi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm (kp {R} {R′}) =
    mi (λ p lW′ y₁ y₂ r →
      at (BNi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ ll₁ ll₂ hA hw hY (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) (≤tr wm p) lW′ (toRl (accK R) r))
         ≤rf (⊲ᴮ↑ p tm₁) (⊲ᴮ↑ p tm₂) lW′)
  RKi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm rs =
    ml (λ n →
      at (Run-R ac′₁ ac′₂ (proj₁ (proj₂ (Chn-R ac′₁ ac′₂ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) lW (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw) hY n)))
                ≤rf lW (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw)
                (proj₁ (Chn-R ac′₁ ac′₂ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) lW (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw) hY n))
                (proj₂ (proj₂ (Chn-R ac′₁ ac′₂ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) lW (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ (F₁.kk r₁ q₀ ll₁) (F₂.kk r₂ q₀ ll₂) ll₁ ll₂ hA hw) hY n))))
         wm tm₁ tm₂ lm)

  BNi-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ ll₁ ll₂ hA hw hY hk₁ hk₂ p lW′ rz =
    ig (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ hk₁ hk₂ ll₁ ll₂ hA hw) p lW′ rz
      (⊕-R lW′ (cv-R p hY)
         (Run-R ac′₁ ac′₂ rz ≤rf lW′ (⊲ᴮ↑ p hk₁) (⊲ᴮ↑ p hk₂) (Ig↾-R p (Ai-R ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₀ hk₁ hk₂ ll₁ ll₂ hA hw)) mz (cv-R p hY)))
```

**旧种类的闭包结点.** 第 0 层目标: 有损 (`lossy`), 两边都是当前世界里分支的输出重复 $\omega$ 次, 再 `drp` 到目标的世界; 第 $\ge1$ 层目标: 保留, 两边对同一个更大的世界取分支.

```agda
  RKc-R {κ = κ} ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY hz wm tm₁ tm₂ lm =
    RKa-R ac₁ ac₂ (fbA G κ) (fl κ) (lossy κ) h q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm
  RKc-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY (hs b) wm tm₁ tm₂ lm = RKk-R ac₁ ac₂ h q₀ ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm tt
  RKc-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY (hl f) wm tm₁ tm₂ lm = RKk-R ac₁ ac₂ h q₀ ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm tt
  RKc-R ac₁ ac₂ h q₀ lW ll₁ ll₂ hA hw hY (hΩ κ′ g) wm tm₁ tm₂ lm = RKk-R ac₁ ac₂ h q₀ ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm tt

  RKk-R ac₁ ac₂ h q₀ ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm zt =
    mc (λ q lW′ →
      at (Run-R ac₁ ac₂ (h (≤tr (≤tr q₀ wm) q) lW′) ≤rf lW′ (⊲ᴮ↑ (≤tr wm q) ll₁) (⊲ᴮ↑ (≤tr wm q) ll₂) (Ig↾-R (≤tr wm q) hA)
                (mw hw) (cv-R (≤tr wm q) hY))
         ≤rf (⊲ᴮ↑ q tm₁) (⊲ᴮ↑ q tm₂) lW′)

  RKa-R ac₁ ac₂ s tl refl h q₀ lW ll₁ ll₂ hA hw hY wm tm₁ tm₂ lm =
    ml (λ _ → drp-M acc⁺ acc⁺ (at (Run-R ac₁ ac₂ (h q₀ lW) ≤rf lW ll₁ ll₂ hA hw hY) ≤rf (z⊲ᴮ Λ₁) (z⊲ᴮ Λ₂) lW))
```

## §4 读到第 0 层

```agda
  cross : ∀ {ly W} (ac₁ ac₂ : AccY ly) {x₁ x₂ : D ly W} → Rl ly x₁ x₂ → (lW : LgW L₀ W) (ll₁ : T₁.LW ly W) (ll₂ : T₂.LW ly W)
          {A₁ : T₁.Ig ly W} {A₂ : T₂.Ig ly W} → IgR A₁ A₂ → {w₁ w₂ : D ly W} → Rl ly w₁ w₂ → {Y₁ : T₁.St W} {Y₂ : T₂.St W} → StR Y₁ Y₂ →
          ∀ {b b′} → b ≤ᴬ b′ →
          sum b (F₁.yc (F₁.Run ac₁ x₁ ≤rf lW ll₁ A₁ w₁ Y₁) (F₁.τ₀ lW)) ≤ᴬ sum b′ (F₂.yc (F₂.Run ac₂ x₂ ≤rf lW ll₂ A₂ w₂ Y₂) (F₂.τ₀ lW))
  cross ac₁ ac₂ hx lW ll₁ ll₂ hA hw hY h =
    sum-M acc⁺ (at (Run-R ac₁ ac₂ hx ≤rf lW ll₁ ll₂ hA hw hY) ≤rf (z⊲ᴮ Λ₁) (z⊲ᴮ Λ₂) lW) h
```
