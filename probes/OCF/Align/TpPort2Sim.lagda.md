# 两种种类的 Ω-极限一步 (一): 两边世界各自独立的互模拟

> 入口 [TpPort2](TpPort2.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport2/mk_tpport2.py` 从 [MonoPort8Sim](MonoPort8Sim.lagda.md) 的 §1–§7 逐字节可重生成. 公共变换用 `probes/Survey/scripts/tpport/tpgen.py` (同 `TpPort` 的克隆): 世界的类型与序 (`A`, `_⊲_` 换成 `Wd₂`, `_≤ʷ_`; `C.self`, `⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), `Step` 换名 `Stp`; 世界变量表多 `m′`, `U`, `U′`, `U₁`, `U₂`. 逐字替换: 世界的类型注记 (`{W W′ : A}` 等) 换成 `Wd₂`; `Two` 多两个实例的 `o₁`, `o₂` (两种种类的折叠要第 1 层是第一位置); `IntE` 多两个 `NZ₁` 搬运参数 `zz₁`, `zz₂` (两种种类的 `Int` 的字面), 节点一句与 `Ai-E` 的内层多 `NZ₁-S`; 原文的 `no-κE` (只对单种类的 `hΩ g` 写) 去掉, 两种种类的对应在 [TpPort2Cross](TpPort2Cross.lagda.md). 关系没有 `nκ`, `nμ` 的构造子, 所以折叠的 `nκ`, `nμ` 两句不出现. 证明逐句不变.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPort2Sim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; LgB; ⊲ᴮ↑)
open import OCF.Align.HtTowerFTree renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerFClosed using (ω⋅)
import OCF.Align.HtTowerFFold as Fold
open import OCF.Align.TpPortSim using (Free; free⊲; outS-inS)
open import OCF.Align.TpPortRun using (module Val)

```
```agda
reH : ∀ {a b m m′} → Free b → a ⊲[ m ] b → a ⊲[ m′ ] b
reH f hself = hself
reH f (hsuc p) = hsuc (reH f p)
reH f (hlim n p) = hlim n (reH (f n) p)
reH f (hLim e p) = ⊥-elim f

reS : ∀ {k t m m′} → Free t → StH m k t → StH m′ k t
reS f (ss P) = ss (reH f P)
reS f (sl n P) = sl n (reH (f n) P)
reS f (sL e P) = ⊥-elim f
```
```agda
module _ {L : Ht} (Lo : ∀ {W k} → StH W k L → ∀ {u u′} → D k u → D k u′ → Set) where
  data SimE : ∀ {W W′} → D L W → D L W′ → Set where
    e0 : ∀ {W W′} → SimE (n0 {W = W}) (n0 {W = W′})
    e1 : ∀ {W W′} → SimE (n1 {W = W}) (n1 {W = W′})
    e⨾ : ∀ {W W′} {x y : D L W} {x′ y′ : D L W′} → SimE x x′ → SimE y y′ → SimE (x ⨾ y) (x′ ⨾ y′)
    el : ∀ {W W′} {d : ℕ → D L W} {d′ : ℕ → D L W′} → (∀ n → SimE (d n) (d′ n)) → SimE (nl d) (nl d′)
    ei : ∀ {W W′ k} {R : StH W k L} {R′ : StH W′ k L}
           {v : ∀ {V} → W ≤ʷ V → LgW₂ V → Vs L R V → D L V} {v′ : ∀ {V′} → W′ ≤ʷ V′ → LgW₂ V′ → Vs L R′ V′ → D L V′} →
         (∀ {V V′} (p : W ≤ʷ V) (p′ : W′ ≤ʷ V′) (l : LgW₂ V) (l′ : LgW₂ V′) y y′ → Lo R (outS R y) (outS R′ y′) → SimE (v p l y) (v′ p′ l′ y′)) →
         SimE (ni R v) (ni R′ v′)
    ew : ∀ {W₀ W W₀′ W′} {p : W₀ ≤ʷ W} {p′ : W₀′ ≤ʷ W′} {x : D L W₀} {x′ : D L W₀′} → SimE x x′ → SimE (nw p x) (nw p′ x′)

RelE : ∀ {L} → AccY L → ∀ {W W′} → D L W → D L W′ → Set
RelE (acc g) = SimE (λ R → RelE (g R))

Re : ∀ L {W W′} → D L W → D L W′ → Set
Re L = RelE (accᴸ {L})

irrE : ∀ {L} (a b : AccY L) {W W′} {x : D L W} {y : D L W′} → RelE a x y → RelE b x y
irrE (acc f) (acc g) e0 = e0
irrE (acc f) (acc g) e1 = e1
irrE (acc f) (acc g) (e⨾ p q) = e⨾ (irrE (acc f) (acc g) p) (irrE (acc f) (acc g) q)
irrE (acc f) (acc g) (el h) = el (λ n → irrE (acc f) (acc g) (h n))
irrE (acc f) (acc g) (ei {R = R} h) = ei (λ p p′ l l′ y y′ r → irrE (acc f) (acc g) (h p p′ l l′ y y′ (irrE (g R) (f R) r)))
irrE (acc f) (acc g) (ew p) = ew (irrE (acc f) (acc g) p)

toE : ∀ {L} (a : AccY L) {W W′} {x : D L W} {y : D L W′} → RelE a x y → Re L x y
toE a = irrE a accᴸ

ofE : ∀ {L} (a : AccY L) {W W′} {x : D L W} {y : D L W′} → Re L x y → RelE a x y
ofE a = irrE accᴸ a
```
```agda
symE0 : ∀ (a : AccY hz) {W W′} {x : D hz W} {y : D hz W′} → RelE a x y → RelE a y x
symE0 (acc g) e0 = e0
symE0 (acc g) e1 = e1
symE0 (acc g) (e⨾ p q) = e⨾ (symE0 (acc g) p) (symE0 (acc g) q)
symE0 (acc g) (el h) = el (λ n → symE0 (acc g) (h n))
symE0 (acc g) (ei {R = ()} h)
symE0 (acc g) (ew p) = ew (symE0 (acc g) p)

sumE : ∀ (a : AccY hz) {W W′} {x : D₀ W} {y : D₀ W′} → RelE a x y → ∀ {b b′} → b ≤ b′ → sum b x ≤ sum b′ y
ptE  : ∀ (a : AccY hz) {W W′} {d : ℕ → D₀ W} {d′ : ℕ → D₀ W′} → (∀ n → RelE a (d n) (d′ n)) → ∀ {b b′} → b ≤ b′ → ∀ n → pt b d n ≤ pt b′ d′ n
sumE (acc g) e0 h = h
sumE (acc g) e1 h = s≤ h
sumE (acc g) (e⨾ p q) h = sumE (acc g) q (sumE (acc g) p h)
sumE (acc g) (el hd) h = l≤ (λ n → ≤l n (ptE (acc g) hd h n))
sumE (acc g) (ei {R = ()} _) h
sumE (acc g) (ew p) h = sumE (acc g) p h
ptE a hd h zero = h
ptE a hd h (suc n) = sumE a (hd n) (ptE a hd h n)
```
```agda
convE : ∀ {L W W′ k u u′} (a : AccY k) (R : StH W k L) (R′ : StH W′ k L) {x : D k u} {y : D k u′} → Re k x y →
        RelE a (outS R (inS R x)) (outS R′ (inS R′ y))
convE a R R′ {x} {y} r = subst₂ (RelE a) (sym (outS-inS R x)) (sym (outS-inS R′ y)) (ofE a r)

-- Ω_t 与自己相关, 两边世界任意, t 不含 Ω-极限
ΩdE : ∀ t → Free t → (a : AccY t) → ∀ {W W′} → RelE a (Ωd t {W}) (Ωd t {W′})
ΩdE hz ft (acc g) = e1
ΩdE (hs b) ft (acc g) = e⨾ e1 (ei (λ p p′ l l′ y y′ r → e1))
ΩdE (hl f) ft (acc g) = e⨾ e1 (el (λ n → ei (λ p p′ l l′ y y′ r → e1)))
ΩdE (hΩ _ h) () a
```
```agda
PreE : ∀ {L : Ht} {W₀ W W₀′ W′} (q₀ : W₀ ≤ʷ W) (q₀′ : W₀′ ≤ʷ W′) {d₁ : ℕ → D L W₀} {d₂ : ℕ → D L W₀′} →
       (∀ n → Re L (d₁ n) (d₂ n)) → ∀ n → Re L (Pre q₀ d₁ n) (Pre q₀′ d₂ n)
PreE q₀ q₀′ h zero = e0
PreE q₀ q₀′ h (suc n) = e⨾ (PreE q₀ q₀′ h n) (ew (h n))

UE : ∀ (k ly : Ht) (W W′ : Wd₂) → (∀ {V} → W ≤ʷ V → LgW₂ V → D k V → D ly V) → (∀ {V′} → W′ ≤ʷ V′ → LgW₂ V′ → D k V′ → D ly V′) → Set
UE k ly W W′ u₁ u₂ = ∀ {V V′} (p : W ≤ʷ V) (p′ : W′ ≤ʷ V′) (l : LgW₂ V) (l′ : LgW₂ V′) {y₁ : D k V} {y₂ : D k V′} → Re k y₁ y₂ → Re ly (u₁ p l y₁) (u₂ p′ l′ y₂)

IntE : ∀ {ly k W₀ W W₀′ W′} (a₁ a₂ : AccY k) {x₁ : D k W₀} {x₂ : D k W₀′} → Re k x₁ x₂ → (q₀ : W₀ ≤ʷ W) (q₀′ : W₀′ ≤ʷ W′) (lW : LgW₂ W) (lW′ : LgW₂ W′)
       (zy₁ zy₂ : NZ ly) (zz₁ zz₂ : NZ₁ k → NZ₁ ly) (mk₁ : ∀ {W₁ j} → W ≤ʷ W₁ → StH W₁ j k → StH W₁ j ly) (mk₂ : ∀ {W₁ j} → W′ ≤ʷ W₁ → StH W₁ j k → StH W₁ j ly)
       {u₁ : ∀ {V} → W ≤ʷ V → LgW₂ V → D k V → D ly V} {u₂ : ∀ {V′} → W′ ≤ʷ V′ → LgW₂ V′ → D k V′ → D ly V′} → UE k ly W W′ u₁ u₂ →
       {w₁ : D k W} {w₂ : D k W′} → Re k w₁ w₂ → Re ly (Int a₁ x₁ q₀ lW zy₁ zz₁ mk₁ u₁ w₁) (Int a₂ x₂ q₀′ lW′ zy₂ zz₂ mk₂ u₂ w₂)
IntE a₁ a₂ e0 q₀ q₀′ lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw = e0
IntE a₁ a₂ e1 q₀ q₀′ lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw = hu ≤rf ≤rf lW lW′ hw
IntE a₁ a₂ (e⨾ hx hy) q₀ q₀′ lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw =
  e⨾ (IntE a₁ a₂ hx q₀ q₀′ lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw) (IntE a₁ a₂ hy q₀ q₀′ lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu (e⨾ hw (ew hx)))
IntE a₁ a₂ (el h) q₀ q₀′ lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw =
  el (λ n → IntE a₁ a₂ (h n) q₀ q₀′ lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu (e⨾ hw (PreE q₀ q₀′ h n)))
IntE a₁ a₂ (ew {p = p} {p′ = p′} hx) q₀ q₀′ lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw = IntE a₁ a₂ hx (≤tr p q₀) (≤tr p′ q₀′) lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw
IntE (acc g₁) (acc g₂) (ei {R = R₁} {R′ = R₂} h) q₀ q₀′ lW lW′ zy₁ zy₂ zz₁ zz₂ mk₁ mk₂ hu hw =
  ei (λ p p′ l l′ y₁ y₂ r →
    IntE (acc g₁) (acc g₂)
      (h (≤tr q₀ p) (≤tr q₀′ p′) l l′ _ _ (convE (accK R₁) R₁ R₂ (toE (accK (mk₁ ≤rf (Kup q₀ R₁))) r)))
      ≤rf ≤rf l l′ zy₁ zy₂ zz₁ zz₂ (λ p₁ → mk₁ (≤tr p p₁)) (λ p₁ → mk₂ (≤tr p′ p₁)) (λ p₁ p₂ → hu (≤tr p p₁) (≤tr p′ p₂))
      (e⨾ (ew hw) (IntE (g₁ R₁) (g₂ R₂) (toE (accK (mk₁ ≤rf (Kup q₀ R₁))) r) ≤rf ≤rf l l′ (NZ-S R₁) (NZ-S R₂) (NZ₁-S R₁) (NZ₁-S R₂)
                     (mkOf R₁ (≤tr q₀ p)) (mkOf R₂ (≤tr q₀′ p′))
                     (λ p₁ p₂ l₁ l₂ r′ → h (≤tr (≤tr q₀ p) p₁) (≤tr (≤tr q₀′ p′) p₂) l₁ l₂ _ _ (convE (accK R₁) R₁ R₂ r′)) e0)))
```
```agda
module Two (Λ₁ : Ht) (l₁ : LgB Λ₁) (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ₁) (Λ₂ : Ht) (l₂ : LgB Λ₂) (o₂ : ∀ {w} → hs hz ⊲[ w ] Λ₂) (fr : ∀ {t m m′} → t ⊲[ m ] Λ₁ → t ⊲[ m′ ] Λ₂ → Free t) where
  module F₁ = Fold ω⋅ Λ₁ l₁ o₁
  module F₂ = Fold ω⋅ Λ₂ l₂ o₂
  module V₁ = Val Λ₁ l₁ o₁
  module V₂ = Val Λ₂ l₂ o₂

  record DfE {W W′ : Wd₂} (Δ₁ : F₁.Df W) (Δ₂ : F₂.Df W′) : Set where
    constructor dfe
    field
      at : ∀ {t m m′} (wm : W ≤ʷ m) (wm′ : W′ ≤ʷ m′) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m′ ] Λ₂) (lm : LgW₂ m) (lm′ : LgW₂ m′) →
           Re t (F₁.yc Δ₁ (F₁.tg wm tm₁ lm)) (F₂.yc Δ₂ (F₂.tg wm′ tm₂ lm′))
  open DfE public

  record StE {W W′ : Wd₂} (Y₁ : F₁.St W) (Y₂ : F₂.St W′) : Set where
    constructor ste
    field
      dE : DfE (F₁.d Y₁) (F₂.d Y₂)
  open StE public

  record IgE {ly : Ht} {W W′ : Wd₂} (A₁ : F₁.Ig ly W) (A₂ : F₂.Ig ly W′) : Set where
    constructor ige
    field
      ig : ∀ {V V′} (p : W ≤ʷ V) (p′ : W′ ≤ʷ V′) (lV : LgW₂ V) (lV′ : LgW₂ V′) {w₁ : D ly V} {w₂ : D ly V′} → Re ly w₁ w₂ →
           {Y₁ : F₁.St V} {Y₂ : F₂.St V′} → StE Y₁ Y₂ → DfE (A₁ p lV w₁ Y₁) (A₂ p′ lV′ w₂ Y₂)
  open IgE public

  zeroE : ∀ {W W′} → DfE (F₁.zeroD {W}) (F₂.zeroD {W′})
  zeroE = dfe (λ wm wm′ tm₁ tm₂ lm lm′ → e0)

  ⨾E : ∀ {W W′} {a₁ b₁ : F₁.Df W} {a₂ b₂ : F₂.Df W′} → DfE a₁ a₂ → DfE b₁ b₂ → DfE (a₁ F₁.⨾ᴰ b₁) (a₂ F₂.⨾ᴰ b₂)
  ⨾E ha hb = dfe (λ wm wm′ tm₁ tm₂ lm lm′ → e⨾ (at ha wm wm′ tm₁ tm₂ lm lm′) (at hb wm wm′ tm₁ tm₂ lm lm′))

  nlE : ∀ {W W′} {G₁ : ℕ → F₁.Df W} {G₂ : ℕ → F₂.Df W′} → (∀ n → DfE (G₁ n) (G₂ n)) → DfE (F₁.nlᴰ G₁) (F₂.nlᴰ G₂)
  nlE h = dfe (λ wm wm′ tm₁ tm₂ lm lm′ → el (λ n → at (h n) wm wm′ tm₁ tm₂ lm lm′))

  ⊕E : ∀ {W W′} (lW : LgW₂ W) (lW′ : LgW₂ W′) {Y₁ : F₁.St W} {Y₂ : F₂.St W′} {Δ₁ : F₁.Df W} {Δ₂ : F₂.Df W′} → StE Y₁ Y₂ → DfE Δ₁ Δ₂ →
       StE (F₁._⊕⟨_⟩_ Y₁ lW Δ₁) (F₂._⊕⟨_⟩_ Y₂ lW′ Δ₂)
  ⊕E lW lW′ hY hΔ = ste (⨾E (dE hY) hΔ)

  cvE : ∀ {W W′ U U′} (q : W ≤ʷ U) (q′ : W′ ≤ʷ U′) {Y₁ : F₁.St W} {Y₂ : F₂.St W′} → StE Y₁ Y₂ → StE (F₁.cv q Y₁) (F₂.cv q′ Y₂)
  cvE q q′ hY = ste (dfe (λ wm wm′ tm₁ tm₂ lm lm′ → at (dE hY) (≤tr q wm) (≤tr q′ wm′) tm₁ tm₂ lm lm′))

  StepE : ∀ {W W′} {Y₁ : F₁.St W} {Y₂ : F₂.St W′} → StE Y₁ Y₂ → DfE (F₁.Stp Y₁) (F₂.Stp Y₂)
  StepE hY = dfe (λ {t} wm wm′ tm₁ tm₂ lm lm′ → el (λ _ → e⨾ (ΩdE t (fr tm₁ tm₂) accᴸ) (at (dE hY) wm wm′ tm₁ tm₂ lm lm′)))

  Ig↾E : ∀ {ly W W′ U U′} (p : W ≤ʷ U) (p′ : W′ ≤ʷ U′) {A₁ : F₁.Ig ly W} {A₂ : F₂.Ig ly W′} → IgE A₁ A₂ → IgE (F₁.Ig↾ p A₁) (F₂.Ig↾ p′ A₂)
  Ig↾E p p′ hA = ige (λ p₁ p₂ → ig hA (≤tr p p₁) (≤tr p′ p₂))

  data RkE {k t : Ht} {m m′ : Wd₂} : F₁.Rk k t m → F₂.Rk k t m′ → Set where
    kp : ∀ {R R′} → RkE (F₁.keep R) (F₂.keep R′)
    rs : RkE F₁.rise F₂.rise

  -- 判定一致: 目标层不含 Ω-极限, 节点种类可以换世界
  rk-rel : ∀ {k t m m′} → Free t → (x₁ : F₁.Rk k t m) (x₂ : F₂.Rk k t m′) → V₁.Valid x₁ → V₂.Valid x₂ → RkE x₁ x₂
  rk-rel ft (F₁.keep R) (F₂.keep R′) _ _ = kp
  rk-rel ft (F₁.keep R) F₂.rise _ v = ⊥-elim (v (reS ft R))
  rk-rel ft F₁.rise (F₂.keep R) v _ = ⊥-elim (v (reS ft R))
  rk-rel ft F₁.rise F₂.rise _ _ = rs

  rkT-rel : ∀ {k t m m′} (km₁ : k ⊲[ m ] Λ₁) (tm₁ : t ⊲[ m ] Λ₁) (lm : LgW₂ m) (km₂ : k ⊲[ m′ ] Λ₂) (tm₂ : t ⊲[ m′ ] Λ₂) (lm′ : LgW₂ m′) →
            RkE (F₁.rkT km₁ tm₁ lm) (F₂.rkT km₂ tm₂ lm′)
  rkT-rel km₁ tm₁ lm km₂ tm₂ lm′ = rk-rel (fr tm₁ tm₂) _ _ (V₁.rk-valid km₁ tm₁ lm) (V₂.rk-valid km₂ tm₂ lm′)

  Br : ∀ {ly W₀ k} (r : StH W₀ k ly) → Set
  Br {ly} {W₀} r = ∀ {W′} → W₀ ≤ʷ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′

  HU : ∀ {ly V V′ k} (r₁ : StH V k ly) (r₂ : StH V′ k ly) → Br r₁ → Br r₂ → Set
  HU {ly} {V} {V′} r₁ r₂ u₁ u₂ = ∀ {U U′} (p : V ≤ʷ U) (p′ : V′ ≤ʷ U′) (l : LgW₂ U) (l′ : LgW₂ U′) y₁ y₂ →
                                 RelE (accK r₁) (outS r₁ y₁) (outS r₂ y₂) → Re ly (u₁ p l y₁) (u₂ p′ l′ y₂)
```
```agda
  Run-E   : ∀ {ly V₁ V₂ W₁ W₂} (ac₁ ac₂ : AccY ly) {x₁ : D ly V₁} {x₂ : D ly V₂} → Re ly x₁ x₂ →
            (q₁ : V₁ ≤ʷ W₁) (q₂ : V₂ ≤ʷ W₂) (lW₁ : LgW₂ W₁) (lW₂ : LgW₂ W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ →
            DfE (F₁.Run ac₁ x₁ q₁ lW₁ ll₁ A₁ w₁ Y₁) (F₂.Run ac₂ x₂ q₂ lW₂ ll₂ A₂ w₂ Y₂)
  Rpt-E   : ∀ {ly V₁ V₂ W₁ W₂} (ac₁ ac₂ : AccY ly) {G₁ : ℕ → D ly V₁} {G₂ : ℕ → D ly V₂} → (∀ n → Re ly (G₁ n) (G₂ n)) →
            (q₁ : V₁ ≤ʷ W₁) (q₂ : V₂ ≤ʷ W₂) (lW₁ : LgW₂ W₁) (lW₂ : LgW₂ W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ → ∀ n →
            Re ly (proj₁ (F₁.Rpt ac₁ G₁ q₁ lW₁ ll₁ A₁ w₁ Y₁ n)) (proj₁ (F₂.Rpt ac₂ G₂ q₂ lW₂ ll₂ A₂ w₂ Y₂ n)) ×
            StE (proj₂ (F₁.Rpt ac₁ G₁ q₁ lW₁ ll₁ A₁ w₁ Y₁ n)) (proj₂ (F₂.Rpt ac₂ G₂ q₂ lW₂ ll₂ A₂ w₂ Y₂ n))
  RunNi-E : ∀ {ly V₁ V₂ W₁ W₂ k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ : StH V₁ k ly) (r₂ : StH V₂ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₁ : V₁ ≤ʷ W₁) (q₂ : V₂ ≤ʷ W₂) (lW₁ : LgW₂ W₁) (lW₂ : LgW₂ W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ →
            DfE (F₁.RunNi ac₁ ac′₁ r₁ u₁ q₁ lW₁ ll₁ A₁ w₁ Y₁) (F₂.RunNi ac₂ ac′₂ r₂ u₂ q₂ lW₂ ll₂ A₂ w₂ Y₂)
  Ai-E    : ∀ {ly V₁ V₂ W₁ W₂ k} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ : StH V₁ k ly) (r₂ : StH V₂ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₁ : V₁ ≤ʷ W₁) (q₂ : V₂ ≤ʷ W₂) (hk₁ : F₁.LW k W₁) (hk₂ : F₂.LW k W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            IgE (F₁.Ai ac₁ ac′₁ r₁ u₁ q₁ hk₁ ll₁ A₁ w₁) (F₂.Ai ac₂ ac′₂ r₂ u₂ q₂ hk₂ ll₂ A₂ w₂)
  Chn-E   : ∀ {k W₁ W₂} (ac′₁ ac′₂ : AccY k) (hk₁ : F₁.LW k W₁) (hk₂ : F₂.LW k W₂) (lW₁ : LgW₂ W₁) (lW₂ : LgW₂ W₂)
            {A₁ : F₁.Ig k W₁} {A₂ : F₂.Ig k W₂} → IgE A₁ A₂ → {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ → ∀ n →
            Re k (proj₁ (F₁.Chn ac′₁ hk₁ lW₁ A₁ Y₁ n)) (proj₁ (F₂.Chn ac′₂ hk₂ lW₂ A₂ Y₂ n)) ×
            (Re k (proj₁ (proj₂ (F₁.Chn ac′₁ hk₁ lW₁ A₁ Y₁ n))) (proj₁ (proj₂ (F₂.Chn ac′₂ hk₂ lW₂ A₂ Y₂ n))) ×
             StE (proj₂ (proj₂ (F₁.Chn ac′₁ hk₁ lW₁ A₁ Y₁ n))) (proj₂ (proj₂ (F₂.Chn ac′₂ hk₂ lW₂ A₂ Y₂ n))))
  RKi-E   : ∀ {ly V₁ V₂ W₁ W₂ k t m m′} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ : StH V₁ k ly) (r₂ : StH V₂ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₁ : V₁ ≤ʷ W₁) (q₂ : V₂ ≤ʷ W₂) (lW₁ : LgW₂ W₁) (lW₂ : LgW₂ W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ →
            (wm : W₁ ≤ʷ m) (wm′ : W₂ ≤ʷ m′) (tm₁ : t ⊲[ m ] Λ₁) (tm₂ : t ⊲[ m′ ] Λ₂) (lm : LgW₂ m) (lm′ : LgW₂ m′)
            {x₁ : F₁.Rk k t m} {x₂ : F₂.Rk k t m′} → RkE x₁ x₂ →
            Re t (F₁.RKi ac₁ ac′₁ r₁ u₁ q₁ lW₁ ll₁ A₁ w₁ Y₁ (F₁.tg wm tm₁ lm) x₁) (F₂.RKi ac₂ ac′₂ r₂ u₂ q₂ lW₂ ll₂ A₂ w₂ Y₂ (F₂.tg wm′ tm₂ lm′) x₂)
  BNi-E   : ∀ {ly V₁ V₂ W₁ W₂ k U₁ U₂} (ac₁ ac₂ : AccY ly) (ac′₁ ac′₂ : AccY k) (r₁ : StH V₁ k ly) (r₂ : StH V₂ k ly) {u₁ : Br r₁} {u₂ : Br r₂} → HU r₁ r₂ u₁ u₂ →
            (q₁ : V₁ ≤ʷ W₁) (q₂ : V₂ ≤ʷ W₂) (ll₁ : F₁.LW ly W₁) (ll₂ : F₂.LW ly W₂)
            {A₁ : F₁.Ig ly W₁} {A₂ : F₂.Ig ly W₂} → IgE A₁ A₂ → {w₁ : D ly W₁} {w₂ : D ly W₂} → Re ly w₁ w₂ →
            {Y₁ : F₁.St W₁} {Y₂ : F₂.St W₂} → StE Y₁ Y₂ →
            (hk₁ : F₁.LW k W₁) (hk₂ : F₂.LW k W₂) (p : W₁ ≤ʷ U₁) (p′ : W₂ ≤ʷ U₂) (lU₁ : LgW₂ U₁) (lU₂ : LgW₂ U₂) {z₁ : D k U₁} {z₂ : D k U₂} → Re k z₁ z₂ →
            DfE (F₁.BNi ac₁ ac′₁ r₁ u₁ q₁ ll₁ A₁ w₁ Y₁ hk₁ p lU₁ z₁) (F₂.BNi ac₂ ac′₂ r₂ u₂ q₂ ll₂ A₂ w₂ Y₂ hk₂ p′ lU₂ z₂)

  Run-E ac₁ ac₂ e0 q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY = zeroE
  Run-E ac₁ ac₂ e1 q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY = ig hA ≤rf ≤rf lW₁ lW₂ hw hY
  Run-E ac₁ ac₂ (e⨾ hx hy) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY =
    ⨾E (Run-E ac₁ ac₂ hx q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY)
       (Run-E ac₁ ac₂ hy q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA (e⨾ hw (ew hx)) (⊕E lW₁ lW₂ hY (Run-E ac₁ ac₂ hx q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY)))
  Run-E ac₁ ac₂ (el h) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY =
    nlE (λ n → Run-E ac₁ ac₂ (h n) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA (proj₁ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n))
                 (proj₂ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n)))
  Run-E ac₁ ac₂ (ew {p = p} {p′ = p′} hx) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY = Run-E ac₁ ac₂ hx (≤tr p q₁) (≤tr p′ q₂) lW₁ lW₂ ll₁ ll₂ hA hw hY
  Run-E (acc f₁) (acc f₂) (ei {R = r₁} {R′ = r₂} h) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY =
    RunNi-E (acc f₁) (acc f₂) (f₁ r₁) (f₂ r₂) r₁ r₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY

  Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY zero = hw , hY
  Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY (suc n) =
    e⨾ (proj₁ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n)) (ew (h n)) ,
    ⊕E lW₁ lW₂ (proj₂ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n))
      (Run-E ac₁ ac₂ (h n) q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA (proj₁ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n))
         (proj₂ (Rpt-E ac₁ ac₂ h q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY n)))

  RunNi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY =
    dfe (λ wm wm′ tm₁ tm₂ lm lm′ →
      RKi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY wm wm′ tm₁ tm₂ lm lm′
        (rkT-rel (⊲ᴮ↑ wm (F₁.kk r₁ q₁ ll₁)) tm₁ lm (⊲ᴮ↑ wm′ (F₂.kk r₂ q₂ ll₂)) tm₂ lm′))

  Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ hk₁ hk₂ ll₁ ll₂ hA hw =
    ige (λ p p′ lV lV′ {z₁} {z₂} rz hY′ →
      Run-E ac₁ ac₂ (hu (≤tr q₁ p) (≤tr q₂ p′) lV lV′ (inS r₁ z₁) (inS r₂ z₂) (convE (accK r₁) r₁ r₂ rz)) ≤rf ≤rf lV lV′
        (⊲ᴮ↑ p ll₁) (⊲ᴮ↑ p′ ll₂) (Ig↾E p p′ hA)
        (e⨾ (ew hw) (IntE ac′₁ ac′₂ rz ≤rf ≤rf lV lV′ (NZ-S r₁) (NZ-S r₂) (NZ₁-S r₁) (NZ₁-S r₂) (mkOf r₁ (≤tr q₁ p)) (mkOf r₂ (≤tr q₂ p′))
                       (λ p₁ p₂ l₁ l₂ r′ → hu (≤tr (≤tr q₁ p) p₁) (≤tr (≤tr q₂ p′) p₂) l₁ l₂ _ _ (convE (accK r₁) r₁ r₂ r′)) e0))
        hY′)

  Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY zero = e0 , (at (dE hY) ≤rf ≤rf hk₁ hk₂ lW₁ lW₂ , hY)
  Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY (suc n) =
    e⨾ (proj₁ (Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)) (proj₁ (proj₂ (Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n))) ,
    (at (Run-E ac′₁ ac′₂ (proj₁ (proj₂ (Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n))) ≤rf ≤rf lW₁ lW₂ hk₁ hk₂ hA
              (proj₁ (Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)) (proj₂ (proj₂ (Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n))))
        ≤rf ≤rf hk₁ hk₂ lW₁ lW₂ ,
     ⊕E lW₁ lW₂ (proj₂ (proj₂ (Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)))
       (Run-E ac′₁ ac′₂ (proj₁ (proj₂ (Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n))) ≤rf ≤rf lW₁ lW₂ hk₁ hk₂ hA
              (proj₁ (Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)) (proj₂ (proj₂ (Chn-E ac′₁ ac′₂ hk₁ hk₂ lW₁ lW₂ hA hY n)))))

  RKi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY wm wm′ tm₁ tm₂ lm lm′ (kp {R} {R′}) =
    ei (λ p p′ l l′ y₁ y₂ r →
      at (BNi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ ll₁ ll₂ hA hw hY (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) (≤tr wm p) (≤tr wm′ p′) l l′ (toE (accK R) r))
         ≤rf ≤rf (⊲ᴮ↑ p tm₁) (⊲ᴮ↑ p′ tm₂) l l′)
  RKi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ lW₁ lW₂ ll₁ ll₂ hA hw hY wm wm′ tm₁ tm₂ lm lm′ rs =
    el (λ n →
      at (Run-E ac′₁ ac′₂ (proj₁ (proj₂ (Chn-E ac′₁ ac′₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) lW₁ lW₂ (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) ll₁ ll₂ hA hw) hY n)))
                ≤rf ≤rf lW₁ lW₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) ll₁ ll₂ hA hw)
                (proj₁ (Chn-E ac′₁ ac′₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) lW₁ lW₂ (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) ll₁ ll₂ hA hw) hY n))
                (proj₂ (proj₂ (Chn-E ac′₁ ac′₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) lW₁ lW₂ (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ (F₁.kk r₁ q₁ ll₁) (F₂.kk r₂ q₂ ll₂) ll₁ ll₂ hA hw) hY n))))
         wm wm′ tm₁ tm₂ lm lm′)

  BNi-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ ll₁ ll₂ hA hw hY hk₁ hk₂ p p′ lU₁ lU₂ rz =
    ig (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ hk₁ hk₂ ll₁ ll₂ hA hw) p p′ lU₁ lU₂ rz
      (⊕E lU₁ lU₂ (cvE p p′ hY)
         (Run-E ac′₁ ac′₂ rz ≤rf ≤rf lU₁ lU₂ (⊲ᴮ↑ p hk₁) (⊲ᴮ↑ p′ hk₂)
            (Ig↾E p p′ (Ai-E ac₁ ac₂ ac′₁ ac′₂ r₁ r₂ hu q₁ q₂ hk₁ hk₂ ll₁ ll₂ hA hw)) e0 (cvE p p′ hY)))
```
