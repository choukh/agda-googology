# 按级回灌, 否定一路 (一): 种类的级, 与 "读回不能写回自己这一级"

> 不含记号. 入口 [NegKindLv](NegKindLv.lagda.md). 本篇**不依赖**构造一路的接口 `KindLvIf` (接口定稿之前写的部分), 只用 [HtTowerTy](HtTowerTy.lagda.md) 与 [HtTowerNeg](HtTowerNeg.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> "每个种类按自己的级回灌" 先要说清 "种类的级" 是什么. `Lev c` 的种类是对 $c$ 的构造子递归给出的; 每个种类的坐标类型要么是 `A`, 要么是某个 `HB (Lev y)`. 本篇:
>
> 1. **`lvK`, `coord-lv` (定义与定理, 对一切 `S`, 一切 $c$).** `lvK c κ : ⊤ ⊎ HB S` 是种类 $\kappa$ 的级: `inj₁ tt` 表示坐标是 `A`, `inj₂ y` 表示坐标是 `HB (Lev y)`; `coord-lv`: `E (Lev c) κ ≡ Cd (lvK c κ)`. 证明是对 $c$ 的结构递归, 每一支 `refl`. 所以 "种类的级" 是树侧的概念, 不读记号, 不要判定.
> 2. **`lv-sub` (定理).** 级是 $c$ 的**严格子项**: `lvK c κ ≡ inj₂ y` 时 $y\sqsubset c$ ($\sqsubset$ 是结构子项关系 `≺ᴮ` 的传递闭包). 级 $y$ 出现在 `Lev c` 里当且仅当 $c$ 里有一个子项 `hs y` (判断, 只证了 "仅当" 的方向所需的形状).
> 3. **`no-desc`, `lv-not-self`, `no-desc-step` (定理, 否定; 对照 `HtTowerNeg.no-retract`).** 对一切 $c$, 一切种类 $\kappa$ 的级 $\ell$: `HB (Lev c)` 不是 `Cd ℓ` 的收缩 (没有 $d$, $u$ 使 $u\circ d=\mathrm{id}$). 推论: 没有种类的级是 $c$ 自己 (`lv-not-self`); 第 $c+1$ 级的高度不能无损地写进第 $c$ 级的坐标 (`no-desc-step`). 读法: **层 $c$ 的读回 (落在 `HB (Lev c)`) 只能回灌给 `step (Lev c)` 的新种类, 不能无损地回灌给 `Lev c` 自己的任何种类**; `Lev c` 的种类只能从更低的级 $y\sqsubset c$ 的读回得到坐标.
>
> **只否定什么.** 只否定 "写入 (高一级到低一级坐标) 再读回是恒等" 这一个形状 (收缩). **不否定**: 有损的写入 (例如 `NewTwrRd.flatT`, `GenFoldRd.encH`); 从低级到高级的嵌入 (`up`, `ι`); 读回本身. 这条与 `NegDnFoldRet.no-faithful` (只对坐标为 `Ht` 的种类) 同型, 这里对一切级一条.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKindLvLev where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (no-retract; _≺ᴮ_; ≺s; ≺l; ≺Ω)
```

## §1 种类的级

```agda
Cd : ∀ {S : KS} → ⊤ ⊎ HB S → Set
Cd (inj₁ _) = A
Cd (inj₂ y) = HB (Lev y)

lvK : ∀ {S : KS} (c : HB S) → K (Lev c) → ⊤ ⊎ HB S
lvK hz κ = inj₁ tt
lvK (hs x) (inj₁ κ) = lvK x κ
lvK (hs x) (inj₂ _) = inj₂ x
lvK (hl f) (n , κ) = lvK (f n) κ
lvK (hΩ κ g) (e , κ′) = lvK (g e) κ′

coord-lv : ∀ {S : KS} (c : HB S) (κ : K (Lev c)) → E (Lev c) κ ≡ Cd (lvK c κ)
coord-lv hz κ = refl
coord-lv (hs x) (inj₁ κ) = coord-lv x κ
coord-lv (hs x) (inj₂ _) = refl
coord-lv (hl f) (n , κ) = coord-lv (f n) κ
coord-lv (hΩ κ g) (e , κ′) = coord-lv (g e) κ′

-- step 的新种类的级就是 c 自己
lv-new : ∀ {S : KS} (c : HB S) → lvK (hs c) (inj₂ tt) ≡ inj₂ c
lv-new c = refl
```

## §2 级是严格子项

```agda
module _ {S : KS} where
  infix 4 _⊏_
  data _⊏_ : HB S → HB S → Set where
    one  : ∀ {x y} → x ≺ᴮ y → x ⊏ y
    snoc : ∀ {x y z} → x ⊏ y → y ≺ᴮ z → x ⊏ z

  LvP : HB S → ⊤ ⊎ HB S → Set
  LvP c (inj₁ _) = ⊤
  LvP c (inj₂ y) = y ⊏ c

  lvP-up : ∀ {x z} → x ≺ᴮ z → ∀ ℓ → LvP x ℓ → LvP z ℓ
  lvP-up q (inj₁ _) p = tt
  lvP-up q (inj₂ y) p = snoc p q

lv-sub : ∀ {S : KS} (c : HB S) (κ : K (Lev c)) → LvP c (lvK c κ)
lv-sub hz κ = tt
lv-sub (hs x) (inj₁ κ) = lvP-up ≺s (lvK x κ) (lv-sub x κ)
lv-sub (hs x) (inj₂ _) = one ≺s
lv-sub (hl f) (n , κ) = lvP-up (≺l n) (lvK (f n) κ) (lv-sub (f n) κ)
lv-sub (hΩ κ g) (e , κ′) = lvP-up (≺Ω e) (lvK (g e) κ′) (lv-sub (g e) κ′)
```

## §3 读回不能无损地写回本级或更低的级 (对照 `no-retract`)

```agda
subst-ss : ∀ {X Y : Set} (e : X ≡ Y) (y : X) → subst (λ Z → Z) (sym e) (subst (λ Z → Z) e y) ≡ y
subst-ss refl y = refl

subst-sr : ∀ {X Y : Set} (e : X ≡ Y) (y : Y) → subst (λ Z → Z) e (subst (λ Z → Z) (sym e) y) ≡ y
subst-sr refl y = refl

-- 一般: 某个种类的坐标类型等于 X 时, HB S 不是 X 的收缩
no-desc-at : ∀ {S : KS} (κ : K S) {X : Set} → E S κ ≡ X → (d : HB S → X) (u : X → HB S) → ¬ (∀ x → u (d x) ≡ x)
no-desc-at {S} κ eq d u sec =
  no-retract κ (λ x → subst (λ Z → Z) (sym eq) (d x)) (λ e → u (subst (λ Z → Z) eq e))
    (λ x → trans (cong u (subst-sr eq (d x))) (sec x))

-- 对一切 c, 一切种类的级 ℓ: HB (Lev c) 不是 Cd ℓ 的收缩
no-desc : ∀ {S : KS} (c : HB S) (κ : K (Lev c)) (d : HB (Lev c) → Cd (lvK c κ)) (u : Cd (lvK c κ) → HB (Lev c)) →
  ¬ (∀ x → u (d x) ≡ x)
no-desc c κ = no-desc-at κ (coord-lv c κ)

-- 推论: 没有种类的级是 c 自己
lv-not-self : ∀ {S : KS} (c : HB S) (κ : K (Lev c)) → ¬ (lvK c κ ≡ inj₂ c)
lv-not-self c κ eq =
  no-desc-at κ (trans (coord-lv c κ) (cong Cd eq)) (λ x → x) (λ x → x) (λ x → refl)

-- 推论: 第 c+1 级的高度不能无损地写进第 c 级的坐标
no-desc-step : ∀ {S : KS} (c : HB S) (d : HB (Lev (hs c)) → HB (Lev c)) (u : HB (Lev c) → HB (Lev (hs c))) →
  ¬ (∀ x → u (d x) ≡ x)
no-desc-step c = no-desc (hs c) (inj₂ tt)
```

**前提实例与对照.** `no-desc` 的前提是任意 $c$ 与任意种类 $\kappa$; 种类存在的实例: `Lev (hs c)` 的新种类 `inj₂ tt` (对一切 $c$, `inst-new`), 以及 `Lev c` 的底种类 (`GenFoldInst.genLev c` 的 `aK`). 反方向 (低级进高级) 有保第一位置与合法的嵌入 `up` (`HtTowerTy.up-⊲`, `Lg-up`), 所以本篇的否定只在 "向下写" 一侧. ("`up` 有左逆" 要对 $\Omega$-分支的函数外延, 本篇不写.)

```agda
inst-new : ∀ {S : KS} (c : HB S) → Σ (K (Lev (hs c))) (λ κ → lvK (hs c) κ ≡ inj₂ c)
inst-new c = inj₂ tt , refl
```

## §4 结论 (按档)

- **[定义, 定理]** `Cd`, `lvK`; **`coord-lv`** (每个种类的坐标类型是它的级给出的类型), `lv-new`; **`lv-sub`** (级是严格子项).
- **[定理, 否定]** **`no-desc-at`**, **`no-desc`**, **`lv-not-self`**, **`no-desc-step`** (由 `HtTowerNeg.no-retract`).
- **[判断]** 对 "按级回灌" 的设计的含义: 层的读回若落在 `HB (Lev c)`, 它能作坐标的种类是 `step (Lev c)` 的新种类, 或级为 $c$ 的种类 (只在比 `Lev c` 更高的结构里出现); 把它直接塞进 `Lev c` 自己的种类, 必然有损.
