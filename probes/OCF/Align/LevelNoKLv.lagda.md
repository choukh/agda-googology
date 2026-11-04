# 名字无关的层号语法: 由 [GuardTightLv](GuardTightLv.lagda.md) 用脚本改写

> 不含记号. 结论写在 [LevelNoK](LevelNoK.lagda.md). `LG`, 路径, 位置, 搬运 `⊴` 的形状不变. 改动都是一件事: **两个下标之间不再有 `D` 上的关系 (`η ≅ᴰ η′`, `η ⊑ᴰ η′`, `η <ᴰ ℓ`), 只有同一个下界 $c$ 之上的证据之间的关系 (`e ≤ᵉ e′`, `e <ᵉ F`).** 所以 $\mathbb U$ 上模式匹配时每个值只有一个父亲, 不形成回路.
>
> - `_≅ᴰ_`: 两个下界的守卫纤维在 `D` 上同构且保序. 这是 `Lv` 里的记录, 不再是 `Dom` 的字段.
> - `_≈_`: `o≈ d e h h⁻ hˡ hʳ`. `h η e : g η e ≈ g′ η (conv d e)`: 同一个 $\eta$, 证据由 `conv d` 算出. 没有 "任意两个证据". `h⁻` 是逆向的 (这样 `≈-sym` 与 `tr⁻O` 的递归还是结构的), `hˡ`, `hʳ` 是两边各自的自反 (`selfAt`, `selfC`, `cmpN` 要).
> - `WFˢ`: 上升读 `e ≤ᵉ e′`.
> - `Up`, `at`, `Bel′`: 表的值是节点加纤维里的上界 `F : c ⊑ᴰ X`. `cmpBr` 把比较放在表项的纤维里做, 再用 `h` 拉回节点. **`conv` 之间不需要相干性.**
> - `Flr`: 项是帧 (带证据), 不是 `D` 的元.
>
> 去掉了 `Ordᴵ` 的嵌入 (`b₁`, `rd`, 折叠本来不读), `WF`, `cmpF`, `cmpP` (表的路线不读), `bot` (空表没有项).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelNoKLv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
```

## §1 定义域

`D`: 下标的集合. `c ⊑ᴰ η`: $\eta$ 过下界 $c$ 的守卫. `e ≤ᵉ e′`, `e <ᵉ F`: **同一个下界之上的证据之间的关系.** `bd`: 字面上界 $F$ 之下的两个证据可比.

```agda
record Dom : Set₁ where
  infix 4 _⊑ᴰ_ _≤ᵉ_ _<ᵉ_
  field
    D      : Set
    _⊑ᴰ_   : D → D → Set
    sD     : D → D
    _≤ᵉ_   : ∀ {c a b} → c ⊑ᴰ a → c ⊑ᴰ b → Set
    _<ᵉ_   : ∀ {c a X} → c ⊑ᴰ a → c ⊑ᴰ X → Set
    bd     : ∀ {c a b X} (e₁ : c ⊑ᴰ a) (e₂ : c ⊑ᴰ b) (F : c ⊑ᴰ X) → e₁ <ᵉ F → e₂ <ᵉ F → (e₁ ≤ᵉ e₂) ⊎ (e₂ ≤ᵉ e₁)
    sF     : ∀ {c η} → c ⊑ᴰ η → c ⊑ᴰ sD η
    self<ᵉ : ∀ {c η} (e : c ⊑ᴰ η) → e <ᵉ sF e

module Lv (𝔻 : Dom) where
  open Dom 𝔻 public
```

## §2 层号, 路径, 第一路径, 位置

`_≪_`: 第一路径, 不走 `bra`. `Cpᶠ`: 第一位置. 这是节点的路径与闭包的位置将来用的东西: 两者都不需要证据.

```agda
  data LG : Set where
    zero : LG
    suc  : LG → LG
    lim  : (ℕ → LG) → LG
    lc   : (c : D) (t : LG) (g : (η : D) → c ⊑ᴰ η → LG) → LG

  infix 4 _<_ _≪_
  data _<_ : LG → LG → Set where
    zero : ∀ {a} → a < suc a
    suc  : ∀ {a b} → a < b → a < suc b
    lim  : ∀ {a f} n → a < f n → a < lim f
    fst  : ∀ {a c t g} → a < t → a < lc c t g
    bra  : ∀ {a c t g} (η : D) (e : c ⊑ᴰ η) → a < g η e → a < lc c t g

  data _≪_ : LG → LG → Set where
    zero : ∀ {a} → a ≪ suc a
    suc  : ∀ {a b} → a ≪ b → a ≪ suc b
    lim  : ∀ {a f} n → a ≪ f n → a ≪ lim f
    fst  : ∀ {a c t g} → a ≪ t → a ≪ lc c t g

  ≪→< : ∀ {a b} → a ≪ b → a < b
  ≪→< zero      = zero
  ≪→< (suc r)   = suc (≪→< r)
  ≪→< (lim n r) = lim n (≪→< r)
  ≪→< (fst r)   = fst (≪→< r)

  data Cpᶠ : LG → LG → Set where
    self : ∀ {c} → Cpᶠ c c
    suc  : ∀ {a b} → Cpᶠ a b → Cpᶠ a (suc b)
    lim  : ∀ {a f} n → Cpᶠ a (f n) → Cpᶠ a (lim f)
    fst  : ∀ {a c t g} → Cpᶠ a t → Cpᶠ a (lc c t g)
```

## §3 结构相等

`_≅ᴰ_`: 两个下界的守卫纤维同构, 保 $\le^e$, $<^e$. `o≈`: 同一个 $\eta$, 证据由 `conv` 算出. 部分等价: `hˡ`, `hʳ` 是两边的自反.

```agda
  infix 4 _≅ᴰ_
  record _≅ᴰ_ (c c′ : D) : Set where
    field
      conv    : ∀ {η} → c ⊑ᴰ η → c′ ⊑ᴰ η
      conv⁻   : ∀ {η} → c′ ⊑ᴰ η → c ⊑ᴰ η
      ret     : ∀ {η} (e : c ⊑ᴰ η) → conv⁻ (conv e) ≡ e
      sec     : ∀ {η} (e : c′ ⊑ᴰ η) → conv (conv⁻ e) ≡ e
      ≤-conv  : ∀ {a b} (e₁ : c ⊑ᴰ a) (e₂ : c ⊑ᴰ b) → e₁ ≤ᵉ e₂ → conv e₁ ≤ᵉ conv e₂
      ≤-conv⁻ : ∀ {a b} (e₁ : c′ ⊑ᴰ a) (e₂ : c′ ⊑ᴰ b) → e₁ ≤ᵉ e₂ → conv⁻ e₁ ≤ᵉ conv⁻ e₂
      <-conv  : ∀ {a b} (e₁ : c ⊑ᴰ a) (e₂ : c ⊑ᴰ b) → e₁ <ᵉ e₂ → conv e₁ <ᵉ conv e₂
      <-conv⁻ : ∀ {a b} (e₁ : c′ ⊑ᴰ a) (e₂ : c′ ⊑ᴰ b) → e₁ <ᵉ e₂ → conv⁻ e₁ <ᵉ conv⁻ e₂
  open _≅ᴰ_ public

  ≅ᴰ-refl : ∀ x → x ≅ᴰ x
  ≅ᴰ-refl x = record
    { conv = λ e → e ; conv⁻ = λ e → e ; ret = λ e → refl ; sec = λ e → refl
    ; ≤-conv = λ _ _ s → s ; ≤-conv⁻ = λ _ _ s → s ; <-conv = λ _ _ s → s ; <-conv⁻ = λ _ _ s → s }

  ≅ᴰ-sym : ∀ {x y} → x ≅ᴰ y → y ≅ᴰ x
  ≅ᴰ-sym d = record
    { conv = conv⁻ d ; conv⁻ = conv d ; ret = sec d ; sec = ret d
    ; ≤-conv = ≤-conv⁻ d ; ≤-conv⁻ = ≤-conv d ; <-conv = <-conv⁻ d ; <-conv⁻ = <-conv d }

  ≅ᴰ-trans : ∀ {x y z} → x ≅ᴰ y → y ≅ᴰ z → x ≅ᴰ z
  ≅ᴰ-trans d d′ = record
    { conv = λ e → conv d′ (conv d e)
    ; conv⁻ = λ e → conv⁻ d (conv⁻ d′ e)
    ; ret = λ e → trans (cong (conv⁻ d) (ret d′ (conv d e))) (ret d e)
    ; sec = λ e → trans (cong (conv d′) (sec d (conv⁻ d′ e))) (sec d′ e)
    ; ≤-conv = λ e₁ e₂ s → ≤-conv d′ _ _ (≤-conv d e₁ e₂ s)
    ; ≤-conv⁻ = λ e₁ e₂ s → ≤-conv⁻ d _ _ (≤-conv⁻ d′ e₁ e₂ s)
    ; <-conv = λ e₁ e₂ s → <-conv d′ _ _ (<-conv d e₁ e₂ s)
    ; <-conv⁻ = λ e₁ e₂ s → <-conv⁻ d _ _ (<-conv⁻ d′ e₁ e₂ s)
    }

  infix 4 _≈_
  data _≈_ : LG → LG → Set where
    z≈ : zero ≈ zero
    s≈ : ∀ {a b} → a ≈ b → suc a ≈ suc b
    l≈ : ∀ {f g} → (∀ n → f n ≈ g n) → lim f ≈ lim g
    o≈ : ∀ {c c′ t t′ g g′} (d : c ≅ᴰ c′) → t ≈ t′ →
         (∀ (η : D) (e : c ⊑ᴰ η) → g η e ≈ g′ η (conv d e)) →
         (∀ (η : D) (e : c′ ⊑ᴰ η) → g η (conv⁻ d e) ≈ g′ η e) →
         (∀ (η : D) (e : c ⊑ᴰ η) → g η e ≈ g η e) →
         (∀ (η : D) (e : c′ ⊑ᴰ η) → g′ η e ≈ g′ η e) → lc c t g ≈ lc c′ t′ g′

  ≈-sym : ∀ {a b} → a ≈ b → b ≈ a
  ≈-sym z≈ = z≈
  ≈-sym (s≈ e) = s≈ (≈-sym e)
  ≈-sym (l≈ h) = l≈ (λ n → ≈-sym (h n))
  ≈-sym (o≈ d e h h⁻ hˡ hʳ) = o≈ (≅ᴰ-sym d) (≈-sym e) (λ η e′ → ≈-sym (h⁻ η e′)) (λ η e′ → ≈-sym (h η e′)) hʳ hˡ

  ≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
  ≈-trans z≈ z≈ = z≈
  ≈-trans (s≈ e) (s≈ e′) = s≈ (≈-trans e e′)
  ≈-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈-trans (h n) (h′ n))
  ≈-trans (o≈ d e h h⁻ hˡ hʳ) (o≈ d′ e′ h′ h′⁻ hˡ′ hʳ′) =
    o≈ (≅ᴰ-trans d d′) (≈-trans e e′)
       (λ η e₁ → ≈-trans (h η e₁) (h′ η (conv d e₁)))
       (λ η e₁ → ≈-trans (h⁻ η (conv⁻ d′ e₁)) (h′⁻ η e₁))
       hˡ hʳ′

  ≈-reflˡ : ∀ {a b} → a ≈ b → a ≈ a
  ≈-reflˡ z≈ = z≈
  ≈-reflˡ (s≈ e) = s≈ (≈-reflˡ e)
  ≈-reflˡ (l≈ h) = l≈ (λ n → ≈-reflˡ (h n))
  ≈-reflˡ (o≈ d e h h⁻ hˡ hʳ) = o≈ (≅ᴰ-refl _) (≈-reflˡ e) hˡ hˡ hˡ hˡ

  oc≅ : ∀ {c t g c′ t′ g′} → lc c t g ≈ lc c′ t′ g′ → c ≅ᴰ c′
  oc≅ (o≈ d e h h⁻ hˡ hʳ) = d

  -- 分支沿 ≈
  hh : ∀ {c t g c′ t′ g′} (o : lc c t g ≈ lc c′ t′ g′) η (e : c ⊑ᴰ η) → g η e ≈ g′ η (conv (oc≅ o) e)
  hh (o≈ d e h h⁻ hˡ hʳ) = h

  hh⁻ : ∀ {c t g c′ t′ g′} (o : lc c t g ≈ lc c′ t′ g′) η (e : c′ ⊑ᴰ η) → g η (conv⁻ (oc≅ o) e) ≈ g′ η e
  hh⁻ (o≈ d e h h⁻ hˡ hʳ) = h⁻

  -- conv 沿 ≈ 的计算
  oc-tr : ∀ {c t g c′ t′ g′ c″ t″ g″ η} (o : lc c t g ≈ lc c′ t′ g′) (o′ : lc c′ t′ g′ ≈ lc c″ t″ g″) (e : c ⊑ᴰ η) →
          conv (oc≅ (≈-trans o o′)) e ≡ conv (oc≅ o′) (conv (oc≅ o) e)
  oc-tr (o≈ d _ _ _ _ _) (o≈ d′ _ _ _ _ _) e = refl

  oc-sym : ∀ {c t g c′ t′ g′ η} (o : lc c t g ≈ lc c′ t′ g′) (e : c′ ⊑ᴰ η) → conv (oc≅ (≈-sym o)) e ≡ conv⁻ (oc≅ o) e
  oc-sym (o≈ d _ _ _ _ _) e = refl

  oc-sym-ret : ∀ {c t g c′ t′ g′ η} (o : lc c t g ≈ lc c′ t′ g′) (e : c ⊑ᴰ η) → conv (oc≅ (≈-sym o)) (conv (oc≅ o) e) ≡ e
  oc-sym-ret (o≈ d _ _ _ _ _) e = ret d e

  oc-sym-sec : ∀ {c t g c′ t′ g′ η} (o : lc c t g ≈ lc c′ t′ g′) (e : c′ ⊑ᴰ η) → conv (oc≅ o) (conv (oc≅ (≈-sym o)) e) ≡ e
  oc-sym-sec (o≈ d _ _ _ _ _) e = sec d e

  -- ≈ 或字面相等 (从 LevelFixBase 移上来: 帧的证据要它)
  Lk : LG → LG → Set
  Lk a b = (a ≈ b) ⊎ (a ≡ b)

  lkG : ∀ {c c′ t t′ g g′ η} → Lk (lc c t g) (lc c′ t′ g′) → c ⊑ᴰ η → c′ ⊑ᴰ η
  lkG (inj₁ o) e = conv (oc≅ o) e
  lkG (inj₂ refl) e = e

  lkT : ∀ {a b c} → a ≈ b → Lk b c → Lk a c
  lkT e (inj₁ d) = inj₁ (≈-trans e d)
  lkT e (inj₂ refl) = inj₁ e

  lkC : ∀ {a b c} → Lk a b → Lk b c → Lk a c
  lkC (inj₁ d) k = lkT d k
  lkC (inj₂ refl) k = k

  lkS : ∀ {a b} → Lk a b → Lk b a
  lkS (inj₁ d) = inj₁ (≈-sym d)
  lkS (inj₂ refl) = inj₂ refl

  lk→≈ : ∀ {a b} → a ≈ a → Lk a b → a ≈ b
  lk→≈ s (inj₁ d) = d
  lk→≈ s (inj₂ refl) = s

  lkG-∘ : ∀ {c c′ c″ t t′ t″ g g′ g″ η} (k : Lk (lc c t g) (lc c′ t′ g′)) (k′ : Lk (lc c′ t′ g′) (lc c″ t″ g″)) (e : c ⊑ᴰ η) →
          lkG k′ (lkG k e) ≡ lkG (lkC k k′) e
  lkG-∘ (inj₂ refl) k′ e = refl
  lkG-∘ (inj₁ (o≈ d _ _ _ _ _)) (inj₂ refl) e = refl
  lkG-∘ (inj₁ (o≈ d _ _ _ _ _)) (inj₁ (o≈ d′ _ _ _ _ _)) e = refl
```

## §4 表与可容许性

表: 节点, 与节点纤维里的上界. `at` 的形状不变, 值从 `D` 换成 `Up`. `Bel′`: 证据被 `≈` 搬到表项的纤维里, 在字面上界之下. `CovB`: 帧的证据是路径证据的像.

```agda
  record Up : Set where
    constructor mkU
    field
      uc : D
      ut : LG
      ug : (η : D) → uc ⊑ᴰ η → LG
      uX : D
      uF : uc ⊑ᴰ uX
  open Up public

  key : Up → LG
  key u = lc (uc u) (ut u) (ug u)

  infixl 5 _▸_
  data Ents : Set where
    ∅   : Ents
    _▸_ : Ents → Up → Ents

  at : Ents → LG → Up → Set
  at ∅         y u = ⊥
  at (E ▸ w)   y u = ((y ≈ key w) × (u ≡ w)) ⊎ (((y ≈ key w) → ⊥) × at E y u)

  at-resp : ∀ {E y y′ u} → y ≈ y′ → at E y u → at E y′ u
  at-resp {E = ∅} e ()
  at-resp {E ▸ w} e (inj₁ (d , r)) = inj₁ (≈-trans (≈-sym e) d , r)
  at-resp {E ▸ w} e (inj₂ (n , a)) = inj₂ ((λ d → n (≈-trans e d)) , at-resp {E} e a)

  at-uq : ∀ {E y y′ u u′} → y ≈ y′ → at E y u → at E y′ u′ → u ≡ u′
  at-uq {E = ∅} e ()
  at-uq {E ▸ w} e (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
  at-uq {E ▸ w} e (inj₁ (d , _)) (inj₂ (n , _)) = ⊥-elim (n (≈-trans (≈-sym e) d))
  at-uq {E ▸ w} e (inj₂ (n , _)) (inj₁ (d , _)) = ⊥-elim (n (≈-trans e d))
  at-uq {E ▸ w} e (inj₂ (_ , a)) (inj₂ (_ , b)) = at-uq {E} e a b

  -- 活的分支变量 (帧): 闭包的节点与这一枝的值
  record Frm : Set where
    constructor frm
    field
      fc : D
      ft : LG
      fg : (η : D) → fc ⊑ᴰ η → LG
      fη : D
      fe : fc ⊑ᴰ fη
  open Frm public

  κ : Frm → LG
  κ f = lc (fc f) (ft f) (fg f)

  yf : Frm → LG
  yf f = fg f (fη f) (fe f)

  infixr 5 _∪_
  data Fl : Set where
    tz  : Fl
    tk  : Frm → Fl
    _∪_ : Fl → Fl → Fl

  data Mem : Fl → Frm → Set where
    hr : ∀ {f} → Mem (tk f) f
    ml : ∀ {a b f} → Mem a f → Mem (a ∪ b) f
    mr : ∀ {a b f} → Mem b f → Mem (a ∪ b) f

  Wk : Fl → Fl → Set
  Wk π ρ = ∀ {f} → Mem π f → Mem ρ f

  -- 分支值的来源: 表, 或活的帧
  data Src : Set where
    tab : Ents → Src
    cov : Fl → Src

  CovB : Fl → ∀ c t (g : (η : D) → c ⊑ᴰ η → LG) {η} → c ⊑ᴰ η → Set
  CovB π c t g {η} e = Σ D λ c₁ → Σ LG λ t₁ → Σ ((x : D) → c₁ ⊑ᴰ x → LG) λ g₁ → Σ (c₁ ⊑ᴰ η) λ e₁ →
    Mem π (frm c₁ t₁ g₁ η e₁) × Σ (Lk (lc c t g) (lc c₁ t₁ g₁)) λ k → e₁ ≡ lkG k e

  Bel′ : Ents → ∀ c t (g : (η : D) → c ⊑ᴰ η → LG) {η} → c ⊑ᴰ η → Set
  Bel′ E c t g e = Σ Up λ u → at E (lc c t g) u × Σ (lc c t g ≈ key u) λ o → conv (oc≅ o) e <ᵉ uF u

  Bel : Src → ∀ c t (g : (η : D) → c ⊑ᴰ η → LG) {η} → c ⊑ᴰ η → Set
  Bel (tab E) c t g e = Bel′ E c t g e
  Bel (cov π) c t g e = CovB π c t g e

  Bel-resp : ∀ {E c t g c′ t′ g′ η} (o : lc c t g ≈ lc c′ t′ g′) {e : c ⊑ᴰ η} → Bel E c t g e → Bel E c′ t′ g′ (conv (oc≅ o) e)
  Bel-resp {tab E} {c} {t} {g} {c′} {t′} {g′} o {e} (u , a , o₁ , q) =
    u , at-resp {E} o a , ≈-trans (≈-sym o) o₁ , subst (λ z → z <ᵉ uF u) (sym (tr-sym o o₁)) q
    where
    tr-sym : ∀ {c₁ t₁ g₁} (o : lc c t g ≈ lc c′ t′ g′) (o₁ : lc c t g ≈ lc c₁ t₁ g₁) →
             conv (oc≅ (≈-trans (≈-sym o) o₁)) (conv (oc≅ o) e) ≡ conv (oc≅ o₁) e
    tr-sym (o≈ d _ _ _ _ _) (o≈ d₁ _ _ _ _ _) = cong (conv d₁) (ret d e)
  Bel-resp {cov π} {c} {t} {g} {c′} {t′} {g′} o {e} (c₁ , t₁ , g₁ , e₁ , m , inj₁ d , eq) =
    c₁ , t₁ , g₁ , e₁ , m , inj₁ (≈-trans (≈-sym o) d) , trans eq (sym (tr-sym o d))
    where
    tr-sym : ∀ {c₁ t₁ g₁} (o : lc c t g ≈ lc c′ t′ g′) (o₁ : lc c t g ≈ lc c₁ t₁ g₁) →
             conv (oc≅ (≈-trans (≈-sym o) o₁)) (conv (oc≅ o) e) ≡ conv (oc≅ o₁) e
    tr-sym (o≈ d _ _ _ _ _) (o≈ d₁ _ _ _ _ _) = cong (conv d₁) (ret d e)
  Bel-resp {cov π} o {e} (c₁ , t₁ , g₁ , e₁ , m , inj₂ refl , eq) =
    c₁ , t₁ , g₁ , e₁ , m , inj₁ (≈-sym o) , trans eq (sym (oc-sym-ret o e))

  Adm : Src → ∀ {a c} → a < c → Set
  Adm E zero      = ⊤
  Adm E (suc r)   = Adm E r
  Adm E (lim n r) = Adm E r
  Adm E (fst r)   = Adm E r
  Adm E (bra {c = c} {t = t} {g = g} η e r) = Bel E c t g e × Adm E r

  data Cp : LG → LG → Set where
    self : ∀ {c} → Cp c c
    suc  : ∀ {a b} → Cp a b → Cp a (suc b)
    lim  : ∀ {a f} n → Cp a (f n) → Cp a (lim f)
    fst  : ∀ {a c t g} → Cp a t → Cp a (lc c t g)
    bra  : ∀ {a c t g} (η : D) (e : c ⊑ᴰ η) → Cp a (g η e) → Cp a (lc c t g)

  AdmC : Src → ∀ {a c} → Cp a c → Set
  AdmC E self      = ⊤
  AdmC E (suc r)   = AdmC E r
  AdmC E (lim n r) = AdmC E r
  AdmC E (fst r)   = AdmC E r
  AdmC E (bra {c = c} {t = t} {g = g} η e r) = Bel E c t g e × AdmC E r
```

## §4′ 搬运: 路径, 第一路径, 位置

`a ⊑ b`: 路径搬运, 带对一切表的转移 (与 [LvKeyBase](LvKeyBase.lagda.md) 同形). **`cmpF`, `cmpP` 不读转移.** `a ⊑ᶠ b`: 第一路径搬到第一路径. `a ⊑ᵏ b`: 闭包的第一位置搬到第一位置. `a ⊑ᴷ b`: 闭包的位置搬到位置, 带转移. 四者合起来是 `⊴`. 读回的闭包定理对这四者一样成立, 因为它只用几条封闭性 (`⊴-*`).

```agda
  record _≺⟨_⟩_ (a : LG) (A : Src → Set) (b : LG) : Set where
    constructor viaᴸ
    field
      {rep} : LG
      eqv   : a ≈ rep
      pth   : rep < b
      trf   : ∀ E → A E → Adm E pth
  open _≺⟨_⟩_ public

  record _≺ᶠ_ (a b : LG) : Set where
    constructor preᶠ
    field
      {repᶠ} : LG
      eqvᶠ   : a ≈ repᶠ
      pthᶠ   : repᶠ ≪ b
  open _≺ᶠ_ public

  record Kvᶠ (c : D) (t : LG) (g : (η : D) → c ⊑ᴰ η → LG) (b : LG) : Set where
    constructor viaᵏ
    field
      {kc} : D
      {kt} : LG
      {kg} : (η : D) → kc ⊑ᴰ η → LG
      keq  : lc c t g ≈ lc kc kt kg
      kpth : Cpᶠ (lc kc kt kg) b
  open Kvᶠ public

  record Kv (c : D) (t : LG) (g : (η : D) → c ⊑ᴰ η → LG) (A : Src → Set) (b : LG) : Set where
    constructor viaᴷ
    field
      {kc′} : D
      {kt′} : LG
      {kg′} : (η : D) → kc′ ⊑ᴰ η → LG
      keq′  : lc c t g ≈ lc kc′ kt′ kg′
      kpth′ : Cp (lc kc′ kt′ kg′) b
      ktrf  : ∀ E → A E → AdmC E kpth′
  open Kv public

  infix 4 _⊑_ _⊑ᶠ_ _⊑ᵏ_ _⊑ᴷ_ _⊴_
  _⊑_ _⊑ᶠ_ _⊑ᵏ_ _⊑ᴷ_ : LG → LG → Set
  a ⊑ b  = ∀ {k} (r : k < a) → k ≺⟨ (λ E → Adm E r) ⟩ b
  a ⊑ᶠ b = ∀ {k} → k ≪ a → k ≺ᶠ b
  a ⊑ᵏ b = ∀ {c t g} → Cpᶠ (lc c t g) a → Kvᶠ c t g b
  a ⊑ᴷ b = ∀ {c t g} (p : Cp (lc c t g) a) → Kv c t g (λ E → AdmC E p) b

  record _⊴_ (a b : LG) : Set where
    constructor ⊴i
    field
      ⊴p : a ⊑ b
      ⊴f : a ⊑ᶠ b
      ⊴k : a ⊑ᵏ b
      ⊴K : a ⊑ᴷ b
  open _⊴_ public

  ≈-move : ∀ {a b} → a ≈ b → a ⊑ b
  ≈-move (s≈ e) zero = viaᴸ e zero (λ _ _ → tt)
  ≈-move (s≈ e) (suc r) with ≈-move e r
  ... | viaᴸ d p t = viaᴸ d (suc p) t
  ≈-move (l≈ h) (lim n r) with ≈-move (h n) r
  ... | viaᴸ d p t = viaᴸ d (lim n p) t
  ≈-move (o≈ d e h h⁻ hˡ hʳ) (fst r) with ≈-move e r
  ... | viaᴸ d′ p t = viaᴸ d′ (fst p) t
  ≈-move (o≈ d e h h⁻ hˡ hʳ) (bra η e₁ r) with ≈-move (h η e₁) r
  ... | viaᴸ d′ p t = viaᴸ d′ (bra η (conv d e₁) p) (λ E u → Bel-resp {E} (o≈ d e h h⁻ hˡ hʳ) (proj₁ u) , t E (proj₂ u))

  ≈-moveᶠ : ∀ {a b} → a ≈ b → a ⊑ᶠ b
  ≈-moveᶠ (s≈ e) zero = preᶠ e zero
  ≈-moveᶠ (s≈ e) (suc r) with ≈-moveᶠ e r
  ... | preᶠ d p = preᶠ d (suc p)
  ≈-moveᶠ (l≈ h) (lim n r) with ≈-moveᶠ (h n) r
  ... | preᶠ d p = preᶠ d (lim n p)
  ≈-moveᶠ (o≈ d e h h⁻ hˡ hʳ) (fst r) with ≈-moveᶠ e r
  ... | preᶠ d′ p = preᶠ d′ (fst p)

  ≈-moveᵏ : ∀ {a b} → a ≈ b → a ⊑ᵏ b
  ≈-moveᵏ (o≈ d e h h⁻ hˡ hʳ) self = viaᵏ (o≈ d e h h⁻ hˡ hʳ) self
  ≈-moveᵏ (s≈ e) (suc r) with ≈-moveᵏ e r
  ... | viaᵏ d p = viaᵏ d (suc p)
  ≈-moveᵏ (l≈ h) (lim n r) with ≈-moveᵏ (h n) r
  ... | viaᵏ d p = viaᵏ d (lim n p)
  ≈-moveᵏ (o≈ d e h h⁻ hˡ hʳ) (fst r) with ≈-moveᵏ e r
  ... | viaᵏ d′ p = viaᵏ d′ (fst p)

  ≈-moveᴷ : ∀ {a b} → a ≈ b → a ⊑ᴷ b
  ≈-moveᴷ (o≈ d e h h⁻ hˡ hʳ) self = viaᴷ (o≈ d e h h⁻ hˡ hʳ) self (λ _ _ → tt)
  ≈-moveᴷ (s≈ e) (suc r) with ≈-moveᴷ e r
  ... | viaᴷ d p t = viaᴷ d (suc p) t
  ≈-moveᴷ (l≈ h) (lim n r) with ≈-moveᴷ (h n) r
  ... | viaᴷ d p t = viaᴷ d (lim n p) t
  ≈-moveᴷ (o≈ d e h h⁻ hˡ hʳ) (fst r) with ≈-moveᴷ e r
  ... | viaᴷ d′ p t = viaᴷ d′ (fst p) t
  ≈-moveᴷ (o≈ d e h h⁻ hˡ hʳ) (bra η e₁ r) with ≈-moveᴷ (h η e₁) r
  ... | viaᴷ d′ p t = viaᴷ d′ (bra η (conv d e₁) p) (λ E u → Bel-resp {E} (o≈ d e h h⁻ hˡ hʳ) (proj₁ u) , t E (proj₂ u))

  ≈→⊴ : ∀ {a b} → a ≈ b → a ⊴ b
  ≈→⊴ e = ⊴i (≈-move e) (≈-moveᶠ e) (≈-moveᵏ e) (≈-moveᴷ e)

  ⊴-trans : ∀ {a b c} → a ⊴ b → b ⊴ c → a ⊴ c
  ⊴-trans {a} {b} {c} x y = ⊴i pp ff kk KK
    where
    pp : a ⊑ c
    pp r with ⊴p x r
    ... | viaᴸ d p t with ⊴p y p
    ...   | viaᴸ d′ p′ t′ = viaᴸ (≈-trans d d′) p′ (λ E u → t′ E (t E u))
    ff : a ⊑ᶠ c
    ff r with ⊴f x r
    ... | preᶠ d p with ⊴f y p
    ...   | preᶠ d′ p′ = preᶠ (≈-trans d d′) p′
    kk : a ⊑ᵏ c
    kk r with ⊴k x r
    ... | viaᵏ d p with ⊴k y p
    ...   | viaᵏ d′ p′ = viaᵏ (≈-trans d d′) p′
    KK : a ⊑ᴷ c
    KK r with ⊴K x r
    ... | viaᴷ d p t with ⊴K y p
    ...   | viaᴷ d′ p′ t′ = viaᴷ (≈-trans d d′) p′ (λ E u → t′ E (t E u))

  ⊴-zero : ∀ {b} → zero ⊴ b
  ⊴-zero = ⊴i (λ ()) (λ ()) (λ ()) (λ ())

  ⊴-lim-r : ∀ {a f} n → a ⊴ f n → a ⊴ lim f
  ⊴-lim-r {a} {f} n x = ⊴i pp ff kk KK
    where
    pp : a ⊑ lim f
    pp r with ⊴p x r
    ... | viaᴸ d p t = viaᴸ d (lim n p) t
    ff : a ⊑ᶠ lim f
    ff r with ⊴f x r
    ... | preᶠ d p = preᶠ d (lim n p)
    kk : a ⊑ᵏ lim f
    kk r with ⊴k x r
    ... | viaᵏ d p = viaᵏ d (lim n p)
    KK : a ⊑ᴷ lim f
    KK r with ⊴K x r
    ... | viaᴷ d p t = viaᴷ d (lim n p) t

  ⊴-lim-l : ∀ {f b} → (∀ n → f n ⊴ b) → lim f ⊴ b
  ⊴-lim-l h = ⊴i (λ { (lim n r) → ⊴p (h n) r }) (λ { (lim n r) → ⊴f (h n) r }) (λ { (lim n r) → ⊴k (h n) r }) (λ { (lim n r) → ⊴K (h n) r })

  ⊴-suc-r : ∀ {a b} → a ⊴ b → a ⊴ suc b
  ⊴-suc-r {a} {b} x = ⊴i pp ff kk KK
    where
    pp : a ⊑ suc b
    pp r with ⊴p x r
    ... | viaᴸ d p t = viaᴸ d (suc p) t
    ff : a ⊑ᶠ suc b
    ff r with ⊴f x r
    ... | preᶠ d p = preᶠ d (suc p)
    kk : a ⊑ᵏ suc b
    kk r with ⊴k x r
    ... | viaᵏ d p = viaᵏ d (suc p)
    KK : a ⊑ᴷ suc b
    KK r with ⊴K x r
    ... | viaᴷ d p t = viaᴷ d (suc p) t

  ⊴-fst : ∀ {a c t g} → a ⊴ t → a ⊴ lc c t g
  ⊴-fst {a} {c} {t} {g} x = ⊴i pp ff kk KK
    where
    pp : a ⊑ lc c t g
    pp r with ⊴p x r
    ... | viaᴸ d p u = viaᴸ d (fst p) u
    ff : a ⊑ᶠ lc c t g
    ff r with ⊴f x r
    ... | preᶠ d p = preᶠ d (fst p)
    kk : a ⊑ᵏ lc c t g
    kk r with ⊴k x r
    ... | viaᵏ d p = viaᵏ d (fst p)
    KK : a ⊑ᴷ lc c t g
    KK r with ⊴K x r
    ... | viaᴷ d p u = viaᴷ d (fst p) u
```

## §5 合法性

`WFˢ`: 极限相邻步进, 闭包的第一支在每个分支之下, 分支沿同一个下界之上的 `≤ᵉ` 上升.

```agda
  record Below (a b : LG) : Set where
    constructor pre
    field
      {repᵇ} : LG
      eqvᵇ   : a ≈ repᵇ
      pthᵇ   : repᵇ < b
  open Below public

  WFˢ : LG → Set
  WFˢ zero       = ⊤
  WFˢ (suc k)    = WFˢ k
  WFˢ (lim f)    = (∀ n → f n ⊴ f (suc n)) × (∀ n → WFˢ (f n))
  WFˢ (lc c t g) = (∀ η e → t ⊴ g η e) × (∀ η e η′ e′ → e ≤ᵉ e′ → g η e ⊴ g η′ e′) × WFˢ t × (∀ η e → WFˢ (g η e))

  -- 好层号
  Cfˢ : LG → Set
  Cfˢ c = WFˢ c × (c ≈ c)

  stepsˢ : ∀ {f : ℕ → LG} → (∀ n → f n ⊴ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊴ f m
  stepsˢ s zero    = s _
  stepsˢ s (suc q) = ⊴-trans (stepsˢ s q) (s _)

  selfAt : ∀ {a c} → c ≈ c → a < c → a ≈ a
  selfAt (s≈ e) zero = e
  selfAt (s≈ e) (suc r) = selfAt e r
  selfAt (l≈ h) (lim n r) = selfAt (h n) r
  selfAt (o≈ d e h h⁻ hˡ hʳ) (fst r) = selfAt e r
  selfAt (o≈ d e h h⁻ hˡ hʳ) (bra η e₁ r) = selfAt (hˡ η e₁) r
```

## §6 同一个节点上两个分支的比较

**`cmpBr`.** 两个分支值都被搬到表项的纤维里, 在同一个字面上界之下, `bd` 给可比. 比较的结果用 `o₁` 的逆拉回节点, 拉回后第二个证据不是 `e₂` 而是 `conv⁻ o₁ (conv o₂ e₂)`, 但 `≈` 的 `h` 给同一个分支值. **这里没有 `o₁`, `o₂` 的相干性, 也不要名字的回路平凡.**

```agda
  cmpBr₁ : ∀ {c t g u x y} → (∀ η (e : c ⊑ᴰ η) η′ (e′ : c ⊑ᴰ η′) → e ≤ᵉ e′ → g η e ⊴ g η′ e′) →
           (o₁ o₂ : lc c t g ≈ key u) (e₁ : c ⊑ᴰ x) (e₂ : c ⊑ᴰ y) →
           conv (oc≅ o₁) e₁ ≤ᵉ conv (oc≅ o₂) e₂ → g x e₁ ⊴ g y e₂
  cmpBr₁ {c} {t} {g} {u} {x} {y} dir o₁ o₂ e₁ e₂ s =
    ⊴-trans (dir x e₁ y e₂″ s′) (≈→⊴ (≈-trans (hh⁻ o₁ y (conv (oc≅ o₂) e₂)) (≈-sym (hh o₂ y e₂))))
    where
    e₂″ : c ⊑ᴰ y
    e₂″ = conv⁻ (oc≅ o₁) (conv (oc≅ o₂) e₂)
    s′ : e₁ ≤ᵉ e₂″
    s′ = subst (λ z → z ≤ᵉ e₂″) (ret (oc≅ o₁) e₁) (≤-conv⁻ (oc≅ o₁) _ _ s)

  cmpBr : ∀ {c t g u x y} → (∀ η (e : c ⊑ᴰ η) η′ (e′ : c ⊑ᴰ η′) → e ≤ᵉ e′ → g η e ⊴ g η′ e′) →
          (o₁ o₂ : lc c t g ≈ key u) (e₁ : c ⊑ᴰ x) (e₂ : c ⊑ᴰ y) →
          conv (oc≅ o₁) e₁ <ᵉ uF u → conv (oc≅ o₂) e₂ <ᵉ uF u → (g x e₁ ⊴ g y e₂) ⊎ (g y e₂ ⊴ g x e₁)
  cmpBr {u = u} dir o₁ o₂ e₁ e₂ l₁ l₂ with bd (conv (oc≅ o₁) e₁) (conv (oc≅ o₂) e₂) (uF u) l₁ l₂
  ... | inj₁ s = inj₁ (cmpBr₁ {u = u} dir o₁ o₂ e₁ e₂ s)
  ... | inj₂ s = inj₂ (cmpBr₁ {u = u} dir o₂ o₁ e₂ e₁ s)
```

## §7 地板与求界的接口

`Fᵉ F`: 字面上界 $F$ 之下的证据的树, **求界只看这个**. `Flr`: 折叠收集的地板, 项是帧. `Ev w φ`: 地板的每一项经 `≈` 搬到 $w$ 的纤维里, 在 $w$ 的上界之下. `toFᵉ`: 把 `Flr` 与证据读成 `Fᵉ`. `Tp`: 求界的结果. `Bd` 是新闭包的下界, `gr` 把它之上的证据读回 $c$ 之上. 对 `Bd` 之上的 $\eta$, `upF` 是一个字面的公共上界: 地板 (`upEv`) 与 $\eta$ (`up<`) 都在它之下. **这里没有比较两个任意元.**

```agda
  data Fᵉ {c X : D} (F : c ⊑ᴰ X) : Set where
    fzᵉ  : Fᵉ F
    fkᵉ  : ∀ {K} (e : c ⊑ᴰ K) → e <ᵉ F → Fᵉ F
    _⊔ᵉ_ : Fᵉ F → Fᵉ F → Fᵉ F

  Allᵉ : ∀ {c X} {F : c ⊑ᴰ X} {Y} → c ⊑ᴰ Y → Fᵉ F → Set
  Allᵉ G fzᵉ = ⊤
  Allᵉ G (fkᵉ e _) = e <ᵉ G
  Allᵉ G (a ⊔ᵉ b) = Allᵉ G a × Allᵉ G b

  record Tp {c X : D} (F : c ⊑ᴰ X) (ψ : Fᵉ F) : Set where
    constructor tpr
    field
      Bd   : D
      gr   : ∀ {η} → Bd ⊑ᴰ η → c ⊑ᴰ η
      upX  : ∀ {η} → Bd ⊑ᴰ η → D
      upF  : ∀ {η} (d : Bd ⊑ᴰ η) → c ⊑ᴰ upX d
      upEv : ∀ {η} (d : Bd ⊑ᴰ η) → Allᵉ (upF d) ψ
      up<  : ∀ {η} (d : Bd ⊑ᴰ η) → gr d <ᵉ upF d
  open Tp public

  infixl 5 _⊔_
  data Flr : Set where
    fz  : Flr
    fk  : Frm → Flr
    _⊔_ : Flr → Flr → Flr

  Ev : Up → Flr → Set
  Ev w fz = ⊤
  Ev w (fk f) = Σ (κ f ≈ key w) λ o → conv (oc≅ o) (fe f) <ᵉ uF w
  Ev w (a ⊔ b) = Ev w a × Ev w b

  toFᵉ : ∀ {w} φ → Ev w φ → Fᵉ (uF w)
  toFᵉ fz _ = fzᵉ
  toFᵉ {w} (fk f) (o , q) = fkᵉ (conv (oc≅ o) (fe f)) q
  toFᵉ (a ⊔ b) (x , y) = toFᵉ a x ⊔ᵉ toFᵉ b y

  -- 新的上界在 w 的纤维里: 读回到节点 c₂ 的纤维
  evBack : ∀ {u c₂ t₂ g₂ Y} (o₃ : lc c₂ t₂ g₂ ≈ key u) (G : uc u ⊑ᴰ Y) φ (ev : Ev u φ) → Allᵉ G (toFᵉ φ ev) →
           Ev (mkU c₂ t₂ g₂ Y (conv⁻ (oc≅ o₃) G)) φ
  evBack o₃ G fz _ _ = tt
  evBack {u} {c₂} {t₂} {g₂} o₃ G (fk f) (o , q) a =
    ≈-trans o (≈-sym o₃) ,
    subst (λ z → z <ᵉ conv⁻ (oc≅ o₃) G) (sym (eq o o₃)) (<-conv⁻ (oc≅ o₃) _ _ a)
    where
    eq : ∀ {c₃ t₃ g₃ c₄ t₄ g₄} (o : lc (fc f) (ft f) (fg f) ≈ lc c₃ t₃ g₃) (o₃ : lc c₄ t₄ g₄ ≈ lc c₃ t₃ g₃) →
         conv (oc≅ (≈-trans o (≈-sym o₃))) (fe f) ≡ conv⁻ (oc≅ o₃) (conv (oc≅ o) (fe f))
    eq (o≈ d _ _ _ _ _) (o≈ d₃ _ _ _ _ _) = refl
  evBack o₃ G (a ⊔ b) (x , y) (p , q) = evBack o₃ G a x p , evBack o₃ G b y q
```
