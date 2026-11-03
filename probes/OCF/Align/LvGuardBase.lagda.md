# 带守卫的层号 (底座): 分支受下界支配, 比较不看分支值

> 不含记号. 结论写在 [LvGuard](LvGuard.lagda.md).
>
> `lc c t g`: $t$ 是第一支, 分支 $g\,\eta\,e$ 只在 $e:c\sqsubseteq\eta$ 上有定义, 与 `ŝ` 同形. 分支的定义域不止 `Ordᴵ`: `Fam` 给出更高层的定义域, 下标类型由 `Tag` 区分. 比较有且只有一种: **第一路径** (不走 `bra`) 对任意路径 (`cmpF`). 两个 `bra` 从不相比, 所以这里没有世界, 没有表, 没有 `<ᴵ-dec`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvGuardBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; <ᴵ-dec; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; zero; suc; lim; z≅; s≅; l≅; z⊑; s⊑; l⊑;
   ≅ᴵ-refl; ≅ᴵ-sym; ≅ᴵ-trans; ⊑ᴵ-trans; ⊑ᴵ-refl)
open import OCF.Align.InaccFloorBase using (≺→⊑ᴵ; ≅→⊑ᴵ)
```

## §1 定义域

`Dom`: 分支的定义域, 只要等价, 守卫关系, "下一个", 与两条封闭性, 外加 `Ordᴵ` 的嵌入 (读回要它). `Dom₀` 是 `Ordᴵ`. 更高的定义域是**一个**集合: `Ordᴵ` 与上一层好层号的和 ([LvGuardNext](LvGuardNext.lagda.md)), 所以这里只有一个下标类型, 没有标签要判等.

```agda
record Dom : Set₁ where
  infix 4 _⊑ᴰ_ _≅ᴰ_
  field
    D       : Set
    _⊑ᴰ_    : D → D → Set
    _≅ᴰ_    : D → D → Set
    sD      : D → D
    ≅ᴰ-refl : ∀ x → x ≅ᴰ x
    ≅ᴰ-sym  : ∀ {x y} → x ≅ᴰ y → y ≅ᴰ x
    ≅ᴰ-trans : ∀ {x y z} → x ≅ᴰ y → y ≅ᴰ z → x ≅ᴰ z
    conv    : ∀ {c c′ x} → c ≅ᴰ c′ → c ⊑ᴰ x → c′ ⊑ᴰ x
    gs      : ∀ {c x y} → c ⊑ᴰ x → sD x ⊑ᴰ y → c ⊑ᴰ y
    -- 世界: 字面上界之下的比较 (只有表的路线用它, cmpF, cmpP 不用)
    _<ᴰ_    : D → D → Set
    bd      : ∀ {a b X} → a <ᴰ X → b <ᴰ X → (sD a ⊑ᴰ b) ⊎ (sD b ⊑ᴰ a) ⊎ (a ≅ᴰ b)
    -- Ordᴵ 的嵌入: 下界 1 之上的元读回 Ordᴵ
    b₁      : D
    rd      : ∀ {η} → b₁ ⊑ᴰ η → Ordᴵ
    rd-one  : ∀ {η} (e : b₁ ⊑ᴰ η) → suc zero ⊑ᴵ rd e
    rd-s    : ∀ {η η′} (e : b₁ ⊑ᴰ η) (e′ : b₁ ⊑ᴰ η′) → sD η ⊑ᴰ η′ → suc (rd e) ⊑ᴵ rd e′
    rd-≅    : ∀ {η η′} (e : b₁ ⊑ᴰ η) (e′ : b₁ ⊑ᴰ η′) → η ≅ᴰ η′ → rd e ≅ᴵ rd e′

≻ᴵ→⊑ : ∀ {a b : Ordᴵ} → suc a ⊑ᴵ b → a ⊑ᴵ b
≻ᴵ→⊑ (s⊑ e q) = ≺→⊑ᴵ (via e q)

bd₀ : ∀ {a b} → (a ≺ᴵ b) ⊎ (b ≺ᴵ a) ⊎ (a ≅ᴵ b) → (suc a ⊑ᴵ b) ⊎ (suc b ⊑ᴵ a) ⊎ (a ≅ᴵ b)
bd₀ (injᵃ (via e q)) = injᵃ (s⊑ e q)
bd₀ (injᵇ (via e q)) = injᵇ (s⊑ e q)
bd₀ (injᶜ d)         = injᶜ d

Dom₀ : Dom
Dom₀ = record
  { D = Ordᴵ ; _⊑ᴰ_ = _⊑ᴵ_ ; _≅ᴰ_ = _≅ᴵ_ ; sD = suc
  ; ≅ᴰ-refl = ≅ᴵ-refl ; ≅ᴰ-sym = ≅ᴵ-sym ; ≅ᴰ-trans = ≅ᴵ-trans
  ; conv = λ d e → ⊑ᴵ-trans (≅→⊑ᴵ (≅ᴵ-sym d)) e
  ; gs = λ e e′ → ⊑ᴵ-trans e (≻ᴵ→⊑ e′)
  ; _<ᴰ_ = _<ᴵ_
  ; bd = λ p q → bd₀ (<ᴵ-dec p q)
  ; b₁ = suc zero
  ; rd = λ {η} _ → η
  ; rd-one = λ e → e
  ; rd-s = λ e e′ d → d
  ; rd-≅ = λ e e′ d → d
  }

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

部分等价. 闭包要界 $\cong$, 第一支 $\approx$, 分支在 $\cong$ 的下标上 $\approx$.

```agda
  infix 4 _≈_
  data _≈_ : LG → LG → Set where
    z≈ : zero ≈ zero
    s≈ : ∀ {a b} → a ≈ b → suc a ≈ suc b
    l≈ : ∀ {f g} → (∀ n → f n ≈ g n) → lim f ≈ lim g
    o≈ : ∀ {c c′ t t′ g g′} → c ≅ᴰ c′ → t ≈ t′ →
         (∀ (η : D) (e : c ⊑ᴰ η) (η′ : D) (e′ : c′ ⊑ᴰ η′) → η ≅ᴰ η′ → g η e ≈ g′ η′ e′) → lc c t g ≈ lc c′ t′ g′

  ≈-sym : ∀ {a b} → a ≈ b → b ≈ a
  ≈-sym z≈ = z≈
  ≈-sym (s≈ e) = s≈ (≈-sym e)
  ≈-sym (l≈ h) = l≈ (λ n → ≈-sym (h n))
  ≈-sym (o≈ d e h) = o≈ (≅ᴰ-sym d) (≈-sym e) (λ η e′ η′ e″ k → ≈-sym (h η′ e″ η e′ (≅ᴰ-sym k)))

  ≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
  ≈-trans z≈ z≈ = z≈
  ≈-trans (s≈ e) (s≈ e′) = s≈ (≈-trans e e′)
  ≈-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈-trans (h n) (h′ n))
  ≈-trans (o≈ d e h) (o≈ d′ e′ h′) =
    o≈ (≅ᴰ-trans d d′) (≈-trans e e′)
       (λ η e₁ η″ e₃ k → ≈-trans (h η e₁ η″ (conv (≅ᴰ-sym d′) e₃) k) (h′ η″ (conv (≅ᴰ-sym d′) e₃) η″ e₃ (≅ᴰ-refl η″)))

  ≈-reflˡ : ∀ {a b} → a ≈ b → a ≈ a
  ≈-reflˡ e = ≈-trans e (≈-sym e)

  ≈-reflʳ : ∀ {a b} → a ≈ b → b ≈ b
  ≈-reflʳ e = ≈-trans (≈-sym e) e
```

## §4 表与可容许性

表 `Ents`: 按节点 (模 `≈`) 给界, 只有带表的路线用它 (`at` 与 [LvKeyBase](LvKeyBase.lagda.md) 同形: 关系, 写下它不判定任何东西).

```agda
  infixl 5 _▸_,_
  data Ents : Set where
    ∅      : D → Ents
    _▸_,_  : Ents → LG → D → Ents

  at : Ents → LG → D → Set
  at (∅ d)       y ℓ = ℓ ≡ d
  at (E ▸ κ , X) y ℓ = ((y ≈ κ) × (ℓ ≡ X)) ⊎ (((y ≈ κ) → ⊥) × at E y ℓ)

  at-resp : ∀ {E y y′ ℓ} → y ≈ y′ → at E y ℓ → at E y′ ℓ
  at-resp {∅ d} e a = a
  at-resp {E ▸ κ , X} e (inj₁ (d , r)) = inj₁ (≈-trans (≈-sym e) d , r)
  at-resp {E ▸ κ , X} e (inj₂ (n , a)) = inj₂ ((λ d → n (≈-trans e d)) , at-resp {E} e a)

  at-uq : ∀ {E y y′ ℓ ℓ′} → y ≈ y′ → at E y ℓ → at E y′ ℓ′ → ℓ ≡ ℓ′
  at-uq {∅ d} e refl refl = refl
  at-uq {E ▸ κ , X} e (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
  at-uq {E ▸ κ , X} e (inj₁ (d , _)) (inj₂ (n , _)) = ⊥-elim (n (≈-trans (≈-sym e) d))
  at-uq {E ▸ κ , X} e (inj₂ (n , _)) (inj₁ (d , _)) = ⊥-elim (n (≈-trans e d))
  at-uq {E ▸ κ , X} e (inj₂ (_ , a)) (inj₂ (_ , b)) = at-uq {E} e a b

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

  CovB : Fl → LG → D → Set
  CovB π y η = Σ D λ c₁ → Σ LG λ t₁ → Σ ((x : D) → c₁ ⊑ᴰ x → LG) λ g₁ → Σ (c₁ ⊑ᴰ η) λ e₁ → Mem π (frm c₁ t₁ g₁ η e₁) × (y ≈ lc c₁ t₁ g₁ ⊎ (y ≡ lc c₁ t₁ g₁))

  Bel′ : Ents → LG → D → Set
  Bel′ E y η = Σ D λ ℓ → at E y ℓ × (η <ᴰ ℓ)

  Bel : Src → LG → D → Set
  Bel (tab E) y η = Bel′ E y η
  Bel (cov π) y η = CovB π y η

  Bel-resp : ∀ {E y y′ η} → y ≈ y′ → Bel E y η → Bel E y′ η
  Bel-resp {tab E} e (ℓ , a , q) = ℓ , at-resp {E} e a , q
  Bel-resp {cov π} e (c₁ , t₁ , g₁ , e₁ , m , inj₁ d) = c₁ , t₁ , g₁ , e₁ , m , inj₁ (≈-trans (≈-sym e) d)
  Bel-resp {cov π} e (c₁ , t₁ , g₁ , e₁ , m , inj₂ refl) = c₁ , t₁ , g₁ , e₁ , m , inj₁ (≈-sym e)

  Adm : Src → ∀ {a c} → a < c → Set
  Adm E zero      = ⊤
  Adm E (suc r)   = Adm E r
  Adm E (lim n r) = Adm E r
  Adm E (fst r)   = Adm E r
  Adm E (bra {c = c} {t = t} {g = g} η e r) = Bel E (lc c t g) η × Adm E r

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
  AdmC E (bra {c = c} {t = t} {g = g} η e r) = Bel E (lc c t g) η × AdmC E r
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
  ≈-move (o≈ d e h) (fst r) with ≈-move e r
  ... | viaᴸ d′ p t = viaᴸ d′ (fst p) t
  ≈-move (o≈ d e h) (bra η e₁ r) with ≈-move (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) r
  ... | viaᴸ d′ p t = viaᴸ d′ (bra η (conv d e₁) p) (λ E u → Bel-resp {E} (o≈ d e h) (proj₁ u) , t E (proj₂ u))

  ≈-moveᶠ : ∀ {a b} → a ≈ b → a ⊑ᶠ b
  ≈-moveᶠ (s≈ e) zero = preᶠ e zero
  ≈-moveᶠ (s≈ e) (suc r) with ≈-moveᶠ e r
  ... | preᶠ d p = preᶠ d (suc p)
  ≈-moveᶠ (l≈ h) (lim n r) with ≈-moveᶠ (h n) r
  ... | preᶠ d p = preᶠ d (lim n p)
  ≈-moveᶠ (o≈ d e h) (fst r) with ≈-moveᶠ e r
  ... | preᶠ d′ p = preᶠ d′ (fst p)

  ≈-moveᵏ : ∀ {a b} → a ≈ b → a ⊑ᵏ b
  ≈-moveᵏ (o≈ d e h) self = viaᵏ (o≈ d e h) self
  ≈-moveᵏ (s≈ e) (suc r) with ≈-moveᵏ e r
  ... | viaᵏ d p = viaᵏ d (suc p)
  ≈-moveᵏ (l≈ h) (lim n r) with ≈-moveᵏ (h n) r
  ... | viaᵏ d p = viaᵏ d (lim n p)
  ≈-moveᵏ (o≈ d e h) (fst r) with ≈-moveᵏ e r
  ... | viaᵏ d′ p = viaᵏ d′ (fst p)

  ≈-moveᴷ : ∀ {a b} → a ≈ b → a ⊑ᴷ b
  ≈-moveᴷ (o≈ d e h) self = viaᴷ (o≈ d e h) self (λ _ _ → tt)
  ≈-moveᴷ (s≈ e) (suc r) with ≈-moveᴷ e r
  ... | viaᴷ d p t = viaᴷ d (suc p) t
  ≈-moveᴷ (l≈ h) (lim n r) with ≈-moveᴷ (h n) r
  ... | viaᴷ d p t = viaᴷ d (lim n p) t
  ≈-moveᴷ (o≈ d e h) (fst r) with ≈-moveᴷ e r
  ... | viaᴷ d′ p t = viaᴷ d′ (fst p) t
  ≈-moveᴷ (o≈ d e h) (bra η e₁ r) with ≈-moveᴷ (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) r
  ... | viaᴷ d′ p t = viaᴷ d′ (bra η (conv d e₁) p) (λ E u → Bel-resp {E} (o≈ d e h) (proj₁ u) , t E (proj₂ u))

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

`WF`: 极限相邻步进, 闭包的第一支在每个分支之下, 分支沿**严格**的守卫上升. 没有 "$\eta\preceq\eta'$" 的非严格形式, 因为没有任何地方比较两个分支. 上升只要求路径搬运 (`⊑ⁿ`), 不带转移, 也不保持第一路径: $x\mapsto x$ 作分支 ($\Omega_2$) 的上升是假的 `⊴` (`no-↑` 的形状), 真的 `⊑ⁿ`. `cmpF`, `cmpP` 只读第一支与极限的 `⊴`, 从不读上升. `WFˢ`: 上升也是 `⊴`, 表的路线 ([LvGuardTab](LvGuardTab.lagda.md)) 要它, 读回给的就是它.

```agda
  infix 4 _⊑ⁿ_
  record Below (a b : LG) : Set where
    constructor pre
    field
      {repᵇ} : LG
      eqvᵇ   : a ≈ repᵇ
      pthᵇ   : repᵇ < b
  open Below public

  _⊑ⁿ_ : LG → LG → Set
  a ⊑ⁿ b = ∀ {k} → k < a → Below k b

  ⊴→⊑ⁿ : ∀ {a b} → a ⊴ b → a ⊑ⁿ b
  ⊴→⊑ⁿ x r with ⊴p x r
  ... | viaᴸ d p _ = pre d p

  ≈→⊑ⁿ : ∀ {a b} → a ≈ b → a ⊑ⁿ b
  ≈→⊑ⁿ e r with ≈-move e r
  ... | viaᴸ d p _ = pre d p

  infixr 9 _∘<_
  _∘<_ : ∀ {k a b} → k < a → a < b → k < b
  r ∘< zero      = suc r
  r ∘< suc s     = suc (r ∘< s)
  r ∘< lim n s   = lim n (r ∘< s)
  r ∘< fst s     = fst (r ∘< s)
  r ∘< bra η e s = bra η e (r ∘< s)

  ⊑ⁿ-trans : ∀ {a b c} → a ⊑ⁿ b → b ⊑ⁿ c → a ⊑ⁿ c
  ⊑ⁿ-trans x y r with x r
  ... | pre d p with y p
  ...   | pre d′ p′ = pre (≈-trans d d′) p′

  -- 弱的搬运: 没有转移, 没有带分支的位置
  infix 4 _⊴ʷ_
  record _⊴ʷ_ (a b : LG) : Set where
    constructor ⊴w
    field
      ⊴ʷp : a ⊑ⁿ b
      ⊴ʷf : a ⊑ᶠ b
      ⊴ʷk : a ⊑ᵏ b
  open _⊴ʷ_ public

  ⊴→⊴ʷ : ∀ {a b} → a ⊴ b → a ⊴ʷ b
  ⊴→⊴ʷ x = ⊴w (⊴→⊑ⁿ x) (⊴f x) (⊴k x)

  ⊴ʷ-trans : ∀ {a b c} → a ⊴ʷ b → b ⊴ʷ c → a ⊴ʷ c
  ⊴ʷ-trans {a} {b} {c} x y = ⊴w (⊑ⁿ-trans (⊴ʷp x) (⊴ʷp y)) ff kk
    where
    ff : a ⊑ᶠ c
    ff r with ⊴ʷf x r
    ... | preᶠ d p with ⊴ʷf y p
    ...   | preᶠ d′ p′ = preᶠ (≈-trans d d′) p′
    kk : a ⊑ᵏ c
    kk r with ⊴ʷk x r
    ... | viaᵏ d p with ⊴ʷk y p
    ...   | viaᵏ d′ p′ = viaᵏ (≈-trans d d′) p′

  ⊴ʷ-zero : ∀ {b} → zero ⊴ʷ b
  ⊴ʷ-zero = ⊴w (λ ()) (λ ()) (λ ())

  ≈→⊴ʷ : ∀ {a b} → a ≈ b → a ⊴ʷ b
  ≈→⊴ʷ e = ⊴w (≈→⊑ⁿ e) (≈-moveᶠ e) (≈-moveᵏ e)

  WF : LG → Set
  WF zero       = ⊤
  WF (suc k)    = WF k
  WF (lim f)    = (∀ n → f n ⊴ʷ f (suc n)) × (∀ n → WF (f n))
  WF (lc c t g) = (∀ η e → t ⊴ʷ g η e) × (∀ η e η′ e′ → sD η ⊑ᴰ η′ → g η e ⊑ⁿ g η′ e′) × WF t × (∀ η e → WF (g η e))

  WFˢ : LG → Set
  WFˢ zero       = ⊤
  WFˢ (suc k)    = WFˢ k
  WFˢ (lim f)    = (∀ n → f n ⊴ f (suc n)) × (∀ n → WFˢ (f n))
  WFˢ (lc c t g) = (∀ η e → t ⊴ g η e) × (∀ η e η′ e′ → sD η ⊑ᴰ η′ → g η e ⊴ g η′ e′) × WFˢ t × (∀ η e → WFˢ (g η e))

  WFˢ→WF : ∀ c → WFˢ c → WF c
  WFˢ→WF zero w = tt
  WFˢ→WF (suc k) w = WFˢ→WF k w
  WFˢ→WF (lim f) (st , w) = (λ n → ⊴→⊴ʷ (st n)) , (λ n → WFˢ→WF (f n) (w n))
  WFˢ→WF (lc c t g) (tg , dir , wt , wg) = (λ η e → ⊴→⊴ʷ (tg η e)) , (λ η e η′ e′ d → ⊴→⊑ⁿ (dir η e η′ e′ d)) , WFˢ→WF t wt , (λ η e → WFˢ→WF (g η e) (wg η e))

  -- 好层号
  Cf Cfˢ : LG → Set
  Cf c = WF c × (c ≈ c)
  Cfˢ c = WFˢ c × (c ≈ c)

  steps : ∀ {f : ℕ → LG} → (∀ n → f n ⊴ʷ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊴ʷ f m
  steps s zero    = s _
  steps s (suc q) = ⊴ʷ-trans (steps s q) (s _)

  stepsˢ : ∀ {f : ℕ → LG} → (∀ n → f n ⊴ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊴ f m
  stepsˢ s zero    = s _
  stepsˢ s (suc q) = ⊴-trans (stepsˢ s q) (s _)

  selfAt : ∀ {a c} → c ≈ c → a < c → a ≈ a
  selfAt (s≈ e) zero = e
  selfAt (s≈ e) (suc r) = selfAt e r
  selfAt (l≈ h) (lim n r) = selfAt (h n) r
  selfAt (o≈ d e h) (fst r) = selfAt e r
  selfAt (o≈ d e h) (bra η e₁ r) = selfAt (h η e₁ η e₁ (≅ᴰ-refl η)) r
```

## §6 比较: 第一路径对任意路径

**定理 `cmpF`.** 对 `Cf c`, 第一路径 $p$ 与任意路径 $q$ 三歧. 对 $c$ 结构递归. 极限处比较 $\mathbb N$ 并搬运; 闭包处第一路径只会是 `fst`, 对方是 `fst` 就递归, 对方是 `bra` 就把第一支搬进那个分支. **任何分支值都不被比较, `<ᴵ-dec` 不出现, 所以这条定理没有世界.** 对照壁垒: `noBT` 的 `zigzag` 比的是两个 `bra`, 这里不存在这种情形.

```agda
  data CmpF (a b : LG) : Set where
    flt : a ≺ᶠ b → CmpF a b
    fgt : Below b a → CmpF a b
    feq : a ≈ b → CmpF a b

  shL : ∀ {a a′ b} → a ≈ a′ → CmpF a′ b → CmpF a b
  shL e (flt (preᶠ d s)) = flt (preᶠ (≈-trans e d) s)
  shL e (fgt (pre d s)) with ≈-move (≈-sym e) s
  ... | viaᴸ d′ s′ _ = fgt (pre (≈-trans d d′) s′)
  shL e (feq d) = feq (≈-trans e d)

  shR : ∀ {a b b′} → b ≈ b′ → CmpF a b′ → CmpF a b
  shR e (fgt (pre d s)) = fgt (pre (≈-trans e d) s)
  shR e (flt (preᶠ d s)) with ≈-moveᶠ (≈-sym e) s
  ... | preᶠ d′ s′ = flt (preᶠ (≈-trans d d′) s′)
  shR e (feq d) = feq (≈-trans d (≈-sym e))

  cmpF : ∀ {c} → WF c → c ≈ c → ∀ {a b} → a ≪ c → b < c → CmpF a b
  cmpF w (s≈ e) zero zero = feq e
  cmpF w (s≈ e) zero (suc q) with ≈-move e q
  ... | viaᴸ d s _ = fgt (pre d s)
  cmpF w (s≈ e) (suc p) zero with ≈-moveᶠ e p
  ... | preᶠ d s = flt (preᶠ d s)
  cmpF w (s≈ e) (suc p) (suc q) = cmpF w e p q
  cmpF (st , w) (l≈ e) (lim n p) (lim m q) with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴ʷf (steps st n<m) p
  ...   | preᶠ d p′ = shL d (cmpF (w m) (e m) p′ q)
  cmpF (st , w) (l≈ e) (lim n p) (lim m q) | injᵇ m<n with ⊴ʷp (steps st m<n) q
  ...   | pre d q′ = shR d (cmpF (w n) (e n) p q′)
  cmpF (st , w) (l≈ e) (lim n p) (lim _ q) | injᶜ refl = cmpF (w n) (e n) p q
  cmpF (tg , dir , wt , wg) (o≈ d e h) (fst p) (fst q) = cmpF wt e p q
  cmpF (tg , dir , wt , wg) (o≈ d e h) (fst p) (bra η e₁ q) with ⊴ʷf (tg η e₁) p
  ... | preᶠ d′ p′ = shL d′ (cmpF (wg η e₁) (h η e₁ η e₁ (≅ᴰ-refl η)) p′ q)
```

**定理 `cmpP`.** 闭包的第一位置 $Q$ 与路径 $q$: 目标要么在闭包之下, 要么闭包在目标里仍是第一位置. 同一个骨架.

```agda
  data CmpP (c : D) (t : LG) (g : (η : D) → c ⊑ᴰ η → LG) (b : LG) : Set where
    pbelow : Below b (lc c t g) → CmpP c t g b
    pabove : Kvᶠ c t g b → CmpP c t g b

  shK : ∀ {c t g c′ t′ g′ b} → lc c t g ≈ lc c′ t′ g′ → CmpP c′ t′ g′ b → CmpP c t g b
  shK e (pbelow (pre d s)) with ≈-move (≈-sym e) s
  ... | viaᴸ d′ s′ _ = pbelow (pre (≈-trans d d′) s′)
  shK e (pabove (viaᵏ d p)) = pabove (viaᵏ (≈-trans e d) p)

  shB : ∀ {c t g b b′} → b ≈ b′ → CmpP c t g b′ → CmpP c t g b
  shB e (pbelow (pre d s)) = pbelow (pre (≈-trans e d) s)
  shB e (pabove (viaᵏ d p)) with ≈-moveᵏ (≈-sym e) p
  ... | viaᵏ d′ p′ = pabove (viaᵏ (≈-trans d d′) p′)

  cmpP : ∀ {y} → WF y → y ≈ y → ∀ {c t g b} → Cpᶠ (lc c t g) y → b < y → CmpP c t g b
  cmpP w sf self q = pbelow (pre (selfAt sf q) q)
  cmpP w (s≈ e) (suc Q) zero with ≈-moveᵏ e Q
  ... | viaᵏ d p = pabove (viaᵏ d p)
  cmpP w (s≈ e) (suc Q) (suc q) = cmpP w e Q q
  cmpP (st , w) (l≈ e) (lim n Q) (lim m q) with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴ʷk (steps st n<m) Q
  ...   | viaᵏ d Q′ = shK d (cmpP (w m) (e m) Q′ q)
  cmpP (st , w) (l≈ e) (lim n Q) (lim m q) | injᵇ m<n with ⊴ʷp (steps st m<n) q
  ...   | pre d q′ = shB d (cmpP (w n) (e n) Q q′)
  cmpP (st , w) (l≈ e) (lim n Q) (lim _ q) | injᶜ refl = cmpP (w n) (e n) Q q
  cmpP (tg , dir , wt , wg) (o≈ d e h) (fst Q) (fst q) = cmpP wt e Q q
  cmpP (tg , dir , wt , wg) (o≈ d e h) (fst Q) (bra η e₁ q) with ⊴ʷk (tg η e₁) Q
  ... | viaᵏ d′ Q′ = shK d′ (cmpP (wg η e₁) (h η e₁ η e₁ (≅ᴰ-refl η)) Q′ q)
```
