# 下一层: 分支是上一层的好层号, 带守卫 (任务 1)

> 不含记号. 结论写在 [LvGuard](LvGuard.lagda.md). `NextDom 𝔻`: 定义域是 $D\uplus$ `GLv 𝔻`, 守卫是上一层的路径搬运 $\sqsubseteq^n$, 不跨两边. `Ω⁺`: 下一个基数, $\sup_x x$, 对任何 `Dom`. 所以 $\Omega_2,\Omega_3,\dots$ 是同一个定义的实例 (`𝔻ₙ`, `Ωₙ`, `Cf-Ωₙ`), 没有标签, 没有表, 没有世界. 上升就是 `gs` 的路径复合.
>
> **这一层没有 `WFˢ`:** $x\mapsto x$ 的上升不保持第一路径, 不带转移 (`no-↑` 的形状). 所以第二档的层号走不了表的路线, 只有 `cmpF`, `cmpP`.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvGuardNext where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level using (Ordᴵ; _≅ᴵ_; _⊑ᴵ_)
open import OCF.Align.LvGuardBase
```

## §1 定义域

```agda
module Up (𝔻 : Dom) where
  open Dom 𝔻 renaming (D to D₀; _⊑ᴰ_ to _⊑₀_; _≅ᴰ_ to _≅₀_; sD to s₀; ≅ᴰ-refl to refl₀; ≅ᴰ-sym to sym₀; ≅ᴰ-trans to trans₀;
                       conv to conv₀; gs to gs₀; _<ᴰ_ to _<₀_; bd to bd₀′; b₁ to b₀; rd to rd₀; rd-one to rd-one₀; rd-s to rd-s₀; rd-≅ to rd-≅₀)
  module L₀ = Lv 𝔻
  open L₀ using (LG; WF; Cf; _≈_; _⊑ⁿ_; pre; zero; suc)

  GLv : Set
  GLv = Σ LG Cf

  D′ : Set
  D′ = D₀ ⊎ GLv

  _⊑′_ _≅′_ _<′_ : D′ → D′ → Set
  inj₁ a ⊑′ inj₁ b = a ⊑₀ b
  inj₂ x ⊑′ inj₂ y = proj₁ x ⊑ⁿ proj₁ y
  inj₁ _ ⊑′ inj₂ _ = ⊥
  inj₂ _ ⊑′ inj₁ _ = ⊥
  inj₁ a ≅′ inj₁ b = a ≅₀ b
  inj₂ x ≅′ inj₂ y = proj₁ x ≈ proj₁ y
  inj₁ _ ≅′ inj₂ _ = ⊥
  inj₂ _ ≅′ inj₁ _ = ⊥
  inj₁ a <′ inj₁ b = a <₀ b
  inj₂ _ <′ _ = ⊥
  inj₁ _ <′ inj₂ _ = ⊥

  s′ : D′ → D′
  s′ (inj₁ a) = inj₁ (s₀ a)
  s′ (inj₂ (x , w , e)) = inj₂ (suc x , w , L₀.s≈ e)

  gs′ : ∀ {c x y} → c ⊑′ x → s′ x ⊑′ y → c ⊑′ y
  gs′ {inj₁ _} {inj₁ _} {inj₁ _} e e′ = gs₀ e e′
  gs′ {inj₂ _} {inj₂ (x , _)} {inj₂ _} e e′ with e′ L₀.zero
  ... | pre d p = λ r → step (e r)
    where
    step : ∀ {k} → L₀.Below k x → L₀.Below k _
    step (pre d₁ p₁) with L₀.≈→⊑ⁿ d p₁
    ... | pre d₂ p₂ = pre (L₀.≈-trans d₁ d₂) (p₂ L₀.∘< p)
  gs′ {inj₁ _} {inj₂ _} ()
  gs′ {inj₂ _} {inj₁ _} ()
  gs′ {inj₁ _} {inj₁ _} {inj₂ _} e ()
  gs′ {inj₂ _} {inj₂ (_ , _)} {inj₁ _} e ()

  conv′ : ∀ {c c′ x} → c ≅′ c′ → c ⊑′ x → c′ ⊑′ x
  conv′ {inj₁ _} {inj₁ _} {inj₁ _} d e = conv₀ d e
  conv′ {inj₂ _} {inj₂ _} {inj₂ _} d e = L₀.⊑ⁿ-trans (L₀.≈→⊑ⁿ (L₀.≈-sym d)) e
  conv′ {inj₁ _} {inj₂ _} ()
  conv′ {inj₂ _} {inj₁ _} ()
  conv′ {inj₁ _} {inj₁ _} {inj₂ _} d ()
  conv′ {inj₂ _} {inj₂ _} {inj₁ _} d ()

  bd′ : ∀ {a b X} → a <′ X → b <′ X → (s′ a ⊑′ b) ⊎ (s′ b ⊑′ a) ⊎ (a ≅′ b)
  bd′ {inj₁ _} {inj₁ _} {inj₁ _} p q = bd₀′ p q
  bd′ {inj₁ _} {inj₂ _} {inj₁ _} p ()
  bd′ {inj₂ _} ()
  bd′ {inj₁ _} {inj₁ _} {inj₂ _} ()
  bd′ {inj₁ _} {inj₂ _} {inj₂ _} ()

  rd′ : ∀ {η} → inj₁ b₀ ⊑′ η → Ordᴵ
  rd′ {inj₁ _} e = rd₀ e

  NextDom : Dom
  NextDom = record
    { D = D′ ; _⊑ᴰ_ = _⊑′_ ; _≅ᴰ_ = _≅′_ ; sD = s′
    ; ≅ᴰ-refl = λ { (inj₁ a) → refl₀ a ; (inj₂ x) → proj₂ (proj₂ x) }
    ; ≅ᴰ-sym = λ { {inj₁ _} {inj₁ _} d → sym₀ d ; {inj₂ _} {inj₂ _} d → L₀.≈-sym d }
    ; ≅ᴰ-trans = λ { {inj₁ _} {inj₁ _} {inj₁ _} d d′ → trans₀ d d′ ; {inj₂ _} {inj₂ _} {inj₂ _} d d′ → L₀.≈-trans d d′ }
    ; conv = λ {c} {c′} {x} → conv′ {c} {c′} {x} ; gs = λ {c} {x} {y} → gs′ {c} {x} {y}
    ; _<ᴰ_ = _<′_ ; bd = λ {a} {b} {X} → bd′ {a} {b} {X}
    ; b₁ = inj₁ b₀ ; rd = λ {η} e → rd′ {η} e
    ; rd-one = λ { {inj₁ _} e → rd-one₀ e }
    ; rd-s = λ { {inj₁ a} {inj₁ b} e e′ d → rd-s₀ {a} {b} e e′ d }
    ; rd-≅ = λ { {inj₁ a} {inj₁ b} e e′ d → rd-≅₀ {a} {b} e e′ d }
    }
```

## §2 上一层嵌入

`emb`: 结构递归. 路径两边都拉得回 (`pull`, `pullᶠ`, `pullᵏ`), 所以 `⊴ʷ` 与 `WF` 保持.

```agda
  module L₁ = Lv NextDom
  open L₁ using () renaming (LG to LG′)

  emb : LG → LG′
  emb L₀.zero = L₁.zero
  emb (L₀.suc a) = L₁.suc (emb a)
  emb (L₀.lim f) = L₁.lim (λ n → emb (f n))
  emb (L₀.lc c t g) = L₁.lc (inj₁ c) (emb t) (λ { (inj₁ η) e → emb (g η e) ; (inj₂ _) () })

  emb≈ : ∀ {a b} → a ≈ b → emb a L₁.≈ emb b
  emb≈ L₀.z≈ = L₁.z≈
  emb≈ (L₀.s≈ e) = L₁.s≈ (emb≈ e)
  emb≈ (L₀.l≈ h) = L₁.l≈ (λ n → emb≈ (h n))
  emb≈ (L₀.o≈ d e h) = L₁.o≈ d (emb≈ e) λ { (inj₁ η) e₁ (inj₁ η′) e₂ k → emb≈ (h η e₁ η′ e₂ k) }

  emb< : ∀ {a b} → a L₀.< b → emb a L₁.< emb b
  emb< L₀.zero = L₁.zero
  emb< (L₀.suc r) = L₁.suc (emb< r)
  emb< (L₀.lim n r) = L₁.lim n (emb< r)
  emb< (L₀.fst r) = L₁.fst (emb< r)
  emb< (L₀.bra η e r) = L₁.bra (inj₁ η) e (emb< r)

  emb≪ : ∀ {a b} → a L₀.≪ b → emb a L₁.≪ emb b
  emb≪ L₀.zero = L₁.zero
  emb≪ (L₀.suc r) = L₁.suc (emb≪ r)
  emb≪ (L₀.lim n r) = L₁.lim n (emb≪ r)
  emb≪ (L₀.fst r) = L₁.fst (emb≪ r)

  pull : ∀ b {k} → k L₁.< emb b → Σ LG λ k₀ → (k ≡ emb k₀) × (k₀ L₀.< b)
  pull (L₀.suc a) L₁.zero = a , refl , L₀.zero
  pull (L₀.suc a) (L₁.suc r) with pull a r
  ... | k₀ , e , q = k₀ , e , L₀.suc q
  pull (L₀.lim f) (L₁.lim n r) with pull (f n) r
  ... | k₀ , e , q = k₀ , e , L₀.lim n q
  pull (L₀.lc c t g) (L₁.fst r) with pull t r
  ... | k₀ , e , q = k₀ , e , L₀.fst q
  pull (L₀.lc c t g) (L₁.bra (inj₁ η) e′ r) with pull (g η e′) r
  ... | k₀ , e , q = k₀ , e , L₀.bra η e′ q

  pullᶠ : ∀ b {k} → k L₁.≪ emb b → Σ LG λ k₀ → (k ≡ emb k₀) × (k₀ L₀.≪ b)
  pullᶠ (L₀.suc a) L₁.zero = a , refl , L₀.zero
  pullᶠ (L₀.suc a) (L₁.suc r) with pullᶠ a r
  ... | k₀ , e , q = k₀ , e , L₀.suc q
  pullᶠ (L₀.lim f) (L₁.lim n r) with pullᶠ (f n) r
  ... | k₀ , e , q = k₀ , e , L₀.lim n q
  pullᶠ (L₀.lc c t g) (L₁.fst r) with pullᶠ t r
  ... | k₀ , e , q = k₀ , e , L₀.fst q

  emb-p : ∀ {a b} → a ⊑ⁿ b → emb a L₁.⊑ⁿ emb b
  emb-p {a} h r with pull a r
  ... | k₀ , refl , q with h q
  ... | pre d p = L₁.pre (emb≈ d) (emb< p)

  emb-f : ∀ {a b} → a L₀.⊑ᶠ b → emb a L₁.⊑ᶠ emb b
  emb-f {a} h r with pullᶠ a r
  ... | k₀ , refl , q with h q
  ... | L₀.preᶠ d p = L₁.preᶠ (emb≈ d) (emb≪ p)
```

**位置.** 拉回一个闭包的第一位置: 这个闭包字面上是 `emb` 的像.

```agda
  embCp : ∀ {a b} → L₀.Cpᶠ a b → L₁.Cpᶠ (emb a) (emb b)
  embCp L₀.self = L₁.self
  embCp (L₀.suc p) = L₁.suc (embCp p)
  embCp (L₀.lim n p) = L₁.lim n (embCp p)
  embCp (L₀.fst p) = L₁.fst (embCp p)

  record PullK (a : LG) (c′ : D′) (t′ : LG′) (g′ : (η : D′) → c′ ⊑′ η → LG′) : Set where
    constructor pk
    field
      {c₀} : D₀
      {t₀} : LG
      {g₀} : (η : D₀) → c₀ ⊑₀ η → LG
      eqk  : L₁.lc c′ t′ g′ L₁.≈ emb (L₀.lc c₀ t₀ g₀)
      posk : L₀.Cpᶠ (L₀.lc c₀ t₀ g₀) a

  pullᵏ : ∀ a {c t g} → L₁.Cpᶠ (L₁.lc c t g) (emb a) → L₁.lc c t g L₁.≈ L₁.lc c t g → PullK a c t g
  pullᵏ (L₀.suc a) (L₁.suc p) sf with pullᵏ a p sf
  ... | pk e q = pk e (L₀.suc q)
  pullᵏ (L₀.lim f) (L₁.lim n p) sf with pullᵏ (f n) p sf
  ... | pk e q = pk e (L₀.lim n q)
  pullᵏ (L₀.lc c t g) L₁.self sf = pk sf L₀.self
  pullᵏ (L₀.lc c t g) (L₁.fst p) sf with pullᵏ t p sf
  ... | pk e q = pk e (L₀.fst q)
```

`⊑ᵏ` 对 `emb` 的搬运要节点自反, 由源层号的自反得到 (`selfCp`).

```agda
  selfCp : ∀ {a b} → b L₁.≈ b → L₁.Cpᶠ a b → a L₁.≈ a
  selfCp e L₁.self = e
  selfCp (L₁.s≈ e) (L₁.suc p) = selfCp e p
  selfCp (L₁.l≈ h) (L₁.lim n p) = selfCp (h n) p
  selfCp (L₁.o≈ d e h) (L₁.fst p) = selfCp e p

  emb-k : ∀ {a b} → emb a L₁.≈ emb a → a L₀.⊑ᵏ b → emb a L₁.⊑ᵏ emb b
  emb-k {a} sf h Q with pullᵏ a Q (selfCp sf Q)
  ... | pk e q with h q
  ... | L₀.viaᵏ d p = L₁.viaᵏ (L₁.≈-trans e (emb≈ d)) (embCp p)

  emb-w : ∀ {a b} → a ≈ a → a L₀.⊴ʷ b → emb a L₁.⊴ʷ emb b
  emb-w sf x = L₁.⊴w (emb-p (L₀.⊴ʷp x)) (emb-f (L₀.⊴ʷf x)) (emb-k (emb≈ sf) (L₀.⊴ʷk x))

  WF-emb : ∀ a → WF a → a ≈ a → L₁.WF (emb a)
  WF-emb L₀.zero w sf = tt
  WF-emb (L₀.suc a) w (L₀.s≈ sf) = WF-emb a w sf
  WF-emb (L₀.lim f) (st , w) (L₀.l≈ sf) = (λ n → emb-w (sf n) (st n)) , (λ n → WF-emb (f n) (w n) (sf n))
  WF-emb (L₀.lc c t g) (tg , dir , wt , wg) (L₀.o≈ d se sh) =
    (λ { (inj₁ η) e → emb-w se (tg η e) }) ,
    (λ { (inj₁ η) e (inj₁ η′) e′ d′ → emb-p (dir η e η′ e′ d′) }) ,
    WF-emb t wt se ,
    (λ { (inj₁ η) e → WF-emb (g η e) (wg η e) (sh η e η e (refl₀ η)) })

  Cf-emb : ∀ a → Cf a → L₁.Cf (emb a)
  Cf-emb a (w , sf) = WF-emb a w sf , emb≈ sf
```

## §3 下一个基数

`Ω⁺`: $\sup_{x}x$, $x$ 取好层号, 对任何 `Dom`. 第一支是 0, 守卫的下界是 0 (`zero` 搬进任何层号). 这里的上升就是路径复合 (`s⊑ⁿ→⊑ⁿ`), 没有比较.

```agda
  zeroᵍ : GLv
  zeroᵍ = L₀.zero , tt , L₀.z≈

  s⊑ⁿ→⊑ⁿ : ∀ {x y} → L₀.suc x ⊑ⁿ y → x ⊑ⁿ y
  s⊑ⁿ→⊑ⁿ {x} h r with h L₀.zero
  ... | pre d p with L₀.≈→⊑ⁿ d r
  ... | pre d′ p′ = pre d′ (p′ L₀.∘< p)

  Ω⁺ : LG′
  Ω⁺ = L₁.lc (inj₂ zeroᵍ) L₁.zero (λ { (inj₂ x) e → emb (proj₁ x) ; (inj₁ _) () })

  WF-Ω⁺ : L₁.WF Ω⁺
  WF-Ω⁺ =
    (λ { (inj₂ x) e → L₁.⊴ʷ-zero }) ,
    (λ { (inj₂ x) e (inj₂ y) e′ d → emb-p (s⊑ⁿ→⊑ⁿ d) }) ,
    tt ,
    (λ { (inj₂ x) e → WF-emb (proj₁ x) (proj₁ (proj₂ x)) (proj₂ (proj₂ x)) })

  self-Ω⁺ : Ω⁺ L₁.≈ Ω⁺
  self-Ω⁺ = L₁.o≈ L₀.z≈ L₁.z≈ (λ { (inj₂ x) e (inj₂ y) e′ k → emb≈ k })

  Cf-Ω⁺ : L₁.Cf Ω⁺
  Cf-Ω⁺ = WF-Ω⁺ , self-Ω⁺

  -- 第一路径到不了分支
  first-Ω⁺ : ∀ {k} → k L₁.≪ Ω⁺ → ⊥
  first-Ω⁺ (L₁.fst ())

  -- 每个好层号都在它之下
  below-Ω⁺ : (x : GLv) → emb (proj₁ x) L₁.< Ω⁺
  below-Ω⁺ (x , w , e) = L₁.bra (inj₂ (L₀.suc x , w , L₀.s≈ e)) (λ ()) L₁.zero
```

## §4 逐分支的比较

**`cmpW`.** 分支 $x$ 是好层号, 守卫证据 $e$ 把目标放进 $x$: 那么 $x$ 里的任何第一路径都能与目标比较. 局部上界就是分支 $x$ 自己, 不要世界, 不要 `Mlev`. **这是 [ScafOmega2Family](ScafOmega2Family.lagda.md) 的 `cmpW` 在 `Ordᴵ` 之外的形式.**

```agda
  cmpW : ∀ (x : GLv) {τ a} → L₀.Below τ (proj₁ x) → a L₀.≪ proj₁ x → L₀.CmpF a τ
  cmpW (x , w , sf) (pre d p) r = L₀.shR d (L₀.cmpF w sf r p)

open Up using (NextDom)
```

## §5 塔: 对自然数层

```agda
𝔻ₙ : ℕ → Dom
𝔻ₙ zero    = Dom₀
𝔻ₙ (suc n) = Up.NextDom (𝔻ₙ n)

Ωₙ : ∀ n → Lv.LG (𝔻ₙ (suc n))
Ωₙ n = Up.Ω⁺ (𝔻ₙ n)

Cf-Ωₙ : ∀ n → Lv.Cf (𝔻ₙ (suc n)) (Ωₙ n)
Cf-Ωₙ n = Up.Cf-Ω⁺ (𝔻ₙ n)
```
