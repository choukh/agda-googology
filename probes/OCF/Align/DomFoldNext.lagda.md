# 下一层定义域: 守卫是第一路径

> 不含记号. 结论写在 [DomFold](DomFold.lagda.md).
>
> [GuardTightNext](GuardTightNext.lagda.md) 的守卫是 `⊑ⁿ`, 那里 `no-WFˢ-Ω⁺` 说 $\Omega_2$ 没有 `WFˢ`: $x\sqsubseteq^n y$ 的路径可以穿过 $y$ 的分支, 分支的证据不在表里. 这里把**守卫**换成 `Fg`: $x\approx y$ 或 $x$ 经第一路径在 $y$ 之下. 第一路径只走 `suc`, `lim`, `fst`, 没有新的分支, 所以搬运对一切表成立 (`fg→⊴`). 于是:
>
> - `WF-Ωᶠ`: **$\Omega_2$ 这样的闭包在新守卫下有 `WFˢ`, 无条件, 对任何 `DomX`.** `no-WFˢ-Ω⁺` 不适用: 它的反例 $\Omega+3$, $\Omega\cdot2$ 不满足新守卫 (`no-fg-Ω3-Ω2`, 在 [DomFoldNeg](DomFoldNeg.lagda.md)).
> - 字面上界之下的比较 `bd′`: 两个第一路径 (`cmpFF`). 这是 [ScafOmega2Family](ScafOmega2Family.lagda.md) 的 `cmpW` 的形状: 分支 $x$ 的后继 $x+1$ 就是局部上界, 地板与 $x$ 都是它的第一路径 (`fg<suc`). **没有比较两个分支路径**, `no-bra-cmp` 不碰.
> - `emb⊴`: 下一层的嵌入保持带转移的 `⊴`, 对一切表. 用的是帧的来源 (`cov`): 下层的转移对 `cov` 也成立, 这说明搬运后的路径上每个分支值都是原路径上的分支值.
>
> **代价写在这里, 否定写在 [DomFoldNeg](DomFoldNeg.lagda.md): 这个守卫比 `⊑ⁿ` 窄.** 分支集仍是好层号里向上的一族, 但不是所有比 $c$ 大的 $x$ 都在 $c$ 之上.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DomFoldNext where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Free.Level using (Ordᴵ)
open import OCF.Align.GuardTightLv
open import OCF.Align.DomFoldDom

leq : ℕ → ℕ → Bool
leq zero    _       = true
leq (suc _) zero    = false
leq (suc a) (suc b) = leq a b

pick₂ : ∀ {A : Set} → Bool → A → A → A
pick₂ true  a b = a
pick₂ false a b = b
```

## §1 第一路径的守卫, 在一层之内

```agda
module FgOf (𝔻 : Dom) where
  open Lv 𝔻
  open Dom 𝔻 using ()

  Fg : LG → LG → Set
  Fg a b = (a ≈ b) ⊎ (a ≺ᶠ b)

  infixr 9 _≪∘≪_
  _≪∘≪_ : ∀ {a b c} → a ≪ b → b ≪ c → a ≪ c
  r ≪∘≪ zero    = suc r
  r ≪∘≪ suc s   = suc (r ≪∘≪ s)
  r ≪∘≪ lim n s = lim n (r ≪∘≪ s)
  r ≪∘≪ fst s   = fst (r ≪∘≪ s)

  fg-tr : ∀ {a b c} → Fg a b → Fg b c → Fg a c
  fg-tr (inj₁ d) (inj₁ d′) = inj₁ (≈-trans d d′)
  fg-tr (inj₁ d) (inj₂ (preᶠ e p)) = inj₂ (preᶠ (≈-trans d e) p)
  fg-tr (inj₂ (preᶠ e p)) (inj₁ d′) with ≈-moveᶠ d′ p
  ... | preᶠ e′ p′ = inj₂ (preᶠ (≈-trans e e′) p′)
  fg-tr (inj₂ (preᶠ e p)) (inj₂ (preᶠ e′ p′)) with ≈-moveᶠ e′ p
  ... | preᶠ e″ p″ = inj₂ (preᶠ (≈-trans e e″) (p″ ≪∘≪ p′))

  fg-≈l : ∀ {a a′ b} → a ≈ a′ → Fg a′ b → Fg a b
  fg-≈l d f = fg-tr (inj₁ d) f

  fg-≈r : ∀ {a b b′} → b ≈ b′ → Fg a b′ → Fg a b
  fg-≈r d f = fg-tr f (inj₁ (≈-sym d))

  fg-suc : ∀ {a b} → Fg (suc a) b → Fg a b
  fg-suc (inj₁ (s≈ d)) = inj₂ (preᶠ d zero)
  fg-suc (inj₂ (preᶠ (s≈ d) p)) = inj₂ (preᶠ d (zero ≪∘≪ p))

  fg<suc : ∀ {a b} → b ≈ b → Fg a b → a ≺ᶠ suc b
  fg<suc sf (inj₁ d) = preᶠ d zero
  fg<suc sf (inj₂ (preᶠ d p)) = preᶠ d (suc p)

  ≪→⊴ : ∀ {a y} → y ≈ y → a ≪ y → a ⊴ y
  ≪→⊴ (s≈ e) zero = ⊴-suc-r (≈→⊴ e)
  ≪→⊴ (s≈ e) (suc r) = ⊴-suc-r (≪→⊴ e r)
  ≪→⊴ (l≈ h) (lim n r) = ⊴-lim-r n (≪→⊴ (h n) r)
  ≪→⊴ (o≈ d e h) (fst r) = ⊴-fst (≪→⊴ e r)

  fg→⊴ : ∀ {a b} → b ≈ b → Fg a b → a ⊴ b
  fg→⊴ sf (inj₁ d) = ≈→⊴ d
  fg→⊴ sf (inj₂ (preᶠ d p)) = ⊴-trans (≈→⊴ d) (≪→⊴ sf p)

  selfᶠ : ∀ {a c} → c ≈ c → a ≪ c → a ≈ a
  selfᶠ sf r = selfAt sf (≪→< r)
```

**定理 `cmpFF`.** 同一个好层号里的两条第一路径可比, 对层号结构递归, 没有世界, 没有判决. 极限处比较 $\mathbb N$ 并搬运; 闭包处只有 `fst`. 这是 `cmpF` 的对称形式: 对方也是第一路径, 所以答案也是第一路径.

```agda
  shFl : ∀ {a a′ b} → a ≈ a′ → (Fg a′ b) ⊎ (Fg b a′) → (Fg a b) ⊎ (Fg b a)
  shFl d (inj₁ f) = inj₁ (fg-≈l d f)
  shFl d (inj₂ f) = inj₂ (fg-≈r d f)

  shFr : ∀ {a b b′} → b ≈ b′ → (Fg a b′) ⊎ (Fg b′ a) → (Fg a b) ⊎ (Fg b a)
  shFr d (inj₁ f) = inj₁ (fg-≈r d f)
  shFr d (inj₂ f) = inj₂ (fg-≈l d f)

  cmpFF : ∀ {c} → WFˢ c → c ≈ c → ∀ {a b} → a ≪ c → b ≪ c → (Fg a b) ⊎ (Fg b a)
  cmpFF w (s≈ e) zero zero = inj₁ (inj₁ e)
  cmpFF w (s≈ e) zero (suc q) = inj₂ (inj₂ (preᶠ (selfᶠ e q) q))
  cmpFF w (s≈ e) (suc p) zero = inj₁ (inj₂ (preᶠ (selfᶠ e p) p))
  cmpFF w (s≈ e) (suc p) (suc q) = cmpFF w e p q
  cmpFF (st , w) (l≈ e) (lim n p) (lim m q) with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴f (stepsˢ st n<m) p
  ...   | preᶠ d p′ = shFl d (cmpFF (w m) (e m) p′ q)
  cmpFF (st , w) (l≈ e) (lim n p) (lim m q) | injᵇ m<n with ⊴f (stepsˢ st m<n) q
  ...   | preᶠ d q′ = shFr d (cmpFF (w n) (e n) p q′)
  cmpFF (st , w) (l≈ e) (lim n p) (lim _ q) | injᶜ refl = cmpFF (w n) (e n) p q
  cmpFF (tg , dir , wt , wg) (o≈ d e h) (fst p) (fst q) = cmpFF wt e p q
```

## §2 下一层

```agda
module Next (X : DomX) where
  open DomX X using (𝔻) renaming (⊑-tr to ⊑-tr₀; self< to self<₀; bound to bound₀′; ht to ht₀; ix to ix₀; nodeC to nodeC₀; nodeF to nodeF₀; emᵈ to emᵈ₀; base to base₀; bot to bot₀)
  open Dom 𝔻 renaming (D to D₀; _⊑ᴰ_ to _⊑₀_; _≅ᴰ_ to _≅₀_; sD to s₀; ≅ᴰ-refl to refl₀; ≅ᴰ-sym to sym₀; ≅ᴰ-trans to trans₀;
                       conv to conv₀; gs to gs₀; _<ᴰ_ to _<₀_; bd to bd₀′; s⊑ᴰ to s⊑₀; b₁ to b₀; rd to rd₀; rd-one to rd-one₀; rd-s to rd-s₀; rd-≅ to rd-≅₀; rd-m to rd-m₀)
  module L₀ = Lv 𝔻
  open L₀ using (LG; Cfˢ; WFˢ; _≈_; _≪_; _≺ᶠ_; preᶠ)
  open FgOf 𝔻 public

  GLv : Set
  GLv = Σ LG Cfˢ

  D′ : Set
  D′ = D₀ ⊎ GLv

  _⊑′_ _≅′_ _<′_ : D′ → D′ → Set
  inj₁ a ⊑′ inj₁ b = a ⊑₀ b
  inj₂ x ⊑′ inj₂ y = Fg (proj₁ x) (proj₁ y)
  inj₁ _ ⊑′ inj₂ _ = ⊥
  inj₂ _ ⊑′ inj₁ _ = ⊥
  inj₁ a ≅′ inj₁ b = a ≅₀ b
  inj₂ x ≅′ inj₂ y = proj₁ x ≈ proj₁ y
  inj₁ _ ≅′ inj₂ _ = ⊥
  inj₂ _ ≅′ inj₁ _ = ⊥
  inj₁ a <′ inj₁ b = a <₀ b
  inj₂ a <′ inj₂ b = proj₁ a ≺ᶠ proj₁ b
  inj₂ _ <′ inj₁ _ = ⊥
  inj₁ _ <′ inj₂ _ = ⊥

  s′ : D′ → D′
  s′ (inj₁ a) = inj₁ (s₀ a)
  s′ (inj₂ (x , w , e)) = inj₂ (L₀.suc x , w , L₀.s≈ e)

  gs′ : ∀ {c x y} → c ⊑′ x → s′ x ⊑′ y → c ⊑′ y
  gs′ {inj₁ _} {inj₁ _} {inj₁ _} e e′ = gs₀ e e′
  gs′ {inj₂ _} {inj₂ (x , _)} {inj₂ _} e e′ = fg-tr e (fg-suc e′)
  gs′ {inj₁ _} {inj₂ _} ()
  gs′ {inj₂ _} {inj₁ _} ()
  gs′ {inj₁ _} {inj₁ _} {inj₂ _} e ()
  gs′ {inj₂ _} {inj₂ (_ , _)} {inj₁ _} e ()

  conv′ : ∀ {c c′ x} → c ≅′ c′ → c ⊑′ x → c′ ⊑′ x
  conv′ {inj₁ _} {inj₁ _} {inj₁ _} d e = conv₀ d e
  conv′ {inj₂ _} {inj₂ _} {inj₂ _} d e = fg-≈l (L₀.≈-sym d) e
  conv′ {inj₁ _} {inj₂ _} ()
  conv′ {inj₂ _} {inj₁ _} ()
  conv′ {inj₁ _} {inj₁ _} {inj₂ _} d ()
  conv′ {inj₂ _} {inj₂ _} {inj₁ _} d ()

  -- 字面上界之下的比较: 第 1 层是两条第一路径
  bd′ : ∀ {a b Y} → a <′ Y → b <′ Y → (a ⊑′ b) ⊎ (b ⊑′ a)
  bd′ {inj₁ _} {inj₁ _} {inj₁ _} p q = bd₀′ p q
  bd′ {inj₂ _} {inj₂ _} {inj₂ (y , w , sf)} (preᶠ d p) (preᶠ d′ q) =
    shFl d (shFr d′ (cmpFF w sf p q))
  bd′ {inj₁ _} {inj₂ _} {inj₁ _} p ()
  bd′ {inj₂ _} {inj₁ _} {inj₁ _} ()
  bd′ {inj₂ _} {inj₂ _} {inj₁ _} ()
  bd′ {inj₁ _} {inj₂ _} {inj₂ _} ()
  bd′ {inj₂ _} {inj₁ _} {inj₂ _} p ()
  bd′ {inj₁ _} {inj₁ _} {inj₂ _} ()

  s⊑′ : ∀ {a b} → s′ a ⊑′ b → a ⊑′ b
  s⊑′ {inj₁ _} {inj₁ _} e = s⊑₀ e
  s⊑′ {inj₂ (x , _)} {inj₂ (y , _)} e = fg-suc e
  s⊑′ {inj₁ _} {inj₂ _} ()
  s⊑′ {inj₂ (_ , _)} {inj₁ _} ()

  rd′ : ∀ {η} → inj₁ b₀ ⊑′ η → Ordᴵ
  rd′ {inj₁ _} e = rd₀ e

  NextDom : Dom
  NextDom = record
    { D = D′ ; _⊑ᴰ_ = _⊑′_ ; _≅ᴰ_ = _≅′_ ; sD = s′
    ; ≅ᴰ-refl = λ { (inj₁ a) → refl₀ a ; (inj₂ x) → proj₂ (proj₂ x) }
    ; ≅ᴰ-sym = λ { {inj₁ _} {inj₁ _} d → sym₀ d ; {inj₂ _} {inj₂ _} d → L₀.≈-sym d }
    ; ≅ᴰ-trans = λ { {inj₁ _} {inj₁ _} {inj₁ _} d d′ → trans₀ d d′ ; {inj₂ _} {inj₂ _} {inj₂ _} d d′ → L₀.≈-trans d d′ }
    ; conv = λ {c} {c′} {x} → conv′ {c} {c′} {x} ; gs = λ {c} {x} {y} → gs′ {c} {x} {y}
    ; _<ᴰ_ = _<′_ ; bd = λ {a} {b} {Y} → bd′ {a} {b} {Y} ; s⊑ᴰ = λ {a} {b} → s⊑′ {a} {b}
    ; b₁ = inj₁ b₀ ; rd = λ {η} e → rd′ {η} e
    ; rd-one = λ { {inj₁ _} e → rd-one₀ e }
    ; rd-s = λ { {inj₁ a} {inj₁ b} e e′ d → rd-s₀ {a} {b} e e′ d }
    ; rd-≅ = λ { {inj₁ a} {inj₁ b} e e′ d → rd-≅₀ {a} {b} e e′ d }
    ; rd-m = λ { {inj₁ a} {inj₁ b} e e′ d → rd-m₀ {a} {b} e e′ d }
    }

  module L₁ = Lv NextDom
  open L₁ using () renaming (LG to LG′)
```

## §3 上一层嵌入, 保持带转移的 `⊴`

`emb`, `emb≈`, `emb<`, `emb≪`, `pull*` 与 [GuardTightNext](GuardTightNext.lagda.md) 同形. 新的是拉回带转移: 路径就是原来的路径.

```agda
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

  emb≪ : ∀ {a b} → a ≪ b → emb a L₁.≪ emb b
  emb≪ L₀.zero = L₁.zero
  emb≪ (L₀.suc r) = L₁.suc (emb≪ r)
  emb≪ (L₀.lim n r) = L₁.lim n (emb≪ r)
  emb≪ (L₀.fst r) = L₁.fst (emb≪ r)

  embCᶠ : ∀ {a b} → L₀.Cpᶠ a b → L₁.Cpᶠ (emb a) (emb b)
  embCᶠ L₀.self = L₁.self
  embCᶠ (L₀.suc p) = L₁.suc (embCᶠ p)
  embCᶠ (L₀.lim n p) = L₁.lim n (embCᶠ p)
  embCᶠ (L₀.fst p) = L₁.fst (embCᶠ p)

  embC : ∀ {a b} → L₀.Cp a b → L₁.Cp (emb a) (emb b)
  embC L₀.self = L₁.self
  embC (L₀.suc p) = L₁.suc (embC p)
  embC (L₀.lim n p) = L₁.lim n (embC p)
  embC (L₀.fst p) = L₁.fst (embC p)
  embC (L₀.bra η e p) = L₁.bra (inj₁ η) e (embC p)

  record Pull (b : LG) {k : LG′} (r : k L₁.< emb b) : Set where
    constructor pl
    field
      {k₀} : LG
      eqk  : k ≡ emb k₀
      pth  : k₀ L₀.< b
      rel  : ∀ E → L₁.Adm E r → L₁.Adm E (emb< pth)
  open Pull

  pull : ∀ b {k} (r : k L₁.< emb b) → Pull b r
  pull (L₀.suc a) L₁.zero = pl refl L₀.zero (λ _ _ → tt)
  pull (L₀.suc a) (L₁.suc r) with pull a r
  ... | pl e q u = pl e (L₀.suc q) u
  pull (L₀.lim f) (L₁.lim n r) with pull (f n) r
  ... | pl e q u = pl e (L₀.lim n q) u
  pull (L₀.lc c t g) (L₁.fst r) with pull t r
  ... | pl e q u = pl e (L₀.fst q) u
  pull (L₀.lc c t g) (L₁.bra (inj₁ η) e′ r) with pull (g η e′) r
  ... | pl e q u = pl e (L₀.bra η e′ q) (λ E a → proj₁ a , u E (proj₂ a))

  pullᶠ : ∀ b {k} → k L₁.≪ emb b → Σ LG λ k₀ → (k ≡ emb k₀) × (k₀ ≪ b)
  pullᶠ (L₀.suc a) L₁.zero = a , refl , L₀.zero
  pullᶠ (L₀.suc a) (L₁.suc r) with pullᶠ a r
  ... | k₀ , e , q = k₀ , e , L₀.suc q
  pullᶠ (L₀.lim f) (L₁.lim n r) with pullᶠ (f n) r
  ... | k₀ , e , q = k₀ , e , L₀.lim n q
  pullᶠ (L₀.lc c t g) (L₁.fst r) with pullᶠ t r
  ... | k₀ , e , q = k₀ , e , L₀.fst q

  selfCp : ∀ {a b} → b L₁.≈ b → L₁.Cp a b → a L₁.≈ a
  selfCp e L₁.self = e
  selfCp (L₁.s≈ e) (L₁.suc p) = selfCp e p
  selfCp (L₁.l≈ h) (L₁.lim n p) = selfCp (h n) p
  selfCp (L₁.o≈ d e h) (L₁.fst p) = selfCp e p
  selfCp (L₁.o≈ d e h) (L₁.bra η e₁ p) = selfCp (h η e₁ η e₁ (Dom.≅ᴰ-refl NextDom η)) p

  selfCpᶠ : ∀ {a b} → b L₁.≈ b → L₁.Cpᶠ a b → a L₁.≈ a
  selfCpᶠ e L₁.self = e
  selfCpᶠ (L₁.s≈ e) (L₁.suc p) = selfCpᶠ e p
  selfCpᶠ (L₁.l≈ h) (L₁.lim n p) = selfCpᶠ (h n) p
  selfCpᶠ (L₁.o≈ d e h) (L₁.fst p) = selfCpᶠ e p

  record PullKᶠ (a : LG) (c′ : D′) (t′ : LG′) (g′ : (η : D′) → c′ ⊑′ η → LG′) : Set where
    constructor pkf
    field
      {cf₀} : D₀
      {tf₀} : LG
      {gf₀} : (η : D₀) → cf₀ ⊑₀ η → LG
      eqf   : L₁.lc c′ t′ g′ L₁.≈ emb (L₀.lc cf₀ tf₀ gf₀)
      posf  : L₀.Cpᶠ (L₀.lc cf₀ tf₀ gf₀) a

  pullᵏ : ∀ a {c t g} → L₁.Cpᶠ (L₁.lc c t g) (emb a) → L₁.lc c t g L₁.≈ L₁.lc c t g → PullKᶠ a c t g
  pullᵏ (L₀.suc a) (L₁.suc p) sf with pullᵏ a p sf
  ... | pkf e q = pkf e (L₀.suc q)
  pullᵏ (L₀.lim f) (L₁.lim n p) sf with pullᵏ (f n) p sf
  ... | pkf e q = pkf e (L₀.lim n q)
  pullᵏ (L₀.lc c t g) L₁.self sf = pkf sf L₀.self
  pullᵏ (L₀.lc c t g) (L₁.fst p) sf with pullᵏ t p sf
  ... | pkf e q = pkf e (L₀.fst q)

  record PullK (a : LG) {c′ : D′} {t′ : LG′} {g′ : (η : D′) → c′ ⊑′ η → LG′} (p : L₁.Cp (L₁.lc c′ t′ g′) (emb a)) : Set where
    constructor pk
    field
      {c₀} : D₀
      {t₀} : LG
      {g₀} : (η : D₀) → c₀ ⊑₀ η → LG
      eqK  : L₁.lc c′ t′ g′ L₁.≈ emb (L₀.lc c₀ t₀ g₀)
      posK : L₀.Cp (L₀.lc c₀ t₀ g₀) a
      relK : ∀ E → L₁.AdmC E p → L₁.AdmC E (embC posK)

  pullᴷ : ∀ a {c t g} (p : L₁.Cp (L₁.lc c t g) (emb a)) → L₁.lc c t g L₁.≈ L₁.lc c t g → PullK a p
  pullᴷ (L₀.suc a) (L₁.suc p) sf with pullᴷ a p sf
  ... | pk e q u = pk e (L₀.suc q) u
  pullᴷ (L₀.lim f) (L₁.lim n p) sf with pullᴷ (f n) p sf
  ... | pk e q u = pk e (L₀.lim n q) u
  pullᴷ (L₀.lc c t g) L₁.self sf = pk sf L₀.self (λ _ _ → tt)
  pullᴷ (L₀.lc c t g) (L₁.fst p) sf with pullᴷ t p sf
  ... | pk e q u = pk e (L₀.fst q) u
  pullᴷ (L₀.lc c t g) (L₁.bra (inj₁ η) e′ p) sf with pullᴷ (g η e′) p sf
  ... | pk e q u = pk e (L₀.bra η e′ q) (λ E a → proj₁ a , u E (proj₂ a))
```

**转移.** 下层的 `⊴` 对 `cov (帧)` 也成立. 取帧为原路径自己的帧: 搬运后路径的每个分支值都是原路径的分支值, 键模 $\approx$ 相同. 于是上层任何表的证据都带得过去, 不必把上层的表翻译成下层的表.

```agda
  pFp : ∀ {a c} → a L₀.< c → L₀.Fl
  pFp L₀.zero = L₀.tz
  pFp (L₀.suc r) = pFp r
  pFp (L₀.lim n r) = pFp r
  pFp (L₀.fst r) = pFp r
  pFp (L₀.bra {c = c} {t = t} {g = g} η e r) = L₀.tk (L₀.frm c t g η e) L₀.∪ pFp r

  admWk : ∀ {π ρ a b} → L₀.Wk π ρ → (r : a L₀.< b) → L₀.Adm (L₀.cov π) r → L₀.Adm (L₀.cov ρ) r
  admWk w L₀.zero _ = tt
  admWk w (L₀.suc r) a = admWk w r a
  admWk w (L₀.lim n r) a = admWk w r a
  admWk w (L₀.fst r) a = admWk w r a
  admWk w (L₀.bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) = (c₁ , t₁ , g₁ , e₁ , w m , k) , admWk w r a

  admPp : ∀ {a c} (r : a L₀.< c) → L₀.Adm (L₀.cov (pFp r)) r
  admPp L₀.zero = tt
  admPp (L₀.suc r) = admPp r
  admPp (L₀.lim n r) = admPp r
  admPp (L₀.fst r) = admPp r
  admPp (L₀.bra {c = c} {t = t} {g = g} η e r) = (c , t , g , e , L₀.ml L₀.hr , inj₂ refl) , admWk L₀.mr r (admPp r)

  belFrames : ∀ E {k c} (q : k L₀.< c) → L₁.Adm E (emb< q) → ∀ {f} → L₀.Mem (pFp q) f → L₁.Bel E (emb (L₀.κ f)) (inj₁ (L₀.fη f))
  belFrames E L₀.zero a ()
  belFrames E (L₀.suc q) a m = belFrames E q a m
  belFrames E (L₀.lim n q) a m = belFrames E q a m
  belFrames E (L₀.fst q) a m = belFrames E q a m
  belFrames E (L₀.bra η e q) (u , a) (L₀.ml L₀.hr) = u
  belFrames E (L₀.bra η e q) (u , a) (L₀.mr m) = belFrames E q a m

  belLift : ∀ E {φ y η} → L₀.CovB φ y η → (∀ {f} → L₀.Mem φ f → L₁.Bel E (emb (L₀.κ f)) (inj₁ (L₀.fη f))) → L₁.Bel E (emb y) (inj₁ η)
  belLift E (c₁ , t₁ , g₁ , e₁ , m , inj₁ d) H = L₁.Bel-resp {E} (emb≈ (L₀.≈-sym d)) (H m)
  belLift E (c₁ , t₁ , g₁ , e₁ , m , inj₂ refl) H = H m

  liftAdm : ∀ E {φ k b} (s : k L₀.< b) → L₀.Adm (L₀.cov φ) s → (∀ {f} → L₀.Mem φ f → L₁.Bel E (emb (L₀.κ f)) (inj₁ (L₀.fη f))) → L₁.Adm E (emb< s)
  liftAdm E L₀.zero _ H = tt
  liftAdm E (L₀.suc s) a H = liftAdm E s a H
  liftAdm E (L₀.lim n s) a H = liftAdm E s a H
  liftAdm E (L₀.fst s) a H = liftAdm E s a H
  liftAdm E (L₀.bra η e s) (u , a) H = belLift E u H , liftAdm E s a H

  pFc : ∀ {a c} → L₀.Cp a c → L₀.Fl
  pFc L₀.self = L₀.tz
  pFc (L₀.suc r) = pFc r
  pFc (L₀.lim n r) = pFc r
  pFc (L₀.fst r) = pFc r
  pFc (L₀.bra {c = c} {t = t} {g = g} η e r) = L₀.tk (L₀.frm c t g η e) L₀.∪ pFc r

  admWkC : ∀ {π ρ a b} → L₀.Wk π ρ → (r : L₀.Cp a b) → L₀.AdmC (L₀.cov π) r → L₀.AdmC (L₀.cov ρ) r
  admWkC w L₀.self _ = tt
  admWkC w (L₀.suc r) a = admWkC w r a
  admWkC w (L₀.lim n r) a = admWkC w r a
  admWkC w (L₀.fst r) a = admWkC w r a
  admWkC w (L₀.bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , a) = (c₁ , t₁ , g₁ , e₁ , w m , k) , admWkC w r a

  admPc : ∀ {a c} (r : L₀.Cp a c) → L₀.AdmC (L₀.cov (pFc r)) r
  admPc L₀.self = tt
  admPc (L₀.suc r) = admPc r
  admPc (L₀.lim n r) = admPc r
  admPc (L₀.fst r) = admPc r
  admPc (L₀.bra {c = c} {t = t} {g = g} η e r) = (c , t , g , e , L₀.ml L₀.hr , inj₂ refl) , admWkC L₀.mr r (admPc r)

  belFramesC : ∀ E {k c} (q : L₀.Cp k c) → L₁.AdmC E (embC q) → ∀ {f} → L₀.Mem (pFc q) f → L₁.Bel E (emb (L₀.κ f)) (inj₁ (L₀.fη f))
  belFramesC E L₀.self a ()
  belFramesC E (L₀.suc q) a m = belFramesC E q a m
  belFramesC E (L₀.lim n q) a m = belFramesC E q a m
  belFramesC E (L₀.fst q) a m = belFramesC E q a m
  belFramesC E (L₀.bra η e q) (u , a) (L₀.ml L₀.hr) = u
  belFramesC E (L₀.bra η e q) (u , a) (L₀.mr m) = belFramesC E q a m

  liftAdmC : ∀ E {φ k b} (s : L₀.Cp k b) → L₀.AdmC (L₀.cov φ) s → (∀ {f} → L₀.Mem φ f → L₁.Bel E (emb (L₀.κ f)) (inj₁ (L₀.fη f))) → L₁.AdmC E (embC s)
  liftAdmC E L₀.self _ H = tt
  liftAdmC E (L₀.suc s) a H = liftAdmC E s a H
  liftAdmC E (L₀.lim n s) a H = liftAdmC E s a H
  liftAdmC E (L₀.fst s) a H = liftAdmC E s a H
  liftAdmC E (L₀.bra η e s) (u , a) H = belLift E u H , liftAdmC E s a H

  emb⊴ : ∀ {a b} → a ≈ a → a L₀.⊴ b → emb a L₁.⊴ emb b
  emb⊴ {a} {b} sf x = L₁.⊴i pp ff kk KK
    where
    pp : emb a L₁.⊑ emb b
    pp r with pull a r
    ... | pl refl q u with L₀.⊴p x q
    ...   | L₀.viaᴸ d s t = L₁.viaᴸ (emb≈ d) (emb< s)
              (λ E A → liftAdm E s (t (L₀.cov (pFp q)) (admPp q)) (belFrames E q (u E A)))
    ff : emb a L₁.⊑ᶠ emb b
    ff r with pullᶠ a r
    ... | k₀ , refl , q with L₀.⊴f x q
    ...   | preᶠ d p = L₁.preᶠ (emb≈ d) (emb≪ p)
    kk : emb a L₁.⊑ᵏ emb b
    kk Q with pullᵏ a Q (selfCpᶠ (emb≈ sf) Q)
    ... | pkf e q with L₀.⊴k x q
    ...   | L₀.viaᵏ d p = L₁.viaᵏ (L₁.≈-trans e (emb≈ d)) (embCᶠ p)
    KK : emb a L₁.⊑ᴷ emb b
    KK Q with pullᴷ a Q (selfCp (emb≈ sf) Q)
    ... | pk e q u with L₀.⊴K x q
    ...   | L₀.viaᴷ d p t = L₁.viaᴷ (L₁.≈-trans e (emb≈ d)) (embC p)
              (λ E A → liftAdmC E p (t (L₀.cov (pFc q)) (admPc q)) (belFramesC E q (u E A)))

  WFˢ-emb : ∀ a → WFˢ a → a ≈ a → L₁.WFˢ (emb a)
  WFˢ-emb L₀.zero w sf = tt
  WFˢ-emb (L₀.suc a) w (L₀.s≈ sf) = WFˢ-emb a w sf
  WFˢ-emb (L₀.lim f) (st , w) (L₀.l≈ sf) = (λ n → emb⊴ (sf n) (st n)) , (λ n → WFˢ-emb (f n) (w n) (sf n))
  WFˢ-emb (L₀.lc c t g) (tg , dir , wt , wg) (L₀.o≈ d se sh) =
    (λ { (inj₁ η) e → emb⊴ se (tg η e) }) ,
    (λ { (inj₁ η) e (inj₁ η′) e′ d′ → emb⊴ (sh η e η e (refl₀ η)) (dir η e η′ e′ d′) }) ,
    WFˢ-emb t wt se ,
    (λ { (inj₁ η) e → WFˢ-emb (g η e) (wg η e) (sh η e η e (refl₀ η)) })

  Cf-emb : ∀ a → Cfˢ a → L₁.Cfˢ (emb a)
  Cf-emb a (w , sf) = WFˢ-emb a w sf , emb≈ sf
```

## §4 下一个基数

`Ωᶠ`: $\sup_x x$, $x$ 取好层号, 守卫是第一路径. 第一支与下界都是 `base`: 第 1 层是 $\Omega_1$, 第 $n+1$ 层是上一层的 `Ωᶠ` (`X′` 的 `base`). 这与 EBO 的 $\gamma_0=\Omega_\mu$ 同形 (**受记号影响**: 第一支是看记号的 $\gamma$-链定的).

**定理 `WF-Ωᶠ`, `Cf-Ωᶠ`.** 对任何 `DomX`, 无条件.

```agda
  sfO : (x : GLv) → proj₁ x ≈ proj₁ x
  sfO x = proj₂ (proj₂ x)

  Ωᶠ : LG′
  Ωᶠ = L₁.lc (inj₂ base₀) (emb (proj₁ base₀)) (λ { (inj₂ x) e → emb (proj₁ x) ; (inj₁ _) () })

  WF-Ωᶠ : L₁.WFˢ Ωᶠ
  WF-Ωᶠ =
    (λ { (inj₂ x) e → emb⊴ (sfO base₀) (fg→⊴ (sfO x) e) }) ,
    (λ { (inj₂ x) e (inj₂ y) e′ d → emb⊴ (sfO x) (fg→⊴ (sfO y) d) }) ,
    WFˢ-emb (proj₁ base₀) (proj₁ (proj₂ base₀)) (sfO base₀) ,
    (λ { (inj₂ x) e → WFˢ-emb (proj₁ x) (proj₁ (proj₂ x)) (sfO x) })

  self-Ωᶠ : Ωᶠ L₁.≈ Ωᶠ
  self-Ωᶠ = L₁.o≈ (sfO base₀) (emb≈ (sfO base₀)) (λ { (inj₂ x) e (inj₂ y) e′ k → emb≈ k })

  Cf-Ωᶠ : L₁.Cfˢ Ωᶠ
  Cf-Ωᶠ = WF-Ωᶠ , self-Ωᶠ

  -- 每个在 base 之上的好层号都在 Ωᶠ 之下
  below-Ωᶠ : (x : GLv) → Fg (proj₁ base₀) (L₀.suc (proj₁ x)) → emb (proj₁ x) L₁.< Ωᶠ
  below-Ωᶠ (x , w , e) f = L₁.bra (inj₂ (L₀.suc x , w , L₀.s≈ e)) f L₁.zero
```

## §5 求界

目标层: 地板全在第 0 支 (`inj₁`) 就交给下一层; 全在第 1 支 (`inj₂`) 就在字面上界 $Y$ 之下取最大 (`maxF`), 局部上界是分支的后继.

```agda
  private
    module F₀ = FlrOf 𝔻
    module F₁ = FlrOf NextDom

  dn : F₁.Flr → F₀.Flr
  dn F₁.fz = F₀.fz
  dn (F₁.fk (inj₁ K)) = F₀.fk K
  dn (F₁.fk (inj₂ _)) = F₀.fz
  dn (a F₁.⊔ b) = dn a F₀.⊔ dn b

  toE₁ : ∀ {ℓ} φ → F₁.Ev (inj₁ ℓ) φ → F₀.Ev ℓ (dn φ)
  toE₁ F₁.fz e = tt
  toE₁ (F₁.fk (inj₁ K)) e = e
  toE₁ (F₁.fk (inj₂ _)) ()
  toE₁ (a F₁.⊔ b) (x , y) = toE₁ a x , toE₁ b y

  ofE₁ : ∀ {ℓ Y} φ → F₁.Ev (inj₁ ℓ) φ → F₀.Ev Y (dn φ) → F₁.Ev (inj₁ Y) φ
  ofE₁ F₁.fz _ e = tt
  ofE₁ (F₁.fk (inj₁ K)) _ e = e
  ofE₁ (F₁.fk (inj₂ _)) () e
  ofE₁ (a F₁.⊔ b) (u , v) (x , y) = ofE₁ a u x , ofE₁ b v y

  inDn : ∀ {K φ} → F₁.InF (inj₁ K) φ → F₀.InF K (dn φ)
  inDn F₁.ink = F₀.ink
  inDn (F₁.inl i) = F₀.inl (inDn i)
  inDn (F₁.inr i) = F₀.inr (inDn i)

  record MaxR (Y : GLv) (φ : F₁.Flr) (m : GLv) : Set where
    constructor mxr
    field
      M   : GLv
      M<  : proj₁ M ≺ᶠ proj₁ Y
      m⊑  : Fg (proj₁ m) (proj₁ M)
      all : ∀ {K} → F₁.InF K φ → K ⊑′ inj₂ M

  maxF : ∀ {Y} φ → F₁.Ev (inj₂ Y) φ → ∀ m → proj₁ m ≺ᶠ proj₁ Y → MaxR Y φ m
  maxF F₁.fz e m q = mxr m q (inj₁ (sfO m)) (λ ())
  maxF (F₁.fk (inj₁ _)) () m q
  maxF {Y} (F₁.fk (inj₂ k)) e m q with bd′ {inj₂ m} {inj₂ k} {inj₂ Y} q e
  ... | inj₁ f = mxr k e f (λ { F₁.ink → inj₁ (sfO k) })
  ... | inj₂ f = mxr m q (inj₁ (sfO m)) (λ { F₁.ink → f })
  maxF (a F₁.⊔ b) (x , y) m q with maxF a x m q
  ... | mxr M₁ M₁< m₁ al₁ with maxF b y M₁ M₁<
  ...   | mxr M₂ M₂< m₂ al₂ = mxr M₂ M₂< (fg-tr m₁ m₂)
          (λ { (F₁.inl i) → up⊑ (al₁ i) m₂ ; (F₁.inr i) → al₂ i })
    where
    up⊑ : ∀ {K M M′} → K ⊑′ inj₂ M → Fg (proj₁ M) (proj₁ M′) → K ⊑′ inj₂ M′
    up⊑ {inj₂ _} f g = fg-tr f g

  evsuc : ∀ {x} φ → (∀ {K} → F₁.InF K φ → K ⊑′ inj₂ x) → F₁.Ev (s′ (inj₂ x)) φ
  evsuc F₁.fz h = tt
  evsuc {x} (F₁.fk (inj₁ K)) h with h F₁.ink
  ... | ()
  evsuc {x} (F₁.fk (inj₂ k)) h = fg<suc (sfO x) (h F₁.ink)
  evsuc (a F₁.⊔ b) h = evsuc a (λ i → h (F₁.inl i)) , evsuc b (λ i → h (F₁.inr i))

  bound′ : ∀ {ℓ K₀} (φ : F₁.Flr) → F₁.Ev ℓ φ → K₀ <′ ℓ → F₁.Tp ℓ φ
  bound′ {inj₁ ℓ} {inj₁ K₀} φ y q = F₁.tpr (inj₁ (F₀.Bd B)) kb
      (λ { {inj₁ η} d → inj₁ (F₀.upX B d) ; {inj₂ _} () })
      (λ { {inj₁ η} d → ofE₁ φ y (F₀.upEv B d) ; {inj₂ _} () })
      (λ { {inj₁ η} d → F₀.up< B d ; {inj₂ _} () })
    where
    B = bound₀′ (dn φ) (toE₁ φ y) q
    kb : ∀ {K} → F₁.InF K φ → K ⊑′ inj₁ (F₀.Bd B)
    kb {inj₁ K} i = F₀.Kb B (inDn i)
    kb {inj₂ K} i with F₁.evIn y i
    ... | ()
  bound′ {inj₁ _} {inj₂ _} φ y ()
  bound′ {inj₂ _} {inj₁ _} φ y ()
  bound′ {inj₂ Y} {inj₂ k₀} φ y q with maxF φ y k₀ q
  ... | mxr M M< m⊑ all = F₁.tpr (inj₂ M) all
      (λ { {inj₂ x} d → s′ (inj₂ x) ; {inj₁ _} () })
      (λ { {inj₂ x} d → evsuc φ (λ i → tr′ (all i) d) ; {inj₁ _} () })
      (λ { {inj₂ x} d → preᶠ (sfO x) L₀.zero ; {inj₁ _} () })
    where
    tr′ : ∀ {K M x} → K ⊑′ inj₂ M → Fg (proj₁ M) (proj₁ x) → K ⊑′ inj₂ x
    tr′ {inj₂ _} f g = fg-tr f g
```

## §6 `DomX` 的下一层

```agda
  ⊑-tr′ : ∀ {a b c} → a ⊑′ b → b ⊑′ c → a ⊑′ c
  ⊑-tr′ {inj₁ _} {inj₁ _} {inj₁ _} p q = ⊑-tr₀ p q
  ⊑-tr′ {inj₂ _} {inj₂ _} {inj₂ _} p q = fg-tr p q
  ⊑-tr′ {inj₁ _} {inj₂ _} ()
  ⊑-tr′ {inj₂ _} {inj₁ _} ()
  ⊑-tr′ {inj₁ _} {inj₁ _} {inj₂ _} p ()
  ⊑-tr′ {inj₂ _} {inj₂ _} {inj₁ _} p ()

  self<′ : ∀ η → η <′ s′ η
  self<′ (inj₁ a) = self<₀ a
  self<′ (inj₂ x) = preᶠ (sfO x) L₀.zero

  X′ : DomX
  X′ = record
    { 𝔻 = NextDom
    ; ⊑-tr = λ {a} {b} {c} → ⊑-tr′ {a} {b} {c}
    ; self< = self<′
    ; bound = λ {ℓ} {K₀} φ y q → bound′ {ℓ} {K₀} φ y q
    ; ht = suc ht₀
    ; ix = λ { (inj₁ a) → ix₀ a ; (inj₂ _) → suc ht₀ }
    ; nodeC = λ n → pick₂ (leq n ht₀) (inj₁ (nodeC₀ n)) (inj₂ base₀)
    ; nodeF = λ n → pick₂ (leq n ht₀) (emb (nodeF₀ n)) (emb (proj₁ base₀))
    ; emᵈ = λ { (inj₁ a) → emb (emᵈ₀ a) ; (inj₂ x) → emb (proj₁ x) }
    ; base = Ωᶠ , Cf-Ωᶠ
    ; bot = inj₁ bot₀
    }
```

## §7 塔: 对 $n$ 一致

```agda
Xₙ : ℕ → DomX
Xₙ zero    = X₀
Xₙ (suc n) = Next.X′ (Xₙ n)

-- Ω_{n+2}: 第 n+1 层定义域上的层号. 一个定义.
Ωₙ : ∀ n → Lv.LG (DomX.𝔻 (Xₙ (suc n)))
Ωₙ n = Next.Ωᶠ (Xₙ n)

Cf-Ωₙ : ∀ n → Lv.Cfˢ (DomX.𝔻 (Xₙ (suc n))) (Ωₙ n)
Cf-Ωₙ n = Next.Cf-Ωᶠ (Xₙ n)
```
