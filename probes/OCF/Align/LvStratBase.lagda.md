# 分层的 $\approx$: 地板、低层含 `limᴼ`、相对比较 (底座)

> 底座, 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). 由 [LevelKBase](LevelKBase.lagda.md) 改写. 与它的差别: (1) 低层不再要 `NoO`, `limᴼ` 可以低; (2) `BL`, `low-at` 只问可容许路径; (3) `Lo` 的分支只问地板; (4) 树的可容许性 `Tw`: 原始的树在 `limᴼ` 层上可以有不可容许的节点与 `up`, 所以 "层号的前驱都低" 不再对原始的树成立, 要显式地带上; (5) $\approx$ 有第二个构造子 `b≈`: 两侧参数层只要 $\approx$, 分支用来回搬运 (不要字面相同); (6) `Stage` 去掉 `low-≈`, 改成 `low≈` (低层对 $\approx$ 封闭) 与 `A-tr` (地板跨层封闭).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvStratBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; toLv; toLvD; Tree; limᵢ; up; intoL; outL; down; Dn; DnT; outD; Ω)
```

## §0 可容许路径与地板

`BL k`: 这一层的**可容许**前驱都低. 低层对可容许前驱封闭, 所以低层都是 `BL`. `Lo`: 层号的参数层都低, 分支只问地板. 这两个都不再提 `NoO`.

`Tw k x`: 树 $x$ 的节点路径可容许, `limᴼ` 层上的 `up` 带地板里的分支. 树的分支只问地板. **这是新的**: `NoO` 的层上它自动成立 (路径全可容许, 没有 `limᴼ` 的 `up`), `limᴼ` 的层上原始的树不满足, 所以 `lo-toLv` 要它.

```agda
AdmOf : ((k : Lv) → Ordᴸ k → Set) → (c : Lv) → Pre c → Set
AdmOf B (suc k)    (inj₁ _)        = ⊤
AdmOf B (suc k)    (inj₂ r)        = AdmOf B k r
AdmOf B (lim f)    (n , r)         = AdmOf B (f n) r
AdmOf B (limᴼ k g) (inj₁ (inj₁ _)) = ⊤
AdmOf B (limᴼ k g) (inj₁ (inj₂ r)) = AdmOf B k r
AdmOf B (limᴼ k g) (inj₂ (x , r))  = B k x × AdmOf B (g x) r

-- 层上的搬运. 对两个层号的结构递归, 不看证据, 总函数: 头不合就给 `zero`.
-- 形状同 `InaccTreeBase.tr`, 差别是那里的证据对全部原始分支成立, 这里的 $\approx$ 只对地板成立,
-- 所以证据不能进定义. 只在地板上才有规格 (`LvStratTr`).
tr  : (a b : Lv) → Ordᴸ a → Ordᴸ b
res : (a b : Lv) (r : Pre a) → Maybe (Σ (Pre b) λ r′ → Ordᴸ (at b r′) → Ordᴸ (at a r))

tr a b Tree.zero    = Tree.zero
tr a b (Tree.suc x) = Tree.suc (tr a b x)
tr a b (Tree.lim h) = Tree.lim (λ n → tr a b (h n))
tr a b (limᵢ r f) with res a b r
... | just (r′ , bk) = limᵢ r′ (λ y → tr a b (f (intoL a r (bk (outL b r′ y)))))
... | nothing        = Tree.zero
tr (suc a) (suc b) (up _ x) = up tt (tr a b x)
tr (lim f) (lim g) (up n x) = up n (tr (f n) (g n) x)
tr (limᴼ k h) (limᴼ k′ h′) (up x t) = up (tr k k′ x) (tr (h x) (h′ (tr k k′ x)) t)
tr _ _ (up _ _) = Tree.zero

mapI : ∀ {b c} {P : Set} (i : Pre b → P) (at′ : P → Lv) → (∀ q → at′ (i q) ≡ at b q) →
       Maybe (Σ (Pre b) λ r′ → Ordᴸ (at b r′) → Ordᴸ c) → Maybe (Σ P λ r′ → Ordᴸ (at′ r′) → Ordᴸ c)
mapI i at′ e (just (q , bk)) = just (i q , λ y → bk (subst Ordᴸ (e q) y))
mapI i at′ e nothing = nothing

res (suc a) (suc b) (inj₁ _) = just (inj₁ tt , tr b a)
res (suc a) (suc b) (inj₂ r) = mapI {b} {at a r} inj₂ (at (suc b)) (λ _ → refl) (res a b r)
res (lim f) (lim g) (n , r)  = mapI {g n} {at (f n) r} (n ,_) (at (lim g)) (λ _ → refl) (res (f n) (g n) r)
res (limᴼ k h) (limᴼ k′ h′) (inj₁ (inj₁ _)) = just (inj₁ (inj₁ tt) , tr k′ k)
res (limᴼ k h) (limᴼ k′ h′) (inj₁ (inj₂ r)) =
  mapI {k′} {at k r} (λ q → inj₁ (inj₂ q)) (at (limᴼ k′ h′)) (λ _ → refl) (res k k′ r)
res (limᴼ k h) (limᴼ k′ h′) (inj₂ (x , r)) =
  mapI {h′ (tr k k′ x)} {at (h x) r} (λ q → inj₂ (tr k k′ x , q)) (at (limᴼ k′ h′)) (λ _ → refl)
    (res (h x) (h′ (tr k k′ x)) r)
res _ _ _ = nothing

LoOf : (Lv → Set) → ((k : Lv) → Ordᴸ k → Set) → Lv → Set
LoOf Lw A zero       = ⊤
LoOf Lw A (suc k)    = LoOf Lw A k
LoOf Lw A (lim f)    = ∀ n → LoOf Lw A (f n)
LoOf Lw A (limᴼ k g) = Lw k × (∀ x → A k x → LoOf Lw A (g x))

record Fl : Set₁ where
  field
    Lw : Lv → Set
    A   : (k : Lv) → Ordᴸ k → Set
    A→Lw   : ∀ k x → A k x → Lw k
    low-at  : ∀ j → Lw j → ∀ r → AdmOf A j r → Lw (at j r)
    low-lo  : ∀ j → Lw j → LoOf Lw A j

  Bs : (k : Lv) → Ordᴸ k → Set
  Bs k x = Lw k → A k x

  A⊆B : ∀ k x → A k x → Bs k x
  A⊆B k x a _ = a

  BL : Lv → Set
  BL k = ∀ r → AdmOf A k r → Lw (at k r)

  lw→bl : ∀ {j} → Lw j → BL j
  lw→bl {j} l = low-at j l

  bl-suc : ∀ {k} → BL (suc k) → BL k
  bl-suc h r d = h (inj₂ r) d

  bl-lim : ∀ {f} n → BL (lim f) → BL (f n)
  bl-lim m h r d = h (m , r) d

  bl-par : ∀ {k g} → BL (limᴼ k g) → Lw k
  bl-par h = h (inj₁ (inj₁ tt)) tt

  bl-o : ∀ {k g x} → BL (limᴼ k g) → A k x → BL (g x)
  bl-o {x = x} h a r d = h (inj₂ (x , r)) (a , d)

  -- 路径可容许 (相对于 `Bs`) 在 `BL` 的层上就是可容许
  bl-adm : ∀ {c} → BL c → ∀ r → AdmOf Bs c r → AdmOf A c r
  bl-adm {suc k}    b (inj₁ _)        d = tt
  bl-adm {suc k}    b (inj₂ r)        d = bl-adm (bl-suc b) r d
  bl-adm {lim f}    b (n , r)         d = bl-adm (bl-lim n b) r d
  bl-adm {limᴼ k g} b (inj₁ (inj₁ _)) d = tt
  bl-adm {limᴼ k g} b (inj₁ (inj₂ r)) d = bl-adm (lw→bl (bl-par b)) r d
  bl-adm {limᴼ k g} b (inj₂ (x , r)) (a , d) =
    let ax = a (bl-par b) in ax , bl-adm (bl-o b ax) r d

  blL : ∀ {c} → BL c → ∀ r → AdmOf Bs c r → Lw (at c r)
  blL b r d = b r (bl-adm b r d)

  Lo : Lv → Set
  Lo = LoOf Lw A

  Tw : ∀ k → Ordᴸ k → Set
  Tw k Tree.zero     = ⊤
  Tw k (Tree.suc x)  = Tw k x
  Tw k (Tree.lim h)  = ∀ n → Tw k (h n)
  Tw k (limᵢ r f)    = AdmOf A k r × (∀ z → A (at k r) z → Tw k (f (intoL k r z)))
  Tw (suc k)    (up d x) = Tw k x
  Tw (lim f)    (up n x) = Tw (f n) x
  Tw (limᴼ k g) (up d x) = A k d × Tw (g d) x

  lo-toLv : ∀ {k} → BL k → (x : Ordᴸ k) → Tw k x → Lo (toLv x)
  lo-toLv b Tree.zero     _ = tt
  lo-toLv b (Tree.suc x)  t = lo-toLv b x t
  lo-toLv b (Tree.lim h)  t = λ n → lo-toLv b (h n) (t n)
  lo-toLv {k} b (limᵢ r f) (a , t) = b r a , (λ y ay → lo-toLv b (f (intoL k r y)) (t y ay))
  lo-toLv {suc k} b (up d x) t = lo-toLv (bl-suc b) x t
  lo-toLv {lim f} b (up n x) t = lo-toLv (bl-lim n b) x t
  lo-toLv {limᴼ k g} b (up d x) (a , t) = lo-toLv (bl-o b a) x t

  -- 参数层全低的层号上, `Bs` 的路径就是地板的路径: 问它的判决只问地板
  lo-adm : ∀ a → Lo a → ∀ r → AdmOf Bs a r → AdmOf A a r
  lo-adm (suc k)    w (inj₁ _)        d = tt
  lo-adm (suc k)    w (inj₂ r)        d = lo-adm k w r d
  lo-adm (lim f)    w (n , r)         d = lo-adm (f n) (w n) r d
  lo-adm (limᴼ k g) w (inj₁ (inj₁ _)) d = tt
  lo-adm (limᴼ k g) w (inj₁ (inj₂ r)) d = lo-adm k (low-lo k (proj₁ w)) r d
  lo-adm (limᴼ k g) w (inj₂ (x , r)) (a , d) =
    let ax = a (proj₁ w) in ax , lo-adm (g x) (proj₂ w x ax) r d

  lo-at : ∀ a → Lo a → ∀ r → AdmOf A a r → Lo (at a r)
  lo-at (suc k)    w (inj₁ _)        _ = w
  lo-at (suc k)    w (inj₂ r)        d = lo-at k w r d
  lo-at (lim f)    w (n , r)         d = lo-at (f n) (w n) r d
  lo-at (limᴼ k g) w (inj₁ (inj₁ _)) _ = low-lo k (proj₁ w)
  lo-at (limᴼ k g) w (inj₁ (inj₂ r)) d = lo-at k (low-lo k (proj₁ w)) r d
  lo-at (limᴼ k g) w (inj₂ (x , r)) (a , d) = lo-at (g x) (proj₂ w x a) r d
```

## §1 叶子与相对比较

```agda
module Leaf (F : Fl) where
  open Fl F public

  infix 4 _≈ᴮ_
  data _≈ᴮ_ : Lv → Lv → Set where
    z≈ : zero ≈ᴮ zero
    s≈ : ∀ {a b} → a ≈ᴮ b → suc a ≈ᴮ suc b
    l≈ : ∀ {f g} → (∀ n → f n ≈ᴮ g n) → lim f ≈ᴮ lim g
    o≈ : ∀ {k g g′} → (∀ x → Bs k x → g x ≈ᴮ g′ x) → limᴼ k g ≈ᴮ limᴼ k g′
    b≈ : ∀ {k k′ g g′} → Lw k → Lw k′ → k ≈ᴮ k′ →
         (∀ x → A k x → Σ (Ordᴸ k′) λ x′ → A k′ x′ × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g′ x′) →
         (∀ x′ → A k′ x′ → Σ (Ordᴸ k) λ x → A k x × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g′ x′) →
         limᴼ k g ≈ᴮ limᴼ k′ g′

  ≈ᴮ-refl : ∀ a → a ≈ᴮ a
  ≈ᴮ-refl zero       = z≈
  ≈ᴮ-refl (suc a)    = s≈ (≈ᴮ-refl a)
  ≈ᴮ-refl (lim f)    = l≈ (λ n → ≈ᴮ-refl (f n))
  ≈ᴮ-refl (limᴼ k g) = o≈ (λ x _ → ≈ᴮ-refl (g x))

  ≈ᴮ-sym : ∀ {a b} → a ≈ᴮ b → b ≈ᴮ a
  ≈ᴮ-sym z≈     = z≈
  ≈ᴮ-sym (s≈ e) = s≈ (≈ᴮ-sym e)
  ≈ᴮ-sym (l≈ h) = l≈ (λ n → ≈ᴮ-sym (h n))
  ≈ᴮ-sym (o≈ h) = o≈ (λ x d → ≈ᴮ-sym (h x d))
  ≈ᴮ-sym {limᴼ k g} {limᴼ k′ g′} (b≈ l l′ e u v) = b≈ l′ l (≈ᴮ-sym e) sym-v sym-u
    where
    sym-v : ∀ x → A k′ x → Σ (Ordᴸ k) λ x′ → A k x′ × toLv x ≈ᴮ toLv x′ × g′ x ≈ᴮ g x′
    sym-v x a with v x a
    ... | y , ay , t , q = y , ay , ≈ᴮ-sym t , ≈ᴮ-sym q
    sym-u : ∀ x′ → A k x′ → Σ (Ordᴸ k′) λ x → A k′ x × toLv x ≈ᴮ toLv x′ × g′ x ≈ᴮ g x′
    sym-u x a with u x a
    ... | y , ay , t , q = y , ay , ≈ᴮ-sym t , ≈ᴮ-sym q

  ≈ᴮ-trans : ∀ {a b c} → a ≈ᴮ b → b ≈ᴮ c → a ≈ᴮ c
  ≈ᴮ-trans z≈     z≈      = z≈
  ≈ᴮ-trans (s≈ e) (s≈ e′) = s≈ (≈ᴮ-trans e e′)
  ≈ᴮ-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈ᴮ-trans (h n) (h′ n))
  ≈ᴮ-trans (o≈ h) (o≈ h′) = o≈ (λ x d → ≈ᴮ-trans (h x d) (h′ x d))
  ≈ᴮ-trans {limᴼ k g} {limᴼ .k g₁} {limᴼ k₂ g₂} (o≈ h) (b≈ l l′ e u v) = b≈ l l′ e u′ v′
    where
    u′ : ∀ x → A k x → Σ (Ordᴸ k₂) λ x′ → A k₂ x′ × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g₂ x′
    u′ x a with u x a
    ... | y , ay , t , q = y , ay , t , ≈ᴮ-trans (h x (A⊆B k x a)) q
    v′ : ∀ x′ → A k₂ x′ → Σ (Ordᴸ k) λ x → A k x × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g₂ x′
    v′ x a with v x a
    ... | y , ay , t , q = y , ay , t , ≈ᴮ-trans (h y (A⊆B k y ay)) q
  ≈ᴮ-trans {limᴼ k g} {limᴼ k₁ g₁} {limᴼ .k₁ g₂} (b≈ l l′ e u v) (o≈ h) = b≈ l l′ e u′ v′
    where
    u′ : ∀ x → A k x → Σ (Ordᴸ k₁) λ x′ → A k₁ x′ × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g₂ x′
    u′ x a with u x a
    ... | y , ay , t , q = y , ay , t , ≈ᴮ-trans q (h y (A⊆B k₁ y ay))
    v′ : ∀ x′ → A k₁ x′ → Σ (Ordᴸ k) λ x → A k x × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g₂ x′
    v′ x a with v x a
    ... | y , ay , t , q = y , ay , t , ≈ᴮ-trans q (h x (A⊆B k₁ x a))
  ≈ᴮ-trans {limᴼ k g} {limᴼ k₁ g₁} {limᴼ k₂ g₂} (b≈ l l₁ e u v) (b≈ l₁′ l₂ e′ u₂ v₂) = b≈ l l₂ (≈ᴮ-trans e e′) u′ v′
    where
    u′ : ∀ x → A k x → Σ (Ordᴸ k₂) λ x′ → A k₂ x′ × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g₂ x′
    u′ x a with u x a
    ... | y , ay , t , q with u₂ y ay
    ...   | w , aw , t′ , q′ = w , aw , ≈ᴮ-trans t t′ , ≈ᴮ-trans q q′
    v′ : ∀ x′ → A k₂ x′ → Σ (Ordᴸ k) λ x → A k x × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g₂ x′
    v′ x a with v₂ x a
    ... | y , ay , t , q with v y ay
    ...   | w , aw , t′ , q′ = w , aw , ≈ᴮ-trans t′ t , ≈ᴮ-trans q′ q

  -- `o≈` 两侧参数层不是变量时用
  o≈′ : ∀ {j j′ g g′} (e : j ≡ j′) → (∀ x → Bs j x → g x ≈ᴮ g′ (subst Ordᴸ e x)) → limᴼ j g ≈ᴮ limᴼ j′ g′
  o≈′ refl h = o≈ h

  -- 低层上两个构造子合一: 参数层 $\approx$, 来回搬运
  o≈-inv : ∀ {j j′ g g′} → Lw j → limᴼ j g ≈ᴮ limᴼ j′ g′ →
           j ≈ᴮ j′ ×
           (∀ x → A j x → Σ (Ordᴸ j′) λ x′ → A j′ x′ × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g′ x′) ×
           (∀ x′ → A j′ x′ → Σ (Ordᴸ j) λ x → A j x × toLv x ≈ᴮ toLv x′ × g x ≈ᴮ g′ x′)
  o≈-inv {j} l (o≈ h) =
    ≈ᴮ-refl j ,
    (λ x a → x , a , ≈ᴮ-refl _ , h x (A⊆B j x a)) ,
    (λ x a → x , a , ≈ᴮ-refl _ , h x (A⊆B j x a))
  o≈-inv l (b≈ _ _ e u v) = e , u , v

  AdmB : (c : Lv) → Pre c → Set
  AdmB = AdmOf Bs

  Adm : (c : Lv) → Pre c → Set
  Adm = AdmOf A

  Adm→B : ∀ c r → Adm c r → AdmB c r
  Adm→B (suc k)    (inj₁ _)        d = tt
  Adm→B (suc k)    (inj₂ r)        d = Adm→B k r d
  Adm→B (lim f)    (n , r)         d = Adm→B (f n) r d
  Adm→B (limᴼ k g) (inj₁ (inj₁ _)) d = tt
  Adm→B (limᴼ k g) (inj₁ (inj₂ r)) d = Adm→B k r d
  Adm→B (limᴼ k g) (inj₂ (x , r)) (a , d) = A⊆B k x a , Adm→B (g x) r d

  path≈ : ∀ {a b} → a ≈ᴮ b → (r : Pre a) → AdmB a r → Σ (Pre b) λ r′ → AdmB b r′ × at a r ≈ᴮ at b r′
  path≈ (s≈ e) (inj₁ _) _ = inj₁ tt , tt , e
  path≈ (s≈ e) (inj₂ r) d with path≈ e r d
  ... | r′ , d′ , e′ = inj₂ r′ , d′ , e′
  path≈ (l≈ h) (n , r) d with path≈ (h n) r d
  ... | r′ , d′ , e′ = (n , r′) , d′ , e′
  path≈ (o≈ {k} h) (inj₁ (inj₁ _)) _ = inj₁ (inj₁ tt) , tt , ≈ᴮ-refl k
  path≈ (o≈ h) (inj₁ (inj₂ r)) d = inj₁ (inj₂ r) , d , ≈ᴮ-refl _
  path≈ (o≈ h) (inj₂ (x , r)) (a , d) with path≈ (h x a) r d
  ... | r′ , d′ , e′ = inj₂ (x , r′) , (a , d′) , e′
  path≈ (b≈ l l′ e u v) (inj₁ (inj₁ _)) _ = inj₁ (inj₁ tt) , tt , e
  path≈ (b≈ l l′ e u v) (inj₁ (inj₂ r)) d with path≈ e r d
  ... | r′ , d′ , e′ = inj₁ (inj₂ r′) , d′ , e′
  path≈ {limᴼ k g} {limᴼ k′ g′} (b≈ l l′ e u v) (inj₂ (x , r)) (a , d) with u x (a l)
  ... | y , ay , t , q with path≈ q r d
  ...   | r′ , d′ , e′ = inj₂ (y , r′) , (A⊆B k′ y ay , d′) , e′

  record _≺ᴬ_ (a b : Lv) : Set where
    constructor viaᴬ
    field
      pthᴬ : Pre b
      admᴬ : Adm b pthᴬ
      prfᴬ : a ≈ᴮ at b pthᴬ

  _⊑ᴬ_ : Lv → Lv → Set
  a ⊑ᴬ b = (r : Pre a) → Adm a r → at a r ≺ᴬ b

  ≺ᴬ-respˡ : ∀ {a a′ b} → a′ ≈ᴮ a → a ≺ᴬ b → a′ ≺ᴬ b
  ≺ᴬ-respˡ e (viaᴬ r d e′) = viaᴬ r d (≈ᴮ-trans e e′)

  ⊑ᴬ-trans : ∀ {a b c} → a ⊑ᴬ b → b ⊑ᴬ c → a ⊑ᴬ c
  ⊑ᴬ-trans σ τ r d with σ r d
  ... | viaᴬ s ds e = ≺ᴬ-respˡ e (τ s ds)

  ⊑ᴬ-refl : ∀ {a} → a ⊑ᴬ a
  ⊑ᴬ-refl r d = viaᴬ r d (≈ᴮ-refl _)

  ≺⊑ : ∀ {a b c} → a ≺ᴬ b → b ⊑ᴬ c → a ≺ᴬ c
  ≺⊑ (viaᴬ s ds e) τ = ≺ᴬ-respˡ e (τ s ds)

  ≈⊑ : ∀ {a b} → a ≈ᴮ b → a ⊑ᴬ b
  ≈⊑ (s≈ e) (inj₁ _) _ = viaᴬ (inj₁ tt) tt e
  ≈⊑ (s≈ e) (inj₂ r) d with ≈⊑ e r d
  ... | viaᴬ r′ d′ e′ = viaᴬ (inj₂ r′) d′ e′
  ≈⊑ (l≈ h) (n , r) d with ≈⊑ (h n) r d
  ... | viaᴬ r′ d′ e′ = viaᴬ (n , r′) d′ e′
  ≈⊑ (o≈ h) (inj₁ (inj₁ _)) _ = viaᴬ (inj₁ (inj₁ tt)) tt (≈ᴮ-refl _)
  ≈⊑ (o≈ h) (inj₁ (inj₂ r)) d = viaᴬ (inj₁ (inj₂ r)) d (≈ᴮ-refl _)
  ≈⊑ (o≈ {k} h) (inj₂ (x , r)) (a , d) with ≈⊑ (h x (A⊆B k x a)) r d
  ... | viaᴬ r′ d′ e′ = viaᴬ (inj₂ (x , r′)) (a , d′) e′
  ≈⊑ (b≈ l l′ e u v) (inj₁ (inj₁ _)) _ = viaᴬ (inj₁ (inj₁ tt)) tt e
  ≈⊑ (b≈ l l′ e u v) (inj₁ (inj₂ r)) d with ≈⊑ e r d
  ... | viaᴬ r′ d′ e′ = viaᴬ (inj₁ (inj₂ r′)) d′ e′
  ≈⊑ (b≈ l l′ e u v) (inj₂ (x , r)) (a , d) with u x a
  ... | y , ay , t , q with ≈⊑ q r d
  ...   | viaᴬ r′ d′ e′ = viaᴬ (inj₂ (y , r′)) (ay , d′) e′

  ≺ᴬ-respʳ : ∀ {a b b′} → a ≺ᴬ b → b ≈ᴮ b′ → a ≺ᴬ b′
  ≺ᴬ-respʳ p e = ≺⊑ p (≈⊑ e)

  -- 路径的传递性: 严格小蕴含前序
  comp : ∀ b (r : Pre b) → Adm b r → (s : Pre (at b r)) → Adm (at b r) s → Σ (Pre b) λ t → Adm b t × at b t ≡ at (at b r) s
  comp (suc k)    (inj₁ _)        _ s ds = inj₂ s , ds , refl
  comp (suc k)    (inj₂ r)        d s ds with comp k r d s ds
  ... | t , dt , e = inj₂ t , dt , e
  comp (lim f)    (n , r)         d s ds with comp (f n) r d s ds
  ... | t , dt , e = (n , t) , dt , e
  comp (limᴼ k g) (inj₁ (inj₁ _)) _ s ds = inj₁ (inj₂ s) , ds , refl
  comp (limᴼ k g) (inj₁ (inj₂ r)) d s ds with comp k r d s ds
  ... | t , dt , e = inj₁ (inj₂ t) , dt , e
  comp (limᴼ k g) (inj₂ (x , r)) (a , d) s ds with comp (g x) r d s ds
  ... | t , dt , e = inj₂ (x , t) , (a , dt) , e

  ≈≡′ : ∀ {a b c} → a ≈ᴮ b → c ≡ b → a ≈ᴮ c
  ≈≡′ e refl = e

  ≡→≈′ : ∀ {a b} → a ≡ b → a ≈ᴮ b
  ≡→≈′ {a} refl = ≈ᴮ-refl a

  ≺→⊑ : ∀ {a b} → a ≺ᴬ b → a ⊑ᴬ b
  ≺→⊑ {a} {b} (viaᴬ q dq e) r d with ≈⊑ e r d
  ... | viaᴬ s ds e′ with comp b q dq s ds
  ...   | t , dt , et = viaᴬ t dt (≈≡′ e′ et)

  Tri : Lv → Lv → Set
  Tri a b = a ≺ᴬ b ⊎ b ≺ᴬ a ⊎ a ≈ᴮ b

  shL : ∀ {a a′ b} → a ≈ᴮ a′ → Tri a′ b → Tri a b
  shL e (injᵃ r) = injᵃ (≺ᴬ-respˡ e r)
  shL e (injᵇ r) = injᵇ (≺ᴬ-respʳ r (≈ᴮ-sym e))
  shL e (injᶜ r) = injᶜ (≈ᴮ-trans e r)

  shR : ∀ {a b b′} → b ≈ᴮ b′ → Tri a b′ → Tri a b
  shR e (injᵃ r) = injᵃ (≺ᴬ-respʳ r (≈ᴮ-sym e))
  shR e (injᵇ r) = injᵇ (≺ᴬ-respˡ e r)
  shR e (injᶜ r) = injᶜ (≈ᴮ-trans r (≈ᴮ-sym e))

  WFᴬ : Lv → Set
  WFᴬ zero       = ⊤
  WFᴬ (suc k)    = WFᴬ k
  WFᴬ (lim f)    = (∀ n → f n ⊑ᴬ f (suc n)) × (∀ n → WFᴬ (f n))
  WFᴬ (limᴼ k g) = (∀ x y → A k x → A k y → Σ (Ordᴸ k) λ z → A k z × g x ⊑ᴬ g z × g y ⊑ᴬ g z)
                 × (Σ (Ordᴸ k) λ x₀ → A k x₀ × k ≺ᴬ g x₀ × k ⊑ᴬ g x₀)
                 × (∀ x → A k x → WFᴬ (g x))

  stepsᴬ : ∀ {f : ℕ → Lv} → (∀ n → f n ⊑ᴬ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑ᴬ f m
  stepsᴬ s zero    = s _
  stepsᴬ s (suc p) = ⊑ᴬ-trans (stepsᴬ s p) (s _)

  branchᴬ : ∀ {k g} → (Σ (Ordᴸ k) λ x₀ → A k x₀ × k ≺ᴬ g x₀ × k ⊑ᴬ g x₀) → (p : Pre (limᴼ k g)) → Adm (limᴼ k g) p →
            Σ (Ordᴸ k) λ x → A k x × at (limᴼ k g) p ≺ᴬ g x
  branchᴬ (x₀ , ax , h , _) (inj₁ (inj₁ _)) _ = x₀ , ax , h
  branchᴬ (x₀ , ax , _ , h) (inj₁ (inj₂ r)) d = x₀ , ax , h r d
  branchᴬ _ (inj₂ (x , r)) (ax , d) = x , ax , viaᴬ r d (≈ᴮ-refl _)

  <-decᴬ : ∀ c → WFᴬ c → (p q : Pre c) → Adm c p → Adm c q → Tri (at c p) (at c q)
  <-decᴬ (suc k) w (inj₁ _) (inj₁ _) _ _ = injᶜ (≈ᴮ-refl k)
  <-decᴬ (suc k) w (inj₁ _) (inj₂ q) _ dq = injᵇ (viaᴬ q dq (≈ᴮ-refl _))
  <-decᴬ (suc k) w (inj₂ p) (inj₁ _) dp _ = injᵃ (viaᴬ p dp (≈ᴮ-refl _))
  <-decᴬ (suc k) w (inj₂ p) (inj₂ q) dp dq = <-decᴬ k w p q dp dq
  <-decᴬ (lim f) (s , w) (n , p) (m , q) dp dq with <ᴺ-dec n m
  ... | injᵃ n<m with stepsᴬ s n<m p dp
  ...   | viaᴬ p′ d′ e = shL e (<-decᴬ (f m) (w m) p′ q d′ dq)
  <-decᴬ (lim f) (s , w) (n , p) (m , q) dp dq | injᵇ m<n with stepsᴬ s m<n q dq
  ...   | viaᴬ q′ d′ e = shR e (<-decᴬ (f n) (w n) p q′ dp d′)
  <-decᴬ (lim f) (s , w) (n , p) (_ , q) dp dq | injᶜ refl = <-decᴬ (f n) (w n) p q dp dq
  <-decᴬ (limᴼ k g) (dir , par , w) p q dp dq with branchᴬ par p dp | branchᴬ par q dq
  ... | x , ax , viaᴬ p′ dp′ e | y , ay , viaᴬ q′ dq′ e′ with dir x y ax ay
  ...   | z , az , gx , gy with gx p′ dp′ | gy q′ dq′
  ...     | viaᴬ p″ dp″ f | viaᴬ q″ dq″ f′ =
    shL (≈ᴮ-trans e f) (shR (≈ᴮ-trans e′ f′) (<-decᴬ (g z) (w z az) p″ q″ dp″ dq″))
```

## §2 字面的路径给 $\Omega$ 的路径

```agda
  path→Ω : ∀ i r → Adm i r → at i r ≺ᴬ toLv (Ω i)
  path→Ω (suc k)    (inj₁ _)        _ = viaᴬ (inj₁ (inj₁ tt)) tt (≈ᴮ-refl k)
  path→Ω (suc k)    (inj₂ r)        d = viaᴬ (inj₁ (inj₂ r)) d (≈ᴮ-refl _)
  path→Ω (lim f)    (n , r)         d with path→Ω (f n) r d
  ... | viaᴬ q dq e = viaᴬ (n , q) dq e
  path→Ω (limᴼ k g) (inj₁ (inj₁ _)) _ = viaᴬ (inj₁ (inj₁ tt)) tt (≈ᴮ-refl k)
  path→Ω (limᴼ k g) (inj₁ (inj₂ r)) d = viaᴬ (inj₁ (inj₂ r)) d (≈ᴮ-refl _)
  path→Ω (limᴼ k g) (inj₂ (x , r)) (a , d) with path→Ω (g x) r d
  ... | viaᴬ q dq e = viaᴬ (inj₂ (x , q)) (a , dq) e
```

## §3 层号的好性

`Cx a`: 可比较 (`WFᴬ`), 分支尊重 $\approx$ (`Rp`), 分支对比较单调 (`Mn`). 三者都只说 `Lv` 上的路径, 不提折叠. `Rp` 与 `Mn` 的前提是**层号上的**关系 `toLv z ≈ᴮ toLv z′`, `toLv z ⊑ᴬ toLv z′`, 这就是不进循环的原因: 地板上的相等与序都读层号, 不读观测.

`Cx` 对路径封闭 (`cx-at`, 要低层自己可比较), 对 $\approx$ 封闭 (`cx≈`).

```agda
  Rp : Lv → Set
  Rp zero       = ⊤
  Rp (suc k)    = Rp k
  Rp (lim f)    = ∀ n → Rp (f n)
  Rp (limᴼ k g) = (∀ x → Bs k x → Rp (g x)) × (∀ z z′ → Bs k z → Bs k z′ → toLv z ≈ᴮ toLv z′ → g z ≈ᴮ g z′)

  Mn : Lv → Set
  Mn zero       = ⊤
  Mn (suc k)    = Mn k
  Mn (lim f)    = ∀ n → Mn (f n)
  Mn (limᴼ k g) = (∀ x → A k x → Mn (g x)) × (∀ z z′ → A k z → A k z′ → toLv z ⊑ᴬ toLv z′ → g z ⊑ᴬ g z′)

  Cx : Lv → Set
  Cx a = WFᴬ a × Rp a × Mn a

  wf-at : (∀ j → Lw j → Cx j) → ∀ a → Lo a → WFᴬ a → ∀ r → Adm a r → WFᴬ (at a r)
  wf-at lw (suc k)    l w (inj₁ _) _ = w
  wf-at lw (suc k)    l w (inj₂ r) d = wf-at lw k l w r d
  wf-at lw (lim f)    l w (n , r)  d = wf-at lw (f n) (l n) (proj₂ w n) r d
  wf-at lw (limᴼ k g) l w (inj₁ (inj₁ _)) _ = proj₁ (lw k (proj₁ l))
  wf-at lw (limᴼ k g) l w (inj₁ (inj₂ r)) d = wf-at lw k (low-lo k (proj₁ l)) (proj₁ (lw k (proj₁ l))) r d
  wf-at lw (limᴼ k g) l w (inj₂ (x , r)) (a , d) = wf-at lw (g x) (proj₂ l x a) (proj₂ (proj₂ w) x a) r d

  rp-at : (∀ j → Lw j → Cx j) → ∀ a → Lo a → Rp a → ∀ r → Adm a r → Rp (at a r)
  rp-at lw (suc k)    l w (inj₁ _) _ = w
  rp-at lw (suc k)    l w (inj₂ r) d = rp-at lw k l w r d
  rp-at lw (lim f)    l w (n , r)  d = rp-at lw (f n) (l n) (w n) r d
  rp-at lw (limᴼ k g) l w (inj₁ (inj₁ _)) _ = proj₁ (proj₂ (lw k (proj₁ l)))
  rp-at lw (limᴼ k g) l w (inj₁ (inj₂ r)) d = rp-at lw k (low-lo k (proj₁ l)) (proj₁ (proj₂ (lw k (proj₁ l)))) r d
  rp-at lw (limᴼ k g) l w (inj₂ (x , r)) (a , d) = rp-at lw (g x) (proj₂ l x a) (proj₁ w x (A⊆B k x a)) r d

  mn-at : (∀ j → Lw j → Cx j) → ∀ a → Lo a → Mn a → ∀ r → Adm a r → Mn (at a r)
  mn-at lw (suc k)    l w (inj₁ _) _ = w
  mn-at lw (suc k)    l w (inj₂ r) d = mn-at lw k l w r d
  mn-at lw (lim f)    l w (n , r)  d = mn-at lw (f n) (l n) (w n) r d
  mn-at lw (limᴼ k g) l w (inj₁ (inj₁ _)) _ = proj₂ (proj₂ (lw k (proj₁ l)))
  mn-at lw (limᴼ k g) l w (inj₁ (inj₂ r)) d = mn-at lw k (low-lo k (proj₁ l)) (proj₂ (proj₂ (lw k (proj₁ l)))) r d
  mn-at lw (limᴼ k g) l w (inj₂ (x , r)) (a , d) = mn-at lw (g x) (proj₂ l x a) (proj₁ w x a) r d

  cx-at : (∀ j → Lw j → Cx j) → ∀ a → Lo a → Cx a → ∀ r → Adm a r → Cx (at a r)
  cx-at lw a l (w , rp , mn) r d = wf-at lw a l w r d , rp-at lw a l rp r d , mn-at lw a l mn r d

  ⊑≈ : ∀ {a a′ b b′} → a ≈ᴮ a′ → b′ ≈ᴮ b → a′ ⊑ᴬ b′ → a ⊑ᴬ b
  ⊑≈ e e′ σ = ⊑ᴬ-trans (≈⊑ e) (⊑ᴬ-trans σ (≈⊑ e′))

  wf≈ : ∀ {a b} → a ≈ᴮ b → WFᴬ b → WFᴬ a
  wf≈ z≈ w = tt
  wf≈ (s≈ e) w = wf≈ e w
  wf≈ (l≈ h) (s , w) =
    (λ n → ⊑≈ (h n) (≈ᴮ-sym (h (suc n))) (s n)) , (λ n → wf≈ (h n) (w n))
  wf≈ (o≈ {k} h) (dir , (x₀ , ax , p , q) , w) =
    (λ x y ax ay → let z , az , gx , gy = dir x y ax ay
                   in z , az , ⊑≈ (h x (A⊆B k x ax)) (≈ᴮ-sym (h z (A⊆B k z az))) gx ,
                               ⊑≈ (h y (A⊆B k y ay)) (≈ᴮ-sym (h z (A⊆B k z az))) gy) ,
    (x₀ , ax , ≺ᴬ-respʳ p (≈ᴮ-sym (h x₀ (A⊆B k x₀ ax))) , ⊑ᴬ-trans q (≈⊑ (≈ᴮ-sym (h x₀ (A⊆B k x₀ ax))))) ,
    (λ x a → wf≈ (h x (A⊆B k x a)) (w x a))
  wf≈ {limᴼ k g} {limᴼ k′ g′} (b≈ l l′ e u v) (dir , (x₀ , ax , p , q) , w) = dir′ , par′ , her′
    where
    dir′ : ∀ x y → A k x → A k y → Σ (Ordᴸ k) λ z → A k z × g x ⊑ᴬ g z × g y ⊑ᴬ g z
    dir′ x y ax ay with u x ax | u y ay
    ... | x₁ , ax₁ , _ , qx | y₁ , ay₁ , _ , qy with dir x₁ y₁ ax₁ ay₁
    ...   | z₁ , az₁ , gx , gy with v z₁ az₁
    ...     | z , az , _ , qz = z , az , ⊑≈ qx (≈ᴮ-sym qz) gx , ⊑≈ qy (≈ᴮ-sym qz) gy
    par′ : Σ (Ordᴸ k) λ x → A k x × k ≺ᴬ g x × k ⊑ᴬ g x
    par′ with v x₀ ax
    ... | x , a , _ , qx = x , a , ≺ᴬ-respˡ e (≺ᴬ-respʳ p (≈ᴮ-sym qx)) , ⊑≈ e (≈ᴮ-sym qx) q
    her′ : ∀ x → A k x → WFᴬ (g x)
    her′ x a with u x a
    ... | y , ay , _ , qy = wf≈ qy (w y ay)

  rp≈ : ∀ {a b} → a ≈ᴮ b → Rp b → Rp a
  rp≈ z≈ w = tt
  rp≈ (s≈ e) w = rp≈ e w
  rp≈ (l≈ h) w = λ n → rp≈ (h n) (w n)
  rp≈ (o≈ h) (b , r) =
    (λ x d → rp≈ (h x d) (b x d)) ,
    (λ z z′ d d′ e → ≈ᴮ-trans (h z d) (≈ᴮ-trans (r z z′ d d′ e) (≈ᴮ-sym (h z′ d′))))
  rp≈ {limᴼ k g} {limᴼ k′ g′} (b≈ l l′ e u v) (b , r) = br , rs
    where
    br : ∀ x → Bs k x → Rp (g x)
    br x d with u x (d l)
    ... | y , ay , _ , qy = rp≈ qy (b y (A⊆B k′ y ay))
    rs : ∀ z z′ → Bs k z → Bs k z′ → toLv z ≈ᴮ toLv z′ → g z ≈ᴮ g z′
    rs z z′ d d′ t with u z (d l) | u z′ (d′ l)
    ... | y , ay , ty , qy | y′ , ay′ , ty′ , qy′ =
      ≈ᴮ-trans qy (≈ᴮ-trans (r y y′ (A⊆B k′ y ay) (A⊆B k′ y′ ay′) (≈ᴮ-trans (≈ᴮ-sym ty) (≈ᴮ-trans t ty′))) (≈ᴮ-sym qy′))

  mn≈ : ∀ {a b} → a ≈ᴮ b → Mn b → Mn a
  mn≈ z≈ w = tt
  mn≈ (s≈ e) w = mn≈ e w
  mn≈ (l≈ h) w = λ n → mn≈ (h n) (w n)
  mn≈ (o≈ {k} h) (b , r) =
    (λ x d → mn≈ (h x (A⊆B k x d)) (b x d)) ,
    (λ z z′ d d′ e → ⊑≈ (h z (A⊆B k z d)) (≈ᴮ-sym (h z′ (A⊆B k z′ d′))) (r z z′ d d′ e))
  mn≈ {limᴼ k g} {limᴼ k′ g′} (b≈ l l′ e u v) (b , r) = br , rs
    where
    br : ∀ x → A k x → Mn (g x)
    br x d with u x d
    ... | y , ay , _ , qy = mn≈ qy (b y ay)
    rs : ∀ z z′ → A k z → A k z′ → toLv z ⊑ᴬ toLv z′ → g z ⊑ᴬ g z′
    rs z z′ d d′ t with u z d | u z′ d′
    ... | y , ay , ty , qy | y′ , ay′ , ty′ , qy′ =
      ⊑≈ qy (≈ᴮ-sym qy′) (r y y′ ay ay′ (⊑≈ (≈ᴮ-sym ty) ty′ t))

  cx≈ : ∀ {a b} → a ≈ᴮ b → Cx b → Cx a
  cx≈ e (w , r , m) = wf≈ e w , rp≈ e r , mn≈ e m

  lo≈ : ∀ {a b} → a ≈ᴮ b → Lo b → Lo a
  lo≈ z≈ w = tt
  lo≈ (s≈ e) w = lo≈ e w
  lo≈ (l≈ h) w = λ n → lo≈ (h n) (w n)
  lo≈ (o≈ {k} h) (lk , lg) = lk , (λ x a → lo≈ (h x (A⊆B k x a)) (lg x a))
  lo≈ {limᴼ k g} {limᴼ k′ g′} (b≈ l l′ e u v) (lk , lg) = l , br
    where
    br : ∀ x → A k x → Lo (g x)
    br x a with u x a
    ... | y , ay , _ , qy = lo≈ qy (lg y ay)

  -- $\Omega$ 的层号尊重 $\approx$. `BL` 给 `suc` 的参数层低
  Ωlv : (∀ {j j′} → Lw j → j ≈ᴮ j′ → ∀ z → A j z → Σ (Ordᴸ j′) λ z′ → A j′ z′ × toLv z ≈ᴮ toLv z′) →
        ∀ {a b} → BL a → BL b → a ≈ᴮ b → toLv (Ω a) ≈ᴮ toLv (Ω b)
  Ωlv atr b b′ z≈ = s≈ z≈
  Ωlv atr {suc a} {suc c} bl bl′ (s≈ e) = b≈ l l′ e u v
    where
    l  = bl (inj₁ tt) tt
    l′ = bl′ (inj₁ tt) tt
    u : ∀ x → A a x → Σ (Ordᴸ c) λ x′ → A c x′ × toLv x ≈ᴮ toLv x′ × toLv x ≈ᴮ toLv x′
    u x ax with atr l e x ax
    ... | y , ay , t = y , ay , t , t
    v : ∀ x′ → A c x′ → Σ (Ordᴸ a) λ x → A a x × toLv x ≈ᴮ toLv x′ × toLv x ≈ᴮ toLv x′
    v x ax with atr l′ (≈ᴮ-sym e) x ax
    ... | y , ay , t = y , ay , ≈ᴮ-sym t , ≈ᴮ-sym t
  Ωlv atr bl bl′ (l≈ h) = l≈ (λ n → Ωlv atr (bl-lim n bl) (bl-lim n bl′) (h n))
  Ωlv atr bl bl′ (o≈ {k} h) =
    o≈ (λ x d → let a = d (bl-par bl) in Ωlv atr (bl-o bl a) (bl-o bl′ a) (h x d))
  Ωlv atr {limᴼ k g} {limᴼ k′ g′} bl bl′ (b≈ l l′ e u v) = b≈ l l′ e u′ v′
    where
    u′ : ∀ x → A k x → Σ (Ordᴸ k′) λ x′ → A k′ x′ × toLv x ≈ᴮ toLv x′ × toLv (Ω (g x)) ≈ᴮ toLv (Ω (g′ x′))
    u′ x a with u x a
    ... | y , ay , t , q = y , ay , t , Ωlv atr (bl-o bl a) (bl-o bl′ ay) q
    v′ : ∀ x′ → A k′ x′ → Σ (Ordᴸ k) λ x → A k x × toLv x ≈ᴮ toLv x′ × toLv (Ω (g x)) ≈ᴮ toLv (Ω (g′ x′))
    v′ x a with v x a
    ... | y , ay , t , q = y , ay , t , Ωlv atr (bl-o bl ay) (bl-o bl′ a) q

  tw-Ω : (∀ j x → A j x → Tw j x) → ∀ j → BL j → Tw j (Ω j)
  tw-Ω tw zero    b = tt
  tw-Ω tw (suc k) b = tt , (λ z az → tw k z az)
  tw-Ω tw (lim f) b = λ n → tw-Ω tw (f n) (bl-lim n b)
  tw-Ω tw (limᴼ k g) b = tt , (λ x a → a , tw-Ω tw (g x) (bl-o b a))
```

## §4 阶段

`Stage`: 低层对 $\approx$ 封闭 (`low≈`), 地板跨 $\approx$ 的层封闭 (`tr-A`, 这是**搬运只在地板上**的形状: `tr` 本身是总函数, 规格只对地板元), 低层自己好 (`low-cx`), 地板元的树可容许 (`twA`), 其余与 [LevelKBase](LevelKBase.lagda.md) 同. 没有 `low-≈`: 两个 $\approx$ 而不字面相同的层可以同时低.

```agda
record Stage : Set₁ where
  field fl : Fl
  open Leaf fl
  field
    low≈   : ∀ {a b} → Lw a → a ≈ᴮ b → Lw b
    tr-A   : ∀ {j j′} → Lw j → j ≈ᴮ j′ → ∀ z → A j z → A j′ (tr j j′ z) × toLv z ≈ᴮ toLv (tr j j′ z)
    low-cx : ∀ j → Lw j → Cx j
    ΩA     : ∀ j → Lw j → A j (Ω j)
    pΩ     : ∀ j → Lw j → j ≺ᴬ toLv (Ω j)
    cmpA   : ∀ j x y → A j x → A j y → Tri (toLv x) (toLv y)
    cxA    : ∀ j x → A j x → Cx (toLv x)
    twA    : ∀ j x → A j x → Tw j x

  A-tr : ∀ {j j′} → Lw j → j ≈ᴮ j′ → ∀ z → A j z → Σ (Ordᴸ j′) λ z′ → A j′ z′ × toLv z ≈ᴮ toLv z′
  A-tr {j} {j′} l e z a = tr j j′ z , proj₁ (tr-A l e z a) , proj₂ (tr-A l e z a)
```

## §5 加一层地板

`Ext F F′`: `F′` 只多了不在 `Lw` 里的层. `≈↓` 对 `Lo` 成立, 这里要 `F` 上低层对 $\approx$ 封闭 (`lwc`): 否则 `b≈` 另一侧的参数层看不见. 地板元的层号是 `Lo` (`loA`).

```agda
record Ext (F F′ : Fl) : Set where
  private
    module F  = Fl F
    module F′ = Fl F′
  field
    low⊂ : ∀ {j} → F.Lw j → F′.Lw j
    A⊂   : ∀ {j x} → F.A j x → F′.A j x
    A⊃   : ∀ {j x} → F.Lw j → F′.A j x → F.A j x

module Move (F F′ : Fl) (X : Ext F F′)
            (lwc : ∀ {a b} → Fl.Lw F a → Leaf._≈ᴮ_ F a b → Fl.Lw F b)
            (loA : ∀ {j x} → Fl.A F j x → Fl.Lo F (toLv x)) where
  open Ext X
  module L  = Leaf F
  module L′ = Leaf F′
  open L using (Lo; Bs; Lw; A; BL; lo-toLv; lo-at; low-lo; lw→bl)

  B′⊂B : ∀ {j x} → L′.Bs j x → Bs j x
  B′⊂B b l = A⊃ l (b (low⊂ l))

  B⊂B′ : ∀ {j x} → Lw j → Bs j x → L′.Bs j x
  B⊂B′ l b _ = A⊂ (b l)

  ≈↑ : ∀ {a b} → a L.≈ᴮ b → a L′.≈ᴮ b
  ≈↑ L.z≈ = L′.z≈
  ≈↑ (L.s≈ e) = L′.s≈ (≈↑ e)
  ≈↑ (L.l≈ h) = L′.l≈ (λ n → ≈↑ (h n))
  ≈↑ (L.o≈ h) = L′.o≈ (λ x b → ≈↑ (h x (B′⊂B b)))
  ≈↑ {limᴼ k g} {limᴼ k′ g′} (L.b≈ l l′ e u v) = L′.b≈ (low⊂ l) (low⊂ l′) (≈↑ e) u′ v′
    where
    u′ : ∀ x → F′ .Fl.A k x → Σ (Ordᴸ k′) λ x′ → F′ .Fl.A k′ x′ × toLv x L′.≈ᴮ toLv x′ × g x L′.≈ᴮ g′ x′
    u′ x a with u x (A⊃ l a)
    ... | y , ay , t , q = y , A⊂ ay , ≈↑ t , ≈↑ q
    v′ : ∀ x′ → F′ .Fl.A k′ x′ → Σ (Ordᴸ k) λ x → F′ .Fl.A k x × toLv x L′.≈ᴮ toLv x′ × g x L′.≈ᴮ g′ x′
    v′ x a with v x (A⊃ l′ a)
    ... | y , ay , t , q = y , A⊂ ay , ≈↑ t , ≈↑ q

  ≈↓ : ∀ {a b} → Lo a → a L′.≈ᴮ b → a L.≈ᴮ b
  ≈↓ l L′.z≈ = L.z≈
  ≈↓ l (L′.s≈ e) = L.s≈ (≈↓ l e)
  ≈↓ l (L′.l≈ h) = L.l≈ (λ n → ≈↓ (l n) (h n))
  ≈↓ (lk , lg) (L′.o≈ h) = L.o≈ (λ x b → ≈↓ (lg x (b lk)) (h x (B⊂B′ lk b)))
  ≈↓ {limᴼ k g} {limᴼ k′ g′} (lk , lg) (L′.b≈ _ _ e u v) = L.b≈ lk lk′ e′ u′ v′
    where
    e′ : k L.≈ᴮ k′
    e′ = ≈↓ (low-lo k lk) e
    lk′ : Lw k′
    lk′ = lwc lk e′
    u′ : ∀ x → A k x → Σ (Ordᴸ k′) λ x′ → A k′ x′ × toLv x L.≈ᴮ toLv x′ × g x L.≈ᴮ g′ x′
    u′ x a with u x (A⊂ a)
    ... | y , ay , t , q = y , A⊃ lk′ ay , ≈↓ (loA a) t , ≈↓ (lg x a) q
    v′ : ∀ x′ → A k′ x′ → Σ (Ordᴸ k) λ x → A k x × toLv x L.≈ᴮ toLv x′ × g x L.≈ᴮ g′ x′
    v′ x a with v x (A⊂ a)
    ... | y , ay , t , q = y , A⊃ lk ay , ≈↓ (loA (A⊃ lk ay)) t , ≈↓ (lg y (A⊃ lk ay)) q

  adm↑ : ∀ c r → L.Adm c r → L′.Adm c r
  adm↑ (suc k)    (inj₁ _)        d = tt
  adm↑ (suc k)    (inj₂ r)        d = adm↑ k r d
  adm↑ (lim f)    (n , r)         d = adm↑ (f n) r d
  adm↑ (limᴼ k g) (inj₁ (inj₁ _)) d = tt
  adm↑ (limᴼ k g) (inj₁ (inj₂ r)) d = adm↑ k r d
  adm↑ (limᴼ k g) (inj₂ (x , r)) (a , d) = A⊂ a , adm↑ (g x) r d

  adm↓ : ∀ c → Lo c → ∀ r → L′.Adm c r → L.Adm c r
  adm↓ (suc k)    l (inj₁ _)        d = tt
  adm↓ (suc k)    l (inj₂ r)        d = adm↓ k l r d
  adm↓ (lim f)    l (n , r)         d = adm↓ (f n) (l n) r d
  adm↓ (limᴼ k g) l (inj₁ (inj₁ _)) d = tt
  adm↓ (limᴼ k g) l (inj₁ (inj₂ r)) d = adm↓ k (low-lo k (proj₁ l)) r d
  adm↓ (limᴼ k g) l (inj₂ (x , r)) (a , d) =
    let ax = A⊃ (proj₁ l) a in ax , adm↓ (g x) (proj₂ l x ax) r d

  ≺↑ : ∀ {a b} → a L.≺ᴬ b → a L′.≺ᴬ b
  ≺↑ {b = b} (L.viaᴬ r d e) = L′.viaᴬ r (adm↑ b r d) (≈↑ e)

  Tri↑ : ∀ {a b} → L.Tri a b → L′.Tri a b
  Tri↑ (injᵃ p) = injᵃ (≺↑ p)
  Tri↑ (injᵇ p) = injᵇ (≺↑ p)
  Tri↑ (injᶜ e) = injᶜ (≈↑ e)

  ⊑↑ : ∀ {a b} → Lo a → a L.⊑ᴬ b → a L′.⊑ᴬ b
  ⊑↑ {a} l σ r d = ≺↑ (σ r (adm↓ a l r d))

  ≺↓ : ∀ {a b} → Lo b → a L′.≺ᴬ b → a L.≺ᴬ b
  ≺↓ {b = b} l (L′.viaᴬ r d e) =
    let d′ = adm↓ b l r d in
    L.viaᴬ r d′ (L.≈ᴮ-sym (≈↓ (lo-at b l r d′) (L′.≈ᴮ-sym e)))

  ⊑↓ : ∀ {a b} → Lo b → a L′.⊑ᴬ b → a L.⊑ᴬ b
  ⊑↓ {a} l σ r d = ≺↓ l (σ r (adm↑ a r d))

  wf↑ : ∀ a → Lo a → L.WFᴬ a → L′.WFᴬ a
  wf↑ zero       l w = tt
  wf↑ (suc k)    l w = wf↑ k l w
  wf↑ (lim f)    l (s , w) = (λ n → ⊑↑ (l n) (s n)) , (λ n → wf↑ (f n) (l n) (w n))
  wf↑ (limᴼ k g) (lk , lg) (dir , (x₀ , ax , p , q) , w) =
    (λ x y ax ay → let ax′ = A⊃ lk ax ; ay′ = A⊃ lk ay
                       z , az , gx , gy = dir x y ax′ ay′
                   in z , A⊂ az , ⊑↑ (lg x ax′) gx , ⊑↑ (lg y ay′) gy) ,
    (x₀ , A⊂ ax , ≺↑ p , ⊑↑ (low-lo k lk) q) ,
    (λ x a → let a′ = A⊃ lk a in wf↑ (g x) (lg x a′) (w x a′))

  rp↑ : ∀ a → Lo a → L.Rp a → L′.Rp a
  rp↑ zero       l w = tt
  rp↑ (suc k)    l w = rp↑ k l w
  rp↑ (lim f)    l w = λ n → rp↑ (f n) (l n) (w n)
  rp↑ (limᴼ k g) (lk , lg) (b , r) =
    (λ x d → rp↑ (g x) (lg x (B′⊂B d lk)) (b x (B′⊂B d))) ,
    (λ z z′ d d′ e → ≈↑ (r z z′ (B′⊂B d) (B′⊂B d′) (≈↓ (loA (B′⊂B d lk)) e)))

  mn↑ : ∀ a → Lo a → L.Mn a → L′.Mn a
  mn↑ zero       l w = tt
  mn↑ (suc k)    l w = mn↑ k l w
  mn↑ (lim f)    l w = λ n → mn↑ (f n) (l n) (w n)
  mn↑ (limᴼ k g) (lk , lg) (b , r) =
    (λ x d → let d′ = A⊃ lk d in mn↑ (g x) (lg x d′) (b x d′)) ,
    (λ z z′ d d′ e → let a = A⊃ lk d ; a′ = A⊃ lk d′ in
       ⊑↑ (lg z a) (r z z′ a a′ (⊑↓ (loA a′) e)))

  Cx↑ : ∀ a → Lo a → L.Cx a → L′.Cx a
  Cx↑ a l (w , r , m) = wf↑ a l w , rp↑ a l r , mn↑ a l m

  lo↑ : ∀ a → Lo a → L′.Lo a
  lo↑ zero       l = tt
  lo↑ (suc k)    l = lo↑ k l
  lo↑ (lim f)    l = λ n → lo↑ (f n) (l n)
  lo↑ (limᴼ k g) (lk , lg) = low⊂ lk , (λ x a → lo↑ (g x) (lg x (A⊃ lk a)))

  tw↑ : ∀ a → BL a → (x : Ordᴸ a) → L.Tw a x → L′.Tw a x
  tw↑ a b Tree.zero    t = tt
  tw↑ a b (Tree.suc x) t = tw↑ a b x t
  tw↑ a b (Tree.lim h) t = λ n → tw↑ a b (h n) (t n)
  tw↑ a b (limᵢ r f) (dr , tf) = adm↑ a r dr , (λ z az → tw↑ a b (f (intoL a r z)) (tf z (A⊃ (b r dr) az)))
  tw↑ (suc k)    b (up d x) t = tw↑ k (L.bl-suc b) x t
  tw↑ (lim f)    b (up n x) t = tw↑ (f n) (L.bl-lim n b) x t
  tw↑ (limᴼ k g) b (up d x) (a , t) = A⊂ a , tw↑ (g d) (L.bl-o b a) x t
```
