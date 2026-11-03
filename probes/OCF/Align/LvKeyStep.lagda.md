# 参数层 $\ge1$ 的分支: 比较是局部于世界的 (任务 4)

> 不含记号. 结论写在 [LvKey](LvKey.lagda.md). `Sys`: 一层 "层号系统" 的接口, 只要比较 `tri`. `Step`: 下一层, 分支的定义域是上一层的**好层号** `GL` (层号 + `WF` + 自反). 这一步只写层号一侧, 没有树.
>
> **编译过的定理.** `Ωnext`, `WF-Ωnext`, `self-Ωnext`: 对任何 `Sys`, 下一个基数作层号, $\sup_{x}x$ ($x$ 取好层号). `S₀` 是 [LvKeyBase](LvKeyBase.lagda.md) 的实例, 所以 $\Omega_2$ (`Step S₀`) 与 $\Omega_3$ (`Step (Step S₀)`) 都是这同一个定义的实例.
>
> **编译过的否定.** `no-↑`: [LvKeyBase](LvKeyBase.lagda.md) 的 `⊑` 的转移对一切表成立; 这个形式下 $\Omega+3\sqsubseteq\Omega\cdot2$ 是**假**的. 所以分支 $x\mapsto x$ 的单调不能照搬: `Step` 把比较改成局部于世界 (`Pre`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKeyStep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; zero; suc)
import OCF.Align.LvKeyBase as B
```

## §1 接口

`Pre`: 在世界 $w$ 里 $a$ 模 `≈` 是 $b$ 的字面前驱. **没有对一切世界的转移**: 路径的可容许性只在 $w$ 里.

```agda
record Pre {L W : Set} (_≈_ _<_ : L → L → Set) (Adm : W → ∀ {a c} → _<_ a c → Set) (w : W) (a b : L) : Set where
  constructor pre
  field
    {rep} : L
    eqv   : a ≈ rep
    pth   : _<_ rep b
    adm   : Adm w pth
open Pre public

data Cmp {L W : Set} (_≈_ _<_ : L → L → Set) (Adm : W → ∀ {a c} → _<_ a c → Set) (w : W) (a b : L) : Set where
  clt : Pre _≈_ _<_ Adm w a b → Cmp _≈_ _<_ Adm w a b
  cgt : Pre _≈_ _<_ Adm w b a → Cmp _≈_ _<_ Adm w a b
  ceq : a ≈ b → Cmp _≈_ _<_ Adm w a b

record Sys : Set₁ where
  infix 4 _≈_ _<_
  field
    L     : Set
    _≈_   : L → L → Set
    ≈-sym : ∀ {a b} → a ≈ b → b ≈ a
    ≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
    _<_   : L → L → Set
    W     : Set
    Ok    : W → Set
    Adm   : W → ∀ {a c} → a < c → Set
    WF    : L → Set
    tri   : ∀ {c} → WF c → c ≈ c → ∀ {a b} (p : a < c) (q : b < c) (w : W) → Ok w → Adm w p → Adm w q → Cmp _≈_ _<_ Adm w a b
    resp  : ∀ {a b k} (w : W) → a ≈ b → (r : k < a) → Adm w r → Pre _≈_ _<_ Adm w k b
    comp  : ∀ {k a b} (w : W) → k ≈ k → (r : k < a) → (s : a < b) → Adm w r → Adm w s → Pre _≈_ _<_ Adm w k b
```

## §2 下一层

`GL`: 好层号, 自带证书. 分支的定义域是 `GL`, 所以 "对一切分支" 只量词化好输入: 证书不是对原始树全称 (那是 `no-all-branch`, `no-Ω₂`), 而是**分支的类型就是好的**, 就像 `Ordᴵ` 的 `lim` 自带步进. 表的项: 节点与好层号作界. 这一层没有 `fst`: 第一支的优待只在树上才要 (判断).

```agda
module Next (S : Sys) where
  open Sys S renaming (L to L₀; _≈_ to _≈₀_; _<_ to _<₀_; W to W₀; Ok to Ok₀; Adm to Adm₀; WF to WF₀;
                       ≈-sym to ≈₀-sym; ≈-trans to ≈₀-trans; tri to tri₀; resp to resp₀; comp to comp₀)

  Pre₀ = Pre _≈₀_ _<₀_ Adm₀
  Cmp₀ = Cmp _≈₀_ _<₀_ Adm₀

  record GL : Set where
    constructor gl
    field
      ⌞_⌟  : L₀
      cert : WF₀ ⌞_⌟
      slf  : ⌞_⌟ ≈₀ ⌞_⌟
  open GL public

  data Lv : Set where
    emb : L₀ → Lv
    suc : Lv → Lv
    lim : (ℕ → Lv) → Lv
    lc  : (GL → Lv) → Lv

  infix 4 _≈′_ _<′_
  data _≈′_ : Lv → Lv → Set where
    e≈ : ∀ {a b} → a ≈₀ b → emb a ≈′ emb b
    s≈ : ∀ {a b} → a ≈′ b → suc a ≈′ suc b
    l≈ : ∀ {f g} → (∀ n → f n ≈′ g n) → lim f ≈′ lim g
    o≈ : ∀ {g g′} → (∀ x y → ⌞ x ⌟ ≈₀ ⌞ y ⌟ → g x ≈′ g′ y) → lc g ≈′ lc g′

  ≈′-sym : ∀ {a b} → a ≈′ b → b ≈′ a
  ≈′-sym (e≈ e) = e≈ (≈₀-sym e)
  ≈′-sym (s≈ e) = s≈ (≈′-sym e)
  ≈′-sym (l≈ h) = l≈ (λ n → ≈′-sym (h n))
  ≈′-sym (o≈ h) = o≈ (λ x y d → ≈′-sym (h y x (≈₀-sym d)))

  ≈′-trans : ∀ {a b c} → a ≈′ b → b ≈′ c → a ≈′ c
  ≈′-trans (e≈ e) (e≈ e′) = e≈ (≈₀-trans e e′)
  ≈′-trans (s≈ e) (s≈ e′) = s≈ (≈′-trans e e′)
  ≈′-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈′-trans (h n) (h′ n))
  ≈′-trans (o≈ h) (o≈ h′) = o≈ (λ x y d → ≈′-trans (h x x (slf x)) (h′ x y d))

  data _<′_ : Lv → Lv → Set where
    emb  : ∀ {k x} → k <₀ x → emb k <′ emb x
    zero : ∀ {a} → a <′ suc a
    suc  : ∀ {a b} → a <′ b → a <′ suc b
    lim  : ∀ {a f} n → a <′ f n → a <′ lim f
    bra  : ∀ {a g} x → a <′ g x → a <′ lc g

  infixl 5 _▸_,_
  data Ents : Set where
    ∅      : GL → Ents
    _▸_,_  : Ents → Lv → GL → Ents

  at : Ents → Lv → GL → Set
  at (∅ d)       y ℓ = ℓ ≡ d
  at (E ▸ κ , X) y ℓ = ((y ≈′ κ) × (ℓ ≡ X)) ⊎ (((y ≈′ κ) → ⊥) × at E y ℓ)

  at-resp : ∀ {E y y′ ℓ} → y ≈′ y′ → at E y ℓ → at E y′ ℓ
  at-resp {∅ d} e a = a
  at-resp {E ▸ κ , X} e (inj₁ (d , r)) = inj₁ (≈′-trans (≈′-sym e) d , r)
  at-resp {E ▸ κ , X} e (inj₂ (n , a)) = inj₂ ((λ d → n (≈′-trans e d)) , at-resp {E} e a)

  at-uq : ∀ {E y y′ ℓ ℓ′} → y ≈′ y′ → at E y ℓ → at E y′ ℓ′ → ℓ ≡ ℓ′
  at-uq {∅ d} e refl refl = refl
  at-uq {E ▸ κ , X} e (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
  at-uq {E ▸ κ , X} e (inj₁ (d , _)) (inj₂ (n , _)) = ⊥-elim (n (≈′-trans (≈′-sym e) d))
  at-uq {E ▸ κ , X} e (inj₂ (n , _)) (inj₁ (d , _)) = ⊥-elim (n (≈′-trans e d))
  at-uq {E ▸ κ , X} e (inj₂ (_ , a)) (inj₂ (_ , b)) = at-uq {E} e a b

  W′ : Set
  W′ = W₀ × Ents

  Ok′ : W′ → Set
  Ok′ w = Ok₀ (proj₁ w)

  Bel : W′ → Lv → GL → Set
  Bel w y x = Σ GL λ ℓ → at (proj₂ w) y ℓ × Pre₀ (proj₁ w) ⌞ x ⌟ ⌞ ℓ ⌟

  Adm′ : W′ → ∀ {a c} → a <′ c → Set
  Adm′ w (emb r)   = Adm₀ (proj₁ w) r
  Adm′ w zero      = ⊤
  Adm′ w (suc r)   = Adm′ w r
  Adm′ w (lim n r) = Adm′ w r
  Adm′ w (bra {g = g} x r) = Bel w (lc g) x × Adm′ w r

  Pre′ = Pre _≈′_ _<′_ Adm′
  Cmp′ = Cmp _≈′_ _<′_ Adm′

  -- 局部的单调: 只在一个世界里, 只对字面相比的两个分支
  _⊑[_]_ : Lv → W′ → Lv → Set
  a ⊑[ w ] b = ∀ {k} (r : k <′ a) → Adm′ w r → Pre′ w k b

  WF′ : Lv → Set
  WF′ (emb x) = WF₀ x × (x ≈₀ x)
  WF′ (suc k) = WF′ k
  WF′ (lim f) = (∀ n w → Ok′ w → f n ⊑[ w ] f (suc n)) × (∀ n → WF′ (f n))
  WF′ (lc g)  = (∀ {x y} w → Ok′ w → Pre₀ (proj₁ w) ⌞ x ⌟ ⌞ y ⌟ → g x ⊑[ w ] g y) × (∀ x → WF′ (g x))
```

**搬运与三歧.** 与 [LvKeyBase](LvKeyBase.lagda.md) 同一个骨架. `lc` 处: 两个分支的证据给出同一个界 $\ell$ (`at-uq`), 在 $\ell$ 里用上一层的 `tri` 比较, 这就是 "比较是上一层的定理" 的全部内容.

```agda
  resp′ : ∀ {a b k} (w : W′) → a ≈′ b → (r : k <′ a) → Adm′ w r → Pre′ w k b
  resp′ w (e≈ e) (emb r) ad with resp₀ (proj₁ w) e r ad
  ... | pre d p t = pre (e≈ d) (emb p) t
  resp′ w (s≈ e) zero ad = pre e zero tt
  resp′ w (s≈ e) (suc r) ad with resp′ w e r ad
  ... | pre d p t = pre d (suc p) t
  resp′ w (l≈ h) (lim n r) ad with resp′ w (h n) r ad
  ... | pre d p t = pre d (lim n p) t
  resp′ {lc g} {lc g′} w (o≈ h) (bra x r) (u , ad) with resp′ w (h x x (slf x)) r ad
  ... | pre d p t = pre d (bra x p) ((proj₁ u , at-resp {proj₂ w} (o≈ h) (proj₁ (proj₂ u)) , proj₂ (proj₂ u)) , t)

  shL : ∀ {w a a′ b} → a ≈′ a′ → Cmp′ w a′ b → Cmp′ w a b
  shL e (clt (pre d s t)) = clt (pre (≈′-trans e d) s t)
  shL {w} e (cgt (pre d s t)) with resp′ w (≈′-sym e) s t
  ... | pre d′ s′ t′ = cgt (pre (≈′-trans d d′) s′ t′)
  shL e (ceq d) = ceq (≈′-trans e d)

  shR : ∀ {w a b b′} → b ≈′ b′ → Cmp′ w a b′ → Cmp′ w a b
  shR e (cgt (pre d s t)) = cgt (pre (≈′-trans e d) s t)
  shR {w} e (clt (pre d s t)) with resp′ w (≈′-sym e) s t
  ... | pre d′ s′ t′ = clt (pre (≈′-trans d d′) s′ t′)
  shR e (ceq d) = ceq (≈′-trans d (≈′-sym e))

  -- 上一层的比较, 模两个代表元
  cmpG : ∀ {w₀ x y r₁ r₂} → x ≈₀ r₁ → y ≈₀ r₂ → Cmp₀ w₀ r₁ r₂ → Cmp₀ w₀ x y
  cmpG {w₀} ex ey (clt (pre d s t)) with resp₀ w₀ (≈₀-sym ey) s t
  ... | pre d′ s′ t′ = clt (pre (≈₀-trans ex (≈₀-trans d d′)) s′ t′)
  cmpG {w₀} ex ey (cgt (pre d s t)) with resp₀ w₀ (≈₀-sym ex) s t
  ... | pre d′ s′ t′ = cgt (pre (≈₀-trans ey (≈₀-trans d d′)) s′ t′)
  cmpG ex ey (ceq d) = ceq (≈₀-trans ex (≈₀-trans d (≈₀-sym ey)))

  stepsᴸ : ∀ {f : ℕ → Lv} w → Ok′ w → (∀ n w → Ok′ w → f n ⊑[ w ] f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑[ w ] f m
  stepsᴸ w ok s zero r a = s _ w ok r a
  stepsᴸ {f} w ok s (suc q) r a with stepsᴸ w ok s q r a
  ... | pre d p t with s _ w ok p t
  ...   | pre d′ p′ t′ = pre (≈′-trans d d′) p′ t′

  tri′ : ∀ {c} → WF′ c → c ≈′ c → ∀ {a b} (p : a <′ c) (q : b <′ c) (w : W′) → Ok′ w → Adm′ w p → Adm′ w q → Cmp′ w a b
  tri′ {emb x} (cx , _) (e≈ e) (emb p) (emb q) w ok ap aq with tri₀ cx e p q (proj₁ w) ok ap aq
  ... | clt (pre d s t) = clt (pre (e≈ d) (emb s) t)
  ... | cgt (pre d s t) = cgt (pre (e≈ d) (emb s) t)
  ... | ceq d = ceq (e≈ d)
  tri′ {suc k} wf (s≈ e) zero zero w ok _ _ = ceq e
  tri′ {suc k} wf (s≈ e) zero (suc q) w ok _ aq with resp′ w e q aq
  ... | pre d s t = cgt (pre d s t)
  tri′ {suc k} wf (s≈ e) (suc p) zero w ok ap _ with resp′ w e p ap
  ... | pre d s t = clt (pre d s t)
  tri′ {suc k} wf (s≈ e) (suc p) (suc q) w ok ap aq = tri′ wf e p q w ok ap aq
  tri′ {lim f} (st , wf) (l≈ e) (lim n p) (lim m q) w ok ap aq with <ᴺ-dec n m
  ... | injᵃ n<m with stepsᴸ w ok st n<m p ap
  ...   | pre d p′ t = shL d (tri′ (wf m) (e m) p′ q w ok t aq)
  tri′ {lim f} (st , wf) (l≈ e) (lim n p) (lim m q) w ok ap aq | injᵇ m<n with stepsᴸ w ok st m<n q aq
  ...   | pre d q′ t = shR d (tri′ (wf n) (e n) p q′ w ok ap t)
  tri′ {lim f} (st , wf) (l≈ e) (lim n p) (lim _ q) w ok ap aq | injᶜ refl = tri′ (wf n) (e n) p q w ok ap aq
  tri′ {lc g} (dir , wf) (o≈ e) (bra x p) (bra y q) w ok ((ℓ , a , lx) , ap) ((ℓ′ , a′ , ly) , aq) with at-uq {proj₂ w} (o≈ e) a a′
  ... | refl with cmpG {x = ⌞ x ⌟} {y = ⌞ y ⌟} (eqv lx) (eqv ly) (tri₀ (cert ℓ) (slf ℓ) (pth lx) (pth ly) (proj₁ w) ok (adm lx) (adm ly))
  ...   | clt r with dir w ok r p ap
  ...     | pre d p′ t = shL d (tri′ (wf y) (e y y (slf y)) p′ q w ok t aq)
  tri′ {lc g} (dir , wf) (o≈ e) (bra x p) (bra y q) w ok ((ℓ , a , lx) , ap) ((ℓ′ , a′ , ly) , aq) | refl | cgt r with dir w ok r q aq
  ...     | pre d q′ t = shR d (tri′ (wf x) (e x x (slf x)) p q′ w ok ap t)
  tri′ {lc g} (dir , wf) (o≈ e) (bra x p) (bra y q) w ok ((ℓ , a , lx) , ap) ((ℓ′ , a′ , ly) , aq) | refl | ceq d with resp′ w (e x y d) p ap
  ...     | pre d′ p′ t = shL d′ (tri′ (wf y) (e y y (slf y)) p′ q w ok t aq)

  comp′ : ∀ {k a b} (w : W′) → k ≈′ k → (r : k <′ a) → (s : a <′ b) → Adm′ w r → Adm′ w s → Pre′ w k b
  comp′ w (e≈ e) (emb r) (emb s) ar as with comp₀ (proj₁ w) e r s ar as
  ... | pre d p t = pre (e≈ d) (emb p) t
  comp′ w e r zero ar as = pre e (suc r) ar
  comp′ w e r (suc s) ar as with comp′ w e r s ar as
  ... | pre d p t = pre d (suc p) t
  comp′ w e r (lim n s) ar as with comp′ w e r s ar as
  ... | pre d p t = pre d (lim n p) t
  comp′ w e r (bra x s) ar (u , as) with comp′ w e r s ar as
  ... | pre d p t = pre d (bra x p) (u , t)
```

## §3 下一个基数: 一个定义, 对任何 `Sys`

`Ωnext`: $\sup_x x$, $x$ 取好层号. 单调是 "把 $x$ 的路径接到 $y$ 里 $x$ 的路径上面". **接上去要 $y$ 到 $x$ 那一段的可容许性, 它来自比较时的世界**: 这就是转移不能对一切世界成立的原因 (`no-↑`).

```agda
  Ωnext : Lv
  Ωnext = lc (λ x → emb ⌞ x ⌟)

  self-Ωnext : Ωnext ≈′ Ωnext
  self-Ωnext = o≈ (λ x y d → e≈ d)

  WF-Ωnext : WF′ Ωnext
  WF-Ωnext = (λ {x} {y} w ok r → dir {x} {y} w ok r) , (λ x → cert x , slf x)
    where
    dir : ∀ {x y} w → Ok′ w → Pre₀ (proj₁ w) ⌞ x ⌟ ⌞ y ⌟ → emb ⌞ x ⌟ ⊑[ w ] emb ⌞ y ⌟
    dir w ok (pre d s t) (emb r) ad with resp₀ (proj₁ w) d r ad
    ... | pre d₂ r₂ a₂ with comp₀ (proj₁ w) (≈₀-trans (≈₀-sym d₂) d₂) r₂ s a₂ t
    ...   | pre d₃ p t₃ = pre (e≈ (≈₀-trans d₂ d₃)) (emb p) t₃

Step : Sys → Sys
Step S = record
  { L = Lv ; _≈_ = _≈′_ ; ≈-sym = ≈′-sym ; ≈-trans = ≈′-trans ; _<_ = _<′_ ; W = W′ ; Ok = Ok′ ; Adm = Adm′ ; WF = WF′
  ; tri = tri′ ; resp = resp′ ; comp = comp′ }
  where open Next S
```

## §4 实例: 第一层就是 [LvKeyBase](LvKeyBase.lagda.md)

`S₀`: 忘掉对一切表的转移. `S₁`, `S₂`: 迭代. $\Omega_2$, $\Omega_3$ 都是 `Ωnext` 的实例, 不是另写的.

```agda
∘ᴮ : ∀ {k a b} → k B.<ᴸ a → a B.<ᴸ b → k B.<ᴸ b
∘ᴮ r B.zero      = B.suc r
∘ᴮ r (B.suc s)   = B.suc (∘ᴮ r s)
∘ᴮ r (B.lim n s) = B.lim n (∘ᴮ r s)
∘ᴮ r (B.fst s)   = B.fst (∘ᴮ r s)
∘ᴮ r (B.bra η s) = B.bra η (∘ᴮ r s)

adm∘ᴮ : ∀ {E k a b} (r : k B.<ᴸ a) (s : a B.<ᴸ b) → B.Adm E r → B.Adm E s → B.Adm E (∘ᴮ r s)
adm∘ᴮ r B.zero      x _ = x
adm∘ᴮ r (B.suc s)   x y = adm∘ᴮ r s x y
adm∘ᴮ r (B.lim n s) x y = adm∘ᴮ r s x y
adm∘ᴮ r (B.fst s)   x y = adm∘ᴮ r s x y
adm∘ᴮ r (B.bra η s) x (u , y) = u , adm∘ᴮ r s x y

S₀ : Sys
S₀ = record
  { L = B.LI ; _≈_ = B._≈_ ; ≈-sym = B.≈-sym ; ≈-trans = B.≈-trans ; _<_ = B._<ᴸ_ ; W = B.Ents ; Ok = B.OkE ; Adm = B.Adm ; WF = B.WF
  ; tri = λ wf e p q E ok ap aq → tr (B.<-dec wf e p q E ok ap aq) E ap aq
  ; resp = λ E e r a → rs (B.≈-move e r) E a
  ; comp = λ E e r s ar as → pre e (∘ᴮ r s) (adm∘ᴮ {E} r s ar as)
  }
  where
  rs : ∀ {k a A} → k B.≺⟨ A ⟩ a → (E : B.Ents) → A E → Pre B._≈_ B._<ᴸ_ B.Adm E k a
  rs (B.viaᴸ d s t) E x = pre d s (t E x)
  tr : ∀ {a b c} {p : a B.<ᴸ c} {q : b B.<ᴸ c} → B.Tri p q → (E : B.Ents) → B.Adm E p → B.Adm E q → Cmp B._≈_ B._<ᴸ_ B.Adm E a b
  tr (B.tlt v) E ap aq = clt (rs v E ap)
  tr (B.tgt v) E ap aq = cgt (rs v E aq)
  tr (B.teq d) E ap aq = ceq d

S₁ S₂ : Sys
S₁ = Step S₀
S₂ = Step S₁

Ω₂ : Sys.L S₁
Ω₂ = Next.Ωnext S₀

Ω₃ : Sys.L S₂
Ω₃ = Next.Ωnext S₁

Cf₂ : Sys.WF S₁ Ω₂ × Sys._≈_ S₁ Ω₂ Ω₂
Cf₂ = Next.WF-Ωnext S₀ , Next.self-Ωnext S₀

Cf₃ : Sys.WF S₂ Ω₃ × Sys._≈_ S₂ Ω₃ Ω₃
Cf₃ = Next.WF-Ωnext S₁ , Next.self-Ωnext S₁
```

## §5 否定: 对一切表的转移在 $\Omega_2$ 上不成立

$\Omega+2<\Omega+3$ 的路径没有分支证据, 而 $\Omega\cdot2$ 里到 $\Omega+2$ 的路径必须经过 $\eta\ge3$ 的分支. 所以 $\Omega+3\sqsubseteq\Omega\cdot2$ (带对一切表的转移) 是假的, 尽管 $\Omega+3$ 确实小于 $\Omega\cdot2$. **`x ↦ x` 不是 `WF (lcl g)` 那个意义下的单调函数.** `WF` 对 `times` 成立是因为 `L ⊞ η` 的路径搬到 `L ⊞ η′` 不产生新分支.

```agda
natI : ℕ → Ordᴵ
natI zero    = zero
natI (suc n) = suc (natI n)

no-↑ : (B.base B.⊞ natI 3) B.⊑ (B.Ω· 2) → ⊥
no-↑ f with f {k = B.base B.⊞ natI 2} B.zero
... | B.viaᴸ () (B.fst B.zero) t
... | B.viaᴸ d (B.fst (B.suc ())) t
... | B.viaᴸ d (B.bra η p) t = go (proj₁ (t (B.∅ B.one) tt)) p
  where
  go : ∀ {η r} → B.Bel (B.∅ B.one) (B.lcl (B.base B.⊞_)) η → r B.<ᴸ (B.base B.⊞ η) → ⊥
  go (_ , refl , zero) ()
  go (_ , refl , suc ()) p
```

## §6 有限测试: 跨分支的比较

节点 $\Omega_2$ 上两条路径: 分支 $x=\Omega+3$, $y=\Omega\cdot2$, 界 $\ell=\Omega\cdot2+1$. 比较用上一层的 `tri`, 输出的路径带 $\Omega\cdot2$ 那一段的分支证据, 取自 $x$ 在 $\ell$ 里的路径. 这是测试, 不是定理.

```agda
module Test where
  open Next S₀
  open B using (WFΩ; selfΩ; Ω·_; base; _⊞_; s≈; ∅)

  gΩ·2 : GL
  gΩ·2 = gl (Ω· 2) (WFΩ 2) (selfΩ 2)

  gΩ+ : ℕ → GL
  gΩ+ n = gl (base ⊞ natI n) (B.Mono.WF-⊞ base B.b≈ tt (natI n)) (B.self⊞ B.b≈ (natI n))

  gℓ : GL
  gℓ = gl (B.suc (Ω· 2)) (WFΩ 2) (s≈ (selfΩ 2))

  w : W′
  w = ∅ (natI 5) , ∅ gℓ

  ok : Ok′ w
  ok = suc (suc (suc (suc zero)))

  -- x = Ω+3 在 ℓ 里: 经分支 3 的 `zero` 再后继
  p₃ : (base ⊞ natI 3) B.<ᴸ B.suc (Ω· 2)
  p₃ = B.suc (B.bra (natI 4) B.zero)

  a₃ : B.Adm (∅ (natI 5)) p₃
  a₃ = (natI 5 , refl , zero) , tt

  belx : Bel w Ωnext (gΩ+ 3)
  belx = gℓ , refl , pre (B.self⊞ B.b≈ (natI 3)) p₃ a₃

  bely : Bel w Ωnext gΩ·2
  bely = gℓ , refl , pre (selfΩ 2) B.zero tt

  isLt : ∀ {w a b} → Cmp′ w a b → Set
  isLt (clt _) = ⊤
  isLt (cgt _) = ⊥
  isLt (ceq _) = ⊥

  isGt : ∀ {w a b} → Cmp′ w a b → Set
  isGt (clt _) = ⊥
  isGt (cgt _) = ⊤
  isGt (ceq _) = ⊥

  -- Ω+2 (在 x 里) 与 Ω+1 (在 y 的分支 3 里): 大的是前者
  c₁ : isGt (tri′ WF-Ωnext self-Ωnext (bra (gΩ+ 3) (emb B.zero)) (bra gΩ·2 (emb (B.bra (natI 3) (B.suc B.zero)))) w ok (belx , tt) (bely , ((natI 5 , refl , suc zero) , tt)))
  c₁ = tt

  -- Ω+2 (在 x 里) 与 Ω+4 (在 y 的分支 5 里, 世界要 5 在界内): 小的是前者
  w′ : W′
  w′ = ∅ (natI 7) , ∅ gℓ

  a₃′ : B.Adm (∅ (natI 7)) p₃
  a₃′ = (natI 7 , refl , suc (suc zero)) , tt

  c₂ : isLt (tri′ WF-Ωnext self-Ωnext {a = emb (base ⊞ natI 2)} {b = emb (base ⊞ natI 4)} (bra (gΩ+ 3) (emb B.zero)) (bra gΩ·2 (emb (B.bra (natI 5) B.zero))) w′ (suc (suc (suc (suc (suc (suc zero)))))) ((gℓ , refl , pre (B.self⊞ B.b≈ (natI 3)) p₃ a₃′) , tt) ((gℓ , refl , pre (selfΩ 2) B.zero tt) , ((natI 7 , refl , suc zero) , tt)))
  c₂ = tt
```
