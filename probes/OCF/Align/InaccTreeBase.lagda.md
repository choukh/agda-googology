# 不可达层的树侧: 裸层号宇宙、外部派发与统一折叠 (底座)

> 底座, 结论写在 [InaccTree](InaccTree.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccTreeBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Ord-Ord; module Trich; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter) public
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
```

## §1 层号宇宙与树族

```agda
data Tree (P : Set) (Br : P → Set) (D : Set) (Dr : D → Set) : Set where
  zero : Tree P Br D Dr
  suc  : Tree P Br D Dr → Tree P Br D Dr
  lim  : (ℕ → Tree P Br D Dr) → Tree P Br D Dr
  limᵢ : (r : P) → (Br r → Tree P Br D Dr) → Tree P Br D Dr
  up   : (d : D) → Dr d → Tree P Br D Dr

data Lv : Set
Pre  : Lv → Set
Low  : (ℓ : Lv) → Pre ℓ → Set
Dn   : Lv → Set
DnT  : (ℓ : Lv) → Dn ℓ → Set
Ordᴸ : Lv → Set

data Lv where
  zero : Lv
  suc  : Lv → Lv
  lim  : (ℕ → Lv) → Lv
  limᴼ : (k : Lv) → (Ordᴸ k → Lv) → Lv

Pre zero       = ⊥
Pre (suc k)    = ⊤ ⊎ Pre k
Pre (lim f)    = Σ ℕ λ n → Pre (f n)
Pre (limᴼ k g) = (⊤ ⊎ Pre k) ⊎ Σ (Ordᴸ k) λ x → Pre (g x)

Low (suc k)    (inj₁ _)            = Ordᴸ k
Low (suc k)    (inj₂ r)            = Low k r
Low (lim f)    (n , r)             = Low (f n) r
Low (limᴼ k g) (inj₁ (inj₁ _))     = Ordᴸ k
Low (limᴼ k g) (inj₁ (inj₂ r))     = Low k r
Low (limᴼ k g) (inj₂ (x , r))      = Low (g x) r

Dn zero       = ⊥
Dn (suc k)    = ⊤
Dn (lim f)    = ℕ
Dn (limᴼ k g) = Ordᴸ k

DnT (suc k)    _ = Ordᴸ k
DnT (lim f)    n = Ordᴸ (f n)
DnT (limᴼ k g) x = Ordᴸ (g x)

Ordᴸ ℓ = Tree (Pre ℓ) (Low ℓ) (Dn ℓ) (DnT ℓ)

at : (ℓ : Lv) → Pre ℓ → Lv
at (suc k)    (inj₁ _)        = k
at (suc k)    (inj₂ r)        = at k r
at (lim f)    (n , r)         = at (f n) r
at (limᴼ k g) (inj₁ (inj₁ _)) = k
at (limᴼ k g) (inj₁ (inj₂ r)) = at k r
at (limᴼ k g) (inj₂ (x , r))  = at (g x) r

down : (ℓ : Lv) → Dn ℓ → Lv
down (suc k)    _ = k
down (lim f)    n = f n
down (limᴼ k g) x = g x

outL : ∀ ℓ r → Low ℓ r → Ordᴸ (at ℓ r)
outL (suc k)    (inj₁ _)        y = y
outL (suc k)    (inj₂ r)        y = outL k r y
outL (lim f)    (n , r)         y = outL (f n) r y
outL (limᴼ k g) (inj₁ (inj₁ _)) y = y
outL (limᴼ k g) (inj₁ (inj₂ r)) y = outL k r y
outL (limᴼ k g) (inj₂ (x , r))  y = outL (g x) r y

intoL : ∀ ℓ r → Ordᴸ (at ℓ r) → Low ℓ r
intoL (suc k)    (inj₁ _)        y = y
intoL (suc k)    (inj₂ r)        y = intoL k r y
intoL (lim f)    (n , r)         y = intoL (f n) r y
intoL (limᴼ k g) (inj₁ (inj₁ _)) y = y
intoL (limᴼ k g) (inj₁ (inj₂ r)) y = intoL k r y
intoL (limᴼ k g) (inj₂ (x , r))  y = intoL (g x) r y

outD : ∀ ℓ d → DnT ℓ d → Ordᴸ (down ℓ d)
outD (suc k)    _ y = y
outD (lim f)    n y = y
outD (limᴼ k g) x y = y

intoD : ∀ ℓ d → Ordᴸ (down ℓ d) → DnT ℓ d
intoD (suc k)    _ y = y
intoD (lim f)    n y = y
intoD (limᴼ k g) x y = y
```

## §2 Ω、层号化、提升与加法

```agda
Ω : (ℓ : Lv) → Ordᴸ ℓ
Ω zero       = suc zero
Ω (suc k)    = limᵢ (inj₁ tt) (up tt)
Ω (lim f)    = lim (λ n → up n (Ω (f n)))
Ω (limᴼ k g) = limᵢ (inj₁ (inj₁ tt)) (λ x → up x (Ω (g x)))

toLv  : ∀ {ℓ} → Ordᴸ ℓ → Lv
toLvD : ∀ ℓ d → DnT ℓ d → Lv

toLv zero         = zero
toLv (suc x)      = suc (toLv x)
toLv (lim f)      = lim (λ n → toLv (f n))
toLv {ℓ} (limᵢ r f) = limᴼ (at ℓ r) (λ y → toLv (f (intoL ℓ r y)))
toLv {ℓ} (up d x) = toLvD ℓ d x

toLvD (suc k)    _ x = toLv x
toLvD (lim f)    n x = toLv x
toLvD (limᴼ k g) y x = toLv x

Sim : Lv → Lv → Set
Sim k ℓ = (r : Pre k) → Σ (Pre ℓ) λ r′ → at ℓ r′ ≡ at k r

σ-id : ∀ ℓ → Sim ℓ ℓ
σ-id ℓ r = r , refl

ι : ∀ ℓ d → Sim (down ℓ d) ℓ
ι (suc k)    _ r = inj₂ r , refl
ι (lim f)    n r = (n , r) , refl
ι (limᴼ k g) x r = inj₂ (x , r) , refl

_∘σ_ : ∀ {a b c} → Sim b c → Sim a b → Sim a c
_∘σ_ {a} {b} {c} τ σ r with σ r
... | r′ , e with τ r′
...   | r″ , e′ = r″ , trans′ e′ e where
  trans′ : ∀ {x y z : Lv} → x ≡ y → y ≡ z → x ≡ z
  trans′ refl q = q

add : ∀ {k ℓ} → Ordᴸ ℓ → Sim k ℓ → Ordᴸ k → Ordᴸ ℓ
add a σ zero    = a
add a σ (suc b) = suc (add a σ b)
add a σ (lim f) = lim (λ n → add a σ (f n))
add {k} {ℓ} a σ (limᵢ r f) = limᵢ (proj₁ (σ r)) (λ y → add a σ (f (intoL k r (back y)))) where
  back : Low ℓ (proj₁ (σ r)) → Ordᴸ (at k r)
  back y = subst Ordᴸ (proj₂ (σ r)) (outL ℓ (proj₁ (σ r)) y)
add {suc k}    a σ (up d x) = add a (σ ∘σ ι (suc k) d) x
add {lim f}    a σ (up d x) = add a (σ ∘σ ι (lim f) d) x
add {limᴼ k g} a σ (up d x) = add a (σ ∘σ ι (limᴼ k g) d) x

infixl 6 _+_
_+_ : ∀ {ℓ} → Ordᴸ ℓ → Ordᴸ ℓ → Ordᴸ ℓ
_+_ {ℓ} a b = add a (σ-id ℓ) b

upL : ∀ ℓ d → Ordᴸ (down ℓ d) → Ordᴸ ℓ
upL ℓ d x = up d (intoD ℓ d x)
```

## §3 外部派发与折叠

派发判决: 节点层 `j` 对目标 `i`. `pen r b` 说 `j` 对应目标的前驱 `r` (穿透), `b` 把目标层的输入搬回节点层; `rise` 说 `i ≼ j` (链). 类型不要求判决为真: **任何**函数 `Oracle` 都让折叠成为总函数, 判决的真实性是外部条件 (层 3).

```agda
data Verdict (j i : Lv) : Set where
  pen  : (r : Pre i) → (Ordᴸ (at i r) → Ordᴸ j) → Verdict j i
  rise : Verdict j i

Oracle : Set
Oracle = (j i : Lv) → Verdict j i

module Fold (D : Oracle) where
  ψ  : ∀ {i k} → Ordᴸ k → Ordᴸ i
  ψ {i} zero      = Ω i
  ψ {i} (suc a)   = lim (iter (ψ {i} a +_) zero)
  ψ {i} (lim f)   = lim (λ n → ψ {i} (f n))
  ψ {i} {k} (limᵢ r f) with D (at k r) i
  ... | pen r′ b = limᵢ r′ (λ y → ψ {i} (f (intoL k r (b (outL i r′ y)))))
  ... | rise     = lim (λ n → ψ {i} (f (intoL k r
                     (iter (λ x → ψ {at k r} (f (intoL k r x))) (Ω (at k r)) n))))
  ψ {i} {suc k}    (up d x) = ψ {i} x
  ψ {i} {lim f}    (up d x) = ψ {i} x
  ψ {i} {limᴼ k g} (up d x) = ψ {i} x

-- 目标不低于树的层: 从不比较, 不用判决 (`Sim k i` 就是全部证据)
ψ↓ : ∀ {i k} → Sim k i → Ordᴸ k → Ordᴸ i
ψ↓ {i} σ zero    = Ω i
ψ↓ {i} σ (suc a) = lim (iter (ψ↓ σ a +_) zero)
ψ↓ {i} σ (lim f) = lim (λ n → ψ↓ σ (f n))
ψ↓ {i} {k} σ (limᵢ r f) = limᵢ (proj₁ (σ r)) (λ y → ψ↓ σ (f (intoL k r (subst Ordᴸ (proj₂ (σ r)) (outL i (proj₁ (σ r)) y)))))
ψ↓ {i} {suc k}    σ (up d x) = ψ↓ (σ ∘σ ι (suc k) d) x
ψ↓ {i} {lim f}    σ (up d x) = ψ↓ (σ ∘σ ι (lim f) d) x
ψ↓ {i} {limᴼ k g} σ (up d x) = ψ↓ (σ ∘σ ι (limᴼ k g) d) x

FGH : Ordᴸ zero → ℕ → ℕ
FGH zero    n = suc n
FGH (suc a) n = iter (FGH a) n n
FGH (lim f) n = FGH (f n) n
```

## §4 跨层互模拟与搬运

`≅` 是**普通**数据类型, 不进归纳-递归块: `limᴼ` 情形带参数层的 `≅` 与两个显式的分支互搬函数 `u`, `v` (Aczel 式), 不要求 `u`, `v` 是 `tr` 的像. 这样 scout 记下的 "`o≅` 要 `tr` 再进互递归块一次" 不发生.

```agda
infix 4 _≅_ _≺_ _⊑_

data _≅_ : Lv → Lv → Set where
  z≅ : zero ≅ zero
  s≅ : ∀ {a b} → a ≅ b → suc a ≅ suc b
  l≅ : ∀ {f g} → (∀ n → f n ≅ g n) → lim f ≅ lim g
  o≅ : ∀ {k k′ g g′} → k ≅ k′ →
       (u : Ordᴸ k → Ordᴸ k′) (v : Ordᴸ k′ → Ordᴸ k) →
       (∀ x → g x ≅ g′ (u x)) → (∀ y → g (v y) ≅ g′ y) → limᴼ k g ≅ limᴼ k′ g′

≅-refl : ∀ a → a ≅ a
≅-refl zero       = z≅
≅-refl (suc a)    = s≅ (≅-refl a)
≅-refl (lim f)    = l≅ (λ n → ≅-refl (f n))
≅-refl (limᴼ k g) = o≅ (≅-refl k) (λ x → x) (λ x → x) (λ x → ≅-refl (g x)) (λ x → ≅-refl (g x))

≅-sym : ∀ {a b} → a ≅ b → b ≅ a
≅-sym z≅     = z≅
≅-sym (s≅ e) = s≅ (≅-sym e)
≅-sym (l≅ h) = l≅ (λ n → ≅-sym (h n))
≅-sym (o≅ e u v a b) = o≅ (≅-sym e) v u (λ y → ≅-sym (b y)) (λ x → ≅-sym (a x))

≅-trans : ∀ {a b c} → a ≅ b → b ≅ c → a ≅ c
≅-trans z≅     z≅      = z≅
≅-trans (s≅ e) (s≅ e′) = s≅ (≅-trans e e′)
≅-trans (l≅ h) (l≅ h′) = l≅ (λ n → ≅-trans (h n) (h′ n))
≅-trans (o≅ e u v a b) (o≅ e′ u′ v′ a′ b′) =
  o≅ (≅-trans e e′) (λ x → u′ (u x)) (λ y → v (v′ y))
     (λ x → ≅-trans (a x) (a′ (u x))) (λ y → ≅-trans (b (v′ y)) (b′ y))

record Restr (j b : Lv) : Set where
  constructor restr
  field
    rep  : Pre b
    eq   : j ≅ at b rep
    back : Ordᴸ (at b rep) → Ordᴸ j
open Restr public

tr   : ∀ {a b} → a ≅ b → Ordᴸ a → Ordᴸ b
tr⁻  : ∀ {a b} → a ≅ b → Ordᴸ b → Ordᴸ a
res  : ∀ {a b} (r : Pre a) → a ≅ b → Restr (at a r) b
res⁻ : ∀ {a b} (r : Pre b) → a ≅ b → Restr (at b r) a

tr e zero    = zero
tr e (suc x) = suc (tr e x)
tr e (lim f) = lim (λ n → tr e (f n))
tr {a} {b} e (limᵢ r f) = limᵢ (rep (res r e)) (λ y → tr e (f (intoL a r (back (res r e) (outL b (rep (res r e)) y)))))
tr (s≅ e) (up _ x) = up tt (tr e x)
tr (l≅ h) (up n x) = up n (tr (h n) x)
tr (o≅ e u v a b) (up x y) = up (u x) (tr (a x) y)

tr⁻ e zero    = zero
tr⁻ e (suc x) = suc (tr⁻ e x)
tr⁻ e (lim f) = lim (λ n → tr⁻ e (f n))
tr⁻ {a} {b} e (limᵢ r f) = limᵢ (rep (res⁻ r e)) (λ y → tr⁻ e (f (intoL b r (back (res⁻ r e) (outL a (rep (res⁻ r e)) y)))))
tr⁻ (s≅ e) (up _ x) = up tt (tr⁻ e x)
tr⁻ (l≅ h) (up n x) = up n (tr⁻ (h n) x)
tr⁻ (o≅ e u v a b) (up y x) = up (v y) (tr⁻ (b y) x)

res (inj₁ _) (s≅ e) = restr (inj₁ tt) e (tr⁻ e)
res (inj₂ r) (s≅ e) = restr (inj₂ (rep (res r e))) (eq (res r e)) (back (res r e))
res (n , r)  (l≅ h) = restr (n , rep (res r (h n))) (eq (res r (h n))) (back (res r (h n)))
res (inj₁ (inj₁ _)) (o≅ e u v a b) = restr (inj₁ (inj₁ tt)) e (tr⁻ e)
res (inj₁ (inj₂ r)) (o≅ e u v a b) = restr (inj₁ (inj₂ (rep (res r e)))) (eq (res r e)) (back (res r e))
res (inj₂ (x , r))  (o≅ e u v a b) = restr (inj₂ (u x , rep (res r (a x)))) (eq (res r (a x))) (back (res r (a x)))

res⁻ (inj₁ _) (s≅ e) = restr (inj₁ tt) (≅-sym e) (tr e)
res⁻ (inj₂ r) (s≅ e) = restr (inj₂ (rep (res⁻ r e))) (eq (res⁻ r e)) (back (res⁻ r e))
res⁻ (n , r)  (l≅ h) = restr (n , rep (res⁻ r (h n))) (eq (res⁻ r (h n))) (back (res⁻ r (h n)))
res⁻ (inj₁ (inj₁ _)) (o≅ e u v a b) = restr (inj₁ (inj₁ tt)) (≅-sym e) (tr e)
res⁻ (inj₁ (inj₂ r)) (o≅ e u v a b) = restr (inj₁ (inj₂ (rep (res⁻ r e)))) (eq (res⁻ r e)) (back (res⁻ r e))
res⁻ (inj₂ (y , r))  (o≅ e u v a b) = restr (inj₂ (v y , rep (res⁻ r (b y)))) (eq (res⁻ r (b y))) (back (res⁻ r (b y)))
```

## §5 序与有界三歧

```agda
record _≺_ (a b : Lv) : Set where
  constructor via
  field
    pth : Pre b
    prf : a ≅ at b pth
open _≺_ public

_⊑_ : Lv → Lv → Set
a ⊑ b = (r : Pre a) → at a r ≺ b

comp : ∀ b (r : Pre b) (s : Pre (at b r)) → Σ (Pre b) λ t → at b t ≡ at (at b r) s
comp (suc k)    (inj₁ _)        s = inj₂ s , refl
comp (suc k)    (inj₂ r)        s = inj₂ (proj₁ (comp k r s)) , proj₂ (comp k r s)
comp (lim f)    (n , r)         s = (n , proj₁ (comp (f n) r s)) , proj₂ (comp (f n) r s)
comp (limᴼ k g) (inj₁ (inj₁ _)) s = inj₁ (inj₂ s) , refl
comp (limᴼ k g) (inj₁ (inj₂ r)) s = inj₁ (inj₂ (proj₁ (comp k r s))) , proj₂ (comp k r s)
comp (limᴼ k g) (inj₂ (x , r))  s = inj₂ (x , proj₁ (comp (g x) r s)) , proj₂ (comp (g x) r s)

≅-subst : ∀ {a b c} → a ≅ b → b ≡ c → a ≅ c
≅-subst e refl = e

≺-respˡ : ∀ {a a′ b} → a′ ≅ a → a ≺ b → a′ ≺ b
≺-respˡ e (via r e′) = via r (≅-trans e e′)

<-≅ : ∀ {a a′} (r : Pre a) → a ≅ a′ → at a r ≺ a′
<-≅ r e = via (rep (res r e)) (eq (res r e))

≺-respʳ : ∀ {a b b′} → a ≺ b → b ≅ b′ → a ≺ b′
≺-respʳ (via r e) e′ = ≺-respˡ e (<-≅ r e′)

≺-trans : ∀ {a b c} → a ≺ b → b ≺ c → a ≺ c
≺-trans {c = c} (via r e) (via s e′) with <-≅ r e′
... | via t e″ with comp c s t
...   | u , q = via u (≅-trans e (≅-subst e″ (sym q)))

self≺ : ∀ a (r : Pre a) → at a r ≺ a
self≺ a r = via r (≅-refl _)

⊑-trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans σ τ r with σ r
... | via s e = ≺-respˡ e (τ s)
```

**可比性证书.** `WF c` 是 "以 `c` 为界可以比较" 的证据: `lim` 要步进, `limᴼ` 要分支族有向 (`Dir`) 且参数层被某分支支配. 这就是 scout 的 `Lv⁺` 证据, 但放在层号之外, 所以 `toLv` 保持总函数. 下面的 `<-dec` 是 Level `<ᴵ-dec` 的推广, `limᴼ` 情形只用公共上界 `g z`, 反而比 `lim` 情形简单.

```agda
Trichʹ : Lv → Lv → Set
Trichʹ a b = a ≺ b ⊎ b ≺ a ⊎ a ≅ b

WF : Lv → Set
WF zero       = ⊤
WF (suc k)    = WF k
WF (lim f)    = (∀ n → f n ⊑ f (suc n)) × (∀ n → WF (f n))
WF (limᴼ k g) = (∀ x y → Σ (Ordᴸ k) λ z → g x ⊑ g z × g y ⊑ g z)
              × (Σ (Ordᴸ k) λ x₀ → k ≺ g x₀)
              × (∀ x → WF (g x))

shiftL : ∀ {a a′ b} → a ≅ a′ → Trichʹ a′ b → Trichʹ a b
shiftL e (injᵃ r) = injᵃ (≺-respˡ e r)
shiftL e (injᵇ r) = injᵇ (≺-respʳ r (≅-sym e))
shiftL e (injᶜ r) = injᶜ (≅-trans e r)

shiftR : ∀ {a b b′} → b ≅ b′ → Trichʹ a b′ → Trichʹ a b
shiftR e (injᵃ r) = injᵃ (≺-respʳ r (≅-sym e))
shiftR e (injᵇ r) = injᵇ (≺-respˡ e r)
shiftR e (injᶜ r) = injᶜ (≅-trans r (≅-sym e))

steps : ∀ {f : ℕ → Lv} → (∀ n → f n ⊑ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑ f m
steps s zero    = s _
steps s (suc p) = ⊑-trans (steps s p) (s _)

-- 把 limᴼ 层的任一前驱归到某个分支里
intoBranch : ∀ {k g} → (Σ (Ordᴸ k) λ x₀ → k ≺ g x₀) → (p : Pre (limᴼ k g)) →
             Σ (Ordᴸ k) λ x → at (limᴼ k g) p ≺ g x
intoBranch (x₀ , h) (inj₁ (inj₁ _)) = x₀ , h
intoBranch {k} (x₀ , h) (inj₁ (inj₂ r)) = x₀ , ≺-trans (self≺ k r) h
intoBranch {g = g} d (inj₂ (x , r)) = x , self≺ (g x) r

<-dec : ∀ c → WF c → (p q : Pre c) → Trichʹ (at c p) (at c q)
<-dec (suc k) w (inj₁ _) (inj₁ _) = injᶜ (≅-refl k)
<-dec (suc k) w (inj₁ _) (inj₂ q) = injᵇ (self≺ k q)
<-dec (suc k) w (inj₂ p) (inj₁ _) = injᵃ (self≺ k p)
<-dec (suc k) w (inj₂ p) (inj₂ q) = <-dec k w p q
<-dec (lim f) (s , w) (n , p) (m , q) with <ᴺ-dec n m
... | injᵃ n<m with steps s n<m p
...   | via p′ e = shiftL e (<-dec (f m) (w m) p′ q)
<-dec (lim f) (s , w) (n , p) (m , q) | injᵇ m<n with steps s m<n q
...   | via q′ e = shiftR e (<-dec (f n) (w n) p q′)
<-dec (lim f) (s , w) (n , p) (_ , q) | injᶜ refl = <-dec (f n) (w n) p q
<-dec (limᴼ k g) (dir , par , w) p q with intoBranch par p | intoBranch par q
... | x , via p′ e | y , via q′ e′ with dir x y
...   | z , gx , gy with gx p′ | gy q′
...     | via p″ f | via q″ f′ =
  shiftL (≅-trans e f) (shiftR (≅-trans e′ f′) (<-dec (g z) (w z) p″ q″))

fromTrich : ∀ {j i} → Trichʹ j i → Verdict j i
fromTrich (injᵃ (via r e)) = pen r (tr⁻ e)
fromTrich (injᵇ _)         = rise
fromTrich (injᶜ _)         = rise
```

## §6 闭项用的启发式判决 (脚手架, 无主张)

`cast` 是不带证据的结构搬运 (结构不合处落到 `zero`), `same` 是有限采样的结构比较, `ver` 是由它们拼出的总函数 `Oracle`. **它们不声称正确**: 壁垒定理说任何对 `Ordᴸ 0` 全体正确的总判决推出 WLPO (见 InaccTree). 它们只是让闭项能计算的脚手架, 对访问到的点是否正确由验收节 (与 EBO 比较) 检验.

```agda
cast  : ∀ a b → Ordᴸ a → Ordᴸ b
castP : ∀ a b (r : Pre a) → Maybe (Σ (Pre b) λ r′ → Ordᴸ (at b r′) → Ordᴸ (at a r))

cast a b zero    = zero
cast a b (suc x) = suc (cast a b x)
cast a b (lim f) = lim (λ n → cast a b (f n))
cast a b (limᵢ r f) with castP a b r
... | just (r′ , bk) = limᵢ r′ (λ y → cast a b (f (intoL a r (bk (outL b r′ y)))))
... | nothing        = zero
cast (suc a)    (suc b)      (up _ x) = up tt (cast a b x)
cast (lim f)    (lim h)      (up n x) = up n (cast (f n) (h n) x)
cast (limᴼ k g) (limᴼ k′ g′) (up x y) = up (cast k k′ x) (cast (g x) (g′ (cast k k′ x)) y)
cast _          _            (up _ _) = zero

castP (suc a) (suc b) (inj₁ _) = just (inj₁ tt , cast b a)
castP (suc a) (suc b) (inj₂ r) with castP a b r
... | just (r′ , bk) = just (inj₂ r′ , bk)
... | nothing        = nothing
castP (lim f) (lim h) (n , r) with castP (f n) (h n) r
... | just (r′ , bk) = just ((n , r′) , bk)
... | nothing        = nothing
castP (limᴼ k g) (limᴼ k′ g′) (inj₁ (inj₁ _)) = just (inj₁ (inj₁ tt) , cast k′ k)
castP (limᴼ k g) (limᴼ k′ g′) (inj₁ (inj₂ r)) with castP k k′ r
... | just (r′ , bk) = just (inj₁ (inj₂ r′) , bk)
... | nothing        = nothing
castP (limᴼ k g) (limᴼ k′ g′) (inj₂ (x , r)) with castP (g x) (g′ (cast k k′ x)) r
... | just (r′ , bk) = just (inj₂ (cast k k′ x , r′) , bk)
... | nothing        = nothing
castP _ _ _ = nothing

same : Lv → Lv → Bool
same zero       zero         = true
same (suc a)    (suc b)      = same a b
same (lim f)    (lim h)      = same (f 0) (h 0) ∧ same (f 1) (h 1) ∧ same (f 3) (h 3)
same (limᴼ k g) (limᴼ k′ g′) = same k k′ ∧ same (g zero) (g′ zero) ∧ same (g (suc zero)) (g′ (suc zero))
same _          _            = false

reify : ∀ {k} → Lv → Ordᴸ k
reify zero       = zero
reify (suc a)    = suc (reify a)
reify (lim f)    = lim (λ n → reify (f n))
reify (limᴼ _ _) = zero

ver     : Oracle
search  : ℕ → ∀ j (h : ℕ → Lv) → Verdict j (lim h)

ver j zero = rise
ver j (suc i) with same j i
... | true  = pen (inj₁ tt) (cast i j)
... | false with ver j i
...   | pen r b = pen (inj₂ r) b
...   | rise    = rise
ver j (lim h) = search 16 j h
ver j (limᴼ k g) with same j k
... | true  = pen (inj₁ (inj₁ tt)) (cast k j)
... | false with ver j k
...   | pen r b = pen (inj₁ (inj₂ r)) b
...   | rise with ver j (g (suc (reify j)))
...     | pen r b = pen (inj₂ (suc (reify j) , r)) b
...     | rise    = rise

search zero    j h = rise
search (suc m) j h = go (ver j (h m)) where
  go : Verdict j (h m) → Verdict j (lim h)
  go (pen r b) = pen (m , r) b
  go rise      = search m j h
```
