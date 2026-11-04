# 从 `toLevel` 层号到累加层号

> 接 [BTBOFullV3](BTBOFullV3.lagda.md). `V1`: 对 `SV` 的层号 $a$, $a$ 的前驱保序映到 `ordᴰ (bkᴵ a)` 的前驱. 块由 `SV` 给的字面前驱 $c_n$ 判定: $x\prec c_{m+1}$ 时比较 $x$ 与 $c_m$, 这是有界三歧, 不用判定 $x\prec f_m$. 另有把 `Eb` 包成 `PEmb` 的 `PW₁`, `PW₂`, `PW₃`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOFullV1 where

open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (≤⇒≤′; m≤m+n; m≤n+m)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; module Trich; injᵃ; injᵇ; injᶜ)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum; cumsum-mono) renaming (_+_ to _+ᴰ_)
open S using (ordᴰ)
open import OCF.Align.Level hiding (below)
open import OCF.Align.BTBOValDn using (τ; τ-<; via<)
open import OCF.Align.BTBOValNeg using (HS-≺; two-preds)
open import OCF.Align.BTBOFullQ using (<ᴰ-irrefl; clash-lt)
open import OCF.Align.BTBOFullLv using (SV; svz; svs; svl)
open import OCF.Align.BTBOFullEmb using (PEmb)
open import OCF.Align.BTBOFullEb using (lt-add; module Blocks; 𝕆)
open import OCF.Align.BTBOFullV3 using (𝕋₀; bkᴵ; O∘; Fʸ)
```

## §1 反映 $\tau$

```agda
τ-refl< : ∀ {A c} → c <ᴵ τ A → Σ Ordᴰ (λ c₀ → c₀ B.< A × c ≅ᴵ τ c₀)
τ-refl< {B.suc A} zero      = A , B.zero , ≅ᴵ-refl _
τ-refl< {B.suc A} (suc q)   = let c₀ , p , e = τ-refl< {A} q in c₀ , B.suc p , e
τ-refl< {B.lim f m} (lim n q) = let c₀ , p , e = τ-refl< {f n} q in c₀ , B.lim n p , e

τ-refl : ∀ {A c} → c ≺ᴵ τ A → Σ Ordᴰ (λ c₀ → c₀ B.< A × c ≅ᴵ τ c₀)
τ-refl {A} (via e q) = let c₀ , p , e′ = τ-refl< {A} q in c₀ , p , ≅ᴵ-trans e e′

ord-lt : ∀ {A c₀ d₀} → c₀ B.< A → d₀ B.< A → τ c₀ ≺ᴵ τ d₀ → c₀ B.< d₀
ord-lt p q r with B.<-dec p q
... | injᵃ x    = x
... | injᵇ x    = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans r (via< (τ-< x))))
... | injᶜ refl = ⊥-elim (≺ᴵ-irrefl r)

ord-eq : ∀ {A c₀ d₀} → c₀ B.< A → d₀ B.< A → τ c₀ ≅ᴵ τ d₀ → c₀ ≡ d₀
ord-eq p q r with B.<-dec p q
... | injᵃ x = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (via< (τ-< x)) (≅ᴵ-sym r)))
... | injᵇ x = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (via< (τ-< x)) r))
... | injᶜ x = x

≡→≅ᴵ : ∀ {a b : Ordᴵ} → a ≡ b → a ≅ᴵ b
≡→≅ᴵ refl = ≅ᴵ-refl _
```

## §2 包装

```agda
module WO = Blocks 𝕆
module WT = Blocks 𝕋₀

PW₁ : ∀ {A T} → WO.Eb A T → PEmb (τ A) (τ T)
PW₁ {A} e = record { map = m ; bnd = bd ; mono = mn ; coh = ch }
  where
  m : ∀ {c} → c ≺ᴵ τ A → Ordᴵ
  m r = let c₀ , p , _ = τ-refl {A} r in τ (WO.map e p)
  bd : ∀ {c} (r : c ≺ᴵ τ A) → m r ≺ᴵ τ _
  bd r = let c₀ , p , _ = τ-refl {A} r in via< (τ-< (WO.below e p))
  mn : ∀ {c d} (r : c ≺ᴵ τ A) (s : d ≺ᴵ τ A) → c ≺ᴵ d → m r ≺ᴵ m s
  mn r s x with τ-refl {A} r | τ-refl {A} s
  ... | c₀ , p , e₁ | d₀ , q , e₂ = via< (τ-< (WO.mono e p q (ord-lt p q (≺ᴵ-respˡ (≅ᴵ-sym e₁) (≺ᴵ-respʳ x e₂)))))
  ch : ∀ {c d} (r : c ≺ᴵ τ A) (s : d ≺ᴵ τ A) → c ≅ᴵ d → m r ≅ᴵ m s
  ch r s x with τ-refl {A} r | τ-refl {A} s
  ... | c₀ , p , e₁ | d₀ , q , e₂ = ≡→≅ᴵ (cong τ (WO.coh e p q (ord-eq p q (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans x e₂)))))

PW₂ : ∀ {A} {y : Ordᶜ Ordᴵ.zero} (h : HS y) → WT.Eb A y → PEmb (τ A) (toLevel y h)
PW₂ {A} {y} h e = record { map = m ; bnd = bd ; mono = mn ; coh = ch }
  where
  m : ∀ {c} → c ≺ᴵ τ A → Ordᴵ
  m r = let c₀ , p , _ = τ-refl {A} r in toLevel (WT.map e p) (HS-≺ (WT.below e p) h)
  bd : ∀ {c} (r : c ≺ᴵ τ A) → m r ≺ᴵ toLevel y h
  bd r = let c₀ , p , _ = τ-refl {A} r in toLevel-≺ (HS-≺ (WT.below e p) h) h (WT.below e p)
  mn : ∀ {c d} (r : c ≺ᴵ τ A) (s : d ≺ᴵ τ A) → c ≺ᴵ d → m r ≺ᴵ m s
  mn r s x with τ-refl {A} r | τ-refl {A} s
  ... | c₀ , p , e₁ | d₀ , q , e₂ = toLevel-≺ _ _ (WT.mono e p q (ord-lt p q (≺ᴵ-respˡ (≅ᴵ-sym e₁) (≺ᴵ-respʳ x e₂))))
  ch : ∀ {c d} (r : c ≺ᴵ τ A) (s : d ≺ᴵ τ A) → c ≅ᴵ d → m r ≅ᴵ m s
  ch r s x with τ-refl {A} r | τ-refl {A} s
  ... | c₀ , p , e₁ | d₀ , q , e₂ = toLevel-≅ _ _ (WT.coh e p q (ord-eq p q (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans x e₂))))

record Ev (a : Ordᴵ) (T : Ordᴰ) : Set where
  field
    em : ∀ {c} → c ≺ᴵ a → Ordᴰ
    et : ∀ {c} (r : c ≺ᴵ a) → em r B.< T
    en : ∀ {c d} (r : c ≺ᴵ a) (s : d ≺ᴵ a) → c ≺ᴵ d → em r B.< em s
    ec : ∀ {c d} (r : c ≺ᴵ a) (s : d ≺ᴵ a) → c ≅ᴵ d → em r ≡ em s
open Ev

PW₃ : ∀ {a T} → Ev a T → PEmb a (τ T)
PW₃ e = record
  { map = λ r → τ (em e r) ; bnd = λ r → via< (τ-< (et e r))
  ; mono = λ r s x → via< (τ-< (en e r s x)) ; coh = λ r s x → ≡→≅ᴵ (cong τ (ec e r s x)) }
```

## §3 `V1`

```agda
≺⊑ : ∀ {c b a} → c ≺ᴵ b → b ⊑ᴵ a → c ≺ᴵ a
≺⊑ (via e q) k = ≺ᴵ-respˡ e (sim k q)

module Lim {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)}
           (st : ∀ n → Σ Ordᴵ (λ c → c ≺ᴵ f (suc n) × f n ⊑ᴵ c))
           (e : ∀ n → Ev (f n) (O∘ f n)) where

  c : ℕ → Ordᴵ
  c n = proj₁ (st n)
  rc : ∀ n → c n ≺ᴵ f (suc n)
  rc n = proj₁ (proj₂ (st n))
  kc : ∀ n → f n ⊑ᴵ c n
  kc n = proj₂ (proj₂ (st n))
  Σs : ℕ → Ordᴰ
  Σs = cumsum (O∘ f)

  c≺c : ∀ m → c m ≺ᴵ c (suc m)
  c≺c m = ≺⊑ (rc m) (kc (suc m))

  Ξ : ∀ m {x} → x ≺ᴵ c m → Ordᴰ
  Ξ m r = Σs m +ᴰ em (e (suc m)) (≺ᴵ-trans r (rc m))

  En : ∀ n {x} → x ≺ᴵ c n → Ordᴰ
  En zero    r = Ξ 0 r
  En (suc m) r with two-preds r (c≺c m)
  ... | injᵃ y = En m y
  ... | injᵇ _ = Ξ (suc m) r
  ... | injᶜ _ = Ξ (suc m) r

  Ξ-lt : ∀ m {x} (r : x ≺ᴵ c m) → Ξ m r B.< Σs (suc m)
  Ξ-lt m r = B.+-mono (B.suc (et (e (suc m)) _))

  En-lt : ∀ n {x} (r : x ≺ᴵ c n) → En n r B.< Σs (suc n)
  En-lt zero    r = Ξ-lt 0 r
  En-lt (suc m) r with two-preds r (c≺c m)
  ... | injᵃ y = B.<-trans (En-lt m y) (cumsum-mono (O∘ f) Trich.zero)
  ... | injᵇ _ = Ξ-lt (suc m) r
  ... | injᶜ _ = Ξ-lt (suc m) r

  En-mono : ∀ n {x y} (r : x ≺ᴵ c n) (t : y ≺ᴵ c n) → x ≺ᴵ y → En n r B.< En n t
  En-mono zero r t w = B.+-mono (en (e 1) _ _ w)
  En-mono (suc m) r t w with two-preds r (c≺c m) | two-preds t (c≺c m)
  ... | injᵃ r′ | injᵃ t′ = En-mono m r′ t′ w
  ... | injᵃ r′ | injᵇ _  = lt-add (En-lt m r′) _
  ... | injᵃ r′ | injᶜ _  = lt-add (En-lt m r′) _
  ... | injᵇ g  | injᵃ t′ = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans g (≺ᴵ-trans w t′)))
  ... | injᶜ g  | injᵃ t′ = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym g) (≺ᴵ-trans w t′)))
  ... | injᵇ _  | injᵇ _  = B.+-mono (en (e (suc (suc m))) _ _ w)
  ... | injᵇ _  | injᶜ _  = B.+-mono (en (e (suc (suc m))) _ _ w)
  ... | injᶜ _  | injᵇ _  = B.+-mono (en (e (suc (suc m))) _ _ w)
  ... | injᶜ _  | injᶜ _  = B.+-mono (en (e (suc (suc m))) _ _ w)

  En-coh : ∀ n {x y} (r : x ≺ᴵ c n) (t : y ≺ᴵ c n) → x ≅ᴵ y → En n r ≡ En n t
  En-coh zero r t w = cong (Σs 0 +ᴰ_) (ec (e 1) _ _ w)
  En-coh (suc m) r t w with two-preds r (c≺c m) | two-preds t (c≺c m)
  ... | injᵃ r′ | injᵃ t′ = En-coh m r′ t′ w
  ... | injᵃ r′ | injᵇ g  = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respʳ g (≅ᴵ-sym w)) r′))
  ... | injᵃ r′ | injᶜ g  = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym (≅ᴵ-trans w g)) r′))
  ... | injᵇ g  | injᵃ t′ = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respʳ g w) t′))
  ... | injᶜ g  | injᵃ t′ = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-trans (≅ᴵ-sym g) w) t′))
  ... | injᵇ _  | injᵇ _  = cong (Σs (suc m) +ᴰ_) (ec (e (suc (suc m))) _ _ w)
  ... | injᵇ _  | injᶜ _  = cong (Σs (suc m) +ᴰ_) (ec (e (suc (suc m))) _ _ w)
  ... | injᶜ _  | injᵇ _  = cong (Σs (suc m) +ᴰ_) (ec (e (suc (suc m))) _ _ w)
  ... | injᶜ _  | injᶜ _  = cong (Σs (suc m) +ᴰ_) (ec (e (suc (suc m))) _ _ w)

  lift1 : ∀ m {x} → x ≺ᴵ c m → x ≺ᴵ c (suc m)
  lift1 m r = ≺ᴵ-trans r (c≺c m)

  ext1 : ∀ m {x} (r : x ≺ᴵ c m) → En (suc m) (lift1 m r) ≡ En m r
  ext1 m r with two-preds (lift1 m r) (c≺c m)
  ... | injᵃ y = En-coh m y r (≅ᴵ-refl _)
  ... | injᵇ g = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans g r))
  ... | injᶜ g = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym g) r))

  liftS : ∀ {n k x} → n ≤′ k → x ≺ᴵ c n → x ≺ᴵ c k
  liftS ≤′-refl     r = r
  liftS (≤′-step l) r = lift1 _ (liftS l r)

  extS : ∀ {n k x} (l : n ≤′ k) (r : x ≺ᴵ c n) → En k (liftS l r) ≡ En n r
  extS ≤′-refl     r = refl
  extS (≤′-step l) r = trans (ext1 _ (liftS l r)) (extS l r)

  addr : ∀ {x} → x ≺ᴵ lim f s → Σ ℕ (λ n → x ≺ᴵ c n)
  addr (via e′ (lim n q)) = n , ≺⊑ (via e′ q) (kc n)

  emL : ∀ {x} → x ≺ᴵ lim f s → Ordᴰ
  emL r = let n , t = addr r in En n t

  ev : Ev (lim f s) (B.lim Σs (cumsum-mono (O∘ f)))
  ev = record { em = emL ; et = etL ; en = enL ; ec = ecL }
    where
    etL : ∀ {x} (r : x ≺ᴵ lim f s) → emL r B.< B.lim Σs (cumsum-mono (O∘ f))
    etL r = let n , t = addr r in B.lim (suc n) (En-lt n t)
    enL : ∀ {x y} (r : x ≺ᴵ lim f s) (t : y ≺ᴵ lim f s) → x ≺ᴵ y → emL r B.< emL t
    enL r t w with addr r | addr t
    ... | n , r′ | k , t′ = subst₂′ (extS (≤⇒≤′ (m≤m+n n k)) r′) (extS (≤⇒≤′ (m≤n+m k n)) t′)
        (En-mono (n +ᴺ k) (liftS (≤⇒≤′ (m≤m+n n k)) r′) (liftS (≤⇒≤′ (m≤n+m k n)) t′) w)
      where
      subst₂′ : ∀ {a a′ b b′} → a ≡ a′ → b ≡ b′ → a B.< b → a′ B.< b′
      subst₂′ refl refl q = q
    ecL : ∀ {x y} (r : x ≺ᴵ lim f s) (t : y ≺ᴵ lim f s) → x ≅ᴵ y → emL r ≡ emL t
    ecL r t w with addr r | addr t
    ... | n , r′ | k , t′ = trans (sym (extS (≤⇒≤′ (m≤m+n n k)) r′))
        (trans (En-coh (n +ᴺ k) (liftS (≤⇒≤′ (m≤m+n n k)) r′) (liftS (≤⇒≤′ (m≤n+m k n)) t′) w) (extS (≤⇒≤′ (m≤n+m k n)) t′))

V1 : ∀ {a} → SV a → Ev a (ordᴰ (bkᴵ a))
V1 svz = record { em = λ { (via e ()) } ; et = λ { (via e ()) } ; en = λ { (via e ()) } ; ec = λ { (via e ()) } }
V1 {suc a₀} (svs d) = record { em = m ; et = t ; en = n ; ec = c }
  where
  e₀ = V1 d
  m : ∀ {x} → x ≺ᴵ suc a₀ → Ordᴰ
  m (via e zero)    = ordᴰ (bkᴵ a₀)
  m (via e (suc q)) = em e₀ (via e q)
  t : ∀ {x} (r : x ≺ᴵ suc a₀) → m r B.< B.suc (ordᴰ (bkᴵ a₀))
  t (via e zero)    = B.zero
  t (via e (suc q)) = B.suc (et e₀ (via e q))
  n : ∀ {x y} (r : x ≺ᴵ suc a₀) (s : y ≺ᴵ suc a₀) → x ≺ᴵ y → m r B.< m s
  n (via e zero)    (via e′ zero)     w = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym e) (≺ᴵ-respʳ w e′)))
  n (via e zero)    (via e′ (suc q))  w = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respˡ (≅ᴵ-sym e) w) (via e′ q)))
  n (via e (suc q)) (via e′ zero)     w = et e₀ (via e q)
  n (via e (suc q)) (via e′ (suc q′)) w = en e₀ (via e q) (via e′ q′) w
  c : ∀ {x y} (r : x ≺ᴵ suc a₀) (s : y ≺ᴵ suc a₀) → x ≅ᴵ y → m r ≡ m s
  c (via e zero)    (via e′ zero)     w = refl
  c (via e zero)    (via e′ (suc q))  w = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans w e′)) (via (≅ᴵ-refl _) q)))
  c (via e (suc q)) (via e′ zero)     w = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-trans (≅ᴵ-sym e′) (≅ᴵ-trans (≅ᴵ-sym w) e)) (via (≅ᴵ-refl _) q)))
  c (via e (suc q)) (via e′ (suc q′)) w = ec e₀ (via e q) (via e′ q′) w
V1 {lim f s} (svl d st) = Lim.ev st (λ n → V1 (d n))
```
