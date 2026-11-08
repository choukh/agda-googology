# 严格分支边界把前驱嵌入拼成实际累计嵌入

复用 BTBOFullV1 的边界选择证明，但目标逐字为新 Run.complete。
不将旧有重叠的源限列直接分块；先在同一源边界 c(n+1) 内比较，
使同一前驱在不同分支中被统一选择。目标分支只需要各自有界嵌入
及其有界相容，不要求裸层号的全局比较。这里不改最终运行器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailEmbedding where
open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (≤⇒≤′; m≤m+n; m≤n+m)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Align.TotalValueBuildIf
open import OCF.Align.TotalValueBuildEmbedding using (shift-predecessor)
import OCF.Free.TotalOrbitRun as R
open BoundedEmbedding renaming (map to em; bound to et; ordered to en; coherent to ec)
infixl 6 _+ᴿ_
_+ᴿ_ = R.add

≺⊑ : ∀ {c b a} → c ≺ᴵ b → b ⊑ᴵ a → c ≺ᴵ a
≺⊑ (via e q) k = ≺ᴵ-respˡ e (sim k q)
keep-left : ∀ {x a} → x ≺ᴵ a → ∀ b → x ≺ᴵ R.add a b
keep-left r b = ≺⊑ r (R.prefix _ b)
sum-step : ∀ g n {x} → x ≺ᴵ R.sum g n → x ≺ᴵ R.sum g (suc n)
sum-step g n r = keep-left r (g (suc n))
into-lim : ∀ {g} n {x} → x ≺ᴵ R.sum g n → x ≺ᴵ R.complete g
into-lim n (via e q) = via e (lim n q)

two-preds : ∀ {a b c} → a ≺ᴵ c → b ≺ᴵ c → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
two-preds (via e q) (via e′ q′) with <ᴵ-dec q q′
... | injᵃ r = injᵃ (≺ᴵ-respˡ e (≺ᴵ-respʳ r (≅ᴵ-sym e′)))
... | injᵇ r = injᵇ (≺ᴵ-respˡ e′ (≺ᴵ-respʳ r (≅ᴵ-sym e)))
... | injᶜ r = injᶜ (≅ᴵ-trans e (≅ᴵ-trans r (≅ᴵ-sym e′)))

module Assemble {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)}
  (g : ℕ → Ordᴵ)
  (st : ∀ n → Σ Ordᴵ (λ c → c ≺ᴵ f (suc n) × f n ⊑ᴵ c))
  (e : ∀ n → BoundedEmbedding (f n) (g n)) where
  c : ℕ → Ordᴵ
  c n = proj₁ (st n)
  rc : ∀ n → c n ≺ᴵ f (suc n)
  rc n = proj₁ (proj₂ (st n))
  kc : ∀ n → f n ⊑ᴵ c n
  kc n = proj₂ (proj₂ (st n))
  Σs : ℕ → Ordᴵ
  Σs = R.sum g

  c≺c : ∀ m → c m ≺ᴵ c (suc m)
  c≺c m = ≺⊑ (rc m) (kc (suc m))

  Ξ : ∀ m {x} → x ≺ᴵ c m → Ordᴵ
  Ξ m r = Σs m +ᴿ em (e (suc m)) (≺ᴵ-trans r (rc m))

  En : ∀ n {x} → x ≺ᴵ c n → Ordᴵ
  En zero    r = Ξ 0 r
  En (suc m) r with two-preds r (c≺c m)
  ... | injᵃ y = En m y
  ... | injᵇ _ = Ξ (suc m) r
  ... | injᶜ _ = Ξ (suc m) r

  Ξ-lt : ∀ m {x} (r : x ≺ᴵ c m) → Ξ m r ≺ᴵ Σs (suc m)
  Ξ-lt m r = shift-predecessor (Σs m) (et (e (suc m)) _)

  En-lt : ∀ n {x} (r : x ≺ᴵ c n) → En n r ≺ᴵ Σs (suc n)
  En-lt zero    r = Ξ-lt 0 r
  En-lt (suc m) r with two-preds r (c≺c m)
  ... | injᵃ y = sum-step g (suc m) (En-lt m y)
  ... | injᵇ _ = Ξ-lt (suc m) r
  ... | injᶜ _ = Ξ-lt (suc m) r

  En-mono : ∀ n {x y} (r : x ≺ᴵ c n) (t : y ≺ᴵ c n) → x ≺ᴵ y → En n r ≺ᴵ En n t
  En-mono zero r t w = shift-predecessor _ (en (e 1) _ _ w)
  En-mono (suc m) r t w with two-preds r (c≺c m) | two-preds t (c≺c m)
  ... | injᵃ r′ | injᵃ t′ = En-mono m r′ t′ w
  ... | injᵃ r′ | injᵇ _  = keep-left (En-lt m r′) _
  ... | injᵃ r′ | injᶜ _  = keep-left (En-lt m r′) _
  ... | injᵇ g  | injᵃ t′ = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans g (≺ᴵ-trans w t′)))
  ... | injᶜ g  | injᵃ t′ = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym g) (≺ᴵ-trans w t′)))
  ... | injᵇ _  | injᵇ _  = shift-predecessor _ (en (e (suc (suc m))) _ _ w)
  ... | injᵇ _  | injᶜ _  = shift-predecessor _ (en (e (suc (suc m))) _ _ w)
  ... | injᶜ _  | injᵇ _  = shift-predecessor _ (en (e (suc (suc m))) _ _ w)
  ... | injᶜ _  | injᶜ _  = shift-predecessor _ (en (e (suc (suc m))) _ _ w)

  En-coh : ∀ n {x y} (r : x ≺ᴵ c n) (t : y ≺ᴵ c n) → x ≅ᴵ y → En n r ≅ᴵ En n t
  En-coh zero r t w = R.add-cong (Σs 0) (ec (e 1) _ _ w)
  En-coh (suc m) r t w with two-preds r (c≺c m) | two-preds t (c≺c m)
  ... | injᵃ r′ | injᵃ t′ = En-coh m r′ t′ w
  ... | injᵃ r′ | injᵇ g  = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respʳ g (≅ᴵ-sym w)) r′))
  ... | injᵃ r′ | injᶜ g  = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym (≅ᴵ-trans w g)) r′))
  ... | injᵇ g  | injᵃ t′ = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respʳ g w) t′))
  ... | injᶜ g  | injᵃ t′ = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-trans (≅ᴵ-sym g) w) t′))
  ... | injᵇ _  | injᵇ _  = R.add-cong (Σs (suc m)) (ec (e (suc (suc m))) _ _ w)
  ... | injᵇ _  | injᶜ _  = R.add-cong (Σs (suc m)) (ec (e (suc (suc m))) _ _ w)
  ... | injᶜ _  | injᵇ _  = R.add-cong (Σs (suc m)) (ec (e (suc (suc m))) _ _ w)
  ... | injᶜ _  | injᶜ _  = R.add-cong (Σs (suc m)) (ec (e (suc (suc m))) _ _ w)

  lift1 : ∀ m {x} → x ≺ᴵ c m → x ≺ᴵ c (suc m)
  lift1 m r = ≺ᴵ-trans r (c≺c m)

  ext1 : ∀ m {x} (r : x ≺ᴵ c m) → En (suc m) (lift1 m r) ≅ᴵ En m r
  ext1 m r with two-preds (lift1 m r) (c≺c m)
  ... | injᵃ y = En-coh m y r (≅ᴵ-refl _)
  ... | injᵇ g = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans g r))
  ... | injᶜ g = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym g) r))

  liftS : ∀ {n k x} → n ≤′ k → x ≺ᴵ c n → x ≺ᴵ c k
  liftS ≤′-refl     r = r
  liftS (≤′-step l) r = lift1 _ (liftS l r)

  extS : ∀ {n k x} (l : n ≤′ k) (r : x ≺ᴵ c n) → En k (liftS l r) ≅ᴵ En n r
  extS ≤′-refl     r = ≅ᴵ-refl _
  extS (≤′-step l) r = ≅ᴵ-trans (ext1 _ (liftS l r)) (extS l r)

  addr : ∀ {x} → x ≺ᴵ lim f s → Σ ℕ (λ n → x ≺ᴵ c n)
  addr (via e′ (lim n q)) = n , ≺⊑ (via e′ q) (kc n)

  emL : ∀ {x} → x ≺ᴵ lim f s → Ordᴵ
  emL r = let n , t = addr r in En n t

  embedding : BoundedEmbedding (lim f s) (R.complete g)
  embedding = record { map = emL ; bound = etL ; ordered = enL ; coherent = ecL }
    where
    etL : ∀ {x} (r : x ≺ᴵ lim f s) → emL r ≺ᴵ R.complete g
    etL r = let n , t = addr r in into-lim (suc n) (En-lt n t)
    enL : ∀ {x y} (r : x ≺ᴵ lim f s) (t : y ≺ᴵ lim f s) → x ≺ᴵ y → emL r ≺ᴵ emL t
    enL r t w with addr r | addr t
    ... | n , r′ | k , t′ =
      ≺ᴵ-respˡ (≅ᴵ-sym (extS (≤⇒≤′ (m≤m+n n k)) r′))
        (≺ᴵ-respʳ
          (En-mono (n +ᴺ k) (liftS (≤⇒≤′ (m≤m+n n k)) r′)
            (liftS (≤⇒≤′ (m≤n+m k n)) t′) w)
          (extS (≤⇒≤′ (m≤n+m k n)) t′))
    ecL : ∀ {x y} (r : x ≺ᴵ lim f s) (t : y ≺ᴵ lim f s) → x ≅ᴵ y → emL r ≅ᴵ emL t
    ecL r t w with addr r | addr t
    ... | n , r′ | k , t′ = ≅ᴵ-trans (≅ᴵ-sym (extS (≤⇒≤′ (m≤m+n n k)) r′))
        (≅ᴵ-trans (En-coh (n +ᴺ k) (liftS (≤⇒≤′ (m≤m+n n k)) r′)
          (liftS (≤⇒≤′ (m≤n+m k n)) t′) w)
          (extS (≤⇒≤′ (m≤n+m k n)) t′))
```

以下实例不要求尚未填充的回调合同：任意已有严格分支边界的源，
其每支恒等嵌入可以直接拼入实际累计解释；也可在每支加任意同一前缀。
自然数整列给出非空的无限源实例。

```agda
identity : ∀ a → BoundedEmbedding a a
identity a = record
  { map = λ {d} p → d ; bound = λ p → p
  ; ordered = λ p q r → r ; coherent = λ p q r → r }

self-completion : ∀ (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n)) →
  (∀ n → Σ Ordᴵ (λ c → c ≺ᴵ f (suc n) × f n ⊑ᴵ c)) →
  BoundedEmbedding (lim f s) (R.complete f)
self-completion f s st = Assemble.embedding {s = s} f st (λ n → identity (f n))

import OCF.Align.TotalValueBuildEmbedding as Shift
shifted-completion : ∀ a (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n)) →
  (∀ n → Σ Ordᴵ (λ c → c ≺ᴵ f (suc n) × f n ⊑ᴵ c)) →
  BoundedEmbedding (lim f s) (R.complete (λ n → R.add a (f n)))
shifted-completion a f s st = Assemble.embedding {s = s}
  (λ n → R.add a (f n)) st (λ n → Shift.cumulative a (f n))

num : ℕ → Ordᴵ
num zero = zero
num (suc n) = suc (num n)
num-step : ∀ n → num n ⊑ᴵ num (suc n)
num-step n = Sim→⊑ᴵ suc
num-boundaries : ∀ n → Σ Ordᴵ (λ c → c ≺ᴵ num (suc n) × num n ⊑ᴵ c)
num-boundaries n = num n , via (≅ᴵ-refl _) zero , ⊑ᴵ-refl

omega-embedded : BoundedEmbedding (lim num num-step) (R.complete num)
omega-embedded = self-completion num num-step num-boundaries
omega-shifted : ∀ a → BoundedEmbedding (lim num num-step)
  (R.complete (λ n → R.add a (num n)))
omega-shifted a = shifted-completion a num num-step num-boundaries
```

Assemble.embedding 不要求分支嵌入跨编号使用相同映射：边界选择正是
为解决源分支重叠。它仍要求每支已有真正的 bound/ordered/coherent，
不能从每支仅有序数值不等式反推。将它用于最高原闭项，还需实际
旧输出的严格边界，以及旧／新反馈之间每支的有界嵌入。
