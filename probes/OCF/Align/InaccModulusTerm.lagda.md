# 层号判决的范数模: 下标类的封闭性 (验收)

> **验收节.** 纯语法: `Cnt` (顶层下标全为 0, 即可数), `Sub N` (出现的每个下标都在 `N` 里). 只要 `N` 满足 `ClN`, `Cnt ∧ Sub N` 就对 `fsn`、`pred` 封闭, 并给出 `Commute` 要的 `ClQ`. 这里没有标准形, 没有序数论. 结论在 [InaccModulus](InaccModulus.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulusTerm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.InaccStrikeCommute using (ClQ)
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; cof; cofψ0; cofA; cofψ₊; pred; pred-<; fsn; fsn↓; fsn↓₊; fsn↓0; fsn↓c; rep↓; trm; dec; fsT; fsT0; fsT₊; fsTc; fsT↓; fsT↓-trm; γT; γ↓; γ↓-trm; Ωt; sucT; cmpᵀ; Cmp; lt; eq; gt; 𝟏; natT; fsn₊-eq; fsn0-eq) renaming (ψ to ψᵗ)

Cnt : T → Set
Cnt []                = ⊤
Cnt (ψᵗ [] a ∷ xs)    = Cnt xs
Cnt (ψᵗ (_ ∷ _) a ∷ xs) = ⊥

Sub : (T → Set) → T → Set
Sub N []            = ⊤
Sub N (ψᵗ u a ∷ xs) = N u × Sub N a × Sub N xs

Sub-map : ∀ {N M : T → Set} → (∀ {u} → N u → M u) → ∀ t → Sub N t → Sub M t
Sub-map f [] s = tt
Sub-map f (ψᵗ u a ∷ xs) (nu , sa , sx) = f nu , Sub-map f a sa , Sub-map f xs sx

gt-suc : ∀ μ → cmpᵀ (sucT μ) [] ≡ gt
gt-suc []      = refl
gt-suc (x ∷ μ) = refl

-- 可数的项没有 Ω 共尾度
Cnt-noΩ : ∀ t {ν} → Cnt t → cof t ≡ cΩ ν → ⊥
Cnt-noΩ [] c ()
Cnt-noΩ (ψᵗ [] [] ∷ []) c ()
Cnt-noΩ (ψᵗ [] (y ∷ ys) ∷ []) c e = go (cof (y ∷ ys)) e where
  go : ∀ k {ν} → cofA [] k ≡ cΩ ν → ⊥
  go c0 ()
  go c1 ()
  go cω ()
  go (cΩ μ) e′ = go′ (cmpᵀ (sucT μ) []) (gt-suc μ) e′ where
    go′ : ∀ m {ν} → m ≡ gt → cofψ₊ [] μ m ≡ cΩ ν → ⊥
    go′ gt p ()
Cnt-noΩ (ψᵗ [] a ∷ y ∷ ys) c e = Cnt-noΩ (y ∷ ys) c e

Cnt-pred : ∀ t → Cnt t → Cnt (pred t)
Cnt-pred [] c = tt
Cnt-pred (ψᵗ [] [] ∷ []) c = tt
Cnt-pred (ψᵗ [] (_ ∷ _) ∷ []) c = tt
Cnt-pred (ψᵗ [] a ∷ y ∷ ys) c = Cnt-pred (y ∷ ys) c
```

`pred` 只删末尾的 `𝟏`. 下面的闭包对任意 `N` 成立, 但 `Sub N (natT n)` 要 `N []`.

```agda
record ClN (N : T → Set) : Set where
  field
    N-nil : N []
    N-sub : ∀ {u} → N u → Sub N u
    N-pr  : ∀ {u} → N u → cof u ≡ c1 → N (pred u)
    N-fs  : ∀ {u} → N u → cof u ≡ cω → ∀ n → N (fsn u n)
    N-nc  : ∀ {u ν} → N u → cof u ≡ cΩ ν → ⊥

module Closed {N : T → Set} (cn : ClN N) where
  open ClN cn

  Sub-nat : ∀ n → Sub N (natT n)
  Sub-nat zero    = tt
  Sub-nat (suc n) = N-nil , tt , Sub-nat n

  Sub-pred : ∀ t → Sub N t → Sub N (pred t)
  Sub-pred [] s = tt
  Sub-pred (ψᵗ [] [] ∷ []) s = tt
  Sub-pred (ψᵗ [] (_ ∷ _) ∷ []) s = s
  Sub-pred (ψᵗ (_ ∷ _) a ∷ []) s = s
  Sub-pred (ψᵗ u a ∷ y ∷ ys) (nu , sa , sx) = nu , sa , Sub-pred (y ∷ ys) sx

  -- cl-nu: Ω 共尾度的 ν 来自某个下标的 pred
  nuT : ∀ w {ν} → Sub N w → cof w ≡ cΩ ν → N ν
  nuA : ∀ u b k → Sub N b → cof b ≡ k → ∀ {ν} → cofA u k ≡ cΩ ν → N ν
  nuC : ∀ u b μ m → Sub N b → cof b ≡ cΩ μ → ∀ {ν} → cofψ₊ u μ m ≡ cΩ ν → N ν
  nu0 : ∀ u k → N u → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → N ν

  nuT [] s ()
  nuT (ψᵗ [] [] ∷ []) s ()
  nuT (ψᵗ u (y ∷ ys) ∷ []) (_ , sa , _) e = nuA u (y ∷ ys) (cof (y ∷ ys)) sa refl e
  nuT (ψᵗ (w ∷ ws) [] ∷ []) (nu , _ , _) e = nu0 (w ∷ ws) (cof (w ∷ ws)) nu refl e
  nuT (ψᵗ u a ∷ y ∷ ys) (_ , _ , sx) e = nuT (y ∷ ys) sx e

  nuA u b c0 s p ()
  nuA u b c1 s p ()
  nuA u b cω s p ()
  nuA u b (cΩ μ) s p e = nuC u b μ (cmpᵀ (sucT μ) u) s p e
  nuC u b μ lt s p refl = nuT b s p
  nuC u b μ eq s p refl = nuT b s p
  nuC u b μ gt s p ()
  nu0 u c0 nu p ()
  nu0 u c1 nu p refl = N-pr nu p
  nu0 u cω nu p ()
  nu0 u (cΩ μ) nu p e = ⊥-elim (N-nc nu p)

  clQ : ClQ (Sub N) N
  clQ = record
    { cl-tl  = λ { {ψᵗ _ _} s → proj₂ (proj₂ s) }
    ; cl-sub = λ s → N-sub (proj₁ s)
    ; cl-arg = λ s → proj₁ (proj₂ s)
    ; cl-idx = proj₁
    ; cl-nu  = λ {w} s e → nuT w s e
    }

  Sub-fsT : ∀ a {η} → Sub N a → Sub N η → Sub N (fsT a η)
  sfA : ∀ u b k {η} → N u → Sub N b → Sub N η → Sub N (fsT₊ u b k η)
  sfC : ∀ u b ν m {η} → N u → Sub N b → Sub N η → Sub N (fsTc u b ν m η)
  sf0 : ∀ u k {η} → N u → cof u ≡ k → Sub N η → Sub N (fsT0 u k η)

  Sub-fsT [] s h = tt
  Sub-fsT (ψᵗ [] [] ∷ []) s h = tt
  Sub-fsT (ψᵗ u (y ∷ ys) ∷ []) (nu , sa , _) h = sfA u (y ∷ ys) (cof (y ∷ ys)) nu sa h
  Sub-fsT (ψᵗ (w ∷ ws) [] ∷ []) (nu , _ , _) h = sf0 (w ∷ ws) (cof (w ∷ ws)) nu refl h
  Sub-fsT (ψᵗ u a ∷ y ∷ ys) (nu , sa , sx) h = nu , sa , Sub-fsT (y ∷ ys) sx h

  sfA u b c0 nu s h = nu , s , tt
  sfA u b c1 nu s h = nu , s , tt
  sfA u b cω nu s h = nu , s , tt
  sfA u b (cΩ ν) nu s h = sfC u b ν (cmpᵀ (sucT ν) u) nu s h
  sfC u b ν lt nu s h = nu , Sub-fsT b s h , tt
  sfC u b ν eq nu s h = nu , Sub-fsT b s h , tt
  sfC u b ν gt nu s h = nu , s , tt
  sf0 u c0 nu p h = nu , tt , tt
  sf0 u c1 nu p h = h
  sf0 u cω nu p h = nu , tt , tt
  sf0 u (cΩ ν) nu p h = ⊥-elim (N-nc nu p)

  Sub-γ : ∀ b ν → N ν → Sub N b → ∀ k → Sub N (γT b ν k)
  Sub-γ b ν nν s zero    = nν , tt , tt
  Sub-γ b ν nν s (suc k) = nν , Sub-fsT b s (Sub-γ b ν nν s k) , tt
```

`fsn` 的闭包: 走 `fsn↓` 的子句, 证书的裸值用 `fsT↓-trm`, `γ↓-trm` 换回 `fsT`, `γT`.

```agda
  srep : ∀ u {a a′} (l : a′ E.<ᵀ a) n → N u → Sub N a′ → Sub N (trm (rep↓ u l n))
  srep u l zero    nu s = tt
  srep u l (suc n) nu s = nu , s , srep u l n nu s

  sfn  : ∀ x xs n → Sub N (x ∷ xs) → Sub N (trm (fsn↓ x xs n))
  sfp  : ∀ u y ys k (be : cof (y ∷ ys) ≡ k) n → N u → Sub N (y ∷ ys) → Sub N (trm (fsn↓₊ u y ys k be n))
  sfc  : ∀ u y ys ν (be : cof (y ∷ ys) ≡ cΩ ν) m n → N u → Sub N (y ∷ ys) → Sub N (trm (fsn↓c u y ys ν be m n))
  sf0n : ∀ w ws k (ue : cof (w ∷ ws) ≡ k) n → N (w ∷ ws) → Sub N (trm (fsn↓0 w ws k ue n))

  sfn (ψᵗ u a) (y ∷ ys) n (nu , sa , sx) = nu , sa , sfn y ys n sx
  sfn (ψᵗ u (y ∷ ys)) [] n (nu , sa , _) = sfp u y ys (cof (y ∷ ys)) refl n nu sa
  sfn (ψᵗ (w ∷ ws) []) [] n (nu , _ , _) = sf0n w ws (cof (w ∷ ws)) refl n nu
  sfn (ψᵗ [] []) [] n _ = tt

  sfp u y ys c0 be n nu s = tt
  sfp u y ys c1 be n nu s = srep u (pred-< (y ∷ ys) be) n nu (Sub-pred (y ∷ ys) s)
  sfp u y ys cω be n nu s = nu , sfn y ys n s , tt
  sfp u y ys (cΩ ν) be n nu s = sfc u y ys ν be (cmpᵀ (sucT ν) u) n nu s

  sfc u y ys ν be gt n nu s =
    nu , subst (Sub N) (sym (trans (fsT↓-trm (y ∷ ys) be (dec (γ↓ (y ∷ ys) ν be n))) (cong (fsT (y ∷ ys)) (γ↓-trm (y ∷ ys) ν be n))))
               (Sub-fsT (y ∷ ys) s (Sub-γ (y ∷ ys) ν (nuT (y ∷ ys) s be) s n)) , tt
  sfc u y ys ν be lt n nu s =
    nu , subst (Sub N) (sym (fsT↓-trm (y ∷ ys) be (E.natT<Ωs n ν))) (Sub-fsT (y ∷ ys) s (Sub-nat n)) , tt
  sfc u y ys ν be eq n nu s =
    nu , subst (Sub N) (sym (fsT↓-trm (y ∷ ys) be (E.natT<Ωs n ν))) (Sub-fsT (y ∷ ys) s (Sub-nat n)) , tt

  sf0n w ws c0 ue n nu = tt
  sf0n w ws c1 ue n nu = subst (Sub N) refl (Sub-nat n)
  sf0n w ws cω ue n nu = N-fs nu ue n , tt , tt
  sf0n w ws (cΩ ν) ue n nu = ⊥-elim (N-nc nu ue)

  Sub-fsn : ∀ t n → Sub N t → Sub N (fsn t n)
  Sub-fsn [] n s = tt
  Sub-fsn (x ∷ xs) n s = sfn x xs n s
```

可数性对 `fsn` 封闭.

```agda
crep : ∀ {a a′} (l : a′ E.<ᵀ a) n → Cnt (trm (rep↓ [] l n))
crep l zero    = tt
crep l (suc n) = crep l n

cfn : ∀ x xs n → Cnt (x ∷ xs) → Cnt (trm (fsn↓ x xs n))
cfp : ∀ y ys k (be : cof (y ∷ ys) ≡ k) n → Cnt (trm (fsn↓₊ [] y ys k be n))
cfc : ∀ y ys ν (be : cof (y ∷ ys) ≡ cΩ ν) m n → Cnt (trm (fsn↓c [] y ys ν be m n))

cfn (ψᵗ [] a) (y ∷ ys) n c = cfn y ys n c
cfn (ψᵗ [] (y ∷ ys)) [] n c = cfp y ys (cof (y ∷ ys)) refl n
cfn (ψᵗ [] []) [] n c = tt

cfp y ys c0 be n = tt
cfp y ys c1 be n = crep (pred-< (y ∷ ys) be) n
cfp y ys cω be n = tt
cfp y ys (cΩ ν) be n = cfc y ys ν be (cmpᵀ (sucT ν) []) n
cfc y ys ν be lt n = tt
cfc y ys ν be eq n = tt
cfc y ys ν be gt n = tt

Cnt-fsn : ∀ t n → Cnt t → Cnt (fsn t n)
Cnt-fsn [] n c = tt
Cnt-fsn (x ∷ xs) n c = cfn x xs n c
```
