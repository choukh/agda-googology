# YiIrrNeg 第 1 项：`FoldRows` 有实例，所以接口本身不可否定

**判决（编译构造）。** `model : FoldRows`，定义域是 `Only0 × Legal × Low0`（整个零层合法片段，另带相关的下界证据）。
所以 `FoldRows → ⊥` 不可证；去掉 `Low0` 的取法见 [YiIrrNegWideDecide](YiIrrNegWideDecide.lagda.md)。
本篇只是可满足性的见证：没有值定理，没有 Ω₁ 上的同值或下界，这些仍是构造路的交付。入口 [YiIrrNeg](YiIrrNeg.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrNegModel where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrNegWide using (Low0; Ω₁-low)
open import OCF.Align.YiIrrNegForced using (add-legal; times-ω-legal)
```

第 0 层的算术：`x ⊲ x + y` 对一切 `y` 成立（极限处取第 0 项），所以链点的守卫不需要正性；
严格增长才需要。

```agda
cp-tr : ∀ {a b} d → Cp zero a b → Cp zero b d → Cp zero a d
dn-tr : ∀ {a b} d → Cp zero a b → Dn zero b d → Dn zero a d
cp-tr d p (inj₁ refl) = p
cp-tr d p (inj₂ q) = inj₂ (dn-tr d p q)
dn-tr G.zero p ()
dn-tr (G.suc d) p q = cp-tr d p q
dn-tr (G.lim f) p (n , q) = n , cp-tr (f n) p q
dn-tr (G.lc () c t g) p q
dn-tr (G.em () a) p q
dn-tr G.top p ()

add-cp : ∀ x y → Cp zero x (x +ʳ y)
add-cp x G.zero = inj₁ refl
add-cp x (G.suc y) = inj₂ (add-cp x y)
add-cp x (G.lim f) = inj₂ (zero , add-cp x (f zero))
add-cp x (G.lc () c t g)
add-cp x (G.em () a)
add-cp x G.top = inj₂ (inj₁ refl)

add-dn : ∀ x y → Dn zero G.zero y → Dn zero x (x +ʳ y)
add-dn x G.zero ()
add-dn x (G.suc y) p = add-cp x y
add-dn x (G.lim f) p = zero , add-cp x (f zero)
add-dn x (G.lc () c t g) p
add-dn x (G.em () a) p
add-dn x G.top ()
```

链的一步对子折叠 `o` 参数化；`o` 的输出合法只在守卫（无关字段）里用。

```agda
chain-step : (c : R) (o : (η : R) → .(Gd zero c η) → R) →
  .((η : R) (e : Gd zero c η) → Lgl zero (o η e)) → Point c → Point c
chain-step c o ol (point η e) = point (η +ʳ o η e)
  (cp-tr (η +ʳ o η e) (proj₁ e) (add-cp η (o η e)) ,
   add-legal η (o η e) (proj₁ (proj₂ e)) (ol η e) ,
   raw0-Nested (η +ʳ o η e))

chain-out : (c : R) (o : (η : R) → .(Gd zero c η) → R) → Point c → R
chain-out c o (point η e) = o η e

Dom⁺ : LF → Set
Dom⁺ x = Only0 x × Legal x × Low0 x

at⁺ : ∀ f → Dom⁺ (lim f) → ∀ n → Dom⁺ (f n)
at⁺ f (o , (st , L) , W) n = o n , L n , W n

br : ∀ c .(w : Lgl zero c) .(b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) →
  Dom⁺ (lc zero c w b t g) → ∀ η (e : Gd zero c η) → Dom⁺ (g η e)
br c w b t g (o , (Lk , tg , dir , irr , Lt , Lg) , (lc′ , nc , Wt , Wg)) η e =
  proj₂ o η e , Lg η e , Wg η e
```

折叠与它的合法性互递归：链点的守卫要子输出合法。`ψ⁺` 只在无关位置用证明。
`ψ-position` 对目标树递归；Ω 结点的 `fst` 情形用起点分支，起点的守卫来自 `Low0`。

```agda
ψ⁺ : (x : LF) → .(Dom⁺ x) → R
ψ-legal : (x : LF) (d : Dom⁺ x) → Lgl zero (ψ⁺ x d)
ψ-pos : (x : LF) .(d : Dom⁺ x) → Dn zero G.zero (ψ⁺ x d)
ψ-position : ∀ x y (dx : Dom⁺ x) (dy : Dom⁺ y) → CP x y →
  Cp zero (ψ⁺ x dx) (ψ⁺ y dy)

ψ⁺ zero d = one
ψ⁺ (suc x) d = successor (ψ⁺ x d)
ψ⁺ (lim f) d = G.lim (λ n → ψ⁺ (f n) (at⁺ f d n))
ψ⁺ (lc zero c w b t g) d = G.lim (λ n →
  chain-out c (λ η e → ψ⁺ (g η e) (br c w b t g d η e))
    (iterate
      (chain-step c (λ η e → ψ⁺ (g η e) (br c w b t g d η e))
        (λ η e → ψ-legal (g η e) (br c w b t g d η e)))
      (start c w b) n))
ψ⁺ (lc (suc k) c w b t g) d = one
ψ⁺ (lc (lim f) c w b t g) d = one
ψ⁺ (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = one

ψ-pos zero d = inj₁ refl
ψ-pos (suc x) d = zero , inj₁ refl
ψ-pos (lim f) d = zero , inj₂ (ψ-pos (f zero) (at⁺ f d zero))
ψ-pos (lc zero c w b t g) d = zero , inj₂
  (ψ-pos (g c (inj₁ refl , w , b)) (br c w b t g d c (inj₁ refl , w , b)))
ψ-pos (lc (suc k) c w b t g) d = inj₁ refl
ψ-pos (lc (lim f) c w b t g) d = inj₁ refl
ψ-pos (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = inj₁ refl

ψ-position x zero dx dy self = inj₁ refl
ψ-position x (suc y) dx dy self = inj₁ refl
ψ-position x (suc y) dx dy (suc p) = inj₂ (suc zero , ψ-position x y dx dy p)
ψ-position x (lim f) dx dy self = inj₁ refl
ψ-position x (lim f) dx dy (lim n p) =
  inj₂ (n , ψ-position x (f n) dx (at⁺ f dy n) p)
ψ-position x (lc zero c w b t g) dx dy self = inj₁ refl
ψ-position x (lc zero c w b t g) dx
  (o , (Lk , tg , dir , irr , Lt , Lg) , (lc′ , nc , Wt , Wg)) (fst p) =
  inj₂ (zero , ψ-position x (g c (inj₁ refl , lc′ , nc)) dx
    (proj₂ o c (inj₁ refl , lc′ , nc) , Lg c (inj₁ refl , lc′ , nc) ,
      Wg c (inj₁ refl , lc′ , nc))
    (CP-tr p (tg c (inj₁ refl , lc′ , nc))))
ψ-position x (lc (suc k) c w b t g) dx (() , _) p
ψ-position x (lc (lim f) c w b t g) dx (() , _) p
ψ-position x (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) dx (() , _) p

ψ-legal zero d = tt
ψ-legal (suc x) d = times-ω-legal (ψ⁺ x d) (ψ-legal x d) (inj₂ (ψ-pos x d))
ψ-legal (lim f) (o , (st , L) , W) =
  (λ n → ψ-position (f n) (f (suc n)) (o n , L n , W n)
    (o (suc n) , L (suc n) , W (suc n)) (st n)) ,
  (λ n → ψ-legal (f n) (o n , L n , W n))
ψ-legal (lc zero c w b t g)
  (o , (Lk , tg , dir , irr , Lt , Lg) , (lc′ , nc , Wt , Wg)) = steps , lawful
  where
  d : Dom⁺ (lc zero c w b t g)
  d = o , (Lk , tg , dir , irr , Lt , Lg) , (lc′ , nc , Wt , Wg)
  sub : (η : R) → .(Gd zero c η) → R
  sub η e = ψ⁺ (g η e) (br c w b t g d η e)
  P : ℕ → Point c
  P = iterate
    (chain-step c sub (λ η e → ψ-legal (g η e) (br c w b t g d η e)))
    (start c w b)
  pt : ℕ → R
  pt n = coordinate (P n)
  rg : ∀ n → Gd zero c (pt n)
  rg zero = inj₁ refl , lc′ , nc
  rg (suc n) =
    cp-tr (pt n +ʳ sub (pt n) (rg n)) (proj₁ (rg n))
      (add-cp (pt n) (sub (pt n) (rg n))) ,
    add-legal (pt n) (sub (pt n) (rg n)) (proj₁ (proj₂ (rg n)))
      (ψ-legal (g (pt n) (rg n)) (br c w b t g d (pt n) (rg n))) ,
    raw0-Nested (pt n +ʳ sub (pt n) (rg n))
  lawful : ∀ n → Lgl zero (chain-out c sub (P n))
  lawful n = ψ-legal (g (pt n) (rg n)) (br c w b t g d (pt n) (rg n))
  steps : ∀ n → Cp zero (chain-out c sub (P n)) (chain-out c sub (P (suc n)))
  steps n = ψ-position (g (pt n) (rg n)) (g (pt (suc n)) (rg (suc n)))
    (br c w b t g d (pt n) (rg n))
    (br c w b t g d (pt (suc n)) (rg (suc n)))
    (dir (pt n) (rg n) (pt (suc n)) (rg (suc n))
      (add-cp (pt n) (sub (pt n) (rg n)) ,
       proj₁ (proj₂ (rg (suc n))) ,
       raw0-Nested (pt (suc n))))
ψ-legal (lc (suc k) c w b t g) d = tt
ψ-legal (lc (lim f) c w b t g) d = tt
ψ-legal (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = tt
```

各行是 `refl`；`next` 就是上面的链步。

```agda
grow⁺ : ∀ c (w : Lgl zero c) (b : Nested zero c) t
  (g : (η : R) → .(Gd zero c η) → LF) (d : Dom⁺ (lc zero c w b t g))
  (p : Point c) →
  Dn zero (coordinate p) (coordinate
    (chain-step c (λ η e → ψ⁺ (g η e) (br c w b t g d η e))
      (λ η e → ψ-legal (g η e) (br c w b t g d η e)) p))
grow⁺ c w b t g d (point η e) = add-dn η
  (ψ⁺ (g η e) (br c w b t g d η e))
  (ψ-pos (g η e) (br c w b t g d η e))

model : FoldRows
model = record
  { Dom = Dom⁺
  ; dom-pred = λ x d → d
  ; dom-at = at⁺
  ; dom-branch = λ c w b t g d η e → br c w b t g d η e
  ; dom-only = λ x d → proj₁ d
  ; dom-legal = λ x d → proj₁ (proj₂ d)
  ; dom-Ω₁ = Ω₁-only , Ω₁-legal , Ω₁-low
  ; ψ = ψ⁺
  ; next = λ c w b t g d →
      chain-step c (λ η e → ψ⁺ (g η e) (br c w b t g d η e))
        (λ η e → ψ-legal (g η e) (br c w b t g d η e))
  ; zero-row = λ d → refl
  ; suc-row = λ x d → refl
  ; lim-row = λ f d → refl
  ; next-additive = λ c w b t g d p → refl
  ; next-grow = grow⁺
  ; gt-row = λ c w b t g d → refl
  ; fold-legal = ψ-legal
  ; fold-positive = λ x d → ψ-pos x d
  ; position = ψ-position
  }

-- 接口不可否定的形式: 任何 FoldRows → A 都给出 A.
not-refutable : ∀ {A : Set} → (FoldRows → A) → A
not-refutable h = h model
```

范围：`model` 的定义域带相关的下界证据 `Low0`；树里的 `w`、`b` 与 `ψ⁺` 的证书参数仍是无关的。
`ψ⁺` 在层号不为 0 的结点上取 1，那些结点不在定义域里（`Only0` 为空）。
