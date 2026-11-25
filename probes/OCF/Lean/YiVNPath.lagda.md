# 反例那一对层号之间没有字面路径

> 判决: 编译定理, 无前提, 不读记号. 对 [YiVNIdx](YiVNIdx.lagda.md) 的两个实例, 反例里的两个层号 `ℓ (Ωt K)` 与 `ℓ c′` 之间没有目标路径 ≤ (可经下标层侧), 所以也没有字面路径 ⊑ (`no-path₀`, `no-path₁` 及其 ⊑ 版).
> 做了什么: 不变量 `AllIdx P` (层号里每个 Ω 形状的下标层满足 P) 沿路径向下传; 顶层是同一个下标层的 Ω 形状, 自身路径由第 0 个孩子不同排除, 进孩子的路径由孩子里没有下标层为 k 的 Ω 形状排除.
> 不否定什么: 不说以 ⊑/≤ 为前提的下标单调成立, 只说 `YiVNIdx` 的反例碰不到它; 只对 K 为第 1、2 层两个实例, 一般的 k 要层号无环的引理, 没有做.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVNPath where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (c₀)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiVNIdx using (one; module G₀; module G₁)
```

## 不变量

```agda
mutual
  AllIdx : (L → Set) → L → Set
  AllIdx P zero     = ⊤
  AllIdx P (nd s h) = IdxS P s × ((c : Ch s) → AllIdx P (h c))

  IdxS : (L → Set) → Sh → Set
  IdxS P sS     = ⊤
  IdxS P sL     = ⊤
  IdxS P (sΩ j) = P j × AllIdx P j

down : ∀ {b P X Y} → AllIdx P Y → Pth b X Y → AllIdx P X
down a                 self              = a
down (_ , ah)          (inc c v)         = down (ah c) v
down (_ , ah)          (inu {s = s} vs)  = down (ah (c₀ s)) (vs (c₀ s))
down ((_ , aj) , _)    (ink v)           = down aj v

⊕-all : ∀ {P} (a b : L) → AllIdx P a → AllIdx P b → AllIdx P (a ⊕ b)
⊕-all a zero     aa _         = aa
⊕-all a (nd s h) aa (is , ah) = is , λ c → ⊕-all a (h c) aa (ah c)

↑0-all : ∀ {P} (d : Tr zero) → AllIdx P (↑ zero d)
↑0-all zero          = tt
↑0-all (suc d)       = tt , λ _ → ↑0-all d
↑0-all (lim f a)     = tt , λ n → ↑0-all (f n)
↑0-all (Ω () g)
↑0-all (up x () y e)

↑1-all : ∀ {P} → P zero → (d : Tr one) → AllIdx P (↑ one d)
↑1-all pz zero                          = tt
↑1-all pz (suc d)                       = tt , λ _ → ↑1-all pz d
↑1-all pz (lim f a)                     = tt , λ n → ↑1-all pz (f n)
↑1-all pz (Ω (inj₁ ()) g)
↑1-all pz (Ω (inj₂ (tt , inj₁ tt)) g)   = (pz , tt) , λ c → ↑1-all pz (g c)
↑1-all pz (Ω (inj₂ (tt , inj₂ ())) g)
↑1-all pz (up x c y e)                  = ⊕-all (↑ one x) (↑ zero y) (↑1-all pz x) (↑0-all y)
```

## 顶层

```agda
child0 : L → L
child0 zero          = zero
child0 (nd sS h)     = zero
child0 (nd sL h)     = zero
child0 (nd (sΩ j) h) = h zero

childS : L → L
childS (nd sS h) = h tt
childS _         = zero

nd≢z : ∀ {s h} → nd s h ≡ zero → ⊥
nd≢z ()

module Top (k : L) (P : L → Set) (nP : P k → ⊥) (ak : AllIdx P k) (h h′ : Tr k → L)
           (ah′ : (c : Tr k) → AllIdx P (h′ c)) (ne : h zero ≡ h′ zero → ⊥) where
  aux : ∀ {X Y} → X ≤ Y → X ≡ nd (sΩ k) h → Y ≡ nd (sΩ k) h′ → ⊥
  aux self      e₁   e₂   = ne (cong child0 (trans (sym e₁) e₂))
  aux (inc c v) refl refl = nP (proj₁ (proj₁ (down (ah′ c) v)))
  aux (inu vs)  refl refl = nP (proj₁ (proj₁ (down (ah′ zero) (vs zero))))
  aux (ink v)   refl refl = nP (proj₁ (proj₁ (down ak v)))

  no : nd (sΩ k) h ≤ nd (sΩ k) h′ → ⊥
  no v = aux v refl refl
```

## 两个实例

```agda
P₀ : L → Set
P₀ j = j ≡ zero → ⊥

ah₀ : (c : Tr zero) → AllIdx P₀ (G₀.ℓ (G₀.g′ c))
ah₀ zero          = tt , λ _ → tt
ah₀ (suc d)       = ⊕-all one (zero ⊕ ↑ zero (suc d)) (tt , λ _ → tt) (⊕-all zero (↑ zero (suc d)) tt (↑0-all (suc d)))
ah₀ (lim f a)     = tt , λ _ → tt
ah₀ (Ω () g)
ah₀ (up x () y e)

no-path₀ : G₀.ℓ G₀.ΩK ≤ G₀.ℓ G₀.c′ → ⊥
no-path₀ = Top.no zero P₀ (λ f → f refl) tt (λ d → G₀.ℓ (G₀.g d)) (λ d → G₀.ℓ (G₀.g′ d)) ah₀
  (λ e → nd≢z (cong childS e))

no-path⊑₀ : G₀.ℓ G₀.ΩK ⊑ G₀.ℓ G₀.c′ → ⊥
no-path⊑₀ v = no-path₀ (wk v)

P₁ : L → Set
P₁ j = j ≡ one → ⊥

ah₁ : (c : Tr one) → AllIdx P₁ (G₁.ℓ (G₁.g′ c))
ah₁ zero         = tt , λ _ → tt , λ _ → tt
ah₁ (suc d)      = ⊕-all G₁.K (zero ⊕ ↑ one (suc d)) (tt , λ _ → tt , λ _ → tt)
  (⊕-all zero (↑ one (suc d)) tt (↑1-all (λ ()) (suc d)))
ah₁ (lim f a)    = tt , λ _ → tt , λ _ → tt
ah₁ (Ω q g)      = tt , λ _ → tt , λ _ → tt
ah₁ (up x c y e) = tt , λ _ → tt , λ _ → tt

no-path₁ : G₁.ℓ G₁.ΩK ≤ G₁.ℓ G₁.c′ → ⊥
no-path₁ = Top.no one P₁ (λ f → f refl) (tt , λ _ → tt) (λ d → G₁.ℓ (G₁.g d)) (λ d → G₁.ℓ (G₁.g′ d)) ah₁
  (λ e → nd≢z (cong childS (cong childS e)))

no-path⊑₁ : G₁.ℓ G₁.ΩK ⊑ G₁.ℓ G₁.c′ → ⊥
no-path⊑₁ v = no-path₁ (wk v)
```
