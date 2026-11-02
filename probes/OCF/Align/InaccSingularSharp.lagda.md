# 奇异下标的定时检验: 正则目标上的判决 `D♯` (不含记号)

> 底座, 结论在 [InaccSingular](InaccSingular.lagda.md). 导入链不含 `OCF.Align.EBO`. **`D♯` 只比 `Dᵐ` 多一条子句: 目标 `limᴼ 0 g`, 且 `j` 的 1-走步上没有 `limᴼ` 时, 进分支 `x = 1 + toT₀ j`.** 这里 `x` 不是模, 是 `j` 自身的读数; `limᴼ 0 toLv` (即 Ω₁) 上它是字面的逆, 不需要任何比较.
>
> `Fam F` 之外什么也不假设: `sharp-ok` 对任意规整族 `F` 与 Ω₁ 成立. 这是 "读数" 在树上唯一无需额外结构就正确的情形; 它不涉及奇异性, 见 [InaccSingular](InaccSingular.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccSingularSharp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccStrikeBase using (Funext; St; strip; toLvS; module Ext; module FoldS)
open import OCF.Align.InaccModulusBase
```

## §1 `D♯`

`cntb` 沿分支 1 走, 碰到 `limᴼ` 就答假. `toT₀` 把 `limᴼ` 落到 0 (`cntb` 为真时碰不到). 判决与 `Dᵐ` 一样只走一条路径, 不搜索. `k ≠ 0` 的 `limᴼ` 目标仍答 `rise`: 它们**不被声称正确**.

```agda
cntb : Lv → Bool
cntb zero       = true
cntb (suc a)    = cntb a
cntb (lim f)    = cntb (f 1)
cntb (limᴼ _ _) = false

toT₀ : Lv → Ordᴸ zero
toT₀ zero       = zero
toT₀ (suc a)    = suc (toT₀ a)
toT₀ (lim f)    = lim (λ n → toT₀ (f n))
toT₀ (limᴼ _ _) = zero

rdx : Lv → Ordᴸ zero
rdx j = suc (toT₀ j)

om♯ : ∀ j (g : Ordᴸ zero → Lv) → Bool → Verdict j (g (rdx j)) → Verdict j (limᴼ zero g)
om♯ j g true  (pen r b) = pen (inj₂ (rdx j , r)) b
om♯ j g true  rise      = rise
om♯ j g false _         = rise

Dm♯ : ℕ → (j i : Lv) → Verdict j i
Dm♯ μ j zero              = rise
Dm♯ μ j (suc i)           = svᵐ j i (samᵐ j i) (Dm♯ μ j i)
Dm♯ μ j (lim h)           = lvᵐ μ j h (Dm♯ μ j (h μ))
Dm♯ μ j (limᴼ zero g)     = om♯ j g (cntb j) (Dm♯ μ j (g (rdx j)))
Dm♯ μ j (limᴼ (suc _) _)  = rise
Dm♯ μ j (limᴼ (lim _) _)  = rise
Dm♯ μ j (limᴼ (limᴼ _ _) _) = rise

D♯ : Oracle
D♯ j i = Dm♯ (suc (wk j)) j i
```

## §2 `toT₀` 是 `toLv` 在族内的字面逆

```agda
module OnFam♯ {F : Lv → Set} (fam : Fam F) (fe : Funext) where
  open Fam fam
  open OnFam fam
  open CastR fe
  open Ext fe using (toLv-strip)

  cntb-F : ∀ j → F j → cntb j ≡ true
  cntb-F zero       _  = refl
  cntb-F (suc a)    fj = cntb-F a (f-suc fj)
  cntb-F (lim f)    fj = cntb-F (f 1) (f-lim fj 1)
  cntb-F (limᴼ _ _) fj = ⊥-elim (f-no fj)

  toT₀-inv : ∀ j → F j → toLv (toT₀ j) ≡ j
  toT₀-inv zero       _  = refl
  toT₀-inv (suc a)    fj = cong Lv.suc (toT₀-inv a (f-suc fj))
  toT₀-inv (lim f)    fj = cong Lv.lim (fe (λ n → toT₀-inv (f n) (f-lim fj n)))
  toT₀-inv (limᴼ _ _) fj = ⊥-elim (f-no fj)

  -- 在无 `limᴼ` 的目标上 `D♯` 就是 `Dᵐ`
  agree : ∀ μ j i → F i → Dm♯ μ j i ≡ Dm μ j i
  agree μ j zero       _  = refl
  agree μ j (suc i)    fi = cong (svᵐ j i (samᵐ j i)) (agree μ j i (f-suc fi))
  agree μ j (lim h)    fi = cong (lvᵐ μ j h) (agree μ j (h μ) (f-lim fi μ))
  agree μ j (limᴼ _ _) fi = ⊥-elim (f-no fi)
```

## §3 Ω₁ 作目标

`g₁ y = toLvS (strip y)` 是 `L Ω₁` 的分支函数 (与 `toLv` 只差 `Funext`, `toLv-strip`). `sharp-ok`: 族内的 `j` 对 Ω₁ 是 `pen`, 路径字面命中; Ω₁ 对自身与对族内目标都是 `rise`.

```agda
  g₁ : Ordᴸ zero → Lv
  g₁ y = toLvS (strip y)

  T₁ : Lv
  T₁ = limᴼ zero g₁

  rd≡ : ∀ j → F j → g₁ (toT₀ j) ≡ j
  rd≡ j fj = trans (toLv-strip (toT₀ j)) (toT₀-inv j fj)

  cast-strip : ∀ {i j} → i ≡ j → F j → ∀ y → strip (cast i j y) ≡ strip y
  cast-strip {j = j} refl fj y = cong strip (cast-id j fj y)

  -- 把 `sam` 的值暴露出来; `i` 是抽象的, 所以不必在大项上做 `with`
  pen-at : ∀ μ j i → i ≡ j → F j → Σ (Ordᴸ i → Ordᴸ j) λ b → (Dm♯ μ j (suc i) ≡ pen (inj₁ tt) b) × (∀ y → strip (b y) ≡ strip y)
  pen-at μ j i e fj with samᵐ j i | sam≡ j i e fj
    where
      sam≡ : ∀ j i → i ≡ j → F j → samᵐ j i ≡ true
      sam≡ j .j refl fj = sam-refl j fj
  ... | true | refl = cast i j , refl , cast-strip e fj

  pen♯ : ∀ j → F j → PenOK (D♯ j T₁)
  pen♯ j fj with cntb j | cntb-F j fj
  ... | true | refl with pen-at (suc (wk j)) j (g₁ (toT₀ j)) (rd≡ j fj) fj
  ...   | b , q , s = record
    { rr = inj₂ (rdx j , inj₁ tt) ; bb = b ; vq = cong (om♯ j g₁ true) q ; lb = rd≡ j fj ; sb = s }

  -- `limᴼ` 作节点时, 无 `limᴼ` 的目标上一律 `rise`
  rise-O : ∀ μ k (g : Ordᴸ k → Lv) i → F i → Dm♯ μ (limᴼ k g) i ≡ rise
  rise-O μ k g zero    _  = refl
  rise-O μ k g (suc i) fi rewrite rise-O μ k g i (f-suc fi) = refl
  rise-O μ k g (lim h) fi rewrite rise-O μ k g (h μ) (f-lim fi μ) = refl
  rise-O μ k g (limᴼ _ _) fi = ⊥-elim (f-no fi)

  rise-self : D♯ T₁ T₁ ≡ rise
  rise-self = refl

  -- **族内: `D♯` 与 `Dᵐ` 相同, 所以正确性就是 `Dᵐ-lt`, `Dᵐ-gt`, `Dᵐ-eq`.**
  lt♯ : ∀ {j i} → F j → F i → Nd j i → PenOK (D♯ j i)
  lt♯ {j} {i} fj fi n = subst PenOK (sym (agree (suc (wk j)) j i fi)) (Dᵐ-lt fj fi n)

  gt♯ : ∀ {j i} → F j → F i → Nd i j → D♯ j i ≡ rise
  gt♯ {j} {i} fj fi n = trans (agree (suc (wk j)) j i fi) (Dᵐ-gt fj fi n)

  eq♯ : ∀ j → F j → D♯ j j ≡ rise
  eq♯ j fj = trans (agree (suc (wk j)) j j fj) (Dᵐ-eq j fj)
```

## §4 `rise` 只在轨道上用参数函数

`ψ_i(limᵢ ℓ f)` 走 `rise` 时只用到 `f` 在轨道 `Ω_ℓ, ψ_ℓ(f(Ω_ℓ)), …` 上的值. `rise-forgets`: 两个函数在轨道上相同, 折叠的结果就字面相同. 所以 `rise` 节点**不可逆**: 从树上读不回 `f` 在轨道外的值; 读数至多读到轨道. 对任意判决成立, 不提记号. 这解释了为什么 "读被折叠的参数" 不是 `toT` 那样的同态 (`InaccSingularRead` §3). 它不是不可能性定理: 标准形的 `f` 可能由轨道决定, 只是没有一条树上的规则说明怎么决定.

```agda
module Forget (fe : Funext) (D : Oracle) where
  open FoldS D

  orb : ∀ {ℓ} → (Ordᴸ ℓ → St) → ℕ → Ordᴸ ℓ
  orb {ℓ} f n = iter (λ x → ψS {ℓ} (f x)) (Ω ℓ) n

  orb-eq : ∀ {ℓ} (f f′ : Ordᴸ ℓ → St) → (∀ n → f (orb f n) ≡ f′ (orb f n)) → ∀ n → orb f n ≡ orb f′ n
  orb-eq f f′ a zero    = refl
  orb-eq {ℓ} f f′ a (suc n) =
    trans (cong (ψS {ℓ}) (a n)) (cong (λ z → ψS {ℓ} (f′ z)) (orb-eq f f′ a n))

  rise-forgets : ∀ {i ℓ} (f f′ : Ordᴸ ℓ → St) → (∀ n → f (orb f n) ≡ f′ (orb f n)) →
                 dispS {i} f rise ≡ dispS {i} f′ rise
  rise-forgets {i} f f′ a = cong Tree.lim (fe (λ n →
    trans (cong (ψS {i}) (a n)) (cong (λ z → ψS {i} (f′ z)) (orb-eq f f′ a n))))
```
