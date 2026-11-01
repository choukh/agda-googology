# 范数基本列与 F：证书上的快速增长层级

流水线最后一段：`λ[n] := max{β ∈ OT : β ≺ λ, Nβ ≤ Nλ + n}`（范数基本列，[../RESEARCH.md](../RESEARCH.md) §116、§120.4 的做法，绕开零／后继／极限的判定），`F` 沿 `Acc` 证书结构递归。这里只需要 `λ[n] ≺ λ`（候选表的过滤保证）与 `λ[n] ∈ OT`；候选表的**完整性**（不漏）留待另证——它决定 λ[n] 是不是"真正的最大值"，不影响 F 是全函数。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.FGH (F : OTFacts) where

open OTFacts F

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.Arith
open import Mahlo.Inacc.BoolLemmas
open import Mahlo.Inacc.Enum
open import Mahlo.Inacc.WO.OrderLemmas F
open import Mahlo.Inacc.WO.Main F

open import Data.Nat.Base using (ℕ; zero; _≤ᵇ_; _*_; s≤s; z≤n) renaming (suc to sucℕ; _+_ to _+ℕ_)
open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
```

## 1. 枚举

见 [Enum](Enum.lagda.md)（`enumT`、`filterB`）。

## 2. λ[n]

候选谓词：`OT`、`≺ λ`、`N ≤ N λ + n`。在 `enumT (3 (Nλ + n) + 1)` 里过滤（`size ≤ 3N + 1` 是 ExtOT §8 的定量范数性，这里作为上界的选择）。候选表的头总是 0（λ ≠ 0 时 0 是候选），所以非空；取 `lt`-最大者。

```agda
cand : Tm → ℕ → Tm → Bool
cand lam n β = isOT β ∧ lt β lam ∧ (N β ≤ᵇ N lam +ℕ n)

cands : Tm → ℕ → List Tm
cands lam n = zer ∷ filterB (cand lam n) (enumT (3 * (N lam +ℕ n) +ℕ 1))

-- 非空表的 lt-最大者
maxGo : Tm → List Tm → Tm
maxGo m []       = m
maxGo m (y ∷ ys) = maxGo (if lt m y then y else m) ys

_[_] : Tm → ℕ → Tm
lam [ n ] = maxGo zer (filterB (cand lam n) (enumT (3 * (N lam +ℕ n) +ℕ 1)))
```

`λ[n] ≺ λ`、`λ[n] ∈ OT`（λ ≠ 0）：`maxGo m ys` 返回 `m ∷ ys` 中的某个元素；表中元素都满足 `cand`；0 满足 `cand`。

```agda
data AllB (p : Tm → Bool) : List Tm → Set where
  []  : AllB p []
  _∷_ : ∀ {x xs} → p x ≡ true → AllB p xs → AllB p (x ∷ xs)

filterB-all : ∀ p xs → AllB p (filterB p xs)
filterB-all p []       = []
filterB-all p (x ∷ xs) with p x in e
... | true  = e ∷ filterB-all p xs
... | false = filterB-all p xs

maxGo-prop : ∀ {p} m ys → p m ≡ true → AllB p ys → p (maxGo m ys) ≡ true
maxGo-prop m []       pm []        = pm
maxGo-prop {p} m (y ∷ ys) pm (py ∷ ps) = maxGo-prop (if lt m y then y else m) ys (pick (lt m y)) ps
  where
    pick : ∀ b → p (if b then y else m) ≡ true
    pick true  = py
    pick false = pm

cand-0 : ∀ lam n → NZ lam → cand lam n zer ≡ true
cand-0 lam n nz =
  ∧-intro {x = isOT zer} {y = lt zer lam ∧ (N zer ≤ᵇ N lam +ℕ n)} refl
    (∧-intro {x = lt zer lam} {y = N zer ≤ᵇ N lam +ℕ n} (lt≡ (⪯-sub⇒≺ (size-NZ lam nz) (0⪯ lam))) refl)

cand-out : ∀ lam n β → cand lam n β ≡ true → isOT β ≡ true × lt β lam ≡ true
cand-out lam n β e =
  let (e₁ , e₂) = ∧-true {x = isOT β} {y = lt β lam ∧ (N β ≤ᵇ N lam +ℕ n)} e
      (e₃ , _)  = ∧-true {x = lt β lam} {y = N β ≤ᵇ N lam +ℕ n} e₂
  in e₁ , e₃

[]-cand : ∀ lam n → NZ lam → cand lam n (lam [ n ]) ≡ true
[]-cand lam n nz =
  maxGo-prop zer (filterB (cand lam n) (enumT (3 * (N lam +ℕ n) +ℕ 1))) (cand-0 lam n nz)
             (filterB-all (cand lam n) (enumT (3 * (N lam +ℕ n) +ℕ 1)))

[]-OT : ∀ lam n → NZ lam → OT (lam [ n ])
[]-OT lam n nz = ot! (proj₁ (cand-out lam n (lam [ n ]) ([]-cand lam n nz)))

[]-≺ : ∀ lam n → NZ lam → lam [ n ] ≺ lam
[]-≺ lam n nz = lt! (proj₂ (cand-out lam n (lam [ n ]) ([]-cand lam n nz)))
```

## 3. F 与大数

`F_0(k) = k + 1`；`F_α(k) = F_{α[k]}^{k+1}(k)`（α ≠ 0）。递归沿证书 `acc h`：`h (α[k] ∈ OT) (α[k] ≺ α)` 是 `acc h` 的结构子项。

```agda
iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f zero     x = x
iter f (sucℕ n) x = f (iter f n x)

F′ : ∀ α → Acc α → ℕ → ℕ
F′ zer     _       k = sucℕ k
F′ (a ▹ p) (acc h) k = iter (F′ ((a ▹ p) [ k ]) (h ([]-OT (a ▹ p) k tt) ([]-≺ (a ▹ p) k tt))) (sucℕ k) k
```

端点族 `endpt n = ψ_{Ω₁}Ω_{I+n}` 单调，所以每个端点本身可达；`ψ_{Ω₁}Ω_{I+ω}[n] := endpt n` 就是 |ML₁W| 的基本列，对角化得 \(F_{\psi_{\Omega_1}\Omega_{\mathrm I+\omega}}(n)\)。

```agda
endpt≺suc : ∀ n → endpt n ≺ endpt (sucℕ n)
endpt≺suc n = ψκ-mono (endpt-OT n) (endpt-OT (sucℕ n)) (ΩI+≺suc n)

Acc-endpt′ : ∀ n → Acc (endpt n)
Acc-endpt′ n = Acc-endpt (sucℕ n) (endpt-OT n) (endpt≺suc n)

-- F_{endpt n}(k)
Fₙ : ℕ → ℕ → ℕ
Fₙ n k = F′ (endpt n) (Acc-endpt′ n) k

-- 大数：F_{ψ_{Ω₁}Ω_{I+ω}}(n) := F_{endpt n}(n)
BIG : ℕ → ℕ
BIG n = Fₙ n n

-- 这是一个 Agda 里定义出来的自然数（值不可求）
𝔑 : ℕ
𝔑 = BIG 8
```

`BIG`、`𝔑` 的类型能检，值不能求；它们只相对于 `F : OTFacts` 存在——构造出 `OTFacts` 后即无条件。
