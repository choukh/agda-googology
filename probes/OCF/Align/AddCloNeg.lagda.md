# 换一步: 加法封闭不是树逼的

> 不含记号, 不含旧树. 入口 [AddClo](AddClo.lagda.md).
>
> 1. `Req S`: 这一路能写出的树侧要求. 回灌 (`Lg`), 层严格 (`SA`), 折叠对输入和状态单调 (`SubS S S`, 由 [AddCloRel](AddCloRel.lagda.md) 的 `main` 推到整个折叠), 一步保持严格 (`SSt`). 链的行, 和的行对一切 `S` 定义性地相同 ([TLRule](TLRule.lagda.md) 的 `Rows`).
> 2. `req-·2`, `req-+1`: $S=\cdot2$ 和 $S=+1$ 满足全部要求. `no-clo-·2`, `no-clo-+1`: 它们的 $\psi_0(1)=2$, 不对加法封闭. **所以这些树侧要求推不出 "输出对加法封闭".**
> 3. `succ-spec`, `ω+ω<ω·ω`: "取最小的闭包点" 这条原则 (`chain-least`, `ω-uniq` 同形) 也不定下 $S$: 换成对后继封闭, 最小点是 $c+\omega$, 与 $c\cdot\omega$ 不同值. 原则只把选择从 $S$ 挪到 "对什么封闭".
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddCloNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
open import OCF.Align.TLRuleSum using (D; n1; _⨾_; nl; module Gen; ω⋅)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; irr; Clo; _⊞_; ⊞-mono; z⊞; ωm; mul; ≤lim⁻; ω-clo)
open import OCF.Align.AddCloRel using (Rel; r1; rp; SubS)
open import OCF.Align.AddCloStr using (SA; SSt; SSt-ω; SSt-·2; SSt-+1; module Cell)
```

## §1 要求

```agda
record Req (S : ∀ {t} → D t → D t) : Set where
  field
    lg   : ∀ y w → Lg (Gen.Ψ S y w)
    sa   : ∀ n → SA (proj₁ (Gen.cell S n))
    mono : SubS S S
    sst  : SSt S

req : ∀ (S : ∀ {t} → D t → D t) → SubS S S → (h : SSt S) → Req S
req S m h = record { lg = Gen.Lg-Ψ S ; sa = Cell.SA-cell S h ; mono = m ; sst = h }

·2ˢ +1ˢ : ∀ {t} → D t → D t
·2ˢ c = c
+1ˢ _ = n1

req-·2 : Req ·2ˢ
req-·2 = req ·2ˢ (λ _ _ q → q) SSt-·2

req-+1 : Req +1ˢ
req-+1 = req +1ˢ (λ _ _ _ → r1) SSt-+1

req-ω : Req ω⋅
req-ω = req ω⋅ (λ _ _ q → rp (λ _ → q)) SSt-ω
```

## §2 反例

```agda
two : A
two = asuc (asuc azero)

ψ1-·2 : Gen.Ψ ·2ˢ azero tt ≡ two
ψ1-·2 = refl

ψ1-+1 : Gen.Ψ +1ˢ azero tt ≡ two
ψ1-+1 = refl

no-clo-2 : ¬ Clo two
no-clo-2 C = irr two (C {asuc azero} {asuc azero} (≤-refl two) (≤-refl two))   -- 1 ⊞ 1 = 2
no-clo-·2 : ¬ Clo (Gen.Ψ ·2ˢ azero tt)
no-clo-·2 = no-clo-2

no-clo-+1 : ¬ Clo (Gen.Ψ +1ˢ azero tt)
no-clo-+1 = no-clo-2

-- 对照: S = ω⋅ 的 ψ₀(1) 是 ω, 对加法封闭
```

## §3 换成对后继封闭

```agda
Clo₁ : A → Set
Clo₁ y = ∀ {u} → asuc u ≤ y → asuc (asuc u) ≤ y

nat : ℕ → A
nat zero = azero
nat (suc n) = asuc (nat n)

ωA : A
ωA = alim nat

succ-clo : ∀ c → Clo₁ (c ⊞ ωA)
succ-clo c p with ≤lim⁻ p
... | n , q = ≤l (suc n) (s≤ q)

succ-least : ∀ {c y} → Clo₁ y → asuc c ≤ y → c ⊞ ωA ≤ y
succ-least {c} {y} C h = l≤ (λ n → ≤-trans (≤-suc (≤-refl _)) (go n))
  where
  go : ∀ n → asuc (c ⊞ nat n) ≤ y
  go zero = h
  go (suc n) = C (go n)

succ-spec : ∀ c → Clo₁ (c ⊞ ωA) × (asuc c ≤ c ⊞ ωA) × (∀ {y} → Clo₁ y → asuc c ≤ y → c ⊞ ωA ≤ y)
succ-spec c = succ-clo c , ≤l 1 (≤-refl _) , succ-least

-- ω+ω 与 ω·ω 不同值: 两条原则给不同的 ψ(a+1)
ω+ω<ω·ω : asuc (ωA ⊞ ωA) ≤ ωm ωA
ω+ω<ω·ω = ≤l 3 (≤l 1 (s≤ (⊞-mono {ωA} {mul ωA 1} {ωA} {ωA} (z⊞ ωA) (≤-refl ωA))))
  where
  _ : mul ωA 3 ≡ ((azero ⊞ ωA) ⊞ ωA) ⊞ ωA
  _ = refl
```
