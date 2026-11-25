# 变体的代价: 哪些已证的东西照样成立

> 判决: 编译定理, 无前提, 不读记号. [YiABFold](YiABFold.lagda.md) 上: 换基行的形状与换基律 (`row-rebᵛ`, `rebᵛ′`, 对照 `YiBLFold.Main.row-reb`, `rebᴮ′`; 辅助系统 `YiBLFold.Aux` 对任意底陈述, 原样可用); 底值不高于像 (`ψ-⊵ᵛ`); 外层的底不低于各层 Ω 树时替身的底也不低于 (`sub-ok`), 所以 `YiSVMono.Mono.Car` 一族 (对一切这样的底量化) 的承载结论对变体的替身成立 (`seenᵛ-car`).
> 外层在零树, 默认底上交来的 `Low` 逐点是 Ω 树, 此时替身的底逐点等于 `B₀` (`sub-B₀`); 塔第 0 项的闭项与 `YiBSFold` 的逐字相同 (`closed0`).
> 不给出什么: 逐点相等不给出两个替身的像相等 (要对底的函数外延, 没有做); 塔第 1 项起闭项是否相同没有检查 (不是 `refl`); 以 `foldᴮ` 为参数的分级实例与各 `low*` 定理要对变体重新实例化, 这里没有做.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiABCost where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
import OCF.Lean.YiRBSib as R
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiGIBlock using (ChTᵍ; upᵍ)
open import OCF.Lean.YiBLFold using (_⊴ᵗ_; cW-eq; module Aux)
open import OCF.Lean.YiSVMono using (_⊴_; ⊴r; ⊴◃; ⊴-◃; OKB; module Mono)
import OCF.Lean.YiABFold as V
open import OCF.Lean.YiABFold using (Low; subB; seenᵛ)
```

## 底值不高于像; 替身的底不低于 Ω 树

```agda
ψ-⊵ᵛ : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ)
  → proj₁ β ⊴ proj₁ (V.ψ ℓ o r B j w β x)
ψ-⊵ᵛ ℓ o r B j w β x with zl x
... | inj₁ refl = ⊴r
... | inj₂ d    = ⊴◃ (V.mono ℓ o r B j w β d)

⊴-tr : ∀ {ℓ} {x y z : Tr ℓ} → x ⊴ y → y ⊴ z → x ⊴ z
⊴-tr e ⊴r     = e
⊴-tr e (⊴◃ d) = ⊴◃ (⊴-◃ e d)

sub-ok : (j b : L) (ob : OkO j b) (D : Low j) → (∀ i u′ → proj₁ (Ωt i) ⊴ proj₁ (D i u′)) → OKB (subB j b ob D)
sub-ok j b ob D ok i q = cW-ind (λ Z → proj₁ (Ωt i) ⊴ proj₁ Z) (split j b ob q) (ok i) (λ _ → ⊴r)

sub-B₀ : (j b : L) (ob : OkO j b) (i : L) (q : i ≤ (j ⊕ b)) → subB j b ob (λ i′ _ → Ωt i′) i q ≡ B₀ (j ⊕ b) i q
sub-B₀ j b ob i q = cW-ind (λ Z → Z ≡ Ωt i) (split j b ob q) (λ _ → refl) (λ _ → refl)
```

## 换基行与换基律

参数同 `YiBLFold.Main`. `Dᵛ`: 行交给替身的 `Low`. 替身状态的底是 `subB`, 其余同 `Srᴮ`.

```agda
module Mainᵛ (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
             (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j)
             (eq : route S j c′ v ≡ inj₂ u) where
  open Aux j

  ℓ : L
  ℓ = nd (sΩ k) h
  r : Rb ℓ
  r = just S , rc
  w : j ≤ ℓ
  w = inc c′ v
  oj : Ok j
  oj = downOk (h c′) (proj₂ o c′) j v

  Dᵛ : Tr ℓ → Low j
  Dᵛ x i u′ = V.ψ ℓ o r B i (inc c′ (u′ ∙ v)) (B i (inc c′ (u′ ∙ v))) x

  row-rebᵛ : ∀ β x c y e → V.ψ ℓ o r B j w β (up x c y e)
    ≡ seenᵛ S j oj u (Dᵛ x) (V.ψ ℓ o r B j w β x) c ⊞ V.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y
  row-rebᵛ β x c y e = cW-eq (route S j c′ v) eq

  obᵛ : (c : Tr k) → OkO j (offsets S c)
  obᵛ c = raiseO (floor S) j (offsets S c) u (ok-offsets S c)

  Srᵛ : Tr⁺ j → (c : Tr k) → Tr ℓ → Stᴬ (j ⊕ offsets S c)
  Srᵛ β c x = rbs (offsets S c) (Ok⊕ j (offsets S c) oj (obᵛ c)) (subB j (offsets S c) (obᵛ c) (Dᵛ x)) (V.ψ ℓ o r B j w β x)

  seen-isᵛ : ∀ β c x → Φᴬ (Srᵛ β c x) (proj₁ (Ωt (j ⊕ offsets S c))) ≡ seenᵛ S j oj u (Dᵛ x) (V.ψ ℓ o r B j w β x) c
  seen-isᵛ β c x = refl

  rebᵛ′ : ∀ β c x (y : ChTᵍ ℓ c)
    → proj₁ (Φᴬ (Srᵛ β c x) (proj₁ (Ωt (j ⊕ offsets S c)))) ⊴ᵗ proj₁ (V.ψ ℓ o r B j w β (upᵍ x c y))
  rebᵛ′ β c x (y , e) = inj₂ (subst (λ Z → j ⊢ proj₁ (seenᵛ S j oj u (Dᵛ x) (V.ψ ℓ o r B j w β x) c) ◃ proj₁ Z)
    (sym (row-rebᵛ β x c y e))
    (+-mono _ (ι-mono j (proj₂ (V.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))))

  D-ok : OKB B → ∀ x i u′ → proj₁ (Ωt i) ⊴ proj₁ (Dᵛ x i u′)
  D-ok okB x i u′ = ⊴-tr (okB i (inc c′ (u′ ∙ v))) (ψ-⊵ᵛ ℓ o r B i (inc c′ (u′ ∙ v)) (B i (inc c′ (u′ ∙ v))) x)
```

`YiSVMono.Mono.Car` 对一切不低于 Ω 树的底量化, 所以它给出的承载结论对变体的替身照样成立.

```agda
  module _ (P Q : Tr j → Set)
      (P↑ : ∀ {x y} → P x → j ⊢ x ◃ y → P y) (Q↑ : ∀ {x y} → Q x → j ⊢ x ◃ y → Q y)
      (Q+ : ∀ (a : Tr j) {y} → Q y → Q (a + y)) where
    open Mono j oj P Q P↑ Q↑ Q+ using (Car)

    seenᵛ-car : OKB B → ∀ β x c → Car (offsets S c) → P (proj₁ (V.ψ ℓ o r B j w β x))
      → Q (proj₁ (seenᵛ S j oj u (Dᵛ x) (V.ψ ℓ o r B j w β x) c))
    seenᵛ-car okB β x c car hβ = car (obᵛ c) (R.rb-no _) (subB j (offsets S c) (obᵛ c) (Dᵛ x)) (V.ψ ℓ o r B j w β x)
      (sub-ok j (offsets S c) (obᵛ c) (Dᵛ x) (D-ok okB x)) hβ
```

## 闭项

塔第 0 项的闭项与 `YiBSFold` 的逐字相同. 第 1 项的等式不是 `refl` (两个折叠是两份定义, 链点是变量时不归约到同一个项), 没有另证.

```agda
closed0 : V.closed 0 ≡ BS.closed 0
closed0 = refl
```
