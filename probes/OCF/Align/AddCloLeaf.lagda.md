# 换一步: 叶子上的一步跨世界

> 不含记号, 不含旧树. 入口 [AddClo](AddClo.lagda.md). `upLeaf`: 世界 $W_2$ 里有节点 $\sum_{z:j}1$ ($r:j\ll W_2$). 目标不高于 $j$ 时, 这个节点是链, 第一段就是状态在 $j$ 上的差. 所以世界 $j$ 里任何 $\trianglelefteq$ 这个差的输入, 都被这个节点盖住. 不用证明层的算术, 不用证书. 这就是 "$\Omega_{j+1}$ 比 $\Omega_j$ 的所有和都大" 的字面形式.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddCloLeaf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg; ⊲-tr; lg⊲; z⊲; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSum using (D; n0; n1; _⨾_; nl; ni; Ωd; AccL; acc; accL; module Fold)
open import OCF.Align.AddCloRel using (Rel; r0; r1; r⨾; rf; rs; rp; rn; rt; ri; reflΩ; oneΩ; SubS; dec-self; lg-tr; module Main)
```

## §1 比较

```agda
cmp-rise : ∀ {j t L} (r : j ≪ L) (τ : t ⊲ j) (w : Lg L) → cmpN r (⊲-tr τ (≪⊲ r)) w ≡ rise τ
cmp-rise C.zero τ w = refl
cmp-rise (C.suc r) τ w = cmp-rise r τ w
cmp-rise (C.lim n r) τ (st , w) rewrite dec-self n = cmp-rise r τ (w n)

⊲-idl : ∀ {a b} (c : a ⊲ b) → ⊲-tr C.self c ≡ c
⊲-idl C.self = refl
⊲-idl (C.suc c) = cong C.suc (⊲-idl c)
⊲-idl (C.lim n c) = cong (C.lim n) (⊲-idl c)
```

## §2 主定理

```agda
module Leaf (W₂ : A) (lW₂ : Lg W₂) (S₁ S₂ : ∀ {t} → D t → D t) (hS : SubS S₁ S₂) {j : A} (r : j ≪ W₂) where
  c : j ⊲ W₂
  c = ≪⊲ r

  open Main j W₂ c lW₂ S₁ S₂ public

  hStep : ∀ {k} {a : D k} {b : D k} {Y : St₁} {Y′ : St₂} → Rel k a b → RS Y Y′ → RS (F₁.Step Y) (F₂.Step Y′)
  hStep {Y = Y} {Y′} _ hY {t} τ =
    subst (λ w → Rel t (S₁ (Ωd t C.self (lg⊲ τ lW₁) ⨾ Y τ)) (S₂ (Ωd t C.self w ⨾ Y′ (⊲-tr τ c))))
      (sym (lg-tr τ c lW₂))
      (hS (oneΩ t C.self (lg⊲ τ lW₁)) (oneΩ t C.self (lg⊲ τ lW₁)) (r⨾ (reflΩ t C.self (lg⊲ τ lW₁)) (hY τ)))

  upLeaf : ∀ (ac₁ : AccL j) {x w′} {Y : St₁} {Y′ : St₂} → Rel j x (Y′ c) → RS Y Y′ → ∀ {t} (τ : t ⊲ j) →
           Rel t (F₁.Run ac₁ C.self (λ _ Z → F₁.Step Z) n0 x Y τ)
                 (F₂.Run (accL W₂) C.self (λ _ Z → F₂.Step Z) w′ (ni r (λ _ → n1)) Y′ (⊲-tr τ c))
  upLeaf ac₁ {x} {w′} {Y} {Y′} d hY {t} τ =
    subst (λ c₀ → Rel t L (F₂.RunK (accL W₂) (f₂ r) C.self (λ _ Z → F₂.Step Z) w′ r (λ _ → n1) Y′ (⊲-tr τ c) c₀))
      (sym (cmp-rise r τ lW₂))
      (rn 0 (main ac₁ (f₂ r) C.self c (⊲-idl c) (λ _ Z → F₁.Step Z)
               (F₂.Ai (accL W₂) r C.self (f₂ r) (λ _ Z → F₂.Step Z) w′ (λ _ → n1))
               (λ {a} {b} {Z} {Z′} g hZ → hStep {a = a} {b} {Z} {Z′} g hZ) r0 d hY τ))
    where
    L = F₁.Run ac₁ C.self (λ _ Z → F₁.Step Z) n0 x Y τ
    f₂ : ∀ {i} → i ≪ W₂ → AccL i
    f₂ {i} q with accL W₂
    ... | acc g = g q
```
