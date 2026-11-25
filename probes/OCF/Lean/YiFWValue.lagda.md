# B7 候选的值前序
> 原型的值验收。复用 `YiVWVal` 的值、前序与加法；新第一位置保持值前序，旧树嵌入保值。
> 跨槽位闭极限的值为 ω；这不是 EBO 或折叠强度验收，也未给新内部 View。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFWValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst)
import OCF.Lean.YiRWBlock as O
import OCF.Lean.YiVWVal as V
open import OCF.Lean.YiFWBlock
open import OCF.Lean.YiFWCompat

val : (ℓ : O.L) → T (Sig ℓ) → V.V ℓ
val ℓ zero = V.zero
val ℓ (suc x) = V.suc (val ℓ x)
val ℓ (lim f a) = V.lim (λ n → val ℓ (f n))
val ℓ (Ω p g) = V.Ω p (λ z → val ℓ (g z))
val ℓ (up x c y e) = val ℓ x V.⊹ V.valCh ℓ c y

mono : (ℓ : O.L) {x y : T (Sig ℓ)} → Lt (Sig ℓ) x y → val ℓ x V.≼ val ℓ y
mono ℓ ◃s = V.≼-suc (V.≼-refl _)
mono ℓ (◃l n) = V.≼l n (V.≼-refl _)
mono ℓ ◃w = V.≼Ω _ (V.≼-refl _)
mono ℓ (◃u x c y e) = V.⊹-mono (val ℓ x) (V.◁→≼ (V.valCh-mono₀ ℓ c y e))
mono ℓ (◃c x c d) = V.⊹-mono (val ℓ x) (V.◁→≼ (V.valCh-mono ℓ c d))
mono ℓ (◃t d e) = V.≼-trans (mono ℓ d) (mono ℓ e)
mono ℓ (◃σ {g = g} {g′ = g′} e h) = V.Ω≼ λ z →
  V.≼Ω (Iso₀.back (proj₂ e) z)
    (subst (λ t → val ℓ (g t) V.≼ val ℓ (g′ (Iso₀.back (proj₂ e) z)))
      (Iso₀.cv-back (proj₂ e) z) (mono ℓ (h (Iso₀.back (proj₂ e) z))))

embed-value : (ℓ : O.L) (x : O.Tr ℓ) → val ℓ (embed ℓ x) V.≈ V.val ℓ x
embed-value ℓ O.zero = V.≈-refl V.zero
embed-value ℓ (O.suc x) = V.s≈ (embed-value ℓ x)
embed-value ℓ (O.lim f a) = V.l≈ (λ n → embed-value ℓ (f n))
embed-value ℓ (O.Ω p g) = V.Ω≈ (λ z → embed-value ℓ (g z))
embed-value ℓ (O.up x c y e) =
  V.⊹-monoˡ (proj₁ (embed-value ℓ x)) (V.valCh ℓ c y) ,
  V.⊹-monoˡ (proj₂ (embed-value ℓ x)) (V.valCh ℓ c y)

natV : ∀ {ℓ} → ℕ → V.V ℓ
natV zero = V.zero
natV (suc n) = V.suc (natV n)

cross-nat-value : ∀ n → val flat (cross-nat n) V.≈ natV {flat} n
cross-nat-value zero = V.≈-refl V.zero
cross-nat-value (suc n) = V.s≈ (cross-nat-value n)

cross-node-value : ∀ n → val flat (cross-node n) V.≈ natV {flat} n
cross-node-value n =
  V.Ω≼ (λ _ → proj₁ (cross-nat-value n)) ,
  V.≼Ω (O.fromBr flat (cross-slotAt n) O.zero) (proj₂ (cross-nat-value n))

cross-limit-value : val flat cross-limit V.≈ V.lim (natV {flat})
cross-limit-value = V.l≈ cross-node-value
```
