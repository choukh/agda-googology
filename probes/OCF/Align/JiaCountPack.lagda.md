# 甲脚手架：构造时携码的可数分支

本篇只处理 S1 的奇异 Ω_Ω 所需的可数输入。`Named t` 是在构造时
带码 t 的树，不接受一个事先给定的 raw 树。极限构造子的分支带码
逐项读自记号，属于甲的脚手架，不是乙的定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaCountPack where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.EboLeanDef using (T; ψ; natT; sucT; Ωt; Ωs; cof; cω; fsn; _<ᵀ_; []<; hd<; lv<)
open import OCF.Align.EboLeanBase using (NF; n[]; nf-ψ; nf-Ω; Ctbl; c[]; c∷)
open import OCF.Align.EboLean3Base using (nf-suc)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase using (Tree; coe; module Layer)
open import OCF.Align.JiaAuditClosure using (G-one)

data Named : T → Set where
  nz : Named []
  ns : ∀ {t} → Named t → Named (sucT t)
  nl : ∀ {t} → NF t → Ctbl t → cof t ≡ cω →
    (∀ n → Named (fsn t n)) → Named t

normal : ∀ {t} → Named t → NF t
normal nz = n[]
normal (ns x) = nf-suc (normal x)
normal (nl nt ct e f) = nt

Ctbl-suc : ∀ {t} → Ctbl t → Ctbl (sucT t)
Ctbl-suc c[] = c∷ c[]
Ctbl-suc (c∷ ct) = c∷ (Ctbl-suc ct)

countable : ∀ {t} → Named t → Ctbl t
countable nz = c[]
countable (ns x) = Ctbl-suc (countable x)
countable (nl nt ct e f) = ct

countable-bound : ∀ {t} → Ctbl t → t <ᵀ Ωs []
countable-bound c[] = []<
countable-bound (c∷ ct) = hd< (lv< []<)

Pack : Set
Pack = Σ T Named

erase : ∀ {t} (a : Acc′ []) → Named t → Tree [] a
erase a nz = Layer.z
erase a (ns x) = Layer.s (erase a x)
erase a (nl nt ct e f) = Layer.l (λ n → erase a (f n))
```

## 码树对应及可及搬运

下面的关系逐构造子约束原树；不能给任意树随手附一个码。
它只用于甲脚手架。搬运保持这条关系，不要求两个可及证明相等，
也不要求两个分支函数相等。

```agda
data Tracks (a : Acc′ []) : T → Tree [] a → Set where
  tz : Tracks a [] Layer.z
  ts : ∀ {t x} → Tracks a t x → Tracks a (sucT t) (Layer.s x)
  tl : ∀ {t f} → cof t ≡ cω →
    (∀ n → Tracks a (fsn t n) (f n)) → Tracks a t (Layer.l f)

erase-tracks : ∀ {t} (a : Acc′ []) (x : Named t) → Tracks a t (erase a x)
erase-tracks a nz = tz
erase-tracks a (ns x) = ts (erase-tracks a x)
erase-tracks a (nl nt ct e f) = tl e (λ n → erase-tracks a (f n))

tracks-coe : (a a′ : Acc′ []) → ∀ {t x} → Tracks a t x → Tracks a′ t (coe a a′ x)
tracks-coe (acc h) (acc h′) tz = tz
tracks-coe (acc h) (acc h′) (ts p) = ts (tracks-coe (acc h) (acc h′) p)
tracks-coe (acc h) (acc h′) (tl e p) = tl e (λ n → tracks-coe (acc h) (acc h′) (p n))

suc-nat : ∀ n → sucT (natT n) ≡ natT (suc n)
suc-nat zero = refl
suc-nat (suc n) = cong (ψ [] [] ∷_) (suc-nat n)

nat : (n : ℕ) → Named (natT n)
nat zero = nz
nat (suc n) = subst Named (suc-nat n) (ns (nat n))

-- 极限构造子的前提也有实填实例，不只给有限输入。
omega-code : T
omega-code = ψ [] (Ωt []) ∷ []

omega-fs : ∀ n → fsn omega-code n ≡ natT n
omega-fs zero = refl
omega-fs (suc n) = cong (ψ [] [] ∷_) (omega-fs n)

omega-named : Named omega-code
omega-named = nl
  (nf-ψ n[] (nf-Ω n[]) (λ p → subst (_<ᵀ Ωt []) (sym (G-one p)) []<))
  (c∷ c[]) refl (λ n → subst Named (sym (omega-fs n)) (nat n))
```

`nat` 与 `omega-named` 给有限及极限构造的实例。没有定义 raw 树到 `Pack` 的函数，
也没有声称 `Pack` 覆盖第零层的全部 raw 树。
