# 验收 (比较表那一行): 塔第 1 项上目标第 2 层的判据

> 验收文件 (读记号), 不进成品. 编译定理, 无前提: 比较表那一行 (`YiTBRow`, 表 `rb1`) 对一切 n 过 `YiRBCrit.CritAt` (`tb-crit`, 含 n = 0, 1, 2; 关系是不带项序封闭的 `YiCLFam.M 2`); 封闭的关系 `M̂` 上, 孩子 `nat m` 对着 ψ₂(Ω_n), n ≤ m (`fiñᴰ`).
> 层号 (`lvlᴰ`): n ≥ 3 时那一支是孩子层 `fn n` 的 Ω 树在 `fn n` 上朝第 2 层的折叠, 路径是 `inc` 链; n ≤ 2 时是孩子的 Ω 树嵌进第 2 层后的自身折叠. 兄弟孩子写法在 `fn (n + 2)` 上折 (`YiRBCrit.eqˢ`).
> 边界: 表 `rb1` 在 ℕ 极限形状的孩子处没有条目, 那一支逐字是主线原行 (`tb-lim`), 判据在那里为假 (`tb-lim-neg`, 引 `YiRCNeg.negS`). 不涉及上界. 带 ℕ 极限孩子的表见 [YiTBLim](YiTBLim.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTBCrit where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow hiding (nat; fn; h₁)
import OCF.Lean.YiTBRow as T
open import OCF.Lean.YiTBFam
open import OCF.Lean.YiRBFam using (tc; OKB)
open import OCF.Lean.YiRBCrit using (two; h₁; blk; CritAt; hβ₂)
import OCF.Lean.YiRBCrit as C
open import OCF.Lean.YiRLNeg using (negˢ)
open import OCF.Lean.YiRCNeg using (negS; Sm+ι; kΩ)
open import OCF.Lean.YiKVRel using (M⁰; mz; mU; _⊴_; ⊴r)
import OCF.Align.EboLeanDef as E
open E using (natT)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiCLFam using (nat; fn; M; Mβ)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth; ΩJ)
open import OCF.Lean.YiDCRel using (Ω≤; app≤)
open import OCF.Lean.YiMHRel using (M̂; ĉ)
```

## 那一支与它的三种情形

`gᴰ c`: 塔第 1 项的 Ω 树第 c 支经孩子 2 朝第 2 层的那一行. 字面地是按表的条目分三种 (`gᴰ-eq`, `refl`).

```agda
o1 : (c : Tr zero) → Ok (h₁ c)
o1 c = proj₂ (Ok-tw 1) c

gᴰ : Tr zero → Tr⁺ two
gᴰ c = ψ (tw 1) (Ok-tw 1) rb1 (B₀ (tw 1)) two (inc (nat 2) self) (Ωt two) (blk c)

Bc : (c : Tr zero) → Base (h₁ c)
Bc c i u = B₀ (tw 1) i (inc c u)

okBc : (c : Tr zero) → OKB (Bc c)
okBc c i u = ⊴r

Fᴰ : (c : Tr zero) → two ≤ h₁ c → Tr⁺ two
Fᴰ c u = ψ (h₁ c) (o1 c) (rb-no _) (Bc c) two (self ∙ u) (Ωt two) (proj₁ (Ωt (h₁ c)))

Gᴰ : (c : Tr zero) → h₁ c ≤ two → Tr⁺ two
Gᴰ c u = ψ two (o1 (nat 2)) (rb-no _) (Bc (nat 2)) two self (Ωt two) (proj₁ (emb two (o1 (nat 2)) u (Ωt (h₁ c))))

Hᴰ : (c : Tr zero) → Tr⁺ two
Hᴰ c = Ωt two ⊞ ψ₀ʳ (h₁ c) (o1 c) (rb-no _) (proj₁ (Ωt (h₁ c)))

gᴰ-eq : (c : Tr zero) → gᴰ c ≡ dW (tb c (nat 2)) (Fᴰ c) (Gᴰ c) (Hᴰ c)
gᴰ-eq c = refl
```

## n ≥ 3: 在孩子自己的层上折, 没有偏移

表的条目在 `YiTBRow.nat` 上算出 (`tb-nat`); 这里的 `nat` 是 `YiCLFam` 的, 两者逐点相等而不是定义相等, 条目连同路径成对地搬过来 (`PE`).

```agda
Pk : ∀ k → two ≤ fn (suc (suc k))
Pk zero    = self
Pk (suc k) = inc tt (Pk k)

AP : Set
AP = Σ (Tr zero) λ a → two ≤ h₁ (suc (suc a))

stepP : AP → AP
stepP (a , p) = suc a , inc tt p

PE : ∀ k → _≡_ {A = AP} (T.nat k , from0 (λ i → T.fn (suc (suc i))) (λ i → inc tt self) k) (nat k , Pk k)
PE zero    = refl
PE (suc k) = cong stepP (PE k)

Dᵉ : AP → Set
Dᵉ (a , p) = tb (suc (suc (suc a))) (nat 2) ≡ just (inj₁ (inc tt p))

tb3 : ∀ k → tb (nat (suc (suc (suc k)))) (nat 2) ≡ just (inj₁ (inc tt (Pk k)))
tb3 k = subst Dᵉ (PE k) (tb-nat (suc (suc (suc k))) 2)

sbk : ∀ k → Sb (suc (suc k)) 2
sbk zero    = s0
sbk (suc k) = ss (sbk k)

pathk : ∀ k → self ∙ Pk k ≡ pth (sbk k)
pathk zero    = refl
pathk (suc k) = cong (inc {s = sS} {h = λ _ → fn (suc (suc k))} tt) (pathk k)

lvlᴰ : ∀ k → gᴰ (nat (suc (suc (suc k))))
     ≡ ψ (fn (suc (suc (suc k)))) (o1 (nat (suc (suc (suc k))))) (rb-no _) (Bc (nat (suc (suc (suc k))))) two
         (inc tt (pth (sbk k))) (Ωt two) (proj₁ (Ωt (fn (suc (suc (suc k))))))
lvlᴰ k =
  subst (λ e → dW e (Fᴰ (nat n)) (Gᴰ (nat n)) (Hᴰ (nat n))
             ≡ ψ (fn n) (o1 (nat n)) (rb-no _) (Bc (nat n)) two (inc tt (pth (sbk k))) (Ωt two) (proj₁ (Ωt (fn n))))
    (sym (tb3 k))
    (cong (λ p → ψ (fn n) (o1 (nat n)) (rb-no _) (Bc (nat n)) two (inc tt p) (Ωt two) (proj₁ (Ωt (fn n)))) (pathk k))
  where
  n = suc (suc (suc k))

crit3 : ∀ k → CritAt gᴰ (suc (suc (suc k)))
crit3 k =
  subst (λ g → M 2 (ψᴺ 2 (Ωᴺ n)) (proj₁ g)) (sym (lvlᴰ k))
    (sΩ-LF (o1 (nat n)) (rb-no _) (tc (sbk k)) (Bc (nat n)) (Ωt two) (okBc (nat n)) hβ₂)
  where
  n = suc (suc (suc k))
```

## n ≤ 2: 孩子的 Ω 树嵌进第 2 层, 再自身折叠

```agda
crit2 : CritAt gᴰ 2
crit2 = (Self.PF 1 (o1 (nat 2)) (rb-no _) (Bc (nat 2)) (Ωt two) {P₀ = []} hβ₂ (Mβ 1))

crit1 : CritAt gᴰ 1
crit1 = (Self.PF 1 (o1 (nat 2)) (rb-no _) (Bc (nat 2)) (Ωt two) {P₀ = []} hβ₂
          {x = proj₁ (emb two (o1 (nat 2)) (inc tt self) (Ωt (fn 1)))} (mU {t = []} {s = Ωᴺ 1} mz (Mβ 0)))

crit0 : CritAt gᴰ 0
crit0 = (Self.PF 1 (o1 (nat 2)) (rb-no _) (Bc (nat 2)) (Ωt two) {P₀ = []} hβ₂
          {x = proj₁ (emb two (o1 (nat 2)) (inc tt (inc tt self)) (Ωt zero))}
                   (mU {t = []} {s = Ωᴺ 0} mz (mU {t = []} {s = Ωᴺ 0} mz (ΩJ 0 (Ωt zero) ⊴r))))

tb-crit : ∀ n → CritAt gᴰ n
tb-crit 0                   = crit0
tb-crit 1                   = crit1
tb-crit 2                   = crit2
tb-crit (suc (suc (suc k))) = crit3 k
```

## 封闭的关系上的一切有限 n

```agda
fiñᴰ : ∀ n m → n ≤ⁿ m → M̂ (M 2) (ψᴺ 2 (Ωᴺ n)) (proj₁ (gᴰ (nat m)))
fiñᴰ n m le = ĉ (app≤ 2 [] (Ω≤ le)) (tb-crit m)
```

## 边界: 表里没有的孩子

`rb1` 在 ℕ 极限形状的孩子处没有条目; 那一支逐字是主线原行, 判据在 ψ₂(Ω_{2+k}) 处为假.

```agda
tb-lim : ∀ f a → proj₁ (gᴰ (lim f a)) ≡ proj₁ (Hᴰ (lim f a))
tb-lim f a = refl

tb-lim-neg : ∀ k f a → M 2 (ψᴺ 2 (Ωᴺ (suc (suc k)))) (proj₁ (gᴰ (lim f a))) → ⊥
tb-lim-neg k f a = negS k refl (Sm+ι kΩ _)
```

## 同一判据, 两种写法

n ≥ 3 时兄弟孩子写法 (`YiRBCrit.gˢ`, 在 `fn (n + 2)` 上折, `YiRBCrit.eqˢ`) 与比较表写法 (在 `fn n` 上折, `lvlᴰ`) 都过判据; n = 1 时兄弟孩子写法不过 (`YiRLNeg.negˢ`), 比较表写法过.

```agda
two-ways : ∀ k → CritAt C.gˢ (suc (suc (suc k))) × CritAt gᴰ (suc (suc (suc k)))
two-ways k = C.sib-crit k , crit3 k

lvl-3ˢ : h₁ (nat 2 + nat 3) ≡ fn 5
lvl-3ˢ = refl

lvl-3ᴰ : gᴰ (nat 3) ≡ ψ (fn 3) (o1 (nat 3)) (rb-no _) (Bc (nat 3)) two (inc tt self) (Ωt two) (proj₁ (Ωt (fn 3)))
lvl-3ᴰ = lvlᴰ 0

sep-1 : (CritAt C.gˢ 1 → ⊥) × CritAt gᴰ 1
sep-1 = negˢ , crit1
```
