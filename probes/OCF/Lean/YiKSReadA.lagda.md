# 龙骨的陈述 (候选 A): K(n) 与 K(2) 的归约

> 验收文件 (读记号), 不进成品; 候选 A (`YiKVFold`) 的块、折叠、合法性一行不改. 陈述与 [YiKSRead](YiKSRead.lagda.md) 逐字相同, 折叠换成候选 A 的.
> 编译定理, 无前提: `k1ᴬ : Kᴬ 1`; `kl→Kᴬ : KLᴬ n → Kᴬ (suc n)`; `K2-redᴬ` (K(2) 归约到 `kl 1` 的逐行), `row0₂ᴬ` (第 0 行成立).
> 只是陈述, 未证: `KLᴬ n` (n ≥ 1); 第 1 行起未走通, 没有编译的否定. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKSReadA where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiKATw1 using (btbo-tw1ᴷ)
open import OCF.Lean.YiKSDesc using (kl)
open import OCF.Lean.YiKSDescA
open import OCF.Lean.YiKSRead using (fs-sup; hs)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
open import OCF.Lean.YiEXRow using (row₂-btbo)
import OCF.Align.EboLeanDef as E
open E using (HC; ΩTower; EBOψ)
open import OCF.Align.EboLeanTree using (hc-tower)
open import OCF.Align.Value using (_≼_; ≼-trans)
```

## Q 与 K

```agda
Q₀ᴬ : (ℓ : L) → Ok ℓ → E.T → Set
Q₀ᴬ ℓ o ν = (h : HC (E.ψ [] (E.Ωt ν) ∷ [])) → Rt h ≼ readRW (F₀ ℓ o)

Kᴬ KLᴬ : ℕ → Set
Kᴬ n  = Q₀ᴬ (tw n) (Ok-tw n) (ΩTower n)
KLᴬ n = Q₀ᴬ (kl n) (okl n) (ΩTower (suc n))

_ : Kᴬ 2 ≡ ((h : HC (EBOψ 3)) → Rt h ≼ readRW (twᶜ 2))
_ = refl

kl→Kᴬ : ∀ n → KLᴬ n → Kᴬ (suc n)
kl→Kᴬ n q h = keel-fromᴬ n (q h)

k1ᴬ : Kᴬ 1
k1ᴬ h = ≼-trans (tree-≼ refl h (hc-tower 2)) (≼-trans row₂-btbo btbo-tw1ᴷ)
```

## K(2) 归约到 `kl 1` 的逐行

```agda
z₂ᴬ : ℕ → Tr zero
z₂ᴬ = chΩ zero hs (okl 1)

Row₂ᴬ : ℕ → ℕ → Set
Row₂ᴬ n m = Rt (hω-inv (hc-tower 3) refl n) ≼ readRW (F₀ (hs (z₂ᴬ m)) (proj₂ (okl 1) (z₂ᴬ m)))

rows₂ᴬ : ∀ m → readRW (F₀ (hs (z₂ᴬ m)) (proj₂ (okl 1) (z₂ᴬ m))) ≼ readRW (twᶜ 2)
rows₂ᴬ m = ≼-trans (rowsΩ zero hs (okl 1) m) (keelᴬ 1)

K2-redᴬ : (∀ n → Σ ℕ λ m → Row₂ᴬ n m) → Kᴬ 2
K2-redᴬ prem h = ≼-trans (tree-≼ refl h (hc-tower 3))
  (fs-sup (hc-tower 3) refl (λ n → ≼-trans (proj₂ (prem n)) (rows₂ᴬ (proj₁ (prem n)))))

row0₂ᴬ : Row₂ᴬ 0 0
row0₂ᴬ = ≼-trans (k1ᴬ (hω-inv (hc-tower 3) refl 0)) (step¹ sS (λ _ → tw 1) (proj₂ (okl 1) zero))
```
