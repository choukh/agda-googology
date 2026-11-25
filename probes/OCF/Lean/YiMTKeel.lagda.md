# 最小比较表: 龙骨层号的下降

> 验收文件 (只读第 0 层的值, 不读记号), 不进成品. 编译定理, 无前提, 对一切 n: `keelᶻ : readRW (F₀ᶻ (kl n) (okl n)) ≼ readRW (twᶻ (suc n))`, 陈述与证明照 `YiKSDesc.keel`, 折叠换成 `YiTBRow` 的, 表取 `rbᶻ`; 路上的各行 (朝第 0 层的结点, 一致路径上的嵌入, 自身行) 不经那一行.
> 另: 塔逐项是前一项的第 0 行 (`row0ᶻ`, `refl`), 所以 `tw≼ᶻ : readRW (twᶻ n) ≼ readRW (twᶻ (suc n))`; Ω 形状层号朝第 0 层的第 n 行是链点孩子上的标准折叠 (`rowsΩᶻ`).
> 不给出什么: `kl n` 上的折叠对记号的关系没有证; 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMTKeel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀; kp)
open import OCF.Lean.YiTBRow using (ψ; mono)
open import OCF.Lean.YiMTTab
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiKSDesc using (T₀; ◃≼ᴿ; plusᴿ; row1; rowN; _⊑¹_; r¹; n¹; ok¹; σ; kl; klP; okσ; okl)
open import OCF.Align.Value using (_≼_; ≼l; ≼-refl; ≼-trans)
```

## 塔逐项

```agda
head : Tr zero → Tr zero
head (lim f a) = f zero
head _         = zero

row0ᶻ : (n : ℕ) → head (twᶻ (suc n)) ≡ twᶻ n
row0ᶻ n = refl

tw≼ᶻ : (n : ℕ) → readRW (twᶻ n) ≼ readRW (twᶻ (suc n))
tw≼ᶻ n = ≼l 0 (≼-refl (readRW (twᶻ n)))
```

## 第一孩子的下降

```agda
F₀ᶻ : (ℓ : L) → Ok ℓ → Tr zero
F₀ᶻ ℓ o = proj₁ (ψ₀ᶻ ℓ o (proj₁ (Ωt ℓ)))

step¹ᶻ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) → readRW (F₀ᶻ (h (c₀ s)) (proj₂ o (c₀ s))) ≼ readRW (F₀ᶻ (nd s h) o)
step¹ᶻ sS h o =
  ≼l 1 (plusᴿ _ _ (◃≼ᴿ (◃t (◃l zero) (◃l zero))))
step¹ᶻ sL g o = ◃≼ᴿ (◃l zero)
step¹ᶻ (sΩ k) h o =
  ◃≼ᴿ (mono (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) (B₀ (nd (sΩ k) h)) zero (z≤ (nd (sΩ k) h)) (Ωt zero) (◃w {p = inj₁ (inj₁ tt)}))

chΩᶻ : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) → ℕ → Tr k
chΩᶻ k h o = iter (λ z → proj₁ (ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) (B₀ (nd (sΩ k) h)) k (ink self) (Ωt k)
                                  (proj₁ (upz {s = sΩ k} {h = h} z (Ωt (h z)))))) zero

rowsΩᶻ : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (n : ℕ)
  → readRW (F₀ᶻ (h (chΩᶻ k h o n)) (proj₂ o (chΩᶻ k h o n))) ≼ readRW (F₀ᶻ (nd (sΩ k) h) o)
rowsΩᶻ k h o n = rowN (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (z≤ (nd (sΩ k) h)))
  (λ z → ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) (B₀ (nd (sΩ k) h)) zero (z≤ (nd (sΩ k) h)) (Ωt zero) (proj₁ (upz {s = sΩ k} {h = h} z (Ωt (h z)))))
  (λ z → proj₁ (ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) (B₀ (nd (sΩ k) h)) k (ink self) (Ωt k) (proj₁ (upz {s = sΩ k} {h = h} z (Ωt (h z))))))
  n (≼-refl (readRW (F₀ᶻ (h (chΩᶻ k h o n)) (proj₂ o (chΩᶻ k h o n)))))

descᶻ : ∀ {j ℓ} (p : j ⊑¹ ℓ) (o : Ok ℓ) → readRW (F₀ᶻ j (ok¹ p o)) ≼ readRW (F₀ᶻ ℓ o)
descᶻ {j} r¹ o = ≼-refl (readRW (F₀ᶻ j o))
descᶻ (n¹ {s} {h} p) o = ≼-trans (descᶻ p (proj₂ o (c₀ s))) (step¹ᶻ s h o)
```

## 龙骨层号在塔第 n+1 项的第 1 行之下

塔第 n+1 项的结点的第 1 个链点在两个折叠里是同一棵树 (`σ-same`, `refl`: 自身行不经那一行).

```agda
σᶻ : (n : ℕ) → Tr (tw n)
σᶻ n = proj₁ (ψ (tw n) (Ok-tw n) (rbᶻ (tw n)) (B₀ (tw n)) (tw n) self (Ωt (tw n)) (proj₁ (Ωt (tw n))))

σ-same : (n : ℕ) → σᶻ (suc n) ≡ σ (suc n)
σ-same n = refl

σ-same0 : σᶻ 0 ≡ σ 0
σ-same0 = refl

rowσᶻ : (n : ℕ) → readRW (F₀ᶻ (tw n ⊕ ↑ (tw n) (σ n)) (okσ n)) ≼ readRW (twᶻ (suc n))
rowσᶻ zero = row1 (kp (tw 1) (Ok-tw 1) (inj₁ (inj₁ tt)) (z≤ (tw 1)))
  (λ z → ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) zero (z≤ (tw 1)) (Ωt zero) (proj₁ (upz {s = sΩ zero} {h = λ c → zero ⊕ ↑ zero c} z (Ωt (zero ⊕ ↑ zero z)))))
  (λ z → proj₁ (ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) zero (ink self) (Ωt zero) (proj₁ (upz {s = sΩ zero} {h = λ c → zero ⊕ ↑ zero c} z (Ωt (zero ⊕ ↑ zero z))))))
  (≼-refl (readRW (F₀ᶻ (zero ⊕ ↑ zero (σ 0)) (okσ 0))))
rowσᶻ (suc n) = row1 (kp ℓ o (inj₁ (inj₁ tt)) (z≤ ℓ))
  (λ z → ψ ℓ o (rbᶻ ℓ) (B₀ ℓ) zero (z≤ ℓ) (Ωt zero) (g z))
  (λ z → proj₁ (ψ ℓ o (rbᶻ ℓ) (B₀ ℓ) (tw (suc n)) (ink self) (Ωt (tw (suc n))) (g z)))
  (≼-refl (readRW (F₀ᶻ (tw (suc n) ⊕ ↑ (tw (suc n)) (σ (suc n))) (okσ (suc n)))))
  where
  ℓ : L
  ℓ = tw (suc (suc n))
  o : Ok ℓ
  o = Ok-tw (suc (suc n))
  g : Tr (tw (suc n)) → Tr ℓ
  g z = proj₁ (upz {s = sΩ (tw (suc n))} {h = λ c → tw (suc n) ⊕ ↑ (tw (suc n)) c} z (Ωt (tw (suc n) ⊕ ↑ (tw (suc n)) z)))

keelᶻ : (n : ℕ) → readRW (F₀ᶻ (kl n) (okl n)) ≼ readRW (twᶻ (suc n))
keelᶻ n = ≼-trans (descᶻ (klP n) (okσ n)) (rowσᶻ n)
```
