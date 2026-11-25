# 龙骨的下降 (候选 A): 塔第 n+1 项不低于龙骨层号上的标准折叠

> 验收文件 (只读第 0 层的值, 不读记号), 不进成品; 候选 A (`YiKVFold`) 的块、折叠、合法性一行不改. 判决: 编译定理, 无前提, 对一切 n.
> `keelᴬ : readRW (ψ₀ (kl n) … (Ωt (kl n))) ≼ readRW (twᶜ (suc n))`, 陈述与证明同 [YiKSDesc](YiKSDesc.lagda.md) 的 `keel`: 路上用到的各行 (朝第 0 层的结点, 一切孩子的路径上的嵌入, 后继形状的嵌入) 两个折叠逐字相同, 分支侧那一行不在路上.
> 不给出什么: `kl n` 上的折叠对记号的关系没有证; 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKSDescA where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiCertFold using (Base; B₀; Keep; node⁺)
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiKSDesc using (T₀; ◃≼ᴿ; plusᴿ; _⊑¹_; r¹; n¹; _∙¹_; ⊕⊑¹; up¹; kl)
open import OCF.Align.Value using (_≼_; ≼l; ≼-refl; ≼-trans)
```

## 结点朝第 0 层: 第 1 行

第 0 层没有槽位, 保留判定只能是 "不保留"; 输出是各行的部分和的极限, 第 1 行在第 1 个部分和里.

```agda
row1 : {X : Set} {x₀ : X} (m : Keep zero X x₀) (G : X → Tr⁺ zero) (s : X → X) {Y : T₀}
  → Y ≼ readRW (proj₁ (G (s x₀))) → Y ≼ readRW (proj₁ (node⁺ m G s))
row1 (just (() , _)) G s q
row1 {x₀ = x₀} nothing G s q = ≼l 1 (plusᴿ (proj₁ (G x₀)) (proj₁ (G (s x₀))) q)

cumᴿ : (F : ℕ → Tr⁺ zero) (n : ℕ) {Y : T₀} → Y ≼ readRW (proj₁ (F n)) → Y ≼ readRW (cum (λ i → proj₁ (F i)) n)
cumᴿ F zero    q = q
cumᴿ F (suc n) q = plusᴿ (cum (λ i → proj₁ (F i)) n) (proj₁ (F (suc n))) q

rowN : {X : Set} {x₀ : X} (m : Keep zero X x₀) (G : X → Tr⁺ zero) (s : X → X) (n : ℕ) {Y : T₀}
  → Y ≼ readRW (proj₁ (G (iter s x₀ n))) → Y ≼ readRW (proj₁ (node⁺ m G s))
rowN (just (() , _)) G s n q
rowN {x₀ = x₀} nothing G s n q = ≼l n (cumᴿ (λ i → G (iter s x₀ i)) n q)
```

## 第一孩子的路与下降

路 `_⊑¹_` 取自 [YiKSDesc](YiKSDesc.lagda.md); 证据 `Ok` 是候选 A 的 (Ω 形状带地板与证书), 所以 `ok¹`, `desc` 在这里重写, 证明逐字相同. `rowsΩ` 同.

```agda
ok¹ : ∀ {j ℓ} → j ⊑¹ ℓ → Ok ℓ → Ok j
ok¹ r¹             o = o
ok¹ (n¹ {s = s} p) o = ok¹ p (proj₂ o (c₀ s))

F₀ : (ℓ : L) → Ok ℓ → Tr zero
F₀ ℓ o = proj₁ (ψ₀ ℓ o (proj₁ (Ωt ℓ)))

step¹ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) → readRW (F₀ (h (c₀ s)) (proj₂ o (c₀ s))) ≼ readRW (F₀ (nd s h) o)
step¹ sS h o =
  ≼l 1 (plusᴿ _ _ (◃≼ᴿ (◃t (◃l zero) (◃l zero))))
step¹ sL g o = ◃≼ᴿ (◃l zero)
step¹ (sΩ k) h o =
  ◃≼ᴿ (mono (nd (sΩ k) h) o (B₀ (nd (sΩ k) h)) zero (z≤ (nd (sΩ k) h)) (Ωt zero) (◃w {p = inj₁ (inj₁ tt)}))

chΩ : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) → ℕ → Tr k
chΩ k h o = iter (λ z → proj₁ (ψ (nd (sΩ k) h) o (B₀ (nd (sΩ k) h)) k (ink self) (Ωt k)
                                 (proj₁ (upz {s = sΩ k} {h = h} z (Ωt (h z)))))) zero

rowsΩ : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (n : ℕ)
  → readRW (F₀ (h (chΩ k h o n)) (proj₂ o (chΩ k h o n))) ≼ readRW (F₀ (nd (sΩ k) h) o)
rowsΩ k h o n = rowN (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (z≤ (nd (sΩ k) h)))
  (λ z → ψ (nd (sΩ k) h) o (B₀ (nd (sΩ k) h)) zero (z≤ (nd (sΩ k) h)) (Ωt zero) (proj₁ (upz {s = sΩ k} {h = h} z (Ωt (h z)))))
  (λ z → proj₁ (ψ (nd (sΩ k) h) o (B₀ (nd (sΩ k) h)) k (ink self) (Ωt k) (proj₁ (upz {s = sΩ k} {h = h} z (Ωt (h z))))))
  n (≼-refl (readRW (F₀ (h (chΩ k h o n)) (proj₂ o (chΩ k h o n)))))

desc : ∀ {j ℓ} (p : j ⊑¹ ℓ) (o : Ok ℓ) → readRW (F₀ j (ok¹ p o)) ≼ readRW (F₀ ℓ o)
desc {j} r¹ o = ≼-refl (readRW (F₀ j o))
desc (n¹ {s} {h} p) o = ≼-trans (desc p (proj₂ o (c₀ s))) (step¹ s h o)
```

## 龙骨层号在塔第 n+1 项的第 1 行之下

`σ n`: 塔第 n+1 项的结点的第 1 个链点, 即层号 `tw n` 上 Ω 树以自身为目标的折叠. n = 0 时它是 ω; n ≥ 1 时结点保留, 零分支是 Ω 树被上折.

```agda
σ : (n : ℕ) → Tr (tw n)
σ n = proj₁ (ψ (tw n) (Ok-tw n) (B₀ (tw n)) (tw n) self (Ωt (tw n)) (proj₁ (Ωt (tw n))))

σ¹ : (n : ℕ) → ↑ (tw n) (proj₁ (Ωt (tw n))) ⊑¹ ↑ (tw n) (σ n)
σ¹ zero    = n¹ r¹
σ¹ (suc n) = n¹ (up¹ _ (down stop zero) (Ωt (tw (suc n))) _)

klP : (n : ℕ) → kl n ⊑¹ tw n ⊕ ↑ (tw n) (σ n)
klP n = ⊕⊑¹ (tw n) (σ¹ n)

okσ : (n : ℕ) → Ok (tw n ⊕ ↑ (tw n) (σ n))
okσ n = proj₂ (Ok-tw (suc n)) (σ n)

okl : (n : ℕ) → Ok (kl n)
okl n = ok¹ (klP n) (okσ n)

rowσ : (n : ℕ) → readRW (F₀ (tw n ⊕ ↑ (tw n) (σ n)) (okσ n)) ≼ readRW (twᶜ (suc n))
rowσ n = row1 (kp ℓ o (inj₁ (inj₁ tt)) (z≤ ℓ))
  (λ z → ψ ℓ o (B₀ ℓ) zero (z≤ ℓ) (Ωt zero) (g z))
  (λ z → proj₁ (ψ ℓ o (B₀ ℓ) (tw n) (ink self) (Ωt (tw n)) (g z)))
  (≼-refl (readRW (F₀ (tw n ⊕ ↑ (tw n) (σ n)) (okσ n))))
  where
  ℓ : L
  ℓ = tw (suc n)
  o : Ok ℓ
  o = Ok-tw (suc n)
  g : Tr (tw n) → Tr ℓ
  g z = proj₁ (upz {s = sΩ (tw n)} {h = λ c → tw n ⊕ ↑ (tw n) c} z (Ωt (tw n ⊕ ↑ (tw n) z)))

keelᴬ : (n : ℕ) → readRW (F₀ (kl n) (okl n)) ≼ readRW (twᶜ (suc n))
keelᴬ n = ≼-trans (desc (klP n) (okσ n)) (rowσ n)

keel-fromᴬ : (n : ℕ) {Y : T₀} → Y ≼ readRW (F₀ (kl n) (okl n)) → Y ≼ readRW (twᶜ (suc n))
keel-fromᴬ n q = ≼-trans q (keelᴬ n)
```
