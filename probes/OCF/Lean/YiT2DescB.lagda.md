# 塔第 2 项 (六): 沿第一孩子下降, 对满足 `OKB` 的一般底

> 验收文件. 判决: 编译定理, 无前提. `descB`: `YiT2Desc.desc` 对一般底的版本. 底 B 逐分量不低于标准底 (`OKB`) 时, 沿第一孩子的路 p 走到的层号 j 上, 以 B 沿路的限制 `res p B` 为底的 Ω 树折叠, 值不高于 ℓ 上以 B 为底的; 限制仍满足 `OKB` (`ok-res`).
> 用到底的地方只有后继一步: 链的第 1 项是 `next (bs B a (ins self))`, 要 `Ωt a ⊴ bs B a (ins self)`.
> 不给出什么: `YiT2Desc.sucΩ≼tw2` 没有一般底的版本; 那条路经过 `↑ (tw 1) (c₂ 1)` 的形状, 它由底在 `tw 1` 上的分量决定 (标准底时是 `Ωt (tw 1)`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiT2DescB where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; inl; inb; Ev; Rt)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; ◃⊑; limcum≽; _⊢_⊴_; ⊴r; ⊴◃; ⊴→≼)
open import OCF.Lean.YiLSFold using (OKB)
open import OCF.Lean.YiT2Desc using (_⊑¹_; r¹; s¹; l¹; w¹; ev¹; rt¹)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ⊑→≼)
```

## 底的限制

第一孩子的底 (`dS … zero`, `dL … zero zero`, `dW … zero zero`) 的各分量就是原来的底沿路径取出的分量 (`sub-S`, `sub-L`, `sub-W`, `refl`).

```agda
sub : ∀ {ℓ ℓ′} → (∀ {i} → i ≤ ℓ′ → i ≤ ℓ) → Base ℓ → Base ℓ′
sub inj B = base (b⊥ B) (n⊥ B) (λ i w → bs B i (inj w)) (λ i w → ns B i (inj w))

ok-sub : ∀ {ℓ ℓ′} (inj : ∀ {i} → i ≤ ℓ′ → i ≤ ℓ) (B : Base ℓ) → OKB ℓ B → OKB ℓ′ (sub inj B)
ok-sub inj B ok = proj₁ ok , λ i w → proj₂ ok i (inj w)

sub-S : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) → dS a ε ρ B zero ≡ sub ins B
sub-S a ε ρ B = refl

sub-L : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) → dL g ε ρ B zero zero ≡ sub (inl zero) B
sub-L g ε ρ B = refl

sub-W : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h))
  → dW k h ε ρ B zero zero ≡ sub (inb zero) B
sub-W k h ε ρ B = refl

res : ∀ {j ℓ} → j ⊑¹ ℓ → Base ℓ → Base j
res r¹     B = B
res (s¹ p) B = res p (sub ins B)
res (l¹ p) B = res p (sub (inl zero) B)
res (w¹ p) B = res p (sub (inb zero) B)

ok-res : ∀ {j ℓ} (p : j ⊑¹ ℓ) (B : Base ℓ) → OKB ℓ B → OKB j (res p B)
ok-res r¹     B ok = ok
ok-res (s¹ p) B ok = ok-res p (sub ins B) (ok-sub ins B ok)
ok-res (l¹ p) B ok = ok-res p (sub (inl zero) B) (ok-sub (inl zero) B ok)
ok-res (w¹ p) B ok = ok-res p (sub (inb zero) B) (ok-sub (inb zero) B ok)
```

## 各步

```agda
mono⊴ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) {x y : Tr ℓ} → ℓ ⊢ x ⊴ y
  → zero ⊢ ψ⊥ ℓ ε ρ B x ⊴ ψ⊥ ℓ ε ρ B y
mono⊴ ℓ ε ρ B ⊴r     = ⊴r
mono⊴ ℓ ε ρ B (⊴◃ d) = ⊴◃ (mono⊥ ℓ ε ρ B d)

module _ (a : L) (ε : Ev a) (ρ : Rt a) (B : Base (suc a)) where
  cB : ℕ → Tr a
  cB = iter (λ z → ψs (suc a) ε ρ B a (ins self) (bs B a (ins self)) (ns B a (ins self)) (up zero tt (suc z) (z◃s z))) zero

  FB : ℕ → Tr zero
  FB n = ψ⊥ (suc a) ε ρ B (up zero tt (suc (cB n)) (z◃s (cB n)))

  nzB : ∀ n → zero ⊢ zero ◃ FB n
  nzB n = nz⊥ (suc a) ε ρ B (up zero tt (suc (cB n)) (z◃s (cB n)))

  SB-form : ψ⊥ (suc a) ε ρ B (Ωt (suc a)) ≡ limc FB nzB
  SB-form = refl

  suc-firstB : zero ⊢ ψ⊥ a ε ρ (sub ins B) (bs B a (ins self)) ◃ FB 1
  suc-firstB = ◃t (◃l zero) (◃l zero)

  suc-stepB : OKB (suc a) B → read (ψ⊥ a ε ρ (sub ins B) (Ωt a)) ≼ read (ψ⊥ (suc a) ε ρ B (Ωt (suc a)))
  suc-stepB ok = limcum≽ FB nzB 1
    (≼-trans (⊴→≼ (mono⊴ a ε ρ (sub ins B) (proj₂ ok a (ins self))))
             (⊑→≼ (read (ψ⊥ a ε ρ (sub ins B) (bs B a (ins self)))) (◃⊑ suc-firstB)))

lim-stepB : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g))
  → zero ⊢ ψ⊥ (g zero) (ε zero) (proj₁ ρ zero) (sub (inl zero) B) (Ωt (g zero)) ◃ ψ⊥ (lim g) ε ρ B (Ωt (lim g))
lim-stepB g ε ρ B = ◃l zero

Ω-stepB : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h))
  → zero ⊢ ψ⊥ (h zero) (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (sub (inb zero) B) (Ωt (h zero))
         ◃ ψ⊥ (Ωₗ k h) ε ρ B (Ωt (Ωₗ k h))
Ω-stepB k h ε ρ B = ◃l zero
```

## 下降

```agda
descB : ∀ {j ℓ} (p : j ⊑¹ ℓ) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B
  → read (ψ⊥ j (ev¹ p ε) (rt¹ p ρ) (res p B) (Ωt j)) ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))
descB {j} r¹ ε ρ B ok = ≼-refl (read (ψ⊥ j ε ρ B (Ωt j)))
descB (s¹ {a} p) ε ρ B ok =
  ≼-trans (descB p ε ρ (sub ins B) (ok-sub ins B ok)) (suc-stepB a ε ρ B ok)
descB (l¹ {g} p) ε ρ B ok =
  ≼-trans (descB p (ε zero) (proj₁ ρ zero) (sub (inl zero) B) (ok-sub (inl zero) B ok))
    (⊑→≼ (read (ψ⊥ (g zero) (ε zero) (proj₁ ρ zero) (sub (inl zero) B) (Ωt (g zero)))) (◃⊑ (lim-stepB g ε ρ B)))
descB (w¹ {k} {h} p) ε ρ B ok =
  ≼-trans (descB p (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (sub (inb zero) B) (ok-sub (inb zero) B ok))
    (⊑→≼ (read (ψ⊥ (h zero) (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (sub (inb zero) B) (Ωt (h zero))))
         (◃⊑ (Ω-stepB k h ε ρ B)))
```
