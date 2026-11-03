# 字面上界: 验收 (与 EBO 比较)

> **验收节.** 记号只在本文件. 结论写在 [InaccFloor](InaccFloor.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccFloorAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.InaccTreeBase using (Lv; Ordᴸ; zero; suc; lim; Ω; toLv; rise)
open import OCF.Align.InaccFloorTree
open import OCF.Align.InaccFloorBase using (module WorldN; module World)
open import OCF.Align.InaccFloorNeg using (ω₀)
open import OCF.Align.Level using (natᴵ)
import OCF.Align.Level as Lvl
import OCF.Align.EBO as E
open E using (fsn; cof; c0; c1; cω; cΩ; sucT; 𝟏; Ωt; natT; pred) renaming (T to Tm; ψ to ψᵗ)
open import OCF.Align.InaccTreeAccept using (diff; walkB)
open import OCF.Align.Uniform5Wall using (tΩΩ; p₁; p₂; t₁; t₃; W; ψ₁; Ω·2; Ω+1)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Uniform4Head using (Ωp)
```

## §1 $\forall S$: 路径上没有问到 `S`

下面每条都是 `S` 为变量的 `refl`. 问到了 `S` 就卡住, 通不过. 宽度与深度是有限的.

```agda
ψ₀t : Tm → Tm
ψ₀t a = ψᵗ [] a ∷ []

ωt : Tm
ωt = ψ₀t (natT 1)

module AllS (S : Sib) where
  open PF S renaming (T to Tᶠ)

  tmAt : List ℕ → Tm
  tmAt q = proj₁ (walkB q tΩΩ TΩΩ)

  dfP : List ℕ → ℕ → ℕ → Maybe (List ℕ)
  dfP q d w = diff d w (tmAt q) (proj₂ (walkB q tΩΩ TΩΩ))

  chk₀ : dfP [] 3 2 ≡ nothing
  chk₀ = refl

  s4 s5 s6 s7 : List ℕ
  s4 = 1 ∷ 0 ∷ 0 ∷ 2 ∷ []
  s5 = 1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ []
  s6 = 1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ []
  s7 = 1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ []

  -- 站名 (与 Uniform5Wall 相同)
  n4 : tmAt s4 ≡ ψ₀t (Ωt (Ωt (natT 2)))
  n4 = refl
  n5 : tmAt s5 ≡ ψ₀t (Ωt (ψ₁ (Ωt Ωᵗ)))
  n5 = refl
  n6 : tmAt s6 ≡ ψ₀t (Ωt (ψ₁ (natT 1)))
  n6 = refl
  n7 : tmAt s7 ≡ t₃
  n7 = refl
  n8 : tmAt p₁ ≡ t₁
  n8 = refl

  c4 : dfP s4 3 2 ≡ nothing
  c4 = refl
  c5 : dfP s5 3 2 ≡ nothing
  c5 = refl
  c6 : dfP s6 3 2 ≡ nothing
  c6 = refl
  c7 : dfP s7 3 2 ≡ nothing
  c7 = refl
  c8 : dfP p₁ 3 2 ≡ nothing
  c8 = refl

  -- 再走 20 步: 仍然没有问到 S. W 在第 40 步, 见 §2
  c29 : dfP (take 29 (p₁ ++ p₂)) 2 2 ≡ nothing
  c29 = refl

  -- 一致族 θ ↦ ψ₀(Ω_{ψ₁(Ω_θ)})
  fam2 : diff 4 2 (ψ₀t (Ωt (ψ₁ (Ωt (natT 2))))) (Tᶠ (toLv (F (natL 2)))) ≡ nothing
  fam2 = refl
  fam3 : diff 4 2 (ψ₀t (Ωt (ψ₁ (Ωt (natT 3))))) (Tᶠ (toLv (F (natL 3)))) ≡ nothing
  fam3 = refl
  famω : diff 4 2 (ψ₀t (Ωt (ψ₁ (Ωt ωt)))) (Tᶠ (toLv (F (toLv ω₀)))) ≡ nothing
  famω = refl
  -- 下标自身是 ψ₁ 的输出
  famψ : diff 3 2 (ψ₀t (Ωt (ψ₁ (Ωt (ψ₁ (Ωt Ωᵗ)))))) (Tᶠ (toLv (F (toLv (F (toLv (Ω (natL 1)))))))) ≡ nothing
  famψ = refl
```

## §2 `S` 不是摆设

**第一次问 `S`** 在 `p₁ ++ p₂` 的第 30 步的第 1 号孩子: `dfP (take 30 _ ++ [1]) 1 1` 对变量 `S` 不归约 (探针, 不能写成编译的否定). 第 30 步的项是 $\psi_0(\psi_{\Omega\cdot2}(\Omega_{\Omega\cdot2}+\Omega_{\Omega+\psi_0(1)})[2])$. 手算: 这与 Uniform5Wall 的 $W$ 同类, 只早 10 步, 目标与节点都是 $\Omega+$可数, 尾巴来自闭包的不同分支. `S` 收到的那一对没有打印出来.

取 `S₀ = rise`: 走到 $W$ 都对, 但在 $W[0]$ 之下深度 10 处错. 这是编译的: `S` 必须答对.

```agda
S₀ : Sib
S₀ _ _ = rise

module Zero where
  open PF S₀ renaming (T to Tᶠ)

  tmAt : List ℕ → Tm
  tmAt q = proj₁ (walkB q tΩΩ TΩΩ)

  dfP : List ℕ → ℕ → ℕ → Maybe (List ℕ)
  dfP q d w = diff d w (tmAt q) (proj₂ (walkB q tΩΩ TΩΩ))

  reachW : tmAt (p₁ ++ p₂) ≡ W
  reachW = refl

  atW : dfP (p₁ ++ p₂) 6 3 ≡ nothing
  atW = refl

  -- 偏离: 这一宽度深度下比较器报告的路径. 是哪一个比较造成的, 没有定位
  dev : dfP ((p₁ ++ p₂) ++ (0 ∷ [])) 10 2 ≡ just (1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ [])
  dev = refl
```

## §3 世界 $\ell$ 给的答案

Uniform5Wall `bx` 的比较 ($\Omega+\eta$ 对 $\Omega+1$) 现在是 `<-decᴬ` 的实例, 字面界 $\Omega+\ell$, 没有语法. 结果与记号的共尾度一致 ($\eta=1$ 穿透, $\eta=2,3$ 折叠).

```agda
data Tag : Set where tlt teq tgt : Tag

module Five where
  open WorldN (natᴵ 5) (Lvl.suc (Lvl.suc (Lvl.suc Lvl.zero)))
  open World (natᴵ 5) (Lvl.suc (Lvl.suc (Lvl.suc Lvl.zero)))

  tag : ∀ {a b} → Tri a b → Tag
  tag (inj₁ _) = tlt
  tag (inj₂ (inj₁ _)) = tgt
  tag (inj₂ (inj₂ _)) = teq

  p0 : natᴵ 0 Lvl.<ᴵ natᴵ 5
  p0 = Lvl.suc (Lvl.suc (Lvl.suc (Lvl.suc Lvl.zero)))
  p1 : natᴵ 1 Lvl.<ᴵ natᴵ 5
  p1 = Lvl.suc (Lvl.suc (Lvl.suc Lvl.zero))
  p2 : natᴵ 2 Lvl.<ᴵ natᴵ 5
  p2 = Lvl.suc (Lvl.suc Lvl.zero)

  -- 节点 Ω+a, 目标 Ω+1. Ω·1 = times zero
  _ : tag (cmpΩ 1 (natᴵ 0) (natᴵ 1) p0 p1) ≡ tlt
  _ = refl
  _ : tag (cmpΩ 1 (natᴵ 1) (natᴵ 1) p1 p1) ≡ teq
  _ = refl
  _ : tag (cmpΩ 1 (natᴵ 2) (natᴵ 1) p2 p1) ≡ tgt
  _ = refl

  _ : cof (ψᵗ Ω+1 (Ωt Ω+1) ∷ []) ≡ cΩ (Ωp ∷ [])
  _ = refl
```
