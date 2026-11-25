# 塔第 2 项 (三): Ω 结点层号的帧 (`up` 一行, 朝第 0 层), 回退一行进入的位置

> 验收文件 (末节的 `note-cof` 读记号). 判决: 编译定理, 无前提, 对一切下标层号 k: `ok-dW` (底的条件过 Ω 结点层号的 `up` 一帧保持), `up-lower` (孩子层号是零/后继/ℕ 极限生成时, `up x c (Ωt (h c))` 的底折叠不低于参照 ψ⁰(Ω_i)), `eqk` (目标第 0 层, 路径 `ink w` 时 `ψs` 与 `ψ⊥` 逐点同形).
> 实例: `tw 1` 上 `Ωt + Ωt` 的折叠的链 `zc` 满足 `zc 1` 在 `twᶜ 1` 之上, `ψ⁰(Ω_{lvl (zc n)}) ≼ read (zc (n+1))`, 各项 `≼ read (twᶜ 2)` (`named`). 参照是 `OCF.Align.Level` 的, 层号取链点的读回, 不是记号项.
> 步 3 的测试 (`refl`): 这一行的孩子的底在第 1 层的分量已经走回退一行 (`β₁-form`); 自身行的输出含孩子一侧槽位的结点 (`self-slot`). 不给出什么: 回退与摊平对 ψ₀(Ω_{Ω+1}) 下界要不要紧没有判决; 孩子层号含 Ω 结点时 `up-lower` 不适用.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiT2Frame where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiLSRel using (Corr)
open import OCF.Lean.YiLSFold using (NL; OKB; ok-B₀; lower; ψ⊥-⊵; ψs-⊵)
open import OCF.Lean.YiLSTw1 using (h₁; εh; ρh; G; nl-↑; corr-↑; lvl; E; ez; es; el; E-next; E-cum; E→≅; LiftP; LiftP-∙; eq0)
open import OCF.Lean.YiT2Desc using (R⁺; nzR⁺; sucΩ≼tw2)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ⊑→≼)
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiMEAnchor using (u₁; Ω₁ᵗ)
open import Data.List using ([]; _∷_)
```

## 对一切下标层号 k

底的条件 (`OKB`: 逐分量不低于标准底) 过 `up` 一帧保持; 证明只用 "折叠值不低于底", 其中 `inb` 目标的 `up` 一行就是回退一行.

```agda
ok-dW : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) → OKB (Ωₗ k h) B
  → (c : Tr k) (t : Tr (Ωₗ k h)) → OKB (h c) (dW k h ε ρ B c t)
ok-dW k h ε ρ B ok c t = ⊴-trans (proj₁ ok) (ψ⊥-⊵ (Ωₗ k h) ε ρ B t)
  , λ j w → ⊴-trans (proj₂ ok j (inb c w)) (ψs-⊵ (Ωₗ k h) ε ρ B j (inb c w) _ _ t)

up-lower : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) → OKB (Ωₗ k h) B
  → (x : Tr (Ωₗ k h)) (c : Tr k) → NL (h c) → ∀ {i} → Corr i (h c)
  → L.ψ⁰ (L.Ω i) ≼ read (ψ⊥ (Ωₗ k h) ε ρ B (up x c (Ωt (h c)) (Ωt-nz (h c))))
up-lower k h ε ρ B ok x c f cr =
  lower f (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) (ok-dW k h ε ρ B ok c x) cr
```

回退一行与孩子的底 (定义的展开, 对一切 k). 目标在某个分支 c′ 之内时, 别的 (或同一个) 分支 c 的孩子树 y 先用标准底整个折到第 0 层, 再嵌回来加在后面; 孩子的底在层号 j 上的分量就是这样一次折叠.

```agda
fallback : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : LF)
  (c′ : Tr k) (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
  (e : h c ⊢ zero ◃ y)
  → ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e)
  ≡ ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x + ι j (ψ₀ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) y)
fallback k h ε ρ B j c′ w β nβ x c y e = refl

inner-base : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h))
  (c : Tr k) (x : Tr (Ωₗ k h)) (j : LF) (w : j ≤ h c)
  → bs (dW k h ε ρ B c x) j w ≡ ψs (Ωₗ k h) ε ρ B j (inb c w) (bs B j (inb c w)) (ns B j (inb c w)) x
inner-base k h ε ρ B c x j w = refl
```

目标是第 0 层, 路径 `ink w`: 结点在第 0 层没有槽位可保留, `up` 一行交给孩子层 (那里用 `YiLSTw1.eq0`). 前提: 接到每个孩子层号的路径是 `lift` 形.

```agda
eqk : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (w : zero ≤ k)
  → ((c : Tr k) → LiftP (w ∙ proj₁ (proj₂ ε c)))
  → (β : Tr zero) (nβ : zero ⊢ zero ◃ β) → E β (b⊥ B)
  → (x : Tr (Ωₗ k h)) → E (ψs (Ωₗ k h) ε ρ B zero (ink w) β nβ x) (ψ⊥ (Ωₗ k h) ε ρ B x)
eqk k h ε ρ B w lw β nβ e zero      = e
eqk k h ε ρ B w lw β nβ e (suc x)   = E-next (eqk k h ε ρ B w lw β nβ e x)
eqk k h ε ρ B w lw β nβ e (lim f a) = el (λ n → eqk k h ε ρ B w lw β nβ e (f n))
eqk k h ε ρ B w lw β nβ e (Ω p g) =
  kp-ind (Ωₗ k h) ε ρ p (ink w) (λ X → E X (ψ⊥ (Ωₗ k h) ε ρ B (Ω p g))) (λ ())
    (E-cum _ _ (λ n → eqk k h ε ρ B w lw β nβ e (g _)))
eqk k h ε ρ B w lw β nβ e (up x c y e′) =
  eq0 (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) (w ∙ proj₁ (proj₂ ε c)) (lw c) _ _
    (eqk k h ε ρ B w lw β nβ e x) y
```

## 实例: `tw 1` 上 `Ωt + Ωt` 的折叠

β 是 `tw 1` 的 Ω 树. `β + β` 是结点, 分支 z 上是 `up β z (Ωt (h₁ z))`; 折叠是链 `zc` 上各行的部分和的极限.

```agda
ε¹ : Ev (tw 1)
ε¹ = Ev-tw 1

ρ¹ : Rt (tw 1)
ρ¹ = Rt-tw 1

β : Tr (tw 1)
β = Ωt (tw 1)

gβ : Tr zero → Tr (tw 1)
gβ z = up β z (Ωt (h₁ z)) (Ωt-nz (h₁ z))

zc : ℕ → Tr zero
zc = iter (λ z → ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) zero (ink self) (Ωt zero) (Ωt-nz zero) (gβ z)) zero

rowβ : ℕ → Tr zero
rowβ n = ψ⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (gβ (zc n))

nzβ : ∀ n → zero ⊢ zero ◃ rowβ n
nzβ n = nz⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (gβ (zc n))

ββ-form : ψ₀ (tw 1) ε¹ ρ¹ (β + β) ≡ limc rowβ nzβ
ββ-form = refl

row-lower : ∀ n → L.ψ⁰ (L.Ω (lvl (zc n))) ≼ read (rowβ n)
row-lower n = up-lower zero h₁ ε¹ ρ¹ (B₀ (tw 1)) (ok-B₀ (tw 1)) β (zc n) (nl-↑ (zc n)) (corr-↑ (zc n) (HSr (zc n)))
```

链点与行: `zc (n+1)` 与第 n 行逐点同形; 第 0 行是 `next (twᶜ 1)`, 所以链从 `twᶜ 1` 之上起步.

```agda
lw¹ : (c : Tr zero) → LiftP (self ∙ proj₁ (proj₂ ε¹ c))
lw¹ c = LiftP-∙ zero (↑ zero c) self tt

zc-row : ∀ n → E (zc (suc n)) (rowβ n)
zc-row n = eqk zero h₁ ε¹ ρ¹ (B₀ (tw 1)) self lw¹ (Ωt zero) (Ωt-nz zero) (es ez) (gβ (zc n))

row0-form : rowβ 0 ≡ next (twᶜ 1) (nz⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) β)
row0-form = refl

tw1◃row0 : zero ⊢ twᶜ 1 ◃ rowβ 0
tw1◃row0 = ◃l zero

chain-closed : ∀ n → L.ψ⁰ (L.Ω (lvl (zc n))) ≼ read (zc (suc n))
chain-closed n = ≼-trans (row-lower n) (≅→≼ (L.≅-sym (E→≅ (zc-row n))))
```

接到塔第 2 项: `β + β` 是 `next β` 的基本列第 1 项, `next β` 是 `T⁺` 的链的第 1 项 (`YiT2Desc.d⁺1`).

```agda
ββ◃R1 : zero ⊢ ψ₀ (tw 1) ε¹ ρ¹ (β + β) ◃ R⁺ 1
ββ◃R1 = ◃t (◃l 1) (◃l zero)

ββ≼tw2 : read (ψ₀ (tw 1) ε¹ ρ¹ (β + β)) ≼ read (twᶜ 2)
ββ≼tw2 = ≼-trans (limcum≽ R⁺ nzR⁺ 1 (⊑→≼ (read (ψ₀ (tw 1) ε¹ ρ¹ (β + β))) (◃⊑ ββ◃R1))) sucΩ≼tw2

named : ∀ n → L.ψ⁰ (L.Ω (lvl (zc n))) ≼ read (twᶜ 2)
named n = ≼-trans (limcum≽ rowβ nzβ n (row-lower n)) ββ≼tw2
```

## 步 3 的测试: 回退一行与孩子一侧的结点各自进入的位置

第 2 行 (z 是 2, 孩子层号 `suc (suc zero)`) 的孩子的底在第 1 层的分量: β 的结点保留, 分支 c 上是 `Ωt 1 + ι 1 (G c)`, `G c` 是层号 `h₁ c` 上的标准折叠 (第 0 层的树). 这是回退一行的输出: 孩子树没有朝第 1 层折叠.

```agda
one two : Tr zero
one = suc zero
two = suc one

β₁-form : bs (dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) two β) (suc zero) (ins self)
        ≡ Ω (inj₁ tt) (λ c → Ωt (suc zero) + ι (suc zero) (G c))
β₁-form = refl
```

自身行 (上折) 的输出: 孩子层号 `suc zero` 的 Ω 树上折进 `tw 1`, 得到孩子一侧槽位 `inj₂ (one , …)` 的结点. 目标路径是 `inb c′ w` 时这种结点一律折叠 (`YiMEStep.drop-same`).

```agda
self-slot : (b : Tr (tw 1)) (nb : tw 1 ⊢ zero ◃ b)
  → Upc (tw 1) one b nb (Ωt (h₁ one))
  ≡ Ω (inj₂ (one , inj₂ (inj₁ tt))) (λ z → Up (suc zero) (down stop one) b nb (up zero tt (suc z) (z◃s z)))
self-slot b nb = refl
```

同一个结点朝同一分支里的第 1 层折叠 (目标路径 `inb one self`): 块的输入是结点 (`flat-in`), 输出是 ℕ 极限 (`flat-lim`). 记号一侧对应的项 ψ₁(ψ_Ω(Ω₁)) 余尾是 Ω₁ (`note-cof`), 即结点保留. 两边余尾不同, 所以 `YiMEBase.Mᴰ` 的 `mΩ` 在这里没有块一侧的结点可对.

```agda
IsLim IsΩ : {ℓ : LF} → Tr ℓ → Set
IsLim (lim _ _) = ⊤
IsLim _         = ⊥
IsΩ (Ω _ _) = ⊤
IsΩ _       = ⊥

flat-in : IsΩ (Upc (tw 1) one β (Ωt-nz (tw 1)) (Ωt (h₁ one)))
flat-in = tt

flat-lim : IsLim (ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (suc zero) (inb one self) (Ωt (suc zero)) (Ωt-nz (suc zero))
                     (Upc (tw 1) one β (Ωt-nz (tw 1)) (Ωt (h₁ one))))
flat-lim = tt

note-cof : E.cof (E.ψ u₁ (E.ψ Ω₁ᵗ Ω₁ᵗ ∷ []) ∷ []) ≡ E.cΩ []
note-cof = refl
```
