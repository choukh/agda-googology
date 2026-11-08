# 世界增长不能直接搬运旧 Gd

本篇检验原 Third 的证书，不改变折叠。合同只要求原 `Gd`，
没有另加输入树的 `LgB`；反例不否定实际生成域的更强不变量。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Lean.CircuitBoundaryGd where

open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
import OCF.Lean.ThirdFold as F

GenericGdTransport : Set₁
GenericGdTransport = ∀ (U : KS) (w w′ : Wd U)
  (lw : LgW U w) (lw′ : LgW U w′) → _≤w_ U w w′ →
  ∀ m h → F.Gd U w lw m h → F.Gd U w′ lw′ m h

U : KS
U = step S⊥

one two : Cd
one = hs hz
two = hs one

w₀ w₁ : Wd U
w₀ = tt , hz
w₁ = tt , one

lw₀ : LgW U w₀
lw₀ = tt , tt
lw₁ : LgW U w₁
lw₁ = tt , tt
grow : _≤w_ U w₀ w₁
grow = tt , hsuc hself

module Old = F U w₀ lw₀
module New = F U w₁ lw₁

m : HB U
m = hΩ (inj₂ tt) (λ _ → hs hz)

legal-m : LgB m
legal-m = (λ _ _ _ _ → hself) , (λ _ _ → tt)

-- 两个世界中的同一个合法字面高度上界。
bound : HB U
bound = hs m
legal-bound : LgB bound
legal-bound = legal-m
height-position : ∀ {w} → m ⊲[ w ] bound
height-position = hsuc hself

bad : HB (Tw U (hs m))
bad = hΩ (inj₁ (two , inj₂ tt)) (λ _ → hz)

g : HB (Tw U m) → HB (Tw U (hs m))
g hz = hz
g (hs _) = hz
g (hl _) = hz
g (hΩ (hz , κ) f) = hz
g (hΩ (hs e , κ) f) = bad
g (hΩ (hl f , κ) g′) = bad
g (hΩ (hΩ () f , κ) g′)

old-branch : ∀ c → Old.Gd m c → Old.Gd (hs m) (g c)
old-branch hz p = tt
old-branch (hs c) p = tt
old-branch (hl f) p = tt
old-branch (hΩ (hz , κ) f) p = tt
old-branch (hΩ (hs e , κ) f) ((() , q) , r)
old-branch (hΩ (hl f , κ) g′) ((() , q) , r)
old-branch (hΩ (hΩ () f , κ) g′) p

input : HB (Tw U (hs m))
input = hΩ (inj₂ tt) g

old-input : Old.Gd (hs m) input
old-input = tt , old-branch

activated : HB (Tw U m)
activated = hΩ (one , inj₂ tt) (λ _ → hz)

activated-new : New.Gd m activated
activated-new = (hself , tt) , (λ _ _ → tt)

two-not-one : ¬ (_⊲[_]_ {S⊥} two tt one)
two-not-one (hsuc ())

no-new-input : ¬ (New.Gd (hs m) input)
no-new-input p = two-not-one (proj₁ (proj₁ (proj₂ p activated activated-new)))

no-generic-transport : ¬ GenericGdTransport
no-generic-transport move = no-new-input (move U w₀ w₁ lw₀ lw₁ grow (hs m) input old-input)
```

新增可入坐标会扩大 `AdT` 的量化域；`Pos` 的正向增长不能补出新枝的证书。
这里只否定任意旧 `Gd` 原样搬运，未证明输入 `input` 合法，也未否定
原闭项生成域、带未来世界条件的证书、修改坐标域的方案或 ψ₀Λ 路线。
