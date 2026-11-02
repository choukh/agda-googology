# 层号判决的范数模: 有限检验、具体的项与编译的否定 (验收)

> **验收节.** 结论在 [InaccModulus](InaccModulus.lagda.md). 这里只有有限检验 (`refl`) 与具体实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulusAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccStrikeBase using (Funext; dz)
open import OCF.Align.InaccStrikeCommute using (module Tr)
open import OCF.Align.InaccStrikeOracle using (pad; natL)
open import OCF.Align.InaccTreeAccept using (LabN; diff)
open import OCF.Align.InaccModulusBase
open import OCF.Align.InaccModulus using (module Main)
open import OCF.Align.Standard using (NF; n[]; n∷; nψ; Ctbl; c[]; c∷; vh; vd; vt; sz; Bnd)
open import OCF.Align.EBOI using (isOTᵉ)
import OCF.Align.EBO as E
open E using (T; PT; cmpᵀ; fsn; fsT; Ωt; 𝟏; []<) renaming (ψ to ψᵗ; natT to natᵗ)

L : T → Lv
L = Tr.L Dᵐ

ψ0Ω : T → T
ψ0Ω u = ψᵗ [] (ψᵗ u [] ∷ []) ∷ []

ω ε₀ BO ψε ψBO : T
ω   = ψ0Ω []                -- ψ₀(Ω₀) = ψ₀(1)
ε₀  = ψ0Ω (𝟏 ∷ [])          -- ψ₀(Ω₁)
BO  = ψ0Ω ω                 -- ψ₀(Ω_ω)
ψε  = ψ0Ω ε₀                -- ψ₀(Ω_{ψ₀(Ω₁)})
ψBO = ψ0Ω BO                -- ψ₀(Ω_{ψ₀(Ω_ω)})
```

## §1 具体的项带标签: 只以 `Funext` 为参数

`NF-ψ0Ω`: `u` 是可数标准形, 则 `ψ₀(Ω_u)` 也是. 所以塔 `tower n` 全是可数标准形, 对每个 `n` 带标签. 塔的上确界是 `ψ₀(Ω_Ω)`, 这也是本定理的上界 (见 [InaccModulus](InaccModulus.lagda.md)).

```agda
NF-ψ0Ω : ∀ {u} → NF u → Ctbl u → NF (ψ0Ω u)
NF-ψ0Ω nu cu = n∷ (nψ n[] c[] (n∷ (nψ nu cu n[] (λ ())) n[] tt) bnd) n[] tt
  where
    bnd : Bnd [] (ψᵗ _ [] ∷ [])
    bnd (vh _)   = []<
    bnd (vd _ ())
    bnd (vt ())

tower : ℕ → T
tower zero    = []
tower (suc n) = ψ0Ω (tower n)

NF-tower : ∀ n → NF (tower n)
Ct-tower : ∀ n → Ctbl (tower n)
NF-tower zero    = n[]
NF-tower (suc n) = NF-ψ0Ω (NF-tower n) (Ct-tower n)
Ct-tower zero    = c[]
Ct-tower (suc n) = c∷ c[]

module Labels (fe : Funext) where
  open Main fe

  label-tower : ∀ n → LabN (dz (Tr.S Dᵐ (tower n))) (tower n)
  label-tower n = label-NF (tower n) (NF-tower n) (Ct-tower n)

  label-BO : LabN (dz (Tr.S Dᵐ BO)) BO
  label-BO = label-tower 2

  label-ψBO : LabN (dz (Tr.S Dᵐ ψBO)) ψBO
  label-ψBO = label-tower 3

  label-ψε : LabN (dz (Tr.S Dᵐ ψε)) ψε
  label-ψε = label-NF ψε (NF-ψ0Ω (NF-ψ0Ω (n∷ (nψ n[] c[] n[] (λ ())) n[] tt) (c∷ c[])) (c∷ c[])) (c∷ c[])
```

## §2 范数的读取表: `wk (L t)` 对 `sz t`

`sz t ≤ wk (L t)` 是定理 (`Lift₂.sz≤wk`). 表说明两点: 对自然数与 ω 的倍数相等; 到 `ε₀` 之上 `wk` 已比 `sz` 大, 所以它只是上界, 不是范数本身.

```agda
isOT-tbl : (isOTᵉ ω ∧ isOTᵉ ε₀ ∧ isOTᵉ BO ∧ isOTᵉ ψε ∧ isOTᵉ ψBO) ≡ true
isOT-tbl = refl

wk-3 : wk (L (natᵗ 3)) ≡ 3
wk-3 = refl

ωω : T
ωω = ψᵗ [] (ω) ∷ []

wk-ω : wk (L ω) ≡ 2
wk-ω = refl
sz-ω : sz ω ≡ 2
sz-ω = refl

wk-ωω : wk (L ωω) ≡ 3
wk-ωω = refl
sz-ωω : sz ωω ≡ 3
sz-ωω = refl

wk-ε₀ : wk (L ε₀) ≡ 4
wk-ε₀ = refl
sz-ε₀ : sz ε₀ ≡ 3
sz-ε₀ = refl

wk-BO : wk (L BO) ≡ 5
wk-BO = refl
sz-BO : sz BO ≡ 4
sz-BO = refl
```

## §3 编译的否定

1. **`pad` 不规整** (`pad-notReg`), `Dᵐ` 在它上面确实答错 (`pad-wrong`): 模只对规整类成立, 这与 `D★-pad` 一致. 这条否定是必要的: 单调不够.
2. **模是紧的.** `j = 3`, `i = ω`: `μ = wk j` 不够 (`tight`), 要 `1 + wk j`.
3. **规整树不必可比.** `ω` 与 `ω⁺ = lim [1,2,…]` 都规整. `InaccStrike` 证过它们互不为节点. 所以类必须是**有向族**, 单棵树的 `Reg` 不够.

```agda
pad-notReg : Reg (lim (pad 10)) → ⊥
pad-notReg (st , _) with st 0
... | ()

isRise : ∀ {j i} → Verdict j i → Bool
isRise rise      = true
isRise (pen _ _) = false

pad-wrong : isRise (Dᵐ (natL 1) (lim (pad 10))) ≡ true
pad-wrong = refl

tight : isRise (Dm 3 (natL 3) (lim natL)) ≡ true
tight = refl

tight′ : isRise (Dm 4 (natL 3) (lim natL)) ≡ false
tight′ = refl

Reg-nat : ∀ n → Reg (natL n)
Reg-nat zero    = tt
Reg-nat (suc n) = Reg-nat n

Reg-ω : Reg (lim natL)
Reg-ω = (λ n → ws0) , Reg-nat

Reg-ω⁺ : Reg (lim (λ n → natL (suc n)))
Reg-ω⁺ = (λ n → ws0) , (λ n → Reg-nat n)
```

## §4 与基线对照: 对角线

`diag-NF` (Standard) 说 `ψ₀(Ω_Ω)` 的 γ-链每一项都是可数标准形. 所以 `Dᵐ` 的翻译逐项带标签覆盖这条链; `ψ₀(Ω_Ω)` 本身下标不可数, 不在定理内.

```agda
open import OCF.Align.Standard using (diag-NF; diag-Ctbl)
open import OCF.Align.Correspond using (γᴱ)

module Diag (fe : Funext) where
  open Main fe

  label-γ : ∀ k → LabN (dz (Tr.S Dᵐ (γᴱ k))) (γᴱ k)
  label-γ k = label-NF (γᴱ k) (diag-NF k) (diag-Ctbl k)
```
