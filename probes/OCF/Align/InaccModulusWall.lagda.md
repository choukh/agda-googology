# 层号判决的范数模: 奇异下标处的墙 (验收)

> **验收节.** 结论在 [InaccModulus](InaccModulus.lagda.md). §1 说自然数值的模在 `limᴼ` 目标上不可能: `Ω_ω < Ω_Ω`, 但 `Ω_ω` 大于**每个** `Ω_Ω[n]`. §2 是把同一方法推到 `limᴼ` 的唯一一次尝试: 走步采样换掉 `D★` 的 `nrm`, 分支下标仍由 `toT` 读取. 它是候选, 不是定理; 只记录它走到哪里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulusWall where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccStrikeCommute using (module Tr)
open import OCF.Align.InaccStrikeOracle using (natT′)
import OCF.Align.EBO as E
open E using (T; PT; cmpᵀ; fsT; Ωt; sucT; 𝟏; Cmp; lt; eq; gt) renaming (ψ to ψᵗ; natT to natᵗ)
```

## §1 自然数值的模失败

```agda
Ωn : ℕ → T
Ωn n = Ωt (natᵗ n)

ω OO : T
ω  = ψᵗ [] (𝟏 ∷ []) ∷ []
OO = Ωt (Ωn 1)

below : cmpᵀ (Ωt ω) OO ≡ lt
below = refl

nat-fails : ∀ n → cmpᵀ (Ωt ω) (fsT OO (natᵗ n)) ≡ gt
nat-fails zero    = refl
nat-fails (suc n) = refl

first-witness : cmpᵀ (Ωt ω) (fsT OO (sucT ω)) ≡ lt
first-witness = refl
```

## §2 候选 `D⁺`

```agda
wk⁺ : Lv → ℕ
wk⁺ zero       = 0
wk⁺ (suc a)    = suc (wk⁺ a)
wk⁺ (lim f)    = suc (wk⁺ (f 1))
wk⁺ (limᴼ k g) = suc (wk⁺ k ⊔ wk⁺ (g (natT′ 1)))

sam⁺ : Lv → Lv → Bool
sam⁺ zero    zero    = true
sam⁺ (suc a) (suc b) = sam⁺ a b
sam⁺ (lim f) (lim h) = sam⁺ (f (suc (wk⁺ (lim f) ⊔ wk⁺ (lim h)))) (h (suc (wk⁺ (lim f) ⊔ wk⁺ (lim h))))
sam⁺ (limᴼ k g) (limᴼ k′ g′) =
  sam⁺ k k′ ∧ sam⁺ (g (natT′ (suc (wk⁺ (limᴼ k g) ⊔ wk⁺ (limᴼ k′ g′))))) (g′ (natT′ (suc (wk⁺ (limᴼ k g) ⊔ wk⁺ (limᴼ k′ g′)))))
sam⁺ _ _ = false

D⁺   : Oracle
toT⁺ : ∀ k → Lv → Ordᴸ k
Dmp  : ℕ → (j i : Lv) → Verdict j i
svp  : ∀ j i → Bool → Verdict j i → Verdict j (suc i)
lvp  : ∀ μ j (h : ℕ → Lv) → Verdict j (h μ) → Verdict j (lim h)
omV  : ∀ μ j k (g : Ordᴸ k → Lv) → Bool → Verdict j (limᴼ k g)
omW  : ∀ μ j k (g : Ordᴸ k → Lv) → Verdict j k → Verdict j (limᴼ k g)
omX  : ∀ j k (g : Ordᴸ k → Lv) (x : Ordᴸ k) → Verdict j (g x) → Verdict j (limᴼ k g)
toTv : ∀ k k′ (g : Ordᴸ k′ → Lv) → Verdict k′ k → Ordᴸ k

D⁺ j i = Dmp (suc (wk⁺ j)) j i
Dmp μ j zero       = rise
Dmp μ j (suc i)    = svp j i (sam⁺ j i) (Dmp μ j i)
Dmp μ j (lim h)    = lvp μ j h (Dmp μ j (h μ))
Dmp μ j (limᴼ k g) = omV μ j k g (sam⁺ j k)

svp j i true  V         = pen (inj₁ tt) (cast i j)
svp j i false (pen r b) = pen (inj₂ r) b
svp j i false rise      = rise
lvp μ j h (pen r b) = pen (μ , r) b
lvp μ j h rise      = rise
omV μ j k g true  = pen (inj₁ (inj₁ tt)) (cast k j)
omV μ j k g false = omW μ j k g (Dmp μ j k)
omW μ j k g (pen r b) = pen (inj₁ (inj₂ r)) b
omW μ j k g rise      = omX j k g (suc (toT⁺ k j)) (Dmp (suc (wk⁺ j)) j (g (suc (toT⁺ k j))))
omX j k g x (pen r b) = pen (inj₂ (x , r)) b
omX j k g x rise      = rise

toT⁺ k zero        = zero
toT⁺ k (suc a)     = suc (toT⁺ k a)
toT⁺ k (lim f)     = lim (λ n → toT⁺ k (f n))
toT⁺ k (limᴼ k′ g) = toTv k k′ g (D⁺ k′ k)
toTv k k′ g (pen r b) = limᵢ r (λ y → toT⁺ k (g (b (outL k r y))))
toTv k k′ g rise      = lim (λ n → toT⁺ k k′ + toT⁺ k (g (natT′ n)))

chkV : ∀ {j i} → Cmp → Verdict j i → Bool
chkV {j} {i} lt (pen r b) = sam⁺ j (at i r)
chkV lt rise = false
chkV eq (pen r b) = false
chkV gt (pen r b) = false
chkV eq rise = true
chkV gt rise = true

L⁺ : T → Lv
L⁺ = Tr.L D⁺

chk : T → T → Bool
chk u v = chkV (cmpᵀ u v) (D⁺ (L⁺ u) (L⁺ v))
```

## §3 `D⁺` 的表

`D⁺` 通过下面九个点, 但 `D★` 错的两个点 (`Ω_Ω` 对自身, `Ω_{Ω₂}` 对 `Ω_Ω`) 它照样错, 另加 `Ω_Ω+1` 对 `Ω_Ω`. 相同目标 `Ω_Ω` 处它取分支 `x = suc (toT⁺ 0 j)`, `x` 是 `j` 的读数, 不在任何规整族里, 于是 `g x` 里出现被采样当成 `j` 的节点. 这正是 `Fam` 的前提失效的地方: 分支下标不是 `F` 里的项.

```agda
good-1 : chk (Ωn 1) (Ωn 2) ≡ true
good-1 = refl
good-2 : chk (Ωn 2) (Ωn 1) ≡ true
good-2 = refl
good-3 : chk (Ωn 1) (Ωn 1) ≡ true
good-3 = refl
good-4 : chk ω (Ωn 1) ≡ true
good-4 = refl
good-5 : chk (Ωt ω) (Ωt ω) ≡ true
good-5 = refl
good-6 : chk (Ωn 3) (Ωt ω) ≡ true
good-6 = refl
good-7 : chk (Ωt ω) OO ≡ true
good-7 = refl
good-8 : chk (Ωn 2) OO ≡ true
good-8 = refl
good-9 : chk OO (Ωt ω) ≡ true
good-9 = refl

⁺-wrong-OO : chk OO OO ≡ false
⁺-wrong-OO = refl

⁺-wrong-OO+1 : chk (sucT OO) OO ≡ false
⁺-wrong-OO+1 = refl

⁺-wrong-Ω₂ : chk (Ωt (Ωn 2)) OO ≡ false
⁺-wrong-Ω₂ = refl
```
