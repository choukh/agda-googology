# 奇异下标的定时检验: 表, 墙与编译的否定 (验收)

> **验收节.** 结论在 [InaccSingular](InaccSingular.lagda.md). 这里只有有限检验与项上的事实.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccSingularAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccStrikeCommute using (module Tr)
open import OCF.Align.InaccTreeAccept using (diff)
open import OCF.Align.InaccModulusBase using (samᵐ; Dᵐ)
open import OCF.Align.InaccSingularSharp using (D♯)
import OCF.Align.EBO as E
open E using (T; PT; cmpᵀ; fsT; fsn; γT; cof; Ωt; sucT; 𝟏; Cmp; lt; eq; gt; c0; c1; cω; cΩ; pred) renaming (ψ to ψᵗ; natT to natᵗ)
```

## §1 项

`Ωn n` 与 `Ω₁ = Ωn 1`; `OO = Ω_Ω`; `(Ω_Ω)² = ψ_{Ω₁}(Ω_Ω)`, 因为 `ψ_u(b+1)[n] = ψ_u(b)·n` 给 `ψ_u(Ω_u)` 的读法 `Ω_u²`.

```agda
Ωn : ℕ → T
Ωn n = Ωt (natᵗ n)

ω Ω₁ Ω₂ OO OO+1 OO·2 OOsq Ωω ΩΩ₂ : T
ω    = ψᵗ [] (𝟏 ∷ []) ∷ []
Ω₁   = Ωn 1
Ω₂   = Ωn 2
OO   = Ωt Ω₁
OO+1 = sucT OO
OO·2 = ψᵗ Ω₁ [] ∷ ψᵗ Ω₁ [] ∷ []
OOsq = ψᵗ Ω₁ OO ∷ []
Ωω   = Ωt ω
ΩΩ₂  = Ωt Ω₂

ψ₀ : T → T
ψ₀ a = ψᵗ [] a ∷ []
```

## §2 `D♯` 的表

`L♯`, `chk♯` 同 Wall 的 `chk`: `lt` 要路径的落点与 `j` 在 `samᵐ` 下相同, 其余要 `rise`.

```agda
L♯ : T → Lv
L♯ = Tr.L D♯

chkV : ∀ {j i} → Cmp → Verdict j i → Bool
chkV {j} {i} lt (pen r b) = samᵐ j (at i r)
chkV lt rise = false
chkV eq (pen r b) = false
chkV gt (pen r b) = false
chkV eq rise = true
chkV gt rise = true

chk♯ : T → T → Bool
chk♯ u v = chkV (cmpᵀ u v) (D♯ (L♯ u) (L♯ v))

-- Ω₁ 作目标: 通过. `ψ₀(Ω₁)` 对 Ω₁ 的同样检验在 420 秒内没有算完 (单独运行 75 秒也超时), 没有结果
ok-1 : chk♯ [] Ω₁ ≡ true
ok-1 = refl
ok-2 : chk♯ (natᵗ 3) Ω₁ ≡ true
ok-2 = refl
ok-3 : chk♯ ω Ω₁ ≡ true
ok-3 = refl
ok-4 : chk♯ Ω₁ Ω₁ ≡ true
ok-4 = refl
ok-5 : chk♯ Ω₁ ω ≡ true
ok-5 = refl
```

## §3 `D♯` 不声称正确的点: 任务单上的四个点

`self-OO`, `right-*` 对, 但没有内容: 节点的 1-走步上有 `limᴼ` 时 `D♯` 一律答 `rise`, 这几个点恰好要 `rise`. 另外三个点答错 (`wrong-*`), 它们对应 `InaccSingularRead` 的三类读数. `count-*`: 连可数的 `j` 对 `Ω_Ω` 也错, 因为 `g x = Ω_{x}` 的 `k ≠ 0`, 而 `D♯` 在那里答 `rise`. 这些错误都在声明之外: `D♯` 只对 Ω₁ 目标声称正确.

```agda
self-OO : chk♯ OO OO ≡ true
self-OO = refl

wrong-Ωω : chk♯ Ωω OO ≡ false
wrong-Ωω = refl

wrong-OO+1 : chk♯ OO+1 OO·2 ≡ false
wrong-OO+1 = refl

wrong-Ω₂ : chk♯ OO ΩΩ₂ ≡ false
wrong-Ω₂ = refl

right-OO+1 : chk♯ OO+1 OO ≡ true
right-OO+1 = refl

right-Ω₂ : chk♯ ΩΩ₂ OO ≡ true
right-Ω₂ = refl

count-1 : chk♯ (natᵗ 2) OO ≡ false
count-1 = refl

count-2 : chk♯ (natᵗ 2) OO·2 ≡ false
count-2 = refl
```
