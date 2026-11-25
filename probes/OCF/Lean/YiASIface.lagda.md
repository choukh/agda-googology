# 不同步引理: 共用接口 (构造一路与否定一路)

> 验收文件 (读记号, 读具体块), 两路共用, 定稿后只增不改. 判决: 只有陈述 (`Set`) 与定义, 无定理; 树、折叠、合法性一行不改.
> "不同步对": 参照项的余尾 Ω 下标低于目标层 (记号一侧保留结点), 树是槽位层不低于目标层的结点 (树一侧走对角). 先在 `YiAbsGIface` 的语言里写 (`Async.AsyncPair`, `Async.LowKeepAsync`, 高低的判据 `Cut` 作参数), 再在有限层号上写具体版本.
> 有限层号: 块、折叠、行、关系同 `YiAbsGFin` (`blkᶠ`, `foldᶠ`, `rowsᶠ`, `YiANFam.M`); `gradedᶠ` 的 `Bd` 取空, 这里另取 `gradedᴬ` (上下文是前缀 t₀, `app t₀ a` 是 ψ_j(t₀ + a), `Bd` 是 `GBᶠ`). 陈述: `LowKeepᶠ`, `LowKeepAsyncᶠ`, `Async₀`, `Async₀ᶜ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiASIface where

open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import OCF.Lean.YiLegBlock as Lg
open import OCF.Lean.YiLegOps using (Ωt; Ωt-nz)
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt)
open import OCF.Lean.YiLegFold using (Base; bs; B₀; ψs)
open import OCF.Lean.YiAbsLeg using (Bsᴸ; Btᴸ)
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiMEBase using (read; _⊴_)
open import OCF.Lean.YiANFam using (fin; M; ψᴺ; Ωᴺ)
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGFin using (blkᶠ; foldᶠ; rowsᶠ; slLᶠ; Nuᶠ)
```

## 抽象的陈述

`Cut`: 高低的判据, 作参数. `Below κ j`: 余尾下标 κ 低于目标层 j (参照一侧保留); `NotBelow j i`: 槽位层 i 不低于目标层 j (树一侧走对角).
`AsyncPair j a x`: a 的余尾是 Ω_{κ+1}, κ 低于 j; x 是槽位 p 上的结点, p 的槽位层不低于 j. `LowKeepAsync`: `LowKeep` 限制到这样的对.

```agda
module Async {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍′ : Val}
             (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍′) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻

  record Cut : Set₁ where
    field
      Below    : T → Lv → Set
      NotBelow : Lv → Lv → Set

  module _ (𝒞 : Cut) where
    open Cut 𝒞

    AsyncPair : ∀ {ℓ} (j : Lv) → T → Tr ℓ → Set
    AsyncPair {ℓ} j a x =
      Σ T λ κ → Σ (Sl ℓ) λ p → Σ (SlT ℓ p → Tr ℓ) λ g →
        CΩ a κ × Below κ j × (x ≡ nd p g) × NotBelow j (slL ℓ p)

    LowKeepAsync : Set
    LowKeepAsync = ∀ {ℓ j} (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (K : Cx ℓ j) → Gb ℓ b → Wl w → Bd b w β K
                 → ∀ {a x} → Gx ℓ x → AsyncPair j a x → R ℓ a x → R j (app K a) (ψ ℓ b j w β x)
```

## 有限层号: 路径与底的条件

`Sbᶠ n j`: 层号 `fin j` 是 `fin n` 或它下面的子层号; `pthᶠ` 是到它的路径 (律所管的路径就是这些).
`GBᶠ n B t₀`: 层号 `fin (suc n)` 的底 B 在每个真子层号 i 上的分量在 Ω 树之上, 且对着 ψ_i(t₀). `Bdᴬ`: 底值对着 ψ_j(t₀), 底满足 `GBᶠ` (层号 0 上无内容).

```agda
open Lg using (Tr; zero; _⊢_◃_)

data Sbᶠ : ℕ → ℕ → Set where
  s0 : ∀ {n} → Sbᶠ n n
  ss : ∀ {n j} → Sbᶠ n j → Sbᶠ (suc n) j

pthᶠ : ∀ {n j} → Sbᶠ n j → fin j ≤ fin n
pthᶠ s0     = self
pthᶠ (ss s) = ins (pthᶠ s)

record GBᶠ (n : ℕ) (B : Base (fin (suc n))) (t₀ : E.T) : Set where
  constructor mkGBᶠ
  field
    gΩ : ∀ {i} (si : Sbᶠ n i) → Ωt (fin i) ⊴ bs B (fin i) (ins (pthᶠ si))
    gM : ∀ {i} (si : Sbᶠ n i) → M i (ψᴺ i t₀) (bs B (fin i) (ins (pthᶠ si)))
open GBᶠ public

GBᴬ : (n : ℕ) → Bsᴸ (fin n) → E.T → Set
GBᴬ zero    b           t₀ = ⊤
GBᴬ (suc n) (ε , ρ , B) t₀ = GBᶠ n B t₀

gradedᴬ : Graded blkᶠ foldᶠ rowsᶠ refᴱ 𝕍
gradedᴬ = record
  { ℓ₀ = 0 ; v = read ; R = M ; Rd = λ n ν → ν ≡ E.natT n ; Nu = Nuᶠ ; bt = proj₁
  ; cl = ψᴺ ; Cx = λ _ _ → E.T ; app = λ {_} {j} t₀ a → ψᴺ j (t₀ ++ a)
  ; Bd = λ {n} {j} b w β t₀ → M j (ψᴺ j t₀) (proj₁ β) × GBᴬ n b t₀ }

domsᴬ : Doms blkᶠ foldᶠ
domsᴬ = record
  { Gx = λ _ _ → ⊤ ; Gb = λ n _ → Σ ℕ λ N → n ≡ suc N
  ; Wl = λ {j} {n} w → Σ (Sbᶠ n j) λ s → w ≡ pthᶠ s ; Gl = λ _ _ → ⊥ }
```

## 有限层号: 不同步对与两条陈述

κ 低于 j: κ 是 `natT i`, i < j (此时 ψ_j 保留余尾, `YiANFam.cmp-pen`). 槽位层 i 不低于 j: j ≤ i (此时折叠取回灌链的部分和极限).

```agda
cutᶠ : Async.Cut gradedᴬ domsᴬ
cutᶠ = record { Below = λ κ j → Σ ℕ λ i → (κ ≡ E.natT i) × (suc i ≤ⁿ j) ; NotBelow = λ j i → j ≤ⁿ i }

AsyncPairᶠ : ∀ {n} (j : ℕ) → E.T → Tr (fin n) → Set
AsyncPairᶠ = Async.AsyncPair gradedᴬ domsᴬ cutᶠ

LowKeepᶠ LowKeepAsyncᶠ : Set
LowKeepᶠ      = Laws.LowKeep gradedᴬ domsᴬ
LowKeepAsyncᶠ = Async.LowKeepAsync gradedᴬ domsᴬ cutᶠ
```

## 最小实例

参照 ψ₂(P + Ω₁), 对着第 3 层 Ω 树折到第 2 层的输出. `Async₀`: 对一切满足 `GBᶠ` 的底, 一切对着 ψ₂(P) 的底值. `Async₀ᶜ`: 闭的一例, 标准底 `B₀`, 底值是第 2 层 Ω 树, P 为空.
`Pair₀`: 最小实例里的对 (Ω₁, 第 3 层 Ω 树) 是不同步对, 且有关系 (这是经放宽得到的对).

```agda
Async₀ : Set
Async₀ = (ε : Ev (fin 3)) (ρ : Rt (fin 3)) (B : Base (fin 3)) (P : E.T) → GBᶠ 2 B P
       → (β : Tr (fin 2)) (nβ : fin 2 ⊢ zero ◃ β) → M 2 (ψᴺ 2 P) β
       → M 2 (ψᴺ 2 (P ++ Ωᴺ 1)) (ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ (Ωt (fin 3)))

Async₀ᶜ : Set
Async₀ᶜ = (ε : Ev (fin 3)) (ρ : Rt (fin 3))
        → M 2 (ψᴺ 2 (Ωᴺ 1)) (ψs (fin 3) ε ρ (B₀ (fin 3)) (fin 2) (ins self) (Ωt (fin 2)) (Ωt-nz (fin 2)) (Ωt (fin 3)))

Pair₀ : Set
Pair₀ = AsyncPairᶠ {n = 3} 2 (Ωᴺ 1) (Ωt (fin 3)) × M 3 (Ωᴺ 1) (Ωt (fin 3))
```
