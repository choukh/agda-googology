# YiDiag 塔的第 3 项：根上的链不累加的闭项与合法性证书

**判决：编译定理 (第 3 层)，无前提。** 闭项 `T₃ : R` 把 `tw 3` 折到第 0 层 (读法 ψ₀(Ω_Ω)，读法不是定理)；`T₃-legal : Lgl zero T₃`。
根上的链 `pt 0 = top`，`pt (n+1) = F (pt n)` (下一点就是这一点上的折叠值)，`T₃` 的第 `n` 项是 `F (pt n)`；内部结点的链也不累加。
合法性靠 `root-mono` (`F` 沿第一位置单调)。值与结构的验收在 [YiDiagAcc](YiDiagAcc.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDiagTw3 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiDiagCore
open import OCF.Lean.YiDiagFold
open import OCF.Lean.YiDiagLegal
```

## 1 第 0 层的树作层号

`lv η`：第 0 层的树读成的层号的 `Lv`，对树结构递归，不读合法性证明。合法性只给出相邻两支之间的路径 (`lv-L`)。

```agda
R : Set
R = Raw zero

⌜_⌝ : R → LF
⌜ η ⌝ = up zero η

lv : (η : R) → Lv ⌜ η ⌝
lv G.zero = v0
lv (G.suc a) = vs (lv a)
lv (G.lim f) = vl (λ n → lv (f n))
lv G.top = vs v0

cp→≤ᵛ : ∀ {a} b → Cp zero a b → lv a ≤ᵛ lv b
cp→≤ᵛ b (inj₁ refl) = rf
cp→≤ᵛ (G.suc b) (inj₂ p) = ps (cp→≤ᵛ b p)
cp→≤ᵛ (G.lim f) (inj₂ (n , p)) = pl n (cp→≤ᵛ (f n) p)
cp→≤ᵛ G.top (inj₂ refl) = ps rf

lv-L : ∀ η → Lgl zero η → LvL (lv η)
lv-L G.zero l = tt
lv-L (G.suc a) l = lv-L a l
lv-L (G.lim f) (st , lf) = (λ n → cp→≤ᵛ (f (suc n)) (st n)) , (λ n → lv-L (f n) (lf n))
lv-L G.top l = tt
```

## 2 各支的折叠，沿第一位置单调

`F η`：`top` 在第 `⌜ η ⌝` 层上折到第 0 层。`F` 不读合法性证明，所以 `root-mono` 不要求两边的证明一致。

```agda
F : R → R
F η = Ψ zero (lv η) (λ _ → tt) G.top

root-mono : ∀ {a} b → Cp zero a b → Cp zero (F a) (F b)
root-mono b p = top-mono (cp→≤ᵛ b p) _ _

F-lgl : ∀ η → Lgl zero η → Lgl zero (F η)
F-lgl η l = Ψ-lgl zero (lv η) (lv-L η l) _ G.top tt
```

## 3 闭项

```agda
pt : ℕ → R
pt = iter F G.top

pt-step : ∀ n → Cp zero (pt n) (pt (suc n))
pt-step zero = Ψ-low zero (vs v0) _ G.top (inj₁ refl)
pt-step (suc n) = root-mono _ (pt-step n)

pt-lgl : ∀ n → Lgl zero (pt n)
pt-lgl zero = tt
pt-lgl (suc n) = F-lgl (pt n) (pt-lgl n)

T₃ : R
T₃ = G.lim (λ n → F (pt n))

T₃-legal : Lgl zero T₃
T₃-legal = (λ n → pt-step (suc n)) , (λ n → pt-lgl (suc n))
```

## 4 行与它折的是 `tw 3`

`tw 3` 是层号 0 的 Ω 结点，第 `η` 支是 `top` 在第 `⌜ η ⌝` 层的读回；`T₃` 的根是这个结点的链行，链从 `top` 起，不累加。

```agda
tw₃-form : tw 3 ≡ lc zero (λ η → up ⌜ η ⌝ G.top)
tw₃-form = refl

T₃-start : pt 0 ≡ G.top
T₃-start = refl

T₃-term : T₃ ≡ G.lim (λ n → Ψ zero (lv (pt n)) (λ _ → tt) G.top)
T₃-term = refl

T₃-feedback : ∀ n → pt (suc n) ≡ F (pt n)
T₃-feedback n = refl
```
