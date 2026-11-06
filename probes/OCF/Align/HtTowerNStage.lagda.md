# 种类结构的对应 (一): 带包含的塔, 种类与世界的对应, 并的反例

> 不含记号. 入口 [HtTowerN](HtTowerN.lagda.md). [HtTowerFNeed](HtTowerFNeed.lagda.md) 的 `Need` 要把 `step (L j)` 的种类搬进 `L k` ($j<k$), 坐标来回换, 往返逐点相等. 对 [HtTowerU](HtTowerU.lagda.md) 的 `L`, $k\ge2$ 时坐标类型是 `HB (L j)` 与 `HB (Lev (up y))` 这样两个**不同的**类型 (`Lev` 只看高度的构造子, 嵌入 `up` 换了种类), 往返要对高度的 $\Omega$-分支 (函数) 相等, 判断要函数外延. 这里不去证它, 也不否定它 (它与函数外延相容), 而是**改塔**:
>
> - `L′ 0 = S₀`, `L′ (k+1) = step (L′ k) ⊕ Lev (Ωtop (L′ k))` (`⊕` 是两个种类结构的并, `sup Bool`). 下一级**字面地含着** `step (L′ k)`. 读法与 `L` 相同 (多出的一个分量在上确界之下; 判断).
> - **`need′`**: 对一切 $j<k$, `KMatch (step (L′ j)) (L′ k)`, 坐标映射是恒等, 往返是 `refl`. 一条对 $j<k$ 的证明递归的定理: 一步是 "进 `⊕` 的左分量", 再 "进 `step` 的旧种类".
> - **世界的对应**: 类型 `WMatch S S′ M`: `wm : Wd S′ → Wd S`, 界双向保持, 合法保持. **`wmatch′`**: 对一切 $j<k$, `L′ k` 的世界投影到 `step (L′ j)` 的世界, 界定义相等.
> - **`no-wmatch`**: 换成逐分量的并 `U′ = sup ℕ (step ∘ L′)` (`HtTowerU` 的 `U` 的做法), 世界的对应不存在: 种类 $(0,\mathrm{new})$ 与种类 $(1, \text{左}(0,\mathrm{new}))$ 在 `L′ 2` 里是**同一个种类**, 坐标相同, 在 `U′` 里却各有各的界 (世界的第 0 个与第 1 个分量互不相干). 一个 `wm` 不能同时保两个界 (反例: 两个界取 $0$ 与 $1$, 坐标取 $1$). 两个前提各自可满足 (`sat₀`, `sat₁`). 所以**对角要的并, 世界必须相干** (下一级的世界里装着上一级的世界), 不能是独立分量的积.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerNStage where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFNeed using (KMatch; km; to; fr; fr-to)
```

## §1 两个种类结构的并, 带包含的塔

```agda
two : KS → KS → Bool → KS
two S S′ true = S
two S S′ false = S′

infixl 6 _⊕ₖ_
_⊕ₖ_ : KS → KS → KS
S ⊕ₖ S′ = sup Bool (two S S′)

L′ : ℕ → KS
L′ zero = S₀
L′ (suc k) = step (L′ k) ⊕ₖ Lev (Ωtop (L′ k))
```

## §2 种类的对应: 一条定理对一切 $j<k$

```agda
kmComp : ∀ {S S′ S″} → KMatch S S′ → KMatch S′ S″ → KMatch S S″
kmComp M N = record
  { km = λ κ → km N (km M κ)
  ; to = λ κ c → to N (km M κ) (to M κ c)
  ; fr = λ κ c → fr M κ (fr N (km M κ) c)
  ; fr-to = λ κ c → trans (cong (fr M κ) (fr-to N (km M κ) (to M κ c))) (fr-to M κ c) }

kmStep : ∀ {S} → KMatch S (step S)
kmStep = record { km = inj₁ ; to = λ κ c → c ; fr = λ κ c → c ; fr-to = λ κ c → refl }

kmL : ∀ k → KMatch (step (L′ k)) (L′ (suc k))
kmL k = record { km = λ κ → true , κ ; to = λ κ c → c ; fr = λ κ c → c ; fr-to = λ κ c → refl }

need′ : ∀ k j → j <ᴺ k → KMatch (step (L′ j)) (L′ k)
need′ (suc j) j zero = kmL j
need′ (suc k) j (suc q) = kmComp (need′ k j q) (kmComp kmStep (kmL k))
```

## §3 世界的对应

```agda
record WMatch (S S′ : KS) (M : KMatch S S′) : Set where
  field
    wm  : Wd S′ → Wd S
    bd→ : ∀ {κ c w′} → Bd S′ (km M κ) (to M κ c) w′ → Bd S κ c (wm w′)
    bd← : ∀ {κ c w′} → Bd S κ c (wm w′) → Bd S′ (km M κ) (to M κ c) w′
    lgw : ∀ {w′} → LgW S′ w′ → LgW S (wm w′)
open WMatch public

wmatch′ : ∀ k j (q : j <ᴺ k) → WMatch (step (L′ j)) (L′ k) (need′ k j q)
wmatch′ (suc j) j zero = record { wm = λ w′ → w′ true ; bd→ = λ e → e ; bd← = λ e → e ; lgw = λ l → l true }
wmatch′ (suc k) j (suc q) = record
  { wm = λ w′ → wm (wmatch′ k j q) (proj₁ (w′ true))
  ; bd→ = λ e → bd→ (wmatch′ k j q) e
  ; bd← = λ e → bd← (wmatch′ k j q) e
  ; lgw = λ l → lgw (wmatch′ k j q) (proj₁ (l true)) }
```

## §4 逐分量的并没有世界的对应

`U′ = sup ℕ (step ∘ L′)`. 两个 `U′` 的种类: `κ0 = (0, new)` (坐标 `H₀`, 界在世界的第 0 个分量) 与 `κ1 = (1, 左 (0,new))` (坐标 `H₀`, 界在第 1 个分量里装着的 `L′ 1` 的世界的左分量). `need′` 把两个都送到 `L′ 2` 的同一个种类 `K₀` (`refl`).

```agda
FU′ : ℕ → KS
FU′ k = step (L′ k)

U′ : KS
U′ = sup ℕ FU′

κ0 κ1 : K U′
κ0 = 0 , inj₂ tt
κ1 = 1 , inj₁ (true , inj₂ tt)

K₀ : K (L′ 2)
K₀ = true , inj₁ (true , inj₂ tt)

same-kind : km (need′ 2 0 (suc zero)) (inj₂ tt) ≡ K₀
same-kind = refl

same-kind′ : km (need′ 2 1 zero) (inj₁ (true , inj₂ tt)) ≡ K₀
same-kind′ = refl

-- 每一级的一个世界 (取最小的分量)
dWLev : ∀ {S} (x : HB S) → Wd (Lev x)
dWLev hz = azero
dWLev (hs x) = dWLev x , hz
dWLev (hl f) = λ n → dWLev (f n)
dWLev (hΩ κ g) = λ c → dWLev (g c)

dW : ∀ k → Wd (L′ k)
dW zero = azero
dW (suc k) = λ { true → (dW k , hz) ; false → dWLev (Ωtop (L′ k)) }

-- U′ 的一个世界: 第 0 个分量的界是 0, 第 1 个分量里 L′ 1 的左分量的界是 1
w⋆ : Wd U′
w⋆ zero = azero , hz
w⋆ (suc zero) = (λ { true → (azero , hs hz) ; false → dWLev (Ωtop S₀) }) , hz
w⋆ (suc (suc k)) = dW (suc (suc k)) , hz

no-wmatch : ∀ (wm′ : Wd U′ → Wd (L′ 2)) →
  (∀ {c w} → Bd U′ κ1 c w → Bd (L′ 2) K₀ c (wm′ w)) →
  (∀ {c w} → Bd (L′ 2) K₀ c (wm′ w) → Bd U′ κ0 c w) → ⊥
no-wmatch wm′ h1 h0 with h0 {hs hz} {w⋆} (h1 {hs hz} {w⋆} hself)
... | ()
```

两个前提各自可满足: 只要求一个种类, 世界的对应就取那一个分量.

```agda
sat₁ : Σ (Wd U′ → Wd (L′ 2)) (λ wm′ → (∀ {c w} → Bd U′ κ1 c w → Bd (L′ 2) K₀ c (wm′ w)) × (∀ {c w} → Bd (L′ 2) K₀ c (wm′ w) → Bd U′ κ1 c w))
sat₁ = (λ w → λ { true → (proj₁ (w 1) , hz) ; false → dWLev (Ωtop (L′ 1)) }) , (λ e → e) , (λ e → e)

sat₀ : Σ (Wd U′ → Wd (L′ 2)) (λ wm′ → (∀ {c w} → Bd U′ κ0 c w → Bd (L′ 2) K₀ c (wm′ w)) × (∀ {c w} → Bd (L′ 2) K₀ c (wm′ w) → Bd U′ κ0 c w))
sat₀ = (λ w → λ { true → ((λ { true → w 0 ; false → dWLev (Ωtop S₀) }) , hz) ; false → dWLev (Ωtop (L′ 1)) }) , (λ e → e) , (λ e → e)
```
