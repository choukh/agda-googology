# Fold1: 接口 (不两段折的折叠的契约)

> 不含记号. 构造一路 Fold1, 否定一路 NegFold1 共用. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 [CRwBase](CRwBase.lagda.md) (种类结构, 高度, 第一位置 `⊲`, 合法 `LgB`, `⊞`, `step`, `sup`, `S⊥`, `Cd`).
>
> **接口定稿 2026-11-06 08:07 (首次编译通过).** 定稿后只增不改.
>
> **这一篇做什么.** 作者本轮 (原话) "摆脱: 改 '在上' 的折法". [CRwFold](CRwFold.lagda.md) 的同底折叠在 "在上" 处 (结点的种类在第 $j+1$ 层, 目标 $t\lhd j$) 走两段: 先把结点坍缩成第 $j$ 层的链, 再把链从 $j$ 折到 $t$. 兄弟位置的子项被直接折, 在上结点的分支里的子项被两段折, 两种折法在第一位置下不可比 (`NoAccStuck.route-mismatch`). 本接口约定的折叠 `Φ` 对可数层号的塔 `Tw m` (§1) 直接折到目标层 $t\lhd m$, 契约是:
>
> - **逐点** (`Φ-pt`, 字面等式): ℕ-极限子句不累加. 零与后继两个子句也写成字面等式 (`Φ-z`, `Φ-s`; 后继是部分积 `mul`, 这一处累加是契约的一部分, 两边的账在入口).
> - **合法由证书给出, 读输入合法** (`Lg`, `Φ-lg`): 各层的合法 `Lg m` 由构造一路给出; 第 $0$ 层的 `Lg` 推出标准 `LgB` (`lg₀`), 地板合法 (`lg-top`). 由 `NegNoAccPt.pt-no-total`, 逐点子句下证书不能不读输入.
> - **单调** (`Φ-mono`, 只对目标是第 $0$ 层): 被比较的两个输入 $a\lhd c$ 带字面公共上界 $c$, 且 $c$ 合法. 输入一侧的第一位置在世界 `Win m lm b` 里 (由目标层的界 $b$ 定出, 构造一路给出).
> - **值的函数, 对无 $\Omega$ 的输入** (`Φ-≤`): 无 $\Omega$-结点的两个输入, 值关系 $\le$ (§2, 不带世界) 下 $a\le c$ 推出 $\Phi\,a\le\Phi\,c$. 特例 `Φ-l11`: $\lim(1,1,\dots)$ 与 $1$ 折出互相 $\le$ 的树 (对照 `NegValCInst.acc-not-mono≤`).
>
> **律的定义域.** 律里出现的层号对只有 $(t, m)$, 带字面 $t\lhd m$ (公共上界 $m$, 且 $m$ 合法); 输入对 $(a, c)$ 在 `Φ-mono` 里带字面 $a\lhd c$ (公共上界 $c$), 在 `Φ-≤` 里带值关系 $a\le c$. **没有裸下标的比较律.** 界 $b$ (目标层的当前界) 在律里只作参数, 带合法 `Lg t b`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.Fold1If where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
```

## §1 可数层号的塔, 地板, 部分积

`Tw S m`: 层号 $m$ (可数树) 处的种类结构, 后继给 `step`, ℕ-极限给 `sup ℕ` (与 `CRwFold.Tw` 同一形状, 这里独立写出, 不导入 `CRwFold`). `top m`: 第 $m$ 层的地板 (后继层取新种类的 $\Omega$-结点, ℕ-极限取部分和). `mul x n` $=x\boxplus\cdots\boxplus x$ ($n+1$ 个).

```agda
Tw : KS → Cd → KS
Tw S hz = S
Tw S (hs x) = step (Tw S x)
Tw S (hl f) = sup ℕ (λ n → Tw S (f n))
Tw S (hΩ () _)

Lv : Cd → KS
Lv = Tw S⊥

module _ {S : KS} where
  mul : HB S → ℕ → HB S
  mul x zero = x
  mul x (suc n) = mul x n ⊞ x

topT : ∀ S → HB S → ∀ m → HB (Tw S m)
ΣT : ∀ S → HB S → (f : ℕ → Cd) → ℕ → HB (Tw S (hl f))
topT S b hz = b
topT S b (hs x) = hΩ (inj₂ tt) up
topT S b (hl f) = hl (ΣT S b f)
topT S b (hΩ () _)
ΣT S b f zero = ι 0 (topT S b (f 0))
ΣT S b f (suc n) = ΣT S b f n ⊞ ι (suc n) (topT S b (f (suc n)))

top : ∀ m → HB (Lv m)
top = topT S⊥ hz
```

## §2 值关系 (不带世界), 无 $\Omega$

`_≤ᵛ_`: 与 `Fab5ValRel` 的规则同名同形, 只去掉世界与坐标的条件 ($\Omega$-极限在右边时任取坐标, 两边都是 $\Omega$-结点时逐坐标). 律 `Φ-≤` 只用在无 $\Omega$ 的输入上 (`OF`), 那里 $\Omega$ 的两条规则用不到. `one`, `l11`: $1$ 与 $\lim(1,1,\dots)$.

```agda
module _ {S : KS} where
  infix 4 _≤ᵛ_
  data _≤ᵛ_ : HB S → HB S → Set where
    z≤  : ∀ {b} → hz ≤ᵛ b
    s≤s : ∀ {a b} → a ≤ᵛ b → hs a ≤ᵛ hs b
    ≤s  : ∀ {a b} → a ≤ᵛ b → a ≤ᵛ hs b
    l≤  : ∀ {f b} → (∀ n → f n ≤ᵛ b) → hl f ≤ᵛ b
    ≤l  : ∀ {a f} n → a ≤ᵛ f n → a ≤ᵛ hl f
    ≤Ω  : ∀ {a κ g} c → a ≤ᵛ g c → a ≤ᵛ hΩ κ g
    Ω≤Ω : ∀ {κ g g′} → (∀ c → g c ≤ᵛ g′ c) → hΩ κ g ≤ᵛ hΩ κ g′

  OF : HB S → Set
  OF hz = ⊤
  OF (hs h) = OF h
  OF (hl f) = ∀ n → OF (f n)
  OF (hΩ _ _) = ⊥

  one : HB S
  one = hs hz

  l11 : HB S
  l11 = hl (λ _ → one)
```

## §3 契约

`Φ m lm t pt b h`: 把第 $m$ 层的高度 $h$ 折到第 $t$ 层 ($t\lhd m$, $m$ 合法), 目标层的当前界 $b$.

```agda
record Fold1If : Set₁ where
  field
    Φ     : (m : Cd) → LgB m → (t : Cd) → t ⊲ m → HB (Lv t) → HB (Lv m) → HB (Lv t)
    Φ-z   : ∀ m lm t pt b → Φ m lm t pt b hz ≡ hs hz
    Φ-s   : ∀ m lm t pt b h → Φ m lm t pt b (hs h) ≡ hl (mul (Φ m lm t pt b h))
    Φ-pt  : ∀ m lm t pt b f → Φ m lm t pt b (hl f) ≡ hl (λ n → Φ m lm t pt b (f n))
    Lg    : ∀ m → HB (Lv m) → Set
    lg₀   : ∀ h → Lg hz h → LgB h
    lg-top : ∀ m → LgB m → Lg m (top m)
    Φ-lg  : ∀ m lm t pt b → Lg t b → ∀ h → Lg m h → Lg t (Φ m lm t pt b h)
    Win   : ∀ m → LgB m → HB (Lv hz) → Wd (Lv m)
    Φ-mono : ∀ m lm (pt : hz ⊲ m) {b a c} → Lg hz b → Lg m c → a ⊲[ Win m lm b ] c →
             Φ m lm hz pt b a ⊲ Φ m lm hz pt b c
    Φ-≤   : ∀ m lm t pt b {a c} → OF a → OF c → a ≤ᵛ c → Φ m lm t pt b a ≤ᵛ Φ m lm t pt b c
    Φ-l11 : ∀ m lm t pt b → (Φ m lm t pt b l11 ≤ᵛ Φ m lm t pt b one) × (Φ m lm t pt b one ≤ᵛ Φ m lm t pt b l11)
```
