# 抽象理论 (二): 块与折叠的框架

> 判决: 框架 (记录) 与编译定理, 无前提, 只导入 `YiAbsObs`. `Block`: 层号, 各层的树, 孩子下标与孩子层, 目标路径 (自身, 指定孩子), 嵌入, 头部观察, 第一位置序, 合法. `Fold`: 带底的折叠 ψ 与孩子的底 dn. 律是按层号陈述的谓词: `Hand` (指定孩子的交接, 即 J2), `HandU` (一致目标的交接), `Mono`, `Pres`.
> 定理: 某层上 `Hand` 加探针处可观察的回退, 弱判定该层孩子下标与探针的字面相等 (`hand→wdec`); 折叠在该层的那一行由 `Hand` 与 `Off` 确定时是 `YiAbsObs.Row` 的实例 (`rowOf`), 所以 "可 (弱) 判等" 是这一行存在的必要条件, 自反证据函数是充分条件. 对任何一棵树, 分支侧目标恰在一支上保留也弱判等 (`branch→wdec`, 不用 `Hand`).
> 不否定什么: `HandU` 与自身行不比较孩子. 实填在 `YiAbsInst`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsFrame where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import OCF.Lean.YiAbsObs
```

## 块

`inc ℓ c w`: 目标在孩子 c 里 (分支侧). `incU ℓ c₁ ws`: 目标对每个孩子各给一条路径 (c₁ 只说明这一层有孩子). 孩子层的树的类型 `ChT` 与 `Tr (chL ℓ c)` 之间留一个换型 `chT` (具体块里按层号的形状分情形, 每一情形是恒等).

```agda
record Block : Set₁ where
  infix 4 _⊑_ _◃_
  field
    Lv   : Set
    Tr   : Lv → Set
    Ch   : Lv → Set
    chL  : (ℓ : Lv) → Ch ℓ → Lv
    ChT  : (ℓ : Lv) → Ch ℓ → Set
    chT  : (ℓ : Lv) (c : Ch ℓ) → ChT ℓ c → Tr (chL ℓ c)
    _⊑_  : Lv → Lv → Set
    self : ∀ {ℓ} → ℓ ⊑ ℓ
    inc  : ∀ {j} (ℓ : Lv) (c : Ch ℓ) → j ⊑ chL ℓ c → j ⊑ ℓ
    incU : ∀ {j} (ℓ : Lv) → Ch ℓ → ((c : Ch ℓ) → j ⊑ chL ℓ c) → j ⊑ ℓ
    up   : ∀ {ℓ} → Tr ℓ → (c : Ch ℓ) → ChT ℓ c → Tr ℓ
    hd   : ∀ {ℓ} → Tr ℓ → Bool
    _◃_  : ∀ {ℓ} → Tr ℓ → Tr ℓ → Set
    Leg  : ∀ {ℓ} → Tr ℓ → Set
```

## 折叠与律

`ψ ℓ b j w β x`: 第 ℓ 层的树 x 折到目标 j (路径 w), b 是底 (连同层号的证据), β 是 x = 0 时的值 (类型 `Bt j`: 裸树, 或带 "非零" 证明的树); `ψβ` 是同一个输出再作偏移. `dn ℓ b c x`: 嵌入 `up x c y` 的孩子 y 用的底.

```agda
record Fold (𝔹 : Block) : Set₁ where
  open Block 𝔹
  field
    Bs   : Lv → Set
    LegB : (ℓ : Lv) → Bs ℓ → Set
    Bt   : Lv → Set
    LegT : (j : Lv) → Bt j → Set
    ψ    : (ℓ : Lv) → Bs ℓ → (j : Lv) → j ⊑ ℓ → Bt j → Tr ℓ → Tr j
    ψβ   : (ℓ : Lv) → Bs ℓ → (j : Lv) → j ⊑ ℓ → Bt j → Tr ℓ → Bt j
    dn   : (ℓ : Lv) → Bs ℓ → (c : Ch ℓ) → Tr ℓ → Bs (chL ℓ c)

  Hand : Lv → Set
  Hand ℓ = (b : Bs ℓ) (j : Lv) (c : Ch ℓ) (w : j ⊑ chL ℓ c) (β : Bt j) (x : Tr ℓ) (y : ChT ℓ c)
    → ψ ℓ b j (inc ℓ c w) β (up x c y)
    ≡ ψ (chL ℓ c) (dn ℓ b c x) j w (ψβ ℓ b j (inc ℓ c w) β x) (chT ℓ c y)

  HandU : Lv → Set
  HandU ℓ = (b : Bs ℓ) (j : Lv) (c₁ : Ch ℓ) (ws : (c : Ch ℓ) → j ⊑ chL ℓ c) (β : Bt j) (x : Tr ℓ)
    (c : Ch ℓ) (y : ChT ℓ c)
    → ψ ℓ b j (incU ℓ c₁ ws) β (up x c y)
    ≡ ψ (chL ℓ c) (dn ℓ b c x) j (ws c) (ψβ ℓ b j (incU ℓ c₁ ws) β x) (chT ℓ c y)

  Mono : Set
  Mono = (ℓ : Lv) (b : Bs ℓ) (j : Lv) (w : j ⊑ ℓ) (β : Bt j) {x y : Tr ℓ} → x ◃ y → ψ ℓ b j w β x ◃ ψ ℓ b j w β y

  Pres : Set
  Pres = (ℓ : Lv) (b : Bs ℓ) → LegB ℓ b → (j : Lv) (w : j ⊑ ℓ) (β : Bt j) → LegT j β
    → (x : Tr ℓ) → Leg x → Leg (ψ ℓ b j w β x)
```

## 探针与否定

探针固定层号 ℓ, 底, 目标 j, 嵌入所在的孩子 c₀ 与孩子树 y, 并对每个孩子各取一条目标路径 `w c′`.
`on`: 孩子自己的折叠的头部为真. `Offᴾ`: 目标在别的孩子里时, 折叠输出的头部为假 (回退可观察).

```agda
  record Probe (ℓ : Lv) : Set where
    field
      b  : Bs ℓ
      j  : Lv
      β  : Bt j
      x  : Tr ℓ
      c₀ : Ch ℓ
      y  : ChT ℓ c₀
      w  : (c′ : Ch ℓ) → j ⊑ chL ℓ c′
      on : hd (ψ (chL ℓ c₀) (dn ℓ b c₀ x) j (w c₀) (ψβ ℓ b j (inc ℓ c₀ (w c₀)) β x) (chT ℓ c₀ y)) ≡ true

    out : Ch ℓ → Tr j
    out c′ = ψ ℓ b j (inc ℓ c′ (w c′)) β (up x c₀ y)

  Offᴾ : ∀ {ℓ} → Probe ℓ → Set
  Offᴾ {ℓ} P = (c′ : Ch ℓ) → (Probe.c₀ P ≡ c′ → ⊥) → hd (Probe.out P c′) ≡ false

  hand→sep : ∀ {ℓ} → Hand ℓ → (P : Probe ℓ) → Offᴾ P → Sep (Probe.c₀ P)
  hand→sep {ℓ} H P O = record
    { f   = λ c′ → hd (out c′)
    ; on  = trans (cong hd (H b j c₀ (w c₀) β x y)) on
    ; off = O }
    where open Probe P

  hand→wdec : ∀ {ℓ} → Hand ℓ → (P : Probe ℓ) → Offᴾ P → (c′ : Ch ℓ) → WDec (Probe.c₀ P ≡ c′)
  hand→wdec H P O = sep→wdec (hand→sep H P O)

  hand→wdecα : ∀ {ℓ} → Hand ℓ → (P : Probe ℓ) → Offᴾ P → (K : Cantor (Probe.c₀ P))
    → ∀ α → AllF α ⊎ (Probe.c₀ P ≡ Cantor.cα K α → ⊥)
  hand→wdecα H P O K = sep→wdecα (hand→sep H P O) K
```

## 对任何一棵树: 分支侧目标不能恰在一支上保留

o 是第 ℓ 层的任意一棵树 (例如任何一种自身行写法在 `up x c₀ y` 上的输出). 以每个孩子里的目标折叠 o, 头部若在 c₀ 支为真, 在字面不同的支为假, 就弱判定与 c₀ 的字面相等. 不用 `Hand`.

```agda
  branch→sep : (ℓ : Lv) (b : Bs ℓ) (j : Lv) (β : Bt j) (c₀ : Ch ℓ) (w : (c′ : Ch ℓ) → j ⊑ chL ℓ c′) (o : Tr ℓ)
    → hd (ψ ℓ b j (inc ℓ c₀ (w c₀)) β o) ≡ true
    → ((c′ : Ch ℓ) → (c₀ ≡ c′ → ⊥) → hd (ψ ℓ b j (inc ℓ c′ (w c′)) β o) ≡ false)
    → Sep c₀
  branch→sep ℓ b j β c₀ w o on off = record { f = λ c′ → hd (ψ ℓ b j (inc ℓ c′ (w c′)) β o) ; on = on ; off = off }

  branch→wdec : (ℓ : Lv) (b : Bs ℓ) (j : Lv) (β : Bt j) (c₀ : Ch ℓ) (w : (c′ : Ch ℓ) → j ⊑ chL ℓ c′) (o : Tr ℓ)
    → hd (ψ ℓ b j (inc ℓ c₀ (w c₀)) β o) ≡ true
    → ((c′ : Ch ℓ) → (c₀ ≡ c′ → ⊥) → hd (ψ ℓ b j (inc ℓ c′ (w c′)) β o) ≡ false)
    → (c′ : Ch ℓ) → WDec (c₀ ≡ c′)
  branch→wdec ℓ b j β c₀ w o on off = sep→wdec (branch→sep ℓ b j β c₀ w o on off)
```

## 这一行是 `Row` 的实例

固定层号, 底, 目标, 偏移与 x 之后, 折叠在嵌入上的那一行是一个派发; `Hand` 是 `Same`.

```agda
  rowOf : (ℓ : Lv) (b : Bs ℓ) (j : Lv) (β : Bt j) (x : Tr ℓ)
    → (fb : (c′ : Ch ℓ) → j ⊑ chL ℓ c′ → (c : Ch ℓ) → ChT ℓ c → Tr j) → Row
  rowOf ℓ b j β x fb = record
    { C  = Ch ℓ
    ; H  = λ c → j ⊑ chL ℓ c
    ; Y  = ChT ℓ
    ; X  = Tr j
    ; hd = hd
    ; k  = λ c w y → ψ (chL ℓ c) (dn ℓ b c x) j w (ψβ ℓ b j (inc ℓ c w) β x) (chT ℓ c y)
    ; fb = fb }

  disp : (ℓ : Lv) (b : Bs ℓ) (j : Lv) (β : Bt j) (x : Tr ℓ)
    → (c′ : Ch ℓ) → j ⊑ chL ℓ c′ → (c : Ch ℓ) → ChT ℓ c → Tr j
  disp ℓ b j β x c′ w c y = ψ ℓ b j (inc ℓ c′ w) β (up x c y)

  hand→same : ∀ {ℓ} → Hand ℓ → (b : Bs ℓ) (j : Lv) (β : Bt j) (x : Tr ℓ)
    (fb : (c′ : Ch ℓ) → j ⊑ chL ℓ c′ → (c : Ch ℓ) → ChT ℓ c → Tr j)
    → RowLaws.Same (rowOf ℓ b j β x fb) (disp ℓ b j β x)
  hand→same H b j β x fb c w y = H b j c w β x y
```
