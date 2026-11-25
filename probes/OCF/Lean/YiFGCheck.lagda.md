# FGH 式折叠 (原型): 有限测试与行的形状

> 有限测试 (`refl`) 与两条编译定理, 不读记号, 不进成品. 行: 零, 后继的前两项, 结点保留与对角; 字面区分: 槽位严格低于目标则保留, 否则在槽位自己的层上取对角 (`kp-*`).
> 压平检查 (ω+1 一带): Ω_{ω+1} 折到第 0 层时, 对角的下标是第 ω 层的值 (`at`, `posW` 都是 `refl`), 且严格高于 Ω_ω (`idx-above`, 定理); 值是这棵第 ω 层的树沿 ω 折到第 0 层 (`ω1-row`). 所以链经过分支自己的层 ω, 不是订正前只经目标层的形状.
> 墙 (照第十八次审查的读法查): Ω 形状层号经指定孩子的路径, 坐标一行逐字是 "底 ⊞ 折到第 0 层再嵌回" (`M-row`, `M-tw1`); 塔第 n+1 项第 1 个迭代的孩子底族在一切层上都是这个形状 (`M-keel`). 龙骨的一步 (`Keel`): 下标沿 `ink self` 取在第 tw n 层, 孩子层号字面地在 `klᶠ n` 之上. 折叠的改法没有动 M 这一行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFGCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp)
open import OCF.Lean.YiFGFold
```

## 有限层号与 ω+1

```agda
fin : ℕ → L
fin zero    = zero
fin (suc n) = nd sS (λ _ → fin n)

ok-fin : (n : ℕ) → Ok (fin n)
ok-fin zero    = tt
ok-fin (suc n) = tt , λ _ → ok-fin n

ωL ω1 : L
ωL = nd sL fin
ω1 = nd sS (λ _ → ωL)

ok-ω : Ok ωL
ok-ω = (λ n → inc tt self) , ok-fin

ok-ω1 : Ok ω1
ok-ω1 = tt , λ _ → ok-ω
```

## 行

```agda
module Rows (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) where
  row-zero : Φ ℓ o B j w β zero ≡ suc⁺ β
  row-zero = refl

  row-suc₀ : ∀ x → proj₁ (Φ ℓ o B j w β (suc x)) ≡ lim _ _
  row-suc₀ x = refl

  row-node : ∀ p g → Φ ℓ o B j w β (Ω p g)
    ≡ nodeF (kp ℓ o p w) (λ z → Φ ℓ o B j w β (g z))
        (Φ ℓ o (jB ℓ o B (g (fromBr ℓ p zero))) j w (Φ ℓ o B j w β (g (fromBr ℓ p zero)))
           (g (fromBr ℓ p (proj₁ (jB ℓ o B (g (fromBr ℓ p zero)) (at ℓ p) (posW ℓ p))))))
  row-node p g = refl
```

后继的第 0 项是目标底, 第 1 项是折一次, 第 2 项是在折过一次的底族上再折一次 (`suc-terms`).

```agda
suc-terms : ∀ (ℓ : L) o B j w β x
  → (proj₁ (Φ ℓ o B j w β (suc x)) ≡ lim (λ n → proj₁ (proj₂ (iter (λ P → jB ℓ o (proj₁ P) x , Φ ℓ o (proj₁ P) j w (proj₂ P) x) (B , β) n))) _)
suc-terms ℓ o B j w β x = refl

suc-2 : ∀ (ℓ : L) o B j w β x
  → proj₂ (iter (λ P → jB ℓ o (proj₁ P) x , Φ ℓ o (proj₁ P) j w (proj₂ P) x) (B , β) 2)
    ≡ Φ ℓ o (jB ℓ o B x) j w (Φ ℓ o B j w β x) x
suc-2 ℓ o B j w β x = refl
```

## 字面区分: 自身或更高取对角, 严格低于保留

ω+1 的 Ω 树分支在第 ω 层: 目标是 ω (自身) 或 0 (更低的目标) 都不保留. 第 ω 层里孩子 3 那一层的槽位: 目标 ω 时严格低于, 保留; 目标 0 时不严格低于, 取对角.

```agda
pΩ : Pos ω1
pΩ = inj₂ (tt , inj₁ tt)

p3 : Pos ω1
p3 = inj₂ (tt , inj₂ (inj₂ (3 , inj₁ tt)))

kp-self : kp ω1 ok-ω1 pΩ (inc tt self) ≡ nothing
kp-self = refl

kp-above : kp ω1 ok-ω1 pΩ (z≤ ω1) ≡ nothing
kp-above = refl

kp-lower : kp ω1 ok-ω1 p3 (inc tt self) ≡ just (inj₂ (3 , inj₁ tt) , (λ z → z) , refl)
kp-lower = refl

kp-lower0 : kp ω1 ok-ω1 p3 (z≤ ω1) ≡ nothing
kp-lower0 = refl
```

## 压平检查: Ω_{ω+1} 折到第 0 层

首分支 `g₁ b₀`, 下标 `idx` 是首分支折到槽位自己的层 (第 ω 层, 路径 `inc tt self`, 底 Ω_ω) 的值.

```agda
g₁ : Tr ωL → Tr ω1
g₁ c = up zero tt (suc c) (z◃ c ◃s)

Ωω1 : proj₁ (Ωt ω1) ≡ Ω pΩ g₁
Ωω1 = refl

at-ω : at ω1 pΩ ≡ ωL
at-ω = refl

posW-ω : posW ω1 pΩ ≡ inc tt self
posW-ω = refl

b₀ω : Tr ω1
b₀ω = g₁ zero

idx : Tr⁺ ωL
idx = Φ ω1 ok-ω1 (B₀ ω1) ωL (inc tt self) (Ωt ωL) b₀ω

idx-above : ωL ⊢ proj₁ (Ωt ωL) ◃ proj₁ idx
idx-above = infl ω1 ok-ω1 (B₀ ω1) ωL (inc tt self) (Ωt ωL) b₀ω

ω1-row : ψ₀ᶠ ω1 ok-ω1 (proj₁ (Ωt ω1))
  ≡ Φ ω1 ok-ω1 (jB ω1 ok-ω1 (B₀ ω1) b₀ω) zero (z≤ ω1) (Φ ω1 ok-ω1 (B₀ ω1) zero (z≤ ω1) (Ωt zero) b₀ω) (g₁ (proj₁ idx))
ω1-row = refl
```

`g₁ (proj₁ idx)` 的坐标是第 ω 层的树 `suc idx`, 沿 ω 的一致路径折到第 0 层; 第 ω 层上不按孩子取对角 (`ω-lim`: Ω_ω+1 在第 ω 层折到第 0 层是 (底族, 底) 的迭代的极限, 第 0 项是目标底).

```agda
ω1-coord : ∀ (B : Base ω1) β → Φ ω1 ok-ω1 B zero (z≤ ω1) β (g₁ (proj₁ idx))
  ≡ Φ ωL ok-ω (λ i u → Φ ω1 ok-ω1 B i (inc tt u) (B i (inc tt u)) zero) zero (z≤ ωL)
      (Φ ω1 ok-ω1 B zero (z≤ ω1) β zero) (suc (proj₁ idx))
ω1-coord B β = refl

ω-lim : ∀ (B : Base ωL) β → proj₁ (Φ ωL ok-ω B zero (z≤ ωL) β (suc (proj₁ (Ωt ωL))))
  ≡ lim (λ n → proj₁ (proj₂ (iter (λ P → jB ωL ok-ω (proj₁ P) (proj₁ (Ωt ωL)) ,
                                  Φ ωL ok-ω (proj₁ P) zero (z≤ ωL) (proj₂ P) (proj₁ (Ωt ωL))) (B , β) n))) _
ω-lim B β = refl
```

## 墙: Ω 形状层号经指定孩子的路径

`M-row`: 对一切 c′, c, 坐标一行是 "x 沿同一路径的值 ⊞ y 以默认底折到第 0 层". `M-tw1`: 塔第 1 项的层号上, 目标是孩子 2 里的第 1 层 (路径 `inc c₂ (inc tt self)`), Ω 树的折叠保留第 0 层的槽位, 每个分支是 `suc β ⊞ ψ₀ᶠ (孩子 z 的 Ω 树)`, 与 z 和 c₂ 的关系无关.

```agda
M-row : ∀ (B : Base (tw 1)) j c′ (v : j ≤ (zero ⊕ ↑ zero c′)) β x c y e
  → Φ (tw 1) (Ok-tw 1) B j (inc c′ v) β (up x c y e)
    ≡ Φ (tw 1) (Ok-tw 1) B j (inc c′ v) β x ⊞ ψ₀ᶠ (zero ⊕ ↑ zero c) (proj₂ (Ok-tw 1) c) y
M-row B j c′ v β x c y e = refl

c₂ : Tr zero
c₂ = suc (suc zero)

i₁ : L
i₁ = nd sS (λ _ → zero)

M-tw1 : ∀ (B : Base (tw 1)) β → proj₁ (Φ (tw 1) (Ok-tw 1) B i₁ (inc c₂ (inc tt self)) β (proj₁ (Ωt (tw 1))))
  ≡ Ω (inj₂ (tt , inj₁ tt)) (λ z → proj₁ (suc⁺ β ⊞ ψ₀ᶠ (zero ⊕ ↑ zero z) (proj₂ (Ok-tw 1) z) (proj₁ (Ωt (zero ⊕ ↑ zero z)))))
M-tw1 B β = refl
```

## 龙骨的一步: 塔第 n+1 项的第 1 个迭代

对一切 n: Ω_{tw (n+1)} 的分支在下标层 tw n (目标 0 不保留, `kp-keel`); 下标 `zK` 是首分支沿 `ink self` 折到第 tw n 层的值, 严格高于 Ω_{tw n} (`zK-above`); 塔第 n+1 项是 (底族, 底) 迭代的极限 (`first`), 第 1 项是孩子层 `tw n ⊕ ↑ zK` 上 Ω 树的折叠 (`first-row`), 这个层号字面地在龙骨层号 `klᶠ n` 之上 (`keel-path`).

```agda
klᶠ : ℕ → L
klᶠ n = tw n ⊕ ↑ (tw n) (proj₁ (Ωt (tw n)))

module Keel (n : ℕ) where
  ℓK : L
  ℓK = tw (suc n)

  oK : Ok ℓK
  oK = Ok-tw (suc n)

  pK : Pos ℓK
  pK = inj₁ (inj₁ tt)

  gK : Tr (tw n) → Tr ℓK
  gK c = up zero c (proj₁ (Ωt (tw n ⊕ ↑ (tw n) c))) (proj₂ (Ωt (tw n ⊕ ↑ (tw n) c)))

  ΩK : proj₁ (Ωt ℓK) ≡ Ω pK gK
  ΩK = refl

  kp-keel : kp ℓK oK pK (z≤ ℓK) ≡ nothing
  kp-keel = refl

  at-keel : at ℓK pK ≡ tw n
  at-keel = refl

  posW-keel : posW ℓK pK ≡ ink self
  posW-keel = refl

  zK : Tr⁺ (tw n)
  zK = jB ℓK oK (B₀ ℓK) (gK zero) (tw n) (ink self)

  zK-above : tw n ⊢ proj₁ (Ωt (tw n)) ◃ proj₁ zK
  zK-above = infl ℓK oK (B₀ ℓK) (tw n) (ink self) (Ωt (tw n)) (gK zero)

  keel-path : klᶠ n ⊑ tw n ⊕ ↑ (tw n) (proj₁ zK)
  keel-path = ⊕⊑ (tw n) (◃→⊑ (tw n) zK-above)

  first : twᶠ (suc n) ≡ lim (λ m → proj₁ (proj₂ (iter (λ P → jB ℓK oK (proj₁ P) (proj₁ (Ωt ℓK)) ,
                       Φ ℓK oK (proj₁ P) zero (z≤ ℓK) (proj₂ P) (proj₁ (Ωt ℓK))) (B₀ ℓK , Ωt zero) m))) _
  first = refl

  first-row : Φ ℓK oK (B₀ ℓK) zero (z≤ ℓK) (Ωt zero) (proj₁ (Ωt ℓK))
    ≡ Φ ℓK oK (jB ℓK oK (B₀ ℓK) (gK zero)) zero (z≤ ℓK) (Φ ℓK oK (B₀ ℓK) zero (z≤ ℓK) (Ωt zero) (gK zero)) (gK (proj₁ zK))
  first-row = refl
```

墙进入这一项的位置: 第 1 个迭代里孩子 zK 的底族由 B′ = `jB … (gK zero)` 沿 `inc` 读出; 对一切层 i, 一切孩子 c, B′ 在 `inc c u` 上的值逐字是 `suc Ω_i ⊞ (Ω_{tw n} 折到第 0 层)` (`M-keel`), 与 c 和 i 的高低无关.

```agda
  M-keel : ∀ i c (u : i ≤ (tw n ⊕ ↑ (tw n) c))
    → jB ℓK oK (B₀ ℓK) (gK zero) i (inc c u) ≡ suc⁺ (Ωt i) ⊞ ψ₀ᶠ (tw n) (proj₂ oK zero) (proj₁ (Ωt (tw n)))
  M-keel i c u = refl
```

## 闭项

```agda
tw-root : ∀ n → twᶠ n ≡ lim _ _
tw-root n = refl

EBO-root : EBOᶠ ≡ lim _ _
EBO-root = refl
```
