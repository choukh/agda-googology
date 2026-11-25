# 上折的配对否定: 摊平后的保留在哪些行成立

> 验收文件 (否定). 判决: 编译定理, 无前提; 本篇是 `YiUpNegFlat` 那条否定的边界 (正面). `YiUpNegFlat.FlatKeep` 的同形陈述 (摊平进孩子 c 的结点, 以经孩子 c 可达的目标折叠时, 以孩子层保留判定给出的槽位为根) 在 `upI` 上对后继 (`flat-suc`), ℕ 极限的指定孩子与一切孩子 (`flat-lim`, `flat-limu`), Ωₗ 的下标层侧与一切孩子 (`flat-ink`, `flat-inu`) 都成立.
> 所以失败的只有 Ωₗ 层的分支侧一行 (`YiUpNegFlat.up-never`); ℕ 极限的指定孩子一行要比较两个孩子号, 用的是 ℕ 上可判定的 `eqℕ`.
> 不否定什么. 工具: 保留判定的两侧归纳 `kp-ind₂` (同一条路径上两次调用 `kp` 走同一支).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpNegBound where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (eqℕ; eqℕ-refl)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold using (kp; kp⁼)
open import OCF.Lean.YiPhiNegK using (Kept)
open import OCF.Lean.YiUpBlock using (Upc)
import OCF.Lean.YiUpFold as F
open import OCF.Lean.YiUpNegFlat using (root⁼)
```

## 两侧归纳

```agda
mutual
  kp-ind₂ : (ℓ : L) (ε : Ev ℓ) (p : Pos ℓ) {j : L} (v : j ≤ ℓ) {X Y : Set} (R : X → Y → Set)
    {K : (q : Pos j) → (Br j q → Br ℓ p) → X} {d : X} {K′ : (q : Pos j) → (Br j q → Br ℓ p) → Y} {d′ : Y}
    → ((q : Pos j) (cv : Br j q → Br ℓ p) → R (K q cv) (K′ q cv)) → R d d′
    → R (kp ℓ ε p v K d) (kp ℓ ε p v K′ d′)
  kp-ind₂ ℓ        ε p       self      R hk hd = hk p (λ z → z)
  kp-ind₂ (suc a)  ε p       (ins v)   R hk hd = kp⁼-ind₂ a ε p v R hk hd
  kp-ind₂ (lim g)  ε (m , p) (inl n v) R hk hd with eqℕ m n
  ... | just refl = kp⁼-ind₂ (g m) (ε m) p v R hk hd
  ... | nothing   = hd
  kp-ind₂ (lim g)  ε (m , p) (inlu vs) R hk hd = kp⁼-ind₂ (g m) (ε m) p (vs m) R hk hd
  kp-ind₂ (Ωₗ k h) (ek , e) (inj₁ t)       (ink v)    R hk hd = kp⁼-ind₂ k ek t v R hk hd
  kp-ind₂ (Ωₗ k h) (ek , e) (inj₁ t)       (inb c v)  R hk hd =
    kp⁼-ind₂ (h c) (proj₂ (e c)) (psh (proj₁ (e c)) t) v R
      (λ q cv → hk q (λ z → pshBr (proj₁ (e c)) t (cv z))) hd
  kp-ind₂ (Ωₗ k h) (ek , e) (inj₁ t)       (inu vs)   R hk hd =
    kp⁼-ind₂ (h zero) (proj₂ (e zero)) (psh (proj₁ (e zero)) t) (vs zero) R
      (λ q cv → hk q (λ z → pshBr (proj₁ (e zero)) t (cv z))) hd
  kp-ind₂ (Ωₗ k h) (ek , e) (inj₂ (c , t)) (ink v)    R hk hd =
    kp⁼-ind₂ (h c) (proj₂ (e c)) t (v ∙ proj₁ (e c)) R hk hd
  kp-ind₂ (Ωₗ k h) (ek , e) (inj₂ (c , t)) (inu vs)   R hk hd = kp⁼-ind₂ (h c) (proj₂ (e c)) t (vs c) R hk hd
  kp-ind₂ (Ωₗ k h) (ek , e) (inj₂ (c , t)) (inb c′ v) R hk hd = hd

  kp⁼-ind₂ : (a : L) (ε : Ev a) (p : Pos⁼ a) {j : L} (v : j ≤ a) {X Y : Set} (R : X → Y → Set)
    {K : (q : Pos j) → (Br j q → Br⁼ a p) → X} {d : X} {K′ : (q : Pos j) → (Br j q → Br⁼ a p) → Y} {d′ : Y}
    → ((q : Pos j) (cv : Br j q → Br⁼ a p) → R (K q cv) (K′ q cv)) → R d d′
    → R (kp⁼ a ε p v K d) (kp⁼ a ε p v K′ d′)
  kp⁼-ind₂ a ε (inj₁ _) v R hk hd = hd
  kp⁼-ind₂ a ε (inj₂ p) v R hk hd = kp-ind₂ a ε p v R hk hd
```

## 保留判定交出槽位, 输出就以它为根

```agda
just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
just-inj refl = refl

keptΩ : ∀ {j} {q q′ : Pos j} (G′ : Br j q′ → Tr j) → q′ ≡ q → Kept q (Ω q′ G′)
keptΩ G′ refl = G′ , refl

root→kept : (a : L) (ε : Ev a) (t : Pos⁼ a) {j : L} (w : j ≤ a)
  (H : (q : Pos j) → (Br j q → Br⁼ a t) → Br j q → Tr j) (d : Tr j) (q : Pos j)
  → root⁼ a ε t w ≡ just q → Kept q (kp⁼ a ε t w (λ q′ cv → Ω q′ (H q′ cv)) d)
root→kept a ε t w H d q =
  kp⁼-ind₂ a ε t w (λ m o → m ≡ just q → Kept q o) (λ q′ cv e → keptΩ (H q′ cv) (just-inj e)) (λ ())
```

## `upI` 的五行

```agda
flat-suc : (a : L) (ε : Ev (suc a)) (B : Base (suc a)) (j : L) (w : j ≤ a) (β : Tr j) (b : Tr (suc a))
  (p : Pos a) (G : Br a p → Tr a) (q : Pos j)
  → root⁼ a ε (inj₂ p) w ≡ just q
  → Kept q (F.ψs (suc a) ε B j (ins w) β (Upc (suc a) tt b (Ω p G)))
flat-suc a ε B j w β b p G q = root→kept a ε (inj₂ p) w _ _ q

flat-lim : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) (j : L) (n : ℕ) (w : j ≤ g n) (β : Tr j)
  (b : Tr (lim g)) (p : Pos (g n)) (G : Br (g n) p → Tr (g n)) (q : Pos j)
  → root⁼ (g n) (ε n) (inj₂ p) w ≡ just q
  → Kept q (F.ψs (lim g) ε B j (inl n w) β (Upc (lim g) n b (Ω p G)))
flat-lim g ε B j n w β b p G q r rewrite eqℕ-refl n = root→kept (g n) (ε n) (inj₂ p) w _ _ q r

flat-limu : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) (j : L) (ws : (n : ℕ) → j ≤ g n) (β : Tr j)
  (b : Tr (lim g)) (n : ℕ) (p : Pos (g n)) (G : Br (g n) p → Tr (g n)) (q : Pos j)
  → root⁼ (g n) (ε n) (inj₂ p) (ws n) ≡ just q
  → Kept q (F.ψs (lim g) ε B j (inlu ws) β (Upc (lim g) n b (Ω p G)))
flat-limu g ε B j ws β b n p G q = root→kept (g n) (ε n) (inj₂ p) (ws n) _ _ q

flat-ink : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (w : j ≤ k) (β : Tr j)
  (b : Tr (Ωₗ k h)) (c : Tr k) (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) (q : Pos j)
  → root⁼ (h c) (proj₂ (proj₂ ε c)) (inj₂ p) (w ∙ proj₁ (proj₂ ε c)) ≡ just q
  → Kept q (F.ψs (Ωₗ k h) ε B j (ink w) β (Upc (Ωₗ k h) c b (Ω p G)))
flat-ink k h ε B j w β b c p G q = root→kept (h c) (proj₂ (proj₂ ε c)) (inj₂ p) (w ∙ proj₁ (proj₂ ε c)) _ _ q

flat-inu : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (ws : (c : Tr k) → j ≤ h c)
  (β : Tr j) (b : Tr (Ωₗ k h)) (c : Tr k) (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) (q : Pos j)
  → root⁼ (h c) (proj₂ (proj₂ ε c)) (inj₂ p) (ws c) ≡ just q
  → Kept q (F.ψs (Ωₗ k h) ε B j (inu ws) β (Upc (Ωₗ k h) c b (Ω p G)))
flat-inu k h ε B j ws β b c p G q = root→kept (h c) (proj₂ (proj₂ ε c)) (inj₂ p) (ws c) _ _ q
```

前提可满足: 各行的 `root⁼ … ≡ just q` 例如 `YiUpNegFlat.root-p₀` (孩子层 h₃ c₀ 的 `wc c₀`, 即 `flat-limu` 那一行的孩子路径).
