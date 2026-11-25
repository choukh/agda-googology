# YiLvFold 第 2 站：层号 ω 的结点，以及只读裸层号的派发到哪里为止

**判决 (编译定理)：`ψ₀ (Ω̂ (suc ω))` 合法 (`fold-Ωω1-legal`)，折叠就是 [YiLvFold](YiLvFold.lagda.md) 的那一个；派发 `wayᵇ` 在目标层 ω
及其下完全 (`complete-ω`, `complete-sub`)。读法 ψ₀(Ω_{ω+1})，没有值的定理。** 到 `suc ω` 为止：`wayᵇ` 在目标层 `suc ω` 上漏掉层号 ω
(`bare-incomplete`)；派发参数在 `tw 3` 的带守卫分支的层号上处处完全则 LPO (`branch-complete→lpo`，接否定路的 `bare-way→lpo`)。
一般的 `K`：闭项对任意派发合法 (`General.fold-K-legal`)，派发的完全性没有；不否定读位置或读证书的派发。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvFoldLim where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (Ω̂; cO; up; raw1)
open import OCF.Align.YiIrrIf using (R; Legal; iterate; self; fst; read0)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvNegCompare using (At)
import OCF.Align.YiLvNegKeep as N
open import OCF.Align.YiLvIf using (Plain; lev; Tri; below; above; same; compare)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase
open import OCF.Align.YiIrrFoldSeed using (Seedᶠ)
open import OCF.Align.YiLvFold using (module Fold)
open import OCF.Align.YiLvFoldFin
```

## 1 目标层 ω 上的派发

层号 `sucʲ 0` 的结点保留在槽位 `(j+1 , inj₁)`；这个槽位只由结点的层号决定，所以同一棵树的两处出现得到同一个输出。

```agda
hit-just : ∀ j (z : Maybe (fin (suc j) ≡ suc (fin j))) → z ≡ just refl →
  hitˡ fin (fin j) (suc j) z ≡ keep (suc j , inj₁ tt) refl
hit-just j .(just refl) refl = refl

way-ω-at : ∀ j n → n ≡ j →
  hitˡ fin (fin j) (suc n) (eqᶠ (fin (suc n)) (suc (fin j))) ≡
  keep (suc j , inj₁ tt) refl
way-ω-at j .j refl = hit-just j _ (cong (map (cong suc)) (eqᶠ-fin j))

way-ω : ∀ j → wayᵇ ω (fin j) ≡ keep (suc j , inj₁ tt) refl
way-ω j = way-ω-at j (sizeᶠ (fin j)) (size-fin j)

lev-fin : ∀ n (r : Pre (fin n)) → Σ ℕ λ j → lev (fin n) r ≡ fin j
lev-fin (suc n) (inj₁ _) = n , refl
lev-fin (suc n) (inj₂ r) = lev-fin n r

complete-ω : ∀ (s : Pre ω) → IsKeep (wayᵇ ω (lev ω s))
complete-ω (n , r) =
  subst (λ k → IsKeep (wayᵇ ω k)) (sym (proj₂ (lev-fin n r)))
    (subst IsKeep (sym (way-ω (proj₁ (lev-fin n r)))) tt)

complete-at : ∀ k j → k ≡ fin j → ∀ (s : Pre k) → IsKeep (wayᵇ k (lev k s))
complete-at .(fin j) j refl s = complete-fin j s

-- ω 之下的每个目标层 (ω 里的位置) 上也完全.
complete-sub : ∀ (q : Pre ω) (s : Pre (lev ω q)) →
  IsKeep (wayᵇ (lev ω q) (lev (lev ω q) s))
complete-sub (n , r) =
  complete-at (lev (fin n) r) (proj₁ (lev-fin n r)) (proj₂ (lev-fin n r))

-- 保留行在目标层 ω 上的样子: 槽位写出来, 下界与分支域原样, 没有搬运.
keep-ω-row : ∀ j c (w : Lgl (fin j) c) (b : Nested (fin j) c) t
  (g : (η : Raw (fin j)) → .(Gd (fin j) c η) → LF)
  (d : Dom (lc (fin j) c w b t g)) →
  ψ ω (lc (fin j) c w b t g) d ≡
  G.lc (suc j , inj₁ tt) c
    (ψ ω t (Node.first (fin j) c w b t g d))
    (λ η e → ψ ω (g η e) (Node.branch (fin j) c w b t g d η e))
keep-ω-row j c w b t g d =
  cong (λ z → ψn ω (fin j) z c w b t g d) (way-ω j)
```

## 2 闭项 `ψ₀ (Ω̂ (suc ω))`

`Ω̂ (suc ω)` 是层号 ω 的结点，下界 `top`，第一支 `Ω̂ ω`，分支是读回 `up ω η`。目标层 0 上它走链行：
链在 `Raw ω` 里，由目标层 ω 的折叠推进，观察是目标层 0 的折叠。

```agda
Ωω-branch : (η : Raw ω) → .(Gd ω G.top η) → LF
Ωω-branch η e = up ω η (proj₂ (proj₂ e))

Ωω1-form : Ω̂ (suc ω) ≡ lc ω G.top tt tt (Ω̂ ω) Ωω-branch
Ωω1-form = refl

dom-Ωω1 : Dom (Ω̂ (suc ω))
dom-Ωω1 = dom-Ω̂ (suc ω) ω-plain ω-legal ω-seed

fold-Ωω1 : R
fold-Ωω1 = ψ zero (Ω̂ (suc ω)) dom-Ωω1

fold-Ωω1-legal : Lgl zero fold-Ωω1
fold-Ωω1-legal = ψ-legal zero tt (Ω̂ (suc ω)) dom-Ωω1

points : ℕ → Pt ω G.top
points = iterate (next ω G.top tt tt (Ω̂ ω) Ωω-branch dom-Ωω1)
  (startᴸ ω G.top tt tt)

fold-Ωω1-row : fold-Ωω1 ≡
  G.lim (λ i → out zero ω G.top tt tt (Ω̂ ω) Ωω-branch dom-Ωω1 (points i))
fold-Ωω1-row = refl

-- 回灌: 下一点是这一点加上目标层 ω 的折叠在这一点的分支上的输出.
fold-Ωω1-feedback : ∀ i → at (points (suc i)) ≡
  plus ω (at (points i))
    (out ω ω G.top tt tt (Ω̂ ω) Ωω-branch dom-Ωω1 (points i))
fold-Ωω1-feedback i =
  next-additive ω G.top tt tt (Ω̂ ω) Ωω-branch dom-Ωω1 (points i)

fold-Ωω1-grow : ∀ i → Dn ω (at (points i)) (at (points (suc i)))
fold-Ωω1-grow i = next-grow ω G.top tt tt (Ω̂ ω) Ωω-branch dom-Ωω1 (points i)

-- 第一支在下: Ω̂ ω 的折叠是 Ω̂ (suc ω) 的折叠的第一位置.
Ωω-below-Ωω1 : Cp zero fold-Ωω fold-Ωω1
Ωω-below-Ωω1 =
  ψ-position zero (Ω̂ ω) (Ω̂ (suc ω)) dom-Ωω dom-Ωω1
    (fst self)

-- 链的推进用的折叠在起点 top 的分支上: 第 1 项是保留结点, 槽位 (1 , inj₁) (有限测试).
test-keep : ψ ω (Ω̂ (fin 1)) (dom-Ωᶠ 1) ≡
  G.lc (1 , inj₁ tt) (cO zero) (ψ ω (Ω̂ zero) (dom-Ωᶠ 0))
    (λ η e → ψ ω (Ωᶠ-branch 0 η e)
      (Node.branch zero (cO zero) tt tt (Ω̂ zero) (Ωᶠ-branch 0) (dom-Ωᶠ 1) η e))
test-keep = refl
```

对一般的 `K` 同一个折叠也给出合法的闭项，对任意派发；`K` 的合法性只进无关的证书，输出不读它 (`fold-K-free`)。
这一条不说派发在 `K` 上完全；完全性只对 ω 证了。

```agda
plain-seed : ∀ K → Plain K → Seedᶠ K
plain-seed zero pl = tt
plain-seed (suc K) pl = plain-seed K pl
plain-seed (lim f) pl = λ n → plain-seed (f n) (pl n)

module General (way : ∀ m k → Way m k) (K : LF) (pl : Plain K) (lg : Legal K) where

  dom-K : Dom (Ω̂ (suc K))
  dom-K = dom-Ω̂ (suc K) pl lg (plain-seed K pl)

  fold-K : R
  fold-K = Fold.ψ way zero (Ω̂ (suc K)) dom-K

  fold-K-legal : Lgl zero fold-K
  fold-K-legal = Fold.ψ-legal way zero tt (Ω̂ (suc K)) dom-K

fold-K-free : ∀ way K pl (lg lg′ : Legal K) →
  General.fold-K way K pl lg ≡ General.fold-K way K pl lg′
fold-K-free way K pl lg lg′ = refl
```

## 3 实验：`Raw ω` 里两个不同分支上的位置

`YiLvIf.compare` 在 ω 上算得出 (有限测试)：位置 `(1 , inj₁)` 的层号是 0，`(3 , inj₂ inj₁)` 的层号是 1。
本路的保留行没有用它：它交出的槽位读合法性的路径，而上面的槽位只读结点的层号。沿 `Low-lev` 的搬运也没有用到 (`nodeAt`)。

```agda
test-compare : compare ω ω-plain ω-legal (1 , inj₁ tt) (3 , inj₂ (inj₁ tt)) ≡
  above (inj₁ tt) refl
test-compare = refl
```

## 4 只读裸层号的派发到哪里为止

`Complete way m`：目标层 `m` 上每个槽位的层号都被保留。`wayᵇ` 在 `suc ω` 上不完全：层号 ω 在槽位 `inj₁`，
而两个极限层号字面相等不能由形状判定。`branch-complete→lpo`：本路折叠的派发参数若在 `tw 3` 的带相关守卫的分支的层号上处处完全，
就是 LPO；这是把否定路的 `YiLvNegKeep.bare-way→lpo` 接到 `Fold` 的参数上。域是一切带守卫的分支，不是链点；只在链点上完全的派发没有被否定。

```agda
Complete : (∀ m k → Way m k) → LF → Set
Complete way m = ∀ (s : Pre m) → IsKeep (way m (lev m s))

ω-complete : Complete wayᵇ ω
ω-complete = complete-ω

bare-incomplete : Complete wayᵇ (suc ω) → ⊥
bare-incomplete h = h (inj₁ tt)

bare : ∀ {m k} → Way m k → At m k ⊎ ⊤
bare (keep s e) = inj₁ (s , e)
bare fold = inj₂ tt

bare-keep : ∀ {m k} (y : Way m k) → IsKeep y → N.IsKeep (bare y)
bare-keep (keep s e) h = tt

BranchComplete : (∀ m k → Way m k) → Set
BranchComplete way = ∀ (η : R) (e : Gd zero raw1 η) (q : Pre (read0 η)) →
  Complete way (lev (read0 η) q)

branch-correct : ∀ way → BranchComplete way → N.Correct (λ m k → bare (way m k))
branch-correct way c η e q .(lev (lev (read0 η) q) s) (s , refl) =
  bare-keep (way (lev (read0 η) q) (lev (lev (read0 η) q) s)) (c η e q s)

branch-complete→lpo : ∀ way → BranchComplete way → N.LPO
branch-complete→lpo way c =
  N.bare-way→lpo (λ m k → bare (way m k)) (branch-correct way c)
```
