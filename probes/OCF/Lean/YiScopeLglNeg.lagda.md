# 作用域块的折叠: 结点的链步不保持合法 (有限反例)

验收文件 (否定). 判决: 编译定理, 无前提, 对象是 [YiScopeFold](YiScopeFold.lagda.md) 的 `F` 与 [YiScopeLegal](YiScopeLegal.lagda.md) 的 `Legal`. 层号 3 的合法闭树 `T` (`T-legal`) 折叠时, 孩子根上那个结点的链步
`R` (分支折到下标层, `step-is-R` 是 `refl`) 不合法 (`R-illegal`): 分支里 ℕ 极限的第 1 项越出保留区再进来, 那一份按 `col` 折叠, 第 0 项是保留的 (`A0-form`, `A1-form`).
否定的是 "链步保持合法" 这条归纳引理, **不是** "`F` 的输出合法" (这个 `T` 的输出合法与否这里不陈述). 不否定作用域块的路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiScopeLglNeg where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.YiScopeCore
open import OCF.Lean.YiScopeFold
open import OCF.Lean.YiScopeLegal
```

## 1 树

层号 1, 2, 3 是零的逐次后继. `pp` 是层 3 里进两次孩子的作用域 (那里是层 1 的根, 结点的下标是可数树).
`z0` 是 `pp` 上分支为零的结点; `z1 = z0 + z0` (作用域里的和: 左加数包回根再加). `S` 是 ℕ 极限 `z0, z1, z1, …`.

```agda
L1 L2 L3 : Level
L1 = sucᴸ zero
L2 = sucᴸ L1
L3 = sucᴸ L2

pp : Path L3
pp = down tt (down tt root)

z0 z1 : Tr ⊥ L3 pp
z0 = G.nd tt (λ _ → G.zero)
z1 = plus (wrap L3 pp z0) z0

f : ℕ → Tr ⊥ L3 pp
f zero = z0
f (suc n) = z1

S : Tr ⊥ L3 pp
S = G.lim f

t₂ : Tr ⊥ L3 (down tt root)
t₂ = G.into tt S

T : Raw L3
T = G.into tt (G.nd tt (λ _ → t₂))

z1-form : z1 ≡ G.nd tt (λ _ → G.up tt refl (G.up tt refl (G.into tt (G.into tt z0))))
z1-form = refl

z0-legal : Legal L3 pp z0
z0-legal = (λ η l → tt) , (λ η η′ l e l′ → inj₁ refl)

step0 : Cp z0 z1
step0 = inj₂ (inj₂ (inj₁ (inj₂ (inj₁ (inj₁ refl)))))

steps : ∀ n → Cp (f n) (f (suc n))
steps zero = step0
steps (suc n) = inj₁ refl

f-legal : ∀ n → Legal L3 pp (f n)
f-legal zero = z0-legal
f-legal (suc n) = (λ η l → z0-legal) , (λ η η′ l e l′ → inj₁ refl)

T-legal : Legal L3 root T
T-legal = (λ η l → steps , f-legal) , (λ η η′ l e l′ → inj₁ refl)
```

## 2 链步

`T` 折到任意层 `J` 时进孩子, 孩子根上的结点经层 1 里的链折叠; 链的第 1 点是 `top` 加上 `R`.

```agda
tp : Raw L1
tp = top L1 G.zero

R : Raw L1
R = F (λ v → v) L2 L1 kp tp (dn ⊥-elim L3 (down tt root) t₂)

T-fold : ∀ J b → F ⊥-elim L3 J col b T ≡ G.lim (λ n → F (λ v → v) L2 J col b (dn ⊥-elim L3 (down tt root) t₂))
T-fold J b = refl

step-is-R : chainD L2 tt (λ γ → RlD (λ v → v) L2 tt (tpD L2 root tt) (dn ⊥-elim L3 (down tt root) t₂)) 1 ≡ plus tp R
step-is-R = refl

A : ℕ → Raw L1
A n = In (λ v → v) L2 (down tt root) tp (dn ⊥-elim L3 pp (f n))

R-form : R ≡ G.lim A
R-form = refl

-- 第 0 项: 结点保留, 分支是底. 第 1 项: 分支里那一份 z0 越出保留区 (到层 3 的根) 再进来, 按 col 折成 ℕ 极限.
A0-form : A 0 ≡ G.nd tt (λ _ → tp)
A0-form = refl

A1-form : A 1 ≡ G.nd tt (λ _ → G.lim (λ _ → tp))
A1-form = refl
```

## 3 不合法

```agda
br : Raw L1 → Raw L1
br (G.nd r h) = h G.zero
br _ = G.zero

nd≢lim : ∀ {K s} {r : Root K s} {h : Dom K s → Tr ⊥ K s} {g} → G.nd r h ≡ G.lim g → ⊥
nd≢lim ()

nd≢into : ∀ {K s} {r : Root K s} {h : Dom K s → Tr ⊥ K s} {c t} → G.nd r h ≡ G.into c t → ⊥
nd≢into ()

q1 : Path L1
q1 = down tt root

isNd : Raw L1 → Set
isNd (G.nd r h) = ⊤
isNd _ = ⊥

-- 层 1 的孩子作用域里, up 下面那棵树.
below : Tr ⊥ L1 q1 → Raw L1
below (G.up {s = root} c refl y) = y
below (G.up {s = down c′ (inj₁ _)} () e y)
below (G.up {s = down c′ (inj₂ ())} d e y)
below _ = G.zero

no-step : Cp (G.nd tt (λ _ → tp)) (G.nd tt (λ _ → G.lim (λ _ → tp))) → ⊥
no-step (inj₁ e) = nd≢lim (cong br e)
no-step (inj₂ (inj₁ e)) = nd≢lim e
no-step (inj₂ (inj₂ (n , inj₁ e))) = nd≢into (cong br e)
no-step (inj₂ (inj₂ (n , inj₂ (inj₁ e)))) = nd≢into e
no-step (inj₂ (inj₂ (n , inj₂ (inj₂ (inj₁ (inj₁ ()))))))
no-step (inj₂ (inj₂ (n , inj₂ (inj₂ (inj₁ (inj₂ (inj₁ e))))))) with cong (λ t → isNd (below t)) e
... | e′ = ⊥-from e′
  where
  ⊥-from : ⊤ ≡ ⊥ → ⊥
  ⊥-from e″ = Relation.Binary.PropositionalEquality.subst (λ X → X) e″ tt
no-step (inj₂ (inj₂ (n , inj₂ (inj₂ (inj₁ (inj₂ (inj₂ (inj₁ (inj₁ ())))))))))
no-step (inj₂ (inj₂ (n , inj₂ (inj₂ (inj₁ (inj₂ (inj₂ (inj₁ (inj₂ ())))))))))
no-step (inj₂ (inj₂ (n , inj₂ (inj₂ (inj₁ (inj₂ (inj₂ (inj₂ (y′ , e , ())))))))))
no-step (inj₂ (inj₂ (n , inj₂ (inj₂ (inj₂ (t′ , e , d)))))) = nd≢into e

R-illegal : Legal L1 root R → ⊥
R-illegal (st , _) = no-step (st 0)
```
