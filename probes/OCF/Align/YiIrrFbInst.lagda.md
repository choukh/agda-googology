# YiIrrFb 闭项：`ψ₀ Ω₂`，它的链点，以及限制到层号 0 的片段

**档位：编译定理，都是 [YiIrrFb](YiIrrFb.lagda.md) 的同一对 `ψ₀`, `ψ₁` 在规范 Ω₂ 上的实例。** 输出合法
(`Ω₂-fold-legal`)；gt 行沿 `Raw 1` 里的链取极限，链的下一点是这一点加 `ψ₁` 的输出 (`Ω₂-row`, `Ω₂-feedback`，`refl`)；
第 1 点是保留结点，读回成层号 0 的 Ω 结点后又被 `ψ₀` 折叠 (`point₁-kept`, `branch₁-form`)。
§3：新的 `ψ₀` 限制到只含层号 0 的树，是旧接口 `FoldRows` 的实例；§4：读回域上的保留行。没有值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFbInst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (up; tw)
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrFoldSeed using (Seedᶠ; seed-Ω̂)
open import OCF.Align.YiIrrFbIf
open import OCF.Align.YiIrrFbBase
open import OCF.Align.YiIrrFb
```

## 1 Ω₂ 上的链

`points` 是定义里的那条链 (守卫无关)；`guards` 是同一列坐标上相关的守卫，只用来写陈述。

```agda
Ω₂-branch : (η : R₁) → .(Gd L1 G.top η) → LF
Ω₂-branch η e = up L1 η (proj₂ (proj₂ e))

dom-up : ∀ η (e : Gd L1 G.top η) → Dom (Ω₂-branch η e)
dom-up = Node₁.branch G.top tt tt (tw 2) Ω₂-branch dom-Ω₂

points : ℕ → Pt L1 G.top
points = iterate (next₁ G.top tt tt (tw 2) Ω₂-branch dom-Ω₂)
  (startᴸ L1 G.top tt tt)

guards : ∀ n → Gd L1 G.top (at (points n))
guards = ChainLegal₁.guards G.top
  (λ η e → ψ₁ (Ω₂-branch η e) (dom-up η e))
  (λ η e → ψ₁-legal (Ω₂-branch η e) (dom-up η e))
  (λ η e → ψ₁-nested (Ω₂-branch η e) (dom-up η e))
  (λ η e → ψ₁-positive (Ω₂-branch η e) (dom-up η e))
  (startᴸ L1 G.top tt tt) (inj₁ refl , tt , tt)
```

## 2 闭项与回灌

```agda
Ω₂-fold : R
Ω₂-fold = ψ₀ Ω₂ dom-Ω₂

Ω₂-fold-legal : Lgl zero Ω₂-fold
Ω₂-fold-legal = ψ₀-legal Ω₂ dom-Ω₂

Ω₂-fold-positive : Dn zero G.zero Ω₂-fold
Ω₂-fold-positive = ψ₀-positive Ω₂ dom-Ω₂

-- 输出是 ψ₀ 沿链的极限.
Ω₂-row : Ω₂-fold ≡
  G.lim (λ n → ψ₀ (Ω₂-branch (at (points n)) (guards n))
    (dom-up (at (points n)) (guards n)))
Ω₂-row = refl

-- 回灌: 链的下一点是这一点加上 ψ₁ 在这一点的分支上的输出.
Ω₂-feedback : ∀ n → at (points (suc n)) ≡
  at (points n) +¹ ψ₁ (Ω₂-branch (at (points n)) (guards n))
    (dom-up (at (points n)) (guards n))
Ω₂-feedback n = refl

Ω₂-grow : ∀ n → Dn L1 (at (points n)) (at (points (suc n)))
Ω₂-grow n = next₁-grow G.top tt tt (tw 2) Ω₂-branch dom-Ω₂ (points n)

-- 第 0 点是 top, 那里的分支是 Ω₁.
point₀ : at (points 0) ≡ G.top
point₀ = refl

branch₀-form : Ω₂-branch (at (points 0)) (guards 0) ≡ tw 2
branch₀-form = refl

-- 第 1 点是 top 加 ψ₁(Ω₁); ψ₁(Ω₁) 是保留结点, 所以这一点是 Raw 1 里的层 0 槽位结点.
Ω₁-branch : (η : R) → .(Gd zero one η) → LF
Ω₁-branch η e = up zero η (proj₂ (proj₂ e))

dom-Ω₁ : Dom (tw 2)
dom-Ω₁ = dom-up G.top (guards 0)

point₁-kept : at (points 1) ≡
  G.lc (inj₁ tt) one (G.top +¹ ψ₁ (suc zero) (tt , tt , tt))
    (λ η e → G.top +¹ ψ₁ (Ω₁-branch η e)
      (Node₀.branch one tt tt (suc zero) Ω₁-branch dom-Ω₁ η e))
point₁-kept = refl

-- 第 1 点处的分支: 读回成层号 0 的 Ω 结点, 它的分支是 ψ₁ 的输出的读回.
branch₁-form : Ω₂-branch (at (points 1)) (guards 1) ≡
  lc zero one tt tt
    (up L1 (G.top +¹ ψ₁ (suc zero) (tt , tt , tt))
      (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (guards 1)))))))
    (λ η e → up L1
      (G.top +¹ ψ₁ (Ω₁-branch η e)
        (Node₀.branch one tt tt (suc zero) Ω₁-branch dom-Ω₁ η e))
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (guards 1))))) η e))
branch₁-form = refl

-- 位置保持的实例: Ω₁ 是 Ω₂ 的第一支, 输出也是.
Ω₁-below-Ω₂ : Cp zero (ψ₀ (tw 2) dom-Ω₁) Ω₂-fold
Ω₁-below-Ω₂ = ψ₀-position (tw 2) Ω₂ dom-Ω₁ dom-Ω₂ (fst self)

-- 目标层 1 在 Ω₂ 上: 合法, 带嵌套证据, 读回仍在定义域里.
Ω₂-fold₁ : R₁
Ω₂-fold₁ = ψ₁ Ω₂ dom-Ω₂

Ω₂-fold₁-legal : Lgl L1 Ω₂-fold₁
Ω₂-fold₁-legal = ψ₁-legal Ω₂ dom-Ω₂

Ω₂-fold₁-nested : Nested L1 Ω₂-fold₁
Ω₂-fold₁-nested = ψ₁-nested Ω₂ dom-Ω₂

Ω₂-fold₁-read-dom : Dom (up L1 Ω₂-fold₁ Ω₂-fold₁-nested)
Ω₂-fold₁-read-dom = up1-dom Ω₂-fold₁ Ω₂-fold₁-legal Ω₂-fold₁-nested
```

## 3 限制到只含层号 0 的树

新的 `ψ₀` 在 `Only0` 的树上满足旧接口 `YiIrrIf.FoldRows` 的全部行 (`refl`)，定义域 `Only0 × Legal × Seedᶠ`。
它与 [YiIrrFold](YiIrrFold.lagda.md) 的 `ψ` 是同一组递归方程的两个解；两者字面相等要比较极限行与链里的函数，
只在函数外延下证得，见 [YiIrrFbAgree](YiIrrFbAgree.lagda.md) (条件)。

```agda
only0→only01 : ∀ x → Only0 x → Only01 x
only0→only01 zero o = tt
only0→only01 (suc x) o = only0→only01 x o
only0→only01 (lim f) o = λ n → only0→only01 (f n) (o n)
only0→only01 (lc zero c w b t g) (ot , og) =
  only0→only01 t ot , (λ η e → only0→only01 (g η e) (og η e))
only0→only01 (lc (suc k) c w b t g) ()
only0→only01 (lc (lim f) c w b t g) ()
only0→only01 (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) ()

Dom⁰ : LF → Set
Dom⁰ x = Only0 x × Legal x × Seedᶠ x

widen : ∀ x → Dom⁰ x → Dom x
widen x (o , l , s) = only0→only01 x o , l , s

level0-rows : FoldRows
level0-rows = record
  { Dom = Dom⁰
  ; dom-pred = λ x d → d
  ; dom-at = λ f d n →
      proj₁ d n , proj₂ (proj₁ (proj₂ d)) n , proj₂ (proj₂ d) n
  ; dom-branch = λ c w b t g d η e →
      proj₂ (proj₁ d) η e ,
      proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₁ (proj₂ d)))))) η e ,
      proj₂ (proj₂ (proj₂ (proj₂ (proj₂ d)))) η e
  ; dom-only = λ x d → proj₁ d
  ; dom-legal = λ x d → proj₁ (proj₂ d)
  ; dom-Ω₁ = Ω₁-only , Ω₁-legal , seed-Ω̂ L1 tt
  ; ψ = λ x d → ψ₀ x (widen x d)
  ; next = λ c w b t g d → next₀ c w b t g (widen (lc zero c w b t g) d)
  ; zero-row = λ d → refl
  ; suc-row = λ x d → refl
  ; lim-row = λ f d → refl
  ; next-additive = λ c w b t g d p → refl
  ; next-grow = λ c w b t g d p →
      next₀-grow c w b t g (widen (lc zero c w b t g) d) p
  ; gt-row = λ c w b t g d → refl
  ; fold-legal = λ x d → ψ₀-legal x (widen x d)
  ; fold-positive = λ x d → ψ₀-positive x (widen x d)
  ; position = λ x y dx dy → ψ₀-position x y (widen x dx) (widen y dy)
  }
```

## 4 读回域上的保留行

`ψ₁ ∘ up 1` 在 `Raw 1` 的结点与 `top` 上算出来 (`refl`)。结点的槽位与下界原样留下：读回域里的结点自带它在目标层里的位置，
这一行不看层号的形状。`top` 读成 Ω₁，折叠后是层 0 槽位的保留结点。

```agda
read-keep : ∀ c t (g : (η : R) → .(Gd zero c η) → R₁)
  (l : Lgl L1 (G.lc (inj₁ tt) c t g)) (nb : Nested L1 (G.lc (inj₁ tt) c t g)) →
  ψ₁ (up L1 (G.lc (inj₁ tt) c t g) nb) (up1-dom (G.lc (inj₁ tt) c t g) l nb) ≡
  G.lc (inj₁ tt) c
    (ψ₁ (up L1 t (proj₁ (proj₂ (proj₂ nb))))
      (up1-dom t (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb)))))
    (λ η e → ψ₁ (up L1 (g η e) (proj₂ (proj₂ (proj₂ nb)) η e))
      (up1-dom (g η e) (proj₂ (proj₂ (proj₂ (proj₂ l))) η e)
        (proj₂ (proj₂ (proj₂ nb)) η e)))
read-keep c t g l nb = refl

read-top : ψ₁ (up L1 G.top tt) (up1-dom G.top tt tt) ≡
  G.lc (inj₁ tt) one (successor₁ G.top)
    (λ η e → ψ₁ (Ω₁-branch η e)
      (Node₀.branch one tt tt (suc zero) Ω₁-branch dom-Ω₁ η e))
read-top = refl
```
