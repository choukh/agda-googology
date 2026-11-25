# YiNext 折叠：公共上界含 Ω 结点层号 `tw 2`，与合法性互递归

**判决：定义与编译定理 (第 2、3 层)，无前提。** `Ψ m V x ξ` 照主线 [YiLeanFold](YiLeanFold.lagda.md)，`V : Lv k` 多一种 `vΩ` (层号 `tw 2`)；
`top` 在 `tw 2` 上：派发在 `p₀` 保留时是层号 0 的结点 (分支 `Kf`)，折叠时是主线 `T₃` 的链 (链点要合法性，所以 `Ψ` 与 `Ψ-lgl` 互递归)。
对任意派发：`Ψ-cp` 保持第一位置，`Ψ-lgl` 合法的输入折成合法的输出。不否定别的写法。部件在 [YiNextBase](YiNextBase.lagda.md)，闭项在 [YiNextTop](YiNextTop.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
```

## 1 折叠与合法性

`top` 在 `tw 2` 上的折叠行的观察是第 `ηₙ` 支的 `top` 的像 (派发一律折叠：结点层 0 不在目标之下时，它上面的位置也都不在)；
链点的合法性要 `Ψ-lgl`。观察单调由 `vΩ` 的字段 `up` 与 `Up-mono` 给出：沿 `Up` 走下去，观察是链或部分和的第 0 项。

```agda
p₀ : Pre (lc zero ⌜_⌝)
p₀ = G.top , tt , inj₁ tt

Ψ : ∀ m {k} → Lv k → Ext m k → Raw k → Raw m
Ψ-lgl : ∀ m {k} (V : Lv k) x ξ → Lgl k ξ → Lgl m (Ψ m V x ξ)
Up-mono : ∀ m {a b} {A : Lv a} {B : Lv b} → Up A B →
  Cp m (Ψ m A (λ _ → fold) G.top) (Ψ m B (λ _ → fold) G.top)
Ψ-cp : ∀ m {k} (V : Lv k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψ m V x ξ) (Ψ m V x ξ′)
Ψ-dn : ∀ m {k} (V : Lv k) x {ξ} ξ′ → Dn k ξ ξ′ → Dn m (Ψ m V x ξ) (Ψ m V x ξ′)

Ψ m V x G.zero = G.top
Ψ m V x (G.suc a) = succ m (Ψ m V x a)
Ψ m V x (G.lim f) = G.lim (λ n → Ψ m V x (f n))
Ψ m {k} V x (G.lc r g) =
  ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmp V r) (g η))
Ψ m (vs V) x (G.em _ a) = Ψ m V (λ r → x (inj₂ r)) a
Ψ m (vl V st) x (G.em n a) = Ψ m (V n) (λ r → x (n , r)) a
Ψ m (vΩ V u) x (G.em (η , l) a) = Ψ m (V η l) (λ r → x (η , l , r)) a
Ψ m v0 x G.top = succ m G.top
Ψ m {suc k} (vs V) x G.top =
  Ψn m k (x (inj₁ tt)) (λ η → Ψ m V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
Ψ m (vl V st) x G.top = G.lim (psum m (λ n → Ψ m (V n) (λ r → x (n , r)) G.top))
Ψ m (vΩ V u) x G.top = ΩT m zero (x p₀)
  (Kf m (λ η → Ψ m (V (nrm η) (nrm-lgl η)) (λ r → x (nrm η , nrm-lgl η , r)) G.top))
  (λ n → let p = pts (λ η l → Ψ zero (V η l) (λ _ → fold) G.top)
                     (λ η l → Ψ-lgl zero (V η l) (λ _ → fold) G.top tt) n in
         Ψ m (V (co p) (lw p)) (λ _ → fold) G.top)

Up-mono m ur = inj₁ refl
Up-mono m (us p) = inj₂ (0 , Up-mono m p)
Up-mono m (ul p) = inj₂ (0 , Up-mono m p)

Ψ-cp m V x (inj₁ refl) = inj₁ refl
Ψ-cp m V x (inj₂ p) = inj₂ (Ψ-dn m V x _ p)

Ψ-dn m V x (G.suc d) p = 0 , Ψ-cp m V x p
Ψ-dn m V x (G.lim f) (n , p) = n , Ψ-cp m V x p
Ψ-dn m {k} V x (G.lc r g) p = ΨN-dn m k r (x r) _ _ (Ψ-cp m V x p)
Ψ-dn m (vs V) x {G.em _ a} (G.em _ d) (refl , p) = Ψ-dn m V _ d p
Ψ-dn m (vl V st) x {G.em n a} (G.em _ d) (refl , p) = Ψ-dn m (V n) _ d p
Ψ-dn m (vΩ V u) x {G.em (η , l) a} (G.em _ d) (refl , p) = Ψ-dn m (V η l) _ d p

Ψ-lgl m V x G.zero l = tt
Ψ-lgl m V x (G.suc a) l = succ-lgl m _ (Ψ-lgl m V x a l)
Ψ-lgl m V x (G.lim f) (st , lf) = (λ n → Ψ-cp m V x (st n)) , (λ n → Ψ-lgl m V x (f n) (lf n))
Ψ-lgl m {k} V x (G.lc r g) (lg , mo) = ΨN-lgl m k r (x r) _ _
  ((λ η l → Ψ-lgl m V x (g η) (lg η l)) , (λ η η′ l e l′ → Ψ-cp m V x (mo η η′ l e l′)))
  (λ η l → Ψ-lgl (lev k r) V (cmp V r) (g η) (lg η l))
Ψ-lgl m (vs V) x (G.em _ a) l = Ψ-lgl m V _ a l
Ψ-lgl m (vl V st) x (G.em n a) l = Ψ-lgl m (V n) _ a l
Ψ-lgl m (vΩ V u) x (G.em (η , lη) a) l = Ψ-lgl m (V η lη) _ a l
Ψ-lgl m v0 x G.top l = succ-lgl m G.top tt
Ψ-lgl m {suc k} (vs V) x G.top l = Ψn-lgl m k (x (inj₁ tt)) _ _
  ((λ η l → Ψ-lgl m V _ η l) , (λ η η′ l e l′ → Ψ-cp m V _ e)) (λ η l → Ψ-lgl k V (self k) η l)
Ψ-lgl m (vl V st) x G.top l = psum-lgl m _ (λ n → Ψ-lgl m (V n) _ G.top tt)
Ψ-lgl m (vΩ V u) x G.top l = ΩT-lgl m zero (x p₀) _ _
  (Kf-br m _ (λ η → Ψ-lgl m (V (nrm η) (nrm-lgl η)) _ G.top tt))
  ((λ n → let p = pts F FL n in Up-mono m (u (co p) (lw p) (F (co p) (lw p)) (FL (co p) (lw p)))) ,
   (λ n → let p = pts F FL n in Ψ-lgl m (V (co p) (lw p)) _ G.top tt))
  where
  F : (η : R) → Lgl zero η → R
  F η l = Ψ zero (V η l) (λ _ → fold) G.top
  FL : ∀ η l → Lgl zero (F η l)
  FL η l = Ψ-lgl zero (V η l) (λ _ → fold) G.top tt
```
