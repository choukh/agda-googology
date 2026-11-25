# 燃料搜索派发的一致折叠

非验收文件. 折叠 `Fold D` 对派发 `D` 参数化 (`YiLamFold` 的 `cmpw` 的 `wΩ` 子句与 `ptsΩ` 里的 `dfin` 换成 `D`, 其余逐字), 实例取 `dl`: 目标层是 `zero` 时折叠, 否则是 [YiLamNFuel](YiLamNFuel.lagda.md) 的燃料搜索 `dlev`; `dl≡dlev` 说两者逐点相等.
编译定理, 无前提: `TΛ-legal` (读法 ψ₀(Λ)), `Tw-legal`, `T⁺ʷ-legal`; `Ψ-lgl` 对一切派发成立. 公共上界 `Lw` 与 Λ 的上界 `VΛ` 直接用 `YiLamFold` 的. 接口实例与有限测试在 [YiDlInst](YiDlInst.lagda.md), 逐点保留得不少于 `dfin` 在 [YiDlMore](YiDlMore.lagda.md), 仍折叠的位置在 [YiDlLost](YiDlLost.lagda.md). 不陈述值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDlFold where
open import Data.Nat.Base using (ℕ; zero; suc; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using
  ( plus-lgl; lev; Way; keep; fold; Ext; R; Ψn; ΨN; succ; psum; self; succ-lgl; psum-lgl; ΨN-dn; ΨN-lgl
  ; Ψn-lgl; ΩT; ΩT-lgl )
open import OCF.Lean.YiLamFold using
  ( Kfk; Kfk-br; nrmk; nrmk-lgl; finOf; Wit; Lw; w0; ws; wl; wΩ; shiftw; Pk; pk; rootW; Lw-tw; VΛ )
open import OCF.Lean.YiLamNFuel using (pol; dlev)
open Pk
```

## 1 派发

```agda
dl : ∀ k K → Ext k K
dl zero K r = fold
dl (suc k) K r = dlev (suc k) K r
dl (lim f) K r = dlev (lim f) K r
dl (lc k g) K r = dlev (lc k g) K r

pol-zero : ∀ L → pol (λ n → n) zero L ≡ fold
pol-zero L with finOf L
... | just _ = refl
... | nothing = refl

dl≡dlev : ∀ k K r → dl k K r ≡ dlev k K r
dl≡dlev zero K r = sym (pol-zero (lev K r))
dl≡dlev (suc k) K r = refl
dl≡dlev (lim f) K r = refl
dl≡dlev (lc k g) K r = refl
```

## 2 对派发参数化的折叠

```agda
module Fold (D : ∀ k K → Ext k K) where

  cmpw : ∀ {k} → Lw k → (q r : Pre k) → Way (lev k q) (lev k r)
  cmpw w0 () r
  cmpw (ws V) (inj₁ _) (inj₂ r) = keep r refl
  cmpw (ws V) (inj₂ q) (inj₂ r) = cmpw V q r
  cmpw (ws V) q r = fold
  cmpw (wl V st) (n , q) (m , r) =
    subst₂ Way (proj₂ (shiftw st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₂ (shiftw st (≤⇒≤′ (m≤n⊔m n m)) r))
      (cmpw (V (n ⊔ m)) (proj₁ (shiftw st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₁ (shiftw st (≤⇒≤′ (m≤n⊔m n m)) r)))
  cmpw {lc k g} (wΩ V w) q r = D (lev (lc k g) q) (lc k g) r

  Ψ : ∀ m {k} → Lw k → Ext m k → Raw k → Raw m
  Ψ-lgl : ∀ m {k} (V : Lw k) x ξ → Lgl k ξ → Lgl m (Ψ m V x ξ)
  Ψ-cp : ∀ m {k} (V : Lw k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψ m V x ξ) (Ψ m V x ξ′)
  Ψ-dn : ∀ m {k} (V : Lw k) x {ξ} ξ′ → Dn k ξ ξ′ → Dn m (Ψ m V x ξ) (Ψ m V x ξ′)
  ptsΩ : ∀ k (g : Raw k → LF) → (∀ η → Lgl k η → Lw (g η)) → ℕ → Pk k

  Ψ m V x G.zero = G.top
  Ψ m V x (G.suc a) = succ m (Ψ m V x a)
  Ψ m V x (G.lim f) = G.lim (λ n → Ψ m V x (f n))
  Ψ m {k} V x (G.lc r g) =
    ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmpw V r) (g η))
  Ψ m (ws V) x (G.em _ a) = Ψ m V (λ r → x (inj₂ r)) a
  Ψ m (wl V st) x (G.em n a) = Ψ m (V n) (λ r → x (n , r)) a
  Ψ m (wΩ V w) x (G.em (η , l) a) = Ψ m (V η l) (λ r → x (η , l , r)) a
  Ψ m w0 x G.top = succ m G.top
  Ψ m {suc k} (ws V) x G.top =
    Ψn m k (x (inj₁ tt)) (λ η → Ψ m V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
  Ψ m (wl V st) x G.top = G.lim (psum m (λ n → Ψ m (V n) (λ r → x (n , r)) G.top))
  Ψ m (wΩ {k} {g} V w) x G.top =
    ΩT m k (rootW m k g w x)
      (Kfk k (λ η → Ψ m (V (nrmk k η) (nrmk-lgl k η)) (λ r → x (nrmk k η , nrmk-lgl k η , r)) G.top))
      (psum m (λ n → Ψ m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (λ r → x (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) G.top))

  ptsΩ k g V zero = pk G.top tt
  ptsΩ k g V (suc n) =
    pk (plus k (co (ptsΩ k g V n)) (Ψ k (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (D k (g (co (ptsΩ k g V n)))) G.top))
       (plus-lgl k _ _ (lw (ptsΩ k g V n)) (Ψ-lgl k (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (D k (g (co (ptsΩ k g V n)))) G.top tt))

  Ψ-cp m V x (inj₁ refl) = inj₁ refl
  Ψ-cp m V x (inj₂ p) = inj₂ (Ψ-dn m V x _ p)

  Ψ-dn m V x (G.suc d) p = 0 , Ψ-cp m V x p
  Ψ-dn m V x (G.lim f) (n , p) = n , Ψ-cp m V x p
  Ψ-dn m {k} V x (G.lc r g) p = ΨN-dn m k r (x r) _ _ (Ψ-cp m V x p)
  Ψ-dn m (ws V) x {G.em _ a} (G.em _ d) (refl , p) = Ψ-dn m V _ d p
  Ψ-dn m (wl V st) x {G.em n a} (G.em _ d) (refl , p) = Ψ-dn m (V n) _ d p
  Ψ-dn m (wΩ V w) x {G.em (η , l) a} (G.em _ d) (refl , p) = Ψ-dn m (V η l) _ d p

  Ψ-lgl m V x G.zero l = tt
  Ψ-lgl m V x (G.suc a) l = succ-lgl m _ (Ψ-lgl m V x a l)
  Ψ-lgl m V x (G.lim f) (st , lf) = (λ n → Ψ-cp m V x (st n)) , (λ n → Ψ-lgl m V x (f n) (lf n))
  Ψ-lgl m {k} V x (G.lc r g) (lg , mo) = ΨN-lgl m k r (x r) _ _
    ((λ η l → Ψ-lgl m V x (g η) (lg η l)) , (λ η η′ l e l′ → Ψ-cp m V x (mo η η′ l e l′)))
    (λ η l → Ψ-lgl (lev k r) V (cmpw V r) (g η) (lg η l))
  Ψ-lgl m (ws V) x (G.em _ a) l = Ψ-lgl m V _ a l
  Ψ-lgl m (wl V st) x (G.em n a) l = Ψ-lgl m (V n) _ a l
  Ψ-lgl m (wΩ V w) x (G.em (η , lη) a) l = Ψ-lgl m (V η lη) _ a l
  Ψ-lgl m w0 x G.top l = succ-lgl m G.top tt
  Ψ-lgl m {suc k} (ws V) x G.top l = Ψn-lgl m k (x (inj₁ tt)) _ _
    ((λ η l → Ψ-lgl m V _ η l) , (λ η η′ l e l′ → Ψ-cp m V _ e)) (λ η l → Ψ-lgl k V (self k) η l)
  Ψ-lgl m (wl V st) x G.top l = psum-lgl m _ (λ n → Ψ-lgl m (V n) _ G.top tt)
  Ψ-lgl m (wΩ {k} {g} V w) x G.top l = ΩT-lgl m k (rootW m k g w x) _ _
    (Kfk-br k _ (λ η → Ψ-lgl m (V (nrmk k η) (nrmk-lgl k η)) _ G.top tt))
    (psum-lgl m _ (λ n → Ψ-lgl m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) _ G.top tt))
```

## 3 实例与闭项

```agda
open Fold dl public

TΛ : R
TΛ = Ψ zero VΛ (λ _ → fold) G.top

TΛ-legal : Lgl zero TΛ
TΛ-legal = Ψ-lgl zero VΛ (λ _ → fold) G.top tt

Tw : ℕ → R
Tw n = Ψ zero (Lw-tw n) (λ _ → fold) G.top

Tw-legal : ∀ n → Lgl zero (Tw n)
Tw-legal n = Ψ-lgl zero (Lw-tw n) (λ _ → fold) G.top tt

-- 读法 ψ₀(Ω_{Ω+1})
T⁺ʷ : R
T⁺ʷ = Ψ zero (ws (Lw-tw 2)) (λ _ → fold) G.top

T⁺ʷ-legal : Lgl zero T⁺ʷ
T⁺ʷ-legal = Ψ-lgl zero (ws (Lw-tw 2)) (λ _ → fold) G.top tt

TΛ-form : TΛ ≡ G.lim (psum zero Tw)
TΛ-form = refl
```
