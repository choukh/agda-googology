# 保留带搬运的一致折叠

非验收文件. 编译定理, 无前提: `TΛ′-legal` (读法 ψ₀(Λ)), `Tw′-legal`, `T⁺ʷ′-legal`; `Ψ′-lgl` 对一切派发 `D` 成立. 折叠逐字照 [YiDlFold](YiDlFold.lagda.md), 派发结果换成 [YiZipWay](YiZipWay.lagda.md) 的 `Way′`;
公共上界上的比较 `cmpz` 只改 Ω 结点层号那一句: 先问派发 `D` (旧的 `cmpw` 这一句就是 `D`); `D` 折叠时, 把源位置按结构对到目标位置的那一支 (`PT`), 在那一支的公共上界里比较, 保留时接上结构搬运 `byMv`, 不判定两支或两个层号相等. 实例的 `D` 取 `dl` (经 `fromWay`). 不陈述值; 有限测试在 [YiZipLost](YiZipLost.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZipFold where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as May
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (plus-lgl; lev; R; succ; psum; succ-lgl; psum-lgl)
open import OCF.Lean.YiLamFold using
  ( Kfk; Kfk-br; nrmk; nrmk-lgl; Wit; none; at; Lw; w0; ws; wl; wΩ; shiftw; Pk; pk; Lw-tw; VΛ )
open import OCF.Lean.YiDlFold using (dl)
open import OCF.Lean.YiZipMove
open import OCF.Lean.YiZipWay
open Pk
```

## 1 公共上界上的比较

`PT a b r`: 位置 `r : Pre a` 按结构对到 `Pre b` (后继对后继, ℕ 极限按分量), 对不上为 `nothing`.

```agda
PT : (a b : LF) → Pre a → Maybe (Pre b)
PT (suc k) (suc k′) (inj₁ _) = just (inj₁ tt)
PT (suc k) (suc k′) (inj₂ r) = May.map inj₂ (PT k k′ r)
PT (lim f) (lim f′) (n , r) = May.map (n ,_) (PT (f n) (f′ n) r)
PT _ _ _ = nothing

viaM : ∀ {m} a b → ((r′ : Pre a) → Way′ m (lev a r′)) → (r : Pre b) → Maybe (Pre a) → Way′ m (lev b r)
viaM a b X r (just r′) = thenMv (X r′) (byMv (lev a r′) (lev b r))
viaM a b X r nothing = fold′

orW : ∀ {m j} → Way′ m j → Way′ m j → Way′ m j
orW (keep′ s t) w = keep′ s t
orW fold′ w = w

rootZ : ∀ m k (g : Raw k → LF) → Wit k g → Ext′ m (lc k g) → Way′ m k
rootZ m k g none x = fold′
rootZ m k g (at ρ e) x = subst (Way′ m) e (x (G.top , tt , ρ))

selfZ : ∀ k → Ext′ k k
selfZ k r = keep′ r (byEq refl)
```

## 2 折叠

```agda
module Fold′ (D : ∀ k K → Ext′ k K) where

  cmpz : ∀ {k} → Lw k → (q r : Pre k) → Way′ (lev k q) (lev k r)
  cmpz w0 () r
  cmpz (ws V) (inj₁ _) (inj₂ r) = keep′ r (byEq refl)
  cmpz (ws V) (inj₂ q) (inj₂ r) = cmpz V q r
  cmpz (ws V) q r = fold′
  cmpz (wl V st) (n , q) (m , r) =
    subst₂ Way′ (proj₂ (shiftw st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₂ (shiftw st (≤⇒≤′ (m≤n⊔m n m)) r))
      (cmpz (V (n ⊔ m)) (proj₁ (shiftw st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₁ (shiftw st (≤⇒≤′ (m≤n⊔m n m)) r)))
  cmpz (wΩ {k} {g} V w) (η , l , q) (η′ , l′ , r) =
    orW (D (lev (g η) q) (lc k g) (η′ , l′ , r))
        (viaM (g η) (g η′) (cmpz (V η l) q) r (PT (g η′) (g η) r))

  Ψ′ : ∀ m {k} → Lw k → Ext′ m k → Raw k → Raw m
  Ψ′-lgl : ∀ m {k} (V : Lw k) x ξ → Lgl k ξ → Lgl m (Ψ′ m V x ξ)
  Ψ′-cp : ∀ m {k} (V : Lw k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψ′ m V x ξ) (Ψ′ m V x ξ′)
  Ψ′-dn : ∀ m {k} (V : Lw k) x {ξ} ξ′ → Dn k ξ ξ′ → Dn m (Ψ′ m V x ξ) (Ψ′ m V x ξ′)
  ptsΩ′ : ∀ k (g : Raw k → LF) → (∀ η → Lgl k η → Lw (g η)) → ℕ → Pk k

  Ψ′ m V x G.zero = G.top
  Ψ′ m V x (G.suc a) = succ m (Ψ′ m V x a)
  Ψ′ m V x (G.lim f) = G.lim (λ n → Ψ′ m V x (f n))
  Ψ′ m {k} V x (G.lc r g) =
    ΨN′ m k r (x r) (λ η → Ψ′ m V x (g η)) (λ η → Ψ′ (lev k r) V (cmpz V r) (g η))
  Ψ′ m (ws V) x (G.em _ a) = Ψ′ m V (λ r → x (inj₂ r)) a
  Ψ′ m (wl V st) x (G.em n a) = Ψ′ m (V n) (λ r → x (n , r)) a
  Ψ′ m (wΩ V w) x (G.em (η , l) a) = Ψ′ m (V η l) (λ r → x (η , l , r)) a
  Ψ′ m w0 x G.top = succ m G.top
  Ψ′ m {suc k} (ws V) x G.top =
    Ψn′ m k (x (inj₁ tt)) (λ η → Ψ′ m V (λ r → x (inj₂ r)) η) (λ η → Ψ′ k V (selfZ k) η)
  Ψ′ m (wl V st) x G.top = G.lim (psum m (λ n → Ψ′ m (V n) (λ r → x (n , r)) G.top))
  Ψ′ m (wΩ {k} {g} V w) x G.top =
    ΩT′ m k (rootZ m k g w x)
      (Kfk k (λ η → Ψ′ m (V (nrmk k η) (nrmk-lgl k η)) (λ r → x (nrmk k η , nrmk-lgl k η , r)) G.top))
      (psum m (λ n → Ψ′ m (V (co (ptsΩ′ k g V n)) (lw (ptsΩ′ k g V n))) (λ r → x (co (ptsΩ′ k g V n) , lw (ptsΩ′ k g V n) , r)) G.top))

  ptsΩ′ k g V zero = pk G.top tt
  ptsΩ′ k g V (suc n) =
    pk (plus k (co (ptsΩ′ k g V n)) (Ψ′ k (V (co (ptsΩ′ k g V n)) (lw (ptsΩ′ k g V n))) (D k (g (co (ptsΩ′ k g V n)))) G.top))
       (plus-lgl k _ _ (lw (ptsΩ′ k g V n)) (Ψ′-lgl k (V (co (ptsΩ′ k g V n)) (lw (ptsΩ′ k g V n))) (D k (g (co (ptsΩ′ k g V n)))) G.top tt))

  Ψ′-cp m V x (inj₁ refl) = inj₁ refl
  Ψ′-cp m V x (inj₂ p) = inj₂ (Ψ′-dn m V x _ p)

  Ψ′-dn m V x (G.suc d) p = 0 , Ψ′-cp m V x p
  Ψ′-dn m V x (G.lim f) (n , p) = n , Ψ′-cp m V x p
  Ψ′-dn m {k} V x (G.lc r g) p = ΨN′-dn m k r (x r) _ _ (Ψ′-cp m V x p)
  Ψ′-dn m (ws V) x {G.em _ a} (G.em _ d) (refl , p) = Ψ′-dn m V _ d p
  Ψ′-dn m (wl V st) x {G.em n a} (G.em _ d) (refl , p) = Ψ′-dn m (V n) _ d p
  Ψ′-dn m (wΩ V w) x {G.em (η , l) a} (G.em _ d) (refl , p) = Ψ′-dn m (V η l) _ d p

  Ψ′-lgl m V x G.zero l = tt
  Ψ′-lgl m V x (G.suc a) l = succ-lgl m _ (Ψ′-lgl m V x a l)
  Ψ′-lgl m V x (G.lim f) (st , lf) = (λ n → Ψ′-cp m V x (st n)) , (λ n → Ψ′-lgl m V x (f n) (lf n))
  Ψ′-lgl m {k} V x (G.lc r g) (lg , mo) = ΨN′-lgl m k r (x r) _ _
    ((λ η l → Ψ′-lgl m V x (g η) (lg η l)) , (λ η η′ l e l′ → Ψ′-cp m V x (mo η η′ l e l′)))
    (λ η l → Ψ′-lgl (lev k r) V (cmpz V r) (g η) (lg η l))
  Ψ′-lgl m (ws V) x (G.em _ a) l = Ψ′-lgl m V _ a l
  Ψ′-lgl m (wl V st) x (G.em n a) l = Ψ′-lgl m (V n) _ a l
  Ψ′-lgl m (wΩ V w) x (G.em (η , lη) a) l = Ψ′-lgl m (V η lη) _ a l
  Ψ′-lgl m w0 x G.top l = succ-lgl m G.top tt
  Ψ′-lgl m {suc k} (ws V) x G.top l = Ψn′-lgl m k (x (inj₁ tt)) _ _
    ((λ η l → Ψ′-lgl m V _ η l) , (λ η η′ l e l′ → Ψ′-cp m V _ e)) (λ η l → Ψ′-lgl k V (selfZ k) η l)
  Ψ′-lgl m (wl V st) x G.top l = psum-lgl m _ (λ n → Ψ′-lgl m (V n) _ G.top tt)
  Ψ′-lgl m (wΩ {k} {g} V w) x G.top l = ΩT′-lgl m k (rootZ m k g w x) _ _
    (Kfk-br k _ (λ η → Ψ′-lgl m (V (nrmk k η) (nrmk-lgl k η)) _ G.top tt))
    (psum-lgl m _ (λ n → Ψ′-lgl m (V (co (ptsΩ′ k g V n)) (lw (ptsΩ′ k g V n))) _ G.top tt))
```

## 3 实例与闭项

```agda
dl′ : ∀ k K → Ext′ k K
dl′ k K r = fromWay (dl k K r)

open Fold′ dl′ public

TΛ′ : R
TΛ′ = Ψ′ zero VΛ (λ _ → fold′) G.top

TΛ′-legal : Lgl zero TΛ′
TΛ′-legal = Ψ′-lgl zero VΛ (λ _ → fold′) G.top tt

Tw′ : ℕ → R
Tw′ n = Ψ′ zero (Lw-tw n) (λ _ → fold′) G.top

Tw′-legal : ∀ n → Lgl zero (Tw′ n)
Tw′-legal n = Ψ′-lgl zero (Lw-tw n) (λ _ → fold′) G.top tt

-- 读法 ψ₀(Ω_{Ω+1})
T⁺ʷ′ : R
T⁺ʷ′ = Ψ′ zero (ws (Lw-tw 2)) (λ _ → fold′) G.top

T⁺ʷ′-legal : Lgl zero T⁺ʷ′
T⁺ʷ′-legal = Ψ′-lgl zero (ws (Lw-tw 2)) (λ _ → fold′) G.top tt
```
