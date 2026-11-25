# 来历作为同支证据: 比较只在有证据时按结构对齐

非验收文件. 编译定理, 无前提: 对一切派发 `D` 与一切证据来源 `E`, `Ψᶜ-lgl` 成立; 闭项 `TΛᶜ` (读法 ψ₀(Λ)), `Twᶜ`, `T⁺ʷᶜ` 合法. 折叠逐字照 [YiZipFold](YiZipFold.lagda.md), 只改 Ω 结点层号那一句: 折叠把目标的支 `η` 与源的支 `η′` 交给证据来源 `E`, `E` 给出 `η ≡ η′` 时按 `cmpz` 的结构对齐 (`orW D 结构`), 否则只走原来的派发 `D`.
证据只作闸门, 输出不依赖证明本身. 实例 `evF` 只在两支都不含 ℕ 极限, Ω 结点, 嵌入时给证据. 有限测试与否定在 [YiCtxTest](YiCtxTest.lagda.md), [YiCtxNeg](YiCtxNeg.lagda.md). 不陈述值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCtxFold where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as May
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (plus-lgl; lev; R; succ; psum; succ-lgl; psum-lgl)
open import OCF.Lean.YiLamFold using
  ( Kfk; Kfk-br; nrmk; nrmk-lgl; Wit; none; at; Lw; w0; ws; wl; wΩ; shiftw; Pk; pk; Lw-tw; VΛ )
open import OCF.Lean.YiZipWay
open import OCF.Lean.YiZipFold using (PT; viaM; orW; rootZ; selfZ; dl′)
open Pk
```

## 1 证据来源与闸门

`Ev`: 给两支下标, 可以给出它们字面相等的证据; `SB k q r`: 两个位置同支 (只在 Ω 结点层号上有内容). `gate`: 有证据时先问 `D` 再按结构, 没有证据时只问 `D`.

```agda
Ev : Set
Ev = ∀ k → (η η′ : Raw k) → Maybe (η ≡ η′)

SB : (k : LF) → Pre k → Pre k → Set
SB zero () r
SB (suc k) q r = ⊥
SB (lim f) q r = ⊥
SB (lc k g) (η , _ , _) (η′ , _ , _) = η ≡ η′

evOf : Ev → ∀ k (q r : Pre k) → Maybe (SB k q r)
evOf E zero () r
evOf E (suc k) q r = nothing
evOf E (lim f) q r = nothing
evOf E (lc k g) (η , _ , _) (η′ , _ , _) = E k η η′

gate : ∀ {A : Set} {m j} → Maybe A → Way′ m j → Way′ m j → Way′ m j
gate nothing d s = d
gate (just _) d s = orW d s
```

## 2 折叠

```agda
module FoldC (D : ∀ k K → Ext′ k K) (E : Ev) where

  -- `cmpe`: 证据作为输入 (这一层的); `cmpc`: 证据取自 `E`.
  cmpe : ∀ {k} → Lw k → (q r : Pre k) → Maybe (SB k q r) → Way′ (lev k q) (lev k r)
  cmpc : ∀ {k} → Lw k → (q r : Pre k) → Way′ (lev k q) (lev k r)
  cmpc {k} V q r = cmpe V q r (evOf E k q r)

  cmpe w0 () r e
  cmpe (ws V) (inj₁ _) (inj₂ r) e = keep′ r (byEq refl)
  cmpe (ws V) (inj₂ q) (inj₂ r) e = cmpc V q r
  cmpe (ws V) q r e = fold′
  cmpe (wl V st) (n , q) (m , r) e =
    subst₂ Way′ (proj₂ (shiftw st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₂ (shiftw st (≤⇒≤′ (m≤n⊔m n m)) r))
      (cmpc (V (n ⊔ m)) (proj₁ (shiftw st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₁ (shiftw st (≤⇒≤′ (m≤n⊔m n m)) r)))
  cmpe (wΩ {k} {g} V w) (η , l , q) (η′ , l′ , r) e =
    gate e (D (lev (g η) q) (lc k g) (η′ , l′ , r))
      (viaM (g η) (g η′) (cmpc (V η l) q) r (PT (g η′) (g η) r))

  Ψᶜ : ∀ m {k} → Lw k → Ext′ m k → Raw k → Raw m
  Ψᶜ-lgl : ∀ m {k} (V : Lw k) x ξ → Lgl k ξ → Lgl m (Ψᶜ m V x ξ)
  Ψᶜ-cp : ∀ m {k} (V : Lw k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψᶜ m V x ξ) (Ψᶜ m V x ξ′)
  Ψᶜ-dn : ∀ m {k} (V : Lw k) x {ξ} ξ′ → Dn k ξ ξ′ → Dn m (Ψᶜ m V x ξ) (Ψᶜ m V x ξ′)
  ptsΩᶜ : ∀ k (g : Raw k → LF) → (∀ η → Lgl k η → Lw (g η)) → ℕ → Pk k

  Ψᶜ m V x G.zero = G.top
  Ψᶜ m V x (G.suc a) = succ m (Ψᶜ m V x a)
  Ψᶜ m V x (G.lim f) = G.lim (λ n → Ψᶜ m V x (f n))
  Ψᶜ m {k} V x (G.lc r g) =
    ΨN′ m k r (x r) (λ η → Ψᶜ m V x (g η)) (λ η → Ψᶜ (lev k r) V (cmpc V r) (g η))
  Ψᶜ m (ws V) x (G.em _ a) = Ψᶜ m V (λ r → x (inj₂ r)) a
  Ψᶜ m (wl V st) x (G.em n a) = Ψᶜ m (V n) (λ r → x (n , r)) a
  Ψᶜ m (wΩ V w) x (G.em (η , l) a) = Ψᶜ m (V η l) (λ r → x (η , l , r)) a
  Ψᶜ m w0 x G.top = succ m G.top
  Ψᶜ m {suc k} (ws V) x G.top =
    Ψn′ m k (x (inj₁ tt)) (λ η → Ψᶜ m V (λ r → x (inj₂ r)) η) (λ η → Ψᶜ k V (selfZ k) η)
  Ψᶜ m (wl V st) x G.top = G.lim (psum m (λ n → Ψᶜ m (V n) (λ r → x (n , r)) G.top))
  Ψᶜ m (wΩ {k} {g} V w) x G.top =
    ΩT′ m k (rootZ m k g w x)
      (Kfk k (λ η → Ψᶜ m (V (nrmk k η) (nrmk-lgl k η)) (λ r → x (nrmk k η , nrmk-lgl k η , r)) G.top))
      (psum m (λ n → Ψᶜ m (V (co (ptsΩᶜ k g V n)) (lw (ptsΩᶜ k g V n))) (λ r → x (co (ptsΩᶜ k g V n) , lw (ptsΩᶜ k g V n) , r)) G.top))

  ptsΩᶜ k g V zero = pk G.top tt
  ptsΩᶜ k g V (suc n) =
    pk (plus k (co (ptsΩᶜ k g V n)) (Ψᶜ k (V (co (ptsΩᶜ k g V n)) (lw (ptsΩᶜ k g V n))) (D k (g (co (ptsΩᶜ k g V n)))) G.top))
       (plus-lgl k _ _ (lw (ptsΩᶜ k g V n)) (Ψᶜ-lgl k (V (co (ptsΩᶜ k g V n)) (lw (ptsΩᶜ k g V n))) (D k (g (co (ptsΩᶜ k g V n)))) G.top tt))

  Ψᶜ-cp m V x (inj₁ refl) = inj₁ refl
  Ψᶜ-cp m V x (inj₂ p) = inj₂ (Ψᶜ-dn m V x _ p)

  Ψᶜ-dn m V x (G.suc d) p = 0 , Ψᶜ-cp m V x p
  Ψᶜ-dn m V x (G.lim f) (n , p) = n , Ψᶜ-cp m V x p
  Ψᶜ-dn m {k} V x (G.lc r g) p = ΨN′-dn m k r (x r) _ _ (Ψᶜ-cp m V x p)
  Ψᶜ-dn m (ws V) x {G.em _ a} (G.em _ d) (refl , p) = Ψᶜ-dn m V _ d p
  Ψᶜ-dn m (wl V st) x {G.em n a} (G.em _ d) (refl , p) = Ψᶜ-dn m (V n) _ d p
  Ψᶜ-dn m (wΩ V w) x {G.em (η , l) a} (G.em _ d) (refl , p) = Ψᶜ-dn m (V η l) _ d p

  Ψᶜ-lgl m V x G.zero l = tt
  Ψᶜ-lgl m V x (G.suc a) l = succ-lgl m _ (Ψᶜ-lgl m V x a l)
  Ψᶜ-lgl m V x (G.lim f) (st , lf) = (λ n → Ψᶜ-cp m V x (st n)) , (λ n → Ψᶜ-lgl m V x (f n) (lf n))
  Ψᶜ-lgl m {k} V x (G.lc r g) (lg , mo) = ΨN′-lgl m k r (x r) _ _
    ((λ η l → Ψᶜ-lgl m V x (g η) (lg η l)) , (λ η η′ l e l′ → Ψᶜ-cp m V x (mo η η′ l e l′)))
    (λ η l → Ψᶜ-lgl (lev k r) V (cmpc V r) (g η) (lg η l))
  Ψᶜ-lgl m (ws V) x (G.em _ a) l = Ψᶜ-lgl m V _ a l
  Ψᶜ-lgl m (wl V st) x (G.em n a) l = Ψᶜ-lgl m (V n) _ a l
  Ψᶜ-lgl m (wΩ V w) x (G.em (η , lη) a) l = Ψᶜ-lgl m (V η lη) _ a l
  Ψᶜ-lgl m w0 x G.top l = succ-lgl m G.top tt
  Ψᶜ-lgl m {suc k} (ws V) x G.top l = Ψn′-lgl m k (x (inj₁ tt)) _ _
    ((λ η l → Ψᶜ-lgl m V _ η l) , (λ η η′ l e l′ → Ψᶜ-cp m V _ e)) (λ η l → Ψᶜ-lgl k V (selfZ k) η l)
  Ψᶜ-lgl m (wl V st) x G.top l = psum-lgl m _ (λ n → Ψᶜ-lgl m (V n) _ G.top tt)
  Ψᶜ-lgl m (wΩ {k} {g} V w) x G.top l = ΩT′-lgl m k (rootZ m k g w x) _ _
    (Kfk-br k _ (λ η → Ψᶜ-lgl m (V (nrmk k η) (nrmk-lgl k η)) _ G.top tt))
    (psum-lgl m _ (λ n → Ψᶜ-lgl m (V (co (ptsΩᶜ k g V n)) (lw (ptsΩᶜ k g V n))) _ G.top tt))
```

## 3 有限结构的证据来源与闭项

`evF` 沿 `zero`, `suc`, `top` 走, 遇到 ℕ 极限, Ω 结点, 嵌入就不给证据 (这三处的字面相等要比较函数或下标的证明).

```agda
evF : Ev
evF k G.zero G.zero = just refl
evF k (G.suc a) (G.suc b) = May.map (cong G.suc) (evF k a b)
evF k G.top G.top = just refl
evF k _ _ = nothing

open FoldC dl′ evF public

TΛᶜ : R
TΛᶜ = Ψᶜ zero VΛ (λ _ → fold′) G.top

TΛᶜ-legal : Lgl zero TΛᶜ
TΛᶜ-legal = Ψᶜ-lgl zero VΛ (λ _ → fold′) G.top tt

Twᶜ : ℕ → R
Twᶜ n = Ψᶜ zero (Lw-tw n) (λ _ → fold′) G.top

Twᶜ-legal : ∀ n → Lgl zero (Twᶜ n)
Twᶜ-legal n = Ψᶜ-lgl zero (Lw-tw n) (λ _ → fold′) G.top tt

-- 读法 ψ₀(Ω_{Ω+1})
T⁺ʷᶜ : R
T⁺ʷᶜ = Ψᶜ zero (ws (Lw-tw 2)) (λ _ → fold′) G.top

T⁺ʷᶜ-legal : Lgl zero T⁺ʷᶜ
T⁺ʷᶜ-legal = Ψᶜ-lgl zero (ws (Lw-tw 2)) (λ _ → fold′) G.top tt
```
