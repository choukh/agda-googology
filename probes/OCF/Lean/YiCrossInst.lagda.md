# `Simʰ` 的出口与接口前提的两个实例

验收文件. 编译定理, 无前提, 对任意派发 `D`: 出口 `simʰ→≼`, 第 0 层的左加 `la₀`, `ladd₀`; 实例 `Zero.mono₀` (左边的源层是第 0 层, 右边任意), `Fin.mono-fin` (两边都是有限层号, 保留行在内, 层号可以不同), `Fin.value-fin`.
两个实例说明 `Compat`, `KeepRow` 可满足; 不含 ℕ 极限层号与 Ω 结点层号 (那里 `Compat` 是派发的性质, 未证未否定). 主定理在 [YiCrossMono](YiCrossMono.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCrossInst where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (n<1+n; m<n⇒m<1+n; <-irrefl; <-asym; <⇒≱; ≮⇒≥; _<?_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext; R; self; psum)
open import OCF.Lean.YiLamFold using (Lw; w0; ws; wl; wΩ)
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-suc; z≼; s≼s; ≼l; l≼)
open import OCF.Lean.YiCrossIface
open import OCF.Lean.YiCrossAdd
open import OCF.Lean.YiCrossMono
```

## 1 出口与第 0 层的左加

第 0 层没有结点, 所以每棵树自相关 (`refl₀`), `Simʰ` 推出读回的值序. 左加只在目标是第 0 层时成立: 那里 `top` 读作 1 (规则 `t0`).

```agda
refl₀ : ∀ (a : R) → Simʰ zero zero a a
refl₀ G.zero = zS
refl₀ (G.suc a) = sS (refl₀ a)
refl₀ (G.lim f) = lL (λ n → lR n (refl₀ (f n)))
refl₀ (G.lc () g)
refl₀ (G.em () a)
refl₀ G.top = tT tt

simʰ→≼ : ∀ {a b : R} → Simʰ zero zero a b → NA.read a ≼ NA.read b
simʰ→≼ zS = z≼
simʰ→≼ (sS d) = s≼s (simʰ→≼ d)
simʰ→≼ (wS d) = ≼-suc (simʰ→≼ d)
simʰ→≼ (lR n d) = ≼l n (simʰ→≼ d)
simʰ→≼ (lL h) = l≼ (λ n → simʰ→≼ (h n))
simʰ→≼ (bR {r′ = ()} d)
simʰ→≼ (nN {r = ()} e p h)
simʰ→≼ (eL {i = ()} d)
simʰ→≼ (eR {i′ = ()} d)
simʰ→≼ (tT e) = ≼-refl _
simʰ→≼ (cR {i′ = ()} c d)
simʰ→≼ (t0 z) = s≼s z≼

la₀ : ∀ {M} {a : Raw M} {y : R} z → Simʰ M zero a y → Simʰ M zero a (plus zero z y)
la₀ z zS = zS
la₀ z (sS d) = sS (la₀ z d)
la₀ z (wS d) = wS (la₀ z d)
la₀ z (lR n d) = lR n (la₀ z d)
la₀ z (lL h) = lL (λ n → la₀ z (h n))
la₀ z (bR {r′ = ()} d)
la₀ z (nN {r′ = ()} e p h)
la₀ {M = zero} z (eL {i = ()} d)
la₀ {M = suc k} z (eL d) = eL (la₀ z d)
la₀ {M = lim f} z (eL d) = eL (la₀ z d)
la₀ {M = lc k g} z (eL d) = eL (la₀ z d)
la₀ z (eR {i′ = ()} d)
la₀ {M = zero} z (tT e) = t0 tt
la₀ {M = suc k} z (tT ())
la₀ {M = lim f} z (tT ())
la₀ {M = lc k g} z (tT ())
la₀ z (cR {i′ = ()} c d)
la₀ {M = zero} z (t0 e) = t0 tt
la₀ {M = suc k} z (t0 ())
la₀ {M = lim f} z (t0 ())
la₀ {M = lc k g} z (t0 ())

ladd₀ : ∀ θ η → Simʰ zero zero η (plus zero θ η)
ladd₀ θ η = la₀ θ (refl₀ η)

psum≽ʰ : ∀ {M} {a : Raw M} (h : ℕ → R) n → Simʰ M zero a (h n) → Simʰ M zero a (psum zero h n)
psum≽ʰ h zero d = d
psum≽ʰ h (suc n) d = la₀ (psum zero h n) d
```

## 2 位置对上的顶

```agda
Q→ʰ : ∀ j k′ r′ → SimQ j k′ r′ G.top (Lay.tp (Lo k′ r′)) → Simʰ j (lev k′ r′) G.top G.top
Q→ʰ j (suc k′) (inj₁ _) p = p
Q→ʰ j (suc k′) (inj₂ r′) = Q→ʰ j k′ r′
Q→ʰ j (lim f′) (n , r′) = Q→ʰ j (f′ n) r′
Q→ʰ j (lc k′ g′) (η , _ , r′) = Q→ʰ j (g′ η) r′

P→ʰ : ∀ k r k′ r′ → SimP k k′ r r′ (Lay.tp (Lo k r)) (Lay.tp (Lo k′ r′)) →
  Simʰ (lev k r) (lev k′ r′) G.top G.top
P→ʰ (suc k) (inj₁ _) k′ r′ = Q→ʰ k k′ r′
P→ʰ (suc k) (inj₂ r) k′ r′ = P→ʰ k r k′ r′
P→ʰ (lim f) (n , r) k′ r′ = P→ʰ (f n) r k′ r′
P→ʰ (lc k g) (η , _ , r) k′ r′ = P→ʰ (g η) r k′ r′
```

每一层的顶自相关.

```agda
top-refl : ∀ K → Simʰ K K G.top G.top
top-refl zero = tT tt
top-refl (suc k) = tT (refl , top-refl k)
top-refl (lim f) = tT (λ n → top-refl (f n))
top-refl (lc k g) = tT (refl , top-refl k)
```

## 3 实例: 左边的源层是第 0 层

第 0 层没有位置, 封闭律都空成立; 右边的层号, 公共上界, 派发任意, 只要目标层的顶相关.

```agda
module Zero (D : ∀ k K → Ext k K) where
  open W.Fold D
  open M D

  data C₀ : ∀ {m k m′ k′} → Lw k → Ext m k → Lw k′ → Ext m′ k′ → Set where
    c₀ : ∀ {m m′ k′} {x : Ext m zero} {V′ : Lw k′} {x′ : Ext m′ k′} →
      Simʰ m m′ G.top G.top → C₀ w0 x V′ x′

  S₀ : Compat D
  Compat.C S₀ = C₀
  Compat.c-top S₀ (c₀ t) = t
  Compat.c-way S₀ (c₀ t) ()
  Compat.c-cmp S₀ (c₀ t) ()
  Compat.c-self S₀ ()
  Compat.c-Ls S₀ ()
  Compat.c-Ll S₀ ()
  Compat.c-LΩ S₀ ()
  Compat.c-Rs S₀ (c₀ t) = c₀ t
  Compat.c-Rl S₀ (c₀ t) n = c₀ t
  Compat.c-RΩ S₀ (c₀ t) η l = c₀ t
  Compat.c-root S₀ ()
  Compat.c-obs S₀ ()

  R₀ : KeepRow D S₀
  KeepRow.c-keep R₀ ()

  mono₀ : ∀ {m m′ k′} (x : Ext m zero) (V′ : Lw k′) (x′ : Ext m′ k′) → Simʰ m m′ G.top G.top →
    ∀ {ξ ξ′} → Simʰ zero k′ ξ ξ′ → Simʰ m m′ (Ψ m w0 x ξ) (Ψ m′ V′ x′ ξ′)
  mono₀ x V′ x′ t d = monoʰ S₀ R₀ (c₀ t) d
```

## 4 实例: 两边都是有限层号

有限层号的公共上界是 `ws` 的链 (`FL`), 内层派发 `cmpw` 只由结构决定: 保留恰当源位置的层号低于目标层 (`ck`, `cf`, 用高度 `ht` 比较), 所以层号相等的位置对上两边同为保留或同为折叠 (`wayF`), 不用派发 `D` 的任何性质.
外部派发要求在层号相等的位置对上同向 (`cᶠ` 的第四个分量).

```agda
ht : LF → ℕ
ht (suc k) = suc (ht k)
ht _ = 0

data FL : ∀ {k} → Lw k → Set where
  f0 : FL w0
  fs : ∀ {k} {V : Lw k} → FL V → FL (ws V)

lev< : ∀ {k} {V : Lw k} → FL V → ∀ q → ht (lev k q) < ht k
lev< (fs F) (inj₁ _) = n<1+n _
lev< (fs F) (inj₂ q) = m<n⇒m<1+n (lev< F q)

top-fin : ∀ {k} {V : Lw k} → FL V → Simʰ k k G.top G.top
top-fin f0 = tT tt
top-fin (fs F) = tT (refl , top-fin F)

data IsKeep {m j : LF} : Way m j → Set where
  isk : ∀ {p e} → IsKeep (keep p e)

kkʳ : ∀ {m j m′ j′} {w : Way m j} {w′ : Way m′ j′} → IsKeep w → IsKeep w′ → WayR w w′
kkʳ isk isk = kk

module Fin (D : ∀ k K → Ext k K) where
  open W.Fold D
  open M D

  ck : ∀ {k} {V : Lw k} → FL V → ∀ r q → ht (lev k q) < ht (lev k r) → IsKeep (cmpw V r q)
  ck (fs F) (inj₁ _) (inj₁ _) h = ⊥-elim (<-irrefl refl h)
  ck (fs F) (inj₁ _) (inj₂ q) h = isk
  ck (fs F) (inj₂ r) (inj₁ _) h = ⊥-elim (<-asym h (lev< F r))
  ck (fs F) (inj₂ r) (inj₂ q) h = ck F r q h

  cf : ∀ {k} {V : Lw k} → FL V → ∀ r q → ht (lev k r) ≤ ht (lev k q) → cmpw V r q ≡ fold
  cf (fs F) (inj₁ _) (inj₁ _) h = refl
  cf (fs F) (inj₁ _) (inj₂ q) h = ⊥-elim (<⇒≱ (lev< F q) h)
  cf (fs F) (inj₂ r) (inj₁ _) h = refl
  cf (fs F) (inj₂ r) (inj₂ q) h = cf F r q h

  wayF : ∀ {k k′} {V : Lw k} {V′ : Lw k′} → FL V → FL V′ → ∀ r r′ → lev k r ≡ lev k′ r′ →
    ∀ q q′ → lev k q ≡ lev k′ q′ → WayR (cmpw V r q) (cmpw V′ r′ q′)
  wayF {k} {k′} F F′ r r′ er q q′ eq with ht (lev k q) <? ht (lev k r)
  ... | yes h = kkʳ (ck F r q h) (ck F′ r′ q′ (subst₂ _<_ (cong ht eq) (cong ht er) h))
  ... | no ¬h = subst₂ WayR (sym (cf F r q (≮⇒≥ ¬h)))
    (sym (cf F′ r′ q′ (subst₂ _≤_ (cong ht er) (cong ht eq) (≮⇒≥ ¬h)))) ff

  data Cᶠ : ∀ {m k m′ k′} → Lw k → Ext m k → Lw k′ → Ext m′ k′ → Set where
    cᶠ : ∀ {m k m′ k′} {V : Lw k} {x : Ext m k} {V′ : Lw k′} {x′ : Ext m′ k′} → FL V → FL V′ →
      Simʰ m m′ G.top G.top → (∀ r r′ → lev k r ≡ lev k′ r′ → WayR (x r) (x′ r′)) → Cᶠ V x V′ x′

  Sᶠ : Compat D
  Compat.C Sᶠ = Cᶠ
  Compat.c-top Sᶠ (cᶠ F F′ t w) = t
  Compat.c-way Sᶠ (cᶠ F F′ t w) r r′ e p = w r r′ e
  Compat.c-cmp Sᶠ {k = k} {k′ = k′} (cᶠ F F′ t w) r r′ e p =
    cᶠ F F′ (P→ʰ k r k′ r′ p) (λ q q′ eq → wayF F F′ r r′ e q q′ eq)
  Compat.c-self Sᶠ (cᶠ (fs F) (fs F′) t w) e t′ = cᶠ F F′ t′ (λ r r′ _ → kk)
  Compat.c-Ls Sᶠ (cᶠ (fs F) F′ t w) = cᶠ F F′ t (λ r r′ e → w (inj₂ r) r′ e)
  Compat.c-Ll Sᶠ (cᶠ () F′ t w)
  Compat.c-LΩ Sᶠ (cᶠ () F′ t w)
  Compat.c-Rs Sᶠ (cᶠ F (fs F′) t w) = cᶠ F F′ t (λ r r′ e → w r (inj₂ r′) e)
  Compat.c-Rl Sᶠ (cᶠ F () t w)
  Compat.c-RΩ Sᶠ (cᶠ F () t w)
  Compat.c-root Sᶠ (cᶠ () F′ t w)
  Compat.c-obs Sᶠ (cᶠ () F′ t w)

  Rᶠ : KeepRow D Sᶠ
  KeepRow.c-keep Rᶠ (cᶠ () F′ t w)

  mono-fin : ∀ {m k m′ k′} {V : Lw k} {V′ : Lw k′} → FL V → FL V′ → (x : Ext m k) (x′ : Ext m′ k′) →
    Simʰ m m′ G.top G.top → (∀ r r′ → lev k r ≡ lev k′ r′ → WayR (x r) (x′ r′)) →
    ∀ {ξ ξ′} → Simʰ k k′ ξ ξ′ → Simʰ m m′ (Ψ m V x ξ) (Ψ m′ V′ x′ ξ′)
  mono-fin F F′ x x′ t w d = monoʰ Sᶠ Rᶠ (cᶠ F F′ t w) d

  -- 保留行在内: 目标是有限层号自己, 派发 self.
  self-fin : ∀ {k} {V : Lw k} → FL V → ∀ {ξ ξ′} → Simʰ k k ξ ξ′ →
    Simʰ k k (Ψ k V (self k) ξ) (Ψ k V (self k) ξ′)
  self-fin {k} F d = mono-fin F F (self k) (self k) (top-fin F) (λ r r′ _ → kk) d

  -- 目标是第 0 层: 两个有限层号 (可以不同) 之间的值序.
  value-fin : ∀ {k k′} {V : Lw k} {V′ : Lw k′} → FL V → FL V′ → ∀ {ξ ξ′} → Simʰ k k′ ξ ξ′ →
    NA.read (Ψ zero V (λ _ → fold) ξ) ≼ NA.read (Ψ zero V′ (λ _ → fold) ξ′)
  value-fin F F′ d = simʰ→≼ (mono-fin F F′ (λ _ → fold) (λ _ → fold) (tT tt) (λ r r′ _ → ff) d)
```
