# YiUni 否定：Ω 结点层号 `tw 2` 上完全的位置比较推出 LPO

**非验收文件。判决：编译定理，无前提。** 对 `tw 2` 的一切位置对，能保留处都保留的比较推出 LPO (`cmp-full→lpo`；接口的形式 `uni-cmp→lpo`)；`tw 2` 实例的 `cmp` 不完全 (`tw2-not-full`)。
被比较的一对在不同的支，两个下标有合法的公共上界就推出 `α` 有真值 (`bound→found`)；带公共上界的证据时可以搬到同一支比较 (`cmpᵂ`，有限测试 `bounded-keep`)。
节点行对一切合法树成立，所以任意一对都被问到 (`probe-lgl`, `probe-row`)。接口 [YiUniIf](YiUniIf.lagda.md)，部件 [YiUniNegBase](YiUniNegBase.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUniNegCmp where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)
open import Data.Bool.Base using (true; false)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; ⌜_⌝; lev; Way; keep; fold; cmp; ΨN; Lv; vΩ)
open import OCF.Lean.YiNextTop using (sh; lv; V₂)
open import OCF.Lean.YiUniIf using (Uni; At; IsKeep; Full; CmpFull)
open import OCF.Lean.YiUniNegBase
open import OCF.Lean.YiUniTw2 using (Tw2)
```

## 1 否定

目标位置 `qα α` 在第 `suc (lim (fα α))` 支的根，层号 `Tα α`；结点位置 `r₁` 在第 `two` 支的根，层号 1。

```agda
ηα : (ℕ → Bool) → R
ηα α = G.suc (G.lim (fα α))

qα : (ℕ → Bool) → Pre (tw 2)
qα α = ηα α , lim-lgl α , inj₁ tt

r₁ : Pre (tw 2)
r₁ = two , tt , inj₁ tt

cmp-full→lpo : (c : (q r : Pre (tw 2)) → Way (lev (tw 2) q) (lev (tw 2) r)) →
  (∀ q → Full (lev (tw 2) q) (tw 2) (c q)) → LPO
cmp-full→lpo c full α = decide α (c (qα α) r₁) (λ fd → full (qα α) r₁ (found→at α fd))

uni-cmp→lpo : (U : Uni) (V : Uni.Bd U (tw 2)) → CmpFull U V → LPO
uni-cmp→lpo U V = cmp-full→lpo (Uni.cmp U V)
```

`tw 2` 实例不完全：同一支 `suc top` 里的一对 (`YiNextAccTest` 的 `lost`) 有槽位，比较给折叠。

```agda
s₂ s₂′ : Pre (tw 2)
s₂ = G.suc G.top , tt , inj₁ tt
s₂′ = G.suc G.top , tt , inj₂ (inj₁ tt)

tw2-not-full : CmpFull Tw2 V₂ → ⊥
tw2-not-full full = full s₂ s₂′ (inj₁ tt , refl)
```

## 2 被问到

```agda
probe : Pre (tw 2) → Pre (tw 2) → Raw (tw 2)
probe q r = G.lc q (λ _ → G.lc r (λ _ → G.zero))

probe-lgl : ∀ q r → Lgl (tw 2) (probe q r)
probe-lgl q r = (λ η l → (λ _ _ → tt) , (λ _ _ _ _ _ → inj₁ refl)) , (λ _ _ _ _ _ → inj₁ refl)

probe-row : (U : Uni) (V : Uni.Bd U (tw 2)) (q r : Pre (tw 2)) →
  Uni.Ψ U (lev (tw 2) q) V (Uni.cmp U V q) (G.lc r (λ _ → G.zero)) ≡
  ΨN (lev (tw 2) q) (tw 2) r (Uni.cmp U V q r) (λ _ → Uni.Ψ U (lev (tw 2) q) V (Uni.cmp U V q) G.zero)
    (λ _ → Uni.Ψ U (lev (tw 2) r) V (Uni.cmp U V r) G.zero)
probe-row U V q r = Uni.node-row U (lev (tw 2) q) V (Uni.cmp U V q) r (λ _ → G.zero)
```

## 3 带公共上界时 (有限测试)

两个下标有合法的公共上界 `w` 时，把两个位置沿 `sh` 搬到第 `w` 支，用可数层号上的比较。

```agda
cmpᵂ : ∀ {η η′} (w : R) → Lgl zero w → Cp zero η w → Cp zero η′ w →
  (q : Pre ⌜ η ⌝) (r : Pre ⌜ η′ ⌝) → Way (lev ⌜ η ⌝ q) (lev ⌜ η′ ⌝ r)
cmpᵂ w lw e e′ q r = subst₂ Way (proj₂ (sh w e q)) (proj₂ (sh w e′ r))
  (cmp (lv w lw) (proj₁ (sh w e q)) (proj₁ (sh w e′ r)))

bounded-keep : cmpᵂ {G.suc G.top} {G.suc G.top} (G.suc G.top) tt (inj₁ refl) (inj₁ refl)
  (inj₁ tt) (inj₂ (inj₁ tt)) ≡ keep (inj₁ tt) refl
bounded-keep = refl
```

## 4 这一对的下标没有不推出真值的公共上界

合法的公共上界之下的两棵树可比 (`cmp-under`)；`two` 不在 `ηα α` 之上，`ηα α` 之上有 `two` 就有真值。

```agda
cp-trans : ∀ {a b c : R} → Cp zero a b → Cp zero b c → Cp zero a c
dn-trans : ∀ {a b : R} c → Cp zero a b → Dn zero b c → Dn zero a c
cp-trans p (inj₁ refl) = p
cp-trans p (inj₂ q) = inj₂ (dn-trans _ p q)
dn-trans (G.suc d) p q = cp-trans p q
dn-trans (G.lim f) p (n , q) = n , cp-trans p q

up-chain : ∀ (f : ℕ → R) → (∀ n → Cp zero (f n) (f (suc n))) → ∀ {n m} → n ≤′ m → Cp zero (f n) (f m)
up-chain f st ≤′-refl = inj₁ refl
up-chain f st (≤′-step p) = cp-trans (up-chain f st p) (st _)

cmp-under : ∀ {a b} (w : R) → Lgl zero w → Cp zero a w → Cp zero b w → Cp zero a b ⊎ Cp zero b a
cmp-under w lw (inj₁ refl) q = inj₂ q
cmp-under w lw (inj₂ p) (inj₁ refl) = inj₁ (inj₂ p)
cmp-under (G.suc d) lw (inj₂ p) (inj₂ q) = cmp-under d lw p q
cmp-under (G.lim f) (st , lf) (inj₂ (n , p)) (inj₂ (m , q)) =
  cmp-under (f (n ⊔ m)) (lf (n ⊔ m))
    (cp-trans p (up-chain f st (≤⇒≤′ (m≤m⊔n n m)))) (cp-trans q (up-chain f st (≤⇒≤′ (m≤n⊔m n m))))

two-pick : ∀ b → Cp zero two (pick b) → b ≡ true
two-pick true c = refl
two-pick false (inj₁ ())
two-pick false (inj₂ (inj₁ ()))
two-pick false (inj₂ (inj₂ ()))

two-η : ∀ α → Cp zero two (ηα α) → Found α
two-η α (inj₁ ())
two-η α (inj₂ (inj₁ ()))
two-η α (inj₂ (inj₂ (n , c))) = hit-found α n (two-pick (hit α n) c)

η-two : ∀ α → Cp zero (ηα α) two → ⊥
η-two α (inj₁ ())
η-two α (inj₂ (inj₁ ()))
η-two α (inj₂ (inj₂ (inj₁ ())))
η-two α (inj₂ (inj₂ (inj₂ ())))

bound→found : ∀ α (w : R) → Lgl zero w → Cp zero (ηα α) w → Cp zero two w → Found α
bound→found α w lw p q with cmp-under w lw p q
... | inj₁ c = ⊥-elim (η-two α c)
... | inj₂ c = two-η α c
```
