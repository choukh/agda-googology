# `Rel 1`, `Rel 2` 与 `⊴⁺`, `⊴²` 的对应

验收文件. 编译定理: `na→` (`NA._⊴_` 进 `Rel 1`), `from1` / `to1` (在 T₁ 上 `⊴⁺` 与 `Rel 1` 互推), `from2` (`⊴²` 进 `Rel 2`; 层号 1 槽位的假设经 `to1` 换回), 由此 `Diag¹`, `e₂⊴γ₂ᴿ`, `diag₂→` 把 [YiSyncDiag](YiSyncDiag.lagda.md), [YiSyncTwo](YiSyncTwo.lagda.md), [YiStepThree](YiStepThree.lagda.md) 的陈述搬到 [YiRelK](YiRelK.lagda.md) 的关系上.
`Rel 2` 的嵌入规则对一切参照层号 (`⊴²` 的 `e1`, `e0` 只对 T₁, T₀); `Rel 2 → ⊴²` 不陈述.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRelKInst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import OCF.Lean.YiNextCore hiding (Le)
import OCF.Lean.YiNextAcc as NA
open import OCF.Align.YiLvVal2 using (T₀; T₁)
import OCF.Align.Level as L
import OCF.Align.Stage2 as S2
import OCF.Lean.YiSyncRel as S
import OCF.Lean.YiStepRel2 as R2
open import OCF.Lean.YiSyncDiag using (Diag)
open import OCF.Lean.YiSyncTwo using (e₂⊴γ₂)
open import OCF.Lean.YiShpTwo using (σB; e₂; γ₂)
open import OCF.Lean.YiShpSq using (ψ₁)
open import OCF.Lean.YiStepTree using (σ₃; ψ₂)
open import OCF.Lean.YiStepThree using (Diag₂ᵀ)
open import OCF.Lean.YiRelK
```

## 1 第 1 层

```agda
na→ : ∀ {ℓ} {x : L.Ordᶜ ℓ} {η} → x NA.⊴ η → Rel 1 x η
na→ NA.z⊴ = z⊴
na→ (NA.s⊴s p) = s⊴s (na→ p)
na→ (NA.⊴s p) = ⊴s (na→ p)
na→ (NA.⊴l n p) = ⊴l n (na→ p)
na→ (NA.l⊴ h) = l⊴ (λ n → na→ (h n))
na→ (NA.⊴b p) = ⊴b (na→ p)
na→ (NA.nd h) = nd L.z≅ (λ y a q s → na→ (h y a q))
na→ (NA.nt h) = nt L.z≅ (λ y a q s → na→ (h y a q))
na→ (NA.em⊴ q) = em q
na→ (NA.u⊴ p) = u⊴ (na→ p)

from1 : ∀ {x : T₁} {η} → x S.⊴⁺ η → Rel 1 x η
from1 S.z⊴ = z⊴
from1 (S.s⊴s p) = s⊴s (from1 p)
from1 (S.⊴s p) = ⊴s (from1 p)
from1 (S.⊴l n p) = ⊴l n (from1 p)
from1 (S.l⊴ h) = l⊴ (λ n → from1 (h n))
from1 (S.⊴b p) = ⊴b (from1 p)
from1 (S.nd h) = nd L.z≅ (λ y a q s → from1 (h y a q))
from1 (S.nt h) = nt L.z≅ (λ y a q s → from1 (h y a q))
from1 (S.u⊴ p) = u⊴ (na→ p)
from1 (S.dg h) = dg z1 (λ n a c → from1 (h n a c))
from1 (S.≅⊴ e p) = ≅⊴ e (from1 p)
```

`Rel 1` 在 T₀ 上带 `dg`, `⊴⁺` 的 `u⊴` 只收 `NA._⊴_`; 反方向时 `up` 经 `≅⊴` 推到后继与极限之内.

```agda
upS : ∀ (y : T₀) → L.up {k = L.zero} L.zero (L.suc y) L.≅ L.suc (L.up {k = L.zero} L.zero y)
upS y = L.upˡ {r = L.zero} (L.s≅ (L.upʳ {r = L.zero} (L.≅-refl⁰ y)))

upL : ∀ (F : ℕ → T₀) → L.up {k = L.zero} L.zero (L.lim F) L.≅ L.lim (λ n → L.up {k = L.zero} L.zero (F n))
upL F = L.upˡ {r = L.zero} (L.l≅ (λ n → L.upʳ {r = L.zero} (L.≅-refl⁰ (F n))))

to1₀ : ∀ {y : T₀} {η} → Rel 1 y η → L.up {k = L.zero} L.zero y S.⊴⁺ η
to1₀ z⊴ = S.u⊴ NA.z⊴
to1₀ (s⊴s {x = y} p) = S.≅⊴ (upS y) (S.s⊴s (to1₀ p))
to1₀ (⊴s p) = S.⊴s (to1₀ p)
to1₀ (⊴l n p) = S.⊴l n (to1₀ p)
to1₀ (l⊴ {F = F} h) = S.≅⊴ (upL F) (S.l⊴ (λ n → to1₀ (h n)))
to1₀ (⊴b {r = inj₁ _} p) = S.⊴b (to1₀ p)
to1₀ (nd {p = ()} e h)
to1₀ (nt {p = ()} e h)
to1₀ (em q) = S.u⊴ (NA.em⊴ q)
to1₀ (u⊴ {r = ()} p)
to1₀ (dg z1 {F = F} h) = S.≅⊴ (upL F) (S.dg (λ n a c → to1₀ (h n a c)))
to1₀ (dg (zs ()) h)
to1₀ (≅⊴ e p) = S.≅⊴ (L.upˡ {r = L.zero} (L.upʳ {r = L.zero} e)) (to1₀ p)

to1 : ∀ {x : T₁} {η} → Rel 1 x η → x S.⊴⁺ η
to1 z⊴ = S.z⊴
to1 (s⊴s p) = S.s⊴s (to1 p)
to1 (⊴s p) = S.⊴s (to1 p)
to1 (⊴l n p) = S.⊴l n (to1 p)
to1 (l⊴ h) = S.l⊴ (λ n → to1 (h n))
to1 (⊴b {r = inj₁ _} p) = S.⊴b (to1 p)
to1 (nd {r = inj₁ _} {p = L.zero} L.z≅ h) = S.nd (λ y a q → to1 (h y a q (L.≅-refl⁰ y)))
to1 (nd {r = inj₁ _} {p = L.suc ()} L.z≅ h)
to1 (nt {p = L.zero} L.z≅ h) = S.nt (λ y a q → to1 (h y a q (L.≅-refl⁰ y)))
to1 (nt {p = L.suc ()} L.z≅ h)
to1 (em ())
to1 (u⊴ {r = L.zero} p) = to1₀ p
to1 (dg z1 h) = S.dg (λ n a c → to1 (h n a c))
to1 (dg (zs ()) h)
to1 (≅⊴ e p) = S.≅⊴ e (to1 p)
```

## 2 第 2 层

```agda
from2 : ∀ {ℓ} {x : L.Ordᶜ ℓ} {η} → x R2.⊴² η → Rel 2 x η
from2 R2.z⊴ = z⊴
from2 (R2.s⊴s p) = s⊴s (from2 p)
from2 (R2.⊴s p) = ⊴s (from2 p)
from2 (R2.⊴l n p) = ⊴l n (from2 p)
from2 (R2.l⊴ h) = l⊴ (λ n → from2 (h n))
from2 (R2.⊴b₁ p) = ⊴b (from2 p)
from2 (R2.⊴b₀ p) = ⊴b (from2 p)
from2 (R2.n1 h) = nd (L.s≅ L.z≅) (λ y a q s → from2 (h y a (to1 q) s))
from2 (R2.t1 h) = nt (L.s≅ L.z≅) (λ y a q s → from2 (h y a (to1 q) s))
from2 (R2.n0 h) = nd L.z≅ (λ y a q s → from2 (h y a q))
from2 (R2.n0′ h) = nd L.z≅ (λ y a q s → from2 (h y a q))
from2 (R2.e1 q) = em (from1 q)
from2 (R2.e0 q) = em (na→ q)
from2 (R2.u1 p) = u⊴ (from2 p)
from2 (R2.u0 p) = u⊴ (from2 p)
from2 (R2.dg h) = dg (zs z1) (λ n a c → from2 (h n a c))
from2 (R2.≅⊴ e p) = ≅⊴ e (from2 p)
```

## 3 搬过来的陈述

```agda
Diag¹ : Rel 1 (L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀)) (ψ₁ G.top)
Diag¹ = from1 Diag

e₂⊴γ₂ᴿ : ∀ n → Rel 1 (e₂ n) (γ₂ n)
e₂⊴γ₂ᴿ n = from1 (e₂⊴γ₂ n)

diag₂→ : Diag₂ᵀ → Rel 2 (L.ψ (σ₃ L.zero) (λ r → r) (L.Ω S2.ℓ₀)) (ψ₂ G.top)
diag₂→ = from2
```
