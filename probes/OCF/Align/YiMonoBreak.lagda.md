# YiMono：结构可比在第 1 步断开

**验收文件，档位：编译定理 (否定)。** 参照第 1 项的层号 `D.L 1` 含字面的 ω+1 (`sω-L1`)；树的一切链点的层号里没有 ≅ᴵ ω 的字面前驱 (`noω`，链点的不变量 `inv-nz`)。
所以对一切 n, m：`¬ (D.L (suc n) ⊑ᴵ κ m)` (`no-L`)，`mono-⊑` 在 n ≥ 1 的链点上永远用不上，错开下标也不行。
不否定 `MonoT`，也不否定值上的单调；只否定 "经 `⊑ᴵ` 与 `Ψ⁰-mono`" 这条路。入口 `no-L`, `no-mono-⊑`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiMonoBreak where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Lgl)
open import OCF.Align.YiIrrIf using (R; one; _+ʳ_; read0; read0-legal)
open import OCF.Align.YiRawFoldTw3 using (Ptᵐ; pointsᵐ; obsᵐ; rplain)
open Ptᵐ using (coordᵐ; lawfulᵐ)
open import OCF.Align.YiBtValAdm using (toIL)
open import OCF.Align.YiBtValBT using (module D; κ)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
open L using (_<ᴵ_; _≅ᴵ_; _⊑ᴵ_)
```

## 1 链点的层号里没有字面的 ω

`NZ K`：`K` 里每个 ℕ 极限的第 0 项不是零。`toIL` 之后，`≅ᴵ ωᴵ` 的层号是第 0 项为零的极限，所以 `NZ` 的层号的字面前驱都不 ≅ᴵ ω。

```agda
NZ0 NZ : LF → Set
NZ0 B.zero = ⊥
NZ0 (B.suc k) = ⊤
NZ0 (B.lim f) = ⊤
NZ0 (B.lc k c w b t g) = ⊤
NZ B.zero = ⊤
NZ (B.suc k) = NZ k
NZ (B.lim f) = NZ0 (f 0) × (∀ n → NZ (f n))
NZ (B.lc k c w b t g) = ⊥

not0 : ∀ K pK lK → NZ0 K → ¬ (L.zero ≅ᴵ toIL K pK lK)
not0 B.zero pK lK () e
not0 (B.suc k) pK lK z ()
not0 (B.lim f) pK lK z ()
not0 (B.lc k c w b t g) () lK z e

notω : ∀ K pK lK → NZ K → ¬ (L.ωᴵ ≅ᴵ toIL K pK lK)
notω B.zero pK lK z ()
notω (B.suc k) pK lK z ()
notω (B.lim f) pK lK (z0 , z) (L.l≅ h) = not0 (f 0) (pK 0) (proj₂ lK 0) z0 (h 0)
notω (B.lc k c w b t g) () lK z e

noω : ∀ K pK lK → NZ K → ∀ {c} → c <ᴵ toIL K pK lK → ¬ (L.ωᴵ ≅ᴵ c)
noω B.zero pK lK z ()
noω (B.suc k) pK lK z L.zero = notω k pK lK z
noω (B.suc k) pK lK z (L.suc q) = noω k pK lK z q
noω (B.lim f) pK lK (z0 , z) (L.lim n q) = noω (f n) (pK n) (proj₂ lK n) (z n) q
noω (B.lc k c w b t g) () lK z q

no-sω : ∀ K pK lK → NZ K → ¬ (L.suc L.ωᴵ ⊑ᴵ toIL K pK lK)
no-sω K pK lK z (L.s⊑ e q) = noω K pK lK z q e
```

链点 ηₙ₊₁ = ηₙ + 折叠值，η₀ = 1；`+ʳ` 在极限处逐项加在 ηₙ 之后，所以第 0 项不是零。与折叠的内容无关。

```agda
NZ0-add : ∀ x c → NZ0 (read0 x) → NZ0 (read0 (x +ʳ c))
NZ0-add x G.zero h = h
NZ0-add x (G.suc c) h = tt
NZ0-add x (G.lim f) h = tt
NZ0-add x (G.lc () c t g) h
NZ0-add x (G.em () a) h
NZ0-add x G.top h = tt

NZ-add : ∀ x c → NZ0 (read0 x) → NZ (read0 x) → NZ (read0 (x +ʳ c))
NZ-add x G.zero h0 h = h
NZ-add x (G.suc c) h0 h = NZ-add x c h0 h
NZ-add x (G.lim f) h0 h = NZ0-add x (f 0) h0 , λ n → NZ-add x (f n) h0 h
NZ-add x (G.lc () c t g) h0 h
NZ-add x (G.em () a) h0 h
NZ-add x G.top h0 h = h

inv-nz : ∀ n → NZ0 (read0 (coordᵐ (pointsᵐ n))) × NZ (read0 (coordᵐ (pointsᵐ n)))
inv-nz zero = tt , tt
inv-nz (suc n) =
  NZ0-add (coordᵐ (pointsᵐ n)) (obsᵐ (pointsᵐ n)) (proj₁ (inv-nz n)) ,
  NZ-add (coordᵐ (pointsᵐ n)) (obsᵐ (pointsᵐ n)) (proj₁ (inv-nz n)) (proj₂ (inv-nz n))

no-sω-κ : ∀ m → ¬ (L.suc L.ωᴵ ⊑ᴵ κ m)
no-sω-κ m = no-sω (read0 (coordᵐ (pointsᵐ m))) (rplain (coordᵐ (pointsᵐ m)))
  (read0-legal (coordᵐ (pointsᵐ m)) (lawfulᵐ (pointsᵐ m))) (proj₂ (inv-nz m))
```

## 2 参照第 1 项的层号含字面的 ω+1

`D.γ 1 = ψ⁰(Ω₁)`；它的第 1 项的第 2 项是 ψ⁰ 2，再第 2 项是 W + W，再第 1 项是 W + 1 = suc W，W = ψ⁰ 1 的层号 ≅ᴵ ω。

```agda
W : L.Ordᶜ L.zero
W = L.ψ⁰ {L.zero} (L.suc L.zero)

1+nat : ∀ n → (L.suc L.zero L.+ L.natᶜ n) ≡ L.natᶜ (suc n)
1+nat zero = refl
1+nat (suc n) = cong L.suc (1+nat n)

iterN : ∀ n → iter (L.suc L.zero L.+_) L.zero n ≡ L.natᶜ n
iterN zero = refl
iterN (suc n) = trans (cong (L.suc L.zero L.+_) (iterN n)) (1+nat n)

natN : ∀ n → L.natᴵ n ≅ᴵ L.toLevel (L.natᶜ n) (L.natᶜ-HS n)
natN zero = L.z≅
natN (suc n) = L.s≅ (natN n)

ω≅W : ∀ h → L.ωᴵ ≅ᴵ L.toLevel W h
ω≅W h = L.l≅ λ n → L.≅ᴵ-trans (natN n)
  (L.toLevel-≅ (L.natᶜ-HS n) (L.hl₁ h n)
    (subst (λ u → L.natᶜ n L.≅ u) (sym (iterN n)) (L.≅-refl⁰ (L.natᶜ n))))

sω-L1 : L.suc L.ωᴵ ⊑ᴵ D.L 1
sω-L1 = L.s⊑ (ω≅W _) (L.lim 1 (L.lim 2 (L.lim 2 (L.lim 1 L.zero))))
```

## 3 结论：一切 n ≥ 1 与一切下标 m

```agda
L-chain : ∀ n → D.L 1 ⊑ᴵ D.L (suc n)
L-chain zero = L.⊑ᴵ-refl
L-chain (suc n) = L.⊑ᴵ-trans (L-chain n) (D.L-step (suc n))

no-mono-⊑ : ∀ n (a : R) (l : Lgl B.zero a) → NZ (read0 a) →
  ¬ (L.toLevel (D.γ (suc n)) (D.cert (suc n)) ⊑ᴵ toIL (read0 a) (rplain a) (read0-legal a l))
no-mono-⊑ n a l z le =
  no-sω (read0 a) (rplain a) (read0-legal a l) z (L.⊑ᴵ-trans sω-L1 (L.⊑ᴵ-trans (L-chain n) le))

no-L : ∀ n m → ¬ (D.L (suc n) ⊑ᴵ κ m)
no-L n m le = no-sω-κ m (L.⊑ᴵ-trans sω-L1 (L.⊑ᴵ-trans (L-chain n) le))
```
