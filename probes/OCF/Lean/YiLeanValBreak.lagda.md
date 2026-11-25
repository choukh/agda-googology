# YiLeanVal：新树上结构可比的证法同样不通

**验收文件，档位：编译定理 (否定)。** 新树的一切链点层号 `κ m` 里没有字面前驱 ≅ᴵ ω (`no-sω-κ`)，而参照的 `D.L 1` 含字面的 ω+1 (`YiMonoBreak.sω-L1`)，所以对一切 n ≥ 1 与一切下标 m 都没有 `D.L n ⊑ᴵ κ m` (`no-L`)。
这只否定 "`⊑ᴵ` 加 `Ψ⁰-mono`" 这一种证法，不否定 BTBO 下界本身，也不否定 `PEmb`/`≼ᵖ` 的路。原因与旧树相同：链从 1 起步，每个链点是累加 `ηₙ + F ηₙ`，ℕ 极限的第 0 项都非零。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLeanValBreak where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanTw3
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read)
open import OCF.Lean.YiLeanValFin using (HS-read; κ)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiMonoBreak using (sω-L1; L-chain)
import OCF.Align.Level as L
open L using (_<ᴵ_; _≅ᴵ_; _⊑ᴵ_)
```

`NZ a`：`a` 里每个 ℕ 极限的第 0 项不是零。`toLevel` 之后 ≅ᴵ ω 的层号是第 0 项为零的极限。

```agda
NZ0 NZ : R → Set
NZ0 G.zero = ⊥
NZ0 (G.suc a) = ⊤
NZ0 (G.lim f) = ⊤
NZ0 (G.lc () g)
NZ0 (G.em () a)
NZ0 G.top = ⊤
NZ G.zero = ⊤
NZ (G.suc a) = NZ a
NZ (G.lim f) = NZ0 (f 0) × (∀ n → NZ (f n))
NZ (G.lc () g)
NZ (G.em () a)
NZ G.top = ⊤

not0 : ∀ a h → NZ0 a → ¬ (L.zero ≅ᴵ L.toLevel (read a) h)
not0 (G.suc a) h z ()
not0 (G.lim f) h z ()
not0 G.top h z ()

notω : ∀ a h → NZ a → ¬ (L.ωᴵ ≅ᴵ L.toLevel (read a) h)
notω (G.lim f) h (z0 , z) (L.l≅ e) = not0 (f 0) (L.hl₁ h 0) z0 (e 0)

noω : ∀ a h → NZ a → ∀ {c} → c <ᴵ L.toLevel (read a) h → ¬ (L.ωᴵ ≅ᴵ c)
noω (G.suc a) h z L.zero = notω a (L.hs⁻ h) z
noω (G.suc a) h z (L.suc q) = noω a (L.hs⁻ h) z q
noω (G.lim f) h (z0 , z) (L.lim n q) = noω (f n) (L.hl₁ h n) (z n) q
noω G.top h z L.zero ()

no-sω : ∀ a h → NZ a → ¬ (L.suc L.ωᴵ ⊑ᴵ L.toLevel (read a) h)
no-sω a h z (L.s⊑ e q) = noω a h z q e
```

`x + c` 在极限处逐项加在 `x` 之后，所以只要 `x` 非零且满足 `NZ`，和就满足 `NZ`，与 `c` 无关 (与折叠的内容无关)。

```agda
NZ0-add : ∀ x c → NZ0 x → NZ0 (plus zero x c)
NZ0-add x G.zero h = h
NZ0-add x (G.suc c) h = tt
NZ0-add x (G.lim f) h = tt
NZ0-add x (G.lc () g) h
NZ0-add x (G.em () a) h
NZ0-add x G.top h = tt

NZ-add : ∀ x c → NZ0 x → NZ x → NZ (plus zero x c)
NZ-add x G.zero h0 h = h
NZ-add x (G.suc c) h0 h = NZ-add x c h0 h
NZ-add x (G.lim f) h0 h = NZ0-add x (f 0) h0 , λ n → NZ-add x (f n) h0 h
NZ-add x (G.lc () g) h0 h
NZ-add x (G.em () a) h0 h
NZ-add x G.top h0 h = h

inv-nz : ∀ n → NZ0 (co (pts n)) × NZ (co (pts n))
inv-nz zero = tt , tt
inv-nz (suc n) =
  NZ0-add (co (pts n)) (obs (pts n)) (proj₁ (inv-nz n)) ,
  NZ-add (co (pts n)) (obs (pts n)) (proj₁ (inv-nz n)) (proj₂ (inv-nz n))

no-sω-κ : ∀ m → ¬ (L.suc L.ωᴵ ⊑ᴵ κ m)
no-sω-κ m = no-sω (co (pts m)) (HS-read (co (pts m)) (lw (pts m))) (proj₂ (inv-nz m))

no-L : ∀ n m → ¬ (D.L (suc n) ⊑ᴵ κ m)
no-L n m le = no-sω-κ m (L.⊑ᴵ-trans sω-L1 (L.⊑ᴵ-trans (L-chain n) le))
```
