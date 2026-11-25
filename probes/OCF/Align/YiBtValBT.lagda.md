# YiBtVal：`T₃ᵐ` 与 BTBO 的参照

**验收文件，档位：编译定理 (`T₃ᵐ-own`) 与条件定理 (`FromMono.btbo`，前提是模块参数 `mono : MonoT`)。** `T₃ᵐ-own`：`T₃ᵐ` 的第 `n` 项不低于 ψ₀(Ω_{κₙ})，`κₙ` 是第 `n` 个链点读成层号后的参照层号 (`toIL`)。
`FromMono.btbo`：若闭项对层号值单调 (`MonoT`)，则 Level 族的 BTBO 参照 `D.BTBOᴵ` (`Diagonal` 取 `Uniform`) ≼ 读回的 `T₃ᵐ`。`MonoT` 没有证；`mono-⊑` 是它在层号结构可比时的实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiBtValBT where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Lgl)
open import OCF.Align.YiIrrIf using (R; one; _+ʳ_; Legal; read0; read0-legal)
open import OCF.Align.YiLvIf using (Plain)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ; Ptᵐ; pointsᵐ; obsᵐ; foldᵐ₃; rplain)
open Ptᵐ using (coordᵐ; lawfulᵐ)
open import OCF.Align.YiIrrFoldValue using (read; read-add)
open import OCF.Align.YiBtValAdm using (toIL; toIL-c)
open import OCF.Align.YiBtValFin using (Zs; lower-any)
import OCF.Align.RR4MonoFragment as MF
import OCF.Align.Diagonal as Diag
import OCF.Align.Uniform as Un
import OCF.Align.Level as L
import OCF.Align.Value as V
open L using (_<ᴵ_)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼; ⊑→≼)

module D = Diag.Diagonal Un.Uniform
```

## 1 链点的层号含字面的零

`ZL K`：`zero <ᴵ toIL K`；`Z⁺L K`：`zero <ᴵ suc (toIL K)`；`ZsL K`：`Zs (toIL K)`。都在 `LF` 上陈述，与 `Plain`, `Legal` 的证据无关。

```agda
Z⁺L ZL ZsL : LF → Set
Z⁺L B.zero = ⊤
Z⁺L (B.suc k) = Z⁺L k
Z⁺L (B.lim f) = Σ ℕ λ n → ZL (f n)
Z⁺L (B.lc k c w b t g) = ⊥
ZL B.zero = ⊥
ZL (B.suc k) = Z⁺L k
ZL (B.lim f) = Σ ℕ λ n → ZL (f n)
ZL (B.lc k c w b t g) = ⊥
ZsL B.zero = ⊤
ZsL (B.suc k) = Z⁺L k
ZsL (B.lim f) = ∀ n → ZsL (f n)
ZsL (B.lc k c w b t g) = ⊥

ZL→Z⁺L : ∀ K → ZL K → Z⁺L K
ZL→Z⁺L B.zero ()
ZL→Z⁺L (B.suc k) z = z
ZL→Z⁺L (B.lim f) z = z
ZL→Z⁺L (B.lc k c w b t g) ()

Z⁺L→ : ∀ K pK lK → Z⁺L K → L.zero <ᴵ L.suc (toIL K pK lK)
ZL→ : ∀ K pK lK → ZL K → L.zero <ᴵ toIL K pK lK
Z⁺L→ B.zero pK lK z = L.zero
Z⁺L→ (B.suc k) pK lK z = L.suc (Z⁺L→ k pK lK z)
Z⁺L→ (B.lim f) pK (st , lg) (n , z) = L.suc (L.lim n (ZL→ (f n) (pK n) (lg n) z))
Z⁺L→ (B.lc k c w b t g) () lK z
ZL→ B.zero pK lK ()
ZL→ (B.suc k) pK lK z = Z⁺L→ k pK lK z
ZL→ (B.lim f) pK (st , lg) (n , z) = L.lim n (ZL→ (f n) (pK n) (lg n) z)
ZL→ (B.lc k c w b t g) () lK z

ZsL→ : ∀ K pK lK → ZsL K → Zs (toIL K pK lK)
ZsL→ B.zero pK lK z = tt
ZsL→ (B.suc k) pK lK z = Z⁺L→ k pK lK z
ZsL→ (B.lim f) pK (st , lg) z = λ n → ZsL→ (f n) (pK n) (lg n) (z n)
ZsL→ (B.lc k c w b t g) () lK z

Z0 : ∀ x c → ZL (read0 x) → ZL (read0 (x +ʳ c))
Z0 x G.zero h = h
Z0 x (G.suc c) h = ZL→Z⁺L (read0 (x +ʳ c)) (Z0 x c h)
Z0 x (G.lim f) h = 0 , Z0 x (f 0) h
Z0 x (G.lc () c t g) h
Z0 x (G.em () a) h
Z0 x G.top h = ZL→Z⁺L (read0 x) h

Zs0 : ∀ x c → ZL (read0 x) → ZsL (read0 x) → ZsL (read0 (x +ʳ c))
Zs0 x G.zero h hs = hs
Zs0 x (G.suc c) h hs = ZL→Z⁺L (read0 (x +ʳ c)) (Z0 x c h)
Zs0 x (G.lim f) h hs = λ n → Zs0 x (f n) h hs
Zs0 x (G.lc () c t g) h hs
Zs0 x (G.em () a) h hs
Zs0 x G.top h hs = ZL→Z⁺L (read0 x) h

inv : ∀ n → ZL (read0 (coordᵐ (pointsᵐ n))) × ZsL (read0 (coordᵐ (pointsᵐ n)))
inv zero = tt , tt
inv (suc n) =
  Z0 (coordᵐ (pointsᵐ n)) (obsᵐ (pointsᵐ n)) (proj₁ (inv n)) ,
  Zs0 (coordᵐ (pointsᵐ n)) (obsᵐ (pointsᵐ n)) (proj₁ (inv n)) (proj₂ (inv n))
```

## 2 每一项不低于它自己层号上的 ψ₀(Ω_·)

```agda
κ : ℕ → L.Ordᴵ
κ n = toIL (read0 (coordᵐ (pointsᵐ n))) (rplain (coordᵐ (pointsᵐ n)))
  (read0-legal (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n)))

term-own : ∀ n → L.ψ⁰ (L.Ω (κ n)) ≼ read (obsᵐ (pointsᵐ n))
term-own n =
  lower-any (read0 (coordᵐ (pointsᵐ n))) (rplain (coordᵐ (pointsᵐ n)))
    (read0-legal (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n)))
    (toIL-c (read0 (coordᵐ (pointsᵐ n))) (rplain (coordᵐ (pointsᵐ n)))
      (read0-legal (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n))))
    (ZsL→ (read0 (coordᵐ (pointsᵐ n))) (rplain (coordᵐ (pointsᵐ n)))
      (read0-legal (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n))) (proj₂ (inv n)))

T₃ᵐ-own : ∀ n → L.ψ⁰ (L.Ω (κ n)) ≼ read T₃ᵐ
T₃ᵐ-own n = ≼l n (term-own n)
```

## 3 与 BTBO 的参照：归结为一条单调性

参照 `D.γ 0 = 1`, `D.γ (n+1) = ψ⁰ (Ω (toLevel (D.γ n)))`, `D.BTBOᴵ = lim (D.γ ∘ suc)`。树一侧 `η₀ = 1`, `ηₙ₊₁ = ηₙ + foldᵐ₃ ηₙ`。
两条链对 `n` 归纳并行，每步要 "参照的值 ≼ 链点的值 ⇒ 参照层号上的 ψ₀(Ω_·) ≼ 链点上的闭项" (`MonoT`)。

```agda
MonoT : Set
MonoT = ∀ (x : L.Ordᶜ L.zero) (h : L.HS x) (a : R) (l : Lgl B.zero a) → x ≼ read a →
  L.ψ⁰ (L.Ω (L.toLevel x h)) ≼ read (foldᵐ₃ a l)

+ʳ≽ : ∀ θ η {y : L.Ordᶜ L.zero} → y ≼ read η → y ≼ read (θ +ʳ η)
+ʳ≽ θ η q = ≼-trans q (≼-trans (MF.≼-+ˡ (read θ) (read η)) (≅→≼ (L.≅-sym (read-add θ η))))

module FromMono (mono : MonoT) where

  chain : ∀ n → D.γ n ≼ read (coordᵐ (pointsᵐ n))
  chain zero = ≼-refl _
  chain (suc n) = +ʳ≽ (coordᵐ (pointsᵐ n)) (obsᵐ (pointsᵐ n))
    (mono (D.γ n) (D.cert n) (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n)) (chain n))

  btbo : D.BTBOᴵ ≼ read T₃ᵐ
  btbo = l≼ (λ n → ≼l n
    (mono (D.γ n) (D.cert n) (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n)) (chain n)))
```

## 4 `MonoT` 的实例：层号结构可比时

```agda
mono-⊑ : ∀ (x : L.Ordᶜ L.zero) (h : L.HS x) (a : R) (l : Lgl B.zero a) →
  L.toLevel x h L.⊑ᴵ toIL (read0 a) (rplain a) (read0-legal a l) → ZsL (read0 a) →
  L.ψ⁰ (L.Ω (L.toLevel x h)) ≼ read (foldᵐ₃ a l)
mono-⊑ x h a l le z =
  ≼-trans (⊑→≼ (L.ψ⁰ (L.Ω (L.toLevel x h))) (L.Ψ⁰-mono le))
    (lower-any (read0 a) (rplain a) (read0-legal a l) (toIL-c (read0 a) (rplain a) (read0-legal a l))
      (ZsL→ (read0 a) (rplain a) (read0-legal a l) z))

-- 第 0 步的实例: 参照 1 与链点 1.
mono₀ : L.ψ⁰ (L.Ω (L.toLevel (D.γ 0) (D.cert 0))) ≼ read (obsᵐ (pointsᵐ 0))
mono₀ = mono-⊑ (D.γ 0) (D.cert 0) one tt L.⊑ᴵ-refl tt
```
