# YiMono：`MonoT` 在链点上归约到参照族的值单调

**验收文件，档位：编译定理与条件定理。** 树一侧是定理：合法坐标的读回满足 `HS` (`HS-read`)，它的 `toLevel` 与折叠用的层号 `toIL (read0 a)` 结构互模拟 (`lvl≅`)。
于是 `VMᴸ` (只谈 Level 族：`HS` 的 x ≼ y ⇒ ψ⁰(Ω_{toLevel x}) ≼ ψ⁰(Ω_{toLevel y})) 推出带 `ZsL` 证据的 `MonoTᶻ`，再推出 `D.BTBOᴵ ≼ read T₃ᵐ` (`btbo-vm`)。
`VMᴸ` 又归约到它的后继情形 `Crux` (`crux→vm`)，或归约到值序给出前驱嵌入 `EmbV` (`embV→vm`)。三者都未证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiMonoVM where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Align.RR5IrrCore as B
open B using (module G; Lgl; Cp; Dn)
open import OCF.Align.YiIrrIf using (R; read0; read0-legal)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ; Ptᵐ; pointsᵐ; obsᵐ; foldᵐ₃; rplain)
open Ptᵐ using (coordᵐ; lawfulᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiBtValAdm using (toIL; toIL-c)
open import OCF.Align.YiBtValFin using (lower-any)
open import OCF.Align.YiBtValBT using (module D; ZsL; ZsL→; inv; +ʳ≽)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≅→≼; ⊑→≼)
```

## 1 树一侧：读回的证书与层号

```agda
cp⊑ : ∀ a b → Cp B.zero a b → read a L.⊑ read b
dn⊑ : ∀ a b → Dn B.zero a b → read a L.⊑ read b
cp⊑ a b (inj₁ refl) h = h
cp⊑ a b (inj₂ p) h = dn⊑ a b p h
dn⊑ a G.zero () h
dn⊑ a (G.suc b) p h = L.≺s (cp⊑ a b p h)
dn⊑ a (G.lim f) (n , p) h = L.≺l n (cp⊑ a (f n) p h)
dn⊑ a (G.lc () c t g) p h
dn⊑ a (G.em () T) p h
dn⊑ a G.top () h

HS-read : ∀ a → Lgl B.zero a → L.HS (read a)
HS-read G.zero l = L.hz
HS-read (G.suc a) l = L.hs (HS-read a l)
HS-read (G.lim f) (st , lf) = L.hl (λ n → HS-read (f n) (lf n)) (λ n → cp⊑ (f n) (f (suc n)) (st n))
HS-read (G.lc () c t g) l
HS-read (G.em () T) l
HS-read G.top l = L.hs L.hz

lvl≅ : ∀ a h pl lg → L.toLevel (read a) h L.≅ᴵ toIL (read0 a) pl lg
lvl≅ G.zero h pl lg = L.z≅
lvl≅ (G.suc a) h pl lg = L.s≅ (lvl≅ a (L.hs⁻ h) pl lg)
lvl≅ (G.lim f) h pl lg = L.l≅ (λ n → lvl≅ (f n) (L.hl₁ h n) (pl n) (proj₂ lg n))
lvl≅ (G.lc () c t g) h pl lg
lvl≅ (G.em () T) h pl lg
lvl≅ G.top h pl lg = L.s≅ L.z≅
```

## 2 约化

```agda
VMᴸ : Set
VMᴸ = ∀ (x : L.Ordᶜ L.zero) (hx : L.HS x) (y : L.Ordᶜ L.zero) (hy : L.HS y) → x ≼ y →
  L.ψ⁰ (L.Ω (L.toLevel x hx)) ≼ L.ψ⁰ (L.Ω (L.toLevel y hy))

MonoTᶻ : Set
MonoTᶻ = ∀ (x : L.Ordᶜ L.zero) (h : L.HS x) (a : R) (l : Lgl B.zero a) → ZsL (read0 a) → x ≼ read a →
  L.ψ⁰ (L.Ω (L.toLevel x h)) ≼ read (foldᵐ₃ a l)

vm→monoᶻ : VMᴸ → MonoTᶻ
vm→monoᶻ vm x h a l z le =
  ≼-trans (vm x h (read a) (HS-read a l) le)
  (≼-trans (≅→≼ (L.ψ⁰-≅ (L.Ω-≅ (lvl≅ a (HS-read a l) (rplain a) (read0-legal a l)))))
    (lower-any (read0 a) (rplain a) (read0-legal a l) (toIL-c (read0 a) (rplain a) (read0-legal a l))
      (ZsL→ (read0 a) (rplain a) (read0-legal a l) z)))

module FromMonoᶻ (mono : MonoTᶻ) where

  chain : ∀ n → D.γ n ≼ read (coordᵐ (pointsᵐ n))
  chain zero = ≼-refl _
  chain (suc n) = +ʳ≽ (coordᵐ (pointsᵐ n)) (obsᵐ (pointsᵐ n))
    (mono (D.γ n) (D.cert n) (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n)) (proj₂ (inv n)) (chain n))

  btbo : D.BTBOᴵ ≼ read T₃ᵐ
  btbo = l≼ (λ n → ≼l n
    (mono (D.γ n) (D.cert n) (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n)) (proj₂ (inv n)) (chain n)))

btbo-vm : VMᴸ → D.BTBOᴵ ≼ read T₃ᵐ
btbo-vm vm = FromMonoᶻ.btbo (vm→monoᶻ vm)
```

`VMᴸ` 对 `x ≼ y` 的推导归纳：零、ℕ 极限的两条都是现成的，只剩 `s≼s` (`Crux`)。前驱嵌入 (`EmbV`) 经 `Ψ-emb` 一行给出 `VMᴸ`。

```agda
Crux : Set
Crux = ∀ (x : L.Ordᶜ L.zero) (hx : L.HS x) (y : L.Ordᶜ L.zero) (hy : L.HS y) → x ≼ y →
  L.ψ⁰ (L.Ω (L.suc (L.toLevel x hx))) ≼ L.ψ⁰ (L.Ω (L.suc (L.toLevel y hy)))

crux→vm : Crux → VMᴸ
crux→vm cx _ hx y hy z≼ = ⊑→≼ _ (L.Ψ⁰0 (L.toLevel y hy))
crux→vm cx (L.suc x) hx (L.suc y) hy (s≼s d) = cx x (L.hs⁻ hx) y (L.hs⁻ hy) d
crux→vm cx x hx (L.lim f) hy (≼l n d) = ≼l n (crux→vm cx x hx (f n) (L.hl₁ hy n) d)
crux→vm cx (L.lim f) hx y hy (l≼ d) = l≼ (λ n → crux→vm cx (f n) (L.hl₁ hx n) y hy (d n))
crux→vm cx x hx y hy (≼i {p = ()} z ez d)
crux→vm cx x hx y hy (i≼ {p = ()} d)
crux→vm cx x hx y hy (≼u {r = ()} d)
crux→vm cx x hx y hy (u≼ {r = ()} d)

EmbV : Set
EmbV = ∀ (x : L.Ordᶜ L.zero) (hx : L.HS x) (y : L.Ordᶜ L.zero) (hy : L.HS y) → x ≼ y →
  PEmb (L.toLevel x hx) (L.toLevel y hy)

embV→vm : EmbV → VMᴸ
embV→vm ev x hx y hy d = Ψ-emb (ev x hx y hy d)
```
