# YiPE 极限层号：主线折叠的部分和接住阶梯

**验收文件，档位：编译定理与条件定理。** `KEYat η`：参照 ψ⁰(Ω_{⌜η⌝}) 的前驱嵌进主线 `F η` 的前驱 (同一层号)。零层与 `top` 是定理 (`key-zero`, `key-top`)；极限层号 `lim f` 上，`F` 是各支折叠值的部分和 (累加)，由 `YiPEStair.stair` 归到各支 (`KeyLim.key-lim`)，前提是相邻两支相等或读回严格上升 (`ss`)。
`key-spine : KEYsuc → Spine η l → KEYat η l`：沿极限脊柱归纳，只剩后继层号 (`KEYsuc`)。于是 `btbo-FS : FUNC → KEYsuc → (∀ m → Spine 链点 m) → D.BTBOᴵ ≼ read T₃`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPEKey where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold using (fold; psum)
open import OCF.Lean.YiLeanTw3 using (R; F; F-lgl; T₃; pts; module Pt)
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read; read-plus)
open import OCF.Lean.YiLeanValFin using (HS-read; lower-read)
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA
import OCF.Align.Level as L
open L using (Ordᴵ; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_)
import OCF.Align.Uniform as Un
open import OCF.Align.Value using (_≼_)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.BTBOFullEmb using (PEmb)
open import OCF.Align.YiVmConExact using (embˣ; XEmb; Tri; tri→cplˣ)
open import OCF.Lean.YiChainOne using (module Phi)
open Phi using (PHI)
open import OCF.Lean.YiChainFlat using (flat; ψ⁰-flat)
open import OCF.Lean.YiFlatWit using (flatΩ-≺)
open import OCF.Lean.YiFlatChain using (lead0)
open import OCF.Lean.YiPEStep using (_⊕_; L⁺; PEmb-≅ˡ; toLevel-+; HS-≅; key₀; FUNC; KEY; btbo-FK; btbo-FK⁺)
open import OCF.Lean.YiPEStair using (module Stair)
```

## 1 ψ⁰∘Ω 对层号的严格单调

第 0 层的 ψ⁰ 把结构前驱送到结构前驱；经压平 (`ψ⁰-flat`, `flatΩ-≺`) 得到 ψ⁰∘Ω 的版本。

```agda
ψ⁰-≺ : ∀ {x y : L.Ordᶜ L.zero} → x L.≺ y → L.ψ⁰ x L.≺ L.ψ⁰ y
ψ⁰-≺ {y = L.suc b} (L.≺z e) = L.≺l 2 (L.≺-respˡ (L.ψ⁰-≅ (L.≅-sym e)) (lead0 (L.ψ⁰ b) (L.z≺ψ⁰ b)))
ψ⁰-≺ (L.≺s d) = L.≺l 1 (ψ⁰-≺ d)
ψ⁰-≺ (L.≺l n d) = L.≺l n (ψ⁰-≺ d)
ψ⁰-≺ (L.≺i {p = ()} x ex d)
ψ⁰-≺ (L.≺u {r = ()} d)

ψ⁰Ω-≺ : ∀ {a b} → a ≺ᴵ b → L.ψ⁰ (L.Ω a) L.≺ L.ψ⁰ (L.Ω b)
ψ⁰Ω-≺ {a} {b} r = L.≺-respʳ (L.≺-respˡ (L.≅-sym (ψ⁰-flat (L.Ω a))) (ψ⁰-≺ (flatΩ-≺ r))) (L.≅-sym (ψ⁰-flat (L.Ω b)))
```

## 2 同一层号上的结构下界

```agda
KEYat : ∀ (η : R) → Lgl zero η → Set
KEYat η l = PEmb (L⁺ (L.toLevel (read η) (HS-read η l))) (L.toLevel (read (F η l)) (HS-read (F η l) (F-lgl η l)))

key-zero : KEYat G.zero tt
key-zero = XEmb.P (embˣ _ (Un.Uniform L.zero) _ _ (proj₁ (PHI (λ _ → fold) (G.suc G.zero))))

key-top : KEYat G.top tt
key-top = key₀

eqκ : ∀ {x y : R} → x ≡ y → (lx : Lgl zero x) (ly : Lgl zero y) →
  L.toLevel (read x) (HS-read x lx) ≅ᴵ L.toLevel (read y) (HS-read y ly)
eqκ {x} refl lx ly = L.toLevel-≅ _ _ (L.≅-refl⁰ (read x))
```

极限层号：源的第 n 项是 ψ⁰(Ω_{κf n})，目标的第 n 块是 `F (f n)`，部分和 `psum` 逐块累加 (`read-plus`, `toLevel-+`)。

```agda
module KeyLim (f : ℕ → R) (st : ∀ n → Cp zero (f n) (f (suc n))) (lf : ∀ n → Lgl zero (f n))
  (ss : ∀ n → (f n ≡ f (suc n)) ⊎ (read (f n) L.≺ read (f (suc n))))
  (kf : ∀ n → KEYat (f n) (lf n)) where

  κf : ℕ → Ordᴵ
  κf n = L.toLevel (read (f n)) (HS-read (f n) (lf n))

  U : L.HS (L.ψ⁰ (L.Ω (L.toLevel (read (G.lim f)) (HS-read (G.lim f) (st , lf)))))
  U = Un.Uniform (L.toLevel (read (G.lim f)) (HS-read (G.lim f) (st , lf)))

  f′ : ℕ → Ordᴵ
  f′ n = L.toLevel (L.ψ⁰ (L.Ω (κf n))) (L.hl₁ U n)

  H : L.HS (read (F (G.lim f) (st , lf)))
  H = HS-read (F (G.lim f) (st , lf)) (F-lgl (G.lim f) (st , lf))

  Fs : ℕ → R
  Fs n = F (f n) (lf n)

  t Y : ℕ → Ordᴵ
  t n = L.toLevel (read (psum zero Fs n)) (L.hl₁ H n)
  Y n = L.toLevel (read (Fs n)) (HS-read (Fs n) (F-lgl (f n) (lf n)))

  P : ∀ n → PEmb (f′ n) (Y n)
  P n = PEmb-≅ˡ (L.toLevel-≅ (L.hl₁ U n) (Un.Uniform (κf n)) (L.≅-refl⁰ _)) (kf n)

  t0 : Y 0 ≅ᴵ t 0
  t0 = L.toLevel-≅ _ _ (L.≅-refl⁰ _)

  tY : ∀ n → (t n ⊕ Y (suc n)) ≅ᴵ t (suc n)
  tY n = L.≅ᴵ-trans (L.≅ᴵ-sym (toLevel-+ (read (psum zero Fs n)) (read (Fs (suc n))) _ _ hn))
    (L.toLevel-≅ hn _ (L.≅-sym (read-plus (psum zero Fs n) (Fs (suc n)))))
    where
    hn : L.HS (read (psum zero Fs n) L.+ read (Fs (suc n)))
    hn = HS-≅ (L.hl₁ H (suc n)) (read-plus (psum zero Fs n) (Fs (suc n)))

  dec : ∀ n → (f′ n ≅ᴵ f′ (suc n)) ⊎ (f′ n ≺ᴵ f′ (suc n))
  dec n with ss n
  ... | inj₁ e = inj₁ (L.toLevel-≅ _ _ (L.ψ⁰-≅ (L.Ω-≅ (eqκ e (lf n) (lf (suc n))))))
  ... | inj₂ lt = inj₂ (L.toLevel-≺ _ _ (ψ⁰Ω-≺ (L.toLevel-≺ _ _ lt)))

  key-lim : KEYat (G.lim f) (st , lf)
  key-lim = Stair.stair f′ _ dec t Y P t0 tY (λ n → L.Sim→⊑ᴵ (L.lim n))
```

## 3 沿极限脊柱归纳

`Spine η l`：从根沿极限的各支往下，直到后继、零或 `top`；每个极限的相邻两支相等或读回严格上升。

```agda
data Spine : (η : R) → Lgl zero η → Set where
  sp0 : Spine G.zero tt
  spT : Spine G.top tt
  spS : ∀ a (l : Lgl zero a) → Spine (G.suc a) l
  spL : ∀ f st lf → (∀ n → (f n ≡ f (suc n)) ⊎ (read (f n) L.≺ read (f (suc n)))) →
    (∀ n → Spine (f n) (lf n)) → Spine (G.lim f) (st , lf)

KEYsuc : Set
KEYsuc = ∀ a (l : Lgl zero a) → KEYat (G.suc a) l

key-suc₀ : KEYat (G.suc G.zero) tt
key-suc₀ = key₀

tri→KEYsuc : Tri → KEYsuc
tri→KEYsuc t a l = XEmb.P (embˣ _ (Un.Uniform _) _ _ (tri→cplˣ t _ _ (lower-read (G.suc a) l)))

key-spine : KEYsuc → ∀ {η l} → Spine η l → KEYat η l
key-spine ks sp0 = key-zero
key-spine ks spT = key-top
key-spine ks (spS a l) = ks a l
key-spine ks (spL f st lf ss sp) = KeyLim.key-lim f st lf ss (λ n → key-spine ks (sp n))

SpineT : Set
SpineT = ∀ m → Spine (co (pts m)) (lw (pts m))

key-from : KEYsuc → SpineT → KEY
key-from ks sp m = key-spine ks (sp m)

btbo-FS : FUNC → KEYsuc → SpineT → D.BTBOᴵ ≼ read T₃
btbo-FS func ks sp = btbo-FK func (key-from ks sp)

btbo-FS⁺ : FUNC → KEYsuc → SpineT → D.BTBOᴵ ≼ NA.read NT.T⁺
btbo-FS⁺ func ks sp = btbo-FK⁺ func (key-from ks sp)

spine₀ : Spine (co (pts 0)) (lw (pts 0))
spine₀ = spT
```
