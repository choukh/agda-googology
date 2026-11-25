# 指定后继孩子族上的 BTBO 共尾链
验收文件；编译定理：指定孩子族的回灌链支配 BTBO 参照列；整行出口在 YiC0Rows。
没有改变公共树、底或路径；本件的 F2 对象经 YiC0Connect 接回同一个 neck。
来源：链证明平移 YiLSBtbo，额外后继的前驱嵌入由 YiC0Pad.V3 加左项得到。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC0Node where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here; emb)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiLSFold using (lower; ok-B₀; ψs-⊵; n+)
open import OCF.Lean.YiLSRel using (cs)
open import OCF.Lean.YiLSTw1 using (es; ez; eq0; LiftP; LiftP-∙; E→≅)
open import OCF.Lean.YiLSBtbo using (cp; cp≅; Mono-cp)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (ordᴰ)
import OCF.Lean.YiC0Pad as P
open P using (module WT)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValNeg using (add-≺)
open import OCF.Align.BTBOFullV3 using (bkᴵ; ≺→⊑₀)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
open import OCF.Align.BTBOFullLv using (SV-L)
open import OCF.Align.BTBOFull using (St-bk; bk≅γ)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.YiMonoEmb using (PEmb-∘; PEmb-⊑)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.NoCumsum as N
open import OCF.Lean.YiBtboV2 using (V2′)
import OCF.Lean.YiPEStep as PS
h₁ : Tr zero → LF
h₁ x = suc (P.h₁ x)
εh : (x : Tr zero) → Ev (h₁ x)
εh = P.εh
ρh : (x : Tr zero) → Rt (h₁ x)
ρh = P.ρh
wh : (x : Tr zero) → zero ≤ h₁ x
wh x = ins (P.wh x)
G : Tr zero → Tr zero
G x = ψ₀ (h₁ x) (εh x) (ρh x) (Ωt (h₁ x))
G-nz : (x : Tr zero) → zero ⊢ zero ◃ G x
G-nz x = nz⊥ (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (Ωt (h₁ x))
feed-w : (x : Tr zero) → zero ≤ h₁ x
feed-w x = self ∙ wh x
feed-lp : (x : Tr zero) → LiftP (feed-w x)
feed-lp zero = tt
feed-lp (suc x) = feed-lp x
feed-lp (lim f a) = λ n → feed-lp (f n)
feed-lp (Ω () _)
feed-lp (up _ () _ _)
K : Tr zero → Tr zero
K x = ψs (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) zero (feed-w x) (suc zero) ◃s (Ωt (h₁ x))
pt : ℕ → Tr zero
pt = iter K zero
lvl : Tr zero → L.Ordᴵ
lvl x = L.suc (P.lvl x)
κ : ℕ → L.Ordᴵ
κ m = lvl (pt m)
LOWER : ∀ m → L.ψ⁰ (L.Ω (κ m)) ≼ read (G (pt m))
LOWER m = lower (n+ (P.nl-↑ (pt m))) (εh (pt m)) (ρh (pt m)) (B₀ (h₁ (pt m))) (ok-B₀ (h₁ (pt m))) (cs (P.corr-↑ (pt m) (HSr (pt m))))
KG : ∀ x → read (K x) L.≅ read (G x)
KG x = E→≅ (eq0 (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (feed-w x) (feed-lp x) (suc zero) ◃s (es ez) (Ωt (h₁ x)))

V3F : ∀ m → WT.Eb (ordᴰ (cp (pt m))) (read (G (pt m)))
V3F m = record
  { map = λ p → read F0 L.+ WT.map e p
  ; below = λ p → ≺→⊑₀ (◃→≺ lt-tree)
      (L.≺-respʳ (add-≺ (read F0) (WT.below e p)) (L.≅-sym (read-+ F0 X)))
  ; mono = λ p q r → add-≺ (read F0) (WT.mono e p q r)
  ; coh = λ p q r → L.add-≅ (L.≅-refl⁰ (read F0)) (WT.coh e p q r) }
  where
  a = P.h₁ (pt m)
  ε = εh (pt m)
  ρ = ρh (pt m)
  Bb = B₀ (h₁ (pt m))
  B′ = dS a ε ρ Bb zero
  β = bs Bb a (ins self)
  nβ = ns Bb a (ins self)
  F0 X top : Tr zero
  F0 = ψ⊥ a ε ρ B′ (suc zero)
  X = ψ⊥ a ε ρ B′ β
  top = F0 + X
  lt-tree : zero ⊢ top ◃ G (pt m)
  lt-tree = ◃t (+-mono F0 (mono⊥ a ε ρ B′ {x = β} {y = suc (next β nβ)} (◃t (◃l zero) ◃s))) (◃l 1)
  e = proj₁ (P.V3 (pt m) ε ρ B′ (λ j w → ⊴r))

shift : ∀ x → PEmb (L.toLevel (read (G x)) (HSr (G x))) (lvl (K x))
shift x = PS.PEmb-≅ʳ
  (PEmb-∘ (PS.PEmb-shift P.L₂ (L.toLevel (read (G x)) (HSr (G x))))
    (PEmb-⊑ (L.Sim→⊑ᴵ L.suc)))
  (L.s≅ (PS.⊕-≅ P.L₂ (L.toLevel-≅ (HSr (G x)) (HSr (K x)) (L.≅-sym (KG x)))))
emb : ∀ n m → D.γ n ≼ read (pt m) → PEmb (D.L n) (κ (suc m))
emb n m w =
  PEmb-∘ (PW₃ (V1 (SV-L n)))
  (PEmb-∘ (PW₁ (V2′ (bkᴵ (N.L n)) (cp η) (St-bk (SV-L n)) (Mono-cp η) w′))
  (PEmb-∘ (PW₂ (HSr (G η)) (V3F m)) (shift η)))
  where
  η = pt m
  w′ : tr₀ (bkᴵ (N.L n)) ≼ tr₀ (cp η)
  w′ = ≼-trans (≅→≼ (bk≅γ n)) (≼-trans w (≅→≼ (L.≅-sym (cp≅ η))))
lowc : ∀ k → L.ψ⁰ (L.Ω (κ k)) ≼ read (pt (suc k))
lowc k = ≼-trans (LOWER k) (≅→≼ (L.≅-sym (KG (pt k))))
chainV : ∀ n → Σ ℕ (λ m → D.γ n ≼ read (pt m))
chainV zero = 1 , ⊴→≼ (ψs-⊵ (h₁ zero) (εh zero) (ρh zero) (B₀ (h₁ zero)) zero (wh zero) (suc zero) ◃s (Ωt (h₁ zero)))
chainV (suc n) = suc (suc (proj₁ (chainV n))) ,
  ≼-trans (Ψ-emb (emb n (proj₁ (chainV n)) (proj₂ (chainV n)))) (lowc (suc (proj₁ (chainV n))))
ΩN : LF
ΩN = Ωₗ zero h₁
εN : Ev ΩN
εN = tt , λ c → wh c , εh c
ρN : Rt ΩN
ρN = tt , ρh
output : Tr zero
output = ψ₀ ΩN εN ρN (Ωt ΩN)
```
