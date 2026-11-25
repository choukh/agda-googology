# YiXVNeedOne
> 验收文件。档位：编译定理。原第 1 行 Need1：read(G(pt 1)) ≼ D.γ 2；经全部 pre 上界与参照 Ω_ω 行。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVNeedOne where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; ⊑→≼)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.BTBOFullV3 using (Fstep)
open import OCF.Align.Uniform using (Uniform)
open import OCF.Align.YiLvValFin using (reference-ω-row)
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVStart as Start
import OCF.Lean.YiXVSourcePrefixes as Prefix

one-plus : ∀ n → L.suc L.zero L.+ L.natᶜ n ≡ L.natᶜ (suc n)
one-plus zero = refl
one-plus (suc n) = cong L.suc (one-plus n)
point : ∀ n → Ord-Ord.iter (L.suc L.zero L.+_) L.zero n ≡ L.natᶜ n
point zero = refl
point (suc n) = trans (cong (L.suc L.zero L.+_) (point n)) (one-plus n)
finite-level : ∀ n (h : L.HS (L.natᶜ n)) → L.toLevel (L.natᶜ n) h ≡ L.natᴵ n
finite-level zero h = refl
finite-level (suc n) h = cong L.suc (finite-level n (L.hs⁻ h))
level-point : ∀ n (x : L.Ordᶜ L.zero) → x ≡ L.natᶜ n → (h : L.HS x) → L.toLevel x h ≡ L.natᴵ n
level-point n .(L.natᶜ n) refl h = finite-level n h
ω-level : L.toLevel (L.ψ⁰ (L.Ω L.zero)) (Uniform L.zero) L.≅ᴵ L.ωᴵ
ω-level = L.l≅ (λ n → subst (λ x → x L.≅ᴵ L.natᴵ n)
  (sym (level-point n _ (point n) (L.hl₁ (Uniform L.zero) n))) (L.≅ᴵ-refl _))
ω-below : L.ωᴵ L.⊑ᴵ D.L 1
ω-below = L.⊑ᴵ-trans (L.Sim→⊑ᴵ L.suc) (L.s⊑′ (L.≺ᴵ-respˡ (L.≅ᴵ-sym ω-level)
  (L.toLevel-≺ (Uniform L.zero) (D.cert 1) (Fstep L.zero))))
reference : L.ψ⁰ (L.Ω L.ωᴵ) ≼ D.γ 2
reference = ⊑→≼ _ (L.Ψ⁰-mono ω-below)
row : Read.read (T.G (T.pt 1)) ≼ L.ψ⁰ (L.Ω L.ωᴵ)
row = subst (λ y → Read.read (T.G (T.pt 1)) ≼ y) (sym reference-ω-row)
  (l≼ (λ n → ≼l (suc (suc n)) (Prefix.allpre n)))
need1 : Start.Need1
need1 = ≼-trans row reference
```
