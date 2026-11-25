# 值接口的记号直连实例 (三): 锚点 ψ₀(Ω₂) 在合法块上 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiMEAnchor` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTMEAnchor where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins)
open import OCF.Lean.YiVTFold
import OCF.Align.EboLeanDef as E
open E using (HC; cof; c1; cω; cΩ; pred; fsn; fsT; γT; ψ; 𝟏; natT)
open import OCF.Align.EboLeanBase using (NF; n[]; nψ; GB; GB[]; gp; gtl; gh; gw; gc; nf-ψ; nf-Ω; nf-rep; c∷; c[])
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiMEBase
open import OCF.Lean.YiMENote

one two : L
one = suc zero
two = suc one

Low¹ : (p : Pos one) → E.T → Br one p → Set
Low¹ (inj₁ _)  = M⁰
Low¹ (inj₂ ())

Nu¹ : Pos one → E.T → Set
Nu¹ _ ν = ν ≡ []

M¹ : E.T → Tr one → Set
M¹ = Mᴰ (Sig one) Low¹ (λ _ → M⁰) Nu¹

module G⁰ = Gen {Sig zero} {λ ()} {λ ()} {λ ()}
module G¹ = Gen {Sig one} {Low¹} {λ _ → M⁰} {Nu¹}

u₀ u₁ : E.T
u₀ = []
u₁ = natT 1

ψ₀ᵗ ψ₁ᵗ : E.T → E.T
ψ₀ᵗ a = ψ u₀ a ∷ []
ψ₁ᵗ a = ψ u₁ a ∷ []

++[] : (Z : E.T → Set) (t : E.T) → Z t → Z (t ++ [])
++[] Z t q = subst Z (sym (++-identityʳ t)) q

Pu : ∀ {t} (b : Tr one) (nb : one ⊢ zero ◃ b) → M¹ (ψ₁ᵗ t) b
   → ∀ {s y} → M⁰ s y → M¹ (ψ₁ᵗ (t ++ s)) (Up zero (down stop tt) b nb y)
Pu {t} b nb mb (mz {x = y}) =
  ++[] (λ z → M¹ (ψ₁ᵗ z) (Up zero (down stop tt) b nb y)) t
    (G¹.m-zl (Up zero (down stop tt) b nb) (Up-mono zero (down stop tt) b nb) mb y)
Pu {t} b nb mb (m1 {t = s} {x = y} e r) =
  G¹.m-next (Up-nz zero (down stop tt) b nb y) (cofψ1 u₁ (t ++ s) (cof++1 t s e))
    (λ n → trans (fsnψ1 u₁ (t ++ s) n (cof++1 t s e)) (cong (λ z → replicate n (ψ u₁ z)) (pred++ t s e)))
    (Pu b nb mb r)
Pu {t} b nb mb (mL {t = s} {x = y} e h) =
  mL (cofψω u₁ (t ++ s) (cof++ω t s e))
    (λ n → subst (λ z → M¹ z (Up zero (down stop tt) b nb y))
      (sym (trans (fsnψω u₁ (t ++ s) n (cof++ω t s e)) (cong ψ₁ᵗ (fsn++ t s n e))))
      (Pu b nb mb (h n)))
Pu b nb mb (mΩ {p = ()} _ _ _)
Pu b nb mb (mU {c = ()} _ _)
Pu b nb mb (mw m d) = mw (Pu b nb mb m) (Up-mono zero (down stop tt) b nb d)

Qu : ∀ {t} (B : Base zero) (b : Tr zero) (nb : zero ⊢ zero ◃ b) → M⁰ (ψ₀ᵗ t) b
   → ∀ {s y} → M⁰ s y → M⁰ (ψ₀ᵗ (t ++ s)) (ψs zero tt tt B zero self b nb y)
Qu {t} B b nb mb (mz {x = y}) =
  ++[] (λ z → M⁰ (ψ₀ᵗ z) (ψs zero tt tt B zero self b nb y)) t
    (G⁰.m-zl (ψs zero tt tt B zero self b nb) (monos zero tt tt B zero self b nb) mb y)
Qu {t} B b nb mb (m1 {t = s} {x = y} e r) =
  G⁰.m-next (nzs zero tt tt B zero self b nb y) (cofψ1 u₀ (t ++ s) (cof++1 t s e))
    (λ n → trans (fsnψ1 u₀ (t ++ s) n (cof++1 t s e)) (cong (λ z → replicate n (ψ u₀ z)) (pred++ t s e)))
    (Qu B b nb mb r)
Qu {t} B b nb mb (mL {t = s} {x = y} e h) =
  mL (cofψω u₀ (t ++ s) (cof++ω t s e))
    (λ n → subst (λ z → M⁰ z (ψs zero tt tt B zero self b nb y))
      (sym (trans (fsnψω u₀ (t ++ s) n (cof++ω t s e)) (cong ψ₀ᵗ (fsn++ t s n e))))
      (Qu B b nb mb (h n)))
Qu B b nb mb (mΩ {p = ()} _ _ _)
Qu B b nb mb (mU {c = ()} _ _)
Qu B b nb mb (mw m d) = mw (Qu B b nb mb m) (monos zero tt tt B zero self b nb d)

Vu : ∀ {t} (B : Base zero) → M⁰ (ψ₀ᵗ t) (b⊥ B)
   → ∀ {s y} → M⁰ s y → M⁰ (ψ₀ᵗ (t ++ s)) (ψ⊥ zero tt tt B y)
Vu {t} B mb (mz {x = y}) =
  ++[] (λ z → M⁰ (ψ₀ᵗ z) (ψ⊥ zero tt tt B y)) t
    (G⁰.m-zl (ψ⊥ zero tt tt B) (mono⊥ zero tt tt B) mb y)
Vu {t} B mb (m1 {t = s} {x = y} e r) =
  G⁰.m-next (nz⊥ zero tt tt B y) (cofψ1 u₀ (t ++ s) (cof++1 t s e))
    (λ n → trans (fsnψ1 u₀ (t ++ s) n (cof++1 t s e)) (cong (λ z → replicate n (ψ u₀ z)) (pred++ t s e)))
    (Vu B mb r)
Vu {t} B mb (mL {t = s} {x = y} e h) =
  mL (cofψω u₀ (t ++ s) (cof++ω t s e))
    (λ n → subst (λ z → M⁰ z (ψ⊥ zero tt tt B y))
      (sym (trans (fsnψω u₀ (t ++ s) n (cof++ω t s e)) (cong ψ₀ᵗ (fsn++ t s n e))))
      (Vu B mb (h n)))
Vu B mb (mΩ {p = ()} _ _ _)
Vu B mb (mU {c = ()} _ _)
Vu B mb (mw m d) = mw (Vu B mb m) (mono⊥ zero tt tt B d)

Ω₁ᵗ Ω₂ᵗ t₂ : E.T
Ω₁ᵗ = E.Ωt u₁
Ω₂ᵗ = E.Ωs u₁
t₂ = ψ₀ᵗ Ω₂ᵗ

module At (B₂ : Base two)
  (hβ : M¹ Ω₁ᵗ (bs B₂ one (ins self)))
  (h0 : M⁰ (𝟏 ∷ []) (bs B₂ zero (ins (ins self))))
  (h⊥ : M⁰ (𝟏 ∷ []) (b⊥ B₂)) where

  Bᵃ : Base one
  Bᵃ = dS one tt tt B₂ zero

  β₁ : Tr one
  β₁ = bs B₂ one (ins self)

  nβ₁ : one ⊢ zero ◃ β₁
  nβ₁ = ns B₂ one (ins self)

  β₀ : Tr zero
  β₀ = bs B₂ zero (ins (ins self))

  nβ₀ : zero ⊢ zero ◃ β₀
  nβ₀ = ns B₂ zero (ins (ins self))

  F : Tr one → Tr one
  F x = ψs one tt tt Bᵃ one self β₁ nβ₁ x

  nzF : (x : Tr one) → one ⊢ zero ◃ F x
  nzF x = nzs one tt tt Bᵃ one self β₁ nβ₁ x

  H : Tr one → Tr zero
  H x = ψs one tt tt Bᵃ zero (ins self) β₀ nβ₀ x

  nzH : (x : Tr one) → zero ⊢ zero ◃ H x
  nzH x = nzs one tt tt Bᵃ zero (ins self) β₀ nβ₀ x

  W : Tr one → Tr zero
  W x = ψ⊥ one tt tt Bᵃ x

  nzW : (x : Tr one) → zero ⊢ zero ◃ W x
  nzW x = nz⊥ one tt tt Bᵃ x

  PF : ∀ {a x} → M¹ a x → M¹ (ψ₁ᵗ a) (F x)
  PF (mz {x = x}) = G¹.m-zl F (monos one tt tt Bᵃ one self β₁ nβ₁) hβ x
  PF (m1 {t = a} {x = x} e r) =
    G¹.m-next (nzF x) (cofψ1 u₁ a e) (λ n → fsnψ1 u₁ a n e) (PF r)
  PF (mL {t = a} {x = x} e h) =
    mL (cofψω u₁ a e) (λ n → subst (λ z → M¹ z (F x)) (sym (fsnψω u₁ a n e)) (PF (h n)))
  PF (mΩ {t = a} {p = inj₁ tt} {g = g} e refl h) =
    mΩ (cofψΩ u₁ a e) refl
      (λ η c l → subst (λ z → M¹ z (F (g c))) (sym (fsTψΩ u₁ a η e)) (PF (h η c l)))
  PF (mΩ {p = inj₂ ()} _ _ _)
  PF (mU {x = x} m ch) = Pu (F x) (nzF x) (PF m) ch
  PF (mw m d) = mw (PF m) (monos one tt tt Bᵃ one self β₁ nβ₁ d)

  vch : (Tr zero → Tr one) → ℕ → Tr zero
  vch g = iter (λ z → H (g z)) zero

  mutual
    QH : ∀ {a x} → M¹ a x → M⁰ (ψ₀ᵗ a) (H x)
    QH (mz {x = x}) = G⁰.m-zl H (monos one tt tt Bᵃ zero (ins self) β₀ nβ₀) h0 x
    QH (m1 {t = a} {x = x} e r) =
      G⁰.m-next (nzH x) (cofψ1 u₀ a e) (λ n → fsnψ1 u₀ a n e) (QH r)
    QH (mL {t = a} {x = x} e h) =
      mL (cofψω u₀ a e) (λ n → subst (λ z → M⁰ z (H x)) (sym (fsnψω u₀ a n e)) (QH (h n)))
    QH (mΩ {t = a} {p = inj₁ tt} {g = g} e refl h) =
      mL (cofψΩ u₀ a e)
        (λ n → subst (λ z → M⁰ z (H (Ω (inj₁ tt) g))) (sym (fsnψΩ u₀ a n e))
          (G⁰.m-cum (λ m → H (g (vch g m))) (λ m → nzH (g (vch g m))) (suc n)
            (QH (h (γT a [] n) (vch g (suc n)) (chain h n)))))
    QH (mΩ {p = inj₂ ()} _ _ _)
    QH (mU {x = x} m ch) = Qu (dS zero tt tt Bᵃ x) (H x) (nzH x) (QH m) ch
    QH (mw m d) = mw (QH m) (monos one tt tt Bᵃ zero (ins self) β₀ nβ₀ d)

    chain : ∀ {a} {g : Tr zero → Tr one} → (∀ η c → M⁰ η c → M¹ (fsT a η) (g c))
          → ∀ n → M⁰ (γT a [] n) (vch g (suc n))
    chain {g = g} h zero    = pos⁰ (H (g zero)) (nzH (g zero))
    chain h (suc n) = QH (h _ _ (chain h n))

  VW : ∀ {a x} → M¹ a x → M⁰ (ψ₀ᵗ a) (W x)
  VW (mz {x = x}) = G⁰.m-zl W (mono⊥ one tt tt Bᵃ) h⊥ x
  VW (m1 {t = a} {x = x} e r) =
    G⁰.m-next (nzW x) (cofψ1 u₀ a e) (λ n → fsnψ1 u₀ a n e) (VW r)
  VW (mL {t = a} {x = x} e h) =
    mL (cofψω u₀ a e) (λ n → subst (λ z → M⁰ z (W x)) (sym (fsnψω u₀ a n e)) (VW (h n)))
  VW (mΩ {t = a} {p = inj₁ tt} {g = g} e refl h) =
    mL (cofψΩ u₀ a e)
      (λ n → subst (λ z → M⁰ z (W (Ω (inj₁ tt) g))) (sym (fsnψΩ u₀ a n e))
        (G⁰.m-cum (λ m → W (g (vch g m))) (λ m → nzW (g (vch g m))) (suc n)
          (VW (h (γT a [] n) (vch g (suc n)) (chain h n)))))
  VW (mΩ {p = inj₂ ()} _ _ _)
  VW (mU {x = x} m ch) = Vu (dS zero tt tt Bᵃ x) (VW m) ch
  VW (mw m d) = mw (VW m) (mono⊥ one tt tt Bᵃ d)

  γ : ℕ → E.T
  γ = γT Ω₂ᵗ u₁

  z : ℕ → Tr one
  z = iter (λ c → next (F c) (nzF c)) zero

  form : ψ⊥ two tt tt B₂ (Ωt two)
       ≡ limc (λ k → next (W (z k)) (nzW (z k))) (λ k → nz⊥ two tt tt B₂ (up zero tt (suc (z k)) (z◃s (z k))))
  form = refl

  sγ : ∀ n → M¹ (γ n) (z (suc n))
  sγ zero    = mw hβ (◃l zero)
  sγ (suc n) = mw (PF (sγ n)) (◃l zero)

  lowerM : M⁰ t₂ (ψ⊥ two tt tt B₂ (Ωt two))
  lowerM = mL refl (λ n →
    G⁰.m-cum (λ k → next (W (z k)) (nzW (z k))) (λ k → nz⊥ two tt tt B₂ (up zero tt (suc (z k)) (z◃s (z k)))) (suc n)
      (mw (VW (sγ n)) (◃l zero)))

Mβ₀ : M¹ Ω₁ᵗ (Ωt one)
Mβ₀ = mΩ refl refl (λ η c l → mU mz (mw l ◃s))

bho-M : M⁰ t₂ (ψ₀ two tt tt (Ωt two))
bho-M = At.lowerM (B₀ two) Mβ₀ (m1 refl mz) (m1 refl mz)

bho-lowerᴹ : (h : HC t₂) → Rt h ≼ read (ψ₀ two tt tt (Ωt two))
bho-lowerᴹ h = lower⁰ bho-M h

nf₂ : NF t₂
nf₂ = nf-ψ n[] (nf-Ω (nf-rep (nψ n[] n[] GB[]) 2)) g
  where
  g : GB [] Ω₂ᵗ Ω₂ᵗ
  g (gp (gh _)) = E.[]<
  g (gp (gw _ (gp (gh _)))) = E.[]<
  g (gp (gw _ (gp (gw _ ()))))
  g (gp (gw _ (gp (gc _ ()))))
  g (gp (gw _ (gtl (gp (gh _))))) = E.[]<
  g (gp (gw _ (gtl (gp (gw _ ())))))
  g (gp (gw _ (gtl (gp (gc _ ())))))
  g (gp (gw _ (gtl (gtl ()))))
  g (gp (gc _ ()))
  g (gtl ())

h₂ : HC t₂
h₂ = hc nf₂ (c∷ c[])
```
