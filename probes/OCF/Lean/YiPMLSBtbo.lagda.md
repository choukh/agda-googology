# 按表参数化: LSBtbo

参数化（工程），数学内容与 `YiVTLSBtbo` 的保持及下降证明相同；验收文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMLSBtbo where

open import OCF.Lean.YiPMTable using (Table)

module F (tb : Table) where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Unit using (⊤; tt)
  open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  open import OCF.Lean.YiLegBlock renaming (L to LF)
  open import OCF.Lean.YiLegOps
  open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here; emb)
  import OCF.Lean.YiPMFold
  open OCF.Lean.YiPMFold.F tb
  open import OCF.Lean.YiLSRead
  import OCF.Lean.YiPMLSFold
  open OCF.Lean.YiPMLSFold.F tb using (ψs-⊵)
  import OCF.Lean.YiPMLSTw1
  open OCF.Lean.YiPMLSTw1.F tb

  import OCF.Align.Level as L
  open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ⊑→≼; ≼l; l≼)
  open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
  module S = Ord-Ord
  module B = BoundedTrich
  open S using (ordᴰ)
  open import OCF.Align.BTBOValBase using (tr₀)
  open import OCF.Align.BTBOValNeg using (add-≺)
  open import OCF.Align.BTBOFullQ using (<ᴰ-irrefl; clash-lt)
  open import OCF.Align.BTBOFullEb using (module Blocks; Inv; inl; inr; inv)
  open import OCF.Align.BTBOFullV3 using (𝕋₀; bkᴵ; ≺→⊑₀; add-left)
  open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
  open import OCF.Align.BTBOFullLv using (SV-L)
  open import OCF.Align.BTBOFull using (St-bk; bk≅γ)
  open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
  open import OCF.Align.YiMonoEmb using (PEmb-∘; PEmb-⊑)
  open import OCF.Align.YiBtValBT using (module D)
  import OCF.Align.NoCumsum as N
  open import OCF.Lean.YiBtboV2 using (Mono; mz; ms; ml; V2′)
  import OCF.Lean.YiPEStep as PS

  module WT = Blocks 𝕋₀

  cp : Tr zero → S.Ord₀
  cp zero          = S.zero
  cp (suc a)       = S.suc (cp a)
  cp (lim f _)     = S.lim (λ n → cp (f n))
  cp (Ω () _)
  cp (up _ () _ _)

  cp≅ : (x : Tr zero) → tr₀ (cp x) L.≅ read x
  cp≅ zero          = L.z≅
  cp≅ (suc a)       = L.s≅ (cp≅ a)
  cp≅ (lim f _)     = L.l≅ (λ n → cp≅ (f n))
  cp≅ (Ω () _)
  cp≅ (up _ () _ _)

  Mono-cp : (x : Tr zero) → Mono (tr₀ (cp x))
  Mono-cp zero          = mz
  Mono-cp (suc a)       = ms (Mono-cp a)
  Mono-cp (lim f a)     = ml (λ n → Mono-cp (f n))
    (λ n → ≼-trans (≅→≼ (cp≅ (f n)))
      (≼-trans (⊑→≼ (read (f n)) (◃⊑ (a n))) (≅→≼ (L.≅-sym (cp≅ (f (suc n)))))))
  Mono-cp (Ω () _)
  Mono-cp (up _ () _ _)

  lift≺ : ∀ {a b : T₀} → a L.≺ b → ∀ {x : T₀} → x L.≺ L.suc a → x L.≺ b
  lift≺ ab (L.≺z e) = L.≺-respˡ (L.≅-sym e) ab
  lift≺ ab (L.≺s h) = ≺→⊑₀ ab h

  OKs : (ℓ : LF) → Base ℓ → Set
  OKs ℓ Bb = (j : LF) (w : j ≤ ℓ) → j ⊢ Ωt j ⊴ bs Bb j w

  mono⊥⊑ : (ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (Bb : Base ℓ) {x y : Tr ℓ} → ℓ ⊢ x ⊴ y
    → read (ψ⊥ ℓ ε ρ Bb x) L.⊑ read (ψ⊥ ℓ ε ρ Bb y)
  mono⊥⊑ ℓ ε ρ Bb ⊴r     h = h
  mono⊥⊑ ℓ ε ρ Bb (⊴◃ d) h = ◃⊑ (mono⊥ ℓ ε ρ Bb d) h

  b◃next : (b : Tr zero) (nb : zero ⊢ zero ◃ b) → zero ⊢ b ◃ next b nb
  b◃next b nb = ◃t (+-mono b nb) (◃l 1)

  V3 : (x : Tr zero) (ε : Ev (h₁ x)) (ρ : Rt (h₁ x)) (Bb : Base (h₁ x)) → OKs (h₁ x) Bb
    → Σ (WT.Eb (ordᴰ (cp x)) (read (ψ⊥ (h₁ x) ε ρ Bb (Ωt (h₁ x)))))
        (λ e → ∀ {c} (p : c B.< ordᴰ (cp x)) → read (b⊥ Bb) L.≺ WT.map e p)
  V3 zero ε ρ Bb ok = WT.Eb-zero , λ ()
  V3 (suc a) ε ρ Bb ok = WT.Eb-suc eS (read top) (λ h → h) (◃→≺ lt-tree) , nzS
    where
    ℓa = h₁ a
    B′ : Base ℓa
    B′ = dS ℓa ε ρ Bb zero
    β = bs Bb ℓa (ins self)
    nβ = ns Bb ℓa (ins self)
    F0 X top : Tr zero
    F0 = ψ⊥ ℓa ε ρ B′ (suc zero)
    X = ψ⊥ ℓa ε ρ B′ β
    top = F0 + X
    lt-tree : zero ⊢ top ◃ ψ⊥ (suc ℓa) ε ρ Bb (Ωt (suc ℓa))
    lt-tree = ◃t (+-mono F0 (mono⊥ ℓa ε ρ B′ {x = β} {y = suc (next β nβ)} (◃t (◃l zero) ◃s))) (◃l 1)
    ih = V3 a ε ρ B′ (λ j w → ok j (ins w))
    e′ = proj₁ ih
    eS : WT.Eb (ordᴰ (cp a)) (read top)
    eS = record
      { map   = λ p → read F0 L.+ WT.map e′ p
      ; below = λ p → L.≺-respʳ (add-≺ (read F0) (mono⊥⊑ ℓa ε ρ B′ (ok ℓa (ins self)) (WT.below e′ p)))
                        (L.≅-sym (read-+ F0 X))
      ; mono  = λ p q r → add-≺ (read F0) (WT.mono e′ p q r)
      ; coh   = λ p q r → L.add-≅ (L.≅-refl⁰ (read F0)) (WT.coh e′ p q r) }
    b◃F0 : zero ⊢ b⊥ Bb ◃ F0
    b◃F0 = b◃next (b⊥ Bb) (n⊥ Bb)
    nzS : ∀ {c} (p : c B.< B.suc (ordᴰ (cp a)))
      → read (b⊥ Bb) L.≺ WT.map (WT.Eb-suc eS (read top) (λ h → h) (◃→≺ lt-tree)) p
    nzS B.zero    = ◃→≺ (◃t b◃F0 (+-mono F0 (nz⊥ ℓa ε ρ B′ β)))
    nzS (B.suc p) = add-left (◃→≺ b◃F0) _
  V3 (lim f a) ε (ρc , R) Bb ok = BL.Lim , nzL
    where
    g : ℕ → LF
    g n = h₁ (f n)
    ρ : Rt (lim g)
    ρ = ρc , R
    O : ℕ → B.Ordᴰ
    O n = ordᴰ (cp (f n))
    En : ℕ → Tr zero
    En n = ψ⊥ (lim g) ε ρ Bb (cumΩ g n)
    pre : ℕ → Tr zero
    pre zero    = b⊥ Bb
    pre (suc n) = En n
    stepE : ∀ n → zero ⊢ En n ◃ En (suc n)
    stepE n = mono⊥ (lim g) ε ρ Bb (◃u (cumΩ g n) (suc n) (Ωt (g (suc n))) (Ωt-nz (g (suc n))))
    pre◃ : ∀ n → zero ⊢ b⊥ Bb ◃ En n
    pre◃ zero    = mono⊥ (lim g) ε ρ Bb (◃u zero zero (Ωt (g zero)) (Ωt-nz (g zero)))
    pre◃ (suc n) = ◃t (pre◃ n) (stepE n)
    eN : ∀ n → Σ (WT.Eb (O n) (read (En n))) (λ e → ∀ {c} (p : c B.< O n) → read (pre n) L.≺ WT.map e p)
    eN zero    = V3 (f zero) (ε zero) (ρc zero) (dL g ε ρ Bb zero zero)
      (λ j w → ⊴-trans (ok j (inl zero w)) (ψs-⊵ (lim g) ε ρ Bb j (inl zero w) (bs Bb j (inl zero w)) (ns Bb j (inl zero w)) zero))
    eN (suc n) = V3 (f (suc n)) (ε (suc n)) (ρc (suc n)) (dL g ε ρ Bb (suc n) (cumΩ g n))
      (λ j w → ⊴-trans (ok j (inl (suc n) w)) (ψs-⊵ (lim g) ε ρ Bb j (inl (suc n) w) (bs Bb j (inl (suc n) w)) (ns Bb j (inl (suc n) w)) (cumΩ g n)))
    T∞ : T₀
    T∞ = read (ψ⊥ (lim g) ε ρ Bb (Ωt (lim g)))
    Bd : ℕ → T₀
    Bd zero    = read (En zero)
    Bd (suc n) = L.suc (read (En (suc n)))
    N′ : ∀ n {d} → d B.< B.suc (O (suc n)) → T₀
    N′ n B.zero    = read (En (suc n))
    N′ n (B.suc p) = WT.map (proj₁ (eN (suc n))) p
    Nb : ∀ n {d} (p : d B.< B.suc (O (suc n))) → N′ n p L.≺ Bd (suc n)
    Nb n B.zero    = L.≺z (L.≅-refl⁰ (read (En (suc n))))
    Nb n (B.suc p) = L.≺s (WT.below (proj₁ (eN (suc n))) p)
    Nm : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O (suc n))) (q : d₂ B.< B.suc (O (suc n))) → d₁ B.< d₂ → N′ n p L.≺ N′ n q
    Nm n B.zero    B.zero    r = ⊥-elim (<ᴰ-irrefl r)
    Nm n B.zero    (B.suc q) r = ⊥-elim (clash-lt r q)
    Nm n (B.suc p) B.zero    r = WT.below (proj₁ (eN (suc n))) p
    Nm n (B.suc p) (B.suc q) r = WT.mono (proj₁ (eN (suc n))) p q r
    Nc : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O (suc n))) (q : d₂ B.< B.suc (O (suc n))) → d₁ ≡ d₂ → N′ n p L.≅ N′ n q
    Nc n B.zero    B.zero    r = L.≅-refl⁰ _
    Nc n B.zero    (B.suc q) refl = ⊥-elim (<ᴰ-irrefl q)
    Nc n (B.suc p) B.zero    refl = ⊥-elim (<ᴰ-irrefl p)
    Nc n (B.suc p) (B.suc q) r = WT.coh (proj₁ (eN (suc n))) p q r
    fl : ∀ n {x} → x L.≺ Bd n → ∀ {d} (p : d B.< B.suc (O (suc n))) → x L.≺ N′ n p
    fl zero    h B.zero    = ≺→⊑₀ (◃→≺ (stepE zero)) h
    fl zero    h (B.suc p) = ≺→⊑₀ (proj₂ (eN (suc zero)) p) h
    fl (suc n) h B.zero    = lift≺ (◃→≺ (stepE (suc n))) h
    fl (suc n) h (B.suc p) = lift≺ (proj₂ (eN (suc (suc n))) p) h
    sp : ∀ n {x} → x L.≺ Bd n → x L.≺ T∞
    sp zero    h = L.≺l 0 h
    sp (suc n) h = L.≺l (suc (suc n)) (lift≺ (◃→≺ (stepE (suc n))) h)
    module BL = WT.Blk O Bd T∞ (proj₁ (eN zero)) N′ Nb Nm Nc fl sp
    nzN : ∀ n {d} (p : d B.< B.suc (O (suc n))) → read (b⊥ Bb) L.≺ N′ n p
    nzN n B.zero    = ◃→≺ (pre◃ (suc n))
    nzN n (B.suc p) = ≺→⊑₀ (proj₂ (eN (suc n)) p) (◃→≺ (pre◃ n))
    nzD : ∀ n {c} (m₀ : ∀ {c′} → c′ B.< BL.Σs n → T₀) → (∀ {c′} (q : c′ B.< BL.Σs n) → read (b⊥ Bb) L.≺ m₀ q)
      → (i : Inv (BL.Σs n) (B.suc (O (suc n))) c) → read (b⊥ Bb) L.≺ BL.disp n m₀ i
    nzD n m₀ h (inl q)     = h q
    nzD n m₀ h (inr d r e) = nzN n r
    nzE : ∀ n {c} (p : c B.< BL.Σs n) → read (b⊥ Bb) L.≺ WT.map (BL.En n) p
    nzE zero    p = proj₂ (eN zero) p
    nzE (suc n) p = nzD n (WT.map (BL.En n)) (nzE n) (inv {BL.Σs n} {B.suc (O (suc n))} p)
    nzL : ∀ {c} (p : c B.< ordᴰ (cp (lim f a))) → read (b⊥ Bb) L.≺ WT.map BL.Lim p
    nzL (B.lim n p) = nzE n p
  V3 (Ω () _) ε ρ Bb ok
  V3 (up _ () _ _) ε ρ Bb ok

  V3F : ∀ m → WT.Eb (ordᴰ (cp (pt m))) (read (G (pt m)))
  V3F m = proj₁ (V3 (pt m) (εh (pt m)) (ρh (pt m)) (B₀ (h₁ (pt m))) (λ j w → ⊴r))

  shift : ∀ x → PEmb (L.toLevel (read (G x)) (HSr (G x))) (lvl (K x))
  shift x = PS.PEmb-≅ʳ (PEmb-⊑ L.⊑ᴵ-refl)
    (L.toLevel-≅ (HSr (G x)) (HSr (K x)) (L.≅-sym (KG x)))

  emb : ∀ n m → D.γ n ≼ read (pt m) → PEmb (D.L n) (κ (suc m))
  emb n m w =
    PEmb-∘ (PW₃ (V1 (SV-L n)))
    (PEmb-∘ (PW₁ (V2′ (bkᴵ (N.L n)) (cp η) (St-bk (SV-L n)) (Mono-cp η) w′))
    (PEmb-∘ (PW₂ (HSr (G η)) (V3F m))
            (shift η)))
    where
    η = pt m
    w′ : tr₀ (bkᴵ (N.L n)) ≼ tr₀ (cp η)
    w′ = ≼-trans (≅→≼ (bk≅γ n)) (≼-trans w (≅→≼ (L.≅-sym (cp≅ η))))

  lowc : ∀ k → L.ψ⁰ (L.Ω (κ k)) ≼ read (pt (suc k))
  lowc k = ≼-trans (LOWER k) (≅→≼ (L.≅-sym (KG (pt k))))

  chainV : ∀ n → Σ ℕ (λ m → D.γ n ≼ read (pt m))
  chainV zero    = 1 , ≼l 0 (≼-refl (L.suc L.zero))
  chainV (suc n) = suc (suc (proj₁ (chainV n))) ,
    ≼-trans (Ψ-emb (emb n (proj₁ (chainV n)) (proj₂ (chainV n)))) (lowc (suc (proj₁ (chainV n))))

  btbo-tw1 : D.BTBOᴵ ≼ read (twᶜ 1)
  btbo-tw1 = l≼ (λ n → ≼-trans (Ψ-emb (emb n (proj₁ (chainV n)) (proj₂ (chainV n))))
    (limcum≽ (λ k → G (pt k)) (λ k → G-nz (pt k)) (suc (proj₁ (chainV n))) (LOWER (suc (proj₁ (chainV n))))))
```
