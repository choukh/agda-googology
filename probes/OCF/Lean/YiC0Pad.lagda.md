# two 上的指定读回孩子族
验收文件；编译定理：该孩子族的低层对应与前驱嵌入 V3，未单独给出公共输出值界。
仅处理 neck 用到的 two 上方读回，不陈述一般跨层单调。
来源：V3 的归纳逐行平移 YiLSBtbo.V3；层号左加复用 YiPEStep。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC0Pad where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here; emb)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiLSFold using (NL; n0; n+; nω; OKB; ok-B₀; lower; ψs-⊵)
open import OCF.Lean.YiLSRel using (Corr; cz; cs; cl)
open import OCF.Lean.YiLSTw1 using (E; es; ez; eq0; LiftP-∙; E→≅)
open import OCF.Lean.YiLSBtbo using (cp; cp≅; Mono-cp; lift≺; mono⊥⊑; b◃next; OKs)
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
open import OCF.Lean.YiBtboV2 using (V2′)
import OCF.Lean.YiPEStep as PS
module WT = Blocks 𝕋₀
two₀ : LF
two₀ = suc (suc zero)
L₂ : L.Ordᴵ
L₂ = L.suc (L.suc L.zero)
h₁ : Tr zero → LF
h₁ x = two₀ ⊕ ↑ zero x
εh : (x : Tr zero) → Ev (h₁ x)
εh x = Ev⊕ two₀ (↑ zero x) tt (EvO↑ two₀ zero tt (ins (ins self)) x)
ρh : (x : Tr zero) → Rt (h₁ x)
ρh x = Rt⊕ two₀ (↑ zero x) tt (RtP↑ zero tt x)
nl-↑ : (x : Tr zero) → NL (h₁ x)
nl-↑ zero = n+ (n+ n0)
nl-↑ (suc x) = n+ (nl-↑ x)
nl-↑ (lim f a) = nω (λ n → nl-↑ (f n))
nl-↑ (Ω () _)
nl-↑ (up _ () _ _)
corr-↑ : (x : Tr zero) (h : L.HS (read x)) → Corr (PS._⊕_ L₂ (L.toLevel (read x) h)) (h₁ x)
corr-↑ zero h = cs (cs cz)
corr-↑ (suc x) h = cs (corr-↑ x (L.hs⁻ h))
corr-↑ (lim f a) h = cl (λ n → corr-↑ (f n) (L.hl₁ h n))
  (λ n → PS.⊕-≺ L₂ (L.toLevel-≺ (L.hl₁ h n) (L.hl₁ h (suc n)) (◃→≺ (a n))))
corr-↑ (Ω () _) h
corr-↑ (up _ () _ _) h
wh : (x : Tr zero) → zero ≤ h₁ x
wh x = ins (ins self) ∙ lift two₀ (↑ zero x)
lvl : Tr zero → L.Ordᴵ
lvl x = PS._⊕_ L₂ (L.toLevel (read x) (HSr x))

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

```
