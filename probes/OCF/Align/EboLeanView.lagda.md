# EboLeanView: 共尾度视图, 沿视图的基本列

> **记号侧验收工作**, 读记号, 不进成品. 逐字取自 [WfFsnView](WfFsnView.lagda.md): 共尾度视图 `VΩ` (Ω-共尾), `Vω` (ω-共尾); 沿视图的 `fΩ`, `fω`, `γ` 与记号的 `fsT`, `fsn`, `γT` 逐点相等 (`fΩ-eq`, `fω-eq`, `γ-eq`); 单调; $\mu$ 标准, $\mu+1<a$. **改动:** `fω-eq` 对 [EboLeanDef](EboLeanDef.lagda.md) 的裸值 `fsn` 证, 每支一个 `cong`, 不再经 EBO 的证书版本 (`fsn↓c-gt`, `fsT↓-trm`, `γ↓-trm`, `fsn₊-eq`, `fsn0-eq`, `rep-trm` 都不要). `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLeanView where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.EboLeanDef
open import OCF.Align.EBO using (pred-suc; <-sucT)
open import OCF.Align.EboLeanBase

fsTc-pen : ∀ u b ν m → Pen m → ∀ η → fsTc u b ν m η ≡ ψ u (fsT b η) ∷ []
fsTc-pen u b ν .lt (inj₁ refl) η = refl
fsTc-pen u b ν .eq (inj₂ refl) η = refl
data NE : T → Set where
  ne : ∀ {x xs} → NE (x ∷ xs)

data VΩ : T → T → Set where
  ωs : ∀ {x y ys μ} → VΩ (y ∷ ys) μ → VΩ (x ∷ y ∷ ys) μ
  ωr : ∀ {u} → cof u ≡ c1 → VΩ (ψ u [] ∷ []) (pred u)
  ωl : ∀ {u μ} → cof u ≡ cΩ μ → VΩ u μ → VΩ (ψ u [] ∷ []) μ
  ωp : ∀ {u b μ} → cof b ≡ cΩ μ → Pen (cmpᵀ (sucT μ) u) → VΩ b μ → VΩ (ψ u b ∷ []) μ

vΩ  : ∀ a {μ} → cof a ≡ cΩ μ → VΩ a μ
vΩ0 : ∀ u c → cof u ≡ c → ∀ {μ} → cofψ0 u c ≡ cΩ μ → VΩ (ψ u [] ∷ []) μ
vΩ₊ : ∀ u b c → cof b ≡ c → ∀ {μ} → cofA u c ≡ cΩ μ → VΩ (ψ u b ∷ []) μ
vΩc : ∀ u b ν → cof b ≡ cΩ ν → ∀ m → cmpᵀ (sucT ν) u ≡ m → ∀ {μ} → cofψ₊ u ν m ≡ cΩ μ →
      VΩ (ψ u b ∷ []) μ

vΩ [] ()
vΩ (x ∷ xs@(_ ∷ _)) e = ωs (vΩ xs e)
vΩ (ψ u b@(_ ∷ _) ∷ []) e = vΩ₊ u b (cof b) refl e
vΩ (ψ u@(_ ∷ _) [] ∷ []) e = vΩ0 u (cof u) refl e
vΩ (𝟏 ∷ []) ()

vΩ0 u c0 ue ()
vΩ0 u c1 ue refl = ωr ue
vΩ0 u cω ue ()
vΩ0 u (cΩ ν) ue refl = ωl ue (vΩ u ue)

vΩ₊ u b c0 be ()
vΩ₊ u b c1 be ()
vΩ₊ u b cω be ()
vΩ₊ u b (cΩ ν) be e = vΩc u b ν be (cmpᵀ (sucT ν) u) refl e

vΩc u b ν be lt m refl = ωp be (inj₁ m) (vΩ b be)
vΩc u b ν be eq m refl = ωp be (inj₂ m) (vΩ b be)
vΩc u b ν be gt m ()

fΩ : ∀ {a μ} → VΩ a μ → T → T
fΩ (ωs {x = x} v) η     = x ∷ fΩ v η
fΩ (ωr _) η             = η
fΩ (ωl _ v) η           = ψ (fΩ v η) [] ∷ []
fΩ (ωp {u = u} _ _ v) η = ψ u (fΩ v η) ∷ []

fΩ-eq : ∀ {a μ} (v : VΩ a μ) η → fsT a η ≡ fΩ v η
fΩ-eq (ωs {x = x} v) η = cong (x ∷_) (fΩ-eq v η)
fΩ-eq (ωr {u = []} ()) η
fΩ-eq (ωr {u = w ∷ ws} e) η = cong (λ c → fsT0 (w ∷ ws) c η) e
fΩ-eq (ωl {u = []} _ ()) η
fΩ-eq (ωl {u = w ∷ ws} e v) η =
  trans (cong (λ c → fsT0 (w ∷ ws) c η) e) (cong (λ z → ψ z [] ∷ []) (fΩ-eq v η))
fΩ-eq (ωp {b = []} () _ _) η
fΩ-eq (ωp {u = u} {b = y ∷ ys} {μ = μ} be pen v) η =
  trans (cong (λ c → fsT₊ u (y ∷ ys) c η) be)
    (trans (fsTc-pen u (y ∷ ys) μ (cmpᵀ (sucT μ) u) pen η) (cong (λ z → ψ u z ∷ []) (fΩ-eq v η)))

fΩ-mono : ∀ {a μ} (v : VΩ a μ) {η₁ η₂} → η₁ <ᵀ η₂ → fΩ v η₁ <ᵀ fΩ v η₂
fΩ-mono (ωs v) p     = tl< (fΩ-mono v p)
fΩ-mono (ωr _) p     = p
fΩ-mono (ωl _ v) p   = hd< (lv< (fΩ-mono v p))
fΩ-mono (ωp _ _ v) p = hd< (ar< (fΩ-mono v p))

fΩ-pos : ∀ {a μ} (v : VΩ a μ) {η} → [] <ᵀ η → [] <ᵀ fΩ v η
fΩ-pos (ωs v) p     = []<
fΩ-pos (ωr _) p     = p
fΩ-pos (ωl _ v) p   = []<
fΩ-pos (ωp _ _ v) p = []<

γ : ∀ {b ν} → VΩ b ν → ℕ → T
γ {ν = ν} w zero    = Ωt ν
γ {ν = ν} w (suc k) = ψ ν (fΩ w (γ w k)) ∷ []

γ-eq : ∀ {b ν} (w : VΩ b ν) k → γT b ν k ≡ γ w k
γ-eq w zero = refl
γ-eq {b} {ν} w (suc k) =
  cong (λ z → ψ ν z ∷ []) (trans (cong (fsT b) (γ-eq w k)) (fΩ-eq w (γ w k)))

γ< : ∀ {b ν} (w : VΩ b ν) k → γ w k <ᵀ Ωs ν
γ< {ν = ν} w zero    = hd< (lv< (<-sucT ν))
γ< {ν = ν} w (suc k) = hd< (lv< (<-sucT ν))

γ-mono : ∀ {b ν} (w : VΩ b ν) k → γ w k <ᵀ γ w (suc k)
γ-mono w zero    = hd< (ar< (fΩ-pos w []<))
γ-mono w (suc k) = hd< (ar< (fΩ-mono w (γ-mono w k)))

val-mono : ∀ {b ν} (w : VΩ b ν) k → fΩ w (γ w k) <ᵀ fΩ w (γ w (suc k))
val-mono w k = fΩ-mono w (γ-mono w k)

val-le0 : ∀ {b ν} (w : VΩ b ν) k → fΩ w (γ w zero) ≤ᵀ fΩ w (γ w k)
val-le0 w zero    = inj₂ refl
val-le0 w (suc k) = ≤-trans′ (val-le0 w k) (inj₁ (val-mono w k))

cof0  : ∀ b → NE b → cof b ≡ c0 → ⊥
cof0P : ∀ x → cofP x ≡ c0 → ⊥
cofA0 : ∀ u c → cofA u c ≡ c0 → ⊥
ψ0-0  : ∀ {u} c → cofψ0 u c ≡ c0 → c ≡ c0
cof0 (x ∷ []) ne e = cof0P x e
cof0 (x ∷ xs@(_ ∷ _)) ne e = cof0 xs ne e
cof0P (ψ u b@(_ ∷ _)) e = cofA0 u (cof b) e
cof0P (ψ u@(_ ∷ _) []) e = cof0 u ne (ψ0-0 (cof u) e)
cof0P (ψ [] []) ()
cofA0 u c0 ()
cofA0 u c1 ()
cofA0 u cω ()
cofA0 u (cΩ μ) e = go (cmpᵀ (sucT μ) u) e where
  go : ∀ m → cofψ₊ u μ m ≡ c0 → ⊥
  go lt ()
  go eq ()
  go gt ()
ψ0-0 c0 _ = refl
ψ0-0 c1 ()
ψ0-0 cω ()
ψ0-0 (cΩ _) ()

pen-ne : ∀ μ u → Pen (cmpᵀ (sucT μ) u) → NE u
pen-ne μ (_ ∷ _) _ = ne
pen-ne [] [] (inj₁ ())
pen-ne [] [] (inj₂ ())
pen-ne (_ ∷ _) [] (inj₁ ())
pen-ne (_ ∷ _) [] (inj₂ ())

reg-eq : ∀ {u} → cof u ≡ c1 → Ωs (pred u) ≡ ψ u [] ∷ []
reg-eq {u} e = cong (λ z → ψ z [] ∷ []) (pred-suc u e)

Ωs≤ : ∀ μ u → Pen (cmpᵀ (sucT μ) u) → Ωs μ ≤ᵀ (ψ u [] ∷ [])
Ωs≤ μ u pen with Pen→≤ (sucT μ) u pen
... | inj₁ p    = inj₁ (hd< (lv< p))
... | inj₂ refl = inj₂ refl

nf-ν : ∀ {a μ} → NF a → VΩ a μ → NF μ
nf-ν n (ωs v)     = nf-ν (nf-tl n) v
nf-ν n (ωr _)     = nf-pred (nfp-u (nf-hd n))
nf-ν n (ωl _ v)   = nf-ν (nfp-u (nf-hd n)) v
nf-ν n (ωp _ _ v) = nf-ν (nfp-a (nf-hd n)) v

dom< : ∀ {a μ} → NF a → VΩ a μ → sucT μ <ᵀ a
dom< n (ωs {x = x} {y} {ys} v) = <ᵀ-trans (dom< (nf-tl n) v) (tail< x (y ∷ ys) (nf-le n) (nf-tl n))
dom< n (ωr {u = u} e) = subst (λ z → z <ᵀ (ψ u [] ∷ [])) (sym (pred-suc u e)) (idx< u [] [])
dom< n (ωl {u = u} e v) = <ᵀ-trans (dom< (nfp-u (nf-hd n)) v) (idx< u [] [])
dom< n (ωp {u = u} {b} {μ} be pen v) = ≤-< (Pen→≤ (sucT μ) u pen) (idx< u b [])

data Vω : T → Set where
  ws : ∀ {x y ys} → Vω (y ∷ ys) → Vω (x ∷ y ∷ ys)
  wl : ∀ {u} → cof u ≡ cω → Vω u → Vω (ψ u [] ∷ [])
  w4 : ∀ {u b} → cof b ≡ c1 → Vω (ψ u b ∷ [])
  w5 : ∀ {u b} → cof b ≡ cω → Vω b → Vω (ψ u b ∷ [])
  w6 : ∀ {u b ν} → cof b ≡ cΩ ν → cmpᵀ (sucT ν) u ≡ gt → VΩ b ν → Vω (ψ u b ∷ [])

vω  : ∀ t → cof t ≡ cω → Vω t
vω0 : ∀ u c → cof u ≡ c → cofψ0 u c ≡ cω → Vω (ψ u [] ∷ [])
vω₊ : ∀ u b → NE b → ∀ c → cof b ≡ c → cofA u c ≡ cω → Vω (ψ u b ∷ [])
vωc : ∀ u b ν → cof b ≡ cΩ ν → ∀ m → cmpᵀ (sucT ν) u ≡ m → cofψ₊ u ν m ≡ cω → Vω (ψ u b ∷ [])

vω [] ()
vω (x ∷ xs@(_ ∷ _)) e = ws (vω xs e)
vω (ψ u b@(_ ∷ _) ∷ []) e = vω₊ u b ne (cof b) refl e
vω (ψ u@(_ ∷ _) [] ∷ []) e = vω0 u (cof u) refl e
vω (𝟏 ∷ []) ()

vω0 u c0 ue ()
vω0 u c1 ue ()
vω0 u cω ue _ = wl ue (vω u ue)
vω0 u (cΩ μ) ue ()

vω₊ u b nb c0 be _ = ⊥-elim (cof0 b nb be)
vω₊ u b nb c1 be _ = w4 be
vω₊ u b nb cω be _ = w5 be (vω b be)
vω₊ u b nb (cΩ ν) be e = vωc u b ν be (cmpᵀ (sucT ν) u) refl e

vωc u b ν be lt m ()
vωc u b ν be eq m ()
vωc u b ν be gt m _ = w6 be m (vΩ b be)

fω : ∀ {t} → Vω t → ℕ → T
fω (ws {x = x} v) n       = x ∷ fω v n
fω (wl _ v) n             = ψ (fω v n) [] ∷ []
fω (w4 {u = u} {b} _) n   = replicate n (ψ u (pred b))
fω (w5 {u = u} _ v) n     = ψ u (fω v n) ∷ []
fω (w6 {u = u} _ _ w) n   = ψ u (fΩ w (γ w n)) ∷ []

fω-eq : ∀ {t} (v : Vω t) n → fsn t n ≡ fω v n
fω-eq (ws {x = x} v) n = cong (x ∷_) (fω-eq v n)
fω-eq (wl {u = []} () v) n
fω-eq (wl {u = u@(_ ∷ _)} e v) n = trans (cong (λ c → fsn0 u c n) e) (cong (λ z → ψ z [] ∷ []) (fω-eq v n))
fω-eq (w4 {b = []} ()) n
fω-eq (w4 {u = u} {b = b@(_ ∷ _)} e) n = cong (λ c → fsn₊ u b c n) e
fω-eq (w5 {b = []} () v) n
fω-eq (w5 {u = u} {b = b@(_ ∷ _)} e v) n = trans (cong (λ c → fsn₊ u b c n) e) (cong (λ z → ψ u z ∷ []) (fω-eq v n))
fω-eq (w6 {b = []} () _ _) n
fω-eq (w6 {u = u} {b = b@(_ ∷ _)} {ν} be g w) n =
  trans (cong (λ c → fsn₊ u b c n) be)
    (trans (cong (λ m → fsnc u b ν m n) g)
      (cong (λ z → ψ u z ∷ []) (trans (cong (fsT b) (γ-eq w n)) (fΩ-eq w (γ w n)))))
```
