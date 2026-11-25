# 验收一侧 (兄弟孩子折叠): 遗传封闭的关系族上折到自身与折到低层的保持

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 量化域是层号 `fn n`, 证据任意. 关系族是 [YiHCFam](YiHCFam.lagda.md) 的 `M` (遗传封闭).
> `Qu`, `Self.PF`, `kcase`, `LF`, `chain`, `sΩ-LF`, `liftC`, `liftU`: 陈述与 `YiRBFam` 的同名定理逐字相同, 只是 `M` 换成封闭后的族.
> 来源: 证明照 `YiRBFam` 逐行搬来, `Qu`, `PF`, `LF` 各加 `mc` 一行 (`YiDCRel.app≤`), 其余各行不改; 路径 (`Pt`, `Tp`), `feedF`, `cb`, `OKB`, `ψ-⊵` 与关系无关, 直接引用 `YiRBFam`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHCFold where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; kp⁼; node⁺)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃; ⊴-◃; ++[])
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (M⁰; mz; m1; mL; mΩ; mU; mw; mc; module G⁰)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; γT; natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; Pen; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiCLFam using (nat; fn; lev; levP; Nw; penN; FD; fd0; fds; dn; ≤ⁿ-step; ≤ⁿ-refl)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth; sb≤; pos⁼; PV; pv; view; levEq; toBr; gen; penJ; gtJ)
open import OCF.Lean.YiRBFam using (Pt; can; pu; pt; pt≤; Tp; tc; tu; tp; ψ-⊵; feedF; feed≡; cb; OKB)
open import OCF.Lean.YiHCFam
```

## 第 0 层的折叠

```agda
Qu : ∀ {t} (o0 : Ok zero) (r0 : Rb zero) (B0 : Base zero) (w : zero ≤ zero) (b : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ b)
   → ∀ {s y} → M⁰ s y → M⁰ (ψᴺ 0 (t ++ s)) (proj₁ (ψ zero o0 r0 B0 zero w b y))
Qu {t} o0 r0 B0 w b mb (mz {x = y}) =
  ++[] (λ z → M⁰ (ψᴺ 0 z) (proj₁ (ψ zero o0 r0 B0 zero w b y))) t
    (G⁰.m-zl (λ y → proj₁ (ψ zero o0 r0 B0 zero w b y)) (mono zero o0 r0 B0 zero w b) mb y)
Qu {t} o0 r0 B0 w b mb (m1 {t = s} {x = y} e r) =
  G⁰.m-next (ψ zero o0 r0 B0 zero w b y) (cofψ1 (natT 0) (t ++ s) (cof++1 t s e))
    (λ n → trans (fsnψ1 (natT 0) (t ++ s) n (cof++1 t s e)) (cong (λ z → replicate n (E.ψ (natT 0) z)) (pred++ t s e)))
    (Qu o0 r0 B0 w b mb r)
Qu {t} o0 r0 B0 w b mb (mL {t = s} {x = y} e h) =
  mL (cofψω (natT 0) (t ++ s) (cof++ω t s e))
    (λ n → subst (λ z → M⁰ z (proj₁ (ψ zero o0 r0 B0 zero w b y)))
      (sym (trans (fsnψω (natT 0) (t ++ s) n (cof++ω t s e)) (cong (ψᴺ 0) (fsn++ t s n e))))
      (Qu o0 r0 B0 w b mb (h n)))
Qu o0 r0 B0 w b mb (mΩ {p = ()} _ _ _)
Qu o0 r0 B0 w b mb (mU {c = ()} _ _)
Qu o0 r0 B0 w b mb (mw m d) = mw (Qu o0 r0 B0 w b mb m) (mono zero o0 r0 B0 zero w b d)
Qu {t} o0 r0 B0 w b mb (mc le m) = mc (app≤ 0 t le) (Qu o0 r0 B0 w b mb m)
```

## 折到自身, 带前缀

```agda
module Self (N : ℕ) (o : Ok (fn (suc N))) (r : Rb (fn (suc N))) (B : Base (fn (suc N))) (β : Tr⁺ (fn (suc N))) where

  F⁺ : Tr (fn (suc N)) → Tr⁺ (fn (suc N))
  F⁺ x = ψ (fn (suc N)) o r B (fn (suc N)) self β x

  F : Tr (fn (suc N)) → Tr (fn (suc N))
  F x = proj₁ (F⁺ x)

  monoF : {x y : Tr (fn (suc N))} → fn (suc N) ⊢ x ◃ y → fn (suc N) ⊢ F x ◃ F y
  monoF = mono (fn (suc N)) o r B (fn (suc N)) self β

  PF : ∀ {P₀} → M (suc N) (ψᴺ (suc N) P₀) (proj₁ β) → ∀ {a x} → M (suc N) a x → M (suc N) (ψᴺ (suc N) (P₀ ++ a)) (F x)
  PF {P₀} hP (mz {x = x}) = ++[] (λ r → M (suc N) (ψᴺ (suc N) r) (F x)) P₀ (GM.m-zl N F monoF hP x)
  PF {P₀} hP (m1 {t = a} {x = x} e r) =
    GM.m-next N (F⁺ x) (cofψ1 (natT (suc N)) (P₀ ++ a) (cof++1 P₀ a e))
      (λ k → trans (fsnψ1 (natT (suc N)) (P₀ ++ a) k (cof++1 P₀ a e))
               (cong (λ r → replicate k (E.ψ (natT (suc N)) r)) (pred++ P₀ a e)))
      (PF hP r)
  PF {P₀} hP (mL {t = a} {x = x} e h) =
    mL (cofψω (natT (suc N)) (P₀ ++ a) (cof++ω P₀ a e))
      (λ k → subst (λ r → M (suc N) r (F x))
        (sym (trans (fsnψω (natT (suc N)) (P₀ ++ a) k (cof++ω P₀ a e)) (cong (ψᴺ (suc N)) (fsn++ P₀ a k e))))
        (PF hP (h k)))
  PF {P₀} hP (mΩ {t = a} {p = p} {g = g} e nu h) =
    mΩ (cofK (natT (suc N)) (P₀ ++ a) (penN N p nu) (cof++Ω P₀ a e)) nu
      (λ η c l → subst (λ r → M (suc N) r (F (g c)))
        (sym (trans (fsTK (natT (suc N)) (P₀ ++ a) η (penN N p nu) (cof++Ω P₀ a e))
               (cong (ψᴺ (suc N)) (fsT++ P₀ a η e))))
        (PF hP (h η c l)))
  PF {P₀} hP (mU {t = s₀} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ r → M (suc N) (ψᴺ (suc N) r) (proj₁ (Up (fn N) (dn (fds fd0)) (F⁺ x) y))) (++-assoc P₀ s₀ s₁)
      (Pu N (fds fd0) (F⁺ x) (PF hP m) ch)
  PF hP (mw m d) = mw (PF hP m) (monoF d)
  PF {P₀} hP (mc le m) = mc (app≤ (suc N) P₀ le) (PF hP m)
```

## 保留判定

槽位 `pos⁼ si` (层号 i) 朝目标 `fn j`: j ≤ i 时不保留; 否则保留. `inu` 一步与 `inc` 一步同样下行.

```agda
kcase : ∀ {n i j} (o : Ok (fn n)) (si : Sb n i) (s : Pt n j) (Q : Keep (fn j) (Br⁼ (fn n) (pos⁼ si)) (bz⁼ (fn n) (pos⁼ si)) → Set)
      → (j ≤ⁿ i → Q nothing)
      → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ (fn n) (pos⁼ si)) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ (fn n) (pos⁼ si))
           → levP j q ≡ i → (∀ η c → LwP j q η c → Lw⁼ n (pos⁼ si) η (cv c)) → Q (just (q , cv , eq)))
      → Q (kp⁼ (fn n) o (pos⁼ si) (pt s))
kcase o s0      s             Q dr kc = dr (pt≤ s)
kcase o (ss si) (can s0)      Q dr kc = kc (inj₂ (tt , pos⁼ si)) (λ z → z) refl (levEq si) (λ η c l → l)
kcase o (ss si) (can (ss s))  Q dr kc = kcase (proj₂ o tt) si (can s) Q dr kc
kcase o (ss si) (pu s)        Q dr kc = kcase (proj₂ o tt) si s Q dr kc

kcaseT : ∀ {n i j} (o : Ok (fn (suc n))) (si : Sb n i) (s : Tp n j)
           (Q : Keep (fn j) (Br⁼ (fn n) (pos⁼ si)) (bz⁼ (fn n) (pos⁼ si)) → Set)
       → (j ≤ⁿ i → Q nothing)
       → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ (fn n) (pos⁼ si)) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ (fn n) (pos⁼ si))
            → levP j q ≡ i → (∀ η c → LwP j q η c → Lw⁼ n (pos⁼ si) η (cv c)) → Q (just (q , cv , eq)))
       → Q (kp (fn (suc n)) o (inj₂ (tt , pos⁼ si)) (tp s))
kcaseT o si (tc s) Q dr kc = kcase (proj₂ o tt) si (can s) Q dr kc
kcaseT o si (tu s) Q dr kc = kcase (proj₂ o tt) si s Q dr kc
```

## 底的条件, 回灌的函数

```agda
record GB (n : ℕ) (B : Base (fn (suc n))) (t₀ : E.T) : Set where
  constructor mkGB
  field
    gΩ : ∀ {i} (si : Sb n i) → proj₁ (Ωt (fn i)) ⊴ proj₁ (B (fn i) (inc tt (pth si)))
    gM : ∀ {i} (si : Sb n i) → M i (ψᴺ i t₀) (proj₁ (B (fn i) (inc tt (pth si))))
open GB public
```

## 折到低层

```agda
mutual
  LF : ∀ {n j} (o : Ok (fn (suc n))) (r : Rb (fn (suc n))) (s : Tp n j) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀
     → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
     → ∀ {a x} → M (suc n) a x
     → M j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ (fn (suc n)) o r B (fn j) (tp s) β x))
  LF {n = n} {j = j} o r s t₀ B gb β hβ (mz {x = x}) =
    ++[] (λ q → M j (ψᴺ j q) (proj₁ (ψ (fn (suc n)) o r B (fn j) (tp s) β x))) t₀
      (zlJ j (λ x → proj₁ (ψ (fn (suc n)) o r B (fn j) (tp s) β x))
        (mono (fn (suc n)) o r B (fn j) (tp s) β) hβ x)
  LF {n = n} {j = j} o r s t₀ B gb β hβ (m1 {t = a} {x = x} e d) =
    nextJ j (ψ (fn (suc n)) o r B (fn j) (tp s) β x) (cofψ1 (natT j) (t₀ ++ a) (cof++1 t₀ a e))
      (λ k → trans (fsnψ1 (natT j) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ q → replicate k (E.ψ (natT j) q)) (pred++ t₀ a e)))
      (LF o r s t₀ B gb β hβ d)
  LF {n = n} {j = j} o r s t₀ B gb β hβ (mL {t = a} {x = x} e h) =
    mLJ j (cofψω (natT j) (t₀ ++ a) (cof++ω t₀ a e))
      (λ k → subst (λ q → M j q (proj₁ (ψ (fn (suc n)) o r B (fn j) (tp s) β x)))
        (sym (trans (fsnψω (natT j) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ j) (fsn++ t₀ a k e))))
        (LF o r s t₀ B gb β hβ (h k)))
  LF {n = n} o r s t₀ B gb β hβ (mΩ {p = inj₂ (tt , t)} e nu h) = LFΩ o r s t₀ B gb β hβ t (view n t) e nu h
  LF {n = zero} o r (tc s0) t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ q → M⁰ (ψᴺ 0 q) (proj₁ (ψ zero (proj₂ o tt) (proj₂ r tt) (cb o r B x) zero self
                                        (ψ (fn 1) o r B zero (inc tt self) β x) y)))
      (++-assoc t₀ a s₁)
      (Qu (proj₂ o tt) (proj₂ r tt) (cb o r B x) self (ψ (fn 1) o r B zero (inc tt self) β x)
        (LF o r (tc s0) t₀ B gb β hβ m) ch)
  LF {n = zero} o r (tu (can s0)) t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ q → M⁰ (ψᴺ 0 q) (proj₁ (ψ zero (proj₂ o tt) (proj₂ r tt) (cb o r B x) zero self
                                        (ψ (fn 1) o r B zero (inu (λ _ → self)) β x) y)))
      (++-assoc t₀ a s₁)
      (Qu (proj₂ o tt) (proj₂ r tt) (cb o r B x) self (ψ (fn 1) o r B zero (inu (λ _ → self)) β x)
        (LF o r (tu (can s0)) t₀ B gb β hβ m) ch)
  LF {n = suc n} o r (tc s0) t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ q → M (suc n) (ψᴺ (suc n) q)
        (Self.F n (proj₂ o tt) (proj₂ r tt) (cb o r B x) (ψ (fn (suc (suc n))) o r B (fn (suc n)) (inc tt self) β x) y))
      (++-assoc t₀ a s₁)
      (Self.PF n (proj₂ o tt) (proj₂ r tt) (cb o r B x) (ψ (fn (suc (suc n))) o r B (fn (suc n)) (inc tt self) β x)
                 (LF o r (tc s0) t₀ B gb β hβ m) ch)
  LF {n = suc n} o r (tu (can s0)) t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ q → M (suc n) (ψᴺ (suc n) q)
        (Self.F n (proj₂ o tt) (proj₂ r tt) (cb o r B x) (ψ (fn (suc (suc n))) o r B (fn (suc n)) (inu (λ _ → self)) β x) y))
      (++-assoc t₀ a s₁)
      (Self.PF n (proj₂ o tt) (proj₂ r tt) (cb o r B x) (ψ (fn (suc (suc n))) o r B (fn (suc n)) (inu (λ _ → self)) β x)
                 (LF o r (tu (can s0)) t₀ B gb β hβ m) ch)
  LF {n = suc n} {j = j} o r (tc (ss s)) t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ q → M j (ψᴺ j q)
        (proj₁ (ψ (fn (suc n)) (proj₂ o tt) (proj₂ r tt) (cb o r B x) (fn j) (inc tt (pth s))
                  (ψ (fn (suc (suc n))) o r B (fn j) (inc tt (inc tt (pth s))) β x) y)))
      (++-assoc t₀ a s₁)
      (LF (proj₂ o tt) (proj₂ r tt) (tc s) (t₀ ++ a) (cb o r B x) (gbS o r t₀ B gb m)
        (ψ (fn (suc (suc n))) o r B (fn j) (inc tt (inc tt (pth s))) β x)
        (LF o r (tc (ss s)) t₀ B gb β hβ m) ch)
  LF {n = suc n} {j = j} o r (tu (can (ss s))) t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ q → M j (ψᴺ j q)
        (proj₁ (ψ (fn (suc n)) (proj₂ o tt) (proj₂ r tt) (cb o r B x) (fn j) (inc tt (pth s))
                  (ψ (fn (suc (suc n))) o r B (fn j) (inu (λ _ → inc tt (pth s))) β x) y)))
      (++-assoc t₀ a s₁)
      (LF (proj₂ o tt) (proj₂ r tt) (tc s) (t₀ ++ a) (cb o r B x) (gbS o r t₀ B gb m)
        (ψ (fn (suc (suc n))) o r B (fn j) (inu (λ _ → inc tt (pth s))) β x)
        (LF o r (tu (can (ss s))) t₀ B gb β hβ m) ch)
  LF {n = suc n} {j = j} o r (tu (pu s)) t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ q → M j (ψᴺ j q)
        (proj₁ (ψ (fn (suc n)) (proj₂ o tt) (proj₂ r tt) (cb o r B x) (fn j) (inu (λ _ → pt s))
                  (ψ (fn (suc (suc n))) o r B (fn j) (inu (λ _ → inu (λ _ → pt s))) β x) y)))
      (++-assoc t₀ a s₁)
      (LF (proj₂ o tt) (proj₂ r tt) (tu s) (t₀ ++ a) (cb o r B x) (gbS o r t₀ B gb m)
        (ψ (fn (suc (suc n))) o r B (fn j) (inu (λ _ → inu (λ _ → pt s))) β x)
        (LF o r (tu (pu s)) t₀ B gb β hβ m) ch)
  LF {n = n} {j = j} o r s t₀ B gb β hβ (mw m d) =
    mwN j (LF o r s t₀ B gb β hβ m) (mono (fn (suc n)) o r B (fn j) (tp s) β d)
  LF {j = j} o r s t₀ B gb β hβ (mc le m) = mcJ j (app≤ j t₀ le) (LF o r s t₀ B gb β hβ m)

  gbS : ∀ {n} (o : Ok (fn (suc (suc n)))) (r : Rb (fn (suc (suc n)))) (t₀ : E.T) (B : Base (fn (suc (suc n)))) → GB (suc n) B t₀
      → ∀ {a x} → M (suc (suc n)) a x → GB n (cb o r B x) (t₀ ++ a)
  gbS {n = n} o r t₀ B gb {x = x} m =
    mkGB (λ {i} si → ⊴-trans (gΩ gb (ss si))
            (ψ-⊵ (fn (suc (suc n))) o r B (fn i) (inc tt (inc tt (pth si))) (B (fn i) (inc tt (inc tt (pth si)))) x))
         (λ {i} si → LF o r (tc (ss si)) t₀ B gb (B (fn i) (inc tt (inc tt (pth si)))) (gM gb (ss si)) m)

  LFΩ : ∀ {n j} (o : Ok (fn (suc n))) (r : Rb (fn (suc n))) (s : Tp n j) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀
      → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
      → (t : Pos⁼ (fn n)) → PV n t → ∀ {a ν} {g : Br⁼ (fn n) t → Tr (fn (suc n))} → cof a ≡ cΩ ν → ν ≡ natT (lev n t)
      → (∀ η c → Lw⁼ n t η c → M (suc n) (fsT a η) (g c))
      → M j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ (fn (suc n)) o r B (fn j) (tp s) β (Ω (inj₂ (tt , t)) g)))
  LFΩ {n = n} {j = j} o r s t₀ B gb β hβ .(pos⁼ si) (pv {i} si) {a} {ν} {g} e nu h =
    kcaseT o si s
      (λ K → M j (ψᴺ j (t₀ ++ a))
               (proj₁ (node⁺ K (λ z → ψ (fn (suc n)) o r B (fn j) (tp s) β (g z)) (feedF o r B (pos⁼ si) g))))
      (λ le → mLJ j (cofG (natT j) (t₀ ++ a) (gtJ le eqν) (cof++Ω t₀ a e))
        (λ k → subst (λ q → M j q (proj₁ (limc⁺ (λ m → ψ (fn (suc n)) o r B (fn j) (tp s) β
                                                     (g (iter (feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) m))))))
          (sym (trans (fsnG (natT j) (t₀ ++ a) k (gtJ le eqν) (cof++Ω t₀ a e))
                      (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
          (cumJ j (λ m → ψ (fn (suc n)) o r B (fn j) (tp s) β
                           (g (iter (feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) m))) (suc k)
            (LF o r s t₀ B gb β hβ (h (γT (t₀ ++ a) ν k) (iter (feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))
                                     (chain o r si t₀ B gb e eqν h k))))))
      (λ q cv eq lq lw →
        mΩP j (cofK (natT j) (t₀ ++ a) (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (nuq lq)
          (λ η c l → subst (λ q′ → M j q′ (proj₁ (ψ (fn (suc n)) o r B (fn j) (tp s) β (g (cv c)))))
            (sym (trans (fsTK (natT j) (t₀ ++ a) η (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a η e))))
            (LF o r s t₀ B gb β hβ (h η (cv c) (lw η c l)))))
    where
    eqν : ν ≡ natT i
    eqν = trans nu (cong natT (levEq si))
    nuq : ∀ {q : Pos (fn j)} → levP j q ≡ i → ν ≡ natT (levP j q)
    nuq lq = trans eqν (cong natT (sym lq))

  chain : ∀ {n i} (o : Ok (fn (suc n))) (r : Rb (fn (suc n))) (si : Sb n i) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀
        → ∀ {a ν} {g : Br⁼ (fn n) (pos⁼ si) → Tr (fn (suc n))} → cof a ≡ cΩ ν → ν ≡ natT i
        → (∀ η c → Lw⁼ n (pos⁼ si) η c → M (suc n) (fsT a η) (g c))
        → ∀ k → Lw⁼ n (pos⁼ si) (γT (t₀ ++ a) ν k) (iter (feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))
  chain {n = n} {i = i} o r si t₀ B gb {a} {g = g} e refl h zero =
    subst (Lw⁼ n (pos⁼ si) (Ωᴺ i)) (sym (feed≡ o r B si g (bz⁼ (fn n) (pos⁼ si))))
      (toLw si (ΩJ i (ψ (fn (suc n)) o r B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si))) (g (bz⁼ (fn n) (pos⁼ si))))
        (⊴-trans (gΩ gb si)
          (ψ-⊵ (fn (suc n)) o r B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si))) (g (bz⁼ (fn n) (pos⁼ si)))))))
  chain {n = n} {i = i} o r si t₀ B gb {a} {g = g} e refl h (suc k) =
    subst (Lw⁼ n (pos⁼ si) (ψᴺ i (fsT (t₀ ++ a) (γT (t₀ ++ a) (natT i) k))))
      (sym (feed≡ o r B si g (iter (feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))))
      (toLw si (subst (λ q → M i (ψᴺ i q)
                   (proj₁ (ψ (fn (suc n)) o r B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si)))
                             (g (iter (feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))))))
        (sym (fsT++ t₀ a (γT (t₀ ++ a) (natT i) k) e))
        (LF o r (tc si) t₀ B gb (B (fn i) (inc tt (pth si))) (gM gb si)
          (h (γT (t₀ ++ a) (natT i) k) (iter (feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k)) (chain o r si t₀ B gb e refl h k)))))
```

## Ω 树的折叠, 沿层号的后继上行

`OKB`: 底的各分量在 Ω 树之上. `SΩ t m j v`: 对一切这样的底与一切起点, t 对着层号 `fn m` 的 Ω 树沿 v 朝 `fn j` 的折叠.

```agda
SΩ : E.T → (m j : ℕ) → Ok (fn m) → Rb (fn m) → fn j ≤ fn m → Set
SΩ t m j o r v = (B : Base (fn m)) (β : Tr⁺ (fn j)) → OKB B → M j (Ωᴺ j) (proj₁ β)
               → M j t (proj₁ (ψ (fn m) o r B (fn j) v β (proj₁ (Ωt (fn m)))))

sΩ-LF : ∀ {n j} (o : Ok (fn (suc n))) (r : Rb (fn (suc n))) (s : Tp n j) → SΩ (ψᴺ j (Ωᴺ (suc n))) (suc n) j o r (tp s)
sΩ-LF {n} o r s B β ok hβ =
  LF o r s [] B (mkGB (λ {i} si → ok (fn i) (inc tt (pth si)))
                      (λ {i} si → ΩJ i (B (fn i) (inc tt (pth si))) (ok (fn i) (inc tt (pth si))))) β hβ (Mβ n)

module _ {t : E.T} {m j : ℕ} (o : Ok (fn (suc m))) (r : Rb (fn (suc m))) (v : fn j ≤ fn m) where
  private
    stepB : (B : Base (fn (suc m))) → OKB B → OKB (cb o r B zero)
    stepB B ok i u = ok i (inc tt u)

    z1 : (B : Base (fn (suc m))) → OKB B → fn m ⊢ proj₁ (Ωt (fn m)) ◃ proj₁ (next⁺ (B (fn m) (inc tt self)))
    z1 B ok = ⊴-◃ (ok (fn m) (inc tt self)) (◃l zero)

  liftC : SΩ t m j (proj₂ o tt) (proj₂ r tt) v → SΩ t (suc m) j o r (inc tt v)
  liftC s B β ok hβ =
    cumJ j (λ k → next⁺ (ψ (fn m) (proj₂ o tt) (proj₂ r tt) (cb o r B zero) (fn j) v β
                           (iter (λ z → proj₁ (next⁺ (ψ (fn m) (proj₂ o tt) (proj₂ r tt) (cb o r B zero) (fn m) self
                                                         (B (fn m) (inc tt self)) z))) zero k))) 1
      (mwN j (mwN j (s (cb o r B zero) β (stepB B ok) hβ)
                    (mono (fn m) (proj₂ o tt) (proj₂ r tt) (cb o r B zero) (fn j) v β (z1 B ok)))
             (◃l zero))

  liftU : SΩ t m j (proj₂ o tt) (proj₂ r tt) v → SΩ t (suc m) j o r (inu (λ _ → v))
  liftU s B β ok hβ =
    cumJ j (λ k → next⁺ (ψ (fn m) (proj₂ o tt) (proj₂ r tt) (cb o r B zero) (fn j) v β
                           (iter (λ z → proj₁ (next⁺ (ψ (fn m) (proj₂ o tt) (proj₂ r tt) (cb o r B zero) (fn m) self
                                                         (B (fn m) (inc tt self)) z))) zero k))) 1
      (mwN j (mwN j (s (cb o r B zero) β (stepB B ok) hβ)
                    (mono (fn m) (proj₂ o tt) (proj₂ r tt) (cb o r B zero) (fn j) v β (z1 B ok)))
             (◃l zero))
```
