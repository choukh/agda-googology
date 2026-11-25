# 有限读回层号的沿帧状态与主引理
验收文件；编译定理：St/nxt/thru 的执行等式，统一关系族 J 与 M 的转换，MS 与 lower。
来源：YiLSFold 的状态机制；结点算式据 YiTBFam.LFΩ/chain 重写，低层递归经本文件 MS，不调用旧 LF、LFΩ、chain。
仅有限层号；未声称 NoΩ 全域主引理或 Need。实际孩子与既有结果对照见 YiFPChosen。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFPFinite where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; node⁺)
import OCF.Lean.YiTBRow as TB
open import OCF.Lean.YiCLFam using (fn; FD; fd0; fds; dn; M; Mβ; mwN; lev; levP; Lw⁼; LwP; Pu)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth; pos⁼; PV; pv; view; levEq; toLw; zlJ; nextJ; mLJ; cumJ; mΩP; ΩJ; penJ; gtJ)
open import OCF.Lean.YiRBFam using (Pt; can; pu; pt; Tp; tc; tu; tp; GB; mkGB; gΩ; gM; kcaseT; OKB)
import OCF.Lean.YiTBFam as Old
open import OCF.Lean.YiKVRel using (M⁰; mz; m1; mL; mΩ; mU; mw; _⊴_; ⊴r; ⊴◃; ++[])
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; γT; natT)

Cfg : ℕ → Set
Cfg n = Ok (fn n) × TB.Rb (fn n) × Base (fn n)
data St : ℕ → ℕ → Set where
  fo : ∀ {j n} → Cfg n → Pt n j → Tr⁺ (fn j) → St j n
  uf : ∀ {j n} → FD (suc j) n → Tr⁺ (fn (suc j)) → St (suc j) n
run⁺ : ∀ {j n} → St j n → Tr (fn n) → Tr⁺ (fn j)
run⁺ {j} {n} (fo (o , r , B) w β) x = TB.ψ (fn n) o r B (fn j) (pt w) β x
run⁺ {j} {n} (uf d b) x = Up (fn n) (dn d) b x
run : ∀ {j n} → St j n → Tr (fn n) → Tr (fn j)
run s x = proj₁ (run⁺ s x)
cb : ∀ {n} → Cfg (suc n) → Tr (fn (suc n)) → Cfg n
cb {n} (o , r , B) x = proj₂ o tt , proj₂ r tt , λ i u → TB.ψ (fn (suc n)) o r B i (inc tt u) (B i (inc tt u)) x
nxt : ∀ {j n} → St j (suc n) → Tr (fn (suc n)) → St j n
nxt s@(fo C (can s0) β) x = uf (fds fd0) (run⁺ s x)
nxt s@(fo C (can (ss w)) β) x = fo (cb C x) (can w) (run⁺ s x)
nxt s@(fo C (pu w) β) x = fo (cb C x) w (run⁺ s x)
nxt s@(uf d b) x = uf (fds d) (run⁺ s x)
thru : ∀ {j n k} → Pt n k → St j n → St j k
thru (can s0) s = s
thru (can (ss w)) s = thru (can w) (nxt s zero)
thru (pu w) s = thru w (nxt s zero)
run-up : ∀ {j n} (s : St j (suc n)) (x : Tr (fn (suc n))) (y : Tr⁺ (fn n))
  → run s (up x tt (proj₁ y) (proj₂ y)) ≡ run (nxt s x) (proj₁ y)
run-up (fo C (can s0) β) x y = refl
run-up (fo C (can (ss w)) β) x y = refl
run-up (fo C (pu w) β) x y = refl
run-up (uf d b) x y = refl
run-thru : ∀ {j n k} (C : Cfg n) (w : Pt n k) (s : St j n) (y : Tr⁺ (fn k))
  → run s (proj₁ (emb (fn n) (proj₁ C) (pt w) y)) ≡ run (thru w s) (proj₁ y)
run-thru C (can s0) s y = refl
run-thru C (can (ss w)) s y = trans (run-up s zero (emb _ (proj₂ (proj₁ C) tt) (pt (can w)) y)) (run-thru (cb C zero) (can w) (nxt s zero) y)
run-thru C (pu w) s y = trans (run-up s zero (emb _ (proj₂ (proj₁ C) tt) (pt w) y)) (run-thru (cb C zero) w (nxt s zero) y)

caseP : ∀ {n j} → Tp n j → Pt (suc n) j
caseP (tc w) = can (ss w)
caseP (tu w) = pu w

GBase : ∀ n → Base (fn n) → E.T → Set
GBase zero B t = ⊤
GBase (suc n) B t = GB n B t
OKS : ∀ {j n} → St j n → E.T → Set
OKS {j} {n} (fo (o , r , B) w β) t = GBase n B t × M j (ψᴺ j t) (proj₁ β)
OKS {suc j} (uf d b) t = M (suc j) (ψᴺ (suc j) t) (proj₁ b)

data J : (n : ℕ) → E.T → Tr (fn n) → Set where
  jz : ∀ {n x} → J n [] x
  j1 : ∀ {n t x} → cof t ≡ c1 → J n (pred t) x → J n t (suc x)
  jL : ∀ {n t x} → cof t ≡ cω → (∀ k → J n (fsn t k) x) → J n t x
  jΩ : ∀ {n t ν p g} → cof t ≡ cΩ ν → ν ≡ natT (levP (suc n) p)
    → (∀ η c → LwP (suc n) p η c → J (suc n) (fsT t η) (g c)) → J (suc n) t (Ω p g)
  jU : ∀ {n t s x y e} → J (suc n) t x → J n s y → J (suc n) (t ++ s) (up x tt y e)
  jw : ∀ {n t x y} → J n t x → fn n ⊢ x ◃ y → J n t y

erase : ∀ {n a x} → J n a x → M n a x
erase {n = zero} jz = mz
erase {n = suc n} jz = mz
erase {n = zero} (j1 e m) = m1 e (erase m)
erase {n = suc n} (j1 e m) = m1 e (erase m)
erase {n = zero} (jL e h) = mL e (λ k → erase (h k))
erase {n = suc n} (jL e h) = mL e (λ k → erase (h k))
erase (jΩ e nu h) = mΩ e nu (λ η c l → erase (h η c l))
erase (jU m ch) = mU (erase m) (erase ch)
erase {n = zero} (jw m e) = mw (erase m) e
erase {n = suc n} (jw m e) = mw (erase m) e

enter0 : ∀ {a x} → M zero a x → J zero a x
enter0 mz = jz
enter0 (m1 e m) = j1 e (enter0 m)
enter0 (mL e h) = jL e (λ k → enter0 (h k))
enter0 (mΩ {p = ()} _ _ _)
enter0 (mU {c = ()} _ _)
enter0 (mw m e) = jw (enter0 m) e
enterS : ∀ n → (∀ {a x} → M n a x → J n a x) → ∀ {a x} → M (suc n) a x → J (suc n) a x
enterS n rec mz = jz
enterS n rec (m1 e m) = j1 e (enterS n rec m)
enterS n rec (mL e h) = jL e (λ k → enterS n rec (h k))
enterS n rec (mΩ e nu h) = jΩ e nu (λ η c l → enterS n rec (h η c l))
enterS n rec (mU m ch) = jU (enterS n rec m) (rec ch)
enterS n rec (mw m e) = jw (enterS n rec m) e
enter : ∀ n {a x} → M n a x → J n a x
enter zero = enter0
enter (suc n) = enterS n (enter n)

mutual
  MS : ∀ {j n} (s : St j n) (t : E.T) → OKS s t → ∀ {a x}
    → J n a x → M j (ψᴺ j (t ++ a)) (run s x)
  MS {j = zero} {n = zero} (fo (o , r , B) (can s0) β) t (gb , hb) m = Old.Qu o r B self β hb (erase m)
  MS {j = suc j} {n = suc .j} (fo (o , r , B) (can s0) β) t (gb , hb) m = Old.Self.PF j o r B β hb (erase m)
  MS (fo C (can (ss w)) β) t ok m = ML C (tc w) t β ok m
  MS (fo C (pu w) β) t ok m = ML C (tu w) t β ok m
  MS {j = suc j} (uf d b) t hb m = Pu _ d b hb (erase m)

  ML : ∀ {n j} (C : Cfg (suc n)) (w : Tp n j) (t : E.T) (β : Tr⁺ (fn j))
    → OKS (fo C (caseP w) β) t → ∀ {a x} → J (suc n) a x
    → M j (ψᴺ j (t ++ a)) (proj₁ (TB.ψ (fn (suc n)) (proj₁ C) (proj₁ (proj₂ C)) (proj₂ (proj₂ C)) (fn j) (tp w) β x))
  ML {n} {j} (o , r , B) w t β (gb , hb) (jz {x = x}) =
    ++[] (λ q → M j (ψᴺ j q) (proj₁ (TB.ψ (fn (suc n)) o r B (fn j) (tp w) β x))) t
      (zlJ j (λ x → proj₁ (TB.ψ (fn (suc n)) o r B (fn j) (tp w) β x))
        (TB.mono (fn (suc n)) o r B (fn j) (tp w) β) hb x)
  ML {n} {j} (o , r , B) w t β ok (j1 {t = a} {x = x} e m) =
    nextJ j (TB.ψ (fn (suc n)) o r B (fn j) (tp w) β x) (cofψ1 (natT j) (t ++ a) (cof++1 t a e))
      (λ k → trans (fsnψ1 (natT j) (t ++ a) k (cof++1 t a e)) (cong (λ q → replicate k (E.ψ (natT j) q)) (pred++ t a e)))
      (ML (o , r , B) w t β ok m)
  ML {n} {j} (o , r , B) w t β ok (jL {t = a} {x = x} e h) =
    mLJ j (cofψω (natT j) (t ++ a) (cof++ω t a e))
      (λ k → subst (λ q → M j q (proj₁ (TB.ψ (fn (suc n)) o r B (fn j) (tp w) β x)))
        (sym (trans (fsnψω (natT j) (t ++ a) k (cof++ω t a e)) (cong (ψᴺ j) (fsn++ t a k e))))
        (ML (o , r , B) w t β ok (h k)))
  ML {n} C w t β ok (jΩ {p = inj₂ (tt , p)} e nu h) = NODE (proj₁ C) (proj₁ (proj₂ C)) w t (proj₂ (proj₂ C)) (proj₁ ok) β (proj₂ ok) p (view n p) e nu h
  ML {n} {j} C (tc w) t β ok (jU {t = a} {s = a′} {x = x} {y = y} {e = e} m ch) =
    subst (λ q → M j (ψᴺ j q) (run (fo C (caseP (tc w)) β) (up x tt y e))) (++-assoc t a a′)
      (subst (M j (ψᴺ j ((t ++ a) ++ a′))) (sym (run-up (fo C (caseP (tc w)) β) x (y , e)))
        (MS (nxt (fo C (caseP (tc w)) β) x) (t ++ a) (ok-next (fo C (caseP (tc w)) β) t ok m) ch))
  ML {n} {j} C (tu w) t β ok (jU {t = a} {s = a′} {x = x} {y = y} {e = e} m ch) =
    subst (λ q → M j (ψᴺ j q) (run (fo C (caseP (tu w)) β) (up x tt y e))) (++-assoc t a a′)
      (subst (M j (ψᴺ j ((t ++ a) ++ a′))) (sym (run-up (fo C (caseP (tu w)) β) x (y , e)))
        (MS (nxt (fo C (caseP (tu w)) β) x) (t ++ a) (ok-next (fo C (caseP (tu w)) β) t ok m) ch))
  ML {n} {j} (o , r , B) w t β ok (jw m e) =
    mwN j (ML (o , r , B) w t β ok m) (TB.mono (fn (suc n)) o r B (fn j) (tp w) β e)

  ok-next : ∀ {j n} (s : St j (suc n)) t → OKS s t → ∀ {a x} → J (suc n) a x → OKS (nxt s x) (t ++ a)
  ok-next s@(fo C (can s0) β) t ok m = MS s t ok m
  ok-next {n = zero} s@(fo C (can (ss w)) β) t ok m = tt , MS s t ok m
  ok-next {n = suc n} s@(fo C (can (ss w)) β) t (gb , hb) m = next-base C t gb m , MS s t (gb , hb) m
  ok-next {n = zero} s@(fo C (pu w) β) t ok m = tt , MS s t ok m
  ok-next {n = suc n} s@(fo C (pu w) β) t (gb , hb) m = next-base C t gb m , MS s t (gb , hb) m
  ok-next s@(uf d b) t hb m = MS s t hb m

  next-base : ∀ {n} (C : Cfg (suc (suc n))) t → GB (suc n) (proj₂ (proj₂ C)) t
    → ∀ {a x} → J (suc (suc n)) a x → GB n (proj₂ (proj₂ (cb C x))) (t ++ a)
  next-base {n} C@(o , r , B) t gb {x = x} m = mkGB
    (λ si → ⊴-trans (gΩ gb (ss si)) (Old.ψ-⊵ (fn (suc (suc n))) o r B _ (inc tt (inc tt (pth si))) (B _ (inc tt (inc tt (pth si)))) x))
    (λ si → MS (fo C (can (ss (ss si))) (B _ (inc tt (inc tt (pth si))))) t (gb , gM gb (ss si)) m)

  NODE : ∀ {n j} (o : Ok (fn (suc n))) (r : TB.Rb (fn (suc n))) (s : Tp n j) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀
      → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
      → (t : Pos⁼ (fn n)) → PV n t → ∀ {a ν} {g : Br⁼ (fn n) t → Tr (fn (suc n))} → cof a ≡ cΩ ν → ν ≡ natT (lev n t)
      → (∀ η c → Lw⁼ n t η c → J (suc n) (fsT a η) (g c))
      → M j (ψᴺ j (t₀ ++ a)) (proj₁ (TB.ψ (fn (suc n)) o r B (fn j) (tp s) β (Ω (inj₂ (tt , t)) g)))
  NODE {n = n} {j = j} o r s t₀ B gb β hβ .(pos⁼ si) (pv {i} si) {a} {ν} {g} e nu h =
    kcaseT o si s
      (λ K → M j (ψᴺ j (t₀ ++ a))
               (proj₁ (node⁺ K (λ z → TB.ψ (fn (suc n)) o r B (fn j) (tp s) β (g z)) (Old.feedF o r B (pos⁼ si) g))))
      (λ le → mLJ j (cofG (natT j) (t₀ ++ a) (gtJ le eqν) (cof++Ω t₀ a e))
        (λ k → subst (λ q → M j q (proj₁ (limc⁺ (λ m → TB.ψ (fn (suc n)) o r B (fn j) (tp s) β
                                                     (g (iter (Old.feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) m))))))
          (sym (trans (fsnG (natT j) (t₀ ++ a) k (gtJ le eqν) (cof++Ω t₀ a e))
                      (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
          (cumJ j (λ m → TB.ψ (fn (suc n)) o r B (fn j) (tp s) β
                           (g (iter (Old.feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) m))) (suc k)
            (ML (o , r , B) s t₀ β (gb , hβ) (h (γT (t₀ ++ a) ν k) (iter (Old.feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))
                                     (CHAIN o r si t₀ B gb e eqν h k))))))
      (λ q cv eq lq lw →
        mΩP j (cofK (natT j) (t₀ ++ a) (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (nuq lq)
          (λ η c l → subst (λ q′ → M j q′ (proj₁ (TB.ψ (fn (suc n)) o r B (fn j) (tp s) β (g (cv c)))))
            (sym (trans (fsTK (natT j) (t₀ ++ a) η (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a η e))))
            (ML (o , r , B) s t₀ β (gb , hβ) (h η (cv c) (lw η c l)))))
    where
    eqν : ν ≡ natT i
    eqν = trans nu (cong natT (levEq si))
    nuq : ∀ {q : Pos (fn j)} → levP j q ≡ i → ν ≡ natT (levP j q)
    nuq lq = trans eqν (cong natT (sym lq))

  CHAIN : ∀ {n i} (o : Ok (fn (suc n))) (r : TB.Rb (fn (suc n))) (si : Sb n i) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀
        → ∀ {a ν} {g : Br⁼ (fn n) (pos⁼ si) → Tr (fn (suc n))} → cof a ≡ cΩ ν → ν ≡ natT i
        → (∀ η c → Lw⁼ n (pos⁼ si) η c → J (suc n) (fsT a η) (g c))
        → ∀ k → Lw⁼ n (pos⁼ si) (γT (t₀ ++ a) ν k) (iter (Old.feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))
  CHAIN {n = n} {i = i} o r si t₀ B gb {a} {g = g} e refl h zero =
    subst (Lw⁼ n (pos⁼ si) (Ωᴺ i)) (sym (Old.feed≡ o r B si g (bz⁼ (fn n) (pos⁼ si))))
      (toLw si (ΩJ i (TB.ψ (fn (suc n)) o r B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si))) (g (bz⁼ (fn n) (pos⁼ si))))
        (⊴-trans (gΩ gb si)
          (Old.ψ-⊵ (fn (suc n)) o r B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si))) (g (bz⁼ (fn n) (pos⁼ si)))))))
  CHAIN {n = n} {i = i} o r si t₀ B gb {a} {g = g} e refl h (suc k) =
    subst (Lw⁼ n (pos⁼ si) (ψᴺ i (fsT (t₀ ++ a) (γT (t₀ ++ a) (natT i) k))))
      (sym (Old.feed≡ o r B si g (iter (Old.feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))))
      (toLw si (subst (λ q → M i (ψᴺ i q)
                   (proj₁ (TB.ψ (fn (suc n)) o r B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si)))
                             (g (iter (Old.feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))))))
        (sym (fsT++ t₀ a (γT (t₀ ++ a) (natT i) k) e))
        (ML (o , r , B) (tc si) t₀ (B (fn i) (inc tt (pth si))) (gb , gM gb si)
          (h (γT (t₀ ++ a) (natT i) k) (iter (Old.feedF o r B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k)) (CHAIN o r si t₀ B gb e refl h k)))))

START : ∀ n → J (suc n) (Ωᴺ (suc n)) (proj₁ (Ωt (fn (suc n))))
START n = enter (suc n) (Mβ n)
lower : ∀ {n j} (C : Cfg (suc n)) (w : Tp n j) (β : Tr⁺ (fn j))
  → OKB (proj₂ (proj₂ C)) → M j (Ωᴺ j) (proj₁ β)
  → M j (ψᴺ j (Ωᴺ (suc n))) (run (fo C (caseP w) β) (proj₁ (Ωt (fn (suc n)))))
lower {n} {j} C@(o , r , B) w β ok hb = MS (fo C (caseP w) β) []
  (mkGB (λ si → ok _ (inc tt (pth si))) (λ si → ΩJ _ (B _ (inc tt (pth si))) (ok _ (inc tt (pth si)))) , hb)
  (START n)


import OCF.Lean.YiKVRel as K
import OCF.Align.Value as V
import OCF.Lean.YiRefTw2
VS : ∀ {n} (st : St 0 n) t → OKS st t → ∀ {a x} → J n a x
  → (h : E.HC (ψᴺ 0 (t ++ a))) → OCF.Lean.YiRefTw2.Rt h V.≼ K.readRW (run st x)
VS st t ok m h = K.lower⁰ (MS st t ok m) h
```
