# 验收 (候选 A): `A1S` 在一切有限 η 处成立, A1 在一切有限 η 与 ω 处成立

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提: `a1s-fin` (`YiKCStep.A1S` 在 η = n+1 处, 对一切满足 `M⁰ n x` 的 x), `a1-fin` (孩子 two 的第 1 层底的第 c 支不低于 ψ₁(Ω_n), 对一切 n 与一切满足 `M⁰ n c` 的 c), `a1-ω` (同上, ψ₁(Ω_ω)).
> 工具: `ΦF` (锚在第 2 层、目标第 1 层的 `φ`, 源是层号 `fn (suc m)` 的树时对 ψ₁(t₀ + a) 的保持): 第 0 层的槽位保留, 其余走回灌链 (`YiCLLow.chain`).
> 不给出 η = ω+1 起的后继 (`A1S` 整条, `critS` 的前提) : 那里层号是 ℕ 极限形状之上的后继, 关系族没有做. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCLPhi where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiKVRel hiding (cof++Ω; fsT++)
open import OCF.Lean.YiKVCheck using (o¹; h₁; g₁)
open import OCF.Lean.YiKVInst using (a1-lim)
open import OCF.Lean.YiKCSem using (o2)
open import OCF.Lean.YiKCStep using (OKB; kk; S; S0; A1S)
open import OCF.Lean.YiKCFin using (c1≢cω; lift⊴; clos⊴; S1)
open import OCF.Lean.YiCertFold using (Base; B₀; Keep; node⁺)
import OCF.Align.EboLeanDef as E
open E using (cof; c0; c1; cω; cΩ; pred; fsn; fsT; γT; natT; sucT; cmpᵀ; gt; 𝟏)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofΩ; fsTΩ; Pen; cmp-gt; cofK; fsTK; cofG; fsnG; cof-nat; pred-nat)
open import OCF.Lean.YiCLFam hiding (Pu)
open import OCF.Lean.YiCLLow
```

## `φ` 的保留判定

源层 `fn m` 的证书 `abf m` 是 `o¹` 在孩子 `nat m` 处的证书. 槽位落在地板 (第 0 层) 上时推进锚层后保留, 否则不保留.

```agda
abf : (m : ℕ) → Ab zero (fn m)
abf m = crt o¹ (nat m)

kcaseΦ : ∀ {m i} (si : Sb m i) (Q : Keep one (Br⁼ (fn m) (pos⁼ si)) (bz⁼ (fn m) (pos⁼ si)) → Set)
       → (1 ≤ⁿ i → Q nothing)
       → ((cv : Tr zero → Br⁼ (fn m) (pos⁼ si)) (eq : cv zero ≡ bz⁼ (fn m) (pos⁼ si))
            → i ≡ 0 → (∀ η c → M⁰ η c → Lw⁼ m (pos⁼ si) η (cv c)) → Q (just (q1 , cv , eq)))
       → Q (kpA two o2 kk (inc tt self) (abf m) (pos⁼ si))
kcaseΦ {m = zero}  s0      Q dr kc = kc _ _ refl (λ η c l → l)
kcaseΦ {m = suc m} s0      Q dr kc = dr (s≤s z≤n)
kcaseΦ {m = suc m} (ss si) Q dr kc = kcaseΦ si Q dr kc

pen1 : ∀ {i ν} → i ≡ 0 → ν ≡ natT i → Pen (cmpᵀ (sucT ν) u₁)
pen1 refl refl = inj₂ refl

nu1 : ∀ {i ν} → i ≡ 0 → ν ≡ natT i → ν ≡ []
nu1 refl e = e
```

## `φ` 对 ψ₁(t₀ + a) 的保持

```agda
module Fin (Ba : Base two) where
  φF : (m : ℕ) → Base (fn m) → Tr⁺ one → Tr (fn m) → Tr⁺ one
  φF m Bm β y = φ two o2 Ba kk one (inc tt self) (fn m) (okf m) (abf m) Bm β y

  ΦF⁰ : (t₀ : E.T) (Bm : Base zero) (β : Tr⁺ one) → M¹ (ψ₁ᵗ t₀) (proj₁ β)
      → ∀ {s y} → M⁰ s y → M¹ (ψ₁ᵗ (t₀ ++ s)) (proj₁ (φF 0 Bm β y))
  ΦF⁰ t₀ Bm β hβ ch = Pu β hβ (G⁰.m-right (suc zero) ch)

  mutual
    ΦF : ∀ m (t₀ : E.T) (Bm : Base (fn (suc m))) → GB m Bm t₀ → (β : Tr⁺ one) → M¹ (ψ₁ᵗ t₀) (proj₁ β)
       → ∀ {a x} → M (suc m) a x → M¹ (ψ₁ᵗ (t₀ ++ a)) (proj₁ (φF (suc m) Bm β x))
    ΦF m t₀ Bm gb β hβ (mz {x = x}) =
      ++[] (λ r → M¹ (ψ₁ᵗ r) (proj₁ (φF (suc m) Bm β x))) t₀
        (G¹.m-zl (λ x → proj₁ (φF (suc m) Bm β x))
          (φm two o2 Ba kk one (inc tt self) (fn (suc m)) (okf (suc m)) (abf (suc m)) Bm β) hβ x)
    ΦF m t₀ Bm gb β hβ (m1 {t = a} {x = x} e r) =
      G¹.m-next (φF (suc m) Bm β x) (cofψ1 u₁ (t₀ ++ a) (cof++1 t₀ a e))
        (λ k → trans (fsnψ1 u₁ (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ r → replicate k (E.ψ u₁ r)) (pred++ t₀ a e)))
        (ΦF m t₀ Bm gb β hβ r)
    ΦF m t₀ Bm gb β hβ (mL {t = a} {x = x} e h) =
      mL (cofψω u₁ (t₀ ++ a) (cof++ω t₀ a e))
        (λ k → subst (λ r → M¹ r (proj₁ (φF (suc m) Bm β x)))
          (sym (trans (fsnψω u₁ (t₀ ++ a) k (cof++ω t₀ a e)) (cong ψ₁ᵗ (fsn++ t₀ a k e))))
          (ΦF m t₀ Bm gb β hβ (h k)))
    ΦF m t₀ Bm gb β hβ (mΩ {p = inj₂ (tt , t)} e nu h) = ΦFΩ m t₀ Bm gb β hβ t (view m t) e nu h
    ΦF zero t₀ Bm gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m′ ch) =
      subst (λ r → M¹ (ψ₁ᵗ r) (proj₁ (φF 0 (λ i u → ψ (fn 1) (okf 1) Bm i (inc tt u) (Bm i (inc tt u)) x) (φF 1 Bm β x) y)))
        (++-assoc t₀ a s₁)
        (ΦF⁰ (t₀ ++ a) (λ i u → ψ (fn 1) (okf 1) Bm i (inc tt u) (Bm i (inc tt u)) x) (φF 1 Bm β x)
          (ΦF zero t₀ Bm gb β hβ m′) ch)
    ΦF (suc m) t₀ Bm gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m′ ch) =
      subst (λ r → M¹ (ψ₁ᵗ r)
          (proj₁ (φF (suc m) (λ i u → ψ (fn (suc (suc m))) (okf (suc (suc m))) Bm i (inc tt u) (Bm i (inc tt u)) x)
                     (φF (suc (suc m)) Bm β x) y)))
        (++-assoc t₀ a s₁)
        (ΦF m (t₀ ++ a) (λ i u → ψ (fn (suc (suc m))) (okf (suc (suc m))) Bm i (inc tt u) (Bm i (inc tt u)) x)
          (gbStep t₀ Bm gb m′) (φF (suc (suc m)) Bm β x) (ΦF (suc m) t₀ Bm gb β hβ m′) ch)
    ΦF m t₀ Bm gb β hβ (mw m′ d) =
      mw (ΦF m t₀ Bm gb β hβ m′) (φm two o2 Ba kk one (inc tt self) (fn (suc m)) (okf (suc m)) (abf (suc m)) Bm β d)

    ΦFΩ : ∀ m (t₀ : E.T) (Bm : Base (fn (suc m))) → GB m Bm t₀ → (β : Tr⁺ one) → M¹ (ψ₁ᵗ t₀) (proj₁ β)
        → (t : Pos⁼ (fn m)) → PV m t → ∀ {a ν} {g : Br⁼ (fn m) t → Tr (fn (suc m))} → cof a ≡ cΩ ν → ν ≡ natT (lev m t)
        → (∀ η c → Lw⁼ m t η c → M (suc m) (fsT a η) (g c))
        → M¹ (ψ₁ᵗ (t₀ ++ a)) (proj₁ (φF (suc m) Bm β (Ω (inj₂ (tt , t)) g)))
    ΦFΩ m t₀ Bm gb β hβ .(pos⁼ si) (pv {i} si) {a} {ν} {g} e nu h =
      kcaseΦ si
        (λ K → M¹ (ψ₁ᵗ (t₀ ++ a)) (proj₁ (node⁺ K (λ z → φF (suc m) Bm β (g z)) (feedF Bm (pos⁼ si) g))))
        (λ le → mL (cofG u₁ (t₀ ++ a) (gtJ {j = 1} le eqν) (cof++Ω t₀ a e))
          (λ k → subst (λ r → M¹ r (proj₁ (limc⁺ (λ k′ → φF (suc m) Bm β
                                                     (g (iter (feedF Bm (pos⁼ si) g) (bz⁼ (fn m) (pos⁼ si)) k′))))))
            (sym (trans (fsnG u₁ (t₀ ++ a) k (gtJ {j = 1} le eqν) (cof++Ω t₀ a e))
                        (cong ψ₁ᵗ (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (G¹.m-cum (λ k′ → φF (suc m) Bm β (g (iter (feedF Bm (pos⁼ si) g) (bz⁼ (fn m) (pos⁼ si)) k′))) (suc k)
              (ΦF m t₀ Bm gb β hβ (h (γT (t₀ ++ a) ν k) (iter (feedF Bm (pos⁼ si) g) (bz⁼ (fn m) (pos⁼ si)) (suc k))
                                     (chain si t₀ Bm gb e eqν h k))))))
        (λ cv eq i0 lw →
          mΩ (cofK u₁ (t₀ ++ a) (pen1 i0 eqν) (cof++Ω t₀ a e)) (nu1 i0 eqν)
            (λ η c l → subst (λ r → M¹ r (proj₁ (φF (suc m) Bm β (g (cv c)))))
              (sym (trans (fsTK u₁ (t₀ ++ a) η (pen1 i0 eqν) (cof++Ω t₀ a e)) (cong ψ₁ᵗ (fsT++ t₀ a η e))))
              (ΦF m t₀ Bm gb β hβ (h η (cv c) (lw η c l)))))
      where
      eqν : ν ≡ natT i
      eqν = trans nu (cong natT (levEq si))
```

## Ω 树的折叠: ψ₁(Ω_{n+2}) 对着孩子 `nat (n+2)` 的支

结点不保留, 链是子层号 `fn (suc n)` 上的自身折叠 (`YiCLFam.Self`), 各项再经 `φ`; 记号 γ₀ = Ω_{n+1}, γₖ₊₁ = ψ_{n+1}(γₖ).

```agda
open Fin (B₀ two)

module Top (n : ℕ) (Bm : Base (fn (suc (suc n)))) (β : Tr⁺ one) (ok : OKB Bm) (hβ : M¹ Ω₁ᵗ (proj₁ β)) where
  Bs : Base (fn (suc n))
  Bs i u = Bm i (inc tt u)

  b : Tr⁺ (fn (suc n))
  b = Bm (fn (suc n)) (inc tt self)

  hb : M (suc n) (Ωᴺ (suc n)) (proj₁ b)
  hb = m⊴N (suc n) (Mβ n) (ok (fn (suc n)) (inc tt self))

  module SF = Self n Bs b

  gbs : GB n Bs []
  gbs = mkGB (λ {i} si → ok (fn i) (inc tt (inc tt (pth si))))
             (λ {i} si → ΩJ i (Bs (fn i) (inc tt (pth si))) (ok (fn i) (inc tt (inc tt (pth si)))))

  Ωη : E.T
  Ωη = Ωᴺ (suc (suc n))

  γ≡ : ∀ k → γT Ωη (natT (suc n)) k ≡ SF.gch [] k
  γ≡ zero    = refl
  γ≡ (suc k) = cong (ψᴺ (suc n)) (trans (fsTΩ (suc n) (γT Ωη (natT (suc n)) k)) (γ≡ k))

  g1 : cmpᵀ (sucT (natT (suc n))) u₁ ≡ gt
  g1 = cmp-gt {b = 1} {a = suc n} (s≤s z≤n)

  res : M¹ (ψ₁ᵗ Ωη) (proj₁ (φF (suc (suc n)) Bm β (proj₁ (Ωt (fn (suc (suc n)))))))
  res = mL (cofG u₁ Ωη g1 (cofΩ (suc n)))
    (λ k → subst (λ r → M¹ r (proj₁ (limc⁺ (λ k′ → next⁺ (φF (suc n) Bs β (SF.z k′))))))
      (sym (trans (fsnG u₁ Ωη k g1 (cofΩ (suc n)))
                  (cong ψ₁ᵗ (trans (fsTΩ (suc n) (γT Ωη (natT (suc n)) k)) (γ≡ k)))))
      (G¹.m-cum (λ k′ → next⁺ (φF (suc n) Bs β (SF.z k′))) (suc k)
        (mw (ΦF n [] Bs gbs β hβ (SF.sγ {P₀ = []} hb hb k)) (◃l zero))))

s-fin : ∀ n → S (ψ₁ᵗ (E.Ωt (natT (suc (suc n))))) (nat (suc (suc n)))
s-fin n Bm β ok hβ = Top.res n Bm β ok hβ
```

## 对一切 c

`M⁰ (natT n) c` 时 c 之下字面地有 `nat n` (`nat⊴`), 再沿 `YiKCStep.clos` 上行.

```agda
z⊴ : (c : Tr zero) → zero ⊴ c
z⊴ c with zl c
... | inj₁ refl = ⊴r
... | inj₂ d    = ⊴◃ d

nat⊴ : ∀ n {t c} → M⁰ t c → t ≡ natT n → nat n ⊴ c
nat⊴ zero    {c = c} m    q    = z⊴ c
nat⊴ (suc n) mz           ()
nat⊴ (suc n) (m1 e r)     refl = lift⊴ (nat⊴ n r (pred-nat n))
nat⊴ (suc n) (mL e h)     refl = ⊥-elim (c1≢cω (trans (sym (cof-nat n)) e))
nat⊴ (suc n) (mΩ {p = ()} _ _ _) q
nat⊴ (suc n) (mU {c = ()} _ _)   q
nat⊴ (suc n) (mw m d)     q    = ⊴◃ (⊴-◃ (nat⊴ (suc n) m q) d)

Sfin : ∀ n {c} → M⁰ (natT n) c → S (ψ₁ᵗ (E.Ωt (natT n))) c
Sfin zero          {c} l = S0 c
Sfin (suc zero)        l = S1 l
Sfin (suc (suc n))     l = clos⊴ (nat⊴ (suc (suc n)) l refl) (s-fin n)

a1s-fin : ∀ n {x} → M⁰ (natT n) x → S (ψ₁ᵗ (E.Ωt (natT (suc n)))) (suc x)
a1s-fin n {x} l = Sfin (suc n) (m1 (cof-nat n) (subst (λ t → M⁰ t x) (sym (pred-nat n)) l))

a1-fin : ∀ n {c} → M⁰ (natT n) c → M¹ (ψ₁ᵗ (E.Ωt (natT n))) (proj₁ (g₁ c))
a1-fin n {c} l = Sfin n l (B₀ (h₁ c)) (Ωt one) (λ i u → ⊴r) Mβ₀
```

## η = ω

基本列逐项是有限数的极限项 (`Lim1`), 例如 ω = ψ₀(1) (`ωᵀ`). 由 `YiKVInst.a1-lim` 与上一节.

```agda
c0≢cω : c0 ≡ cω → ⊥
c0≢cω ()

inv-lim : ∀ {η c} → cof η ≡ cω → M⁰ η c → ∀ k → M⁰ (fsn η k) c
inv-lim e mz                  k = ⊥-elim (c0≢cω e)
inv-lim e (m1 e′ r)           k = ⊥-elim (c1≢cω (trans (sym e′) e))
inv-lim e (mL _ h)            k = h k
inv-lim e (mΩ {p = ()} _ _ _) k
inv-lim e (mU {c = ()} _ _)   k
inv-lim e (mw m d)            k = mw (inv-lim e m k) d

Slim : ∀ η → cof η ≡ cω → (f : ℕ → ℕ) → (∀ k → fsn η k ≡ natT (f k)) → ∀ {c} → M⁰ η c → S (ψ₁ᵗ (E.Ωt η)) c
Slim η e f q {c} l Bm β ok hβ =
  a1-lim η _ e (λ k → subst (λ t → M¹ (ψ₁ᵗ (E.Ωt t)) _) (sym (q k))
    (Sfin (f k) (subst (λ t → M⁰ t c) (q k) (inv-lim e l k)) Bm β ok hβ))

ωᵀ : E.T
ωᵀ = E.ψ [] (𝟏 ∷ []) ∷ []

rep1 : ∀ k → replicate k 𝟏 ≡ natT k
rep1 zero    = refl
rep1 (suc k) = cong (𝟏 ∷_) (rep1 k)

a1-ω : ∀ {c} → M⁰ ωᵀ c → M¹ (ψ₁ᵗ (E.Ωt ωᵀ)) (proj₁ (g₁ c))
a1-ω {c} l = Slim ωᵀ refl (λ k → k) rep1 l (B₀ (h₁ c)) (Ωt one) (λ i u → ⊴r) Mβ₀
```
