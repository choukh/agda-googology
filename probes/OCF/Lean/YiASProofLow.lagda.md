# 不同步引理 (构造一路): 有限层号上主线折叠折到任一子层号的保持

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `LFᶠ`: 主线折叠 (`YiLegFold.ψs`) 把 `M (suc n) a x` 送到 `M j (ψ_j(t₀ + a))`, 对一切推导 (含 `mw`), 底满足 `GBᶠ`; 是 `YiCLLow.LF` (候选 A 的块) 在主线块上的对应物.
> 推论: `lowKeepᶠ : LowKeepᶠ` (`gradedᴬ` 上实填 `LowKeep`, 路径含 `self`), `lowKeepAsyncᶠ : LowKeepAsyncᶠ`.
> 不涉及 ℕ 极限与 Ω 形状层号, 不涉及上界; 接口见 [YiASIface](YiASIface.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiASProofLow where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; posW; posW⁼; Ev; Rt)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSFold using (ψs-⊵)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; γT; ψ; 𝟏; natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMEBase hiding (Rt)
open import OCF.Lean.YiMENote
open import OCF.Lean.YiMEAnchor using (++[]; Qu; module G⁰)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiEVReach using (cv⊴)
open import OCF.Lean.YiANFam
open import OCF.Lean.YiANKp using (≤ⁿ-refl; ≤ⁿ-step; fo; vch)
open import OCF.Lean.YiAbsGIface using (module Laws)
open import OCF.Lean.YiASIface
```

## 槽位的视图

层号 `fin (suc n)` 的每个槽位是某个 `pos⁼ si` (`si : Sbᶠ n i`, 槽位层 i).

```agda
sb≤ : ∀ {n j} → Sbᶠ n j → j ≤ⁿ n
sb≤ {n = n} s0 = ≤ⁿ-refl n
sb≤ (ss s)     = ≤ⁿ-step (sb≤ s)

pos⁼ : ∀ {n i} → Sbᶠ n i → Pos⁼ (fin n)
pos⁼ s0     = inj₁ tt
pos⁼ (ss s) = inj₂ (pos⁼ s)

data PV (n : ℕ) : Pos⁼ (fin n) → Set where
  pv : ∀ {i} (s : Sbᶠ n i) → PV n (pos⁼ s)

view : ∀ n t → PV n t
view n       (inj₁ tt) = pv s0
view (suc n) (inj₂ p) with view n p
... | pv s = pv (ss s)
view zero    (inj₂ ())

levEq : ∀ {n i} (s : Sbᶠ n i) → slot n (pos⁼ s) ≡ i
levEq s0     = refl
levEq (ss s) = levEq s

toBr : ∀ {n i} (s : Sbᶠ n i) → Tr (fin i) → Br⁼ (fin n) (pos⁼ s)
toBr s0     y = y
toBr (ss s) y = toBr s y

toLwˢ : ∀ {n i} (s : Sbᶠ n i) {η y} → M i η y → Lw n (pos⁼ s) η (toBr s y)
toLwˢ s0     m = m
toLwˢ (ss s) m = toLwˢ s m

gen : ∀ {n i} (s : Sbᶠ n i) (Ψ : (k : L) → k ≤ fin n → Tr k)
    → fromBr⁼ (fin n) (pos⁼ s) (Ψ (at⁼ (fin n) (pos⁼ s)) (posW⁼ (fin n) (pos⁼ s))) ≡ toBr s (Ψ (fin i) (pthᶠ s))
gen s0     Ψ = refl
gen (ss s) Ψ = gen s (λ k w → Ψ k (ins w))
```

## 对层号一般的几条

```agda
zlJ : ∀ j {S′ : Sg} (Φ : T S′ → Tr (fin j)) → (∀ {x y} → Lt S′ x y → fin j ⊢ Φ x ◃ Φ y)
    → ∀ {t} → M j t (Φ zero) → (y : T S′) → M j t (Φ y)
zlJ zero    Φ mo m y = G⁰.m-zl Φ mo m y
zlJ (suc j) Φ mo m y = GM.m-zl j Φ mo m y

nextJ : ∀ j {t p b} (nz : fin j ⊢ zero ◃ b) → cof t ≡ cω → (∀ n → fsn t n ≡ replicate n p)
      → M j (p ∷ []) b → M j t (next b nz)
nextJ zero    nz e q m = G⁰.m-next nz e q m
nextJ (suc j) nz e q m = GM.m-next j nz e q m

levP : (j : ℕ) → Pos (fin j) → ℕ
levP (suc j) q = slot j q

LwP : (j : ℕ) (q : Pos (fin j)) → E.T → Br (fin j) q → Set
LwP (suc j) q = Lw j q

mΩP : ∀ j {t ν} {q : Pos (fin j)} {g} → cof t ≡ cΩ ν → ν ≡ natT (levP j q)
    → (∀ η c → LwP j q η c → M j (fsT t η) (g c)) → M j t (Ω q g)
mΩP (suc j) = mΩ

penJ : ∀ j (q : Pos (fin j)) {ν} → ν ≡ natT (levP j q) → Pen (cmpᵀ (sucT ν) (natT j))
penJ (suc j) q nu = penN j q nu

gtJ : ∀ {j i ν} → j ≤ⁿ i → ν ≡ natT i → cmpᵀ (sucT ν) (natT j) ≡ gt
gtJ {j = j} {i = i} le refl = cmp-gt {b = j} {a = i} le

ΩJ : ∀ i (y : Tr (fin i)) → fin i ⊢ zero ◃ y → Ωt (fin i) ⊴ y → M i (Ωᴺ i) y
ΩJ zero    y nz le = pos⁰ y nz
ΩJ (suc i) y nz le = m⊴N (suc i) (Mβ i) le
```

## 保留判定

槽位 `pos⁼ si` (槽位层 i) 朝目标 `fin j` (路径 `pthᶠ s`): j ≤ i 时不保留 (同步或不同步都走这一支, 只看树一侧); 否则保留, 交出目标层里的槽位 q (槽位层仍是 i).

```agda
kcase : ∀ {n i j} (si : Sbᶠ n i) (s : Sbᶠ n j) (ε : Ev (fin n)) (ρ : Rt (fin n)) {X : Set} (Q : X → Set)
        {K : (q : Pos (fin j)) → (Br (fin j) q → Br⁼ (fin n) (pos⁼ si)) → X} {d : X}
      → (j ≤ⁿ i → Q d)
      → ((q : Pos (fin j)) (cv : Br (fin j) q → Br⁼ (fin n) (pos⁼ si)) → levP j q ≡ i
           → (∀ η c → LwP j q η c → Lw n (pos⁼ si) η (cv c)) → Q (K q cv))
      → Q (kp⁼ (fin n) ε ρ (pos⁼ si) (pthᶠ s) K d)
kcase s0      s      ε ρ Q dr kc = dr (sb≤ s)
kcase (ss si) s0     ε ρ Q dr kc = kc (pos⁼ si) (λ z → z) (levEq si) (λ η c l → l)
kcase (ss si) (ss s) ε ρ Q dr kc = kcase si s ε ρ Q dr kc
```

## 回灌

`vch` (`YiANKp`) 逐字是折叠在结点一行里的回灌链; 它的每一步是朝槽位层 `fin i` 的折叠.

```agda
feed≡ : ∀ {n i} (si : Sbᶠ n i) (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (B : Base (fin (suc n)))
        (x : Tr (fin (suc n)))
      → fromBr (fin (suc n)) (pos⁼ si) (fo n ε ρ B (pos⁼ si) x)
      ≡ toBr si (ψs (fin (suc n)) ε ρ B (fin i) (ins (pthᶠ si)) (bs B (fin i) (ins (pthᶠ si))) (ns B (fin i) (ins (pthᶠ si))) x)
feed≡ {n = n} si ε ρ B x =
  gen si (λ k w → ψs (fin (suc n)) ε ρ B k (ins w) (bs B k (ins w)) (ns B k (ins w)) x)
```

## 折到低层

对 `M (suc n) a x` 的推导归纳. 结点处按 `kcase`: 保留时在目标层造结点 (规则 5Ω), 否则取回灌链的部分和极限 (规则 6, `chain`: 回灌链对着 γ-链). 放宽 (`mw`) 处用折叠的单调性.

```agda
mutual
  LFᶠ : ∀ {n j} (s : Sbᶠ n j) (t₀ : E.T) (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (B : Base (fin (suc n)))
      → GBᶠ n B t₀ → (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) → M j (ψᴺ j t₀) β
      → ∀ {a x} → M (suc n) a x
      → M j (ψᴺ j (t₀ ++ a)) (ψs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ x)
  LFᶠ {n = n} {j = j} s t₀ ε ρ B gb β nβ hβ (mz {x = x}) =
    ++[] (λ r → M j (ψᴺ j r) (ψs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ x)) t₀
      (zlJ j (ψs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ)
        (monos (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ) hβ x)
  LFᶠ {n = n} {j = j} s t₀ ε ρ B gb β nβ hβ (m1 {t = a} {x = x} e r) =
    nextJ j (nzs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ x) (cofψ1 (natT j) (t₀ ++ a) (cof++1 t₀ a e))
      (λ k → trans (fsnψ1 (natT j) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ r → replicate k (ψ (natT j) r)) (pred++ t₀ a e)))
      (LFᶠ s t₀ ε ρ B gb β nβ hβ r)
  LFᶠ {n = n} {j = j} s t₀ ε ρ B gb β nβ hβ (mL {t = a} {x = x} e h) =
    mLN j (cofψω (natT j) (t₀ ++ a) (cof++ω t₀ a e))
      (λ k → subst (λ r → M j r (ψs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ x))
        (sym (trans (fsnψω (natT j) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ j) (fsn++ t₀ a k e))))
        (LFᶠ s t₀ ε ρ B gb β nβ hβ (h k)))
  LFᶠ {n = n} s t₀ ε ρ B gb β nβ hβ (mΩ {p = p} e nu h) = LFΩ s t₀ ε ρ B gb β nβ hβ p (view n p) e nu h
  LFᶠ {n = zero} s0 t₀ ε ρ B gb β nβ hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ r → M⁰ (ψᴺ 0 r) (ψs zero tt tt (dS zero ε ρ B x) zero self
                               (ψs (fin 1) ε ρ B zero (ins self) β nβ x) (nzs (fin 1) ε ρ B zero (ins self) β nβ x) y))
      (++-assoc t₀ a s₁)
      (Qu (dS zero ε ρ B x) (ψs (fin 1) ε ρ B zero (ins self) β nβ x) (nzs (fin 1) ε ρ B zero (ins self) β nβ x)
        (LFᶠ s0 t₀ ε ρ B gb β nβ hβ m) ch)
  LFᶠ {n = suc n} s0 t₀ ε ρ B gb β nβ hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ r → M (suc n) (ψᴺ (suc n) r)
        (Self.F n ε ρ (dS (fin (suc n)) ε ρ B x)
          (ψs (fin (suc (suc n))) ε ρ B (fin (suc n)) (ins self) β nβ x)
          (nzs (fin (suc (suc n))) ε ρ B (fin (suc n)) (ins self) β nβ x) y))
      (++-assoc t₀ a s₁)
      (Self.PF n ε ρ (dS (fin (suc n)) ε ρ B x)
        (ψs (fin (suc (suc n))) ε ρ B (fin (suc n)) (ins self) β nβ x)
        (nzs (fin (suc (suc n))) ε ρ B (fin (suc n)) (ins self) β nβ x)
        (LFᶠ s0 t₀ ε ρ B gb β nβ hβ m) ch)
  LFᶠ {n = suc n} {j = j} (ss s) t₀ ε ρ B gb β nβ hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ r → M j (ψᴺ j r)
        (ψs (fin (suc n)) ε ρ (dS (fin (suc n)) ε ρ B x) (fin j) (ins (pthᶠ s))
          (ψs (fin (suc (suc n))) ε ρ B (fin j) (ins (ins (pthᶠ s))) β nβ x)
          (nzs (fin (suc (suc n))) ε ρ B (fin j) (ins (ins (pthᶠ s))) β nβ x) y))
      (++-assoc t₀ a s₁)
      (LFᶠ s (t₀ ++ a) ε ρ (dS (fin (suc n)) ε ρ B x)
        (mkGBᶠ (λ {i} si → ⊴-trans (gΩ gb (ss si))
                  (cv⊴ (ψs-⊵ (fin (suc (suc n))) ε ρ B (fin i) (ins (ins (pthᶠ si)))
                          (bs B (fin i) (ins (ins (pthᶠ si)))) (ns B (fin i) (ins (ins (pthᶠ si)))) x)))
               (λ {i} si → LFᶠ (ss si) t₀ ε ρ B gb (bs B (fin i) (ins (ins (pthᶠ si)))) (ns B (fin i) (ins (ins (pthᶠ si))))
                             (gM gb (ss si)) m))
        (ψs (fin (suc (suc n))) ε ρ B (fin j) (ins (ins (pthᶠ s))) β nβ x)
        (nzs (fin (suc (suc n))) ε ρ B (fin j) (ins (ins (pthᶠ s))) β nβ x)
        (LFᶠ (ss s) t₀ ε ρ B gb β nβ hβ m) ch)
  LFᶠ {n = n} {j = j} s t₀ ε ρ B gb β nβ hβ (mw m d) =
    mwN j (LFᶠ s t₀ ε ρ B gb β nβ hβ m) (monos (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ d)

  LFΩ : ∀ {n j} (s : Sbᶠ n j) (t₀ : E.T) (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (B : Base (fin (suc n)))
      → GBᶠ n B t₀ → (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) → M j (ψᴺ j t₀) β
      → (p : Pos (fin (suc n))) → PV n p → ∀ {a ν} {g : Br (fin (suc n)) p → Tr (fin (suc n))}
      → cof a ≡ cΩ ν → Nw n p ν → (∀ η c → Lw n p η c → M (suc n) (fsT a η) (g c))
      → M j (ψᴺ j (t₀ ++ a)) (ψs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ (Ω p g))
  LFΩ {n = n} {j = j} s t₀ ε ρ B gb β nβ hβ .(pos⁼ si) (pv {i} si) {a} {ν} {g} e nu h =
    kcase si s ε ρ (λ Z → M j (ψᴺ j (t₀ ++ a)) Z)
      (λ le → mLN j (cofG (natT j) (t₀ ++ a) (gtJ le eqν) (cof++Ω t₀ a e))
        (λ k → subst (λ r → M j r (limc (λ m → ψs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ (g (vch n ε ρ B (pos⁼ si) g m)))
                                        (λ m → nzs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ (g (vch n ε ρ B (pos⁼ si) g m)))))
          (sym (trans (fsnG (natT j) (t₀ ++ a) k (gtJ le eqν) (cof++Ω t₀ a e))
                      (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
          (cumN j (λ m → ψs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ (g (vch n ε ρ B (pos⁼ si) g m)))
                  (λ m → nzs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ (g (vch n ε ρ B (pos⁼ si) g m))) (suc k)
            (LFᶠ s t₀ ε ρ B gb β nβ hβ
              (h (γT (t₀ ++ a) ν k) (vch n ε ρ B (pos⁼ si) g (suc k)) (chain si t₀ ε ρ B gb e eqν h k))))))
      (λ q cv lq lw →
        mΩP j (cofK (natT j) (t₀ ++ a) (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (nuq lq)
          (λ η c l → subst (λ r → M j r (ψs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ (g (cv c))))
            (sym (trans (fsTK (natT j) (t₀ ++ a) η (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a η e))))
            (LFᶠ s t₀ ε ρ B gb β nβ hβ (h η (cv c) (lw η c l)))))
    where
    eqν : ν ≡ natT i
    eqν = trans nu (cong natT (levEq si))
    nuq : ∀ {q : Pos (fin j)} → levP j q ≡ i → ν ≡ natT (levP j q)
    nuq lq = trans eqν (cong natT (sym lq))

  chain : ∀ {n i} (si : Sbᶠ n i) (t₀ : E.T) (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (B : Base (fin (suc n)))
        → GBᶠ n B t₀ → ∀ {a ν} {g : Br (fin (suc n)) (pos⁼ si) → Tr (fin (suc n))} → cof a ≡ cΩ ν → ν ≡ natT i
        → (∀ η c → Lw n (pos⁼ si) η c → M (suc n) (fsT a η) (g c))
        → ∀ k → Lw n (pos⁼ si) (γT (t₀ ++ a) ν k) (vch n ε ρ B (pos⁼ si) g (suc k))
  chain {n = n} {i = i} si t₀ ε ρ B gb {a} {g = g} e refl h zero =
    subst (Lw n (pos⁼ si) (Ωᴺ i)) (sym (feed≡ si ε ρ B (g (br0 (fin (suc n)) (pos⁼ si)))))
      (toLwˢ si (ΩJ i
        (ψs (fin (suc n)) ε ρ B (fin i) (ins (pthᶠ si)) (bs B (fin i) (ins (pthᶠ si))) (ns B (fin i) (ins (pthᶠ si)))
            (g (br0 (fin (suc n)) (pos⁼ si))))
        (nzs (fin (suc n)) ε ρ B (fin i) (ins (pthᶠ si)) (bs B (fin i) (ins (pthᶠ si))) (ns B (fin i) (ins (pthᶠ si)))
             (g (br0 (fin (suc n)) (pos⁼ si))))
        (⊴-trans (gΩ gb si)
          (cv⊴ (ψs-⊵ (fin (suc n)) ε ρ B (fin i) (ins (pthᶠ si)) (bs B (fin i) (ins (pthᶠ si))) (ns B (fin i) (ins (pthᶠ si)))
                  (g (br0 (fin (suc n)) (pos⁼ si))))))))
  chain {n = n} {i = i} si t₀ ε ρ B gb {a} {g = g} e refl h (suc k) =
    subst (Lw n (pos⁼ si) (ψᴺ i (fsT (t₀ ++ a) (γT (t₀ ++ a) (natT i) k))))
      (sym (feed≡ si ε ρ B (g (vch n ε ρ B (pos⁼ si) g (suc k)))))
      (toLwˢ si (subst (λ r → M i (ψᴺ i r)
                   (ψs (fin (suc n)) ε ρ B (fin i) (ins (pthᶠ si)) (bs B (fin i) (ins (pthᶠ si))) (ns B (fin i) (ins (pthᶠ si)))
                       (g (vch n ε ρ B (pos⁼ si) g (suc k)))))
        (sym (fsT++ t₀ a (γT (t₀ ++ a) (natT i) k) e))
        (LFᶠ si t₀ ε ρ B gb (bs B (fin i) (ins (pthᶠ si))) (ns B (fin i) (ins (pthᶠ si))) (gM gb si)
          (h (γT (t₀ ++ a) (natT i) k) (vch n ε ρ B (pos⁼ si) g (suc k)) (chain si t₀ ε ρ B gb e refl h k)))))
```

## 接口上的两条

`LowKeep` 在 `gradedᴬ`, `domsᴬ` 上: 路径 `self` 是 `YiANFam.Self.PF`, 其余是 `LFᶠ`. 限制到不同步对是它的特例 (不用到不同步对的任何分量).

```agda
lowKeepᶠ : LowKeepᶠ
lowKeepᶠ {ℓ = .(suc N)} (ε , ρ , B) .self   (β , nβ) t₀ (N , refl) (s0 , refl)   (hβ , gb) _ m = Self.PF N ε ρ B β nβ hβ m
lowKeepᶠ {ℓ = .(suc N)} (ε , ρ , B) .(ins (pthᶠ s)) (β , nβ) t₀ (N , refl) (ss s , refl) (hβ , gb) _ m =
  LFᶠ s t₀ ε ρ B gb β nβ hβ m

lowKeepAsyncᶠ : LowKeepAsyncᶠ
lowKeepAsyncᶠ b w β K gb wl bd gx _ m = lowKeepᶠ b w β K gb wl bd gx m
```
