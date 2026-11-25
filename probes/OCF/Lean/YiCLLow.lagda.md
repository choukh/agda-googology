# 验收 (候选 A, 精简块): 有限读回层号上折到低层的保持

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 量化域同 [YiCLFam](YiCLFam.lagda.md) (层号 `fn n`), 底满足 `GB` (各分量在 Ω 树之上, 且对着 ψ_i(t₀)).
> `LF`: 层号 `fn (suc n)` 的树朝任一子层号 `fn j` (j ≤ n, 路径是 `inc` 链) 的折叠, 把 `M (suc n) a x` 送到 `M j (ψ_j(t₀ + a))`; j = 0 即折到第 0 层. 结点处按 "槽位层号 < 目标层号" 保留 (规则 5Ω), 否则取回灌链 (规则 6, `chain`: 回灌链对着 γ-链); 判定由 `kcase` 对路径递归给出, 不比较两个孩子.
> 不涉及 ℕ 极限层号 (那里保留判定经 `way` 与相邻路径, 配对要另带一致性), 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCLLow where

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
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiKVRel hiding (cof++Ω; fsT++; Pu)
open import OCF.Lean.YiKCStep using (⊴-trans; ψ-⊵)
open import OCF.Lean.YiCertFold using (Base; Keep; node⁺)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; γT; natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; Pen; cmp-pen; cmp-gt; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiCLFam
```

## 子层号, 路径, 槽位的视图

`Sb n j`: `fn j` 是 `fn n` 或它下面的子层号; `pth` 是到它的路径, `pos⁼` 是对应的槽位. 每个槽位都是某个 `pos⁼ s` (`view`).

```agda
data Sb : ℕ → ℕ → Set where
  s0 : ∀ {n} → Sb n n
  ss : ∀ {n j} → Sb n j → Sb (suc n) j

pth : ∀ {n j} → Sb n j → fn j ≤ fn n
pth s0     = self
pth (ss s) = inc tt (pth s)

sb≤ : ∀ {n j} → Sb n j → j ≤ⁿ n
sb≤ {n = n} s0 = ≤ⁿ-refl n
sb≤ (ss s) = ≤ⁿ-step (sb≤ s)

pos⁼ : ∀ {n i} → Sb n i → Pos⁼ (fn n)
pos⁼ s0     = inj₁ tt
pos⁼ (ss s) = inj₂ (inj₂ (tt , pos⁼ s))

data PV (n : ℕ) : Pos⁼ (fn n) → Set where
  pv : ∀ {i} (s : Sb n i) → PV n (pos⁼ s)

mutual
  view : ∀ n t → PV n t
  view n (inj₁ tt) = pv s0
  view n (inj₂ p)  = viewP n p

  viewP : ∀ n p → PV n (inj₂ p)
  viewP (suc n) (inj₂ (tt , t)) with view n t
  ... | pv s = pv (ss s)

levEq : ∀ {n i} (s : Sb n i) → lev n (pos⁼ s) ≡ i
levEq s0     = refl
levEq (ss s) = levEq s

toBr : ∀ {n i} (s : Sb n i) → Tr (fn i) → Br⁼ (fn n) (pos⁼ s)
toBr s0     y = y
toBr (ss s) y = toBr s y

toLw : ∀ {n i} (s : Sb n i) {η y} → M i η y → Lw⁼ n (pos⁼ s) η (toBr s y)
toLw s0     m = m
toLw (ss s) m = toLw s m
```

槽位所在层号与到它的路径, 换成 `fn i` 与 `pth s` (对任意按 "层号, 路径" 取值的 Ψ).

```agda
gen : ∀ {n i} (s : Sb n i) (Ψ : (k : L) → k ≤ fn n → Tr k)
    → proj₂ (sl⁼ (fn n) (pos⁼ s)) (Ψ (proj₁ (sl⁼ (fn n) (pos⁼ s))) (posW⁼ (fn n) (pos⁼ s))) ≡ toBr s (Ψ (fn i) (pth s))
gen s0     Ψ = refl
gen (ss s) Ψ = gen s (λ k w → Ψ k (inc tt w))
```

## 对层号一般的几条

```agda
zlJ : ∀ j {S′ : Sg} (Φ : T S′ → Tr (fn j)) → (∀ {x y} → Lt S′ x y → fn j ⊢ Φ x ◃ Φ y)
    → ∀ {t} → M j t (Φ zero) → (y : T S′) → M j t (Φ y)
zlJ zero    Φ mo m y = G⁰.m-zl Φ mo m y
zlJ (suc j) Φ mo m y = GM.m-zl j Φ mo m y

nextJ : ∀ j {t p} (b : Tr⁺ (fn j)) → cof t ≡ cω → (∀ n → fsn t n ≡ replicate n p)
      → M j (p ∷ []) (proj₁ b) → M j t (proj₁ (next⁺ b))
nextJ zero    b e q m = G⁰.m-next b e q m
nextJ (suc j) b e q m = GM.m-next j b e q m

cumJ : ∀ j {t} (F : ℕ → Tr⁺ (fn j)) (n : ℕ) → M j t (proj₁ (F n)) → M j t (proj₁ (limc⁺ F))
cumJ zero    F n m = G⁰.m-cum F n m
cumJ (suc j) F n m = GM.m-cum j F n m

mLJ : ∀ j {t x} → cof t ≡ cω → (∀ n → M j (fsn t n) x) → M j t x
mLJ zero    = mL
mLJ (suc j) = mL

mΩP : ∀ j {t ν} {q : Pos (fn j)} {g} → cof t ≡ cΩ ν → ν ≡ natT (levP j q)
    → (∀ η c → LwP j q η c → M j (fsT t η) (g c)) → M j t (Ω q g)
mΩP (suc j) = mΩ

ΩJ : ∀ i (y : Tr⁺ (fn i)) → proj₁ (Ωt (fn i)) ⊴ proj₁ y → M i (Ωᴺ i) (proj₁ y)
ΩJ zero    y le = pos⁰ (proj₁ y) (proj₂ y)
ΩJ (suc i) y le = m⊴N (suc i) (Mβ i) le

penJ : ∀ j (q : Pos (fn j)) {ν} → ν ≡ natT (levP j q) → Pen (cmpᵀ (sucT ν) (natT j))
penJ j q refl = cmp-pen (levP< j q)

gtJ : ∀ {j i ν} → j ≤ⁿ i → ν ≡ natT i → cmpᵀ (sucT ν) (natT j) ≡ gt
gtJ {j = j} {i = i} le refl = cmp-gt {b = j} {a = i} le
```

## 保留判定

槽位 `pos⁼ si` (层号 i) 朝目标 `fn j` (路径 `pth s`): j ≤ i 时不保留; 否则保留, 交出目标层里的槽位 q (层号仍是 i) 与分支的对应. 对两条路径同时递归.

```agda
kcase : ∀ {n i j} (si : Sb n i) (s : Sb n j) (Q : Keep (fn j) (Br⁼ (fn n) (pos⁼ si)) (bz⁼ (fn n) (pos⁼ si)) → Set)
      → (j ≤ⁿ i → Q nothing)
      → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ (fn n) (pos⁼ si)) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ (fn n) (pos⁼ si))
           → levP j q ≡ i → (∀ η c → LwP j q η c → Lw⁼ n (pos⁼ si) η (cv c)) → Q (just (q , cv , eq)))
      → Q (kp⁼ (fn n) (okf n) (pos⁼ si) (pth s))
kcase s0      s      Q dr kc = dr (sb≤ s)
kcase (ss si) s0     Q dr kc = kc (inj₂ (tt , pos⁼ si)) (λ z → z) refl (levEq si) (λ η c l → l)
kcase (ss si) (ss s) Q dr kc = kcase si s Q dr kc
```

## 底的条件, 回灌的函数

`GB n B t₀`: 底 B 在每个子层号上的分量在 Ω 树之上, 且对着 ψ_i(t₀). `feedF` 逐字是折叠在结点一行里的回灌.

```agda
record GB (n : ℕ) (B : Base (fn (suc n))) (t₀ : E.T) : Set where
  constructor mkGB
  field
    gΩ : ∀ {i} (si : Sb n i) → proj₁ (Ωt (fn i)) ⊴ proj₁ (B (fn i) (inc tt (pth si)))
    gM : ∀ {i} (si : Sb n i) → M i (ψᴺ i t₀) (proj₁ (B (fn i) (inc tt (pth si))))
open GB public

feedF : ∀ {n} (B : Base (fn (suc n))) (t : Pos⁼ (fn n)) (g : Br⁼ (fn n) t → Tr (fn (suc n))) → Br⁼ (fn n) t → Br⁼ (fn n) t
feedF {n = n} B t g z = proj₂ (sl⁼ (fn n) t)
  (proj₁ (ψ (fn (suc n)) (okf (suc n)) B (proj₁ (sl⁼ (fn n) t)) (inc tt (posW⁼ (fn n) t))
            (B (proj₁ (sl⁼ (fn n) t)) (inc tt (posW⁼ (fn n) t))) (g z)))

feed≡ : ∀ {n i} (si : Sb n i) (B : Base (fn (suc n))) (g : Br⁼ (fn n) (pos⁼ si) → Tr (fn (suc n))) (z : Br⁼ (fn n) (pos⁼ si))
      → feedF B (pos⁼ si) g z
      ≡ toBr si (proj₁ (ψ (fn (suc n)) (okf (suc n)) B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si))) (g z)))
feed≡ {n = n} si B g z = gen si (λ k w → proj₁ (ψ (fn (suc n)) (okf (suc n)) B k (inc tt w) (B k (inc tt w)) (g z)))
```

## 折到低层

```agda
mutual
  LF : ∀ {n j} (s : Sb n j) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀ → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
     → ∀ {a x} → M (suc n) a x
     → M j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β x))
  LF {n = n} {j = j} s t₀ B gb β hβ (mz {x = x}) =
    ++[] (λ r → M j (ψᴺ j r) (proj₁ (ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β x))) t₀
      (zlJ j (λ x → proj₁ (ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β x))
        (mono (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β) hβ x)
  LF {n = n} {j = j} s t₀ B gb β hβ (m1 {t = a} {x = x} e r) =
    nextJ j (ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β x) (cofψ1 (natT j) (t₀ ++ a) (cof++1 t₀ a e))
      (λ k → trans (fsnψ1 (natT j) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ r → replicate k (E.ψ (natT j) r)) (pred++ t₀ a e)))
      (LF s t₀ B gb β hβ r)
  LF {n = n} {j = j} s t₀ B gb β hβ (mL {t = a} {x = x} e h) =
    mLJ j (cofψω (natT j) (t₀ ++ a) (cof++ω t₀ a e))
      (λ k → subst (λ r → M j r (proj₁ (ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β x)))
        (sym (trans (fsnψω (natT j) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ j) (fsn++ t₀ a k e))))
        (LF s t₀ B gb β hβ (h k)))
  LF {n = n} {j = j} s t₀ B gb β hβ (mΩ {p = inj₂ (tt , t)} e nu h) = LFΩ s t₀ B gb β hβ t (view n t) e nu h
  LF {n = zero} s0 t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ r → M⁰ (ψᴺ 0 r) (proj₁ (ψ zero tt (λ i u → ψ (fn 1) (okf 1) B i (inc tt u) (B i (inc tt u)) x) zero self
                                        (ψ (fn 1) (okf 1) B zero (inc tt self) β x) y)))
      (++-assoc t₀ a s₁)
      (Qu tt (λ i u → ψ (fn 1) (okf 1) B i (inc tt u) (B i (inc tt u)) x) self (ψ (fn 1) (okf 1) B zero (inc tt self) β x)
        (LF s0 t₀ B gb β hβ m) ch)
  LF {n = suc n} s0 t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ r → M (suc n) (ψᴺ (suc n) r)
        (Self.F n (λ i u → ψ (fn (suc (suc n))) (okf (suc (suc n))) B i (inc tt u) (B i (inc tt u)) x)
                  (ψ (fn (suc (suc n))) (okf (suc (suc n))) B (fn (suc n)) (inc tt self) β x) y))
      (++-assoc t₀ a s₁)
      (Self.PF n (λ i u → ψ (fn (suc (suc n))) (okf (suc (suc n))) B i (inc tt u) (B i (inc tt u)) x)
                 (ψ (fn (suc (suc n))) (okf (suc (suc n))) B (fn (suc n)) (inc tt self) β x)
                 (LF s0 t₀ B gb β hβ m) ch)
  LF {n = suc n} {j = j} (ss s) t₀ B gb β hβ (mU {t = a} {s = s₁} {x = x} {y = y} m ch) =
    subst (λ r → M j (ψᴺ j r)
        (proj₁ (ψ (fn (suc n)) (okf (suc n)) (λ i u → ψ (fn (suc (suc n))) (okf (suc (suc n))) B i (inc tt u) (B i (inc tt u)) x)
                  (fn j) (inc tt (pth s)) (ψ (fn (suc (suc n))) (okf (suc (suc n))) B (fn j) (inc tt (inc tt (pth s))) β x) y)))
      (++-assoc t₀ a s₁)
      (LF s (t₀ ++ a) (λ i u → ψ (fn (suc (suc n))) (okf (suc (suc n))) B i (inc tt u) (B i (inc tt u)) x)
        (mkGB (λ {i} si → ⊴-trans (gΩ gb (ss si))
                 (ψ-⊵ (fn (suc (suc n))) (okf (suc (suc n))) B (fn i) (inc tt (inc tt (pth si))) (B (fn i) (inc tt (inc tt (pth si)))) x))
              (λ {i} si → LF (ss si) t₀ B gb (B (fn i) (inc tt (inc tt (pth si)))) (gM gb (ss si)) m))
        (ψ (fn (suc (suc n))) (okf (suc (suc n))) B (fn j) (inc tt (inc tt (pth s))) β x)
        (LF (ss s) t₀ B gb β hβ m) ch)
  LF {n = n} {j = j} s t₀ B gb β hβ (mw m d) =
    mwN j (LF s t₀ B gb β hβ m) (mono (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β d)

  LFΩ : ∀ {n j} (s : Sb n j) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀ → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
      → (t : Pos⁼ (fn n)) → PV n t → ∀ {a ν} {g : Br⁼ (fn n) t → Tr (fn (suc n))} → cof a ≡ cΩ ν → ν ≡ natT (lev n t)
      → (∀ η c → Lw⁼ n t η c → M (suc n) (fsT a η) (g c))
      → M j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β (Ω (inj₂ (tt , t)) g)))
  LFΩ {n = n} {j = j} s t₀ B gb β hβ .(pos⁼ si) (pv {i} si) {a} {ν} {g} e nu h =
    kcase si s
      (λ K → M j (ψᴺ j (t₀ ++ a))
               (proj₁ (node⁺ K (λ z → ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β (g z)) (feedF B (pos⁼ si) g))))
      (λ le → mLJ j (cofG (natT j) (t₀ ++ a) (gtJ le eqν) (cof++Ω t₀ a e))
        (λ k → subst (λ r → M j r (proj₁ (limc⁺ (λ m → ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β
                                                     (g (iter (feedF B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) m))))))
          (sym (trans (fsnG (natT j) (t₀ ++ a) k (gtJ le eqν) (cof++Ω t₀ a e))
                      (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
          (cumJ j (λ m → ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β
                           (g (iter (feedF B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) m))) (suc k)
            (LF s t₀ B gb β hβ (h (γT (t₀ ++ a) ν k) (iter (feedF B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))
                                 (chain si t₀ B gb e eqν h k))))))
      (λ q cv eq lq lw →
        mΩP j (cofK (natT j) (t₀ ++ a) (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (nuq lq)
          (λ η c l → subst (λ r → M j r (proj₁ (ψ (fn (suc n)) (okf (suc n)) B (fn j) (inc tt (pth s)) β (g (cv c)))))
            (sym (trans (fsTK (natT j) (t₀ ++ a) η (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a η e))))
            (LF s t₀ B gb β hβ (h η (cv c) (lw η c l)))))
    where
    eqν : ν ≡ natT i
    eqν = trans nu (cong natT (levEq si))
    nuq : ∀ {q : Pos (fn j)} → levP j q ≡ i → ν ≡ natT (levP j q)
    nuq lq = trans eqν (cong natT (sym lq))

  chain : ∀ {n i} (si : Sb n i) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀
        → ∀ {a ν} {g : Br⁼ (fn n) (pos⁼ si) → Tr (fn (suc n))} → cof a ≡ cΩ ν → ν ≡ natT i
        → (∀ η c → Lw⁼ n (pos⁼ si) η c → M (suc n) (fsT a η) (g c))
        → ∀ k → Lw⁼ n (pos⁼ si) (γT (t₀ ++ a) ν k) (iter (feedF B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))
  chain {n = n} {i = i} si t₀ B gb {a} {g = g} e refl h zero =
    subst (Lw⁼ n (pos⁼ si) (Ωᴺ i)) (sym (feed≡ si B g (bz⁼ (fn n) (pos⁼ si))))
      (toLw si (ΩJ i (ψ (fn (suc n)) (okf (suc n)) B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si))) (g (bz⁼ (fn n) (pos⁼ si))))
        (⊴-trans (gΩ gb si)
          (ψ-⊵ (fn (suc n)) (okf (suc n)) B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si))) (g (bz⁼ (fn n) (pos⁼ si)))))))
  chain {n = n} {i = i} si t₀ B gb {a} {g = g} e refl h (suc k) =
    subst (Lw⁼ n (pos⁼ si) (ψᴺ i (fsT (t₀ ++ a) (γT (t₀ ++ a) (natT i) k))))
      (sym (feed≡ si B g (iter (feedF B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))))
      (toLw si (subst (λ r → M i (ψᴺ i r)
                   (proj₁ (ψ (fn (suc n)) (okf (suc n)) B (fn i) (inc tt (pth si)) (B (fn i) (inc tt (pth si)))
                             (g (iter (feedF B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k))))))
        (sym (fsT++ t₀ a (γT (t₀ ++ a) (natT i) k) e))
        (LF si t₀ B gb (B (fn i) (inc tt (pth si))) (gM gb si)
          (h (γT (t₀ ++ a) (natT i) k) (iter (feedF B (pos⁼ si) g) (bz⁼ (fn n) (pos⁼ si)) (suc k)) (chain si t₀ B gb e refl h k)))))
```

## 孩子的底仍满足条件

`up x _ y` 的折叠里, 孩子的底是 "x 朝各子层号的折叠"; 它对着 ψ_i(t₀ + a) (a 对着 x), 由 `LF` 给出.

```agda
gbStep : ∀ {n} (t₀ : E.T) (B : Base (fn (suc (suc n)))) → GB (suc n) B t₀ → ∀ {a x} → M (suc (suc n)) a x
       → GB n (λ i u → ψ (fn (suc (suc n))) (okf (suc (suc n))) B i (inc tt u) (B i (inc tt u)) x) (t₀ ++ a)
gbStep {n = n} t₀ B gb {x = x} m =
  mkGB (λ {i} si → ⊴-trans (gΩ gb (ss si))
          (ψ-⊵ (fn (suc (suc n))) (okf (suc (suc n))) B (fn i) (inc tt (inc tt (pth si))) (B (fn i) (inc tt (inc tt (pth si)))) x))
       (λ {i} si → LF (ss si) t₀ B gb (B (fn i) (inc tt (inc tt (pth si)))) (gM gb (ss si)) m)
```
