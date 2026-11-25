# 正下标升层在 Ω₁ 处的左右值

第四层。对 j≥1，令 Aⱼ=ψ₀ψⱼ(Ωⱼ+Ω₁)。把 Aⱼ 以下原名的每个正下标同时升一级，其值的上确界恰为 Aⱼ₊₁；直接提升 Aⱼ 则把末尾的 Ω₁ 也提升，得到严格更大的值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseCut where

open import Data.Nat.Base using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import OCF.Align.EboLeanDef using (T; PT; ψ; natT; Ωt; _<ᵀ_; hd<; lv<; tl<; ar<; []<; HC; cof; cω; fsn; fsT; γT)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
import Survey.EboPTOFinite as B
import Survey.W4FiniteRaiseNames as R
import B26PSuffix as V

d = λ j t → ψ (natT j) t ∷ []
card = λ j → ψ (natT j) []
inner = λ n z → d (suc n) (card (suc n) ∷ z)
A : ℕ → T
A n = V.φ (inner n (Ωt (natT 1)))
seq : ℕ → ℕ → T
seq n zero = natT 1
seq n (suc k) = V.φ (inner n (seq n k))

body : ∀ n z → fsT (inner n (Ωt (natT 1))) z ≡ inner n z
body zero z = refl
body (suc n) z = refl

loop : ∀ n k → γT (inner n (Ωt (natT 1))) [] k ≡ seq n k
loop n zero = refl
loop n (suc k) = cong V.φ (trans (body n _) (cong (inner n) (loop n k)))

omega : ∀ n → cof (A n) ≡ cω
omega zero = refl
omega (suc n) = refl
branch : ∀ n k → fsn (A n) k ≡ seq n (suc k)
branch zero k = loop zero (suc k)
branch (suc n) k = loop (suc n) (suc k)

commute : ∀ n k → R.raise (seq n k) ≡ seq (suc n) k
commute n zero = refl
commute n (suc k) = cong (λ z → V.φ (inner (suc n) z)) (commute n k)

-- 任何在 Ω₁ 以下的首主项均为零下标，提升后仍在 Ω₁ 以下。
zero-only : ∀ {u} → u <ᵀ natT 1 → u ≡ []
zero-only []< = refl
zero-only (hd< (lv< ()))
zero-only (hd< (ar< ()))
zero-only (tl< ())

below-unit : ∀ {t} → t <ᵀ Ωt (natT 1) → R.raise t <ᵀ Ωt (natT 1)
below-unit []< = []<
below-unit (hd< (lv< h)) rewrite zero-only h = hd< (lv< []<)
below-unit (hd< (ar< ()))
below-unit (tl< ())

under-d : ∀ j {a b t} → (∀ {s} → s <ᵀ a → R.raise s <ᵀ b) →
  t <ᵀ d j a → R.raise t <ᵀ (ψ (R.index (natT j)) b ∷ [])
under-d j rec []< = []<
under-d j rec (hd< (lv< h)) = hd< (lv< (R.index< h))
under-d j rec (hd< (ar< h)) = hd< (ar< (rec h))
under-d j rec (tl< ())

before : ∀ n {t} → t <ᵀ A n → R.raise t <ᵀ A (suc n)
before n = under-d 0 (under-d (suc n) prefix)
  where
  prefix : ∀ {s} → s <ᵀ (card (suc n) ∷ Ωt (natT 1)) → R.raise s <ᵀ (card (suc (suc n)) ∷ Ωt (natT 1))
  prefix []< = []<
  prefix (hd< h) = hd< (R.principal h)
  prefix (tl< h) = tl< (below-unit h)

jump : ∀ n → A (suc n) <ᵀ R.raise (A n)
jump n = hd< (ar< (hd< (ar< (tl< (hd< (lv< (tl< []<)))))))

card-support : ∀ {z u} j → InGP u z (card j) → z ≡ []
card-support j (gh _) = refl
card-support j (gw _ h) = B.num-support j (G-mono (B.bottom _) h)
card-support j (gc _ ())

standard : ∀ n → NF (A n)
standard n = nf-ψ n[] (nf-ψ (B.nf-num j) arg (λ g → small g)) outer
  where
  j = suc n
  t = card j ∷ Ωt (natT 1)
  sort : ∀ m → HdLe (card (suc m)) (Ωt (natT 1))
  sort zero = inj₂ refl
  sort (suc m) = inj₁ (lv< (tl< []<))
  arg = n∷ (nf-hd (nf-Ω (B.nf-num j))) (sort n) (nf-Ω (B.nf-num 1))
  empty : ∀ {u z} → InG u z t → z ≡ []
  empty (gp h) = card-support j h
  empty (gtl (gp h)) = card-support 1 h
  empty (gtl (gtl ()))
  small : ∀ {u} → GB u t t
  small h rewrite empty h = []<
  outer : GB [] (d j t) (d j t)
  outer (gp (gh _)) = hd< (ar< []<)
  outer (gp (gw _ h)) rewrite B.num-support j h = []<
  outer (gp (gc _ h)) rewrite empty h = []<
  outer (gtl ())

indices : ∀ n → B.Indices (suc n) (A n)
indices n = B.cons z≤n (B.cons ≤-refl (B.cons ≤-refl B.empty (B.cons (s≤s z≤n) B.empty B.empty)) B.empty) B.empty

opaque
  cert : ∀ n → HC (A n)
  cert n = hc (standard n) (c∷ c[])

seq-nf : ∀ n k → NF (seq n (suc k))
seq-nf n k = subst NF (branch n k) (cl-fsn-NF (standard n) (omega n) k)
seq< : ∀ n k → seq n (suc k) <ᵀ A n
seq< n k = hd< (ar< (hd< (ar< (tl< (low k)))))
  where
  low : ∀ j → seq n j <ᵀ Ωt (natT 1)
  low zero = hd< (lv< []<)
  low (suc j) = hd< (lv< []<)

row< : ∀ n → A n <ᵀ B.row (suc n)
row< n = hd< (ar< (hd< (lv< (B.numeral-strict (s≤s ≤-refl)))))

lift-nf : ∀ n {t} → NF t → Ctbl t → t <ᵀ A n → NF (R.raise t)
lift-nf n nt c p = R.normal (B.recover (suc n) nt c (<ᵀ-trans p (row< n))) nt

below : ∀ n {t} (nt : NF t) (c : Ctbl t) (p : t <ᵀ A n) (h : HC (R.raise t)) →
  L.suc (Rt h) ≼ Rt (cert (suc n))
below n nt c p h = mono<ⁿ (lift-nf n nt c p) (standard (suc n)) (c∷ c[]) h (cert (suc n)) (before n p)

jump-value : ∀ n (h : HC (R.raise (A n))) → L.suc (Rt (cert (suc n))) ≼ Rt h
jump-value n h = mono<ⁿ (standard (suc n)) (R.normal (indices n) (standard n)) (c∷ c[]) (cert (suc n)) h (jump n)

least : ∀ n {y : L.Ordᶜ L.zero} →
  (∀ t → NF t → Ctbl t → t <ᵀ A n → (h : HC (R.raise t)) → Rt h ≼ y) →
  Rt (cert (suc n)) ≼ y
least n {y} upper = ≼-trans {b = L.lim (λ k → Rt (child k))}
  (proj₁ (V.limit parent (omega (suc n)) (λ k → Rt (child k)) (λ k → V.same refl (child k) (child k))))
  (l≼ point)
  where
  parent = cert (suc n)
  child = hω-inv parent (omega (suc n))
  point : ∀ k → Rt (child k) ≼ y
  point k = ≼-trans {b = Rt h} (tree-≼ eq (child k) h)
    (upper (seq n (suc k)) (seq-nf n k) (c∷ c[]) (seq< n k) h)
    where
    eq = trans (branch (suc n) k) (sym (commute n (suc k)))
    h = subst HC eq (child k)
```

上界来自首个不同主项的比较。最小性只用一个共尾族。从 1 开始反复施 x ↦ ψ₀ψⱼ(Ωⱼ+x) 得到 Aⱼ 的基本列，这条列逐项提升正好是 Aⱼ₊₁ 的基本列。
