# 对一切派发: `Compat` 含塔与 Λ 的配置对就推出 LPO

验收文件. 编译定理, 无前提: 对任意派发 `D`, 若某个 `S : Compat D` 含 `(Lw-tw (2+n), x, Lw-tw (2+j), x′)` (`lpo-tw`), `(Lw-tw (2+n), x, VΛ, x′)` (`lpo-Λ`) 或 `(VΛ, x, VΛ, x′)` (`lpo-ΛΛ`), 则 LPO.
办法同 [YiCompatDlNeg](YiCompatDlNeg.lagda.md) 的 `core`: 左边进 `tw 2` 型的支 `suc (lim (hα α))`, 那里结构派发保留一切更低的位置, `c-way` 逼右边的 `D (Tβ α) _` 在 `α` 有真值时保留层号 `ω` 的源位置, 于是判定 `α` (`base`).
探针序列 `hα α` 逐项严格递增 (`strict`: `0, 1, …, n, ω+n+2, ω+n+3, …` 或 `0, 1, 2, …`), 不是退化结点. 不否定 `Compat D` 可满足.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCompatDlLPO where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst₂)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext; R; ⌜_⌝)
open import OCF.Lean.YiLamFold using (Lw; Lw-tw; VΛ)
import OCF.Lean.YiDlFold as W
open import OCF.Lean.YiUniIf using (At; IsKeep)
open import OCF.Lean.YiUniNegBase using (Found; LPO; hit; or-l; hit-found)
open import OCF.Lean.YiCrossIface
open import OCF.Lean.YiCompatDlNeg using
  (ʰ→Q; ʰ→P; trR; trL; reflR; PR; pre; viaΩ; ιP; ιP-lev; pr-tw; sucs; sucs-lgl; ωR; ωR-lgl; Ωω)
```

## 1 探针

`Tβ α` 有层号 `ω` 的槽位当且仅当 `α` 有真值 (`found→at`, `keep→found`).

```agda
sucω : ℕ → R
sucω zero = ωR
sucω (suc n) = G.suc (sucω n)

pk : Bool → ℕ → R
pk true n = G.suc (sucω n)
pk false n = sucs n

hα : (ℕ → Bool) → ℕ → R
hα α n = pk (hit α n) n

dω : ∀ n m → Dn zero (sucs n) (sucω m)
dω n zero = n , inj₁ refl
dω n (suc m) = inj₂ (dω n m)

dstep : ∀ a b n → Dn zero (pk b n) (pk (a ∨ b) (suc n))
dstep true true n = inj₁ refl
dstep false true n = inj₁ refl
dstep true false n = inj₂ (inj₂ (dω n n))
dstep false false n = inj₁ refl

strict : ∀ α n → Dn zero (hα α n) (hα α (suc n))
strict α n = dstep (α n) (hit α n) n

sucω-lgl : ∀ n → Lgl zero (sucω n)
sucω-lgl zero = ωR-lgl
sucω-lgl (suc n) = sucω-lgl n

pk-lgl : ∀ b n → Lgl zero (pk b n)
pk-lgl true n = sucω-lgl n
pk-lgl false n = sucs-lgl n

hα-lgl : ∀ α → Lgl zero (G.lim (hα α))
hα-lgl α = (λ n → inj₂ (strict α n)) , (λ n → pk-lgl (hit α n) n)

Tβ : (ℕ → Bool) → LF
Tβ α = ⌜ G.lim (hα α) ⌝

slotω : ∀ k → Σ (Pre ⌜ G.suc (sucω k) ⌝) λ s → lev ⌜ G.suc (sucω k) ⌝ s ≡ Ωω
slotω zero = inj₁ tt , refl
slotω (suc k) = inj₂ (proj₁ (slotω k)) , proj₂ (slotω k)

at-pk : ∀ b k → b ≡ true → Σ (Pre ⌜ pk b k ⌝) λ s → lev ⌜ pk b k ⌝ s ≡ Ωω
at-pk true k refl = slotω k

notlim : ∀ k {f} → ⌜ sucs k ⌝ ≡ lim f → ⊥
notlim zero ()
notlim (suc k) ()

finlev : ∀ k (s : Pre ⌜ sucs k ⌝) → lev ⌜ sucs k ⌝ s ≡ Ωω → ⊥
finlev zero () e
finlev (suc k) (inj₁ _) e = notlim k e
finlev (suc k) (inj₂ s) e = finlev k s e

pk-at : ∀ b k (s : Pre ⌜ pk b k ⌝) → lev ⌜ pk b k ⌝ s ≡ Ωω → b ≡ true
pk-at true k s e = refl
pk-at false k s e with finlev k s e
... | ()

found→at : ∀ α → Found α → At (Tβ α) Ωω
found→at α (n , e) with at-pk (hit α (suc n)) (suc n) (or-l (α n) (hit α n) e)
... | s , p = (suc n , s) , p

keep→found : ∀ α (s : Pre (Tβ α)) → lev (Tβ α) s ≡ Ωω → Found α
keep→found α (n , s) e = hit-found α n (pk-at (hit α n) n s e)

decide : ∀ α (w : Way (Tβ α) Ωω) → (Found α → IsKeep w) → Found α ⊎ (Found α → ⊥)
decide α (keep s e) c = inj₁ (keep→found α s e)
decide α fold c = inj₂ c
```

## 2 `tw 2` 里的位置与部件

`qα α`: 层号 `Tβ α`; `rω`: 层号 `ω`.

```agda
qα : (ℕ → Bool) → Pre (tw 2)
qα α = G.suc (G.lim (hα α)) , hα-lgl α , inj₁ tt

rω : Pre (tw 2)
rω = G.suc ωR , ωR-lgl , inj₁ tt

keepOf : ∀ {m j m′ j′} {p : Pre m} {e : lev m p ≡ j} {w : Way m′ j′} → WayR (keep p e) w → IsKeep w
keepOf kk = tt

keep-subst : ∀ {m j m′ j′} {w : Way m j} (e₁ : m ≡ m′) (e₂ : j ≡ j′) → IsKeep w → IsKeep (subst₂ Way e₁ e₂ w)
keep-subst refl refl k = k
```

## 3 推出 LPO

```agda
module _ (D : ∀ k K → Ext k K) (S : Compat D) where
  open Compat S
  open W.Fold D using (cmpw)

  descend : ∀ {K} {V : Lw K} → PR V → ∀ {m} {x : Ext m K} {m′ K′} {V′ : Lw K′} {x′ : Ext m′ K′} →
    C V x V′ x′ → Σ (Ext m (tw 2)) λ y → C (Lw-tw 2) y V′ x′
  descend pre c = _ , c
  descend (viaΩ η l p) c = descend p (c-LΩ c η l)

  base : ∀ {m} {y : Ext m (tw 2)} {K′} {V′ : Lw K′} {m′} {x′ : Ext m′ K′} →
    (t : (ℕ → Bool) → Pre K′) → (∀ α → lev K′ (t α) ≡ Tβ α) → (r′ : Pre K′) → lev K′ r′ ≡ Ωω →
    C (Lw-tw 2) y V′ x′ → LPO
  base {K′ = K′} {V′ = V′} t et r′ er c α =
    decide α (subst₂ Way (et α) er (cmpw V′ (t α) r′)) (λ fd → keep-subst (et α) er (h fd))
    where
    c₂ = c-cmp (c-LΩ c (G.suc (G.lim (hα α))) (hα-lgl α)) (inj₁ tt) (t α) (sym (et α))
           (ʰ→Q (Tβ α) K′ (t α) (trR (sym (et α)) (reflR (G.lim (hα α)))))
    h : Found α → IsKeep (cmpw V′ (t α) r′)
    h fd = keepOf (c-way c₂ (inj₂ (proj₁ (found→at α fd))) r′ (trans (proj₂ (found→at α fd)) (sym er))
      (ʰ→P (Tβ α) (proj₁ (found→at α fd)) K′ r′
        (trL (sym (proj₂ (found→at α fd))) (trR (sym er) (reflR ωR)))))

  kill : ∀ {K} {V : Lw K} {K′} {V′ : Lw K′} → PR V → PR V′ →
    ∀ {m} {x : Ext m K} {m′} {x′ : Ext m′ K′} → C V x V′ x′ → LPO
  kill p p′ c =
    base (λ α → ιP p′ (qα α)) (λ α → ιP-lev p′ (qα α)) (ιP p′ rω) (ιP-lev p′ rω) (proj₂ (descend p c))

  lpo-tw : ∀ n j {m m′} {x : Ext m (tw (suc (suc n)))} {x′ : Ext m′ (tw (suc (suc j)))} →
    C (Lw-tw (suc (suc n))) x (Lw-tw (suc (suc j))) x′ → LPO
  lpo-tw n j = kill (pr-tw n) (pr-tw j)

  lpo-Λ : ∀ n {m m′} {x : Ext m (tw (suc (suc n)))} {x′ : Ext m′ Λ} → C (Lw-tw (suc (suc n))) x VΛ x′ → LPO
  lpo-Λ n c = lpo-tw n 0 (c-Rl c 2)

  lpo-ΛΛ : ∀ {m m′} {x : Ext m Λ} {x′ : Ext m′ Λ} → C VΛ x VΛ x′ → LPO
  lpo-ΛΛ c = lpo-tw 0 0 (c-Rl (c-Ll c 2) 2)
```
