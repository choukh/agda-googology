# 证书与阶段无关: 目标 $k$ 与层号的好性 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). `IsK K St`: 阶段 `St` 的低层恰是 $0,\dots,K-1$. 这时目标 $K$ 的折叠无条件合法, `Cert` 对任何好层号 $\theta$ 给出 $\psi_K(\Omega_\theta)$ 的证书. `Cert` 对 $K$ 没有递归, 也没有分情况: 所有情形都在 `Stage` 的字段里. `cx-tree`: 好且自相似的树的层号好, 这是下一层地板的来源.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKFin where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _≤?_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; <⇒≤; m≤n⇒m<n∨m≡n; suc-injective; <-irrefl; ≰⇒>)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; fin; upM; verdict; chM; natL; isN; finD; asN)
open import OCF.Align.LevelKBase using (NoO; Stage; module Leaf)
open import OCF.Align.LevelKClose using (module Close)
```

## §1 自然数的层

```agda
noo-nat : ∀ n → NoO (natL n)
noo-nat zero    = tt
noo-nat (suc n) = noo-nat n

at-nat : ∀ n (r : Pre (natL n)) → Σ ℕ λ m → m < n × at (natL n) r ≡ natL m
at-nat (suc n) (inj₁ _) = n , ≤-refl , refl
at-nat (suc n) (inj₂ r) with at-nat n r
... | m , p , e = m , ≤-trans p (<⇒≤ ≤-refl) , e

nat-path : ∀ {m n} → m < n → Σ (Pre (natL n)) λ r → at (natL n) r ≡ natL m
nat-path {m} {suc n} (s≤s p) with m≤n⇒m<n∨m≡n p
... | inj₂ refl = inj₁ tt , refl
... | inj₁ q with nat-path q
...   | r , e = inj₂ r , e

natL-inj : ∀ m n → natL m ≡ natL n → m ≡ n
natL-inj zero    zero    _ = refl
natL-inj (suc m) (suc n) e = cong suc (natL-inj m n (suc-lv e)) where
  suc-lv : ∀ {a b : Lv} → Lv.suc a ≡ Lv.suc b → a ≡ b
  suc-lv refl = refl
```

## §2 低层恰是 $0,\dots,K-1$ 的阶段

```agda
record IsK (K : ℕ) (St : Stage) : Set where
  open Stage St
  open Leaf fl
  field
    lw⇒ : ∀ j → Lw j → Σ ℕ λ m → m < K × j ≡ natL m
    ⇐lw : ∀ m → m < K → Lw (natL m)

module Fin (S : Sib) (St : Stage) where
  open Close S St public

  isN-nn : ∀ n {j} → natL n ≈ᴮ j → isN j n ≡ nothing → ⊥
  isN-nn zero z≈ ()
  isN-nn (suc n) (s≈ {b = j} e) eq with isN j n | isN-nn n e
  isN-nn (suc n) (s≈ {b = _} e) () | just refl | _
  ... | nothing | k = k refl

  fin-cv : ∀ j n → CV (finD j n)
  fin-cv j zero = cvr (λ ())
  fin-cv j (suc n) with isN j n in eq
  ... | just refl = cvp (inj₁ tt) refl tt
  ... | nothing with finD j n | fin-cv j n
  ...   | _ | cvp r e a = cvp (inj₂ r) e a
  ...   | _ | cvr k = cvr λ { (inj₁ _) _ q → isN-nn n q eq ; (inj₂ r) d q → k r d q }

  okF : ∀ k {i} n (e : i ≡ natL n) → OK k (fin n e)
  okF zero       n refl = tt
  okF (suc k)    n refl = (λ r d → fin-cv _ n) , okF k n refl
  okF (lim f)    n refl = (λ r d → fin-cv _ n) , (λ m → okF (f m) n refl)
  okF (limᴼ k g) n refl = (λ r d → fin-cv _ n) , (λ x _ → okF (g x) n refl)

  asN-nat : ∀ n → asN (natL n) ≡ just (n , refl)
  asN-nat zero    = refl
  asN-nat (suc n) rewrite asN-nat n = refl

  asN-no : ∀ j n → j ≡ natL n → asN j ≡ nothing → ⊥
  asN-no _ n refl eq with () ← trans (sym (asN-nat n)) eq

  okCh : ∀ k r n → at k r ≡ natL n → OK k (chM k r)
  okCh k r n e with asN (at k r) in eq
  ... | just (m , e′) = okF k m e′
  ... | nothing = ⊥-elim (asN-no _ n e eq)

  FinAt : Lv → Set
  FinAt i = ∀ r → Σ ℕ λ n → at i r ≡ natL n

  lvr-nat : ∀ n → LvR (natL n)
  lvr-nat zero    = tt
  lvr-nat (suc n) = lvr-nat n

  glv-nat : ∀ n → GLv (natL n)
  glv-nat zero    = tt
  glv-nat (suc n) = glv-nat n

  module K-stage (K : ℕ) (isK : IsK K St) where
    open IsK isK

    Zt-nat : ∀ n → K ≤ n → Zt (natL n)
    Zt-nat n K≤n j l with lw⇒ j l
    ... | m , m<K , refl with nat-path (≤-trans m<K K≤n)
    ...   | r , e = r , noo-adm (natL n) (noo-nat n) r , e

    ch-fin : ∀ k r n → at k r ≡ natL n → ChOK k r
    ch-fin k r n e with K ≤? n
    ... | yes p = inj₂ (okCh k r n e , subst Zt (sym e) (Zt-nat n p))
    ... | no q = inj₁ (subst Lw (sym e) (⇐lw n (≰⇒> q)))

    lvt-fin : ∀ i → FinAt i → LvT i
    lvt-fin zero       h = tt
    lvt-fin (suc k)    h =
      (λ r _ → ch-fin (suc k) r (proj₁ (h r)) (proj₂ (h r))) , lvt-fin k (λ r → h (inj₂ r))
    lvt-fin (lim f)    h =
      (λ r _ → ch-fin (lim f) r (proj₁ (h r)) (proj₂ (h r))) , (λ n → lvt-fin (f n) (λ r → h (n , r)))
    lvt-fin (limᴼ k g) h =
      (λ r _ → ch-fin (limᴼ k g) r (proj₁ (h r)) (proj₂ (h r))) ,
      lvt-fin k (λ r → h (inj₁ (inj₂ r))) ,
      (λ x _ → lvt-fin (g x) (λ r → h (inj₂ (x , r))))

    fin-nat : ∀ n → FinAt (natL n)
    fin-nat n r with at-nat n r
    ... | m , _ , e = m , e

    lvp-nat : ∀ n → LvP (natL n)
    lvp-nat n = t→g _ (lvt-fin (natL n) (fin-nat n)) , lvr-nat n , glv-nat n

    bl-K : BL (natL K)
    bl-K = noo-nat K , (λ r → let m , p , e = at-nat K r in subst Lw (sym e) (⇐lw m p))

    Ti-K : Ti (natL K)
    Ti-K = lvt-fin (natL K) (fin-nat K) , Zt-nat K ≤-refl , lvr-nat K

    ok-K : ∀ θ → OK θ (fin {i = natL K} K refl)
    ok-K θ = okF θ K refl

    GΩ-K : GoodT (natL K) (Ω (natL K))
    GΩ-K = Good-Ω (natL K) (lvp-nat K)

    -- 目标 K, 任何好的输入
    Good-ψᴷ : ∀ {k} {x : Ordᴸ k} → GoodT k x → Eq k x x → GoodT (natL K) (ψⁿ K x)
    Good-ψᴷ {k} g e = Good-ψ (fin K refl) (ok-K k) Ti-K GΩ-K g e

    Eq-ψᴷ : ∀ {k} {x : Ordᴸ k} → Eq k x x → Eq (natL K) (ψⁿ K x) (ψⁿ K x)
    Eq-ψᴷ {k} e = ψ≃ (fin K refl) (fin K refl) (ok-K k) (ok-K k) (tgOf Ti-K) e

    Good-F : ∀ θ → LvP θ → GoodT (natL K) (ψⁿ K (Ω θ))
    Good-F θ p@(g , r , _) = Good-ψᴷ (Good-Ω θ p) (Ω-self θ g r)

    -- 证书定理: 对 K 没有递归
    Cert : ∀ θ → LvP θ → WFᴬ (toLv (ψⁿ K (Ω θ)))
    Cert θ p = wf bl-K (Good-F θ p)

    cmp : ∀ θ → LvP θ → (p q : Pre (toLv (ψⁿ K (Ω θ)))) → Adm _ p → Adm _ q → Tri (at _ p) (at _ q)
    cmp θ h = <-decᴬ (toLv (ψⁿ K (Ω θ))) (Cert θ h)
```

## §3 好且自相似的树的层号好

这是 "下一层地板" 的来源: `Cx` 不提折叠, 但对折叠的输出是定理.

```agda
  i-self₂ : ∀ {k} {r : Pre k} {f : Low k r → Ordᴸ k} → Eq k (limᵢ r f) (limᵢ r f) →
            ∀ z z′ → Bs (at k r) z → Bs (at k r) z′ → PE (at k r) z z′ → Eq k (f (intoL k r z)) (f (intoL k r z′))
  i-self₂ {k} {r} (i≃ nd nd′ e lr h) z z′ b b′ d = h z z′ b b′ (PE→P k r d)

  rp-tree : ∀ {a} → BL a → (x : Ordᴸ a) → Eq a x x → Rp (toLv x)
  rp-tree b Tree.zero ex = tt
  rp-tree b (Tree.suc x) ex = rp-tree b x (s-inv ex)
  rp-tree b (Tree.lim h) ex = λ n → rp-tree b (h n) (l-inv ex n)
  rp-tree {a} b (limᵢ r f) ex =
    let l = proj₂ b r in
    (λ z bz → rp-tree b (f (intoL a r z)) (i-self ex z bz (inj₂ (l , refl , ≈ᴮ-refl _)))) ,
    (λ z z′ bz bz′ t → b≃ b b (i-self₂ ex z z′ bz bz′ (inj₂ (l , refl , t))))
  rp-tree {suc k} b (up d x) ex = rp-tree (bl-suc b) x (u-self (suc k) ex)
  rp-tree {lim f} b (up n x) ex = rp-tree (bl-lim n b) x (u-self (lim f) ex)
  rp-tree {limᴼ _ _} (() , _) (up d x) ex

  mn-tree : ∀ {a} → BL a → {x : Ordᴸ a} → GoodT a x → Mn (toLv x)
  mn-tree b gz = tt
  mn-tree b (gs g) = mn-tree b g
  mn-tree b (gl hg st) = λ n → mn-tree b (hg n)
  mn-tree {a} b (gi {r = r} {f = f} hb hm gΩ pos) =
    (λ z az → mn-tree b (hb z (Gi→L a r (inj₁ az)))) ,
    (λ z z′ az az′ σ →
       let bl = lw→bl (proj₂ b r)
       in hm z z′ (Gi→L a r (inj₁ az)) (Gi→L a r (inj₁ az′))
             (mono-lv bl bl z z′ (cxA _ z az) (cxA _ z′ az′) σ) (idO {b = b} {b′ = b}))
  mn-tree {suc k} b (gu db g) = mn-tree (bl-suc b) g
  mn-tree {lim f} b (gu {d = n} db g) = mn-tree (bl-lim n b) g
  mn-tree {limᴼ _ _} (() , _) (gu db g)

  cx-tree : ∀ {a} → BL a → {x : Ordᴸ a} → GoodT a x → Eq a x x → Cx (toLv x)
  cx-tree b {x} g e = wf b g , rp-tree b x e , mn-tree b g
```
