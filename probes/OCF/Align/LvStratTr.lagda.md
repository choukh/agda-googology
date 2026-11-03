# 分层的 $\approx$: 沿 $j\approx j'$ 的搬运 (底座)

> 底座, 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). `tr` 与 `res` 在 [LvStratBase](LvStratBase.lagda.md): 对两个层号的结构递归, 不看证据, 所以对原始的树也是总函数. 这里是它们的规格, **只在地板上**: `resOK`: 可容许路径搬得过去, 搬回来的函数把地板送进地板. `trOK`: 可容许的树搬过去还可容许, 层号 $\approx$. 用到的前提: 上一阶段的 `tr-A` (节点层在低层), 两侧 `Rp` (不同的搬运结果落在同一分支上).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvStratTr where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; at; toLv; Tree; limᵢ; up; intoL; outL)
open import OCF.Align.LvStratBase using (tr; res; mapI; Fl; module Leaf; Stage)

module TrSpec (St : Stage) where
  open Stage St
  open Leaf fl

  out-into : ∀ k r y → outL k r (intoL k r y) ≡ y
  out-into (suc k)    (inj₁ _) y = refl
  out-into (suc k)    (inj₂ r) y = out-into k r y
  out-into (lim f)    (n , r)  y = out-into (f n) r y
  out-into (limᴼ k g) (inj₁ (inj₁ _)) y = refl
  out-into (limᴼ k g) (inj₁ (inj₂ r)) y = out-into k r y
  out-into (limᴼ k g) (inj₂ (x , r))  y = out-into (g x) r y

  record ResOK (a b : Lv) (r : Pre a) : Set where
    constructor rok
    field
      r′  : Pre b
      bk  : Ordᴸ (at b r′) → Ordᴸ (at a r)
      eqv : res a b r ≡ just (r′ , bk)
      adm : Adm b r′
      at≈ : at a r ≈ᴮ at b r′
      bk∈ : ∀ y → A (at b r′) y → A (at a r) (bk y) × toLv (bk y) ≈ᴮ toLv y
  open ResOK

  -- 分支: 搬运的结果落在正确的分支上. 这里用 `Rp`
  br≈ : ∀ {k k′ h h′} → Lw k → Rp (limᴼ k′ h′) → limᴼ k h ≈ᴮ limᴼ k′ h′ → ∀ x → A k x →
        A k′ (tr k k′ x) × h x ≈ᴮ h′ (tr k k′ x)
  br≈ {k} {k′} {h} {h′} lk (rb , rr) e x ax with o≈-inv lk e | tr-A lk (proj₁ (o≈-inv lk e)) x ax
  ... | ke , u , v | ax′ , tx with u x ax
  ...   | y , ay , ty , qy =
    ax′ , ≈ᴮ-trans qy (rr y (tr k k′ x) (A⊆B k′ y ay) (A⊆B k′ _ ax′) (≈ᴮ-trans (≈ᴮ-sym ty) tx))

  resOK : ∀ {a b} → Lo a → Rp b → a ≈ᴮ b → ∀ r → Adm a r → ResOK a b r
  resOK {suc a} {suc b} lo rp (s≈ e) (inj₁ _) _ = rok (inj₁ tt) (tr b a) refl tt e bk∈′
    where
    bk∈′ : ∀ y → A b y → A a (tr b a y) × toLv (tr b a y) ≈ᴮ toLv y
    bk∈′ y ay = proj₁ (tr-A (A→Lw b y ay) (≈ᴮ-sym e) y ay) , ≈ᴮ-sym (proj₂ (tr-A (A→Lw b y ay) (≈ᴮ-sym e) y ay))
  resOK {suc a} {suc b} lo rp (s≈ e) (inj₂ r) d with resOK lo rp e r d
  ... | rok r′ bk eqv ad ae bi =
    rok (inj₂ r′) bk (cong (mapI {b} {at a r} inj₂ (at (suc b)) (λ _ → refl)) eqv) ad ae bi
  resOK {lim f} {lim g} lo rp (l≈ h) (n , r) d with resOK (lo n) (rp n) (h n) r d
  ... | rok r′ bk eqv ad ae bi =
    rok (n , r′) bk (cong (mapI {g n} {at (f n) r} (n ,_) (at (lim g)) (λ _ → refl)) eqv) ad ae bi
  resOK {limᴼ k h} {limᴼ k′ h′} lo rp e (inj₁ (inj₁ _)) _ =
    rok (inj₁ (inj₁ tt)) (tr k′ k) refl tt ke bk∈′
    where
    ke = proj₁ (o≈-inv (proj₁ lo) e)
    bk∈′ : ∀ y → A k′ y → A k (tr k′ k y) × toLv (tr k′ k y) ≈ᴮ toLv y
    bk∈′ y ay = proj₁ (tr-A (A→Lw k′ y ay) (≈ᴮ-sym ke) y ay) , ≈ᴮ-sym (proj₂ (tr-A (A→Lw k′ y ay) (≈ᴮ-sym ke) y ay))
  resOK {limᴼ k h} {limᴼ k′ h′} lo rp e (inj₁ (inj₂ r)) d
    with resOK (low-lo k (proj₁ lo)) (proj₁ (proj₂ (low-cx k′ (low≈ (proj₁ lo) (proj₁ (o≈-inv (proj₁ lo) e)))))) (proj₁ (o≈-inv (proj₁ lo) e)) r d
  ... | rok r′ bk eqv ad ae bi =
    rok (inj₁ (inj₂ r′)) bk (cong (mapI {k′} {_} (λ q → inj₁ (inj₂ q)) (at (limᴼ k′ h′)) (λ _ → refl)) eqv) ad ae bi
  resOK {limᴼ k h} {limᴼ k′ h′} lo rp e (inj₂ (x , r)) (ax , d)
    with br≈ (proj₁ lo) rp e x ax
  ... | ax′ , qx with resOK (proj₂ lo x ax) (proj₁ rp (tr k k′ x) (A⊆B k′ _ ax′)) qx r d
  ...   | rok r′ bk eqv ad ae bi =
    rok (inj₂ (tr k k′ x , r′)) bk (cong (mapI {h′ (tr k k′ x)} {_} (λ q → inj₂ (tr k k′ x , q)) (at (limᴼ k′ h′)) (λ _ → refl)) eqv) (ax′ , ad) ae bi

  tr-i : ∀ a b r (f : Low a r → Ordᴸ a) {r′ bk} → res a b r ≡ just (r′ , bk) →
         tr a b (limᵢ r f) ≡ limᵢ r′ (λ y → tr a b (f (intoL a r (bk (outL b r′ y)))))
  tr-i a b r f e with res a b r | e
  ... | _ | refl = refl

  trOK : ∀ {a b} → BL a → Lo a → Rp b → a ≈ᴮ b → (z : Ordᴸ a) → Tw a z → Rp (toLv z) →
         Tw b (tr a b z) × toLv z ≈ᴮ toLv (tr a b z)
  trOK bl lo rp e Tree.zero t rz = tt , z≈
  trOK bl lo rp e (Tree.suc x) t rz =
    let i = trOK bl lo rp e x t rz in proj₁ i , s≈ (proj₂ i)
  trOK bl lo rp e (Tree.lim h) t rz =
    (λ n → proj₁ (trOK bl lo rp e (h n) (t n) (rz n))) , l≈ (λ n → proj₂ (trOK bl lo rp e (h n) (t n) (rz n)))
  trOK {a} {b} bl lo rp e (limᵢ r f) (dr , tf) (rb , rr) with resOK lo rp e r dr
  ... | rok r′ bk eqv ad ate bi =
    subst (λ w → Tw b w × limᴼ (at a r) (λ y → toLv (f (intoL a r y))) ≈ᴮ toLv w) (sym (tr-i a b r f eqv))
      ((ad , twb) , b≈ l l′ ate u v)
    where
    l  = bl r dr
    l′ = low≈ l ate
    F : Ordᴸ (at b r′) → Ordᴸ a
    F y = f (intoL a r (bk y))
    IH : ∀ y → A (at b r′) y → Tw b (tr a b (F y)) × toLv (F y) ≈ᴮ toLv (tr a b (F y))
    IH y ay = let a₀ = proj₁ (bi y ay) in trOK bl lo rp e (f (intoL a r (bk y))) (tf _ a₀) (rb _ (A⊆B _ _ a₀))
    twb : ∀ y → A (at b r′) y → Tw b (tr a b (F (outL b r′ (intoL b r′ y))))
    twb y ay rewrite out-into b r′ y = proj₁ (IH y ay)
    tl : ∀ y → A (at b r′) y → toLv (F y) ≈ᴮ toLv (tr a b (F (outL b r′ (intoL b r′ y))))
    tl y ay rewrite out-into b r′ y = proj₂ (IH y ay)
    u : ∀ x → A (at a r) x → Σ (Ordᴸ (at b r′)) λ x′ → A (at b r′) x′ × toLv x ≈ᴮ toLv x′ ×
        toLv (f (intoL a r x)) ≈ᴮ toLv (tr a b (F (outL b r′ (intoL b r′ x′))))
    u x ax =
      let ax′ = proj₁ (tr-A l ate x ax)
          tx  = proj₂ (tr-A l ate x ax)
          y   = tr (at a r) (at b r′) x
          a₀  = proj₁ (bi y ax′)
          t₀  = proj₂ (bi y ax′)
      in y , ax′ , tx ,
         ≈ᴮ-trans (rr x (bk y) (A⊆B _ x ax) (A⊆B _ _ a₀) (≈ᴮ-trans tx (≈ᴮ-sym t₀))) (tl y ax′)
    v : ∀ x′ → A (at b r′) x′ → Σ (Ordᴸ (at a r)) λ x → A (at a r) x × toLv x ≈ᴮ toLv x′ ×
        toLv (f (intoL a r x)) ≈ᴮ toLv (tr a b (F (outL b r′ (intoL b r′ x′))))
    v y ay = bk y , proj₁ (bi y ay) , proj₂ (bi y ay) , tl y ay
  trOK {suc a} {suc b} bl lo rp (s≈ e) (up d x) t rz = trOK (bl-suc bl) lo rp e x t rz
  trOK {lim f} {lim g} bl lo rp (l≈ h) (up n x) t rz = trOK (bl-lim n bl) (lo n) (rp n) (h n) x t rz
  trOK {limᴼ k h} {limᴼ .k h′} bl lo rp e@(o≈ _) (up x t) (ax , tt′) rz =
    let ax′ = proj₁ (br≈ (proj₁ lo) rp e x ax)
        qx  = proj₂ (br≈ (proj₁ lo) rp e x ax)
        i   = trOK (bl-o bl ax) (proj₂ lo x ax) (proj₁ rp (tr k k x) (A⊆B k _ ax′)) qx t tt′ rz
    in (ax′ , proj₁ i) , proj₂ i
  trOK {limᴼ k h} {limᴼ k′ h′} bl lo rp e@(b≈ _ _ _ _ _) (up x t) (ax , tt′) rz =
    let ax′ = proj₁ (br≈ (proj₁ lo) rp e x ax)
        qx  = proj₂ (br≈ (proj₁ lo) rp e x ax)
        i   = trOK (bl-o bl ax) (proj₂ lo x ax) (proj₁ rp (tr k k′ x) (A⊆B k′ _ ax′)) qx t tt′ rz
    in (ax′ , proj₁ i) , proj₂ i
```
