# 判决的规格: 两个判决的相似 (底座)

> 底座, 不含记号. 结论写在 [VerdictSpec](VerdictSpec.lagda.md). [InaccThetaEq](InaccThetaEq.lagda.md) 的 `ψ≃` 比较同一个 `S` 下的两个输入; 这里把左右的 `S` 分开, 节点条件 `ND` 拆成左右两份, 判决的正确性换成 [VerdictSpecBase](VerdictSpecBase.lagda.md) 的 `CVx`. 证明的骨架逐字, 新东西只在穿透的情形: 搬运 `b` 可以是 `coe⁺`, 要 `TL⁺`, `TR⁺` 说它尊重 `Eq`. 取 `S′ = S`, 判决都字面正确时回到原来的定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.VerdictSpecTwo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import Data.Maybe using (Maybe; just; nothing)
open import OCF.Align.InaccFloorTree using (Sib; Mode; upM; verdict; chM; module PF)
open import OCF.Align.InaccThetaRel using (module Leaf)
open import OCF.Align.VerdictSpecBase using (module Eqx; coe; coe⁺; coeP)
```

## §1 两侧的相似

`Eq₂₊` 与 `Eq₊` 只差 `i≃` 的两个节点条件: 左边要 `S` 的 `ND`, 右边要 `S′` 的 `ND`. `Eq k x y` 的 `x` 总是 `S` 这一侧的树, `y` 总是 `S′` 这一侧的树. `LRo` 只看左边, 与原来一样.

```agda
module Two (S S′ : Sib) (B₀ : Ordᴸ zero → Set) where
  open Leaf B₀ public
  module L = Eqx S B₀
  module R = Eqx S′ B₀
  open L using (DB; Bs-nz; Bs-subst; Bs-coe; out-into; ≈≡; clash; SD; sd-id; sd∘ι) public

  Resp : (k : Lv) → (Ordᴸ k → Lv) → (Eqk : Ordᴸ k → ∀ {k′} → Ordᴸ k′ → Set) → Set
  Resp k g Eqk = ∀ z z′ → Bs k z → Bs k z′ → Eqk z {k} z′ → g z ≈ᴮ g z′

  data Eq₊ (k : Lv)
           (RL : (r : Pre k) → Ordᴸ (at k r) → ∀ {k′} → Ordᴸ k′ → Set)
           (RD : (d : Dn k) → Ordᴸ (down k d) → ∀ {k′} → Ordᴸ k′ → Set)
           (LR : Pre k → Set) : Ordᴸ k → ∀ {k′} → Ordᴸ k′ → Set where
    z≃ : ∀ {k′} → Eq₊ k RL RD LR Tree.zero {k′} Tree.zero
    s≃ : ∀ {k′} {a} {b : Ordᴸ k′} → Eq₊ k RL RD LR a b → Eq₊ k RL RD LR (Tree.suc a) (Tree.suc b)
    l≃ : ∀ {k′} {f} {g : ℕ → Ordᴸ k′} → (∀ n → Eq₊ k RL RD LR (f n) (g n)) → Eq₊ k RL RD LR (Tree.lim f) (Tree.lim g)
    i≃ : ∀ {k′} {r} {r′ : Pre k′} {f} {f′} → L.ND k r → R.ND k′ r′ → at k r ≈ᴮ at k′ r′ → LR r →
         (∀ z z′ → Bs _ z → Bs _ z′ → RL r z z′ → Eq₊ k RL RD LR (f (intoL k r z)) (f′ (intoL k′ r′ z′))) →
         Eq₊ k RL RD LR (limᵢ r f) (limᵢ r′ f′)
    uˡ : ∀ {k′} {d} {x} {b : Ordᴸ k′} → DB k d → RD d (outD k d x) b → Eq₊ k RL RD LR (up d x) b
    uʳ : ∀ {k′} {a} {d} {y} → DB k′ d → Eq₊ k RL RD LR a (outD k′ d y) → Eq₊ k RL RD LR a {k′} (up d y)

  Eq  : (k : Lv) → Ordᴸ k → ∀ {k′} → Ordᴸ k′ → Set
  RLo : (k : Lv) (r : Pre k) → Ordᴸ (at k r) → ∀ {k′} → Ordᴸ k′ → Set
  RDn : (k : Lv) (d : Dn k) → Ordᴸ (down k d) → ∀ {k′} → Ordᴸ k′ → Set
  LRo : (k : Lv) → Pre k → Set
  LvR : Lv → Set

  Eq k x y = Eq₊ k (RLo k) (RDn k) (LRo k) x y

  RLo (suc k)    (inj₁ _)        z b = Eq k z b
  RLo (suc k)    (inj₂ r)        z b = RLo k r z b
  RLo (lim f)    (n , r)         z b = RLo (f n) r z b
  RLo (limᴼ k g) (inj₁ (inj₁ _)) z b = Eq k z b
  RLo (limᴼ k g) (inj₁ (inj₂ r)) z b = RLo k r z b
  RLo (limᴼ k g) (inj₂ (x , r))  z b = RLo (g x) r z b

  RDn (suc k)    _ z b = Eq k z b
  RDn (lim f)    n z b = Eq (f n) z b
  RDn (limᴼ k g) x z b = Eq (g x) z b

  LRo (suc k)    (inj₁ _)        = LvR k
  LRo (suc k)    (inj₂ r)        = LRo k r
  LRo (lim f)    (n , r)         = LRo (f n) r
  LRo (limᴼ k g) (inj₁ (inj₁ _)) = LvR k
  LRo (limᴼ k g) (inj₁ (inj₂ r)) = LRo k r
  LRo (limᴼ k g) (inj₂ (x , r))  = LRo (g x) r

  LvR zero       = ⊤
  LvR (suc k)    = LvR k
  LvR (lim f)    = ∀ n → LvR (f n)
  LvR (limᴼ k g) = LvR k × (∀ x → Bs k x → LvR (g x)) × Resp k g (λ z {k′} b → Eq k z {k′} b)

  R→Eq : ∀ k r {z : Ordᴸ (at k r)} {k′} {b : Ordᴸ k′} → RLo k r z b → Eq (at k r) z b
  R→Eq (suc k)    (inj₁ _)        d = d
  R→Eq (suc k)    (inj₂ r)        d = R→Eq k r d
  R→Eq (lim f)    (n , r)         d = R→Eq (f n) r d
  R→Eq (limᴼ k g) (inj₁ (inj₁ _)) d = d
  R→Eq (limᴼ k g) (inj₁ (inj₂ r)) d = R→Eq k r d
  R→Eq (limᴼ k g) (inj₂ (x , r))  d = R→Eq (g x) r d

  Eq→R : ∀ k r {z : Ordᴸ (at k r)} {k′} {b : Ordᴸ k′} → Eq (at k r) z b → RLo k r z b
  Eq→R (suc k)    (inj₁ _)        d = d
  Eq→R (suc k)    (inj₂ r)        d = Eq→R k r d
  Eq→R (lim f)    (n , r)         d = Eq→R (f n) r d
  Eq→R (limᴼ k g) (inj₁ (inj₁ _)) d = d
  Eq→R (limᴼ k g) (inj₁ (inj₂ r)) d = Eq→R k r d
  Eq→R (limᴼ k g) (inj₂ (x , r))  d = Eq→R (g x) r d

  lvr-at : ∀ i → LvR i → ∀ r → AdmB i r → LRo i r
  lvr-at (suc k)    w (inj₁ _) _ = w
  lvr-at (suc k)    w (inj₂ r) d = lvr-at k w r d
  lvr-at (lim f)    w (n , r)  d = lvr-at (f n) (w n) r d
  lvr-at (limᴼ k g) w (inj₁ (inj₁ _)) _ = proj₁ w
  lvr-at (limᴼ k g) w (inj₁ (inj₂ r)) d = lvr-at k (proj₁ w) r d
  lvr-at (limᴼ k g) w (inj₂ (x , r)) (a , d) = lvr-at (g x) (proj₁ (proj₂ w) x a) r d

  L→R : ∀ i r → AdmB i r → LRo i r → LvR (at i r)
  L→R (suc k)    (inj₁ _) _ w = w
  L→R (suc k)    (inj₂ r) d w = L→R k r d w
  L→R (lim f)    (n , r)  d w = L→R (f n) r d w
  L→R (limᴼ k g) (inj₁ (inj₁ _)) _ w = w
  L→R (limᴼ k g) (inj₁ (inj₂ r)) d w = L→R k r d w
  L→R (limᴼ k g) (inj₂ (x , r)) (a , d) w = L→R (g x) r d w

  uL : ∀ k {d} {x : DnT k d} {k′} {b : Ordᴸ k′} → DB k d → Eq (down k d) (outD k d x) b → Eq k (up d x) b
  uL (suc k)    db e = uˡ db e
  uL (lim f)    db e = uˡ db e
  uL (limᴼ k g) db e = uˡ db e

  i≃∘ : ∀ {k k′} {r : Pre k} {r′ : Pre k′} {g : Ordᴸ (at k r) → Ordᴸ k} {g′ : Ordᴸ (at k′ r′) → Ordᴸ k′} →
        L.ND k r → R.ND k′ r′ → at k r ≈ᴮ at k′ r′ → LRo k r →
        (∀ z z′ → Bs _ z → Bs _ z′ → Eq (at k r) z z′ → Eq k (g z) (g′ z′)) →
        Eq k (limᵢ r (λ y → g (outL k r y))) (limᵢ r′ (λ y → g′ (outL k′ r′ y)))
  i≃∘ {k} {k′} {r} {r′} {g} {g′} nd nd′ e lr h = i≃ nd nd′ e lr λ z z′ bz bz′ d →
    subst₂ (λ u v → Eq k (g u) (g′ v)) (sym (out-into k r z)) (sym (out-into k′ r′ z′))
           (h z z′ bz bz′ (R→Eq k r d))

  Ω≃ : ∀ {a b} → a ≈ᴮ b → L.LvG a → R.LvG b → LvR a → Eq a (Ω a) (Ω b)
  Ω≃ z≈ _ _ _ = s≃ z≃
  Ω≃ {suc a} {suc b} (s≈ e) ga gb ra =
    i≃ (tt , proj₁ ga , proj₂ ga) (tt , proj₁ gb , proj₂ gb) e ra
       (λ z z′ _ _ d → uˡ tt (uʳ tt d))
  Ω≃ (l≈ h) ga gb ra = l≃ (λ n → uˡ tt (uʳ tt (Ω≃ (h n) (ga n) (gb n) (ra n))))
  Ω≃ {limᴼ k g} {limᴼ .k g′} (o≈ h) ga gb ra =
    i≃ (tt , proj₁ ga , proj₁ (proj₂ ga)) (tt , proj₁ gb , proj₁ (proj₂ gb)) (≈ᴮ-refl k) (proj₁ ra)
       (λ z z′ bz bz′ d → uˡ bz (uʳ bz′
          (Ω≃ (≈ᴮ-trans (proj₂ (proj₂ ra) z z′ bz bz′ d) (h z′ bz′))
              (proj₂ (proj₂ ga) z bz) (proj₂ (proj₂ gb) z′ bz′) (proj₁ (proj₂ ra) z bz))))
```

## §2 加法与折叠

```agda
  subL : ∀ {a b k′} (e : a ≡ b) {z : Ordᴸ a} {z′ : Ordᴸ k′} → Eq a z z′ → Eq b (subst Ordᴸ e z) z′
  subL refl d = d

  subR : ∀ {a b k} (e : a ≡ b) {z : Ordᴸ k} {z′ : Ordᴸ a} → Eq k z z′ → Eq k z (subst Ordᴸ e z′)
  subR refl d = d

  add≃ : ∀ {k k′ l l′} {a : Ordᴸ l} {a′ : Ordᴸ l′} {σ : Sim k l} {σ′ : Sim k′ l′} {x : Ordᴸ k} {y : Ordᴸ k′} →
         L.LvT l → R.LvT l′ → LvR l → SD σ → SD σ′ → Eq l a a′ → Eq k x y → Eq l (add a σ x) (add a′ σ′ y)
  add≃ gl gl′ rl s s′ ea z≃ = ea
  add≃ gl gl′ rl s s′ ea (s≃ e) = s≃ (add≃ gl gl′ rl s s′ ea e)
  add≃ gl gl′ rl s s′ ea (l≃ h) = l≃ (λ n → add≃ gl gl′ rl s s′ ea (h n))
  add≃ {k} {k′} {l} {l′} {a} {a′} {σ} {σ′} gl gl′ rl s s′ ea (i≃ {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ e lr h) =
    i≃∘ {g = λ z → add a σ (f (intoL k r (subst Ordᴸ (proj₂ (σ r)) z)))}
        {g′ = λ z → add a′ σ′ (f′ (intoL k′ r′ (subst Ordᴸ (proj₂ (σ′ r′)) z)))}
      (L.nd-of l gl _ (s r (proj₁ nd))) (R.nd-of l′ gl′ _ (s′ r′ (proj₁ nd′)))
      (≈≡ (proj₂ (σ r)) (proj₂ (σ′ r′)) e) (lvr-at l rl _ (s r (proj₁ nd)))
      (λ z z′ bz bz′ d → add≃ gl gl′ rl s s′ ea
         (h _ _ (Bs-subst (proj₂ (σ r)) bz) (Bs-subst (proj₂ (σ′ r′)) bz′) (Eq→R k r (subL (proj₂ (σ r)) (subR (proj₂ (σ′ r′)) d)))))
  add≃ {suc k} {σ = σ} gl gl′ rl s s′ ea (uˡ {d = d} db e) = add≃ gl gl′ rl (sd∘ι (suc k) d σ s db) s′ ea e
  add≃ {lim f} {σ = σ} gl gl′ rl s s′ ea (uˡ {d = d} db e) = add≃ gl gl′ rl (sd∘ι (lim f) d σ s db) s′ ea e
  add≃ {limᴼ k g} {σ = σ} gl gl′ rl s s′ ea (uˡ {d = d} db e) = add≃ gl gl′ rl (sd∘ι (limᴼ k g) d σ s db) s′ ea e
  add≃ {k′ = suc k} {σ′ = σ} gl gl′ rl s s′ ea (uʳ {d = d} db e) = add≃ gl gl′ rl s (sd∘ι (suc k) d σ s′ db) ea e
  add≃ {k′ = lim f} {σ′ = σ} gl gl′ rl s s′ ea (uʳ {d = d} db e) = add≃ gl gl′ rl s (sd∘ι (lim f) d σ s′ db) ea e
  add≃ {k′ = limᴼ k g} {σ′ = σ} gl gl′ rl s s′ ea (uʳ {d = d} db e) = add≃ gl gl′ rl s (sd∘ι (limᴼ k g) d σ s′ db) ea e

  iter≃ : ∀ {i i′} {c : Ordᴸ i} {c′ : Ordᴸ i′} → L.LvT i → R.LvT i′ → LvR i → Eq i c c′ →
          ∀ n → Eq i (iter (c +_) Tree.zero n) (iter (c′ +_) Tree.zero n)
  iter≃ gi gi′ ri ec zero    = z≃
  iter≃ {i} {i′} gi gi′ ri ec (suc n) = add≃ gi gi′ ri (sd-id {i}) (sd-id {i′}) ec (iter≃ gi gi′ ri ec n)

  LG : Lv → Set
  LG a = L.LvT a × LvR a

  SpL : (a b : Lv) (r : Pre a) → Maybe (Σ (Pre b) λ r′ → Ordᴸ (at b r′) → Ordᴸ (at a r)) → Set
  SpL a b r nothing = ⊥
  SpL a b r (just (r̂ , back)) = AdmB b r̂ × (at a r ≈ᴮ at b r̂) × (∀ z → Bs _ z → Bs _ (back z)) ×
    (∀ {k′} {z} {t : Ordᴸ k′} → RLo b r̂ z t → RLo a r (back z) t)

  SpR : (b c : Lv) (r : Pre b) → Maybe (Σ (Pre c) λ r′ → Ordᴸ (at c r′) → Ordᴸ (at b r)) → Set
  SpR b c r nothing = ⊥
  SpR b c r (just (r̂ , back)) = AdmB c r̂ × (at b r ≈ᴮ at c r̂) × (∀ z → Bs _ z → Bs _ (back z)) ×
    (∀ {k} {u : Ordᴸ k} {z} → Eq k u z → Eq k u (back z))

  TL⁺ : ∀ a b → a ≈ᴮ b → LG a → LG b → L.P0 a → L.P0 b → ∀ {k′} {z : Ordᴸ a} {t : Ordᴸ k′} → Eq a z t → Eq b (coe⁺ a b z) t
  TLc : ∀ a b → a ≈ᴮ b → LG a → LG b → L.P0 a → L.P0 b → ∀ {k′} {z : Ordᴸ a} {t : Ordᴸ k′} → Eq a z t → Eq b (coe a b z) t
  spL : ∀ a b → a ≈ᴮ b → LG a → LG b → L.P0 a → L.P0 b → (r : Pre a) → AdmB a r → SpL a b r (coeP a b r)

  TL⁺ zero zero z≈ ga gb pa pb d = d
  TL⁺ (suc a) (suc b) e ga gb pa pb d = TLc (suc a) (suc b) e ga gb pa pb d
  TL⁺ (lim f) (lim f′) e ga gb pa pb d = TLc (lim f) (lim f′) e ga gb pa pb d
  TL⁺ (limᴼ k g) (limᴼ k′ g′) e ga gb pa pb d = TLc (limᴼ k g) (limᴼ k′ g′) e ga gb pa pb d

  TLc a b e ga gb pa pb z≃ = z≃
  TLc a b e ga gb pa pb (s≃ d) = s≃ (TLc a b e ga gb pa pb d)
  TLc a b e ga gb pa pb (l≃ h) = l≃ (λ n → TLc a b e ga gb pa pb (h n))
  TLc a b e ga gb pa pb {k′} (i≃ {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ ee lr h)
    with coeP a b r | spL a b e ga gb pa pb r (proj₁ nd)
  ... | just (r̂ , back) | d̂ , ê , bkB , tr =
    i≃ (L.nd-of b (proj₁ gb) r̂ d̂) nd′ (≈ᴮ-trans (≈ᴮ-sym ê) ee) (lvr-at b (proj₂ gb) r̂ d̂)
       (λ z z′ bz bz′ dd → subst (λ u → Eq b (coe a b (f (intoL a r (back u)))) (f′ (intoL k′ r′ z′)))
          (sym (out-into b r̂ z))
          (TLc a b e ga gb pa pb (h (back z) z′ (bkB z bz) bz′ (tr dd))))
  TLc (suc a) (suc b) (s≈ e) ga gb pa pb (uˡ db d) =
    uˡ tt (TL⁺ a b e (proj₂ (proj₁ ga) , proj₂ ga) (proj₂ (proj₁ gb) , proj₂ gb) pa pb d)
  TLc (lim f) (lim f′) (l≈ h) ga gb pa pb (uˡ {d = n} db d) =
    uˡ tt (TL⁺ (f n) (f′ n) (h n) (proj₂ (proj₁ ga) n , proj₂ ga n) (proj₂ (proj₁ gb) n , proj₂ gb n) (pa n) (pb n) d)
  TLc (limᴼ zero g) (limᴼ zero g′) (o≈ h) ga gb pa pb (uˡ {d = x} db d) =
    uˡ db (TL⁺ (g x) (g′ x) (h x db)
             (proj₂ (proj₂ (proj₁ ga)) x db , proj₁ (proj₂ (proj₂ ga)) x db)
             (proj₂ (proj₂ (proj₁ gb)) x db , proj₁ (proj₂ (proj₂ gb)) x db)
             (pa x db) (pb x db) d)
  TLc a b e ga gb pa pb (uʳ db d) = uʳ db (TLc a b e ga gb pa pb d)

  spL (suc a) (suc b) (s≈ e) ga gb pa pb (inj₁ _) d =
    tt , e , Bs-coe (≈ᴮ-sym e) ,
    (λ dd → TL⁺ b a (≈ᴮ-sym e) (proj₂ (proj₁ gb) , proj₂ gb) (proj₂ (proj₁ ga) , proj₂ ga) pb pa dd)
  spL (suc a) (suc b) (s≈ e) ga gb pa pb (inj₂ r) d
    with coeP a b r | spL a b e (proj₂ (proj₁ ga) , proj₂ ga) (proj₂ (proj₁ gb) , proj₂ gb) pa pb r d
  ... | just (r′ , bk) | d′ , e′ , bb , tr = d′ , e′ , bb , tr
  spL (lim f) (lim f′) (l≈ h) ga gb pa pb (n , r) d
    with coeP (f n) (f′ n) r | spL (f n) (f′ n) (h n) (proj₂ (proj₁ ga) n , proj₂ ga n) (proj₂ (proj₁ gb) n , proj₂ gb n) (pa n) (pb n) r d
  ... | just (r′ , bk) | d′ , e′ , bb , tr = d′ , e′ , bb , tr
  spL (limᴼ zero g) (limᴼ zero g′) (o≈ h) ga gb pa pb (inj₁ (inj₁ _)) d =
    tt , z≈ , (λ z bz → bz) , (λ dd → dd)
  spL (limᴼ zero g) (limᴼ zero g′) (o≈ h) ga gb pa pb (inj₂ (x , r)) (a , d)
    with coeP (g x) (g′ x) r
       | spL (g x) (g′ x) (h x a)
             (proj₂ (proj₂ (proj₁ ga)) x a , proj₁ (proj₂ (proj₂ ga)) x a)
             (proj₂ (proj₂ (proj₁ gb)) x a , proj₁ (proj₂ (proj₂ gb)) x a)
             (pa x a) (pb x a) r d
  ... | just (r′ , bk) | d′ , e′ , bb , tr = (a , d′) , e′ , bb , tr

  TR⁺ : ∀ b c → b ≈ᴮ c → R.LvT b → R.LvT c → R.P0 b → R.P0 c → ∀ {k} {t : Ordᴸ k} {z : Ordᴸ b} → Eq k t z → Eq k t (coe⁺ b c z)
  TRc : ∀ b c → b ≈ᴮ c → R.LvT b → R.LvT c → R.P0 b → R.P0 c → ∀ {k} {t : Ordᴸ k} {z : Ordᴸ b} → Eq k t z → Eq k t (coe b c z)
  spR : ∀ b c → b ≈ᴮ c → R.LvT b → R.LvT c → R.P0 b → R.P0 c → (r : Pre b) → AdmB b r → SpR b c r (coeP b c r)

  TR⁺ zero zero z≈ gb gc pb pc d = d
  TR⁺ (suc a) (suc b) e gb gc pb pc d = TRc (suc a) (suc b) e gb gc pb pc d
  TR⁺ (lim f) (lim f′) e gb gc pb pc d = TRc (lim f) (lim f′) e gb gc pb pc d
  TR⁺ (limᴼ k g) (limᴼ k′ g′) e gb gc pb pc d = TRc (limᴼ k g) (limᴼ k′ g′) e gb gc pb pc d

  TRc b c e gb gc pb pc z≃ = z≃
  TRc b c e gb gc pb pc (s≃ d) = s≃ (TRc b c e gb gc pb pc d)
  TRc b c e gb gc pb pc (l≃ h) = l≃ (λ n → TRc b c e gb gc pb pc (h n))
  TRc b c e gb gc pb pc {k} (i≃ {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ ee lr h)
    with coeP b c r′ | spR b c e gb gc pb pc r′ (proj₁ nd′)
  ... | just (r̂ , back) | d̂ , ê , bkB , tr =
    i≃ nd (R.nd-of c gc r̂ d̂) (≈ᴮ-trans ee ê) lr
       (λ z z′ bz bz′ dd → subst (λ u → Eq k (f (intoL k r z)) (coe b c (f′ (intoL b r′ (back u)))))
          (sym (R.out-into c r̂ z′))
          (TRc b c e gb gc pb pc (h z (back z′) bz (bkB z′ bz′) (Eq→R k r (tr (R→Eq k r dd))))))
  TRc b c e gb gc pb pc {suc k} (uˡ db d) = uˡ db (TRc b c e gb gc pb pc d)
  TRc b c e gb gc pb pc {lim f} (uˡ db d) = uˡ db (TRc b c e gb gc pb pc d)
  TRc b c e gb gc pb pc {limᴼ k g} (uˡ db d) = uˡ db (TRc b c e gb gc pb pc d)
  TRc (suc a) (suc b) (s≈ e) gb gc pb pc (uʳ db d) = uʳ tt (TR⁺ a b e (proj₂ gb) (proj₂ gc) pb pc d)
  TRc (lim f) (lim f′) (l≈ h) gb gc pb pc (uʳ {d = n} db d) =
    uʳ tt (TR⁺ (f n) (f′ n) (h n) (proj₂ gb n) (proj₂ gc n) (pb n) (pc n) d)
  TRc (limᴼ zero g) (limᴼ zero g′) (o≈ h) gb gc pb pc (uʳ {d = x} db d) =
    uʳ db (TR⁺ (g x) (g′ x) (h x db) (proj₂ (proj₂ gb) x db) (proj₂ (proj₂ gc) x db) (pb x db) (pc x db) d)

  spR (suc a) (suc b) (s≈ e) gb gc pb pc (inj₁ _) d =
    tt , e , Bs-coe (≈ᴮ-sym e) , (λ dd → TR⁺ b a (≈ᴮ-sym e) (proj₂ gc) (proj₂ gb) pc pb dd)
  spR (suc a) (suc b) (s≈ e) gb gc pb pc (inj₂ r) d
    with coeP a b r | spR a b e (proj₂ gb) (proj₂ gc) pb pc r d
  ... | just (r′ , bk) | d′ , e′ , bb , tr = d′ , e′ , bb , tr
  spR (lim f) (lim f′) (l≈ h) gb gc pb pc (n , r) d
    with coeP (f n) (f′ n) r | spR (f n) (f′ n) (h n) (proj₂ gb n) (proj₂ gc n) (pb n) (pc n) r d
  ... | just (r′ , bk) | d′ , e′ , bb , tr = d′ , e′ , bb , tr
  spR (limᴼ zero g) (limᴼ zero g′) (o≈ h) gb gc pb pc (inj₁ (inj₁ _)) d =
    tt , z≈ , (λ z bz → bz) , (λ dd → dd)
  spR (limᴼ zero g) (limᴼ zero g′) (o≈ h) gb gc pb pc (inj₂ (x , r)) (a , d)
    with coeP (g x) (g′ x) r
       | spR (g x) (g′ x) (h x a) (proj₂ (proj₂ gb) x a) (proj₂ (proj₂ gc) x a) (pb x a) (pc x a) r d
  ... | just (r′ , bk) | d′ , e′ , bb , tr = (a , d′) , e′ , bb , tr

  -- 判决的搬运尊重 `Eq`
  trkL : ∀ {j i} {r : Pre i} {b : Ordᴸ (at i r) → Ordᴸ j} → L.BT {j} {i} r b → j ≈ᴮ at i r → LG (at i r) → LG j →
         ∀ {k′} {z : Ordᴸ (at i r)} {t : Ordᴸ k′} → Eq (at i r) z t → Eq j (b z) t
  trkL (L.bl refl) _ _ _ d = d
  trkL (L.bc pa pj) e ga gj d = TL⁺ _ _ (≈ᴮ-sym e) ga gj pa pj d

  trkR : ∀ {j i} {r : Pre i} {b : Ordᴸ (at i r) → Ordᴸ j} → R.BT {j} {i} r b → j ≈ᴮ at i r → R.LvT (at i r) → R.LvT j →
         ∀ {k} {t : Ordᴸ k} {z : Ordᴸ (at i r)} → Eq k t z → Eq k t (b z)
  trkR (R.bl refl) _ _ _ d = d
  trkR (R.bc pa pj) e ga gj d = TR⁺ _ _ (≈ᴮ-sym e) ga gj pa pj d

  bsL : ∀ {j i} {r : Pre i} {b : Ordᴸ (at i r) → Ordᴸ j} → L.BT {j} {i} r b → j ≈ᴮ at i r → ∀ z → Bs _ z → Bs j (b z)
  bsL (L.bl refl) _ z bz = bz
  bsL (L.bc pa pj) e z bz = Bs-coe (≈ᴮ-sym e) z bz

  bsR : ∀ {j i} {r : Pre i} {b : Ordᴸ (at i r) → Ordᴸ j} → R.BT {j} {i} r b → j ≈ᴮ at i r → ∀ z → Bs _ z → Bs j (b z)
  bsR (R.bl refl) _ z bz = bz
  bsR (R.bc pa pj) e z bz = Bs-coe (≈ᴮ-sym e) z bz

  record Tg (i i′ : Lv) : Set where
    constructor tg
    field
      te : i ≈ᴮ i′
      gL : L.LvT i
      gR : R.LvT i′
      zL : L.Zt i
      zR : R.Zt i′
      rL : LvR i
  open Tg public

  chainL : ∀ k r (f : Low k r → Ordᴸ k) → ℕ → Ordᴸ (at k r)
  chainL k r f = iter (λ x → L.ψᵖ (chM k r) (f (intoL k r x))) (Ω (at k r))

  chainR : ∀ k r (f : Low k r → Ordᴸ k) → ℕ → Ordᴸ (at k r)
  chainR k r f = iter (λ x → R.ψᵖ (chM k r) (f (intoL k r x))) (Ω (at k r))

  ψ≃ : ∀ {k k′ i i′} (m : Mode k i) (m′ : Mode k′ i′) {x : Ordᴸ k} {y : Ordᴸ k′} → L.OK k m → R.OK k′ m′ → Tg i i′ →
       Eq k x y → Eq i (L.ψᵖ m x) (R.ψᵖ m′ y)
  chain≃ : ∀ {k k′} {r : Pre k} {r′ : Pre k′} {f : Low k r → Ordᴸ k} {f′ : Low k′ r′ → Ordᴸ k′} →
           L.ND k r → R.ND k′ r′ → at k r ≈ᴮ at k′ r′ → LRo k r → (at k r ≡ zero → ⊥) → (at k′ r′ ≡ zero → ⊥) →
           (∀ z z′ → Bs _ z → Bs _ z′ → RLo k r z z′ → Eq k (f (intoL k r z)) (f′ (intoL k′ r′ z′))) →
           ∀ n → Eq (at k r) (chainL k r f n) (chainR k′ r′ f′ n)

  ψ≃ m m′ ok ok′ t z≃ = Ω≃ (te t) (L.t→g _ (gL t)) (R.t→g _ (gR t)) (rL t)
  ψ≃ m m′ ok ok′ t (s≃ e) = l≃ (iter≃ (gL t) (gR t) (rL t) (ψ≃ m m′ ok ok′ t e))
  ψ≃ m m′ ok ok′ t (l≃ h) = l≃ (λ n → ψ≃ m m′ ok ok′ t (h n))
  ψ≃ {k} {k′} {i} {i′} m m′ ok ok′ t (i≃ {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ e lr h)
    with verdict S m r | L.okV k m ok r (proj₁ nd) | verdict S′ m′ r′ | R.okV k′ m′ ok′ r′ (proj₁ nd′)
  ... | _ | L.cvp r₁ b₁ a₁ j₁ t₁ | _ | R.cvp r₂ b₂ a₂ j₂ t₂ =
    i≃∘ {g = λ z → L.ψᵖ m (f (intoL k r (b₁ z)))} {g′ = λ z → R.ψᵖ m′ (f′ (intoL k′ r′ (b₂ z)))}
      (L.nd-of i (gL t) r₁ a₁) (R.nd-of i′ (gR t) r₂ a₂) (≈ᴮ-trans (≈ᴮ-sym j₁) (≈ᴮ-trans e j₂)) (lvr-at i (rL t) r₁ a₁)
      (λ z z′ bz bz′ d → ψ≃ m m′ ok ok′ t (h (b₁ z) (b₂ z′) (bsL {j = at k r} {r = r₁} {b = b₁} t₁ j₁ z bz) (bsR {j = at k′ r′} {r = r₂} {b = b₂} t₂ j₂ z′ bz′)
         (Eq→R k r {z = b₁ z} {k′ = at k′ r′} {b = b₂ z′}
           (trkR {j = at k′ r′} {r = r₂} {b = b₂} t₂ j₂ (R.lvt-at i′ (gR t) r₂ a₂) (proj₂ (proj₂ nd′)) {k = at k r} {t = b₁ z} {z = z′}
            (trkL {j = at k r} {r = r₁} {b = b₁} t₁ j₁ (L.lvt-at i (gL t) r₁ a₁ , L→R i r₁ a₁ (lvr-at i (rL t) r₁ a₁))
                        (proj₂ (proj₂ nd) , L→R k r (proj₁ nd) lr) {k′ = at i′ r₂} {z = z} {t = z′} d)))))
  ... | _ | L.cvp r₁ b₁ a₁ j₁ t₁ | _ | R.cvr kk = ⊥-elim (clash (te t) e r₁ j₁ a₁ kk)
  ... | _ | L.cvr kk | _ | R.cvp r₂ b₂ a₂ j₂ t₂ = ⊥-elim (clash (≈ᴮ-sym (te t)) (≈ᴮ-sym e) r₂ j₂ a₂ kk)
  ... | _ | L.cvr kk | _ | R.cvr kk′ =
    l≃ (λ n → ψ≃ m m′ ok ok′ t (h _ _ (Bs-nz _ n₀ _) (Bs-nz _ n₀′ _)
         (Eq→R k r (chain≃ {f = f} {f′ = f′} nd nd′ e lr n₀ n₀′ h n))))
    where
    n₀ = L.rise≠0 kk (zL t)
    n₀′ = R.rise≠0 kk′ (zR t)
  ψ≃ {suc k} m m′ ok ok′ t (uˡ {d = d} db e) = ψ≃ (upM (suc k) d m) m′ (L.okU (suc k) m ok d db) ok′ t e
  ψ≃ {lim f} m m′ ok ok′ t (uˡ {d = d} db e) = ψ≃ (upM (lim f) d m) m′ (L.okU (lim f) m ok d db) ok′ t e
  ψ≃ {limᴼ k g} m m′ ok ok′ t (uˡ {d = d} db e) = ψ≃ (upM (limᴼ k g) d m) m′ (L.okU (limᴼ k g) m ok d db) ok′ t e
  ψ≃ {k′ = suc k} m m′ ok ok′ t (uʳ {d = d} db e) = ψ≃ m (upM (suc k) d m′) ok (R.okU (suc k) m′ ok′ d db) t e
  ψ≃ {k′ = lim f} m m′ ok ok′ t (uʳ {d = d} db e) = ψ≃ m (upM (lim f) d m′) ok (R.okU (lim f) m′ ok′ d db) t e
  ψ≃ {k′ = limᴼ k g} m m′ ok ok′ t (uʳ {d = d} db e) = ψ≃ m (upM (limᴼ k g) d m′) ok (R.okU (limᴼ k g) m′ ok′ d db) t e

  chain≃ {k} {k′} {r} {r′} nd nd′ e lr n₀ n₀′ h zero =
    Ω≃ e (L.t→g _ (proj₂ (proj₂ nd))) (R.t→g _ (proj₂ (proj₂ nd′))) (L→R k r (proj₁ nd) lr)
  chain≃ {k} {k′} {r} {r′} {f} {f′} nd nd′ e lr n₀ n₀′ h (suc n) =
    let c  = L.chOK k r (proj₁ (proj₂ nd)) n₀
        c′ = R.chOK k′ r′ (proj₁ (proj₂ nd′)) n₀′
    in ψ≃ (chM k r) (chM k′ r′) (proj₁ c) (proj₁ c′)
          (tg e (proj₂ (proj₂ nd)) (proj₂ (proj₂ nd′)) (proj₂ c) (proj₂ c′) (L→R k r (proj₁ nd) lr))
          (h _ _ (Bs-nz _ n₀ _) (Bs-nz _ n₀′ _) (Eq→R k r (chain≃ {f = f} {f′ = f′} nd nd′ e lr n₀ n₀′ h n)))
```
