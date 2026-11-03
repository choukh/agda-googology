# 分层的 $\approx$: 层号上的序就是观测前序 (底座)

> 底座, 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). 由 [LevelKOrd](LevelKOrd.lagda.md) 改写. 差别: `limᵢ-l` 多带右侧的自相似 (`ZA-ψ` 要它); `suc-path`, `mono-lv` 带 `Tw`; `up` 在 `limᴼ` 层上不再是空情形.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStratOrd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; upM; verdict; chM)
open import OCF.Align.LvStratBase using (Stage)
open import OCF.Align.LvStratObs using (module Core)
```

## §1 低层节点的左右规则

低层的节点在一切观测下都还是低层的节点 (`rise≠low`). 所以右规则可以取地板里**任意**的元, 不只起点; 左规则逐分支. 这是 [InaccThetaMono](InaccThetaMono.lagda.md) 的 `limᵢ-l₀`, `limᵢ-r₀` 的一般形式.

```agda
module Ord (S : Sib) (St : Stage) where
  open Core S St public

  sub-sym : ∀ {a b} (e : a ≡ b) (z : Ordᴸ b) → subst Ordᴸ e (subst Ordᴸ (sym e) z) ≡ z
  sub-sym refl z = refl

  A-sub : ∀ {a b} (e : a ≡ b) {z : Ordᴸ a} → A a z → A b (subst Ordᴸ e z)
  A-sub refl d = d

  Lw-sub : ∀ {a b} (e : a ≡ b) → Lw b → Lw a
  Lw-sub refl d = d

  limᵢ-l : ∀ {k k′} {r : Pre k} {f : Low k r → Ordᴸ k} {y : Ordᴸ k′} → Eq k′ y y → AdmB k r → Lw (at k r) →
           (∀ z → A (at k r) z → f (intoL k r z) ⊑ᵒ y) → (BL k′ → at k r ≺ᴬ toLv y) → limᵢ r f ⊑ᵒ y
  limᵢ-l ey d l K zy (idO {b = b} {b′ = b′}) (inj₁ (inj₁ _)) _ = zy b′
  limᵢ-l ey d l K zy (idO {b = b} {b′ = b′}) (inj₁ (inj₂ s)) ds = ≺→⊑ (zy b′) s ds
  limᵢ-l ey d l K zy (idO {b = b} {b′ = b′}) (inj₂ (x , q)) (ax , dq) = K x ax (idO {b = b} {b′ = b′}) q dq
  limᵢ-l {k} {k′} {r} {f} {y} ey d l K zy (ψo {i = i} m m′ a b ti o) with verdict S m r | okV k m a r d
  ... | _ | cvp r₁ e₁ a₁ =
    limᵢ-l {r = r₁} {f = λ w → ψᵖ m (f (intoL k r (subst Ordᴸ e₁ (outL i r₁ w))))} {y = ψᵖ m′ y}
      (ψ≃ m′ m′ b b (tgOf ti) ey) a₁ (Lw-sub e₁ l)
      (λ z az → subst (λ u → ψᵖ m (f (intoL k r (subst Ordᴸ e₁ u))) ⊑ᵒ ψᵖ m′ y) (sym (out-into i r₁ z))
                      (λ o′ → K _ (A-sub e₁ az) (ψo m m′ a b ti o′)))
      (λ bi → ZA-ψ m′ b (proj₁ (proj₂ ti)) ey _ (Lw-sub e₁ l) bi) o
  ... | _ | cvr kk = ⊥-elim (rise≠low kk (proj₁ (proj₂ ti)) l)
  limᵢ-l {k} {k′} {r} {f} {y} ey d l K zy (addo {l = l₀} {l′ = l′} {a = a₀} {a′ = a′} {σ = σ} {σ′ = σ′} o ea g g′ rl s s′ za) =
    let e = proj₂ (σ r) in
    limᵢ-l {r = proj₁ (σ r)} {f = λ w → add a₀ σ (f (intoL k r (subst Ordᴸ e (outL l₀ (proj₁ (σ r)) w))))} {y = add a′ σ′ y}
      (add≃ g′ g′ (proj₂ (proj₂ za)) s′ s′ (proj₁ (proj₂ za)) ey)
      (s r d) (Lw-sub e l)
      (λ z az → subst (λ u → add a₀ σ (f (intoL k r (subst Ordᴸ e u))) ⊑ᵒ add a′ σ′ y) (sym (out-into l₀ (proj₁ (σ r)) z))
                      (λ o′ → K _ (A-sub e az) (addo o′ ea g g′ rl s s′ za)))
      (λ bl → ZA-add {σ = σ′} s′ (proj₁ za) ey _ (Lw-sub e l) bl) o

  limᵢ-r₀ : ∀ {k₀ k} {x : Ordᴸ k₀} {r : Pre k} {f : Low k r → Ordᴸ k} → AdmB k r → Lw (at k r) →
            ∀ z → A (at k r) z → x ⊑ᵒ f (intoL k r z) → x ⊑ᵒ limᵢ r f
  limᵢ-r₀ l′ l z az p (idO {b = b} {b′ = b′}) q dq with p (idO {b = b} {b′ = b′}) q dq
  ... | viaᴬ s ds e = viaᴬ (inj₂ (z , s)) (az , ds) e
  limᵢ-r₀ {k = k} {x = x} {r = r} {f = f} d l z az p (ψo {i = i} m m′ a b ti o) with verdict S m′ r | okV k m′ b r d
  ... | _ | cvp r₁ e₁ a₁ =
    let z′ = subst Ordᴸ (sym e₁) z in
    limᵢ-r₀ {x = ψᵖ m x} {r = r₁} {f = λ w → ψᵖ m′ (f (intoL k r (subst Ordᴸ e₁ (outL i r₁ w))))} a₁ (Lw-sub e₁ l) z′ (A-sub (sym e₁) az)
      (subst (λ u → ψᵖ m x ⊑ᵒ ψᵖ m′ (f (intoL k r u)))
             (sym (trans (cong (subst Ordᴸ e₁) (out-into i r₁ z′)) (sub-sym e₁ z)))
             (λ o′ → p (ψo m m′ a b ti o′))) o
  ... | _ | cvr kk = ⊥-elim (rise≠low kk (proj₁ (proj₂ ti)) l)
  limᵢ-r₀ {k = k} {x = x} {r = r} {f = f} d l z az p (addo {l′ = l′} {a = a₀} {a′ = a′} {σ = σ} {σ′ = σ′} o ea g g′ rl s s′ za) =
    let e = proj₂ (σ′ r)
        z′ = subst Ordᴸ (sym e) z in
    limᵢ-r₀ {x = add a₀ σ x} {r = proj₁ (σ′ r)} {f = λ w → add a′ σ′ (f (intoL k r (subst Ordᴸ e (outL l′ (proj₁ (σ′ r)) w))))}
      (s′ r d) (Lw-sub e l) z′ (A-sub (sym e) az)
      (subst (λ u → add a₀ σ x ⊑ᵒ add a′ σ′ (f (intoL k r u)))
             (sym (trans (cong (subst Ordᴸ e) (out-into l′ (proj₁ (σ′ r)) z′)) (sub-sym e z)))
             (λ o′ → p (addo o′ ea g g′ rl s s′ za))) o
```

## §2 层号的序给观测前序

`cxL`, `cxB`: `Cx` 进极限与分支. `suc-path`: 后继的字面前驱, 对 $y$ 递归. 路径落在 `limᴼ` 的参数层时, 用 `par` 把它搬进某个分支: 这正是 `<-decᴬ` 用的同一步. `mono-lv` 对 $x$ 递归. 第 $<k$ 层的节点都穿透, 所以 `limᵢ-l`, `limᵢ-r₀` 够用.

```agda
  cxL : ∀ {f : ℕ → Lv} → Cx (lim f) → ∀ n → Cx (f n)
  cxL (w , rp , mn) n = proj₂ w n , rp n , mn n

  cxB : ∀ {k} {g : Ordᴸ k → Lv} → Cx (limᴼ k g) → ∀ z → A k z → Cx (g z)
  cxB {k} (w , rp , mn) z az = proj₂ (proj₂ w) z az , proj₁ rp z (A⊆B k z az) , proj₁ mn z az

  suc-path : ∀ {a a′} → BL a → BL a′ → (t : Ordᴸ a) (y : Ordᴸ a′) → Tw a t → Tw a′ y → Cx (toLv y) →
             (q : Pre (toLv y)) → Adm (toLv y) q → toLv t ≈ᴮ at (toLv y) q → Tree.suc t ⊑ᵒ y
  suc-path b b′ t (Tree.suc y) tt′ ty c (inj₁ _) _ e = ≃→⊑ᵒ (s≃ (T→E b b′ t y tt′ ty (proj₁ (proj₂ c)) e))
  suc-path b b′ t (Tree.suc y) tt′ ty c (inj₂ q) d e = suc-r (suc-path b b′ t y tt′ ty c q d e)
  suc-path b b′ t (Tree.lim h) tt′ ty c (n , q) d e = lim-r n (suc-path b b′ t (h n) tt′ (ty n) (cxL c n) q d e)
  suc-path {a′ = a′} b b′ t (limᵢ r f) tt′ (dr , tf) c (inj₂ (z , q)) (az , d) e =
    limᵢ-r₀ (Adm→B a′ r dr) (b′ r dr) z az (suc-path b b′ t (f (intoL a′ r z)) tt′ (tf z az) (cxB c z az) q d e)
  suc-path {a′ = a′} b b′ t (limᵢ r f) tt′ (dr , tf) c (inj₁ (inj₁ _)) _ e with proj₁ (proj₂ (proj₁ c))
  ... | x₀ , ax , viaᴬ q₂ d₂ e₂ , _ =
    limᵢ-r₀ (Adm→B a′ r dr) (b′ r dr) x₀ ax
      (suc-path b b′ t (f (intoL a′ r x₀)) tt′ (tf x₀ ax) (cxB c x₀ ax) q₂ d₂ (≈ᴮ-trans e e₂))
  suc-path {a′ = a′} b b′ t (limᵢ r f) tt′ (dr , tf) c (inj₁ (inj₂ s)) d e with proj₁ (proj₂ (proj₁ c))
  ... | x₀ , ax , _ , h with h s d
  ...   | viaᴬ q₂ d₂ e₂ =
    limᵢ-r₀ (Adm→B a′ r dr) (b′ r dr) x₀ ax
      (suc-path b b′ t (f (intoL a′ r x₀)) tt′ (tf x₀ ax) (cxB c x₀ ax) q₂ d₂ (≈ᴮ-trans e e₂))
  suc-path {a′ = suc k} b b′ t (up d y) tt′ ty c q dq e = up-r (suc k) tt (suc-path b (bl-suc b′) t y tt′ ty c q dq e)
  suc-path {a′ = lim f} b b′ t (up n y) tt′ ty c q dq e = up-r (lim f) tt (suc-path b (bl-lim n b′) t y tt′ ty c q dq e)
  suc-path {a′ = limᴼ k g} b b′ t (up d y) tt′ (ad , ty) c q dq e =
    up-r (limᴼ k g) (A⊆B k d ad) (suc-path b (bl-o b′ ad) t y tt′ ty c q dq e)

  mono-lv : ∀ {a a′} → BL a → BL a′ → (x : Ordᴸ a) (y : Ordᴸ a′) → Tw a x → Tw a′ y → Cx (toLv x) → Cx (toLv y) → toLv x ⊑ᴬ toLv y → x ⊑ᵒ y
  mono-lv b b′ Tree.zero y tx ty cx cy σ = zero-l (T→E b′ b′ y y ty ty (proj₁ (proj₂ cy)) (≈ᴮ-refl _))
  mono-lv b b′ (Tree.suc t) y tx ty cx cy σ with σ (inj₁ tt) tt
  ... | viaᴬ q d e = suc-path b b′ t y tx ty cy q d e
  mono-lv b b′ (Tree.lim h) y tx ty cx cy σ = lim-l (λ n → mono-lv b b′ (h n) y (tx n) ty (cxL cx n) cy (λ r d → σ (n , r) d))
  mono-lv {a = a} b b′ (limᵢ r f) y (dr , tf) ty cx cy σ =
    limᵢ-l (T→E b′ b′ y y ty ty (proj₁ (proj₂ cy)) (≈ᴮ-refl _)) (Adm→B a r dr) (b r dr)
      (λ z az → mono-lv b b′ (f (intoL a r z)) y (tf z az) ty (cxB cx z az) cy (λ q dq → σ (inj₂ (z , q)) (az , dq)))
      (λ _ → σ (inj₁ (inj₁ tt)) tt)
  mono-lv {a = suc k} b b′ (up d x) y tx ty cx cy σ = up-l (suc k) tt (mono-lv (bl-suc b) b′ x y tx ty cx cy σ)
  mono-lv {a = lim f} b b′ (up n x) y tx ty cx cy σ = up-l (lim f) tt (mono-lv (bl-lim n b) b′ x y tx ty cx cy σ)
  mono-lv {a = limᴼ k g} b b′ (up d x) y (ad , tx) ty cx cy σ =
    up-l (limᴼ k g) (A⊆B k d ad) (mono-lv (bl-o b ad) b′ x y tx ty cx cy σ)
```

## §3 地板有向

`cmpA` 是层号上的比较. 有向性是唯一要它的地方.

```agda
  ⊑ᵒ-refl-A : ∀ j x → A j x → x ⊑ᵒ x
  ⊑ᵒ-refl-A j x ax = let b = lw→bl (A→Lw j x ax) ; c = cxA j x ax ; t = twA j x ax in mono-lv b b x x t t c c ⊑ᴬ-refl

  A-dir : ∀ j x y → A j x → A j y → Σ (Ordᴸ j) λ z → A j z × x ⊑ᵒ z × y ⊑ᵒ z
  A-dir j x y ax ay with cmpA j x y ax ay
  ... | injᵃ p = y , ay , mono-lv b b x y tx ty cx cy (≺→⊑ p) , ⊑ᵒ-refl-A j y ay
    where b = lw→bl (A→Lw j x ax) ; cx = cxA j x ax ; cy = cxA j y ay ; tx = twA j x ax ; ty = twA j y ay
  ... | injᵇ p = x , ax , ⊑ᵒ-refl-A j x ax , mono-lv b b y x ty tx cy cx (≺→⊑ p)
    where b = lw→bl (A→Lw j x ax) ; cx = cxA j x ax ; cy = cxA j y ay ; tx = twA j x ax ; ty = twA j y ay
  ... | injᶜ e = y , ay , mono-lv b b x y tx ty cx cy (≈⊑ e) , ⊑ᵒ-refl-A j y ay
    where b = lw→bl (A→Lw j x ax) ; cx = cxA j x ax ; cy = cxA j y ay ; tx = twA j x ax ; ty = twA j y ay
```
