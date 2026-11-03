# 证书与阶段无关: 遗传的好树 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). 由 [InaccThetaGood](InaccThetaGood.lagda.md) 改写. **循环在这里断开.** 好输入 `Gi j z` 是 "地板元, 或者好且自相似且在 `Bs` 里". 地板 `A` 的定义不提 `Good`, 不提 `Eq`, 不提观测, 只提层号 (`LevelKBase` 的 `Cx`). 反过来 `Good-floor` 是定理: 地板元是好树, 分支单调由 `Mn` 与 `mono-lv` 给出. 所以 `Good → ⊑ᵒ → Eq → Bs → A` 这条依赖链在 `A` 处终止.

`pos` 改成存在式: 节点层是某个分支的字面前驱 (只在可取层号时要).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKGood where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; upM; verdict; chM)
open import OCF.Align.LevelKBase using (NoO; Stage)
open import OCF.Align.LevelKOrd using (module Ord)

module Good (S : Sib) (St : Stage) where
  open Ord S St public
```

## §2 好树

`gi`: 分支在好输入上好, 在好输入上单调, 起点是好输入, 可取层号时节点层是某个分支的字面前驱. 高层没有有向性: 只有链要走, 而链由 `chain-step` 自己单调.

```agda
  data Good₊ (k : Lv) (GL : (r : Pre k) → Ordᴸ (at k r) → Set) (GD : (d : Dn k) → Ordᴸ (down k d) → Set) : Ordᴸ k → Set where
    gz : Good₊ k GL GD Tree.zero
    gs : ∀ {a} → Good₊ k GL GD a → Good₊ k GL GD (Tree.suc a)
    gl : ∀ {h : ℕ → Ordᴸ k} → (∀ n → Good₊ k GL GD (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ k GL GD (Tree.lim h)
    gi : ∀ {r} {f : Low k r → Ordᴸ k} →
         (∀ z → GL r z → Good₊ k GL GD (f (intoL k r z))) →
         (∀ z z′ → GL r z → GL r z′ → z ⊑ᵒ z′ → f (intoL k r z) ⊑ᵒ f (intoL k r z′)) →
         GL r (Ω (at k r)) →
         (BL k → Σ (Ordᴸ (at k r)) λ x₀ → A (at k r) x₀ × at k r ≺ᴬ toLv (f (intoL k r x₀))) →
         Good₊ k GL GD (limᵢ r f)
    gu : ∀ {d} {x : DnT k d} → DB k d → GD d (outD k d x) → Good₊ k GL GD (up d x)

  GoodT : (k : Lv) → Ordᴸ k → Set
  GLo : (k : Lv) (r : Pre k) → Ordᴸ (at k r) → Set
  GDn : (k : Lv) (d : Dn k) → Ordᴸ (down k d) → Set
  Gi : (j : Lv) → Ordᴸ j → Set

  GoodT k = Good₊ k (GLo k) (GDn k)

  GLo (suc k)    (inj₁ _)        z = Gi k z
  GLo (suc k)    (inj₂ r)        z = GLo k r z
  GLo (lim f)    (n , r)         z = GLo (f n) r z
  GLo (limᴼ k g) (inj₁ (inj₁ _)) z = Gi k z
  GLo (limᴼ k g) (inj₁ (inj₂ r)) z = GLo k r z
  GLo (limᴼ k g) (inj₂ (x , r))  z = GLo (g x) r z

  GDn (suc k)    _ z = GoodT k z
  GDn (lim f)    n z = GoodT (f n) z
  GDn (limᴼ k g) x z = GoodT (g x) z

  Gi j z = A j z ⊎ (GoodT j z × Eq j z z × Bs j z)

  L→Gi : ∀ k r {z} → GLo k r z → Gi (at k r) z
  L→Gi (suc k)    (inj₁ _)        d = d
  L→Gi (suc k)    (inj₂ r)        d = L→Gi k r d
  L→Gi (lim f)    (n , r)         d = L→Gi (f n) r d
  L→Gi (limᴼ k g) (inj₁ (inj₁ _)) d = d
  L→Gi (limᴼ k g) (inj₁ (inj₂ r)) d = L→Gi k r d
  L→Gi (limᴼ k g) (inj₂ (x , r))  d = L→Gi (g x) r d

  Gi→L : ∀ k r {z} → Gi (at k r) z → GLo k r z
  Gi→L (suc k)    (inj₁ _)        d = d
  Gi→L (suc k)    (inj₂ r)        d = Gi→L k r d
  Gi→L (lim f)    (n , r)         d = Gi→L (f n) r d
  Gi→L (limᴼ k g) (inj₁ (inj₁ _)) d = d
  Gi→L (limᴼ k g) (inj₁ (inj₂ r)) d = Gi→L k r d
  Gi→L (limᴼ k g) (inj₂ (x , r))  d = Gi→L (g x) r d

  Gi-sub : ∀ {a b} (e : a ≡ b) {z : Ordᴸ a} → Gi a z → Gi b (subst Ordᴸ e z)
  Gi-sub refl d = d

  GiΩ-sub : ∀ {a b} (e : a ≡ b) → Gi b (Ω b) → Gi a (Ω a)
  GiΩ-sub refl d = d

  ⊑ᵒ-sub : ∀ {a b} (e : a ≡ b) {z z′ : Ordᴸ a} → z ⊑ᵒ z′ → subst Ordᴸ e z ⊑ᵒ subst Ordᴸ e z′
  ⊑ᵒ-sub refl p = p

  Gi→Bs : ∀ j {z} → Gi j z → Bs j z
  Gi→Bs j (inj₁ a) = A⊆B j _ a
  Gi→Bs j (inj₂ (_ , _ , b)) = b

  Gi→PE : ∀ j {z} → Gi j z → PE j z z
  Gi→PE j (inj₁ a) = inj₂ (A→Lw j _ a , refl , ≈ᴮ-refl _)
  Gi→PE j (inj₂ (_ , e , _)) = inj₁ e

  Gi→A : ∀ j {z} → Lw j → Gi j z → A j z
  Gi→A j l d = Gi→Bs j d l

  G→Gi : ∀ j {z} → (Lw j → ⊥) → GoodT j z → Eq j z z → Gi j z
  G→Gi j n g e = inj₂ (g , e , Bs-nz j n _)

  gi∘ : ∀ {k} {r : Pre k} {g : Ordᴸ (at k r) → Ordᴸ k} →
        (∀ z → GLo k r z → GoodT k (g z)) →
        (∀ z z′ → GLo k r z → GLo k r z′ → z ⊑ᵒ z′ → g z ⊑ᵒ g z′) →
        GLo k r (Ω (at k r)) →
        (BL k → Σ (Ordᴸ (at k r)) λ x₀ → A (at k r) x₀ × at k r ≺ᴬ toLv (g x₀)) →
        GoodT k (limᵢ r (λ y → g (outL k r y)))
  gi∘ {k} {r} {g} hb hm gΩ pos = gi
    (λ z d → subst (λ u → GoodT k (g u)) (sym (out-into k r z)) (hb z d))
    (λ z z′ d d′ p → subst₂ (λ u v → g u ⊑ᵒ g v) (sym (out-into k r z)) (sym (out-into k r z′)) (hm z z′ d d′ p))
    gΩ
    (λ b → let x₀ , ax , p = pos b in x₀ , ax , subst (λ u → at k r ≺ᴬ toLv (g u)) (sym (out-into k r x₀)) p)
```

## §3 自相似的反演

```agda
  s-inv : ∀ {k} {a : Ordᴸ k} → Eq k (Tree.suc a) (Tree.suc a) → Eq k a a
  s-inv (s≃ e) = e

  l-inv : ∀ {k} {h : ℕ → Ordᴸ k} → Eq k (Tree.lim h) (Tree.lim h) → ∀ n → Eq k (h n) (h n)
  l-inv (l≃ h) = h

  i-nd : ∀ {k} {r : Pre k} {f : Low k r → Ordᴸ k} → Eq k (limᵢ r f) (limᵢ r f) → AdmB k r × ND k r × LRo k r
  i-nd (i≃ nd nd′ e lr h) = proj₁ nd , nd , lr

  i-self : ∀ {k} {r : Pre k} {f : Low k r → Ordᴸ k} → Eq k (limᵢ r f) (limᵢ r f) →
           ∀ z → Bs (at k r) z → PE (at k r) z z → Eq k (f (intoL k r z)) (f (intoL k r z))
  i-self {k} {r} (i≃ nd nd′ e lr h) z b d = h z z b b (PE→P k r d)

  stripL : ∀ k {d} {x : DnT k d} {k′} {b : Ordᴸ k′} → Eq k (up d x) b → Eq (down k d) (outD k d x) b
  stripL (suc k) (uˡ db e) = e
  stripL (lim f) (uˡ db e) = e
  stripL (limᴼ k g) (uˡ db e) = e
  stripL k (uʳ db e) = uʳ db (stripL k e)

  stripR : ∀ k {k′} {d} {y : DnT k′ d} {a : Ordᴸ k} → Eq k a (up d y) → Eq k a (outD k′ d y)
  stripR k (uʳ db e) = e
  stripR (suc k) (uˡ db e) = uˡ db (stripR k e)
  stripR (lim f) (uˡ {d = n} db e) = uˡ db (stripR (f n) e)
  stripR (limᴼ k g) (uˡ {d = x} db e) = uˡ db (stripR (g x) e)

  u-self : ∀ k {d} {x : DnT k d} → Eq k (up d x) (up d x) → Eq (down k d) (outD k d x) (outD k d x)
  u-self k {d} e = stripR (down k d) (stripL k e)
```

## §4 地板元是好树

`Good-floor`: 层号好 (`Cx`) 的树是好树. `gl` 的步进与 `gi` 的单调都由 `mono-lv` 从层号读回观测前序. 这里没有 `Eq` 的传递性, 也没有新的比较.

```agda
  Good-floor : ∀ {a} → BL a → (x : Ordᴸ a) → Cx (toLv x) → GoodT a x
  Good-floor b Tree.zero c = gz
  Good-floor b (Tree.suc x) c = gs (Good-floor b x c)
  Good-floor b (Tree.lim h) c =
    gl (λ n → Good-floor b (h n) (cxL c n))
       (λ n → mono-lv b b (h n) (h (suc n)) (cxL c n) (cxL c (suc n)) (proj₁ (proj₁ c) n))
  Good-floor {a} b (limᵢ r f) c =
    let l  = proj₂ b r
        bl = lw→bl l
        mo = proj₂ (proj₂ (proj₂ c))
    in gi (λ z d → Good-floor b (f (intoL a r z)) (cxB c z (Gi→A (at a r) l (L→Gi a r d))))
          (λ z z′ d d′ p →
             let az  = Gi→A (at a r) l (L→Gi a r d)
                 az′ = Gi→A (at a r) l (L→Gi a r d′)
             in mono-lv b b (f (intoL a r z)) (f (intoL a r z′)) (cxB c z az) (cxB c z′ az′)
                  (mo z z′ az az′ (p (idO {b = bl} {b′ = bl}))))
          (Gi→L a r (inj₁ (ΩA (at a r) l)))
          (λ _ → let x₀ , ax , p , _ = proj₁ (proj₂ (proj₁ c)) in x₀ , ax , p)
  Good-floor {suc k} b (up d x) c = gu tt (Good-floor (bl-suc b) x c)
  Good-floor {lim f} b (up n x) c = gu tt (Good-floor (bl-lim n b) x c)
  Good-floor {limᴼ _ _} (() , _) (up d x) c

  Gi→Gd : ∀ j {z} → Gi j z → GoodT j z
  Gi→Gd j (inj₁ a) = Good-floor (lw→bl (A→Lw j _ a)) _ (cxA j _ a)
  Gi→Gd j (inj₂ (g , _ , _)) = g
```
