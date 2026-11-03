# Label (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Label](../../Align/Label.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Label where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Uniform using (Good; Good-add; Good-ψ; Good-ψ⁰; Good→HS; gz; gu; s-inv; l-inv)
open import OCF.Free.Lab.Correspond using (⟦_⟧; lvl; cert; gγ; diag-≅; Lab; diag-label; γᴱ; cof-ne)
open import OCF.Free.Lab.Closure using (cmpᵀ-refl; lt→<; eq→≡; <→lt)
open import OCF.Free.Lab.Bachmann using (module Generic; zs; ls; zl; sl; <sucT; fs<ᵀ)
import OCF.Free.Lab.NoCumsum as N
import OCF.Align.EBO as E
open import OCF.Free.Lab.Standard using (NF; n[]; Ctbl; c[]; c∷; _≤ᵀ_; <≤-trans; cofin; NF-pred; NF-fsn; Ctbl-pred; Ctbl-fsn; Ctbl-≤; Ctbl-cof; diag-NF; diag-Ctbl; []≤; Desc; d₀; dω; d₁)
```

```agda
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; pred; fsn; _<ᵀ_; []<)
       renaming (ψ to ψᵗ)
```

## §1 下标系统

```agda
record System : Set₁ where
  field
    Sub : T → Set
    lvS : ∀ {w} → Sub w → Ordᴵ
    A   : Ordᴵ
    inA : ∀ {w} (s : Sub w) → lvS s ≺ᴵ A
    S0  : (s : Sub []) → lvS s ≅ᴵ zero
    S1  : ∀ {w} (s : Sub w) → cof w ≡ c1 → Σ (Sub (pred w)) λ s′ → lvS s ≅ᴵ suc (lvS s′)
    Sω  : ∀ {w} (s : Sub w) → cof w ≡ cω → Σ (ℕ → Ordᴵ) λ g → Σ (∀ n → g n ⊑ᴵ g (suc n)) λ st →
          (lvS s ≅ᴵ lim g st) × (∀ n → Σ (Sub (fsn w n)) λ s′ → g n ≅ᴵ lvS s′)
    SΩ  : ∀ {w μ} → Sub w → cof w ≡ cΩ μ → ⊥
    Slt : ∀ {v u} (sv : Sub v) (su : Sub u) → cmpᵀ v u ≡ lt → lvS sv ≺ᴵ lvS su
    Seq : ∀ {v u} (sv : Sub v) (su : Sub u) → cmpᵀ v u ≡ eq → lvS sv ≅ᴵ lvS su
    s0  : Sub []

module GS (S : System) = Generic (System.Sub S) (System.lvS S) (System.A S) (System.inA S) (System.S0 S)
  (System.S1 S) (System.Sω S) (System.SΩ S) (System.Slt S) (System.Seq S)
```

## §2 树侧的三个小引理

```agda
Good-lift : ∀ {k ℓ} (r : k ◃ ℓ) {x : Ordᶜ k} → Good x → Good (lift r x)
Good-lift zero      g = gu g
Good-lift (suc r)   g = gu (Good-lift r g)
Good-lift (self n)  g = gu g
Good-lift (lim n r) g = gu (Good-lift r g)

top″ : ∀ {W A K} (q : W <ᴵ A) → W ≅ᴵ zero → {a : Ordᶜ K} {b : Ordᶜ A} → a ≅ b → ψ⁰ a ≅ lift (<→◃ q) (ψ q (λ r → r) b)
top″ q z≅ d = ≅-sym (lift-≅ (<→◃ q) (≅-sym (ψ⁰≅ψ {p = q} {σ = λ r → r} d)))

asLim : ∀ (X : Ordᶜ zero) {K} {G : ℕ → Ordᶜ K} → X ≅ lim G →
        Σ (ℕ → Ordᶜ zero) λ F → (X ≡ lim F) × (∀ n → F n ≅ G n)
asLim (lim F) e = F , refl , l-inv e
asLim zero ()
asLim (suc X) ()
asLim (limᵢ () f) e
asLim (up () x) e
```

## §3 下标的第 0 层树

```agda
module Tree (S : System) where
  open System S
  open GS S

  Good-node : ∀ {M} (ev : M ≺ᴵ A) {x : Ordᶜ A} → Good x → x ≅ x → Good (node ev x)
  Good-node (via e q) g r = Good-lift (<→◃ q) (Good-ψ g r)

  goodA  : ∀ {t} (d : 𝔸 t) → Good ⟦ d ⟧ᵃ
  goodAᴾ : ∀ {x} (d : 𝔸ᴾ x) → Good ⟦ d ⟧ᵖ
  goodA a[]       = gz
  goodA (a∷ x xs) = Good-add (goodAᴾ x) (⟦⟧ᴾ-refl x) (goodA xs)
  goodAᴾ (aψ s d) = Good-node (inA s) (goodA d) (⟦⟧-refl d)

  T⟦_⟧ : ∀ {t} → 𝔸 t → Ordᶜ zero
  T⟦ a[] ⟧            = zero
  T⟦ a∷ (aψ s d) xs ⟧ = ψ⁰ ⟦ d ⟧ᵃ + T⟦ xs ⟧

  goodT : ∀ {t} (d : 𝔸 t) → Good T⟦ d ⟧
  goodT a[]              = gz
  goodT (a∷ (aψ s d) xs) = Good-add (Good-ψ⁰ (goodA d) (⟦⟧-refl d)) (≅-refl⁰ _) (goodT xs)

  certT : ∀ {t} (d : 𝔸 t) → HS T⟦ d ⟧
  certT d = Good→HS (goodT d)

  top‴ : ∀ {M} (ev : M ≺ᴵ A) → M ≅ᴵ zero → ∀ {K} {a : Ordᶜ K} {b : Ordᶜ A} → a ≅ b → ψ⁰ a ≅ node ev b
  top‴ (via e q) h d = top″ q (≅ᴵ-trans (≅ᴵ-sym e) h) d

  T≅ : ∀ {t} → Ctbl t → (d : 𝔸 t) → T⟦ d ⟧ ≅ ⟦ d ⟧ᵃ
  T≅ c[] a[] = z≅
  T≅ (c∷ c) (a∷ (aψ s d) xs) = add-≅ (top‴ (inA s) (S0 s) (⟦⟧-refl d)) (T≅ c xs)

  nodeU : ∀ {M M′} (ev : M ≺ᴵ A) (ev′ : M′ ≺ᴵ A) → M ≅ᴵ M′ → ∀ {X Y : Ordᶜ A} → X ≅ Y → node ev X ≅ node ev′ Y
  nodeU (via e q) ev′ m d = lift-≅ (<→◃ q) (node-≅ ev′ {p = q} {σ = λ r → r} (≅ᴵ-trans (≅ᴵ-sym e) m) d)

  uniq  : ∀ {t} (d d′ : 𝔸 t) → ⟦ d ⟧ᵃ ≅ ⟦ d′ ⟧ᵃ
  uniqᴾ : ∀ {x} (d d′ : 𝔸ᴾ x) → ⟦ d ⟧ᵖ ≅ ⟦ d′ ⟧ᵖ
  uniq a[] a[] = z≅
  uniq (a∷ x xs) (a∷ x′ xs′) = add-≅ (uniqᴾ x x′) (uniq xs xs′)
  uniqᴾ (aψ {w = w} s d) (aψ s′ d′) = nodeU (inA s) (inA s′) (Seq s s′ (cmpᵀ-refl w)) (uniq d d′)
```

## §4 下一阶段

```agda
module Next (S : System) (β : T) (dβ : GS.𝔸 S β) (nβ : NF β) (cβ : Ctbl β) where
  open System S
  open GS S
  open Tree S

  Sub′ : T → Set
  Sub′ w = 𝔸 w × NF w × (w ≤ᵀ β)

  lvS′ : ∀ {w} → Sub′ w → Ordᴵ
  lvS′ (d , _ , _) = toLevel T⟦ d ⟧ (certT d)

  ctbl : ∀ {w} → Sub′ w → Ctbl w
  ctbl (_ , n , le) = Ctbl-≤ n cβ le

  oc   : ∀ (X : Ordᶜ zero) {u} (du : 𝔸 u) → NF u → Ctbl u → X ≅ ⟦ du ⟧ᵃ →
         ∀ {v} (dv : 𝔸 v) → NF v → Ctbl v → v <ᵀ u → T⟦ dv ⟧ ≺ X
  ocSh : ∀ (X : Ordᶜ zero) {u} (du : 𝔸 u) → NF u → Ctbl u → ∀ c → cof u ≡ c → Sh ⟦ du ⟧ᵃ c u → X ≅ ⟦ du ⟧ᵃ →
         ∀ {v} (dv : 𝔸 v) → NF v → Ctbl v → v <ᵀ u → T⟦ dv ⟧ ≺ X
  oc X {u} du nu cu h dv nv cv p = ocSh X du nu cu (cof u) refl (corr du) h dv nv cv p

  ocSh X {u = []} du nu cu c ce sh h dv nv cv ()
  ocSh X {u = x ∷ xs} du nu cu c0 ce sh h dv nv cv p = ⊥-elim (cof-ne x xs ce)
  ocSh X {u = x ∷ xs} du nu cu (cΩ μ) ce sh h dv nv cv p = ⊥-elim (Ctbl-cof cu ce)
  ocSh zero    {u = x ∷ xs} du nu cu c1 ce (Y , eY , _) h dv nv cv p = ⊥-elim (zs (≅-trans h eY))
  ocSh (lim F) {u = x ∷ xs} du nu cu c1 ce (Y , eY , _) h dv nv cv p = ⊥-elim (ls (≅-trans h eY))
  ocSh (suc X′) {u = u@(x ∷ xs)} du nu cu c1 ce (Y , eY , d′ , e′) h {v} dv nv cv p
    with <sucT (pred u) (subst (v <ᵀ_) (sym (E.pred-suc u ce)) p)
  ... | inj₁ q    = ≺s (oc X′ d′ (NF-pred nu ce) (Ctbl-pred cu) hX′ dv nv cv q)
    where hX′ = ≅-trans (s-inv (≅-trans h eY)) e′
  ... | inj₂ refl = ≺z (≅-trans (T≅ cv dv) (≅-trans (uniq dv d′) (≅-sym hX′)))
    where hX′ = ≅-trans (s-inv (≅-trans h eY)) e′
  ocSh zero    {u = x ∷ xs} du nu cu cω ce (G , eG , _) h dv nv cv p = ⊥-elim (zl (≅-trans h eG))
  ocSh (suc X′) {u = x ∷ xs} du nu cu cω ce (G , eG , _) h dv nv cv p = ⊥-elim (sl (≅-trans h eG))
  ocSh (lim F) {u = u@(x ∷ xs)} du nu cu cω ce (G , eG , hG) h dv nv cv p with cofin nu ce nv p
  ... | n , q = ≺l n (oc (F n) (proj₁ (hG n)) (NF-fsn nu ce n) (Ctbl-fsn cu ce n)
                         (≅-trans (l-inv (≅-trans h eG) n) (proj₂ (hG n))) dv nv cv q)
  ocSh (limᵢ () f) {u = x ∷ xs} du nu cu c1 ce sh h dv nv cv p
  ocSh (up () y)   {u = x ∷ xs} du nu cu c1 ce sh h dv nv cv p
  ocSh (limᵢ () f) {u = x ∷ xs} du nu cu cω ce sh h dv nv cv p
  ocSh (up () y)   {u = x ∷ xs} du nu cu cω ce sh h dv nv cv p
```

```agda
  OC< : ∀ {v u} (sv : Sub′ v) (su : Sub′ u) → v <ᵀ u → T⟦ proj₁ sv ⟧ ≺ T⟦ proj₁ su ⟧
  OC< sv@(dv , nv , _) su@(du , nu , _) p = oc T⟦ du ⟧ du nu (ctbl su) (T≅ (ctbl su) du) dv nv (ctbl sv) p

  Slt′ : ∀ {v u} (sv : Sub′ v) (su : Sub′ u) → cmpᵀ v u ≡ lt → lvS′ sv ≺ᴵ lvS′ su
  Slt′ {v} {u} sv su e = toLevel-≺ (certT (proj₁ sv)) (certT (proj₁ su)) (OC< sv su (lt→< v u e))

  TT : ∀ {v} (sv sv′ : Sub′ v) → T⟦ proj₁ sv ⟧ ≅ T⟦ proj₁ sv′ ⟧
  TT sv@(d , _ , _) sv′@(d′ , _ , _) = ≅-trans (T≅ (ctbl sv) d) (≅-trans (uniq d d′) (≅-sym (T≅ (ctbl sv′) d′)))

  Seq′ : ∀ {v u} (sv : Sub′ v) (su : Sub′ u) → cmpᵀ v u ≡ eq → lvS′ sv ≅ᴵ lvS′ su
  Seq′ {v} {u} sv su e with eq→≡ v u e
  ... | refl = toLevel-≅ (certT (proj₁ sv)) (certT (proj₁ su)) (TT sv su)
```

```agda
  sβ : Sub′ β
  sβ = dβ , nβ , inj₂ refl

  A′ : Ordᴵ
  A′ = suc (lvS′ sβ)

  inA′ : ∀ {w} (s : Sub′ w) → lvS′ s ≺ᴵ A′
  inA′ s@(d , n , inj₁ p)    = ≺-suc (Slt′ s sβ (<→lt p))
  inA′ s@(d , n , inj₂ refl) = via (Seq′ s sβ (cmpᵀ-refl β)) zero

  S0′ : (s : Sub′ []) → lvS′ s ≅ᴵ zero
  S0′ (a[] , _ , _) = z≅

  S1′ : ∀ {w} (s : Sub′ w) → cof w ≡ c1 → Σ (Sub′ (pred w)) λ s′ → lvS′ s ≅ᴵ suc (lvS′ s′)
  S1′ {w} s@(d , n , le) ce with subst (λ c → Sh ⟦ d ⟧ᵃ c w) ce (corr d)
  ... | Y , eY , d′ , e′ = s′ , toLevel-≅ (certT d) (hs (certT d′)) eT
    where
    s′ : Sub′ (pred w)
    s′ = d′ , NF-pred n ce , inj₁ (<≤-trans (E.pred-< w ce) le)
    eT : T⟦ d ⟧ ≅ suc T⟦ d′ ⟧
    eT = ≅-trans (T≅ (ctbl s) d) (≅-trans eY (s≅ (≅-trans e′ (≅-sym (T≅ (ctbl s′) d′)))))

  Sω′ : ∀ {w} (s : Sub′ w) → cof w ≡ cω → Σ (ℕ → Ordᴵ) λ g → Σ (∀ n → g n ⊑ᴵ g (suc n)) λ st →
        (lvS′ s ≅ᴵ lim g st) × (∀ n → Σ (Sub′ (fsn w n)) λ s′ → g n ≅ᴵ lvS′ s′)
  Sω′ {w} s@(d , n , le) ce with subst (λ c → Sh ⟦ d ⟧ᵃ c w) ce (corr d)
  ... | G , eG , hG with asLim T⟦ d ⟧ (≅-trans (T≅ (ctbl s) d) eG)
  ...   | F , eqF , hF =
    (λ m → toLevel (F m) (hl₁ hL m)) , (λ m → toLevel-⊑ (hl₁ hL m) (hl₁ hL (suc m)) (hl₂ hL m)) ,
    toLevel-≅ (certT d) hL (subst (T⟦ d ⟧ ≅_) eqF (≅-refl⁰ _)) ,
    λ m → sm m , toLevel-≅ (hl₁ hL m) (certT (proj₁ (hG m)))
                   (≅-trans (hF m) (≅-trans (proj₂ (hG m)) (≅-sym (T≅ (ctbl (sm m)) (proj₁ (hG m))))))
    where
    hL : HS (lim F)
    hL = subst HS eqF (certT d)
    sm : ∀ m → Sub′ (fsn w m)
    sm m = proj₁ (hG m) , NF-fsn n ce m , inj₁ (<≤-trans (fs<ᵀ ce m) le)

  SΩ′ : ∀ {w μ} → Sub′ w → cof w ≡ cΩ μ → ⊥
  SΩ′ s ce = Ctbl-cof (ctbl s) ce

  next : System
  next = record { Sub = Sub′ ; lvS = lvS′ ; A = A′ ; inA = inA′ ; S0 = S0′ ; S1 = S1′ ; Sω = Sω′ ; SΩ = SΩ′
                ; Slt = Slt′ ; Seq = Seq′ ; s0 = a[] , n[] , []≤ β }
```

## §5 对角线上的阶段

```agda
triv : System
triv = record
  { Sub = λ w → w ≡ []
  ; lvS = λ _ → zero
  ; A   = suc zero
  ; inA = λ _ → via z≅ zero
  ; S0  = λ _ → z≅
  ; S1  = λ { refl () }
  ; Sω  = λ { refl () }
  ; SΩ  = λ { refl () }
  ; Slt = λ { refl refl () }
  ; Seq = λ _ _ _ → z≅
  ; s0  = refl
  }

dγ : ∀ (S : System) k → System.Sub S (γᴱ k) → GS.𝔸 S (γᴱ (suc k))
dγ S k sγ = GS.a∷ {S = S} (GS.aψ {S = S} (System.s0 S) (GS.a∷ {S = S} (GS.aψ {S = S} sγ (GS.a[] {S = S})) (GS.a[] {S = S}))) (GS.a[] {S = S})

dγ₀ : GS.𝔸 triv (γᴱ 0)
dγ₀ = GS.a∷ {S = triv} (GS.aψ {S = triv} refl (GS.a[] {S = triv})) (GS.a[] {S = triv})

prev : ℕ → System
dB   : ∀ k → GS.𝔸 (prev k) (γᴱ k)
St   : ℕ → System
sγ   : ∀ k → System.Sub (St k) (γᴱ k)

St k = Next.next (prev k) (γᴱ k) (dB k) (diag-NF k) (diag-Ctbl k)
sγ k = Next.sβ (prev k) (γᴱ k) (dB k) (diag-NF k) (diag-Ctbl k)
prev zero    = triv
prev (suc k) = St k
dB zero    = dγ₀
dB (suc k) = dγ (St k) k (sγ k)
```

## §6 遗传标签

```agda
agreeT : ∀ k → ⟦ gγ k ⟧ ≅ Tree.T⟦_⟧ (prev k) (dB k)
agreeT zero    = ≅-refl⁰ _
agreeT (suc k) = ψ⁰-≅ (GS.Ω-node (St k) (System.inA (St k) (sγ k))
                        (toLevel-≅ (cert (gγ k)) (Tree.certT (prev k) (dB k)) (agreeT k)))

agree : ∀ k → ⟦ gγ (suc k) ⟧ ≅ GS.⟦_⟧ᵃ (St k) (dγ (St k) k (sγ k))
agree k = Tree.top‴ (St k) (System.inA (St k) (System.s0 (St k))) (System.S0 (St k) (System.s0 (St k)))
            (GS.Ω-node (St k) (System.inA (St k) (sγ k))
               (toLevel-≅ (cert (gγ k)) (Tree.certT (prev k) (dB k)) (agreeT k)))

γ-label : ∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))
γ-label k = GS.lab (St k) (N.γ (suc k)) (dγ (St k) k (sγ k)) (≅-trans (diag-≅ (suc k)) (agree k))

BTBO-label : Lab N.BTBOᴵ (E.EBOψ 2)
BTBO-label = diag-label γ-label
```

## §8 结论与边界
