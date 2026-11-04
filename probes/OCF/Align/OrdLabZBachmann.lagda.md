# Bachmann (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [Bachmann](Bachmann.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZBachmann where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂) 
open import OCF.BTBO using (module Ord-Ord; module Trich; injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZUniform using (≅-reflˡ; ≅-reflʳ; s-inv; l-inv; i-resp)
open import OCF.Align.OrdLabZCorrespond using (𝔾; g[]; g∷; gψ; gΩ; ⟦_⟧; lvl; cert; cof-ne; fs-rep; fs-ω; fsT-c1; fsn↓c-gt; γᴱ; gγ; diag-≅; Lab; l0; l1; lω)
open import OCF.Align.OrdLabZClosure using (Pen; cmpᵀ-refl; cmpᴾ-refl; <→lt; <ᴾ→lt; lt→<; lt→<ᴾ; eq→≡; eq→≡ᴾ; <ᵀ-trans; <ᴾ-trans; <◃; pen⁺; fsT₊-pen′)
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.EBO as E
open import OCF.Align.Bachmann public using (<sucT; <ᵀ-asym; <ᵀ-irrefl; Hd≤; Hd≤-desc; cofA≢c1; fs-gt; fs<ᵀ; gt→<; gt→<ᴾ; gt→≤; pen→<; rep<)
```

```agda
open Ord-Ord using (iter)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; cofP; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; natT; fsn; fsT; fsT0; γT; trm; dec; εₒ;
              _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
       renaming (ψ to ψᵗ)
```

## §5 通用形状定理: 证据由序的对应现场制造

```agda
clash : ∀ {i j} → j ≺ᴵ i → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ⊥
clash s (inj₁ t) = ≺ᴵ-irrefl (≺ᴵ-trans s t)
clash s (inj₂ c) = ≺ᴵ-irrefl (≺ᴵ-respʳ s c)

chainT : ∀ {j K} (q : j <ᴵ K) (f : U j (<→◃ q) → Ordᶜ K) → ℕ → Ordᶜ j
chainT {j} q f = iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j)

fold⁺ : ∀ {i k K j} {p : i <ᴵ k} {σ : Simᴵ K k} {q : j <ᴵ K} {f : U j (<→◃ q) → Ordᶜ K} →
        (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ψ p σ (limᵢ q f) ≡ lim (λ n → ψ p σ (f (into (<→◃ q) (chainT q f n))))
fold⁺ {p = p} {σ = σ} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

zs : ∀ {K K′} {Y : Ordᶜ K′} → 𝟎 {K} ≅ suc Y → ⊥
zs ()
ls : ∀ {K K′} {F : ℕ → Ordᶜ K} {Y : Ordᶜ K′} → lim F ≅ suc Y → ⊥
ls ()
zl : ∀ {K K′} {G : ℕ → Ordᶜ K′} → 𝟎 {K} ≅ lim G → ⊥
zl ()
sl : ∀ {K K′} {Y : Ordᶜ K} {G : ℕ → Ordᶜ K′} → suc Y ≅ lim G → ⊥
sl ()

noΩ0 : ∀ {j K} {q : j <ᴵ K} {f : U j (<→◃ q) → Ordᶜ K} (X : Ordᶜ zero) → X ≅ limᵢ q f → ⊥
noΩ0 zero ()
noΩ0 (suc X) ()
noΩ0 (lim F) ()
noΩ0 (limᵢ () f) e
noΩ0 (up () x) e
```

```agda
module Generic
  (Sub : T → Set)
  (lvS : ∀ {w} → Sub w → Ordᴵ)
  (A : Ordᴵ)
  (inA : ∀ {w} (s : Sub w) → lvS s ≺ᴵ A)
  (S0 : (s : Sub []) → lvS s ≅ᴵ zero)
  (S1 : ∀ {w} (s : Sub w) → cof w ≡ c1 → Σ (Sub (pred w)) λ s′ → lvS s ≅ᴵ suc (lvS s′))
  (Sω : ∀ {w} (s : Sub w) → cof w ≡ cω → Σ (ℕ → Ordᴵ) λ g → Σ (∀ n → g n ⊑ᴵ g (suc n)) λ st →
        (lvS s ≅ᴵ lim g st) × (∀ n → Σ (Sub (fsn w n)) λ s′ → g n ≅ᴵ lvS s′))
  (SΩ : ∀ {w μ} → Sub w → cof w ≡ cΩ μ → ⊥)
  (Slt : ∀ {v u} (sv : Sub v) (su : Sub u) → cmpᵀ v u ≡ lt → lvS sv ≺ᴵ lvS su)
  (Seq : ∀ {v u} (sv : Sub v) (su : Sub u) → cmpᵀ v u ≡ eq → lvS sv ≅ᴵ lvS su)
  where
```

```agda
  data 𝔸  : T → Set
  data 𝔸ᴾ : PT → Set
  data 𝔸 where
    a[] : 𝔸 []
    a∷  : ∀ {x xs} → 𝔸ᴾ x → 𝔸 xs → 𝔸 (x ∷ xs)
  data 𝔸ᴾ where
    aψ : ∀ {w a} → Sub w → 𝔸 a → 𝔸ᴾ (ψᵗ w a)

  node : ∀ {M} → M ≺ᴵ A → Ordᶜ A → Ordᶜ A
  node (via e q) x = lift (<→◃ q) (ψ q (λ r → r) x)

  ⟦_⟧ᵃ : ∀ {t} → 𝔸 t → Ordᶜ A
  ⟦_⟧ᵖ : ∀ {x} → 𝔸ᴾ x → Ordᶜ A
  ⟦ a[] ⟧ᵃ     = zero
  ⟦ a∷ x xs ⟧ᵃ = ⟦ x ⟧ᵖ + ⟦ xs ⟧ᵃ
  ⟦ aψ s d ⟧ᵖ  = node (inA s) ⟦ d ⟧ᵃ
```

```agda
  node-≅ : ∀ {M} (ev : M ≺ᴵ A) {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordᶜ k} {Y : Ordᶜ A} →
           i ≅ᴵ M → X ≅ Y → ψ p σ X ≅ node ev Y
  node-≅ (via e q) {p = p} {σ = σ} ei d =
    ≅-sym (lift-≅ (<→◃ q) (ψ-≅ {p = q} {σ = λ r → r} {p′ = p} {σ′ = σ} (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-sym ei)) (≅-sym d)))

  Ω-node : ∀ {M} (ev : M ≺ᴵ A) {i} → i ≅ᴵ M → Ω i ≅ node ev zero
  Ω-node (via e q) ei = ≅-sym (lift-≅ (<→◃ q) (Ω-≅ (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-sym ei))))

  node-refl : ∀ {M} (ev : M ≺ᴵ A) {X : Ordᶜ A} → X ≅ X → node ev X ≅ node ev X
  node-refl (via e q) d = lift-≅ (<→◃ q) (node-≅ (via e q) {p = q} {σ = λ r → r} (≅ᴵ-sym e) d)

  ⟦⟧-refl  : ∀ {t} (d : 𝔸 t) → ⟦ d ⟧ᵃ ≅ ⟦ d ⟧ᵃ
  ⟦⟧ᴾ-refl : ∀ {x} (d : 𝔸ᴾ x) → ⟦ d ⟧ᵖ ≅ ⟦ d ⟧ᵖ
  ⟦⟧-refl a[]       = z≅
  ⟦⟧-refl (a∷ x xs) = add-≅ (⟦⟧ᴾ-refl x) (⟦⟧-refl xs)
  ⟦⟧ᴾ-refl (aψ s d) = node-refl (inA s) (⟦⟧-refl d)
```

```agda
  Match : T → ∀ {K} → Ordᶜ K → Set
  Match s Y = Σ (𝔸 s) λ d → Y ≅ ⟦ d ⟧ᵃ

  Match-≡ : ∀ {s s′ K} {Y : Ordᶜ K} → s ≡ s′ → Match s′ Y → Match s Y
  Match-≡ refl m = m

  Sh : ∀ {K} → Ordᶜ K → Cof → T → Set
  Sh     X c0     t = X ≅ 𝟎 {A}
  Sh {K} X c1     t = Σ (Ordᶜ K) λ Y → (X ≅ suc Y) × Match (pred t) Y
  Sh {K} X cω     t = Σ (ℕ → Ordᶜ K) λ G → (X ≅ lim G) × (∀ n → Match (fsn t n) (G n))
  Sh {K} X (cΩ ν) t = Σ (Sub ν) λ sν → Σ Ordᴵ λ j → Σ (j <ᴵ K) λ q → Σ (U j (<→◃ q) → Ordᶜ K) λ f →
    (j ≅ᴵ lvS sν) × (X ≅ limᵢ q f) ×
    (∀ η (dη : 𝔸 η) (x : Ordᶜ j) → x ≅ ⟦ dη ⟧ᵃ → Match (fsT t η) (f (into (<→◃ q) x)))
```

```agda
  Sh-lift : ∀ c {t K ℓ} (r : K ◃ ℓ) {X : Ordᶜ K} → Sh X c t → Sh (lift r X) c t
  Sh-lift c0 r e = lift-≅ r e
  Sh-lift c1 r (Y , eY , d , ed) =
    lift r Y , lift-≅ r (≅-trans eY (s≅ (≅-sym (lift-≅ r (≅-reflˡ ed))))) , d , lift-≅ r ed
  Sh-lift cω r (G , eG , hG) =
    (λ n → lift r (G n)) , lift-≅ r (≅-trans eG (l≅ (λ n → ≅-sym (lift-≅ r (≅-reflˡ (proj₂ (hG n))))))) ,
    λ n → proj₁ (hG n) , lift-≅ r (proj₂ (hG n))
  Sh-lift (cΩ ν) {t} r {X} (sν , j , q , f , ej , eX , sp) =
    sν , j , q′ , f′ , ej ,
    lift-≅ r (≅-trans eX (lᵢ≅ (≅ᴵ-refl j) λ x y d →
      subst (λ w → f (into (<→◃ q) x) ≅ lift r (f (into (<→◃ q) w))) (sym (out-into (<→◃ q′) y))
            (≅-sym (lift-≅ r (≅-sym (i-resp (≅-sym eX) (R→≅ (<→◃ q) d))))))) ,
    λ η dη x ex → subst (λ w → Match (fsT t η) (lift r (f (into (<→◃ q) w)))) (sym (out-into (<→◃ q′) x))
                        (proj₁ (sp η dη x ex) , lift-≅ r (proj₂ (sp η dη x ex)))
    where
    q′ = <◃ q r
    f′ : U j (<→◃ q′) → Ordᶜ _
    f′ y = lift r (f (into (<→◃ q) (out (<→◃ q′) y)))
```

```agda
  leaf1 : ∀ {w ws W′} (s′ : Sub (pred (w ∷ ws))) → suc (lvS s′) ≅ᴵ W′ → cof (w ∷ ws) ≡ c1 →
          Sh (Ω W′) (cΩ (pred (w ∷ ws))) (ψᵗ (w ∷ ws) [] ∷ [])
  leaf1 {w} {ws} s′ (s≅ e′) ce = s′ , _ , zero , up zero , ≅ᴵ-sym e′ , Ω-refl _ ,
    λ η dη x ex → Match-≡ (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ce η) (dη , upˡ ex)

  leafω : ∀ {w ws W′} {g : ℕ → Ordᴵ} {st : ∀ n → g n ⊑ᴵ g (suc n)} →
          (∀ n → Σ (Sub (fsn (w ∷ ws) n)) λ s′ → g n ≅ᴵ lvS s′) → lim g st ≅ᴵ W′ → cof (w ∷ ws) ≡ cω →
          Sh (Ω W′) cω (ψᵗ (w ∷ ws) [] ∷ [])
  leafω {w} {ws} hg (l≅ h) ce = _ , Ω-refl _ , λ n →
    Match-≡ (E.fsn0-eq w ws n ce)
      (a∷ (aψ (proj₁ (hg n)) a[]) a[] , upˡ (Ω-node (inA (proj₁ (hg n))) (≅ᴵ-trans (≅ᴵ-sym (h n)) (proj₂ (hg n)))))

  leafC : ∀ {w ws} (sw : Sub (w ∷ ws)) (ev : lvS sw ≺ᴵ A) c → cof (w ∷ ws) ≡ c →
          Sh (node ev zero) (cofψ0 (w ∷ ws) c) (ψᵗ (w ∷ ws) [] ∷ [])
  leafC sw ev c0 ce = ⊥-elim (cof-ne _ _ ce)
  leafC sw (via e q) c1 ce with S1 sw ce
  ... | s′ , es = Sh-lift (cΩ _) (<→◃ q) (leaf1 s′ (≅ᴵ-trans (≅ᴵ-sym es) e) ce)
  leafC sw (via e q) cω ce with Sω sw ce
  ... | g , st , eg , hg = Sh-lift cω (<→◃ q) (leafω hg (≅ᴵ-trans (≅ᴵ-sym eg) e) ce)
  leafC sw ev (cΩ μ) ce = ⊥-elim (SΩ sw ce)

  leaf : ∀ {w} (sw : Sub w) (ev : lvS sw ≺ᴵ A) → Sh (node ev zero) (cofP (ψᵗ w [])) (ψᵗ w [] ∷ [])
  leaf {w = []} sw (via e q) =
    zero , lift-≅ (<→◃ q) (≅-trans (Ω-≅ (≅ᴵ-trans (≅ᴵ-sym e) (S0 sw))) (s≅ z≅)) , a[] , z≅
  leaf {w = w ∷ ws} sw ev = leafC sw ev (cof (w ∷ ws)) refl
```

```agda
  aRep : ∀ {x} → 𝔸ᴾ x → ∀ n → 𝔸 (replicate n x)
  aRep dx zero    = a[]
  aRep dx (suc n) = a∷ dx (aRep dx n)

  rep-≅ : ∀ {x K} {c : Ordᶜ K} (dx : 𝔸ᴾ x) → c ≅ ⟦ dx ⟧ᵖ → ∀ n → iter (c +_) zero n ≅ ⟦ aRep dx n ⟧ᵃ
  rep-≅ dx ec zero    = z≅
  rep-≅ dx ec (suc n) = add-≅ ec (rep-≅ dx ec n)

  penC : ∀ {w y ys ν} (sw : Sub w) (ev : lvS sw ≺ᴵ A) {X : Ordᶜ A} → cof (y ∷ ys) ≡ cΩ ν →
         Sh X (cΩ ν) (y ∷ ys) → Pen (cmpᵀ (sucT ν) w) → Sh (node ev X) (cΩ ν) (ψᵗ w (y ∷ ys) ∷ [])
  penC {w} {y} {ys} {ν} sw (via e q) {X} ce (sν , j , q′ , f , ej , eX , sp) pn
    with pen⁺ {p = q} {σ = λ r → r} {q = q′} {f = f} ej (≺ᴵ-respʳ (Slt sν sw (<→lt (pen→< ν w pn))) e)
  ... | j′ , e₁ , r , eqn = Sh-lift (cΩ ν) (<→◃ q)
    (sν , j′ , r , f′ , ≅ᴵ-trans (≅ᴵ-sym e₁) ej ,
     subst (λ Z → ψ q (λ r → r) X ≅ Z) eqn (ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl _) eX) ,
     λ η dη x ex → subst (λ u → Match (fsT (ψᵗ w (y ∷ ys) ∷ []) η) (ψ q (λ r → r) (f (into (<→◃ q′) (tr⁻ e₁ u)))))
                         (sym (out-into (<→◃ r) x))
                         (Match-≡ (fsT₊-pen′ w (y ∷ ys) ν (cof (y ∷ ys)) ce pn η)
                                  (a∷ (aψ sw (proj₁ (m η dη x ex))) a[] ,
                                   node-≅ (inA sw) {p = q} {σ = λ r → r} (≅ᴵ-sym e) (proj₂ (m η dη x ex)))))
    where
    f′ : U j′ (<→◃ r) → Ordᶜ _
    f′ y = ψ q (λ r → r) (f (into (<→◃ q′) (tr⁻ e₁ (out (<→◃ r) y))))
    m : ∀ η (dη : 𝔸 η) (x : Ordᶜ j′) → x ≅ ⟦ dη ⟧ᵃ → Match (fsT (y ∷ ys) η) (f (into (<→◃ q′) (tr⁻ e₁ x)))
    m η dη x ex = sp η dη (tr⁻ e₁ x) (tr⁻-≅ e₁ ex)
```

```agda
  chainM : ∀ {b ν j} (sν : Sub ν) {q : j <ᴵ A} {f : U j (<→◃ q) → Ordᶜ A} → j ≅ᴵ lvS sν →
           (∀ η (dη : 𝔸 η) (x : Ordᶜ j) → x ≅ ⟦ dη ⟧ᵃ → Match (fsT b η) (f (into (<→◃ q) x))) →
           ∀ n → Match (γT b ν n) (chainT q f n)
  chainM sν ej sp zero = a∷ (aψ sν a[]) a[] , Ω-node (inA sν) ej
  chainM sν {q} {f} ej sp (suc n) =
    a∷ (aψ sν (proj₁ m)) a[] , node-≅ (inA sν) {p = q} {σ = λ r → r} ej (proj₂ m)
    where
    mγ = chainM sν ej sp n
    m = sp _ (proj₁ mγ) (chainT q f n) (proj₂ mγ)

  gt-ev : ∀ {w ν} (sw : Sub w) (sν : Sub ν) → cmpᵀ (sucT ν) w ≡ gt → (lvS sw ≺ᴵ lvS sν) ⊎ (lvS sw ≅ᴵ lvS sν)
  gt-ev {w} {ν} sw sν em with gt→≤ ν w em
  ... | inj₁ p    = inj₁ (Slt sw sν (<→lt p))
  ... | inj₂ refl = inj₂ (Seq sw sν (cmpᵀ-refl w))

  gt-ev′ : ∀ {M N W′ j} → M ≅ᴵ W′ → j ≅ᴵ N → (M ≺ᴵ N) ⊎ (M ≅ᴵ N) → (W′ ≺ᴵ j) ⊎ (W′ ≅ᴵ j)
  gt-ev′ e ej (inj₁ s) = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym e) s) (≅ᴵ-sym ej))
  gt-ev′ e ej (inj₂ c) = inj₂ (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans c (≅ᴵ-sym ej)))

  foldC : ∀ {w y ys ν} (sw : Sub w) (ev : lvS sw ≺ᴵ A) {X : Ordᶜ A} → cof (y ∷ ys) ≡ cΩ ν →
          Sh X (cΩ ν) (y ∷ ys) → cmpᵀ (sucT ν) w ≡ gt → Sh (node ev X) cω (ψᵗ w (y ∷ ys) ∷ [])
  foldC {w} {y} {ys} {ν} sw (via e q) {X} ce (sν , j , q′ , f , ej , eX , sp) em = Sh-lift cω (<→◃ q)
    ((λ n → ψ q (λ r → r) (f (into (<→◃ q′) (chainT q′ f n)))) ,
     subst (λ Z → ψ q (λ r → r) X ≅ Z) (fold⁺ {p = q} {σ = λ r → r} {q = q′} {f = f} (gt-ev′ e ej (gt-ev sw sν em)))
           (ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl _) eX) ,
     λ n → Match-≡ (fs-gt w y ys ν ce em n)
             (a∷ (aψ sw (proj₁ (m n))) a[] , node-≅ (inA sw) {p = q} {σ = λ r → r} (≅ᴵ-sym e) (proj₂ (m n))))
    where
    m : ∀ n → Match (fsT (y ∷ ys) (γT (y ∷ ys) ν n)) (f (into (<→◃ q′) (chainT q′ f n)))
    m n = sp _ (proj₁ (chainM sν ej sp n)) (chainT q′ f n) (proj₂ (chainM sν ej sp n))
```

```agda
  corrΩ : ∀ {w y ys ν} (sw : Sub w) (ev : lvS sw ≺ᴵ A) {X : Ordᶜ A} → cof (y ∷ ys) ≡ cΩ ν →
          Sh X (cΩ ν) (y ∷ ys) → ∀ m → cmpᵀ (sucT ν) w ≡ m → Sh (node ev X) (cofψ₊ w ν m) (ψᵗ w (y ∷ ys) ∷ [])
  corrΩ sw ev ce sh lt em = penC sw ev ce sh (inj₁ em)
  corrΩ sw ev ce sh eq em = penC sw ev ce sh (inj₂ em)
  corrΩ sw ev ce sh gt em = foldC sw ev ce sh em

  corrψ : ∀ {w y ys} (sw : Sub w) (ev : lvS sw ≺ᴵ A) (db : 𝔸 (y ∷ ys)) → ∀ c → cof (y ∷ ys) ≡ c →
          Sh ⟦ db ⟧ᵃ c (y ∷ ys) → Sh (node ev ⟦ db ⟧ᵃ) (cofA w c) (ψᵗ w (y ∷ ys) ∷ [])
  corrψ sw ev db c0 ce sh = ⊥-elim (cof-ne _ _ ce)
  corrψ {w} {y} {ys} sw (via e q) db c1 ce (Y , eY , d′ , e′) = Sh-lift cω (<→◃ q)
    (iter (ψ q (λ r → r) Y +_) zero , ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl _) eY ,
     λ n → Match-≡ (fs-rep w y ys ce n)
             (aRep (aψ sw d′) n , rep-≅ (aψ sw d′) (node-≅ (inA sw) {p = q} {σ = λ r → r} (≅ᴵ-sym e) e′) n))
  corrψ {w} {y} {ys} sw (via e q) db cω ce (G , eG , hG) = Sh-lift cω (<→◃ q)
    ((λ n → ψ q (λ r → r) (G n)) , ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl _) eG ,
     λ n → Match-≡ (fs-ω w y ys ce n)
             (a∷ (aψ sw (proj₁ (hG n))) a[] , node-≅ (inA sw) {p = q} {σ = λ r → r} (≅ᴵ-sym e) (proj₂ (hG n))))
  corrψ {w} sw ev db (cΩ ν) ce sh = corrΩ sw ev ce sh (cmpᵀ (sucT ν) w) refl
```

```agda
  sum : ∀ {x y ys} (dx : 𝔸ᴾ x) (dys : 𝔸 (y ∷ ys)) → ∀ c → cof (y ∷ ys) ≡ c →
        Sh ⟦ dys ⟧ᵃ c (y ∷ ys) → Sh (⟦ dx ⟧ᵖ + ⟦ dys ⟧ᵃ) c (x ∷ y ∷ ys)
  sum dx dys c0 ce _ = ⊥-elim (cof-ne _ _ ce)
  sum dx dys c1 ce (Y , eY , d′ , e′) =
    ⟦ dx ⟧ᵖ + Y , add-≅ (⟦⟧ᴾ-refl dx) eY , a∷ dx d′ , add-≅ (⟦⟧ᴾ-refl dx) e′
  sum dx dys cω ce (G , eG , hG) =
    (λ n → ⟦ dx ⟧ᵖ + G n) , add-≅ (⟦⟧ᴾ-refl dx) eG ,
    λ n → a∷ dx (proj₁ (hG n)) , add-≅ (⟦⟧ᴾ-refl dx) (proj₂ (hG n))
  sum {x} {y} {ys} dx dys (cΩ ν) ce (sν , j , q , f , ej , eX , sp) =
    sν , j , q , (λ z → ⟦ dx ⟧ᵖ + f (coe (<→◃ q) (<→◃ q) z)) , ej , add-≅ (⟦⟧ᴾ-refl dx) eX ,
    λ η dη z ez → subst (λ w → Match (x ∷ fsT (y ∷ ys) η) (⟦ dx ⟧ᵖ + f (into (<→◃ q) w))) (sym (out-into (<→◃ q) z))
                        (a∷ dx (proj₁ (sp η dη z ez)) , add-≅ (⟦⟧ᴾ-refl dx) (proj₂ (sp η dη z ez)))

  corr  : ∀ {t} (d : 𝔸 t) → Sh ⟦ d ⟧ᵃ (cof t) t
  corrᴾ : ∀ {x} (d : 𝔸ᴾ x) → Sh ⟦ d ⟧ᵖ (cofP x) (x ∷ [])
  corr a[] = z≅
  corr (a∷ dx a[]) = corrᴾ dx
  corr (a∷ dx (a∷ {x = y} {xs = ys} dy dys)) = sum dx (a∷ dy dys) (cof (y ∷ ys)) refl (corr (a∷ dy dys))
  corrᴾ (aψ {a = []} sw a[]) = leaf sw (inA sw)
  corrᴾ (aψ {a = y ∷ ys} sw db) = corrψ sw (inA sw) db (cof (y ∷ ys)) refl (corr db)
```

```agda
  lab   : ∀ (X : Ordᶜ zero) {t} (d : 𝔸 t) → X ≅ ⟦ d ⟧ᵃ → Lab X t
  labSh : ∀ (X : Ordᶜ zero) {t} (d : 𝔸 t) c → cof t ≡ c → Sh ⟦ d ⟧ᵃ c t → X ≅ ⟦ d ⟧ᵃ → Lab X t
  lab X {t} d e = labSh X d (cof t) refl (corr d) e
  labSh X d c0 ce sh e = l0 ce (≅-trans (≅-trans e sh) z≅)
  labSh zero    d c1 ce (Y , eY , _) e = ⊥-elim (zs (≅-trans e eY))
  labSh (lim F) d c1 ce (Y , eY , _) e = ⊥-elim (ls (≅-trans e eY))
  labSh (suc X) d c1 ce (Y , eY , d′ , e′) e = l1 ce (s≅ (≅-reflˡ h)) (lab X d′ (≅-trans h e′))
    where h = s-inv (≅-trans e eY)
  labSh zero    d cω ce (G , eG , _) e = ⊥-elim (zl (≅-trans e eG))
  labSh (suc X) d cω ce (G , eG , _) e = ⊥-elim (sl (≅-trans e eG))
  labSh (lim F) d cω ce (G , eG , hG) e =
    lω ce (l≅ (λ n → ≅-reflˡ (h n))) (λ n → lab (F n) (proj₁ (hG n)) (≅-trans (h n) (proj₂ (hG n))))
    where h = l-inv (≅-trans e eG)
  labSh X d (cΩ ν) ce (_ , _ , _ , _ , _ , eX , _) e = ⊥-elim (noΩ0 X (≅-trans e eX))
  labSh (limᵢ () f) d c1 ce sh e
  labSh (up () x)   d c1 ce sh e
  labSh (limᵢ () f) d cω ce sh e
  labSh (up () x)   d cω ce sh e
```

## §9 结论与边界
