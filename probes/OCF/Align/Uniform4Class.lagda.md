# 统一形 (四): 数据树的标签类 `Ld`

> 接 [Uniform4Base](Uniform4Base.lagda.md). 结论先说:
>
> 1. **`Ld c m x u`: 数据树 $x$ 带标签 $u$.** 按 $x$ 的构造子一一给行, 字段就是 Uniform3Depth2Class 行引理的前提. 所有头 ($\psi_i$, $\psi_\Omega$, $\psi_{\Omega+t}$) 都不出现在类里: 类不知道树将被哪个头折叠. 这是相对 `Wd`/`Od`/`Gc` 的简化: **没有深度**.
> 2. **两个模式.** `hon`: 诚实 (地板见证 `FW`, 给 $W$ 与 $L_0$). `wkm c`: 相对目标 $c$ (`FW[ c ]`, 只给 $W$; $\mathtt{limᵢ}$ 穿透行的非诚实输入走这里). `Cv` 是模式的序, `Ld-cv` 是转换.
> 3. **分层.** `lΩ` 的前提里 `Ld` 在箭头左边, 所以按 $c$ 分层: `Ld₊ c L`, `L` 是低层的关系 (`LL`), 与 `O₊`/`Us` 同形.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform4Class where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.StandardOmega using (NF₁)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Decouple using (Idx; lvI)
open import OCF.Align.GoodLBase
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3Hon
open import OCF.Align.Uniform3Depth2Class
open import OCF.Align.Uniform3Depth2W using (InpW; CH; FHν)
open import OCF.Align.Uniform3Full using (FlrLab[]-up; LWʰ-up)
open import OCF.Align.Uniform4Head
open import OCF.Align.Uniform4Base
```

## §1 模式与地板

```agda
data Mode : Set where
  hon : Mode
  wkm : Ordᴵ → Mode

Fw : Mode → Flr → T → PT → T → Set
Fw hon     φ ps y ys = FW₀ φ ps y ys
Fw (wkm c) φ ps y ys = FW[ c ] φ ps y ys

FlU : Mode → Flr → T → Set
FlU hon     φ u = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ (K ≅ᴵ one) ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × Occ w u
FlU (wkm c) φ u = ∀ {K} (k : InF K φ) → IgnK c k ⊎ (K ≅ᴵ one) ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × Occ w u

data Cv : Mode → Mode → Set where
  cv-h : ∀ {m} → Cv hon m
  cv-w : ∀ {c c′} → Up c c′ → Cv (wkm c) (wkm c′)
```

## §2 `Ld`

`lΩ` 的输入 $z$ 在低层 `O k`, 它的标签关系作为参数 `L` 传入 (与 `O₊`/`Us` 同一分层, 否则不严格正).

```agda
module _ (c : ℕ) (L : ∀ {k} → k <ᴸ c → Mode → ∀ {ξ} → O k ξ → T → Set) where
  data Ld₊ : Mode → ∀ {φ} → O c φ → T → Set where
    lz : ∀ {m φ} → Ld₊ m {φ} o0 []
    ls : ∀ {m φ ps y ys} {a : O c φ} → cof (y ∷ ys) ≡ c1 → FlU m φ (ps ++ pred (y ∷ ys)) → Ld₊ m a (ps ++ pred (y ∷ ys)) → Ld₊ m (os a) (ps ++ (y ∷ ys))
    ll : ∀ {m φ ps y ys} {F : ℕ → O c φ} → cof (y ∷ ys) ≡ cω → (∀ n → Ld₊ m (F n) (ps ++ fsn (y ∷ ys) n)) → Ld₊ m (ol F) (ps ++ (y ∷ ys))
    li : ∀ {m φ ps y ys ν j} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {f : Ordˢ j → O c φ} → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (∀ η x → LabL x η → ∀ {i} → j ≺ᴵ i → Cv m (wkm i) → Ld₊ (wkm i) (f x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ η x → InpW j η x → Ld₊ m (f x) (ps ++ fsT (y ∷ ys) η)) → Ld₊ m (oi ac f) (ps ++ (y ∷ ys))
    lĉ : ∀ {m φ ps y ys c₀ z} {zg : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {o₀ : O c φ} {o : (η : Ordᴵ) → c₀ ⊑ᴵ η → O c φ} → cof (y ∷ ys) ≡ cω →
         (K : CCᴸ c₀ z zg) → Ld₊ m o₀ (ps ++ fsn (y ∷ ys) 0) →
         (∀ k → Ld₊ m (o (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) → Ld₊ m (oĉ c₀ z zg o₀ o) (ps ++ (y ∷ ys))
    lŝ : ∀ {m φ ps y ys c₀ w′} {t : O c φ} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → O c φ} → cof (y ∷ ys) ≡ cΩ [] → (Iw′ : Idx w′) → c₀ ⊑ᴵ suc (lvI Iw′) → Ob w′ ps y ys →
         Ld₊ m t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → Ld₊ m (g (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
         Ld₊ m (oŝ c₀ t g) (ps ++ (y ∷ ys))
    lclo : ∀ {m φ ps y ys} {t : O c (φ ⊔ fk zero)} {g : (η : Ordᴵ) → O c (φ ⊔ fk η)} → Fw m (φ ⊔ fk zero) ps y ys → cof (y ∷ ys) ≡ cΩ [] →
         Ld₊ m t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → Ld₊ m (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         Ld₊ m (oclo t g) (ps ++ (y ∷ ys))
    lwk : ∀ {m φ ψ u} {le : ∀ {L} → Ev L ψ → Ev L φ} {x : O c φ} → Ld₊ m x u → Ld₊ m (owk le x) u
    lΩ : ∀ {m φ ps y ys k} {fe : ∀ {L} → Ev L φ → Ev L Fl} {r : k <ᴸ c} {h : ∀ ξ → Us c r ξ → O c (ξ ⊔ φ)} → cof (y ∷ ys) ≡ cΩ (μ k) →
         (∀ {m′} → Cv m m′ → L r m′ {Fl} (Ω̇ k) (Ωt (μ k))) →
         (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → L r m′ z θ → Ld₊ m′ (h ξ (intoU r z)) (ps ++ fsT (y ∷ ys) θ)) → Ld₊ m (oΩ fe r h) (ps ++ (y ∷ ys))

Ld : ∀ c → Mode → ∀ {φ} → O c φ → T → Set
LL : ∀ c {k} → k <ᴸ c → Mode → ∀ {ξ} → O k ξ → T → Set
Ld c m x u = Ld₊ c (LL c) m x u
LL (suc c) zero    m x u = Ld c m x u
LL (suc c) (suc r) m x u = LL c r m x u

outL : ∀ {c k} (r : k <ᴸ c) {m ξ} {z : O k ξ} {θ} → LL c r m z θ → Ld k m z θ
outL zero    l = l
outL (suc r) l = outL r l

intoL : ∀ {c k} (r : k <ᴸ c) {m ξ} {z : O k ξ} {θ} → Ld k m z θ → LL c r m z θ
intoL zero    l = l
intoL (suc r) l = intoL r l
```

## §3 模式转换

```agda
Cv-tr : ∀ {a b d} → Cv a b → Cv b d → Cv a d
Cv-tr cv-h q = cv-h
Cv-tr (cv-w u) (cv-w v) = cv-w (≼-trans u v)

Cv-refl : ∀ m → Cv m m
Cv-refl hon = cv-h
Cv-refl (wkm c) = cv-w (≼-refl c)

IgnK-up′ : ∀ {c c′ K φ} {k : InF K φ} → Up c c′ → IgnK c k → IgnK c′ k
IgnK-up′ u (inj₁ (inj₁ e0)) = inj₁ (inj₁ e0)
IgnK-up′ u (inj₁ (inj₂ kc)) = inj₁ (inj₂ (≼-trans kc u))
IgnK-up′ u (inj₂ (b , le))  = inj₂ (b , ⊑ᴵ-trans le (sB u))

Fw-cv : ∀ {a b φ ps y ys} → Cv a b → Fw a φ ps y ys → Fw b φ ps y ys
Fw-cv {b = hon} cv-h F = F
Fw-cv {b = wkm c} cv-h F = FW→FW[] F
Fw-cv (cv-w u) F k with F k
... | inj₁ g = inj₁ (IgnK-up′ u g)
... | inj₂ w = inj₂ w

FlU-cv : ∀ {a b φ u} → Cv a b → FlU a φ u → FlU b φ u
FlU-cv {b = hon} cv-h F = F
FlU-cv {b = wkm c} cv-h F k with F k
... | inj₁ e0 = inj₁ (inj₁ (inj₁ e0))
... | inj₂ (inj₁ e1) = inj₂ (inj₁ e1)
... | inj₂ (inj₂ w) = inj₂ (inj₂ w)
FlU-cv (cv-w u) F k with F k
... | inj₁ g = inj₁ (IgnK-up′ u g)
... | inj₂ w = inj₂ w

FlM : Mode → Flr → T → Set
FlM hon     φ u = FlrLab φ u
FlM (wkm c) φ u = FlrLab[ c ] φ u

FlM-cv : ∀ {a b φ u} → Cv a b → FlM a φ u → FlM b φ u
FlM-cv {b = hon} cv-h F = F
FlM-cv {b = wkm c} cv-h F = FlrLab→[] F
FlM-cv (cv-w u) F = FlrLab[]-up u F

Ld-cv : ∀ {c a b φ} {x : O c φ} {u} → Cv a b → Ld c a x u → Ld c b x u
Ld-cv v lz = lz
Ld-cv v (ls cc F l) = ls cc (FlU-cv v F) (Ld-cv v l)
Ld-cv v (ll cc h) = ll cc (λ n → Ld-cv v (h n))
Ld-cv v (li cc I e hP hI) = li cc I e (λ η x l s v′ → hP η x l s (Cv-tr v v′)) (λ η x i → Ld-cv v (hI η x i))
Ld-cv v (lĉ cc K h₀ hk) = lĉ cc K (Ld-cv v h₀) (λ k → Ld-cv v (hk k))
Ld-cv v (lŝ cc I b ob h₀ hg) = lŝ cc I b ob (Ld-cv v h₀) (λ θ Y hY lY nθ lt e → Ld-cv v (hg θ Y hY lY nθ lt e))
Ld-cv v (lclo F cc h₀ hg) = lclo (Fw-cv v F) cc (Ld-cv v h₀) (λ θ Y hY lY nθ lt → Ld-cv v (hg θ Y hY lY nθ lt))
Ld-cv v (lwk l) = lwk (Ld-cv v l)
Ld-cv v (lΩ cc b f) = lΩ cc (λ v′ → b (Cv-tr v v′)) (λ v′ → f (Cv-tr v v′))
```
