> **机械克隆.** 由 `Uniform5Class` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (五): 层号 $\Omega+\eta$ ($\eta$ 是可数树) 上的标签类 `Ld`

> 接 [Uniform4Class](Uniform4Class.lagda.md), [Uniform4Two](Uniform4Two.lagda.md). 层号从 ℕ 换成 `Ordᴵ`, 树照用 Uniform4Two 的定义 (不改). 差别只有三处. (1) `lΩ` 带 `Iν : Idx ν` 与 $k\cong$ `lvI Iν`, 共尾度 $\Omega+\nu$ (原来是 $\mu_k$). (2) 分层关系 `L` 按 `◃` 索引 (同 `Us`). (3) `lΩ` 不再带 "$\Omega_{\Omega+k}$ 的标签" 字段: 现在它对一切带 `Idx` 的层号是定理 (Uniform5Tail 的 `LdΩ̇`), 字段是多余的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZUniform5Class where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁)
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI)
open import OCF.Align.ScafLadderZGoodLBase
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZUniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.ScafLadderZUniform3Rel
open import OCF.Align.ScafLadderZUniform3SqABase
open import OCF.Align.ScafLadderZUniform3Hon
open import OCF.Align.ScafLadderZUniform3Depth2Class
open import OCF.Align.ScafLadderZUniform3Depth2W using (InpW; CH; FHν)
open import OCF.Align.ScafLadderZUniform3Full using (FlrLab[]-up; LWʰ-up)
open import OCF.Align.ScafLadderZUniform5Head
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.ScafLadderZUniform4Two
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

```agda
FC : Bool → Ordᴵ → T → Set
FC false c u = ⊤
FC true  c u = FlrLab (flo c) u
```

`lΩ` 的输入 $z$ 在低层 `O k`, 它的标签关系作为参数 `L` 传入 (与 `O₊`/`Us` 同一分层, 否则不严格正).

```agda
module _ (c : Ordᴵ) (L : ∀ {k} → k ◃ c → Mode → ∀ {ξ} → O k ξ → T → Set) where
  data Ld₊ : Bool → Mode → ∀ {φ} → O c φ → T → Set where
    lz : ∀ {b m φ} → Ld₊ b m {φ} o0 []
    ls : ∀ {b m φ ps y ys} {a : O c φ} → cof (y ∷ ys) ≡ c1 → FlU m φ (ps ++ pred (y ∷ ys)) → FC b c (ps ++ pred (y ∷ ys)) → Ld₊ b m a (ps ++ pred (y ∷ ys)) → Ld₊ b m (os a) (ps ++ (y ∷ ys))
    ll : ∀ {b m φ ps y ys} {F : ℕ → O c φ} → cof (y ∷ ys) ≡ cω → (∀ n → Ld₊ b m (F n) (ps ++ fsn (y ∷ ys) n)) → Ld₊ b m (ol F) (ps ++ (y ∷ ys))
    li : ∀ {b m φ ps y ys ν j} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {f : Ordˢ j → O c φ} → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (∀ η x → LabL x η → ∀ {i} → j ≺ᴵ i → Cv m (wkm i) → Ld₊ b (wkm i) (f x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ η x → InpW j η x → Ld₊ b m (f x) (ps ++ fsT (y ∷ ys) η)) → Ld₊ b m (oi ac f) (ps ++ (y ∷ ys))
    lĉ : ∀ {b m φ ps y ys c₀ z} {zg : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {o₀ : O c φ} {o : (η : Ordᴵ) → c₀ ⊑ᴵ η → O c φ} → cof (y ∷ ys) ≡ cω →
         (K : CCᴸ c₀ z zg) → Ld₊ b m o₀ (ps ++ fsn (y ∷ ys) 0) →
         (∀ k → Ld₊ b m (o (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) → Ld₊ b m (oĉ c₀ z zg o₀ o) (ps ++ (y ∷ ys))
    lŝ : ∀ {b m φ ps y ys c₀ w′} {t : O c φ} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → O c φ} → cof (y ∷ ys) ≡ cΩ [] → (Iw′ : Idx w′) → c₀ ⊑ᴵ suc (lvI Iw′) → Ob w′ ps y ys →
         Ld₊ b m t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → Ld₊ b m (g (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
         Ld₊ b m (oŝ c₀ t g) (ps ++ (y ∷ ys))
    lclo : ∀ {b m φ ps y ys} {t : O c (φ ⊔ fk zero)} {g : (η : Ordᴵ) → O c (φ ⊔ fk η)} → Fw m (φ ⊔ fk zero) ps y ys → cof (y ∷ ys) ≡ cΩ [] →
         Ld₊ b m t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → Ld₊ b m (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         Ld₊ b m (oclo t g) (ps ++ (y ∷ ys))
    lwk : ∀ {b m φ ψ u} {le : ∀ {L} → Ev L ψ → Ev L φ} {x : O c φ} → Ld₊ b m x u → Ld₊ b m (owk le x) u
    lΩ : ∀ {b m φ ps y ys k ν} {fe : ∀ {L} → Ev L φ → Ev L Fl} {r : k <ᴵ c} {h : ∀ ξ → Us k (<→◃ r) ξ → O c (ξ ⊔ φ)} → cof (y ∷ ys) ≡ cΩ (μ ν) →
         (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → L (<→◃ r) m′ z θ → Ld₊ b m′ (h ξ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) → Ld₊ b m (oΩ fe r h) (ps ++ (y ∷ ys))
    lob : ∀ {b m φ u k} {r : k ◃₁ c} {z : Us k (◃₁→◃ r) φ} {x : O c φ} → L (◃₁→◃ r) m (outU (◃₁→◃ r) z) u → Ld₊ false m x u → Ld₊ b m (omk r z x) u

Ld : ∀ c → Bool → Mode → ∀ {φ} → O c φ → T → Set
LL : ∀ c {k} → k ◃ c → Mode → ∀ {ξ} → O k ξ → T → Set
Ld c b m x u = Ld₊ c (LL c) b m x u
LL (suc c)   zero      m x u = Ld c true m x u
LL (suc c)   (suc r)   m x u = LL c r m x u
LL (lim f s) (self n)  m x u = Ld (f n) true m x u
LL (lim f s) (lim n r) m x u = LL (f n) r m x u

outL : ∀ {c k} (r : k ◃ c) {m ξ} {z : O k ξ} {θ} → LL c r m z θ → Ld k true m z θ
outL zero      l = l
outL (suc r)   l = outL r l
outL (self n)  l = l
outL (lim n r) l = outL r l

intoL : ∀ {c k} (r : k ◃ c) {m ξ} {z : O k ξ} {θ} → Ld k true m z θ → LL c r m z θ
intoL zero      l = l
intoL (suc r)   l = intoL r l
intoL (self n)  l = l
intoL (lim n r) l = intoL r l
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

Ld-cv : ∀ {c t a b φ} {x : O c φ} {u} → Cv a b → Ld c t a x u → Ld c t b x u
Ld-cv v lz = lz
Ld-cv v (ls cc F Fc l) = ls cc (FlU-cv v F) Fc (Ld-cv v l)
Ld-cv v (ll cc h) = ll cc (λ n → Ld-cv v (h n))
Ld-cv v (li cc I e hP hI) = li cc I e (λ η x l s v′ → hP η x l s (Cv-tr v v′)) (λ η x i → Ld-cv v (hI η x i))
Ld-cv v (lĉ cc K h₀ hk) = lĉ cc K (Ld-cv v h₀) (λ k → Ld-cv v (hk k))
Ld-cv v (lŝ cc I b ob h₀ hg) = lŝ cc I b ob (Ld-cv v h₀) (λ θ Y hY lY nθ lt e → Ld-cv v (hg θ Y hY lY nθ lt e))
Ld-cv v (lclo F cc h₀ hg) = lclo (Fw-cv v F) cc (Ld-cv v h₀) (λ θ Y hY lY nθ lt → Ld-cv v (hg θ Y hY lY nθ lt))
Ld-cv v (lwk l) = lwk (Ld-cv v l)
Ld-cv v (lΩ cc I e f) = lΩ cc I e (λ v′ → f (Cv-tr v v′))
Ld-cv v (lob {r = zero} l x) = lob (Ld-cv v l) (Ld-cv v x)
Ld-cv v (lob {r = self n} l x) = lob (Ld-cv v l) (Ld-cv v x)
```
