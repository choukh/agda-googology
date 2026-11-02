# 统一形 (四): 数据树上的层对齐互模拟

> 接 [Uniform4Base](Uniform4Base.lagda.md). `Rᵒ c x y` 是 Uniform3Rel 的 $\cong^\mathsf A$ 在数据树上的形式, 分层方式同 `Ld`. 封闭性: `R-⊕`, `R-ι`, `R-tl`, `RΩ̇`, `R-ψ`; 求值: `R→Rd`. 全是构造子对构造子. 只有一处不是机械的: `Rᵒ x x` 要被反演 (Uniform4Eval §3), 若 `rΩ` 两边用同一个层号变量, 反演会撞上 K (`k = k`), 所以两边是两个变量加等式 `ek`, 反演时用 ℕ 的 `≡-irrelevant` 去掉.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform4Rel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Decouple using (Idx; lvI; Lab0[])
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.OmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.StandardOmega using ()
open import OCF.Align.GoodLBase
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3Hon
open import OCF.Align.Uniform3Depth2Class
open import OCF.Align.Uniform3Depth2W using (InpW; CH; FHν; fsTΩ)

open import OCF.Align.Uniform3Full using (∅ᴿ-goodʰ)
open import OCF.Align.Uniform4Head
open import OCF.Align.Uniform4Base

```

## §1 关系

`rΩ` 两边的层号是两个变量, 用等式 `ek` 连接: 两边相同的 `Rᵒ x x` 要被反演 (§3 of Eval), 同一变量出现两次会撞上 K. 层号是 ℕ, 等式无关 (`≡-irrelevant`).

```agda
castO : ∀ {k k′ ξ} → k ≡ k′ → O k ξ → O k′ ξ
castO refl z = z

module _ (c : ℕ) (LR : ∀ {k} → k <ᴸ c → ∀ {ξ ξ′} → O k ξ → O k ξ′ → Set) where
  data R₊ : ∀ {φ ψ} → O c φ → O c ψ → Set where
    rz : ∀ {φ ψ} → R₊ {φ} {ψ} o0 o0
    rs : ∀ {φ ψ} {a : O c φ} {a′ : O c ψ} → φ ∼ᶠ ψ → R₊ a a′ → R₊ (os a) (os a′)
    rl : ∀ {φ ψ} {F : ℕ → O c φ} {F′ : ℕ → O c ψ} → (∀ n → R₊ (F n) (F′ n)) → R₊ (ol F) (ol F′)
    ri : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → O c φ} {f′ : Ordˢ j′ → O c ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ᴬ y → R₊ (f x) (f′ y)) → R₊ (oi ac f) (oi ac′ f′)
    rŝ : ∀ {φ ψ c₁ c₂} {t : O c φ} {t′ : O c ψ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → O c φ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O c ψ} →
         c₁ ≅ᴵ c₂ → R₊ t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (g η e) (g′ η′ e′)) → R₊ (oŝ c₁ t g) (oŝ c₂ t′ g′)
    rĉ : ∀ {φ ψ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : O c φ} {o₀′ : O c ψ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → O c φ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O c ψ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → R₊ o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (o η e) (o′ η′ e′)) → R₊ (oĉ c₁ z zg o₀ o) (oĉ c₂ z′ zg′ o₀′ o′)
    rclo : ∀ {φ ψ} {t : O c (φ ⊔ fk zero)} {t′ : O c (ψ ⊔ fk zero)} {g : (η : Ordᴵ) → O c (φ ⊔ fk η)} {g′ : (η : Ordᴵ) → O c (ψ ⊔ fk η)} →
         φ ∼ᶠ ψ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (oclo t g) (oclo t′ g′)
    rwk : ∀ {φ φ′ ψ ψ′} {le : ∀ {L} → Ev L ψ → Ev L φ} {le′ : ∀ {L} → Ev L ψ′ → Ev L φ′} {x : O c φ} {x′ : O c φ′} →
          R₊ x x′ → R₊ (owk le x) (owk le′ x′)
    rΩ : ∀ {φ ψ k k′} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r : k <ᴸ c} {r′ : k′ <ᴸ c}
         {h : ∀ ξ → Us c r ξ → O c (ξ ⊔ φ)} {h′ : ∀ ξ → Us c r′ ξ → O c (ξ ⊔ ψ)} → (ek : k ≡ k′) → φ ∼ᶠ ψ →
         LR r {Fl} {Fl} (Ω̇ k) (Ω̇ k) →
         (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k ξ′) → LR r z z′ → R₊ (h ξ (intoU r z)) (h′ ξ′ (intoU r′ (castO ek z′)))) → R₊ (oΩ fe r h) (oΩ fe′ r′ h′)

Rᵒ : ∀ c {φ ψ} → O c φ → O c ψ → Set
LRᵒ : ∀ c {k} → k <ᴸ c → ∀ {ξ ξ′} → O k ξ → O k ξ′ → Set
Rᵒ c x y = R₊ c (LRᵒ c) x y
LRᵒ (suc c) zero    x y = Rᵒ c x y
LRᵒ (suc c) (suc r) x y = LRᵒ c r x y

outR : ∀ {c k} (r : k <ᴸ c) {ξ ξ′} {z : O k ξ} {z′ : O k ξ′} → LRᵒ c r z z′ → Rᵒ k z z′
outR zero    l = l
outR (suc r) l = outR r l

intoR : ∀ {c k} (r : k <ᴸ c) {ξ ξ′} {z : O k ξ} {z′ : O k ξ′} → Rᵒ k z z′ → LRᵒ c r z z′
intoR zero    l = l
intoR (suc r) l = intoR r l

out-intoU′ : ∀ {c k} (r : k <ᴸ c) {ξ} (z : O k ξ) → outU r (intoU r z) ≡ z
out-intoU′ zero    z = refl
out-intoU′ (suc r) z = out-intoU′ r z
```

## §2 封闭性

```agda
R-⊕ : ∀ {c φ φ′ ψ ψ′} {W : O c φ} {W′ : O c φ′} {t : O c ψ} {t′ : O c ψ′} → φ ∼ᶠ φ′ → Rᵒ c W W′ → Rᵒ c t t′ → Rᵒ c (W ⊕ t) (W′ ⊕ t′)
R-⊕ s rW rz = rwk rW
R-⊕ s rW (rs sa r) = rs (⊔∼ s sa) (R-⊕ s rW r)
R-⊕ s rW (rl h) = rl (λ n → R-⊕ s rW (h n))
R-⊕ s rW (ri e h) = ri e (λ x y d → R-⊕ s rW (h x y d))
R-⊕ s rW (rŝ e r h) = rŝ e (R-⊕ s rW r) (λ η ee η′ e′ d → R-⊕ s rW (h η ee η′ e′ d))
R-⊕ s rW (rĉ e dz dg r h) = rĉ e dz dg (R-⊕ s rW r) (λ η ee η′ e′ d → R-⊕ s rW (h η ee η′ e′ d))
R-⊕ s rW (rclo sψ r h) = rwk (rclo (⊔∼ s sψ) (rwk (R-⊕ s rW r)) (λ η η′ d → rwk (R-⊕ s rW (h η η′ d))))
R-⊕ s rW (rwk r) = rwk (R-⊕ s rW r)
R-⊕ s rW (rΩ ek sψ b f) = rΩ ek (⊔∼ s sψ) b (λ ξ ξ′ d z z′ l → rwk (R-⊕ s rW (f ξ ξ′ d z z′ l)))

R-ι : ∀ {c d φ ψ} (q : c <ᴸ d) {x : O c φ} {x′ : O c ψ} → Rᵒ c x x′ → Rᵒ d (ι q x) (ι q x′)
R-ι q rz = rz
R-ι q (rs sa r) = rs sa (R-ι q r)
R-ι q (rl h) = rl (λ n → R-ι q (h n))
R-ι q (ri e h) = ri e (λ x y d → R-ι q (h x y d))
R-ι q (rŝ e r h) = rŝ e (R-ι q r) (λ η ee η′ e′ d → R-ι q (h η ee η′ e′ d))
R-ι q (rĉ e dz dg r h) = rĉ e dz dg (R-ι q r) (λ η ee η′ e′ d → R-ι q (h η ee η′ e′ d))
R-ι q (rclo s r h) = rclo s (R-ι q r) (λ η η′ d → R-ι q (h η η′ d))
R-ι q (rwk r) = rwk (R-ι q r)
R-ι {d = dd} q (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} refl s b f) =
  rΩ {r = tr< r q} {r′ = tr< r′ q} refl s (intoR (tr< r q) (outR r b))
     (λ ξ ξ′ e z z′ l → subst₂ (λ w w′ → Rᵒ dd (ι q (h ξ (intoU r w))) (ι q (h′ ξ′ (intoU r′ w′)))) (sym (out-intoU′ (tr< r q) z)) (sym (out-intoU′ (tr< r′ q) z′))
                                (R-ι q (f ξ ξ′ e z z′ (intoR r (outR (tr< r q) l)))))
```

## §3 尾巴与 $\Omega_{\Omega+c}$

```agda
R-tl : ∀ {c k₁ k₂ φ φ′} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       k₁ ≅ᴵ k₂ → φ ∼ᶠ φ′ → a ≅ᴬ b → Rᵒ c (tl φ cv a) (tl φ′ cv′ b)
R-tl ek sφ zᴬ = rz
R-tl ek sφ (sᴬ e) = rs sφ (R-tl ek sφ e)
R-tl ek sφ (lᴬ h) = rl (λ n → R-tl ek sφ (h n))
R-tl ek sφ (lᵢᴬ {p = q} e h) = ri e (λ x y dd → R-tl ek sφ (h x y (≅→Rᴬ (<→◃ q) dd)))
R-tl {k₁ = suc k′} {k₂ = suc k″} (s≅ ek) sφ (uᴬ uz dd) = rwk (R-tl ek (flo-∼ ek) dd)
R-tl {k₁ = lim f r} {k₂ = lim g t} (l≅ hh) sφ (uᴬ (us n) dd) = rwk (R-tl (hh n) (flo-∼ (hh n)) dd)
R-tl {k₁ = zero} {k₂ = zero} ek sφ (ŝᴬ k ec et eg) =
  rĉ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl {k₁ = zero} {k₂ = suc _}   ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = zero} {k₂ = lim _ _} ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = suc _}   {k₂ = zero} ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = lim _ _} {k₂ = zero} ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = suc _} {k₂ = suc _} ek sφ (ŝᴬ k ec et eg) = rŝ ec (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl {k₁ = suc _} {k₂ = lim _ _} ek sφ (ŝᴬ k ec et eg) = rŝ ec (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = suc _} ek sφ (ŝᴬ k ec et eg) = rŝ ec (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = lim _ _} ek sφ (ŝᴬ k ec et eg) = rŝ ec (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl ek sφ (ĉᴬ ec dt dg eo eO) = rĉ ec dt dg (R-tl ek sφ eo) (λ η e η′ e′ eη → R-tl ek sφ (eO η e η′ e′ eη))

RΩ̇ : ∀ c → Rᵒ c (Ω̇ c) (Ω̇ c)
RΩ̇ zero = rclo (∼ᶠ-refl fz)
  (R-tl (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero))))
  (λ η η′ eη → R-tl eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)) (Ωˢ-≅ᴬ eη))
RΩ̇ (suc c) = rΩ refl (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (RΩ̇ c) (λ ξ ξ′ d z z′ l → rwk (R-ι zero l))
```

## §4 对 $\psi_{\Omega+t}$ 封闭

```agda
R-rep : ∀ {c φ ψ} {X : O c φ} {X′ : O c ψ} → φ ∼ᶠ ψ → Rᵒ c X X′ → ∀ n → Rᵒ c (repᵒ X n) (repᵒ X′ n)
R-rep s r zero = rz
R-rep s r (suc zero) = r
R-rep s r (suc (suc n)) = rwk (R-⊕ s (R-rep s r (suc n)) r)

R-ψ : ∀ {c t φ ψ} (q q′ : t <ᴸ c) {x : O c φ} {x′ : O c ψ} → Rᵒ c x x′ → Rᵒ t (ψᵒ q x) (ψᵒ q′ x′)
R-ψΩ : ∀ {c t k φ ψ} (q q′ : t <ᴸ c) {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r r′ : k <ᴸ c}
       {h : ∀ ξ → Us c r ξ → O c (ξ ⊔ φ)} {h′ : ∀ ξ → Us c r′ ξ → O c (ξ ⊔ ψ)} → φ ∼ᶠ ψ → LRᵒ c r {Fl} {Fl} (Ω̇ k) (Ω̇ k) →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k ξ′) → LRᵒ c r z z′ → Rᵒ c (h ξ (intoU r z)) (h′ ξ′ (intoU r′ z′))) →
       (p : Pen k t) → Rᵒ t (ψᵒΩ q fe r h p) (ψᵒΩ q′ fe′ r′ h′ p)
chRR : ∀ {c k φ ψ} {r r′ : k <ᴸ c} {h : ∀ ξ → Us c r ξ → O c (ξ ⊔ φ)} {h′ : ∀ ξ → Us c r′ ξ → O c (ξ ⊔ ψ)} → φ ∼ᶠ ψ → LRᵒ c r {Fl} {Fl} (Ω̇ k) (Ω̇ k) →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k ξ′) → LRᵒ c r z z′ → Rᵒ c (h ξ (intoU r z)) (h′ ξ′ (intoU r′ z′))) →
       ∀ n → Rᵒ k (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU r z)))) n) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r′ (h′ (Fl ⊔ ψ) (intoU r′ z)))) n)

R-ψ {t = t} q q′ rz = rwk (RΩ̇ t)
R-ψ q q′ (rs sa r) = rl (R-rep (⊔∼ (∼ᶠ-refl Fl) sa) (R-ψ q q′ r))
R-ψ q q′ (rl h) = rl (λ n → R-ψ q q′ (h n))
R-ψ q q′ (ri e h) = ri e (λ x y d → R-ψ q q′ (h x y d))
R-ψ q q′ (rŝ e r h) = rŝ e (R-ψ q q′ r) (λ η ee η′ e′ d → R-ψ q q′ (h η ee η′ e′ d))
R-ψ q q′ (rĉ e dz dg r h) = rĉ e dz dg (R-ψ q q′ r) (λ η ee η′ e′ d → R-ψ q q′ (h η ee η′ e′ d))
R-ψ q q′ (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-ψ q q′ r)) (λ η η′ d → rwk (R-ψ q q′ (h η η′ d))))
R-ψ q q′ (rwk r) = rwk (R-ψ q q′ r)
R-ψ {t = t} q q′ (rΩ {k = k} {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} refl s b f) = R-ψΩ q q′ {fe} {fe′} {r} {r′} {h} {h′} s b f (cmp< k t)

R-ψΩ {t = t} q q′ {r = r} {r′ = r′} {h = h} {h′ = h′} s b f (pen p) =
  rΩ {r = p} {r′ = p} refl (⊔∼ (∼ᶠ-refl Fl) s) (intoR p (outR r b))
     (λ ξ ξ′ e z z′ l → rwk (subst₂ (λ w w′ → Rᵒ t (ψᵒ q (h ξ (intoU r w))) (ψᵒ q′ (h′ ξ′ (intoU r′ w′)))) (sym (out-intoU′ p z)) (sym (out-intoU′ p z′))
                                     (R-ψ q q′ (f ξ ξ′ e z z′ (intoR r (outR p l))))))
R-ψΩ {φ = φ} {ψ = ψ} q q′ {r = r} {r′ = r′} {h = h} {h′ = h′} s b f chain =
  rl (λ n → rwk (R-ψ q q′ (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR r (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} s b f n)))))

chRR {r = r} s b f zero = rwk (outR r b)
chRR {φ = φ} {ψ = ψ} {r = r} {r′ = r′} {h = h} {h′ = h′} s b f (suc n) =
  rwk (R-ψ r r′ (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR r (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} s b f n))))
```

## §5 求值

```agda
chRE : ∀ {c k φ ψ} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r r′ : k <ᴸ c}
       {h : ∀ ξ → Us c r ξ → O c (ξ ⊔ φ)} {h′ : ∀ ξ → Us c r′ ξ → O c (ξ ⊔ ψ)} → φ ∼ᶠ ψ → LRᵒ c r {Fl} {Fl} (Ω̇ k) (Ω̇ k) →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k ξ′) → LRᵒ c r z z′ → Rᵒ c (h ξ (intoU r z)) (h′ ξ′ (intoU r′ z′))) →
       ∀ n → Rᵒ k (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU r z)))) n) (chainᵒ fe′ (λ z → owk (λ v → fe′ v , (v , v)) (ψᵒ r′ (h′ ψ (intoU r′ z)))) n)
chRE {r = r} s b f zero = rwk (outR r b)
chRE {φ = φ} {ψ = ψ} {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} s b f (suc n) =
  rwk (R-ψ r r′ (f φ ψ s _ _ (intoR r (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} s b f n))))

R→Rd : ∀ {c φ ψ} {x : O c φ} {x′ : O c ψ} → Rᵒ c x x′ → Rd 0 (ψ̄ x) (ψ̄ x′)
R→Rd rz = wkRd 0 _ _ (H→R 0 (proj₂ ∅ᴿ-goodʰ))
R→Rd (rs s r) = sucRᴬ (R→Rd r)
R→Rd (rl h) = limRd 0 (λ n → R→Rd (h n))
R→Rd (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} e h) = limᵢRd 0 {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ (f x)} {H′ = λ x → ψ̄ (f′ x)} e (λ x y d → R→Rd (h x y d))
R→Rd (rŝ e r h) = ŝRd 0 e (R→Rd r) (λ η ee η′ e′ d → R→Rd (h η ee η′ e′ d))
R→Rd (rĉ e dz dg r h) = ĉRd 0 e dz dg (R→Rd r) (λ η ee η′ e′ d → R→Rd (h η ee η′ e′ d))
R→Rd (rclo {t = t} {t′} {g} {g′} s r h) = cloRd 0 {t = ψ̄ t} {g = λ η → ψ̄ (g η)} {t′ = ψ̄ t′} {g′ = λ η → ψ̄ (g′ η)} s (R→Rd r) (λ η η′ d → R→Rd (h η η′ d))
R→Rd (rwk {le = le} {le′ = le′} r) = wkRd 0 le le′ (R→Rd r)
R→Rd (rΩ {φ = φ} {ψ} {fe = fe} {fe′} {r} {r′} {h} {h′} refl s b f) =
  limRd 0 (λ n → wkRd 0 _ _ (R→Rd (f φ ψ s _ _ (intoR r (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} s b f n)))))
```
