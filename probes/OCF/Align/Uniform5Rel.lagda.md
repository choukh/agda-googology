# 统一形 (五): 层号 `Ordᴵ` 上的互模拟

> 接 [Uniform5Psi](Uniform5Psi.lagda.md), [Uniform4Rel](Uniform4Rel.lagda.md). **这里有一处不是机械的: 关系必须是跨层的.** `Rᵒ a b x y` 关联 `O a φ` 与 `O b ψ`, $a,b$ 独立. 原因: `<ᴵ-dec` 的穿透分支给的代表元 $k'<t$ 依赖比较的证明, 两边 (`r`/`q` 与 `r′`/`q′`) 可以字面不同, 所以 `rΩ` 的两个节点只有 $k\cong k'$, 输入在两个不同的字面层上. Uniform4 的 ℕ 层号上这件事被 `≡-irrelevant` 藏起来了, `Ordᴵ` 上没有这个引理. 分层只按左边 ($L$ 按左边的 `◃`). 好处是反演 `Rᵒ x x` 不再撞 K, 也不要 `castO`. 另一个差别: `rΩ` 不再带 $\Omega_{\Omega+k}$ 的字段, `RΩ̇ : a ≅ᴵ b → Rᵒ a b (Ω̇ a) (Ω̇ b)` 是定理.
>
> 新内容: `R-trˡ`/`R-trʳ` 系列 (搬运两侧都不改变关系, §3), `R-ψ` 的 `rΩ` 行的 3×3 派发, 非对角由 `clash` 排除 ([Uniform5RelPsi](Uniform5RelPsi.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5Rel where

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
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Bachmann using (clash)
open import OCF.Align.Uniform5Head
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.Uniform4Two
open RestrO
open import OCF.Align.Uniform5Tail using (out-intoU)
```

## §1 关系

```agda
module _ (a b : Ordᴵ) (LR : ∀ {k} → k ◃ a → ∀ {k′ ξ ξ′} → O k ξ → O k′ ξ′ → Set) where
  data R₊ : ∀ {φ ψ} → O a φ → O b ψ → Set where
    rz : ∀ {φ ψ} → R₊ {φ} {ψ} o0 o0
    rs : ∀ {φ ψ} {p : O a φ} {p′ : O b ψ} → φ ∼ᶠ ψ → R₊ p p′ → R₊ (os p) (os p′)
    rl : ∀ {φ ψ} {F : ℕ → O a φ} {F′ : ℕ → O b ψ} → (∀ n → R₊ (F n) (F′ n)) → R₊ (ol F) (ol F′)
    ri : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → O a φ} {f′ : Ordˢ j′ → O b ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ᴬ y → R₊ (f x) (f′ y)) → R₊ (oi ac f) (oi ac′ f′)
    rŝ : ∀ {φ ψ c₁ c₂} {t : O a φ} {t′ : O b ψ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → O a φ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O b ψ} →
         c₁ ≅ᴵ c₂ → R₊ t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (g η e) (g′ η′ e′)) → R₊ (oŝ c₁ t g) (oŝ c₂ t′ g′)
    rĉ : ∀ {φ ψ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : O a φ} {o₀′ : O b ψ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → O a φ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O b ψ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → R₊ o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (o η e) (o′ η′ e′)) → R₊ (oĉ c₁ z zg o₀ o) (oĉ c₂ z′ zg′ o₀′ o′)
    rclo : ∀ {φ ψ} {t : O a (φ ⊔ fk zero)} {t′ : O b (ψ ⊔ fk zero)} {g : (η : Ordᴵ) → O a (φ ⊔ fk η)} {g′ : (η : Ordᴵ) → O b (ψ ⊔ fk η)} →
         φ ∼ᶠ ψ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (oclo t g) (oclo t′ g′)
    rwk : ∀ {φ φ′ ψ ψ′} {le : ∀ {L} → Ev L ψ → Ev L φ} {le′ : ∀ {L} → Ev L ψ′ → Ev L φ′} {x : O a φ} {x′ : O b φ′} →
          R₊ x x′ → R₊ (owk le x) (owk le′ x′)
    rΩ : ∀ {φ ψ k k′} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r : k <ᴵ a} {r′ : k′ <ᴵ b}
         {h : ∀ ξ → Us k (<→◃ r) ξ → O a (ξ ⊔ φ)} {h′ : ∀ ξ → Us k′ (<→◃ r′) ξ → O b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
         (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → LR (<→◃ r) z z′ → R₊ (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) → R₊ (oΩ fe r h) (oΩ fe′ r′ h′)

Rᵒ : ∀ a b {φ ψ} → O a φ → O b ψ → Set
LRᵒ : ∀ a {k} → k ◃ a → ∀ {k′ ξ ξ′} → O k ξ → O k′ ξ′ → Set
Rᵒ a b x y = R₊ a b (LRᵒ a) x y
LRᵒ (suc k)   zero      {k′} x y = Rᵒ k k′ x y
LRᵒ (suc c)   (suc r)   x y = LRᵒ c r x y
LRᵒ (lim f s) (self n)  {k′} x y = Rᵒ (f n) k′ x y
LRᵒ (lim f s) (lim n r) x y = LRᵒ (f n) r x y

outR : ∀ {c k} (r : k ◃ c) {k′ ξ ξ′} {z : O k ξ} {z′ : O k′ ξ′} → LRᵒ c r z z′ → Rᵒ k k′ z z′
outR zero      l = l
outR (suc r)   l = outR r l
outR (self n)  l = l
outR (lim n r) l = outR r l

intoR : ∀ {c k} (r : k ◃ c) {k′ ξ ξ′} {z : O k ξ} {z′ : O k′ ξ′} → Rᵒ k k′ z z′ → LRᵒ c r z z′
intoR zero      l = l
intoR (suc r)   l = intoR r l
intoR (self n)  l = l
intoR (lim n r) l = intoR r l
```

## §2 封闭性

```agda
R-⊕ : ∀ {a b φ φ′ ψ ψ′} {W : O a φ} {W′ : O b φ′} {t : O a ψ} {t′ : O b ψ′} → φ ∼ᶠ φ′ → Rᵒ a b W W′ → Rᵒ a b t t′ → Rᵒ a b (W ⊕ t) (W′ ⊕ t′)
R-⊕ s rW rz = rwk rW
R-⊕ s rW (rs sa r) = rs (⊔∼ s sa) (R-⊕ s rW r)
R-⊕ s rW (rl h) = rl (λ n → R-⊕ s rW (h n))
R-⊕ s rW (ri e h) = ri e (λ x y d → R-⊕ s rW (h x y d))
R-⊕ s rW (rŝ e r h) = rŝ e (R-⊕ s rW r) (λ η ee η′ e′ d → R-⊕ s rW (h η ee η′ e′ d))
R-⊕ s rW (rĉ e dz dg r h) = rĉ e dz dg (R-⊕ s rW r) (λ η ee η′ e′ d → R-⊕ s rW (h η ee η′ e′ d))
R-⊕ s rW (rclo sψ r h) = rwk (rclo (⊔∼ s sψ) (rwk (R-⊕ s rW r)) (λ η η′ d → rwk (R-⊕ s rW (h η η′ d))))
R-⊕ s rW (rwk r) = rwk (R-⊕ s rW r)
R-⊕ s rW (rΩ ek sψ f) = rΩ ek (⊔∼ s sψ) (λ ξ ξ′ d z z′ l → rwk (R-⊕ s rW (f ξ ξ′ d z z′ l)))

R-ι : ∀ {a b c d φ ψ} (q : a ◃ c) (q′ : b ◃ d) {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ c d (ι q x) (ι q′ x′)
R-ι q q′ rz = rz
R-ι q q′ (rs sa r) = rs sa (R-ι q q′ r)
R-ι q q′ (rl h) = rl (λ n → R-ι q q′ (h n))
R-ι q q′ (ri e h) = ri e (λ x y d → R-ι q q′ (h x y d))
R-ι q q′ (rŝ e r h) = rŝ e (R-ι q q′ r) (λ η ee η′ e′ d → R-ι q q′ (h η ee η′ e′ d))
R-ι q q′ (rĉ e dz dg r h) = rĉ e dz dg (R-ι q q′ r) (λ η ee η′ e′ d → R-ι q q′ (h η ee η′ e′ d))
R-ι q q′ (rclo s r h) = rclo s (R-ι q q′ r) (λ η η′ d → R-ι q q′ (h η η′ d))
R-ι q q′ (rwk r) = rwk (R-ι q q′ r)
R-ι {c = c} {d = dd} q q′ (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f) =
  rΩ {r = <◃ r q} {r′ = <◃ r′ q′} ek s
     (λ ξ ξ′ e z z′ l → subst₂ (λ w w′ → Rᵒ c dd (ι q (h ξ (intoU (<→◃ r) w))) (ι q′ (h′ ξ′ (intoU (<→◃ r′) w′)))) (sym (out-intoU (<→◃ (<◃ r q)) z)) (sym (out-intoU (<→◃ (<◃ r′ q′)) z′))
                                (R-ι q q′ (f ξ ξ′ e _ _ (intoR (<→◃ r) (outR (<→◃ (<◃ r q)) l)))))
```

## §3 尾巴与 $\Omega_{\Omega+\eta}$

```agda
R-tl : ∀ {c c′ k₁ k₂ φ φ′} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       k₁ ≅ᴵ k₂ → φ ∼ᶠ φ′ → a ≅ᴬ b → Rᵒ c c′ (tl φ cv a) (tl φ′ cv′ b)
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

RΩ̇ : ∀ {a b} → a ≅ᴵ b → Rᵒ a b (Ω̇ a) (Ω̇ b)
RΩ̇ z≅ = rclo (∼ᶠ-refl fz)
  (R-tl (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero))))
  (λ η η′ eη → R-tl eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)) (Ωˢ-≅ᴬ eη))
RΩ̇ (s≅ e) = rΩ e (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (λ ξ ξ′ d z z′ l → rwk (R-ι zero zero l))
RΩ̇ (l≅ h) = rl (λ n → R-ι (self n) (self n) (RΩ̇ (h n)))
```

## §4 搬运不改变关系

$\mathtt{trO}\,e\,x$ 与 $x$ 互模拟, 左右各一族. 只有 `rΩ` 行不是逐字的: 新节点的输入 $z_1$ 经 `backO` 拉回到原层, 而拉回本身是搬运.

```agda
R-trˡ  : ∀ {a a′ b φ ψ} (e : a ≅ᴵ a′) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a′ b (trO e x) y
R-tr⁻ˡ : ∀ {a a′ b φ ψ} (e : a′ ≅ᴵ a) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a′ b (tr⁻O e x) y
R-resˡ : ∀ {j a a′ b ξ ξ′} (q : j <ᴵ a) (e : a ≅ᴵ a′) {z : O (repO (resO q e)) ξ} {y : O b ξ′} → Rᵒ _ b z y → Rᵒ j b (backO (resO q e) z) y
R-res⁻ˡ : ∀ {j a a′ b ξ ξ′} (q : j <ᴵ a) (e : a′ ≅ᴵ a) {z : O (repO (res⁻O q e)) ξ} {y : O b ξ′} → Rᵒ _ b z y → Rᵒ j b (backO (res⁻O q e) z) y

R-trˡ e rz = rz
R-trˡ e (rs sa r) = rs sa (R-trˡ e r)
R-trˡ e (rl h) = rl (λ m → R-trˡ e (h m))
R-trˡ e (ri ej h) = ri ej (λ x y d → R-trˡ e (h x y d))
R-trˡ e (rŝ ec r h) = rŝ ec (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
R-trˡ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
R-trˡ e (rclo s r h) = rclo s (R-trˡ e r) (λ η η′ d → R-trˡ e (h η η′ d))
R-trˡ e (rwk r) = rwk (R-trˡ e r)
R-trˡ {a′ = a′} {b} e (rΩ {φ = φ} {ψ} {r = q} {r′} {h} {h′} ek s f) =
  rΩ {r = ltO (resO q e)} (≅ᴵ-trans (≅ᴵ-sym (eqO (resO q e))) ek) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a′ b (trO e (h ξ (intoU (<→◃ q) (backO (resO q e) w)))) (h′ ξ′ (intoU (<→◃ r′) z′))) (sym (out-intoU (<→◃ (ltO (resO q e))) z))
                              (R-trˡ e (f ξ ξ′ d _ z′ (intoR (<→◃ q) (R-resˡ q e (outR (<→◃ (ltO (resO q e))) l))))))

R-tr⁻ˡ e rz = rz
R-tr⁻ˡ e (rs sa r) = rs sa (R-tr⁻ˡ e r)
R-tr⁻ˡ e (rl h) = rl (λ m → R-tr⁻ˡ e (h m))
R-tr⁻ˡ e (ri ej h) = ri ej (λ x y d → R-tr⁻ˡ e (h x y d))
R-tr⁻ˡ e (rŝ ec r h) = rŝ ec (R-tr⁻ˡ e r) (λ η ee η′ e′ d → R-tr⁻ˡ e (h η ee η′ e′ d))
R-tr⁻ˡ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ˡ e r) (λ η ee η′ e′ d → R-tr⁻ˡ e (h η ee η′ e′ d))
R-tr⁻ˡ e (rclo s r h) = rclo s (R-tr⁻ˡ e r) (λ η η′ d → R-tr⁻ˡ e (h η η′ d))
R-tr⁻ˡ e (rwk r) = rwk (R-tr⁻ˡ e r)
R-tr⁻ˡ {a′ = a′} {b} e (rΩ {φ = φ} {ψ} {r = q} {r′} {h} {h′} ek s f) =
  rΩ {r = ltO (res⁻O q e)} (≅ᴵ-trans (≅ᴵ-sym (eqO (res⁻O q e))) ek) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a′ b (tr⁻O e (h ξ (intoU (<→◃ q) (backO (res⁻O q e) w)))) (h′ ξ′ (intoU (<→◃ r′) z′))) (sym (out-intoU (<→◃ (ltO (res⁻O q e))) z))
                              (R-tr⁻ˡ e (f ξ ξ′ d _ z′ (intoR (<→◃ q) (R-res⁻ˡ q e (outR (<→◃ (ltO (res⁻O q e))) l))))))

R-resˡ zero      (s≅ e) l = R-tr⁻ˡ e l
R-resˡ (suc q)   (s≅ e) l = R-resˡ q e l
R-resˡ (lim n q) (l≅ h) l = R-resˡ q (h n) l

R-res⁻ˡ zero      (s≅ e) l = R-trˡ e l
R-res⁻ˡ (suc q)   (s≅ e) l = R-res⁻ˡ q e l
R-res⁻ˡ (lim n q) (l≅ h) l = R-res⁻ˡ q (h n) l
```
