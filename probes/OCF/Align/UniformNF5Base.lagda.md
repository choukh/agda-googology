# 层号参数化的无符号闭包定理 (一): 跨层互模拟与上下文

> 接 [UniformNF4Base](UniformNF4Base.lagda.md), [Uniform4Two](Uniform4Two.lagda.md). 结论先说:
>
> 1. **`Rᵒ a b`: 跨层的互模拟.** 取自 [Uniform5Rel](Uniform5Rel.lagda.md), 值层关系换成 `≅ˢ`, `rwk` 拆成单侧的 `rwkˡ`/`rwkʳ`. `R-ιˡ`, `R-ιʳ`: 嵌入单侧透明, 所以旧的 `R-ψι`, `Rῑ` 不再是单独的定理.
> 2. **`Cx` 多两个构造子 `ptr`, `ptr⁻`, 而 `≈ᶜ` 仍是同层同 $W$ 的.** `pa W C ≈ᶜ pa W C′` 与 `pψ q C ≈ᶜ pψ q C′` 字面相同, 所以 `≈ᶜ-sym`, `≈ᶜ-trans` 不用互模拟的对称、传递 (`Rᵒ` 跨层时没有这两个). 这与值层的 `tro`/`tr⁻o` 同形. 把 `≈ᶜ` 也做成跨层的写法走不通: `pa` 行要 `Rᵒ` 的传递, 而 `rΩ` 的中间输入不存在.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF5Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; toZ; trˢ; tr⁻ˢ; Ωˢ; addˢ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; R→≅ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; tf;
  trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; addˢ-≅; ≅ˢ-sym; ≅ˢ-reflˡ; ≅ˢ-reflʳ; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl)
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.Uniform4Two
open RestrO
```

## §1 互模拟

`flo∼`: 紧地板对齐. 分层只按左边 ($LR$ 按左边的 `◃`). `rΩ` 不再带 $\Omega_k$ 的自相关字段: `RΩ̇` 现在是不依赖 `LR` 的定理. 比较的结果在 $\cong$ 下一致, 非对角由 `clash` 排除 (§5).

```agda
flo∼ : ∀ {k k′} → k ≅ᴵ k′ → flo k ∼ᶠ flo k′
flo∼ z≅     = fz∼
flo∼ (s≅ e) = fk∼ e
flo∼ (l≅ h) = fb∼ (l≅ h)

out-intoU : ∀ {c k} (r : k ◃ c) {ξ} (z : O k ξ) → outU r (intoU r z) ≡ z
out-intoU zero      z = refl
out-intoU (suc r)   z = out-intoU r z
out-intoU (self n)  z = refl
out-intoU (lim n r) z = out-intoU r z

clash : ∀ {i j} → j ≺ᴵ i → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ⊥
clash s (inj₁ t) = ≺ᴵ-irrefl (≺ᴵ-trans s t)
clash s (inj₂ c) = ≺ᴵ-irrefl (≺ᴵ-respʳ s c)

module _ (a b : Ordᴵ) (LR : ∀ {k} → k ◃ a → ∀ {k′ ξ ξ′} → O k ξ → O k′ ξ′ → Set) where
  data R₊ : ∀ {φ ψ} → O a φ → O b ψ → Set where
    rz : ∀ {φ ψ} → R₊ {φ} {ψ} o0 o0
    rs : ∀ {φ ψ} {p : O a φ} {p′ : O b ψ} → φ ∼ᶠ ψ → R₊ p p′ → R₊ (os p) (os p′)
    rl : ∀ {φ ψ} {F : ℕ → O a φ} {F′ : ℕ → O b ψ} → (∀ n → R₊ (F n) (F′ n)) → R₊ (ol F) (ol F′)
    ri : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → O a φ} {f′ : Ordˢ j′ → O b ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → R₊ (f x) (f′ y)) → R₊ (oi ac f) (oi ac′ f′)
    rŝ : ∀ {φ ψ c₁ c₂} {t : O a φ} {t′ : O b ψ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → O a φ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O b ψ} →
         c₁ ≅ᴵ c₂ → R₊ t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (g η e) (g′ η′ e′)) → R₊ (oŝ c₁ t g) (oŝ c₂ t′ g′)
    rĉ : ∀ {φ ψ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : O a φ} {o₀′ : O b ψ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → O a φ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O b ψ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → R₊ o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (o η e) (o′ η′ e′)) → R₊ (oĉ c₁ z zg o₀ o) (oĉ c₂ z′ zg′ o₀′ o′)
    rclo : ∀ {φ ψ} {t : O a (φ ⊔ fk zero)} {t′ : O b (ψ ⊔ fk zero)} {g : (η : Ordᴵ) → O a (φ ⊔ fk η)} {g′ : (η : Ordᴵ) → O b (ψ ⊔ fk η)} →
         φ ∼ᶠ ψ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (oclo t g) (oclo t′ g′)
    rwkˡ : ∀ {φ ψ φ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {x : O a φ} {x′ : O b ψ} → R₊ x x′ → R₊ (owk le x) x′
    rwkʳ : ∀ {φ ψ ψ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {x : O a φ} {x′ : O b ψ} → R₊ x x′ → R₊ x (owk le′ x′)
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
rwk : ∀ {a b φ ψ φ′ ψ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ a b (owk le x) (owk le′ x′)
rwk r = rwkˡ (rwkʳ r)
```

## §2 封闭性

`R-ιˡ`, `R-ιʳ`: 嵌入单侧透明; 双侧的 `R-ι` 是它们的合成.

```agda
R-⊕ : ∀ {a b φ φ′ ψ ψ′} {W : O a φ} {W′ : O b φ′} {t : O a ψ} {t′ : O b ψ′} → φ ∼ᶠ φ′ → Rᵒ a b W W′ → Rᵒ a b t t′ → Rᵒ a b (W ⊕ t) (W′ ⊕ t′)
R-⊕ s rW rz = rwk rW
R-⊕ s rW (rs sa r) = rs (⊔∼ s sa) (R-⊕ s rW r)
R-⊕ s rW (rl h) = rl (λ n → R-⊕ s rW (h n))
R-⊕ s rW (ri e h) = ri e (λ x y d → R-⊕ s rW (h x y d))
R-⊕ s rW (rŝ e r h) = rŝ e (R-⊕ s rW r) (λ η ee η′ e′ d → R-⊕ s rW (h η ee η′ e′ d))
R-⊕ s rW (rĉ e dz dg r h) = rĉ e dz dg (R-⊕ s rW r) (λ η ee η′ e′ d → R-⊕ s rW (h η ee η′ e′ d))
R-⊕ s rW (rclo sψ r h) = rwk (rclo (⊔∼ s sψ) (rwk (R-⊕ s rW r)) (λ η η′ d → rwk (R-⊕ s rW (h η η′ d))))
R-⊕ s rW (rwkˡ r) = rwkˡ (R-⊕ s rW r)
R-⊕ s rW (rwkʳ r) = rwkʳ (R-⊕ s rW r)
R-⊕ s rW (rΩ ek sψ f) = rΩ ek (⊔∼ s sψ) (λ ξ ξ′ d z z′ l → rwk (R-⊕ s rW (f ξ ξ′ d z z′ l)))

R-ιˡ : ∀ {a b c φ ψ} (q : a ◃ c) {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ c b (ι q x) x′
R-ιˡ q rz = rz
R-ιˡ q (rs sa r) = rs sa (R-ιˡ q r)
R-ιˡ q (rl h) = rl (λ n → R-ιˡ q (h n))
R-ιˡ q (ri e h) = ri e (λ x y d → R-ιˡ q (h x y d))
R-ιˡ q (rŝ e r h) = rŝ e (R-ιˡ q r) (λ η ee η′ e′ d → R-ιˡ q (h η ee η′ e′ d))
R-ιˡ q (rĉ e dz dg r h) = rĉ e dz dg (R-ιˡ q r) (λ η ee η′ e′ d → R-ιˡ q (h η ee η′ e′ d))
R-ιˡ q (rclo s r h) = rclo s (R-ιˡ q r) (λ η η′ d → R-ιˡ q (h η η′ d))
R-ιˡ q (rwkˡ r) = rwkˡ (R-ιˡ q r)
R-ιˡ q (rwkʳ r) = rwkʳ (R-ιˡ q r)
R-ιˡ {b = b} {c = c} q (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f) =
  rΩ {r = <◃ r q} {r′ = r′} ek s
     (λ ξ ξ′ e z z′ l → subst (λ w → Rᵒ c b (ι q (h ξ (intoU (<→◃ r) w))) (h′ ξ′ (intoU (<→◃ r′) z′))) (sym (out-intoU (<→◃ (<◃ r q)) z))
                              (R-ιˡ q (f ξ ξ′ e _ z′ (intoR (<→◃ r) (outR (<→◃ (<◃ r q)) l)))))

R-ιʳ : ∀ {a b d φ ψ} (q : b ◃ d) {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ a d x (ι q x′)
R-ιʳ q rz = rz
R-ιʳ q (rs sa r) = rs sa (R-ιʳ q r)
R-ιʳ q (rl h) = rl (λ n → R-ιʳ q (h n))
R-ιʳ q (ri e h) = ri e (λ x y d → R-ιʳ q (h x y d))
R-ιʳ q (rŝ e r h) = rŝ e (R-ιʳ q r) (λ η ee η′ e′ d → R-ιʳ q (h η ee η′ e′ d))
R-ιʳ q (rĉ e dz dg r h) = rĉ e dz dg (R-ιʳ q r) (λ η ee η′ e′ d → R-ιʳ q (h η ee η′ e′ d))
R-ιʳ q (rclo s r h) = rclo s (R-ιʳ q r) (λ η η′ d → R-ιʳ q (h η η′ d))
R-ιʳ q (rwkˡ r) = rwkˡ (R-ιʳ q r)
R-ιʳ q (rwkʳ r) = rwkʳ (R-ιʳ q r)
R-ιʳ {a = a} {d = dd} q (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f) =
  rΩ {r = r} {r′ = <◃ r′ q} ek s
     (λ ξ ξ′ e z z′ l → subst (λ w → Rᵒ a dd (h ξ (intoU (<→◃ r) z)) (ι q (h′ ξ′ (intoU (<→◃ r′) w)))) (sym (out-intoU (<→◃ (<◃ r′ q)) z′))
                              (R-ιʳ q (f ξ ξ′ e z _ l)))

R-ι : ∀ {a b c d φ ψ} (q : a ◃ c) (q′ : b ◃ d) {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ c d (ι q x) (ι q′ x′)
R-ι q q′ r = R-ιˡ q (R-ιʳ q′ r)
```

## §3 尾巴与 $\Omega_{\Omega+\eta}$

```agda
R-tl : ∀ {c c′ k₁ k₂} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       a ≅ˢ b → Rᵒ c c′ (tl (flo k₁) cv a) (tl (flo k₂) cv′ b)
R-tl z≅ = rz
R-tl (s≅ le e) = rs (flo∼ le) (R-tl e)
R-tl (l≅ h) = rl (λ n → R-tl (h n))
R-tl (lᵢ≅ {p = q} e h) = ri e (λ x y dd → R-tl (h x y (≅→Rˢ (<→◃ q) dd)))
R-tl {k₁ = suc k′} (upˡ {r = zero} d) = rwkˡ (R-tl d)
R-tl {k₁ = lim f s} (upˡ {r = self n} d) = rwkˡ (R-tl d)
R-tl {k₂ = suc k′} (upʳ {r = zero} d) = rwkʳ (R-tl d)
R-tl {k₂ = lim f s} (upʳ {r = self n} d) = rwkʳ (R-tl d)
R-tl {k₁ = zero} {k₂ = zero} (ŝ≅ k ec et eg) =
  rĉ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = zero} {k₂ = suc _}   (ŝ≅ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = zero} {k₂ = lim _ _} (ŝ≅ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = suc _}   {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = lim _ _} {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = suc _} {k₂ = suc _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = suc _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = suc _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl (ĉ≅ ec dt dg eo eO) = rĉ ec dt dg (R-tl eo) (λ η e η′ e′ eη → R-tl (eO η e η′ e′ eη))

R-tlΩ : ∀ {c c′ η η′ φ φ′} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} → η ≅ᴵ η′ → φ ∼ᶠ φ′ → Rᵒ c c′ (tl φ cv (Ωˢ η)) (tl φ′ cv′ (Ωˢ η′))
R-tlΩ z≅ s = rs s rz
R-tlΩ (s≅ e) s = ri e (λ x y d → rwk (R-tl d))
R-tlΩ (l≅ h) s = rl (λ n → rwk (R-tl (Ωˢ-≅ (h n))))

RΩ̇ : ∀ {a b} → a ≅ᴵ b → Rᵒ a b (Ω̇ a) (Ω̇ b)
RΩ̇ z≅ = rclo (∼ᶠ-refl fz) (R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
  (λ η η′ eη → R-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
RΩ̇ (s≅ e) = rΩ e (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (λ ξ ξ′ d z z′ l → rwk (R-ι zero zero l))
RΩ̇ (l≅ h) = rl (λ n → R-ι (self n) (self n) (RΩ̇ (h n)))
```

## §4 搬运不改变关系

$\mathtt{trO}\,e\,x$ 与 $x$ 互模拟, 左右各一族. 只有 `rΩ` 行不是逐字的: 新节点的输入经 `backO` 拉回到原层.

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
R-trˡ e (rwkˡ r) = rwkˡ (R-trˡ e r)
R-trˡ e (rwkʳ r) = rwkʳ (R-trˡ e r)
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
R-tr⁻ˡ e (rwkˡ r) = rwkˡ (R-tr⁻ˡ e r)
R-tr⁻ˡ e (rwkʳ r) = rwkʳ (R-tr⁻ˡ e r)
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

R-trʳ  : ∀ {a b b′ φ ψ} (e : b ≅ᴵ b′) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a b′ x (trO e y)
R-tr⁻ʳ : ∀ {a b b′ φ ψ} (e : b′ ≅ᴵ b) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a b′ x (tr⁻O e y)
R-resʳ : ∀ {j a b b′ ξ ξ′} (q : j <ᴵ b) (e : b ≅ᴵ b′) {z : O a ξ} {y : O (repO (resO q e)) ξ′} → Rᵒ a _ z y → Rᵒ a j z (backO (resO q e) y)
R-res⁻ʳ : ∀ {j a b b′ ξ ξ′} (q : j <ᴵ b) (e : b′ ≅ᴵ b) {z : O a ξ} {y : O (repO (res⁻O q e)) ξ′} → Rᵒ a _ z y → Rᵒ a j z (backO (res⁻O q e) y)

R-trʳ e rz = rz
R-trʳ e (rs sa r) = rs sa (R-trʳ e r)
R-trʳ e (rl h) = rl (λ m → R-trʳ e (h m))
R-trʳ e (ri ej h) = ri ej (λ x y d → R-trʳ e (h x y d))
R-trʳ e (rŝ ec r h) = rŝ ec (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rclo s r h) = rclo s (R-trʳ e r) (λ η η′ d → R-trʳ e (h η η′ d))
R-trʳ e (rwkˡ r) = rwkˡ (R-trʳ e r)
R-trʳ e (rwkʳ r) = rwkʳ (R-trʳ e r)
R-trʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s f) =
  rΩ {r = r} {r′ = ltO (resO q e)} (≅ᴵ-trans ek (eqO (resO q e))) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a b′ (h ξ (intoU (<→◃ r) z)) (trO e (h′ ξ′ (intoU (<→◃ q) (backO (resO q e) w))))) (sym (out-intoU (<→◃ (ltO (resO q e))) z′))
                              (R-trʳ e (f ξ ξ′ d z _ (intoR (<→◃ r) (R-resʳ q e (outR (<→◃ r) l))))))

R-tr⁻ʳ e rz = rz
R-tr⁻ʳ e (rs sa r) = rs sa (R-tr⁻ʳ e r)
R-tr⁻ʳ e (rl h) = rl (λ m → R-tr⁻ʳ e (h m))
R-tr⁻ʳ e (ri ej h) = ri ej (λ x y d → R-tr⁻ʳ e (h x y d))
R-tr⁻ʳ e (rŝ ec r h) = rŝ ec (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
R-tr⁻ʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
R-tr⁻ʳ e (rclo s r h) = rclo s (R-tr⁻ʳ e r) (λ η η′ d → R-tr⁻ʳ e (h η η′ d))
R-tr⁻ʳ e (rwkˡ r) = rwkˡ (R-tr⁻ʳ e r)
R-tr⁻ʳ e (rwkʳ r) = rwkʳ (R-tr⁻ʳ e r)
R-tr⁻ʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s f) =
  rΩ {r = r} {r′ = ltO (res⁻O q e)} (≅ᴵ-trans ek (eqO (res⁻O q e))) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a b′ (h ξ (intoU (<→◃ r) z)) (tr⁻O e (h′ ξ′ (intoU (<→◃ q) (backO (res⁻O q e) w))))) (sym (out-intoU (<→◃ (ltO (res⁻O q e))) z′))
                              (R-tr⁻ʳ e (f ξ ξ′ d z _ (intoR (<→◃ r) (R-res⁻ʳ q e (outR (<→◃ r) l))))))

R-resʳ zero      (s≅ e) l = R-tr⁻ʳ e l
R-resʳ (suc q)   (s≅ e) l = R-resʳ q e l
R-resʳ (lim n q) (l≅ h) l = R-resʳ q (h n) l

R-res⁻ʳ zero      (s≅ e) l = R-trʳ e l
R-res⁻ʳ (suc q)   (s≅ e) l = R-res⁻ʳ q e l
R-res⁻ʳ (lim n q) (l≅ h) l = R-res⁻ʳ q (h n) l

R-tr₂ : ∀ {a b a′ b′ φ ψ} (e : a ≅ᴵ a′) (e′ : b ≅ᴵ b′) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a′ b′ (trO e x) (trO e′ y)
R-tr₂ e e′ r = R-trˡ e (R-trʳ e′ r)

R-tr⁻₂ : ∀ {a b a′ b′ φ ψ} (e : a′ ≅ᴵ a) (e′ : b′ ≅ᴵ b) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a′ b′ (tr⁻O e x) (tr⁻O e′ y)
R-tr⁻₂ e e′ r = R-tr⁻ˡ e (R-tr⁻ʳ e′ r)
```

## §5 对 $\psi_{\Omega+\tau}$ 封闭

```agda
R-rep : ∀ {a b φ ψ} {X : O a φ} {X′ : O b ψ} → φ ∼ᶠ ψ → Rᵒ a b X X′ → ∀ n → Rᵒ a b (repᵒ X n) (repᵒ X′ n)
R-rep s r zero = rz
R-rep s r (suc zero) = r
R-rep s r (suc (suc n)) = rwk (R-⊕ s (R-rep s r (suc n)) r)

R-ψ : ∀ {a b t t′ φ ψ} (q : t <ᴵ a) (q′ : t′ <ᴵ b) → t ≅ᴵ t′ → {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ t t′ (ψᵒ q x) (ψᵒ q′ x′)
chRR : ∀ {a b k k′ φ ψ} {r : k <ᴵ a} {r′ : k′ <ᴵ b} {h : ∀ ξ → Us k (<→◃ r) ξ → O a (ξ ⊔ φ)} {h′ : ∀ ξ → Us k′ (<→◃ r′) ξ → O b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → LRᵒ a (<→◃ r) z z′ → Rᵒ a b (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) →
       ∀ n → Rᵒ k k′ (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU (<→◃ r) z)))) n) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r′ (h′ (Fl ⊔ ψ) (intoU (<→◃ r′) z)))) n)

R-ψ q q′ et rz = rwk (RΩ̇ et)
R-ψ q q′ et (rs sa r) = rl (R-rep (⊔∼ (∼ᶠ-refl Fl) sa) (R-ψ q q′ et r))
R-ψ q q′ et (rl h) = rl (λ n → R-ψ q q′ et (h n))
R-ψ q q′ et (ri e h) = ri e (λ x y d → R-ψ q q′ et (h x y d))
R-ψ q q′ et (rŝ e r h) = rŝ e (R-ψ q q′ et r) (λ η ee η′ e′ d → R-ψ q q′ et (h η ee η′ e′ d))
R-ψ q q′ et (rĉ e dz dg r h) = rĉ e dz dg (R-ψ q q′ et r) (λ η ee η′ e′ d → R-ψ q q′ et (h η ee η′ e′ d))
R-ψ q q′ et (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-ψ q q′ et r)) (λ η η′ d → rwk (R-ψ q q′ et (h η η′ d))))
R-ψ q q′ et (rwkˡ r) = rwkˡ (R-ψ q q′ et r)
R-ψ q q′ et (rwkʳ r) = rwkʳ (R-ψ q q′ et r)
R-ψ {t = t} {t′} q q′ et (rΩ {φ = φ} {ψ} {k} {k′} {r = r} {r′} {h} {h′} ek s f) with <ᴵ-dec r q | <ᴵ-dec r′ q′
... | injᵃ (via e p) | injᵃ (via e′ p′) =
  rΩ {r = p} {r′ = p′} (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans ek e′)) (⊔∼ (∼ᶠ-refl Fl) s)
     (λ ξ ξ′ d z z′ l → rwk (subst₂ (λ w w′ → Rᵒ t t′ (ψᵒ q (h ξ (intoU (<→◃ r) (tr⁻O e w)))) (ψᵒ q′ (h′ ξ′ (intoU (<→◃ r′) (tr⁻O e′ w′))))) (sym (out-intoU (<→◃ p) z)) (sym (out-intoU (<→◃ p′) z′))
                                    (R-ψ q q′ et (f ξ ξ′ d _ _ (intoR (<→◃ r) (R-tr⁻ˡ e (R-tr⁻ʳ e′ (outR (<→◃ p) l))))))))
... | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
... | injᵃ a | injᶜ c = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym ek)))))
... | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
... | injᶜ c | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c) ek))))
... | injᵇ _ | injᵇ _ = rl (λ n → rwk (R-ψ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
... | injᵇ _ | injᶜ _ = rl (λ n → rwk (R-ψ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
... | injᶜ _ | injᵇ _ = rl (λ n → rwk (R-ψ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
... | injᶜ _ | injᶜ _ = rl (λ n → rwk (R-ψ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))

chRR ek s f zero = rwk (RΩ̇ ek)
chRR {φ = φ} {ψ = ψ} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f (suc n) =
  rwk (R-ψ r r′ ek (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n))))
```

## §6 求值

```agda
chRE : ∀ {a b k k′ φ ψ} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r : k <ᴵ a} {r′ : k′ <ᴵ b}
       {h : ∀ ξ → Us k (<→◃ r) ξ → O a (ξ ⊔ φ)} {h′ : ∀ ξ → Us k′ (<→◃ r′) ξ → O b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → LRᵒ a (<→◃ r) z z′ → Rᵒ a b (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) →
       ∀ n → Rᵒ k k′ (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n) (chainᵒ fe′ (λ z → owk (λ v → fe′ v , (v , v)) (ψᵒ r′ (h′ ψ (intoU (<→◃ r′) z)))) n)
chRE ek s f zero = rwk (RΩ̇ ek)
chRE {φ = φ} {ψ = ψ} {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f (suc n) =
  rwk (R-ψ r r′ ek (f φ ψ s _ _ (intoR (<→◃ r) (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n))))

r∅ : ∅ᴿ ≈ᴿ ∅ᴿ
r∅ ev p ev′ p′ ei = Ωˢ-≅ ei

R→≈ : ∀ {a b φ ψ} {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → ψ̄ x ≈ᴿ ψ̄ x′
R→≈ rz = wkR _ _ r∅
R→≈ (rs s r) = sucR (R→≈ r)
R→≈ (rl h) = limR (λ n → R→≈ (h n))
R→≈ (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} e h) = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ (f x)} {H′ = λ x → ψ̄ (f′ x)} e (λ x y d → R→≈ (h x y d))
R→≈ (rŝ e r h) = ŝR e (R→≈ r) (λ η ee η′ e′ d → R→≈ (h η ee η′ e′ d))
R→≈ (rĉ e dz dg r h) = ĉR e dz dg (R→≈ r) (λ η ee η′ e′ d → R→≈ (h η ee η′ e′ d))
R→≈ (rclo {t = t} {t′} {g} {g′} s r h) = cloR {t = ψ̄ t} {g = λ η → ψ̄ (g η)} {t′ = ψ̄ t′} {g′ = λ η → ψ̄ (g′ η)} s (R→≈ r) (λ η η′ d → R→≈ (h η η′ d))
R→≈ (rwkˡ {le = le} r) = wkR le (λ e → e) (R→≈ r)
R→≈ (rwkʳ {le′ = le′} r) = wkR (λ e → e) le′ (R→≈ r)
R→≈ (rΩ {φ = φ} {ψ} {fe = fe} {fe′} {r} {r′} {h} {h′} ek s f) =
  limR (λ n → wkR _ _ (R→≈ (f φ ψ s _ _ (intoR (<→◃ r) (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
```

## §7 上下文

```agda
data Obs : Ordᴵ → Set
data Cx : Ordᴵ → Flr → Set

data Obs where
  idO  : Obs zero
  tlo  : ∀ {c k} → Cx c (flo k) → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordˢ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

data Cx where
  top : ∀ {c φ i ℓ} → Obs i → Ev ℓ φ → i <ᴵ ℓ → Cx c φ
  pa  : ∀ {c a φ} → O c a → Cx c (a ⊔ φ) → Cx c φ
  pψ  : ∀ {c t φ} → t <ᴵ c → Cx t (Fl ⊔ φ) → Cx c φ
  pι  : ∀ {c d φ} → c ◃ d → Cx d φ → Cx c φ
  ptr  : ∀ {a b φ} → a ≅ᴵ b → Cx b φ → Cx a φ
  ptr⁻ : ∀ {a b φ} → a ≅ᴵ b → Cx a φ → Cx b φ

run  : ∀ {k} → Obs k → Ordˢ k → Ordˢ zero
runᶜ : ∀ {c φ} → Cx c φ → O c φ → Ordˢ zero
run idO          x = x
run (tlo {k = k} C) x = runᶜ C (tl (flo k) (cvFlo k) x)
run (addo O a σ) x = run O (addˢ a σ x)
run (tro O e)    x = run O (trˢ e x)
run (tr⁻o O e)   x = run O (tr⁻ˢ e x)
runᶜ (top O ev p) x = run O (ψ̄ x ev p)
runᶜ (pa W C)     x = runᶜ C (W ⊕ x)
runᶜ (pψ q C)     x = runᶜ C (ψᵒ q x)
runᶜ (pι q C)     x = runᶜ C (ι q x)
runᶜ (ptr e C)    x = runᶜ C (trO e x)
runᶜ (ptr⁻ e C)   x = runᶜ C (tr⁻O e x)

wkC : ∀ {c φ ψ} → (∀ {L} → Ev L ψ → Ev L φ) → Cx c ψ → Cx c φ
wkC le (top O ev p) = top O (le ev) p
wkC le (pa W C)     = pa W (wkC (λ e → proj₁ e , le (proj₂ e)) C)
wkC le (pψ q C)     = pψ q (wkC (λ e → proj₁ e , le (proj₂ e)) C)
wkC le (pι q C)     = pι q (wkC le C)
wkC le (ptr e C)    = ptr e (wkC le C)
wkC le (ptr⁻ e C)   = ptr⁻ e (wkC le C)

run-wkC : ∀ {c φ ψ} (le : ∀ {L} → Ev L ψ → Ev L φ) (C : Cx c ψ) (x : O c φ) → runᶜ (wkC le C) x ≡ runᶜ C (owk le x)
run-wkC le (top O ev p) x = refl
run-wkC le (pa W C)     x = run-wkC (λ e → proj₁ e , le (proj₂ e)) C (W ⊕ x)
run-wkC le (pψ q C)     x = run-wkC (λ e → proj₁ e , le (proj₂ e)) C (ψᵒ q x)
run-wkC le (pι q C)     x = run-wkC le C (ι q x)
run-wkC le (ptr e C)    x = run-wkC le C (trO e x)
run-wkC le (ptr⁻ e C)   x = run-wkC le C (tr⁻O e x)
```

相似: 同样的栈形, 底部的证据、地板任意.

```agda
infix 4 _≈ᵒ_ _≈ᶜ_
data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set
data _≈ᶜ_ : ∀ {c φ ψ} → Cx c φ → Cx c ψ → Set

data _≈ᵒ_ where
  idO  : idO ≈ᵒ idO
  tlo  : ∀ {c k k′} {C : Cx c (flo k)} {C′ : Cx c (flo k′)} → C ≈ᶜ C′ → tlo C ≈ᵒ tlo C′
  addo : ∀ {k k′ ℓ ℓ′} {O : Obs ℓ} {O′ : Obs ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → ℓ ≅ᴵ ℓ′ → a ≅ˢ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′
  tro  : ∀ {a a′ b b′} {O : Obs b} {O′ : Obs b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} → O ≈ᵒ O′ → tro O e ≈ᵒ tro O′ e′
  tr⁻o : ∀ {a a′ b b′} {O : Obs a} {O′ : Obs a′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} → O ≈ᵒ O′ → tr⁻o O e ≈ᵒ tr⁻o O′ e′

data _≈ᶜ_ where
  top : ∀ {c φ ψ i ℓ ℓ′} {O O′ : Obs i} {ev : Ev ℓ φ} {ev′ : Ev ℓ′ ψ} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} → O ≈ᵒ O′ → _≈ᶜ_ {c} (top O ev p) (top O′ ev′ p′)
  pa  : ∀ {c a φ ψ} {W : O c a} {C : Cx c (a ⊔ φ)} {C′ : Cx c (a ⊔ ψ)} → Rᵒ c c W W → C ≈ᶜ C′ → pa W C ≈ᶜ pa W C′
  pψ  : ∀ {c t φ ψ} {q : t <ᴵ c} {C : Cx t (Fl ⊔ φ)} {C′ : Cx t (Fl ⊔ ψ)} → C ≈ᶜ C′ → pψ q C ≈ᶜ pψ q C′
  pι  : ∀ {c d φ ψ} {q : c ◃ d} {C : Cx d φ} {C′ : Cx d ψ} → C ≈ᶜ C′ → pι q C ≈ᶜ pι q C′
  ptr  : ∀ {a b φ ψ} {e e′ : a ≅ᴵ b} {C : Cx b φ} {C′ : Cx b ψ} → C ≈ᶜ C′ → ptr e C ≈ᶜ ptr e′ C′
  ptr⁻ : ∀ {a b φ ψ} {e e′ : a ≅ᴵ b} {C : Cx a φ} {C′ : Cx a ψ} → C ≈ᶜ C′ → ptr⁻ e C ≈ᶜ ptr⁻ e′ C′

run-≅  : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordˢ k} {x′ : Ordˢ k′} → O ≈ᵒ O′ → x ≅ˢ x′ → run O x ≅ˢ run O′ x′
runᶜ-≅ : ∀ {c φ ψ} {C : Cx c φ} {C′ : Cx c ψ} {x : O c φ} {x′ : O c ψ} → C ≈ᶜ C′ → Rᵒ c c x x′ → runᶜ C x ≅ˢ runᶜ C′ x′
run-≅ idO          d = d
run-≅ (tlo o)      d = runᶜ-≅ o (R-tl d)
run-≅ (addo o k a) d = run-≅ o (addˢ-≅ k a d)
run-≅ (tro {e = e} {e′ = e′} o)  d = run-≅ o (trˢ-≅ e (≅-trˢ e′ d))
run-≅ (tr⁻o {e = e} {e′ = e′} o) d = run-≅ o (tr⁻ˢ-≅ e (≅-tr⁻ˢ e′ d))
runᶜ-≅ (top {i = i} o) r = run-≅ o (R→≈ r _ _ _ _ (≅ᴵ-refl i))
runᶜ-≅ (pa {a = a} rW o) r = runᶜ-≅ o (R-⊕ (∼ᶠ-refl a) rW r)
runᶜ-≅ (pψ {q = q} o) r = runᶜ-≅ o (R-ψ q q (≅ᴵ-refl _) r)
runᶜ-≅ (pι {q = q} o) r = runᶜ-≅ o (R-ι q q r)
runᶜ-≅ (ptr {e = e} {e′ = e′} o) r = runᶜ-≅ o (R-trˡ e (R-trʳ e′ r))
runᶜ-≅ (ptr⁻ {e = e} {e′ = e′} o) r = runᶜ-≅ o (R-tr⁻ˡ e (R-tr⁻ʳ e′ r))

≈ᵒ-reflˡ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O ≈ᵒ O
≈ᶜ-reflˡ : ∀ {c φ ψ} {C : Cx c φ} {C′ : Cx c ψ} → C ≈ᶜ C′ → C ≈ᶜ C
≈ᵒ-reflˡ idO          = idO
≈ᵒ-reflˡ (tlo o)      = tlo (≈ᶜ-reflˡ o)
≈ᵒ-reflˡ (addo o k e) = addo (≈ᵒ-reflˡ o) (≅ᴵ-refl _) (≅ˢ-reflˡ e)
≈ᵒ-reflˡ (tro o)      = tro (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (tr⁻o o)     = tr⁻o (≈ᵒ-reflˡ o)
≈ᶜ-reflˡ (top o)   = top (≈ᵒ-reflˡ o)
≈ᶜ-reflˡ (pa r o)  = pa r (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (pψ o)    = pψ (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (pι o)    = pι (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (ptr o)   = ptr (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (ptr⁻ o)  = ptr⁻ (≈ᶜ-reflˡ o)

≈ᵒ-reflʳ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O′
≈ᶜ-reflʳ : ∀ {c φ ψ} {C : Cx c φ} {C′ : Cx c ψ} → C ≈ᶜ C′ → C′ ≈ᶜ C′
≈ᵒ-reflʳ idO          = idO
≈ᵒ-reflʳ (tlo o)      = tlo (≈ᶜ-reflʳ o)
≈ᵒ-reflʳ (addo o k e) = addo (≈ᵒ-reflʳ o) (≅ᴵ-refl _) (≅ˢ-reflʳ e)
≈ᵒ-reflʳ (tro o)      = tro (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (tr⁻o o)     = tr⁻o (≈ᵒ-reflʳ o)
≈ᶜ-reflʳ (top o)   = top (≈ᵒ-reflʳ o)
≈ᶜ-reflʳ (pa r o)  = pa r (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (pψ o)    = pψ (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (pι o)    = pι (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (ptr o)   = ptr (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (ptr⁻ o)  = ptr⁻ (≈ᶜ-reflʳ o)

≈ᶜ-wkʳ : ∀ {c χ φ ψ} {C : Cx c χ} {C′ : Cx c ψ} (le : ∀ {L} → Ev L ψ → Ev L φ) → C ≈ᶜ C′ → C ≈ᶜ wkC le C′
≈ᶜ-wkʳ le (top o)  = top o
≈ᶜ-wkʳ le (pa r o) = pa r (≈ᶜ-wkʳ (λ e → proj₁ e , le (proj₂ e)) o)
≈ᶜ-wkʳ le (pψ o)   = pψ (≈ᶜ-wkʳ (λ e → proj₁ e , le (proj₂ e)) o)
≈ᶜ-wkʳ le (pι o)   = pι (≈ᶜ-wkʳ le o)
≈ᶜ-wkʳ le (ptr o)  = ptr (≈ᶜ-wkʳ le o)
≈ᶜ-wkʳ le (ptr⁻ o) = ptr⁻ (≈ᶜ-wkʳ le o)

≈ᶜ-wkˡ : ∀ {c χ φ ψ} {C : Cx c ψ} {C′ : Cx c χ} (le : ∀ {L} → Ev L ψ → Ev L φ) → C ≈ᶜ C′ → wkC le C ≈ᶜ C′
≈ᶜ-wkˡ le (top o)  = top o
≈ᶜ-wkˡ le (pa r o) = pa r (≈ᶜ-wkˡ (λ e → proj₁ e , le (proj₂ e)) o)
≈ᶜ-wkˡ le (pψ o)   = pψ (≈ᶜ-wkˡ (λ e → proj₁ e , le (proj₂ e)) o)
≈ᶜ-wkˡ le (pι o)   = pι (≈ᶜ-wkˡ le o)
≈ᶜ-wkˡ le (ptr o)  = ptr (≈ᶜ-wkˡ le o)
≈ᶜ-wkˡ le (ptr⁻ o) = ptr⁻ (≈ᶜ-wkˡ le o)

wkC-comp : ∀ {c φ ψ χ} (A : ∀ {L} → Ev L ψ → Ev L φ) (B : ∀ {L} → Ev L χ → Ev L ψ) (C : Cx c χ) → wkC A (wkC B C) ≡ wkC (λ e → A (B e)) C
wkC-comp A B (top O ev p) = refl
wkC-comp A B (pa W C) = cong (pa W) (wkC-comp (λ e → proj₁ e , A (proj₂ e)) (λ e → proj₁ e , B (proj₂ e)) C)
wkC-comp A B (pψ q C) = cong (pψ q) (wkC-comp (λ e → proj₁ e , A (proj₂ e)) (λ e → proj₁ e , B (proj₂ e)) C)
wkC-comp A B (pι q C) = cong (pι q) (wkC-comp A B C)
wkC-comp A B (ptr e C) = cong (ptr e) (wkC-comp A B C)
wkC-comp A B (ptr⁻ e C) = cong (ptr⁻ e) (wkC-comp A B C)

wkC-id : ∀ {c φ} (C : Cx c φ) → wkC (λ e → e) C ≡ C
wkC-id (top O ev p) = refl
wkC-id (pa W C) = cong (pa W) (wkC-id C)
wkC-id (pψ q C) = cong (pψ q) (wkC-id C)
wkC-id (pι q C) = cong (pι q) (wkC-id C)
wkC-id (ptr e C) = cong (ptr e) (wkC-id C)
wkC-id (ptr⁻ e C) = cong (ptr⁻ e) (wkC-id C)
```
