# 数据树上的无符号闭包定理 (一): 上下文就是数据

> 接 [Uniform4Base](Uniform4Base.lagda.md), [UniformNF3Eq](UniformNF3Eq.lagda.md). 结论先说:
>
> 1. **观测只有一族, 没有深度.** 树层上下文 `Cx c φ` 只有四个构造子: `pa W C` ($x\mapsto C(W\oplus x)$), `pψ q C` ($x\mapsto C(\psi_{\Omega+t}x)$), `pι q C` ($x\mapsto C(\iota x)$), 底部 `top O ev p` ($x\mapsto O(\bar\psi x)$). 值层 `Obs k` 把旧的 `fo`/`fo1` 换成一个 `tlo C`: $y\mapsto C(\mathtt{tl}\,y)$. `fo1`/`fo2`/… 的深度塔消失: 它们都是 `tlo (pa W (pψ q …))`.
> 2. **`pw` 不是构造子.** `wkC le C` 按 $C$ 递归把弱化推到底部的 `ev` 上, `run-wkC`: $\mathtt{run}\,(\mathtt{wkC}\,le\,C)\,x\equiv\mathtt{run}\,C\,(\mathtt{owk}\,le\,x)$, 每一步都是定义性的.
> 3. **`Rᵒ`: 数据树的互模拟.** 取自 [Uniform4Rel](Uniform4Rel.lagda.md) §1–§5, 值层关系从 $\cong^\mathsf A$ 换成 `≅ˢ`, `rwk` 拆成单侧的 `rwkˡ`/`rwkʳ`. `R-tl` 的前提是根地板的对齐函数 $k_1\cong k_2\to\varphi\sim\varphi'$. `run-≅`: 相似上下文加相关树, 计值相关.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF4Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≡-irrelevant)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; toZ; trˢ; tr⁻ˢ; Ωˢ; addˢ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; R→≅ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; tf;
  trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; addˢ-≅; ≅ˢ-sym; ≅ˢ-reflˡ; ≅ˢ-reflʳ; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl)
open import OCF.Align.Uniform4Base
```

## §1 互模拟

`flo∼`: 紧地板对齐. 分层方式同 `O₊`/`Us`.

```agda
flo∼ : ∀ {k k′} → k ≅ᴵ k′ → flo k ∼ᶠ flo k′
flo∼ z≅     = fz∼
flo∼ (s≅ e) = fk∼ e
flo∼ (l≅ h) = fb∼ (l≅ h)

castO : ∀ {k k′ ξ} → k ≡ k′ → O k ξ → O k′ ξ
castO refl z = z

module _ (c : ℕ) (LR : ∀ {k} → k <ᴸ c → ∀ {ξ ξ′} → O k ξ → O k ξ′ → Set) where
  data R₊ : ∀ {φ ψ} → O c φ → O c ψ → Set where
    rz : ∀ {φ ψ} → R₊ {φ} {ψ} o0 o0
    rs : ∀ {φ ψ} {a : O c φ} {a′ : O c ψ} → φ ∼ᶠ ψ → R₊ a a′ → R₊ (os a) (os a′)
    rl : ∀ {φ ψ} {F : ℕ → O c φ} {F′ : ℕ → O c ψ} → (∀ n → R₊ (F n) (F′ n)) → R₊ (ol F) (ol F′)
    ri : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → O c φ} {f′ : Ordˢ j′ → O c ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → R₊ (f x) (f′ y)) → R₊ (oi ac f) (oi ac′ f′)
    rŝ : ∀ {φ ψ c₁ c₂} {t : O c φ} {t′ : O c ψ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → O c φ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O c ψ} →
         c₁ ≅ᴵ c₂ → R₊ t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (g η e) (g′ η′ e′)) → R₊ (oŝ c₁ t g) (oŝ c₂ t′ g′)
    rĉ : ∀ {φ ψ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : O c φ} {o₀′ : O c ψ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → O c φ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O c ψ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → R₊ o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (o η e) (o′ η′ e′)) → R₊ (oĉ c₁ z zg o₀ o) (oĉ c₂ z′ zg′ o₀′ o′)
    rclo : ∀ {φ ψ} {t : O c (φ ⊔ fk zero)} {t′ : O c (ψ ⊔ fk zero)} {g : (η : Ordᴵ) → O c (φ ⊔ fk η)} {g′ : (η : Ordᴵ) → O c (ψ ⊔ fk η)} →
         φ ∼ᶠ ψ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (oclo t g) (oclo t′ g′)
    rwkˡ : ∀ {φ ψ φ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {x : O c φ} {x′ : O c ψ} → R₊ x x′ → R₊ (owk le x) x′
    rwkʳ : ∀ {φ ψ ψ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {x : O c φ} {x′ : O c ψ} → R₊ x x′ → R₊ x (owk le′ x′)
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

rwk : ∀ {c φ ψ φ′ ψ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {x : O c φ} {x′ : O c ψ} → Rᵒ c x x′ → Rᵒ c (owk le x) (owk le′ x′)
rwk r = rwkˡ (rwkʳ r)
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
R-⊕ s rW (rwkˡ r) = rwkˡ (R-⊕ s rW r)
R-⊕ s rW (rwkʳ r) = rwkʳ (R-⊕ s rW r)
R-⊕ s rW (rΩ ek sψ b f) = rΩ ek (⊔∼ s sψ) b (λ ξ ξ′ d z z′ l → rwk (R-⊕ s rW (f ξ ξ′ d z z′ l)))

R-ι : ∀ {c d φ ψ} (q : c <ᴸ d) {x : O c φ} {x′ : O c ψ} → Rᵒ c x x′ → Rᵒ d (ι q x) (ι q x′)
R-ι q rz = rz
R-ι q (rs sa r) = rs sa (R-ι q r)
R-ι q (rl h) = rl (λ n → R-ι q (h n))
R-ι q (ri e h) = ri e (λ x y d → R-ι q (h x y d))
R-ι q (rŝ e r h) = rŝ e (R-ι q r) (λ η ee η′ e′ d → R-ι q (h η ee η′ e′ d))
R-ι q (rĉ e dz dg r h) = rĉ e dz dg (R-ι q r) (λ η ee η′ e′ d → R-ι q (h η ee η′ e′ d))
R-ι q (rclo s r h) = rclo s (R-ι q r) (λ η η′ d → R-ι q (h η η′ d))
R-ι q (rwkˡ r) = rwkˡ (R-ι q r)
R-ι q (rwkʳ r) = rwkʳ (R-ι q r)
R-ι {d = dd} q (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} refl s b f) =
  rΩ {r = tr< r q} {r′ = tr< r′ q} refl s (intoR (tr< r q) (outR r b))
     (λ ξ ξ′ e z z′ l → subst₂ (λ w w′ → Rᵒ dd (ι q (h ξ (intoU r w))) (ι q (h′ ξ′ (intoU r′ w′)))) (sym (out-intoU′ (tr< r q) z)) (sym (out-intoU′ (tr< r′ q) z′))
                                (R-ι q (f ξ ξ′ e z z′ (intoR r (outR (tr< r q) l)))))
```

## §3 尾巴与 $\Omega_{\Omega+c}$

```agda
R-tl : ∀ {c k₁ k₂} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       a ≅ˢ b → Rᵒ c (tl (flo k₁) cv a) (tl (flo k₂) cv′ b)
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

R-tlΩ : ∀ {c η η′ φ φ′} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} → η ≅ᴵ η′ → φ ∼ᶠ φ′ → Rᵒ c (tl φ cv (Ωˢ η)) (tl φ′ cv′ (Ωˢ η′))
R-tlΩ z≅ s = rs s rz
R-tlΩ (s≅ e) s = ri e (λ x y d → rwk (R-tl d))
R-tlΩ (l≅ h) s = rl (λ n → rwk (R-tl (Ωˢ-≅ (h n))))

RΩ̇ : ∀ c → Rᵒ c (Ω̇ c) (Ω̇ c)
RΩ̇ zero = rclo (∼ᶠ-refl fz) (R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
  (λ η η′ eη → R-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
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
R-ψ q q′ (rwkˡ r) = rwkˡ (R-ψ q q′ r)
R-ψ q q′ (rwkʳ r) = rwkʳ (R-ψ q q′ r)
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

r∅ : ∅ᴿ ≈ᴿ ∅ᴿ
r∅ ev p ev′ p′ ei = Ωˢ-≅ ei

R→≈ : ∀ {c φ ψ} {x : O c φ} {x′ : O c ψ} → Rᵒ c x x′ → ψ̄ x ≈ᴿ ψ̄ x′
R→≈ rz = wkR _ _ r∅
R→≈ (rs s r) = sucR (R→≈ r)
R→≈ (rl h) = limR (λ n → R→≈ (h n))
R→≈ (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} e h) = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ (f x)} {H′ = λ x → ψ̄ (f′ x)} e (λ x y d → R→≈ (h x y d))
R→≈ (rŝ e r h) = ŝR e (R→≈ r) (λ η ee η′ e′ d → R→≈ (h η ee η′ e′ d))
R→≈ (rĉ e dz dg r h) = ĉR e dz dg (R→≈ r) (λ η ee η′ e′ d → R→≈ (h η ee η′ e′ d))
R→≈ (rclo {t = t} {t′} {g} {g′} s r h) = cloR {t = ψ̄ t} {g = λ η → ψ̄ (g η)} {t′ = ψ̄ t′} {g′ = λ η → ψ̄ (g′ η)} s (R→≈ r) (λ η η′ d → R→≈ (h η η′ d))
R→≈ (rwkˡ {le = le} r) = wkR le (λ e → e) (R→≈ r)
R→≈ (rwkʳ {le′ = le′} r) = wkR (λ e → e) le′ (R→≈ r)
R→≈ (rΩ {φ = φ} {ψ} {fe = fe} {fe′} {r} {r′} {h} {h′} refl s b f) =
  limR (λ n → wkR _ _ (R→≈ (f φ ψ s _ _ (intoR r (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} s b f n)))))
```

## §6 上下文

```agda
data Obs : Ordᴵ → Set
data Cx : ℕ → Flr → Set

data Obs where
  idO  : Obs zero
  tlo  : ∀ {c k} → Cx c (flo k) → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordˢ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

data Cx where
  top : ∀ {c φ i ℓ} → Obs i → Ev ℓ φ → i <ᴵ ℓ → Cx c φ
  pa  : ∀ {c a φ} → O c a → Cx c (a ⊔ φ) → Cx c φ
  pψ  : ∀ {c t φ} → t <ᴸ c → Cx t (Fl ⊔ φ) → Cx c φ
  pι  : ∀ {c d φ} → c <ᴸ d → Cx d φ → Cx c φ

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

wkC : ∀ {c φ ψ} → (∀ {L} → Ev L ψ → Ev L φ) → Cx c ψ → Cx c φ
wkC le (top O ev p) = top O (le ev) p
wkC le (pa W C)     = pa W (wkC (λ e → proj₁ e , le (proj₂ e)) C)
wkC le (pψ q C)     = pψ q (wkC (λ e → proj₁ e , le (proj₂ e)) C)
wkC le (pι q C)     = pι q (wkC le C)

run-wkC : ∀ {c φ ψ} (le : ∀ {L} → Ev L ψ → Ev L φ) (C : Cx c ψ) (x : O c φ) → runᶜ (wkC le C) x ≡ runᶜ C (owk le x)
run-wkC le (top O ev p) x = refl
run-wkC le (pa W C)     x = run-wkC (λ e → proj₁ e , le (proj₂ e)) C (W ⊕ x)
run-wkC le (pψ q C)     x = run-wkC (λ e → proj₁ e , le (proj₂ e)) C (ψᵒ q x)
run-wkC le (pι q C)     x = run-wkC le C (ι q x)
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
  pa  : ∀ {c a φ ψ} {W : O c a} {C : Cx c (a ⊔ φ)} {C′ : Cx c (a ⊔ ψ)} → Rᵒ c W W → C ≈ᶜ C′ → pa W C ≈ᶜ pa W C′
  pψ  : ∀ {c t φ ψ} {q : t <ᴸ c} {C : Cx t (Fl ⊔ φ)} {C′ : Cx t (Fl ⊔ ψ)} → C ≈ᶜ C′ → pψ q C ≈ᶜ pψ q C′
  pι  : ∀ {c d φ ψ} {q : c <ᴸ d} {C : Cx d φ} {C′ : Cx d ψ} → C ≈ᶜ C′ → pι q C ≈ᶜ pι q C′

run-≅  : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordˢ k} {x′ : Ordˢ k′} → O ≈ᵒ O′ → x ≅ˢ x′ → run O x ≅ˢ run O′ x′
runᶜ-≅ : ∀ {c φ ψ} {C : Cx c φ} {C′ : Cx c ψ} {x : O c φ} {x′ : O c ψ} → C ≈ᶜ C′ → Rᵒ c x x′ → runᶜ C x ≅ˢ runᶜ C′ x′
run-≅ idO          d = d
run-≅ (tlo o)      d = runᶜ-≅ o (R-tl d)
run-≅ (addo o k a) d = run-≅ o (addˢ-≅ k a d)
run-≅ (tro {e = e} {e′ = e′} o)  d = run-≅ o (trˢ-≅ e (≅-trˢ e′ d))
run-≅ (tr⁻o {e = e} {e′ = e′} o) d = run-≅ o (tr⁻ˢ-≅ e (≅-tr⁻ˢ e′ d))
runᶜ-≅ (top {i = i} o) r = run-≅ o (R→≈ r _ _ _ _ (≅ᴵ-refl i))
runᶜ-≅ (pa {a = a} rW o) r = runᶜ-≅ o (R-⊕ (∼ᶠ-refl a) rW r)
runᶜ-≅ (pψ {q = q} o) r = runᶜ-≅ o (R-ψ q q r)
runᶜ-≅ (pι {q = q} o) r = runᶜ-≅ o (R-ι q r)

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

≈ᶜ-wkʳ : ∀ {c χ φ ψ} {C : Cx c χ} {C′ : Cx c ψ} (le : ∀ {L} → Ev L ψ → Ev L φ) → C ≈ᶜ C′ → C ≈ᶜ wkC le C′
≈ᶜ-wkʳ le (top o)  = top o
≈ᶜ-wkʳ le (pa r o) = pa r (≈ᶜ-wkʳ (λ e → proj₁ e , le (proj₂ e)) o)
≈ᶜ-wkʳ le (pψ o)   = pψ (≈ᶜ-wkʳ (λ e → proj₁ e , le (proj₂ e)) o)
≈ᶜ-wkʳ le (pι o)   = pι (≈ᶜ-wkʳ le o)

≈ᶜ-wkˡ : ∀ {c χ φ ψ} {C : Cx c ψ} {C′ : Cx c χ} (le : ∀ {L} → Ev L ψ → Ev L φ) → C ≈ᶜ C′ → wkC le C ≈ᶜ C′
≈ᶜ-wkˡ le (top o)  = top o
≈ᶜ-wkˡ le (pa r o) = pa r (≈ᶜ-wkˡ (λ e → proj₁ e , le (proj₂ e)) o)
≈ᶜ-wkˡ le (pψ o)   = pψ (≈ᶜ-wkˡ (λ e → proj₁ e , le (proj₂ e)) o)
≈ᶜ-wkˡ le (pι o)   = pι (≈ᶜ-wkˡ le o)

wkC-comp : ∀ {c φ ψ χ} (A : ∀ {L} → Ev L ψ → Ev L φ) (B : ∀ {L} → Ev L χ → Ev L ψ) (C : Cx c χ) → wkC A (wkC B C) ≡ wkC (λ e → A (B e)) C
wkC-comp A B (top O ev p) = refl
wkC-comp A B (pa W C) = cong (pa W) (wkC-comp (λ e → proj₁ e , A (proj₂ e)) (λ e → proj₁ e , B (proj₂ e)) C)
wkC-comp A B (pψ q C) = cong (pψ q) (wkC-comp (λ e → proj₁ e , A (proj₂ e)) (λ e → proj₁ e , B (proj₂ e)) C)
wkC-comp A B (pι q C) = cong (pι q) (wkC-comp A B C)

wkC-id : ∀ {c φ} (C : Cx c φ) → wkC (λ e → e) C ≡ C
wkC-id (top O ev p) = refl
wkC-id (pa W C) = cong (pa W) (wkC-id C)
wkC-id (pψ q C) = cong (pψ q) (wkC-id C)
wkC-id (pι q C) = cong (pι q) (wkC-id C)
```
