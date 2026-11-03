# 层号参数化的无符号闭包定理 (十四): `Q m α` 上的互模拟, `oev` 跨 $\ell$

> 接 [Uniform5Syn](Uniform5Syn.lagda.md), [Uniform5SynPsi](Uniform5SynPsi.lagda.md), 由 [UniformNF5Base](UniformNF5Base.lagda.md) §1–§6 经脚本改写. **这是 `oev` 的互模拟, 不是 `Q` 上的闭包定理; 它是 [UniformNF5Main](UniformNF5Main.lagda.md) §4 判断的一个证据.** 不导入记号. 结论先说:
>
> 1. **`rev`: 推迟节点的互模拟是跨环境的.** `rev s h`: 对一切 $e:$ `Ev L φ`, $e′:$ `Ev L′ ψ`, $f\,e$ 与 $f′\,e′$ 相关, $L$, $L′$ 独立.
> 2. **`R-ψ≡`: 这个跨 $\ell$ 的相关在 `ψᵒ` 下成立.** 比较 `<ᴵ-dec` 在两个不同的环境 $\ell$, $\ell′$ 下做, 结果模 $\cong$ 一致: 非对角由 `clash` 排除, 与 `R-ψ` 的 `rΩ` 行是同一个论证. [Uniform5Assess](Uniform5Assess.lagda.md) §3 记为未写的那一件, 在无标签一侧写完了, 没有新东西.
> 3. **`R→≈`: 求值.** `rev` 行直接取 `h ev ev′`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF5SynRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; toZ; trˢ; tr⁻ˢ; Ωˢ; addˢ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; R→≅ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅;
  trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; addˢ-≅; ≅ˢ-sym; ≅ˢ-reflˡ; ≅ˢ-reflʳ; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR) renaming (tf to tfE)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl)
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2; _<ᴸ_; zero; suc; tr<)
open import OCF.Align.Uniform4Two using (<◃)
open import OCF.Align.Uniform5Syn
open import OCF.Align.Uniform5SynPsi
open import OCF.Align.UniformNF5Base using (flo∼; clash)
```

## §1 互模拟

```agda
out-intoU : ∀ {m c k} (r : k ◃ c) {ξ} (z : Q m k ξ) → outU r (intoU r z) ≡ z
out-intoU zero      z = refl
out-intoU (suc r)   z = out-intoU r z
out-intoU (self n)  z = refl
out-intoU (lim n r) z = out-intoU r z

out-intoV : ∀ {m n} (q : n <ᴸ m) {k ξ} (z : Q n k ξ) → outV q (intoV q z) ≡ z
out-intoV zero    z = refl
out-intoV (suc q) z = out-intoV q z

module _ (m : ℕ) (a b : Ordᴵ) (LR : ∀ {k} → k ◃ a → ∀ {k′ ξ ξ′} → Q m k ξ → Q m k′ ξ′ → Set) (LV : ∀ {n} → n <ᴸ m → ∀ {k k′ ξ ξ′} → Q n k ξ → Q n k′ ξ′ → Set) where
  data R₊ : ∀ {φ ψ} → Q m a φ → Q m b ψ → Set where
    rz : ∀ {φ ψ} → R₊ {φ} {ψ} o0 o0
    rs : ∀ {φ ψ} {p : Q m a φ} {p′ : Q m b ψ} → φ ∼ᶠ ψ → R₊ p p′ → R₊ (os p) (os p′)
    rl : ∀ {φ ψ} {F : ℕ → Q m a φ} {F′ : ℕ → Q m b ψ} → (∀ n → R₊ (F n) (F′ n)) → R₊ (ol F) (ol F′)
    ri : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → Q m a φ} {f′ : Ordˢ j′ → Q m b ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → R₊ (f x) (f′ y)) → R₊ (oi ac f) (oi ac′ f′)
    rŝ : ∀ {φ ψ c₁ c₂} {t : Q m a φ} {t′ : Q m b ψ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q m b ψ} →
         c₁ ≅ᴵ c₂ → R₊ t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (g η e) (g′ η′ e′)) → R₊ (oŝ c₁ t g) (oŝ c₂ t′ g′)
    rĉ : ∀ {φ ψ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : Q m a φ} {o₀′ : Q m b ψ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q m b ψ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → R₊ o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (o η e) (o′ η′ e′)) → R₊ (oĉ c₁ z zg o₀ o) (oĉ c₂ z′ zg′ o₀′ o′)
    rclo : ∀ {φ ψ} {t : Q m a (φ ⊔ fk zero)} {t′ : Q m b (ψ ⊔ fk zero)} {g : (η : Ordᴵ) → Q m a (φ ⊔ fk η)} {g′ : (η : Ordᴵ) → Q m b (ψ ⊔ fk η)} →
         φ ∼ᶠ ψ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (oclo t g) (oclo t′ g′)
    rwkˡ : ∀ {φ ψ φ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {x : Q m a φ} {x′ : Q m b ψ} → R₊ x x′ → R₊ (owk le x) x′
    rwkʳ : ∀ {φ ψ ψ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {x : Q m a φ} {x′ : Q m b ψ} → R₊ x x′ → R₊ x (owk le′ x′)
    rΩ : ∀ {φ ψ k k′} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r : k <ᴵ a} {r′ : k′ <ᴵ b}
         {h : ∀ ξ → Us m k (<→◃ r) ξ → Q m a (ξ ⊔ φ)} {h′ : ∀ ξ → Us m k′ (<→◃ r′) ξ → Q m b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
         (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : Q m k ξ) (z′ : Q m k′ ξ′) → LR (<→◃ r) z z′ → R₊ (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) → R₊ (oΩ fe r h) (oΩ fe′ r′ h′)
    rΩ↓ : ∀ {φ ψ n k k′} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {q q′ : n <ᴸ m} {ac : ∀ {L} → Ev L φ → k <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → k′ <ᴵ L}
         {h : ∀ ξ → Vs m q k ξ → Q m a (ξ ⊔ φ)} {h′ : ∀ ξ → Vs m q′ k′ ξ → Q m b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
         (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : Q n k ξ) (z′ : Q n k′ ξ′) → LV q z z′ → R₊ (h ξ (intoV q z)) (h′ ξ′ (intoV q′ z′))) → R₊ (oΩ↓ fe q ac h) (oΩ↓ fe′ q′ ac′ h′)
    rev : ∀ {φ ψ} {f : ∀ {L} → Ev L φ → Q m a φ} {f′ : ∀ {L} → Ev L ψ → Q m b ψ} → φ ∼ᶠ ψ →
         (∀ {L L′} (e : Ev L φ) (e′ : Ev L′ ψ) → R₊ (f e) (f′ e′)) → R₊ (oev f) (oev f′)

Rᵒ : ∀ m a b {φ ψ} → Q m a φ → Q m b ψ → Set
LRᵒ : ∀ m a {k} → k ◃ a → ∀ {k′ ξ ξ′} → Q m k ξ → Q m k′ ξ′ → Set
LVᵒ : ∀ m {n} → n <ᴸ m → ∀ {k k′ ξ ξ′} → Q n k ξ → Q n k′ ξ′ → Set
Rᵒ m a b x y = R₊ m a b (LRᵒ m a) (LVᵒ m) x y
LRᵒ m (suc k)   zero      {k′} x y = Rᵒ m k k′ x y
LRᵒ m (suc c)   (suc r)   x y = LRᵒ m c r x y
LRᵒ m (lim f s) (self n)  {k′} x y = Rᵒ m (f n) k′ x y
LRᵒ m (lim f s) (lim n r) x y = LRᵒ m (f n) r x y
LVᵒ (suc m) zero    {k} {k′} x y = Rᵒ m k k′ x y
LVᵒ (suc m) (suc q) x y = LVᵒ m q x y

outR : ∀ {m c k} (r : k ◃ c) {k′ ξ ξ′} {z : Q m k ξ} {z′ : Q m k′ ξ′} → LRᵒ m c r z z′ → Rᵒ m k k′ z z′
outR zero      l = l
outR (suc r)   l = outR r l
outR (self n)  l = l
outR (lim n r) l = outR r l

intoR : ∀ {m c k} (r : k ◃ c) {k′ ξ ξ′} {z : Q m k ξ} {z′ : Q m k′ ξ′} → Rᵒ m k k′ z z′ → LRᵒ m c r z z′
intoR zero      l = l
intoR (suc r)   l = intoR r l
intoR (self n)  l = l
intoR (lim n r) l = intoR r l

outRV : ∀ {m n} (q : n <ᴸ m) {k k′ ξ ξ′} {z : Q n k ξ} {z′ : Q n k′ ξ′} → LVᵒ m q z z′ → Rᵒ n k k′ z z′
outRV zero    l = l
outRV (suc q) l = outRV q l

intoRV : ∀ {m n} (q : n <ᴸ m) {k k′ ξ ξ′} {z : Q n k ξ} {z′ : Q n k′ ξ′} → Rᵒ n k k′ z z′ → LVᵒ m q z z′
intoRV zero    l = l
intoRV (suc q) l = intoRV q l

rwk : ∀ {m a b φ ψ φ′ ψ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {x : Q m a φ} {x′ : Q m b ψ} → Rᵒ m a b x x′ → Rᵒ m a b (owk le x) (owk le′ x′)
rwk r = rwkˡ (rwkʳ r)
```

## §2 封闭性

```agda
R-⊕ : ∀ {m a b φ φ′ ψ ψ′} {W : Q m a φ} {W′ : Q m b φ′} {t : Q m a ψ} {t′ : Q m b ψ′} → φ ∼ᶠ φ′ → Rᵒ m a b W W′ → Rᵒ m a b t t′ → Rᵒ m a b (W ⊕ t) (W′ ⊕ t′)
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
R-⊕ s rW (rΩ↓ ek sψ f) = rΩ↓ ek (⊔∼ s sψ) (λ ξ ξ′ d z z′ l → rwk (R-⊕ s rW (f ξ ξ′ d z z′ l)))
R-⊕ s rW (rev sψ h) = rev (⊔∼ s sψ) (λ e e′ → R-⊕ s rW (h (proj₂ e) (proj₂ e′)))

R-ιˡ : ∀ {m a b c φ ψ} (q : a ◃ c) {x : Q m a φ} {x′ : Q m b ψ} → Rᵒ m a b x x′ → Rᵒ m c b (ι q x) x′
R-ιˡ q rz = rz
R-ιˡ q (rs sa r) = rs sa (R-ιˡ q r)
R-ιˡ q (rl h) = rl (λ n → R-ιˡ q (h n))
R-ιˡ q (ri e h) = ri e (λ x y d → R-ιˡ q (h x y d))
R-ιˡ q (rŝ e r h) = rŝ e (R-ιˡ q r) (λ η ee η′ e′ d → R-ιˡ q (h η ee η′ e′ d))
R-ιˡ q (rĉ e dz dg r h) = rĉ e dz dg (R-ιˡ q r) (λ η ee η′ e′ d → R-ιˡ q (h η ee η′ e′ d))
R-ιˡ q (rclo s r h) = rclo s (R-ιˡ q r) (λ η η′ d → R-ιˡ q (h η η′ d))
R-ιˡ q (rwkˡ r) = rwkˡ (R-ιˡ q r)
R-ιˡ q (rwkʳ r) = rwkʳ (R-ιˡ q r)
R-ιˡ q (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-ιˡ q (f ξ ξ′ d z z′ l))
R-ιˡ q (rev s h) = rev s (λ e e′ → R-ιˡ q (h e e′))
R-ιˡ {b = b} {c = c} q (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f) =
  rΩ {r = <◃ r q} {r′ = r′} ek s
     (λ ξ ξ′ e z z′ l → subst (λ w → Rᵒ _ c b (ι q (h ξ (intoU (<→◃ r) w))) (h′ ξ′ (intoU (<→◃ r′) z′))) (sym (out-intoU (<→◃ (<◃ r q)) z))
                              (R-ιˡ q (f ξ ξ′ e _ z′ (intoR (<→◃ r) (outR (<→◃ (<◃ r q)) l)))))

R-ιʳ : ∀ {m a b d φ ψ} (q : b ◃ d) {x : Q m a φ} {x′ : Q m b ψ} → Rᵒ m a b x x′ → Rᵒ m a d x (ι q x′)
R-ιʳ q rz = rz
R-ιʳ q (rs sa r) = rs sa (R-ιʳ q r)
R-ιʳ q (rl h) = rl (λ n → R-ιʳ q (h n))
R-ιʳ q (ri e h) = ri e (λ x y d → R-ιʳ q (h x y d))
R-ιʳ q (rŝ e r h) = rŝ e (R-ιʳ q r) (λ η ee η′ e′ d → R-ιʳ q (h η ee η′ e′ d))
R-ιʳ q (rĉ e dz dg r h) = rĉ e dz dg (R-ιʳ q r) (λ η ee η′ e′ d → R-ιʳ q (h η ee η′ e′ d))
R-ιʳ q (rclo s r h) = rclo s (R-ιʳ q r) (λ η η′ d → R-ιʳ q (h η η′ d))
R-ιʳ q (rwkˡ r) = rwkˡ (R-ιʳ q r)
R-ιʳ q (rwkʳ r) = rwkʳ (R-ιʳ q r)
R-ιʳ q (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-ιʳ q (f ξ ξ′ d z z′ l))
R-ιʳ q (rev s h) = rev s (λ e e′ → R-ιʳ q (h e e′))
R-ιʳ {a = a} {d = dd} q (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f) =
  rΩ {r = r} {r′ = <◃ r′ q} ek s
     (λ ξ ξ′ e z z′ l → subst (λ w → Rᵒ _ a dd (h ξ (intoU (<→◃ r) z)) (ι q (h′ ξ′ (intoU (<→◃ r′) w)))) (sym (out-intoU (<→◃ (<◃ r′ q)) z′))
                              (R-ιʳ q (f ξ ξ′ e z _ l)))

R-ι : ∀ {m a b c d φ ψ} (q : a ◃ c) (q′ : b ◃ d) {x : Q m a φ} {x′ : Q m b ψ} → Rᵒ m a b x x′ → Rᵒ m c d (ι q x) (ι q′ x′)
R-ι q q′ r = R-ιˡ q (R-ιʳ q′ r)

R-ι↓ : ∀ {n m k k′ α α′ φ ψ} (q q′ : n <ᴸ m) → k ≅ᴵ k′ → {x : Q n k φ} {x′ : Q n k′ ψ} → Rᵒ n k k′ x x′ → Rᵒ m α α′ (ι↓ q x) (ι↓ q′ x′)
R-ι↓ q q′ ek rz = rz
R-ι↓ q q′ ek (rs sa r) = rs (⊔∼ sa (flo∼ ek)) (R-ι↓ q q′ ek r)
R-ι↓ q q′ ek (rl h) = rl (λ n → R-ι↓ q q′ ek (h n))
R-ι↓ q q′ ek (ri e h) = ri e (λ x y d → R-ι↓ q q′ ek (h x y d))
R-ι↓ q q′ ek (rŝ e r h) = rŝ e (R-ι↓ q q′ ek r) (λ η ee η′ e′ d → R-ι↓ q q′ ek (h η ee η′ e′ d))
R-ι↓ q q′ ek (rĉ e dz dg r h) = rĉ e dz dg (R-ι↓ q q′ ek r) (λ η ee η′ e′ d → R-ι↓ q q′ ek (h η ee η′ e′ d))
R-ι↓ q q′ ek (rclo s r h) = rwk (rclo (⊔∼ s (flo∼ ek)) (rwk (R-ι↓ q q′ ek r)) (λ η η′ d → rwk (R-ι↓ q q′ ek (h η η′ d))))
R-ι↓ q q′ ek (rwkˡ r) = rwkˡ (R-ι↓ q q′ ek r)
R-ι↓ q q′ ek (rwkʳ r) = rwkʳ (R-ι↓ q q′ ek r)
R-ι↓ {m = m} {α = α} {α′ = α′} q q′ ek (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek₂ s f) =
  rΩ↓ ek₂ (⊔∼ s (flo∼ ek))
     (λ ξ ξ′ d z z′ l → rwk (subst₂ (λ w w′ → Rᵒ m α α′ (ι↓ q (h ξ (intoU (<→◃ r) w))) (ι↓ q′ (h′ ξ′ (intoU (<→◃ r′) w′)))) (sym (out-intoV q z)) (sym (out-intoV q′ z′))
                            (R-ι↓ q q′ ek (f ξ ξ′ d _ _ (intoR (<→◃ r) (outRV q l))))))
R-ι↓ {m = m} {α = α} {α′ = α′} q q′ ek (rΩ↓ {q = r} {q′ = r′} {h = h} {h′ = h′} ek₂ s f) =
  rΩ↓ ek₂ (⊔∼ s (flo∼ ek))
     (λ ξ ξ′ d z z′ l → rwk (subst₂ (λ w w′ → Rᵒ m α α′ (ι↓ q (h ξ (intoV r w))) (ι↓ q′ (h′ ξ′ (intoV r′ w′)))) (sym (out-intoV (tr< r q) z)) (sym (out-intoV (tr< r′ q′) z′))
                            (R-ι↓ q q′ ek (f ξ ξ′ d _ _ (intoRV r (outRV (tr< r q) l))))))
R-ι↓ q q′ ek (rev s h) = rev (⊔∼ s (flo∼ ek)) (λ e e′ → R-ι↓ q q′ ek (h (proj₁ e) (proj₁ e′)))
```

## §3 尾巴与 $\dot\Omega$

```agda
R-tl : ∀ {m c c′ k₁ k₂} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       a ≅ˢ b → Rᵒ m c c′ (tl (flo k₁) cv a) (tl (flo k₂) cv′ b)
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
R-tl {k₁ = zero} {k₂ = suc _}   (ŝ≅ k ec et eg) = ⊥-elim (tfE k)
R-tl {k₁ = zero} {k₂ = lim _ _} (ŝ≅ k ec et eg) = ⊥-elim (tfE k)
R-tl {k₁ = suc _}   {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tfE (sym k))
R-tl {k₁ = lim _ _} {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tfE (sym k))
R-tl {k₁ = suc _} {k₂ = suc _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = suc _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = suc _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl (ĉ≅ ec dt dg eo eO) = rĉ ec dt dg (R-tl eo) (λ η e η′ e′ eη → R-tl (eO η e η′ e′ eη))

R-tlΩ : ∀ {m c c′ η η′ φ φ′} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} → η ≅ᴵ η′ → φ ∼ᶠ φ′ → Rᵒ m c c′ (tl φ cv (Ωˢ η)) (tl φ′ cv′ (Ωˢ η′))
R-tlΩ z≅ s = rs s rz
R-tlΩ (s≅ e) s = ri e (λ x y d → rwk (R-tl d))
R-tlΩ (l≅ h) s = rl (λ n → rwk (R-tl (Ωˢ-≅ (h n))))

RΩ̇ : ∀ {m a b} → a ≅ᴵ b → Rᵒ m a b (Ω̇ m a) (Ω̇ m b)
RΩ̇ {m = zero} z≅ = rclo (∼ᶠ-refl fz) (R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
  (λ η η′ eη → R-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
RΩ̇ {m = suc m} z≅ = rwk (rclo (∼ᶠ-refl Fl) (R-ι↓ zero zero (≅ᴵ-refl (suc zero)) (RΩ̇ (≅ᴵ-refl (suc zero))))
  (λ η η′ eη → rwk (R-ι↓ zero zero eη (RΩ̇ eη))))
RΩ̇ {m = zero} (s≅ e) = rΩ e (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (λ ξ ξ′ d z z′ l → rwk (R-ι zero zero l))
RΩ̇ {m = zero} (l≅ h) = rl (λ n → R-ι (self n) (self n) (RΩ̇ (h n)))
RΩ̇ {m = suc m} (s≅ e) = rΩ e (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (λ ξ ξ′ d z z′ l → rwk (R-ι zero zero l))
RΩ̇ {m = suc m} (l≅ h) = rl (λ n → R-ι (self n) (self n) (RΩ̇ (h n)))
```

## §4 搬运

```agda
R-trˡ  : ∀ {m a a′ b φ ψ} (e : a ≅ᴵ a′) {x : Q m a φ} {y : Q m b ψ} → Rᵒ m a b x y → Rᵒ m a′ b (trO e x) y
R-tr⁻ˡ : ∀ {m a a′ b φ ψ} (e : a′ ≅ᴵ a) {x : Q m a φ} {y : Q m b ψ} → Rᵒ m a b x y → Rᵒ m a′ b (tr⁻O e x) y
R-resˡ : ∀ {m j a a′ b ξ ξ′} (q : j <ᴵ a) (e : a ≅ᴵ a′) {z : Q m (repO (resO q e)) ξ} {y : Q m b ξ′} → Rᵒ m _ b z y → Rᵒ m j b (backO (resO q e) z) y
R-res⁻ˡ : ∀ {m j a a′ b ξ ξ′} (q : j <ᴵ a) (e : a′ ≅ᴵ a) {z : Q m (repO (res⁻O q e)) ξ} {y : Q m b ξ′} → Rᵒ m _ b z y → Rᵒ m j b (backO (res⁻O q e) z) y

R-trˡ e rz = rz
R-trˡ e (rs sa r) = rs sa (R-trˡ e r)
R-trˡ e (rl h) = rl (λ m → R-trˡ e (h m))
R-trˡ e (ri ej h) = ri ej (λ x y d → R-trˡ e (h x y d))
R-trˡ e (rŝ ec r h) = rŝ ec (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
R-trˡ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
R-trˡ e (rclo s r h) = rclo s (R-trˡ e r) (λ η η′ d → R-trˡ e (h η η′ d))
R-trˡ e (rwkˡ r) = rwkˡ (R-trˡ e r)
R-trˡ e (rwkʳ r) = rwkʳ (R-trˡ e r)
R-trˡ e (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-trˡ e (f ξ ξ′ d z z′ l))
R-trˡ e (rev s h) = rev s (λ e₁ e₂ → R-trˡ e (h e₁ e₂))
R-trˡ {a′ = a′} {b} e (rΩ {φ = φ} {ψ} {r = q} {r′} {h} {h′} ek s f) =
  rΩ {r = ltO (resO q e)} (≅ᴵ-trans (≅ᴵ-sym (eqO (resO q e))) ek) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ _ a′ b (trO e (h ξ (intoU (<→◃ q) (backO (resO q e) w)))) (h′ ξ′ (intoU (<→◃ r′) z′))) (sym (out-intoU (<→◃ (ltO (resO q e))) z))
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
R-tr⁻ˡ e (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-tr⁻ˡ e (f ξ ξ′ d z z′ l))
R-tr⁻ˡ e (rev s h) = rev s (λ e₁ e₂ → R-tr⁻ˡ e (h e₁ e₂))
R-tr⁻ˡ {a′ = a′} {b} e (rΩ {φ = φ} {ψ} {r = q} {r′} {h} {h′} ek s f) =
  rΩ {r = ltO (res⁻O q e)} (≅ᴵ-trans (≅ᴵ-sym (eqO (res⁻O q e))) ek) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ _ a′ b (tr⁻O e (h ξ (intoU (<→◃ q) (backO (res⁻O q e) w)))) (h′ ξ′ (intoU (<→◃ r′) z′))) (sym (out-intoU (<→◃ (ltO (res⁻O q e))) z))
                              (R-tr⁻ˡ e (f ξ ξ′ d _ z′ (intoR (<→◃ q) (R-res⁻ˡ q e (outR (<→◃ (ltO (res⁻O q e))) l))))))

R-resˡ zero      (s≅ e) l = R-tr⁻ˡ e l
R-resˡ (suc q)   (s≅ e) l = R-resˡ q e l
R-resˡ (lim n q) (l≅ h) l = R-resˡ q (h n) l

R-res⁻ˡ zero      (s≅ e) l = R-trˡ e l
R-res⁻ˡ (suc q)   (s≅ e) l = R-res⁻ˡ q e l
R-res⁻ˡ (lim n q) (l≅ h) l = R-res⁻ˡ q (h n) l

R-trʳ  : ∀ {m a b b′ φ ψ} (e : b ≅ᴵ b′) {x : Q m a φ} {y : Q m b ψ} → Rᵒ m a b x y → Rᵒ m a b′ x (trO e y)
R-tr⁻ʳ : ∀ {m a b b′ φ ψ} (e : b′ ≅ᴵ b) {x : Q m a φ} {y : Q m b ψ} → Rᵒ m a b x y → Rᵒ m a b′ x (tr⁻O e y)
R-resʳ : ∀ {m j a b b′ ξ ξ′} (q : j <ᴵ b) (e : b ≅ᴵ b′) {z : Q m a ξ} {y : Q m (repO (resO q e)) ξ′} → Rᵒ m a _ z y → Rᵒ m a j z (backO (resO q e) y)
R-res⁻ʳ : ∀ {m j a b b′ ξ ξ′} (q : j <ᴵ b) (e : b′ ≅ᴵ b) {z : Q m a ξ} {y : Q m (repO (res⁻O q e)) ξ′} → Rᵒ m a _ z y → Rᵒ m a j z (backO (res⁻O q e) y)

R-trʳ e rz = rz
R-trʳ e (rs sa r) = rs sa (R-trʳ e r)
R-trʳ e (rl h) = rl (λ m → R-trʳ e (h m))
R-trʳ e (ri ej h) = ri ej (λ x y d → R-trʳ e (h x y d))
R-trʳ e (rŝ ec r h) = rŝ ec (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rclo s r h) = rclo s (R-trʳ e r) (λ η η′ d → R-trʳ e (h η η′ d))
R-trʳ e (rwkˡ r) = rwkˡ (R-trʳ e r)
R-trʳ e (rwkʳ r) = rwkʳ (R-trʳ e r)
R-trʳ e (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-trʳ e (f ξ ξ′ d z z′ l))
R-trʳ e (rev s h) = rev s (λ e₁ e₂ → R-trʳ e (h e₁ e₂))
R-trʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s f) =
  rΩ {r = r} {r′ = ltO (resO q e)} (≅ᴵ-trans ek (eqO (resO q e))) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ _ a b′ (h ξ (intoU (<→◃ r) z)) (trO e (h′ ξ′ (intoU (<→◃ q) (backO (resO q e) w))))) (sym (out-intoU (<→◃ (ltO (resO q e))) z′))
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
R-tr⁻ʳ e (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-tr⁻ʳ e (f ξ ξ′ d z z′ l))
R-tr⁻ʳ e (rev s h) = rev s (λ e₁ e₂ → R-tr⁻ʳ e (h e₁ e₂))
R-tr⁻ʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s f) =
  rΩ {r = r} {r′ = ltO (res⁻O q e)} (≅ᴵ-trans ek (eqO (res⁻O q e))) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ _ a b′ (h ξ (intoU (<→◃ r) z)) (tr⁻O e (h′ ξ′ (intoU (<→◃ q) (backO (res⁻O q e) w))))) (sym (out-intoU (<→◃ (ltO (res⁻O q e))) z′))
                              (R-tr⁻ʳ e (f ξ ξ′ d z _ (intoR (<→◃ r) (R-res⁻ʳ q e (outR (<→◃ r) l))))))

R-resʳ zero      (s≅ e) l = R-tr⁻ʳ e l
R-resʳ (suc q)   (s≅ e) l = R-resʳ q e l
R-resʳ (lim n q) (l≅ h) l = R-resʳ q (h n) l

R-res⁻ʳ zero      (s≅ e) l = R-trʳ e l
R-res⁻ʳ (suc q)   (s≅ e) l = R-res⁻ʳ q e l
R-res⁻ʳ (lim n q) (l≅ h) l = R-res⁻ʳ q (h n) l

R-tr₂ : ∀ {m a b a′ b′ φ ψ} (e : a ≅ᴵ a′) (e′ : b ≅ᴵ b′) {x : Q m a φ} {y : Q m b ψ} → Rᵒ m a b x y → Rᵒ m a′ b′ (trO e x) (trO e′ y)
R-tr₂ e e′ r = R-trˡ e (R-trʳ e′ r)

R-tr⁻₂ : ∀ {m a b a′ b′ φ ψ} (e : a′ ≅ᴵ a) (e′ : b′ ≅ᴵ b) {x : Q m a φ} {y : Q m b ψ} → Rᵒ m a b x y → Rᵒ m a′ b′ (tr⁻O e x) (tr⁻O e′ y)
R-tr⁻₂ e e′ r = R-tr⁻ˡ e (R-tr⁻ʳ e′ r)
```

## §5 对 `ψᵒ` 封闭

```agda
R-rep : ∀ {m a b φ ψ} {X : Q m a φ} {X′ : Q m b ψ} → φ ∼ᶠ ψ → Rᵒ m a b X X′ → ∀ n → Rᵒ m a b (repᵒ X n) (repᵒ X′ n)
R-rep s r zero = rz
R-rep s r (suc zero) = r
R-rep s r (suc (suc n)) = rwk (R-⊕ s (R-rep s r (suc n)) r)

sg : ∀ {τ τ′} → τ ≅ᴵ τ′ → (Fl ⊔ fk τ) ∼ᶠ (Fl ⊔ fk τ′)
sg et = ⊔∼ (∼ᶠ-refl Fl) (fk∼ et)

R-ψs : ∀ {m a b t t′ φ ψ} (q : t <ᴵ a) (q′ : t′ <ᴵ b) → t ≅ᴵ t′ → {x : Q m a φ} {x′ : Q m b ψ} → Rᵒ m a b x x′ → Rᵒ m t t′ (ψᵒ (ts q) x) (ψᵒ (ts q′) x′)
R-ψd : ∀ {m a b n τ τ′ φ ψ} (p p′ : n <ᴸ m) → τ ≅ᴵ τ′ → {x : Q m a φ} {x′ : Q m b ψ} → Rᵒ m a b x x′ → Rᵒ n τ τ′ (ψᵒ (td p τ) x) (ψᵒ (td p′ τ′) x′)
chRS : ∀ {m a b k k′ φ ψ} (g : Tg m a) (g′ : Tg m b) → tf g ∼ᶠ tf g′ → {r : k <ᴵ a} {r′ : k′ <ᴵ b} {h : ∀ ξ → Us m k (<→◃ r) ξ → Q m a (ξ ⊔ φ)} {h′ : ∀ ξ → Us m k′ (<→◃ r′) ξ → Q m b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : Q m k ξ) (z′ : Q m k′ ξ′) → LRᵒ m a (<→◃ r) z z′ → Rᵒ m a b (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) →
       ∀ n → Rᵒ m k k′ (chS g r h n) (chS g′ r′ h′ n)
chRD : ∀ {m a b n′ k k′ φ ψ} (g : Tg m a) (g′ : Tg m b) → tf g ∼ᶠ tf g′ → (qn qn′ : n′ <ᴸ m) {ac : ∀ {L} → Ev L φ → k <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → k′ <ᴵ L} {h : ∀ ξ → Vs m qn k ξ → Q m a (ξ ⊔ φ)} {h′ : ∀ ξ → Vs m qn′ k′ ξ → Q m b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : Q n′ k ξ) (z′ : Q n′ k′ ξ′) → LVᵒ m qn z z′ → Rᵒ m a b (h ξ (intoV qn z)) (h′ ξ′ (intoV qn′ z′))) →
       ∀ n → Rᵒ n′ k k′ (chD g qn ac h n) (chD g′ qn′ ac′ h′ n)
R-ψ≡ : ∀ {m a b n k k′ τ τ′ φ ψ} (p p′ qn qn′ : n <ᴸ m) → τ ≅ᴵ τ′ → k ≅ᴵ k′ → φ ∼ᶠ ψ → {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl}
       {ac : ∀ {L} → Ev L φ → k <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → k′ <ᴵ L} {h : ∀ ξ → Vs m qn k ξ → Q m a (ξ ⊔ φ)} {h′ : ∀ ξ → Vs m qn′ k′ ξ → Q m b (ξ ⊔ ψ)} →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : Q n k ξ) (z′ : Q n k′ ξ′) → LVᵒ m qn z z′ → Rᵒ m a b (h ξ (intoV qn z)) (h′ ξ′ (intoV qn′ z′))) →
       (D : (k ≺ᴵ τ) ⊎ (τ ≺ᴵ k) ⊎ (k ≅ᴵ τ)) (D′ : (k′ ≺ᴵ τ′) ⊎ (τ′ ≺ᴵ k′) ⊎ (k′ ≅ᴵ τ′)) →
       Rᵒ n τ τ′ (ψ≡ p qn fe ac h D) (ψ≡ p′ qn′ fe′ ac′ h′ D′)

R-ψs q q′ et rz = rwk (RΩ̇ et)
R-ψs q q′ et (rs sa r) = rl (R-rep (⊔∼ (∼ᶠ-refl Fl) sa) (R-ψs q q′ et r))
R-ψs q q′ et (rl h) = rl (λ n → R-ψs q q′ et (h n))
R-ψs q q′ et (ri e h) = ri e (λ x y d → R-ψs q q′ et (h x y d))
R-ψs q q′ et (rŝ e r h) = rŝ e (R-ψs q q′ et r) (λ η ee η′ e′ d → R-ψs q q′ et (h η ee η′ e′ d))
R-ψs q q′ et (rĉ e dz dg r h) = rĉ e dz dg (R-ψs q q′ et r) (λ η ee η′ e′ d → R-ψs q q′ et (h η ee η′ e′ d))
R-ψs q q′ et (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-ψs q q′ et r)) (λ η η′ d → rwk (R-ψs q q′ et (h η η′ d))))
R-ψs q q′ et (rwkˡ r) = rwkˡ (R-ψs q q′ et r)
R-ψs q q′ et (rwkʳ r) = rwkʳ (R-ψs q q′ et r)
R-ψs q q′ et (rev s h) = rev (⊔∼ (∼ᶠ-refl Fl) s) (λ e e′ → R-ψs q q′ et (h (proj₂ e) (proj₂ e′)))
R-ψs q q′ et (rΩ↓ ek s f) = rΩ↓ ek (⊔∼ (∼ᶠ-refl Fl) s) (λ ξ ξ′ d z z′ l → rwk (R-ψs q q′ et (f ξ ξ′ d z z′ l)))
R-ψs {m} {t = t} {t′} q q′ et (rΩ {φ = φ} {ψ} {k} {k′} {r = r} {r′} {h} {h′} ek s f) with <ᴵ-dec r q | <ᴵ-dec r′ q′
... | injᵃ (via e p) | injᵃ (via e′ p′) =
  rΩ {r = p} {r′ = p′} (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans ek e′)) (⊔∼ (∼ᶠ-refl Fl) s)
     (λ ξ ξ′ d z z′ l → rwk (subst₂ (λ w w′ → Rᵒ m t t′ (ψᵒ (ts q) (h ξ (intoU (<→◃ r) (tr⁻O e w)))) (ψᵒ (ts q′) (h′ ξ′ (intoU (<→◃ r′) (tr⁻O e′ w′))))) (sym (out-intoU (<→◃ p) z)) (sym (out-intoU (<→◃ p′) z′))
                                    (R-ψs q q′ et (f ξ ξ′ d _ _ (intoR (<→◃ r) (R-tr⁻ˡ e (R-tr⁻ʳ e′ (outR (<→◃ p) l))))))))
... | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
... | injᵃ a | injᶜ c = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym ek)))))
... | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
... | injᶜ c | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c) ek))))
... | injᵇ _ | injᵇ _ = rl (λ n → rwk (R-ψs q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRS (ts q) (ts q′) (∼ᶠ-refl Fl) {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
... | injᵇ _ | injᶜ _ = rl (λ n → rwk (R-ψs q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRS (ts q) (ts q′) (∼ᶠ-refl Fl) {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
... | injᶜ _ | injᵇ _ = rl (λ n → rwk (R-ψs q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRS (ts q) (ts q′) (∼ᶠ-refl Fl) {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
... | injᶜ _ | injᶜ _ = rl (λ n → rwk (R-ψs q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRS (ts q) (ts q′) (∼ᶠ-refl Fl) {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))

R-ψd p p′ et rz = rwk (RΩ̇ et)
R-ψd p p′ et (rs sa r) = rl (R-rep (⊔∼ (sg et) sa) (R-ψd p p′ et r))
R-ψd p p′ et (rl h) = rl (λ n → R-ψd p p′ et (h n))
R-ψd p p′ et (ri e h) = ri e (λ x y d → R-ψd p p′ et (h x y d))
R-ψd p p′ et (rŝ e r h) = rŝ e (R-ψd p p′ et r) (λ η ee η′ e′ d → R-ψd p p′ et (h η ee η′ e′ d))
R-ψd p p′ et (rĉ e dz dg r h) = rĉ e dz dg (R-ψd p p′ et r) (λ η ee η′ e′ d → R-ψd p p′ et (h η ee η′ e′ d))
R-ψd p p′ et (rclo s r h) = rwk (rclo (⊔∼ (sg et) s) (rwk (R-ψd p p′ et r)) (λ η η′ d → rwk (R-ψd p p′ et (h η η′ d))))
R-ψd p p′ et (rwkˡ r) = rwkˡ (R-ψd p p′ et r)
R-ψd p p′ et (rwkʳ r) = rwkʳ (R-ψd p p′ et r)
R-ψd p p′ et (rev s h) = rev (⊔∼ (sg et) s) (λ e e′ → R-ψd p p′ et (h (proj₂ e) (proj₂ e′)))
R-ψd {τ = τ} {τ′} p p′ et (rΩ {φ = φ} {ψ} {r = r} {r′} {h} {h′} ek s f) =
  rl (λ n → rwk (R-ψd p p′ et (f ((Fl ⊔ fk τ) ⊔ φ) ((Fl ⊔ fk τ′) ⊔ ψ) (⊔∼ (sg et) s) _ _ (intoR (<→◃ r) (chRS (td p τ) (td p′ τ′) (sg et) {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
R-ψd {m} {n = n} {τ = τ} {τ′} p p′ et (rΩ↓ {φ = φ} {ψ} {n = n″} {k} {k′} {fe = fe} {fe′} {q = qn} {q′ = qn′} {ac} {ac′} {h} {h′} ek s f) with tri n″ n
... | tlt t = rΩ↓ ek (⊔∼ (sg et) s)
       (λ ξ ξ′ d z z′ l → rwk (subst₂ (λ w w′ → Rᵒ n τ τ′ (ψᵒ (td p τ) (h ξ (intoV qn w))) (ψᵒ (td p′ τ′) (h′ ξ′ (intoV qn′ w′)))) (sym (out-intoV t z)) (sym (out-intoV t z′))
                               (R-ψd p p′ et (f ξ ξ′ d _ _ (intoRV qn (outRV t l))))))
... | tgt _ = rl (λ n₁ → rwk (R-ψd p p′ et (f ((Fl ⊔ fk τ) ⊔ φ) ((Fl ⊔ fk τ′) ⊔ ψ) (⊔∼ (sg et) s) _ _ (intoRV qn (chRD (td p τ) (td p′ τ′) (sg et) qn qn′ {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek s f n₁)))))
... | teq refl = rev (⊔∼ (sg et) s) (λ e e′ → R-ψ≡ p p′ qn qn′ et ek s {fe = fe} {fe′ = fe′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} f _ _)

R-ψ≡ {m} {n = n} {τ = τ} {τ′} p p′ qn qn′ et ek s {h = h} {h′ = h′} f (inj₁ (via e u)) (inj₁ (via e′ u′)) =
  rΩ {r = u} {r′ = u′} (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans ek e′)) (⊔∼ (sg et) s)
     (λ ξ ξ′ d z z′ l → rwk (subst₂ (λ w w′ → Rᵒ n τ τ′ (ψᵒ (td p τ) (h ξ (intoV qn (tr⁻O e w)))) (ψᵒ (td p′ τ′) (h′ ξ′ (intoV qn′ (tr⁻O e′ w′))))) (sym (out-intoU (<→◃ u) z)) (sym (out-intoU (<→◃ u′) z′))
                             (R-ψd p p′ et (f ξ ξ′ d _ _ (intoRV qn (R-tr⁻ˡ e (R-tr⁻ʳ e′ (outR (<→◃ u) l))))))))
R-ψ≡ p p′ qn qn′ et ek s f (inj₁ a) (inj₂ (inj₁ b)) = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
R-ψ≡ p p′ qn qn′ et ek s f (inj₁ a) (inj₂ (inj₂ c)) = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym ek)))))
R-ψ≡ p p′ qn qn′ et ek s f (inj₂ (inj₁ b)) (inj₁ a) = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
R-ψ≡ p p′ qn qn′ et ek s f (inj₂ (inj₂ c)) (inj₁ a) = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c) ek))))
R-ψ≡ {τ = τ} {τ′} {φ = φ} {ψ} p p′ qn qn′ et ek s {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} f (inj₂ _) (inj₂ _) =
  rl (λ n₁ → rwk (R-ψd p p′ et (f ((Fl ⊔ fk τ) ⊔ φ) ((Fl ⊔ fk τ′) ⊔ ψ) (⊔∼ (sg et) s) _ _ (intoRV qn (chRD (td p τ) (td p′ τ′) (sg et) qn qn′ {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek s f n₁)))))

chRS g g′ sf ek s f zero = rwk (RΩ̇ ek)
chRS g g′ sf {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f (suc n) =
  rwk (R-ψs r r′ ek (f _ _ (⊔∼ sf s) _ _ (intoR (<→◃ r) (chRS g g′ sf {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n))))

chRD g g′ sf qn qn′ ek s f zero = rwk (RΩ̇ ek)
chRD {k = k} {k′} g g′ sf qn qn′ {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek s f (suc n) =
  rwk (R-ψd qn qn′ ek (f _ _ (⊔∼ sf s) _ _ (intoRV qn (chRD g g′ sf qn qn′ {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek s f n))))
```

## §6 求值

```agda
chRE : ∀ {m a b k k′ φ ψ} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r : k <ᴵ a} {r′ : k′ <ᴵ b}
       {h : ∀ ξ → Us m k (<→◃ r) ξ → Q m a (ξ ⊔ φ)} {h′ : ∀ ξ → Us m k′ (<→◃ r′) ξ → Q m b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : Q m k ξ) (z′ : Q m k′ ξ′) → LRᵒ m a (<→◃ r) z z′ → Rᵒ m a b (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) →
       ∀ n → Rᵒ m k k′ (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ (ts r) (h φ (intoU (<→◃ r) z)))) n) (chainᵒ fe′ (λ z → owk (λ v → fe′ v , (v , v)) (ψᵒ (ts r′) (h′ ψ (intoU (<→◃ r′) z)))) n)
chRE ek s f zero = rwk (RΩ̇ ek)
chRE {φ = φ} {ψ = ψ} {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f (suc n) =
  rwk (R-ψs r r′ ek (f φ ψ s _ _ (intoR (<→◃ r) (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n))))

chRV : ∀ {m a b n′ k k′ φ ψ} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {qn qn′ : n′ <ᴸ m} {ac : ∀ {L} → Ev L φ → k <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → k′ <ᴵ L}
       {h : ∀ ξ → Vs m qn k ξ → Q m a (ξ ⊔ φ)} {h′ : ∀ ξ → Vs m qn′ k′ ξ → Q m b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : Q n′ k ξ) (z′ : Q n′ k′ ξ′) → LVᵒ m qn z z′ → Rᵒ m a b (h ξ (intoV qn z)) (h′ ξ′ (intoV qn′ z′))) →
       ∀ n → Rᵒ n′ k k′ (chainᵒ fe (λ z → owk (λ v → ak₂ (fe v) (ac v) , (v , v)) (ψᵒ (td qn k) (h φ (intoV qn z)))) n) (chainᵒ fe′ (λ z → owk (λ v → ak₂ (fe′ v) (ac′ v) , (v , v)) (ψᵒ (td qn′ k′) (h′ ψ (intoV qn′ z)))) n)
chRV ek s f zero = rwk (RΩ̇ ek)
chRV {φ = φ} {ψ = ψ} {fe = fe} {fe′ = fe′} {qn = qn} {qn′ = qn′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek s f (suc n) =
  rwk (R-ψd qn qn′ ek (f φ ψ s _ _ (intoRV qn (chRV {fe = fe} {fe′ = fe′} {qn = qn} {qn′ = qn′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek s f n))))

r∅ : ∅ᴿ ≈ᴿ ∅ᴿ
r∅ ev p ev′ p′ ei = Ωˢ-≅ ei

R→≈ : ∀ {m a b φ ψ} {x : Q m a φ} {x′ : Q m b ψ} → Rᵒ m a b x x′ → ψ̄ x ≈ᴿ ψ̄ x′
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
R→≈ (rΩ↓ {φ = φ} {ψ} {fe = fe} {fe′} {q = qn} {q′ = qn′} {ac} {ac′} {h} {h′} ek s f) =
  limR (λ n → wkR _ _ (R→≈ (f φ ψ s _ _ (intoRV qn (chRV {fe = fe} {fe′ = fe′} {qn = qn} {qn′ = qn′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek s f n)))))
R→≈ (rev s h) ev p ev′ p′ ei = R→≈ (h ev ev′) ev p ev′ p′ ei

-- 目标 ψ₀(Ω_{Ω·(m+1)+α}) 自相关: 树的计值在任意两个环境下互模拟.
RTQ : ∀ m {a b} → a ≅ᴵ b → TQ m a ≈ᴿ TQ m b
RTQ m e = R→≈ (RΩ̇ e)
```
