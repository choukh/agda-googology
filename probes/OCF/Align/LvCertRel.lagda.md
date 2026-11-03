# 新树上的互模拟: 世界对世界, 比较跨世界一致 (底座)

> 底座, 不含记号. 结论写在 [LvCert](LvCert.lagda.md). 由 [UniformNF5Base](UniformNF5Base.lagda.md) §1–§6 改写到 [UniformLvTree](UniformLvTree.lagda.md) 的树 `O`. 差别:
>
> 1. **`rev`: `oev` 的两边对任意两个世界相关.** 这是 `R-ψ` 的 `oΩ` 行要的: 两边的比较结果在不同世界上算出, 由 `irr`/`clashL`/`clashE` 排除交叉. `irr` 对一切 `LI` 成立, 不要 `WF`.
> 2. **高度掩码 `S`.** `R₊` 只在 $S\,h$ 的高度上对齐地板, 闭包行要 $S\,h$. 取 $S$ 平凡就是全互模拟; 取 $S\,h = (h\ne1)$ 时, 地板 `tk 1 τ` 不同的两棵树仍可相关, 只要里面没有高度 1 的闭包. [LvCertNeg](LvCertNeg.lagda.md) 用它.
> 3. **`R-ι` 是双侧的**, 地板 `dnF` 对齐: 旧的单侧透明不再成立, 因为 `ι (db η)` 真的改了闭包的地板. 这正是 `LvCertNeg` 的否定结果的来源.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvCertRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; zero; suc; lim; <→◃; Simᴵ; <ᴵ-dec; z≅; s≅; l≅; ≅ᴵ-refl; ≅ᴵ-sym; ≅ᴵ-trans; ≺ᴵ-irrefl; ≺ᴵ-trans; ≺ᴵ-respʳ; ≺ᴵ-respˡ; iter-R; clash₁; clash₂; self)
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; tr⁻ˢ)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; _≅ˢ_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; R→≅ˢ; Ωˢ-≅; toZ-≅; tf; tr⁻ˢ-≅; ≅-tr⁻ˢ; addˢ-≅; kd-≅)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; bound; Bd; Fc; evF; iF; FB; liftEv; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl; bound-≅; Top; top₀; accT; accM)
open import OCF.Align.UniformLvBase
open import OCF.Align.UniformLvTree
```

## §1 不反射: 字面前驱不能回到自身

```agda
<ᴸ-trans : ∀ {a b c} → a <ᴸ b → b <ᴸ c → a <ᴸ c
<ᴸ-trans x zero      = suc x
<ᴸ-trans x (suc r)   = suc (<ᴸ-trans x r)
<ᴸ-trans x (lim n r) = lim n (<ᴸ-trans x r)
<ᴸ-trans x (fst r)   = fst (<ᴸ-trans x r)
<ᴸ-trans x (bra η r) = bra η (<ᴸ-trans x r)

-- 只看路径形状, 不带可容许性的转移
_⊑⁻_ : LI → LI → Set
a ⊑⁻ b = ∀ {k} (r : k <ᴸ a) → Σ LI λ rep → (k ≈ rep) × (rep <ᴸ b)

mv⁻ : ∀ {a b} → a ≈ b → a ⊑⁻ b
mv⁻ e r with ≈-move e r
... | viaᴸ d p _ = _ , d , p

irr : ∀ a {r} → a ⊑⁻ r → r <ᴸ a → ⊥
irr (suc b) H zero with H zero
... | _ , d , p = irr b (mv⁻ d) p
irr (suc b) H (suc s) with H zero
... | _ , d , p = irr b (mv⁻ d) (<ᴸ-trans p s)
irr (lim f) H (lim n s) = irr (f n) (λ x → H (lim n x)) s
irr (lcl h g) H (fst s) = irr (g one) (λ x → H (fst x)) s
irr (lcl h g) H (bra η s) = irr (g η) (λ x → H (bra η x)) s

clashL : ∀ {k k′ t t′ rep rep′} → k ≈ k′ → t ≈ t′ → k ≈ rep → rep <ᴸ t → t′ ≈ rep′ → rep′ <ᴸ k′ → ⊥
clashL {t = t} ek et d s d′ s′ with mv⁻ (≈-trans (≈-sym ek) d) s′
... | _ , d″ , p = irr t (mv⁻ (≈-trans et (≈-trans d′ d″))) (<ᴸ-trans p s)

clashE : ∀ {k k′ t t′ rep} → k ≈ k′ → t ≈ t′ → k ≈ rep → rep <ᴸ t → k′ ≈ t′ → ⊥
clashE {t = t} ek et d s c = irr t (mv⁻ (≈-trans et (≈-trans (≈-sym c) (≈-trans (≈-sym ek) d)))) s
```

## §2 值层的相关

`≈ᵗ`: 两次计值在任意两个世界上 $\cong$.

```agda
infix 4 _≈ᵗ_
_≈ᵗ_ : ∀ {φ ψ} → Runᵗ φ → Runᵗ ψ → Set
_≈ᵗ_ {φ} {ψ} R R′ = ∀ {i i′ w w′} (ok : Wok w) (ev : Evt w φ) (p : i <ᴵ w 0) (ok′ : Wok w′) (ev′ : Evt w′ ψ) (p′ : i′ <ᴵ w′ 0) → i ≅ᴵ i′ → R ok ev p ≅ˢ R′ ok′ ev′ p′

limT : ∀ {φ ψ} {F : ℕ → Runᵗ φ} {G : ℕ → Runᵗ ψ} → (∀ n → F n ≈ᵗ G n) → limᵗ F ≈ᵗ limᵗ G
limT h ok ev p ok′ ev′ p′ ei = l≅ (λ n → h n ok ev p ok′ ev′ p′ ei)

sucT : ∀ {φ ψ} {R : Runᵗ φ} {R′ : Runᵗ ψ} → R ≈ᵗ R′ → sucᵗ R ≈ᵗ sucᵗ R′
sucT h ok ev p ok′ ev′ p′ ei = l≅ (iter-R _≅ˢ_ (λ e′ → addˢ-≅ ei (h ok ev p ok′ ev′ p′ ei) e′) z≅)

limᵢT : ∀ {φ ψ j j′} {ac : ∀ {w} → Evt w φ → j <ᴵ w 0} {ac′ : ∀ {w} → Evt w ψ → j′ <ᴵ w 0}
        {H : Ordˢ j → Runᵗ φ} {H′ : Ordˢ j′ → Runᵗ ψ} →
        j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → H x ≈ᵗ H′ y) → limᵢᵗ ac H ≈ᵗ limᵢᵗ ac′ H′
limᵢT {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h ok ev p ok′ ev′ p′ ei with <ᴵ-dec (ac ev) p | <ᴵ-dec (ac′ ev′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → H (tr⁻ˢ e₁ u) ok ev p ≅ˢ H′ (tr⁻ˢ e₂ v) ok′ ev′ p′)
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (h _ _ (tr⁻ˢ-≅ e₁ (≅-tr⁻ˢ e₂ (R→≅ˢ (<→◃ r₁) d))) ok ev p ok′ ev′ p′ ei)
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ok ev (ac ev) ok′ ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ok ev p ok′ ev′ p′ ei)
... | injᵇ _ | injᶜ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ok ev (ac ev) ok′ ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ok ev p ok′ ev′ p′ ei)
... | injᶜ _ | injᵇ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ok ev (ac ev) ok′ ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ok ev p ok′ ev′ p′ ei)
... | injᶜ _ | injᶜ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ok ev (ac ev) ok′ ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ok ev p ok′ ev′ p′ ei)

ĉT : ∀ {φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
     {O₀ : Runᵗ φ} {O₁ : (η : Ordᴵ) → c ⊑ᴵ η → Runᵗ φ} {O₀′ : Runᵗ ψ} {O₁′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Runᵗ ψ} →
     c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
     O₀ ≈ᵗ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → O₁ η e ≈ᵗ O₁′ η′ e′) → ĉᵗ c t₀ g O₀ O₁ ≈ᵗ ĉᵗ c′ t₀′ g′ O₀′ O₁′
ĉT ec dt dg h₀ h ok ev p ok′ ev′ p′ ei = ĉ≅ ec dt dg (h₀ ok ev p ok′ ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ok ev p ok′ ev′ p′ ei)

ŝT : ∀ {φ ψ c c′} {T₀′ : Runᵗ φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Runᵗ φ} {T₁ : Runᵗ ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Runᵗ ψ} →
     c ≅ᴵ c′ → T₀′ ≈ᵗ T₁ → (∀ η e η′ e′ → η ≅ᴵ η′ → G η e ≈ᵗ G′ η′ e′) → ŝᵗ c T₀′ G ≈ᵗ ŝᵗ c′ T₁ G′
ŝT ec h₀ h ok ev p ok′ ev′ p′ ei = ŝ≅ (kd-≅ ei) ec (h₀ ok ev p ok′ ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ok ev p ok′ ev′ p′ ei)

wkT : ∀ {φ φ′ ψ ψ′} {R : Runᵗ φ} {R′ : Runᵗ φ′} (le : ∀ {w} → Evt w ψ → Evt w φ) (le′ : ∀ {w} → Evt w ψ′ → Evt w φ′) →
      R ≈ᵗ R′ → wkᵗ {π = φ} {ρ = ψ} le R ≈ᵗ wkᵗ {π = φ′} {ρ = ψ′} le′ R′
wkT le le′ h ok ev p ok′ ev′ p′ ei = h ok (le ev) p ok′ (le′ ev′) p′ ei
```

**地板的语义对齐.** `_∼ᶠ_` 是结构的, 单位 `fz` 不能抵消; 但嵌入 `ι` 按栈长度加 `tz`, 两边栈长不同时形状就不同. `_∼ᶜ_`: 并入任何已有的 `Top` 之后界 $\cong$. 它有传递与单位律, `_∼ᶠ_` 是它的特例.

```agda
infix 4 _∼ᶜ_
_∼ᶜ_ : Flr → Flr → Set
a ∼ᶜ b = ∀ {i i′ ℓ ℓ′ φ₁ φ₁′} (t : Top i ℓ φ₁) (t′ : Top i′ ℓ′ φ₁′) (ev : Ev ℓ a) (ev′ : Ev ℓ′ b) → Bd t ≅ᴵ Bd t′ → Bd (accT t a ev) ≅ᴵ Bd (accT t′ b ev′)

ᶠ→ᶜ : ∀ {a b} → a ∼ᶠ b → a ∼ᶜ b
ᶠ→ᶜ s t t′ ev ev′ e = accM t t′ s ev ev′ e

⊔∼ᶜ : ∀ {a a′ b b′} → a ∼ᶜ a′ → b ∼ᶜ b′ → (a ⊔ b) ∼ᶜ (a′ ⊔ b′)
⊔∼ᶜ x y t t′ (u , v) (u′ , v′) e = y (accT t _ u) (accT t′ _ u′) v v′ (x t t′ u u′ e)

⊔zˡ : ∀ {a b} → a ∼ᶜ b → (a ⊔ fz) ∼ᶜ b
⊔zˡ x t t′ (u , _) ev′ e = x t t′ u ev′ e

⊔zʳ : ∀ {a b} → a ∼ᶜ b → a ∼ᶜ (b ⊔ fz)
⊔zʳ x t t′ ev (u′ , _) e = x t t′ ev u′ e

bound-≅ᶜ : ∀ {i i′ ℓ ℓ′ φ φ′} → φ ∼ᶜ φ′ → (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ φ′) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ →
           Bd (bound φ ev p) ≅ᴵ Bd (bound φ′ ev′ p′)
bound-≅ᶜ s ev p ev′ p′ ei = s (top₀ p) (top₀ p′) ev ev′ (s≅ ei)
```

**闭包.** 只要第 $h$ 层的地板对齐. 这是整个世界族设计里唯一读地板的地方.

```agda
cloT : ∀ {φ φ′} h {t : Runᵗ φ} {g : (η : Ordᴵ) → Runᵗ (φ ∪ tk h η)} {t′ : Runᵗ φ′} {g′ : (η : Ordᴵ) → Runᵗ (φ′ ∪ tk h η)} →
       prj h φ ∼ᶜ prj h φ′ → t ≈ᵗ t′ → (∀ η η′ → η ≅ᴵ η′ → g η ≈ᵗ g′ η′) → cloᵗ h t g ≈ᵗ cloᵗ h t′ g′
cloT {φ} {φ′} zero s ht hg {i} {i′} {w} {w′} ok ev p ok′ ev′ p′ ei =
  ŝ≅ (kd-≅ ei) (bound-≅ᶜ (⊔∼ᶜ s (ᶠ→ᶜ (fk∼ z≅))) _ p _ p′ ei) (ht ok ev p ok′ ev′ p′ ei)
     (λ η e η′ e′ eη → hg η η′ eη _ _ _ _ _ _ ei)
cloT {φ} {φ′} (suc h) s ht hg {i} {i′} {w} {w′} ok ev p ok′ ev′ p′ ei =
  ŝ≅ (kd-≅ ei) (bound-≅ᶜ (⊔∼ᶜ s (ᶠ→ᶜ (fk∼ z≅))) _ (ok (suc h)) _ (ok′ (suc h)) z≅) (ht ok ev p ok′ ev′ p′ ei)
     (λ η e η′ e′ eη → hg η η′ eη _ _ _ _ _ _ ei)
```

## §3 互模拟

`Rel S`: 只在 $S\,h$ 的高度上对齐地板. `Hg L`: $L$ 里的闭包高度都在 $S$ 内; `RΩ̇` 要它.

```agda
out-intoU : ∀ {c k} (r : k <ᴸ c) {ξ} (z : O k ξ) → outU r (intoU r z) ≡ z
out-intoU zero      z = refl
out-intoU (suc r)   z = out-intoU r z
out-intoU (lim n r) z = out-intoU r z
out-intoU (fst r)   z = out-intoU r z
out-intoU (bra η r) z = out-intoU r z

cv-into : ∀ {a b} (d : Dn a b) {k} (r : k <ᴸ a) {ξ} (z : O k ξ) → cvU d r (intoU (pl d r) z) ≡ intoU r z
cv-into ds     r z = refl
cv-into (dl n) r z = refl
cv-into df     r z = refl
cv-into (db η) r z = refl

sel∼ : ∀ {K K′} → K ≅ᴵ K′ → ∀ a b → sel a b (fk K) ∼ᶠ sel a b (fk K′)
sel∼ e zero    zero    = fk∼ e
sel∼ e zero    (suc b) = fz∼
sel∼ e (suc a) zero    = fz∼
sel∼ e (suc a) (suc b) = sel∼ e a b

selb∼ : ∀ {K K′} → K ≅ᴵ K′ → ∀ a b → sel a b (fb K) ∼ᶠ sel a b (fb K′)
selb∼ e zero    zero    = fb∼ e
selb∼ e zero    (suc b) = fz∼
selb∼ e (suc a) zero    = fz∼
selb∼ e (suc a) (suc b) = selb∼ e a b

module Rel (S : ℕ → Set) where
  infix 4 _∼ₛ_
  _∼ₛ_ : Fᵗ → Fᵗ → Set
  φ ∼ₛ ψ = ∀ h → S h → prj h φ ∼ᶜ prj h ψ

  frefl : ∀ φ → φ ∼ₛ φ
  frefl φ h _ = ᶠ→ᶜ (∼ᶠ-refl (prj h φ))

  ∪∼ : ∀ {a a′ b b′} → a ∼ₛ a′ → b ∼ₛ b′ → (a ∪ b) ∼ₛ (a′ ∪ b′)
  ∪∼ x y h s = ⊔∼ᶜ (x h s) (y h s)

  tk∼ : ∀ {h K K′} → K ≅ᴵ K′ → tk h K ∼ₛ tk h K′
  tk∼ {h = h₀} e h _ = ᶠ→ᶜ (sel∼ e h h₀)

  flo∼ : ∀ {k k′} → k ≅ᴵ k′ → floᵗ k ∼ₛ floᵗ k′
  flo∼ z≅ h _ = ᶠ→ᶜ fz∼
  flo∼ (s≅ e) h _ = ᶠ→ᶜ (sel∼ e h 0)
  flo∼ (l≅ f) h _ = ᶠ→ᶜ (selb∼ (l≅ f) h 0)

  -- 嵌入的地板
  Triv : ∀ {a b} → Dn a b → Set
  Triv d = ∀ h → S h → prj h (dnF d) ∼ᶜ fz

  Hg : LI → Set
  Hg zero      = ⊤
  Hg base      = S 0
  Hg (suc k)   = Hg k
  Hg (lim f)   = ∀ n → Hg (f n)
  Hg (lcl h g) = S h × (∀ η → Hg (g η))

  Hg-≈ : ∀ {a b} → a ≈ b → Hg a → Hg b
  Hg-≈ z≈ x = x
  Hg-≈ b≈ x = x
  Hg-≈ (s≈ e) x = Hg-≈ e x
  Hg-≈ (l≈ h) x n = Hg-≈ (h n) (x n)
  Hg-≈ (o≈ refl h) (s₀ , x) = s₀ , λ η → Hg-≈ (h η η (≅ᴵ-refl η)) (x η)

  Hg-at : ∀ {k c} → k <ᴸ c → Hg c → Hg k
  Hg-at zero x = x
  Hg-at (suc r) x = Hg-at r x
  Hg-at (lim n r) x = Hg-at r (x n)
  Hg-at (fst r) (_ , x) = Hg-at r (x one)
  Hg-at (bra η r) (_ , x) = Hg-at r (x η)

  module _ (a b : LI) (LR : ∀ {k} → k <ᴸ a → ∀ {k′ ξ ξ′} → O k ξ → O k′ ξ′ → Set) where
    data R₊ : ∀ {φ ψ} → O a φ → O b ψ → Set where
      rz : ∀ {φ ψ} → R₊ {φ} {ψ} o0 o0
      rs : ∀ {φ ψ} {p : O a φ} {p′ : O b ψ} → φ ∼ₛ ψ → R₊ p p′ → R₊ (os p) (os p′)
      rl : ∀ {φ ψ} {F : ℕ → O a φ} {F′ : ℕ → O b ψ} → (∀ n → R₊ (F n) (F′ n)) → R₊ (ol F) (ol F′)
      ri : ∀ {φ ψ j j′} {ac : ∀ {w} → Evt w φ → j <ᴵ w 0} {ac′ : ∀ {w} → Evt w ψ → j′ <ᴵ w 0} {f : Ordˢ j → O a φ} {f′ : Ordˢ j′ → O b ψ} →
           j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → R₊ (f x) (f′ y)) → R₊ (oi ac f) (oi ac′ f′)
      rŝ : ∀ {φ ψ c₁ c₂} {t : O a φ} {t′ : O b ψ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → O a φ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O b ψ} →
           c₁ ≅ᴵ c₂ → R₊ t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (g η e) (g′ η′ e′)) → R₊ (oŝ c₁ t g) (oŝ c₂ t′ g′)
      rĉ : ∀ {φ ψ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
           {o₀ : O a φ} {o₀′ : O b ψ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → O a φ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → O b ψ} →
           c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → R₊ o₀ o₀′ →
           (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (o η e) (o′ η′ e′)) → R₊ (oĉ c₁ z zg o₀ o) (oĉ c₂ z′ zg′ o₀′ o′)
      rcl : ∀ {φ ψ h} {t : O a φ} {t′ : O b ψ} {g : (η : Ordᴵ) → O a (φ ∪ tk h η)} {g′ : (η : Ordᴵ) → O b (ψ ∪ tk h η)} →
           S h → φ ∼ₛ ψ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (ocl h t g) (ocl h t′ g′)
      rwkˡ : ∀ {φ ψ φ′} {le : ∀ {w} → Evt w φ′ → Evt w φ} {x : O a φ} {x′ : O b ψ} → R₊ x x′ → R₊ (owk le x) x′
      rwkʳ : ∀ {φ ψ ψ′} {le′ : ∀ {w} → Evt w ψ′ → Evt w ψ} {x : O a φ} {x′ : O b ψ} → R₊ x x′ → R₊ x (owk le′ x′)
      rΩ : ∀ {φ ψ k k′} {fe : ∀ {w} → Evt w φ → Evt w Fl₀} {fe′ : ∀ {w} → Evt w ψ → Evt w Fl₀} {r : k <ᴸ a} {r′ : k′ <ᴸ b}
           {ac : ∀ {w} → Evt w φ → Adm w r} {ac′ : ∀ {w} → Evt w ψ → Adm w r′}
           {h : ∀ ξ → Us a r ξ → O a (ξ ∪ φ)} {h′ : ∀ ξ → Us b r′ ξ → O b (ξ ∪ ψ)} → k ≈ k′ → Hg k → φ ∼ₛ ψ →
           (∀ ξ ξ′ → ξ ∼ₛ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → LR r z z′ → R₊ (h ξ (intoU r z)) (h′ ξ′ (intoU r′ z′))) → R₊ (oΩ fe r ac h) (oΩ fe′ r′ ac′ h′)
      rev : ∀ {φ ψ} {f : ∀ {w} → Wok w → Evt w φ → O a φ} {f′ : ∀ {w} → Wok w → Evt w ψ → O b ψ} →
           (∀ {w w′} (ok : Wok w) (e : Evt w φ) (ok′ : Wok w′) (e′ : Evt w′ ψ) → R₊ (f ok e) (f′ ok′ e′)) → R₊ (oev f) (oev f′)

  Rᵒ : ∀ a b {φ ψ} → O a φ → O b ψ → Set
  LRᵒ : ∀ a {k} → k <ᴸ a → ∀ {k′ ξ ξ′} → O k ξ → O k′ ξ′ → Set
  Rᵒ a b x y = R₊ a b (LRᵒ a) x y
  LRᵒ (suc k)   zero      {k′} x y = Rᵒ k k′ x y
  LRᵒ (suc c)   (suc r)   x y = LRᵒ c r x y
  LRᵒ (lim f)   (lim n r) x y = LRᵒ (f n) r x y
  LRᵒ (lcl h g) (fst r)   x y = LRᵒ (g one) r x y
  LRᵒ (lcl h g) (bra η r) x y = LRᵒ (g η) r x y

  outR : ∀ {c k} (r : k <ᴸ c) {k′ ξ ξ′} {z : O k ξ} {z′ : O k′ ξ′} → LRᵒ c r z z′ → Rᵒ k k′ z z′
  outR zero      l = l
  outR (suc r)   l = outR r l
  outR (lim n r) l = outR r l
  outR (fst r)   l = outR r l
  outR (bra η r) l = outR r l

  intoR : ∀ {c k} (r : k <ᴸ c) {k′ ξ ξ′} {z : O k ξ} {z′ : O k′ ξ′} → Rᵒ k k′ z z′ → LRᵒ c r z z′
  intoR zero      l = l
  intoR (suc r)   l = intoR r l
  intoR (lim n r) l = intoR r l
  intoR (fst r)   l = intoR r l
  intoR (bra η r) l = intoR r l

  rwk : ∀ {a b φ ψ φ′ ψ′} {le : ∀ {w} → Evt w φ′ → Evt w φ} {le′ : ∀ {w} → Evt w ψ′ → Evt w ψ} {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ a b (owk le x) (owk le′ x′)
  rwk r = rwkˡ (rwkʳ r)
```

## §4 封闭性: 加法与嵌入

`R-ι` 双侧, 地板对齐. `R-ιˡ`, `R-ιʳ` 单侧, 只在 `dnF d` 对 $S$ 平凡时成立.

```agda
  R-⊕ : ∀ {a b φ φ′ ψ ψ′} {W : O a φ} {W′ : O b φ′} {t : O a ψ} {t′ : O b ψ′} → φ ∼ₛ φ′ → Rᵒ a b W W′ → Rᵒ a b t t′ → Rᵒ a b (W ⊕ t) (W′ ⊕ t′)
  R-⊕ s rW rz = rwk rW
  R-⊕ s rW (rs sa r) = rs (∪∼ s sa) (R-⊕ s rW r)
  R-⊕ s rW (rl h) = rl (λ n → R-⊕ s rW (h n))
  R-⊕ s rW (ri e h) = ri e (λ x y d → R-⊕ s rW (h x y d))
  R-⊕ s rW (rŝ e r h) = rŝ e (R-⊕ s rW r) (λ η ee η′ e′ d → R-⊕ s rW (h η ee η′ e′ d))
  R-⊕ s rW (rĉ e dz dg r h) = rĉ e dz dg (R-⊕ s rW r) (λ η ee η′ e′ d → R-⊕ s rW (h η ee η′ e′ d))
  R-⊕ s rW (rcl sh sψ r h) = rcl sh (∪∼ s sψ) (R-⊕ s rW r) (λ η η′ d → rwk (R-⊕ s rW (h η η′ d)))
  R-⊕ s rW (rwkˡ r) = rwkˡ (R-⊕ s rW r)
  R-⊕ s rW (rwkʳ r) = rwkʳ (R-⊕ s rW r)
  R-⊕ s rW (rΩ ek hg sψ f) = rΩ ek hg (∪∼ s sψ) (λ ξ ξ′ d z z′ l → rwk (R-⊕ s rW (f ξ ξ′ d z z′ l)))
  R-⊕ s rW (rev h) = rev (λ ok e ok′ e′ → R-⊕ s rW (h ok (proj₂ e) ok′ (proj₂ e′)))

  cvL : ∀ {a b} (d : Dn a b) {k} (r : k <ᴸ a) {k′ ξ ξ′} {z : O k ξ} {z′ : O k′ ξ′} → LRᵒ b (pl d r) z z′ → LRᵒ a r z z′
  cvL ds     r l = l
  cvL (dl n) r l = l
  cvL df     r l = l
  cvL (db η) r l = l

  R-ι : ∀ {a b c e φ ψ} (d : Dn a c) (d′ : Dn b e) → dnF d ∼ₛ dnF d′ → {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ c e (ι d x) (ι d′ x′)
  R-ι d d′ s₀ rz = rz
  R-ι d d′ s₀ (rs sa r) = rs (∪∼ sa s₀) (R-ι d d′ s₀ r)
  R-ι d d′ s₀ (rl h) = rl (λ n → R-ι d d′ s₀ (h n))
  R-ι d d′ s₀ (ri e h) = ri e (λ x y dd → R-ι d d′ s₀ (h x y dd))
  R-ι d d′ s₀ (rŝ e r h) = rŝ e (R-ι d d′ s₀ r) (λ η ee η′ e′ dd → R-ι d d′ s₀ (h η ee η′ e′ dd))
  R-ι d d′ s₀ (rĉ e dz dg r h) = rĉ e dz dg (R-ι d d′ s₀ r) (λ η ee η′ e′ dd → R-ι d d′ s₀ (h η ee η′ e′ dd))
  R-ι d d′ s₀ (rcl sh s r h) = rcl sh (∪∼ s s₀) (R-ι d d′ s₀ r) (λ η η′ dd → rwk (R-ι d d′ s₀ (h η η′ dd)))
  R-ι d d′ s₀ (rwkˡ r) = rwkˡ (R-ι d d′ s₀ r)
  R-ι d d′ s₀ (rwkʳ r) = rwkʳ (R-ι d d′ s₀ r)
  R-ι {c = c} {e = e} d d′ s₀ (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek hg s f) =
    rΩ {r = pl d r} {r′ = pl d′ r′} ek hg (∪∼ s s₀)
       (λ ξ ξ′ dd z z′ l → rwk (subst₂ (λ u v → Rᵒ c e (ι d (h ξ u)) (ι d′ (h′ ξ′ v))) (sym (cv-into d r z)) (sym (cv-into d′ r′ z′))
                                  (R-ι d d′ s₀ (f ξ ξ′ dd z z′ (cvL d r l)))))
  R-ι d d′ s₀ (rev h) = rev (λ ok e ok′ e′ → R-ι d d′ s₀ (h ok (proj₁ e) ok′ (proj₁ e′)))

  ∪zˡ : ∀ {a b x} → (∀ h → S h → prj h x ∼ᶜ fz) → a ∼ₛ b → (a ∪ x) ∼ₛ b
  ∪zˡ t s h sh = λ T T′ ev ev′ e → t h sh (accT T _ (proj₁ ev)) (accT T′ _ ev′) (proj₂ ev) tt (s h sh T T′ (proj₁ ev) ev′ e)

  ∪zʳ : ∀ {a b x} → (∀ h → S h → prj h x ∼ᶜ fz) → a ∼ₛ b → a ∼ₛ (b ∪ x)
  ∪zʳ t s h sh = λ T T′ ev ev′ e → ≅ᴵ-sym (t h sh (accT T′ _ (proj₁ ev′)) (accT T _ ev) (proj₂ ev′) tt (≅ᴵ-sym (s h sh T T′ ev (proj₁ ev′) e)))

  R-ιˡ : ∀ {a b c φ ψ} (d : Dn a c) → Triv d → {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ c b (ι d x) x′
  R-ιˡ d t rz = rz
  R-ιˡ d t (rs sa r) = rs (∪zˡ t sa) (R-ιˡ d t r)
  R-ιˡ d t (rl h) = rl (λ n → R-ιˡ d t (h n))
  R-ιˡ d t (ri e h) = ri e (λ x y dd → R-ιˡ d t (h x y dd))
  R-ιˡ d t (rŝ e r h) = rŝ e (R-ιˡ d t r) (λ η ee η′ e′ dd → R-ιˡ d t (h η ee η′ e′ dd))
  R-ιˡ d t (rĉ e dz dg r h) = rĉ e dz dg (R-ιˡ d t r) (λ η ee η′ e′ dd → R-ιˡ d t (h η ee η′ e′ dd))
  R-ιˡ d t (rcl sh s r h) = rcl sh (∪zˡ t s) (R-ιˡ d t r) (λ η η′ dd → rwkˡ (R-ιˡ d t (h η η′ dd)))
  R-ιˡ d t (rwkˡ r) = rwkˡ (R-ιˡ d t r)
  R-ιˡ d t (rwkʳ r) = rwkʳ (R-ιˡ d t r)
  R-ιˡ {b = b} {c = c} d t (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek hg s f) =
    rΩ {r = pl d r} {r′ = r′} ek hg (∪zˡ t s)
       (λ ξ ξ′ dd z z′ l → rwkˡ (subst (λ u → Rᵒ c b (ι d (h ξ u)) (h′ ξ′ (intoU r′ z′))) (sym (cv-into d r z))
                                  (R-ιˡ d t (f ξ ξ′ dd z z′ (cvL d r l)))))
  R-ιˡ d t (rev h) = rev (λ ok e ok′ e′ → R-ιˡ d t (h ok (proj₁ e) ok′ e′))

  R-ιʳ : ∀ {a b e φ ψ} (d′ : Dn b e) → Triv d′ → {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ a e x (ι d′ x′)
  R-ιʳ d t rz = rz
  R-ιʳ d t (rs sa r) = rs (∪zʳ t sa) (R-ιʳ d t r)
  R-ιʳ d t (rl h) = rl (λ n → R-ιʳ d t (h n))
  R-ιʳ d t (ri e h) = ri e (λ x y dd → R-ιʳ d t (h x y dd))
  R-ιʳ d t (rŝ e r h) = rŝ e (R-ιʳ d t r) (λ η ee η′ e′ dd → R-ιʳ d t (h η ee η′ e′ dd))
  R-ιʳ d t (rĉ e dz dg r h) = rĉ e dz dg (R-ιʳ d t r) (λ η ee η′ e′ dd → R-ιʳ d t (h η ee η′ e′ dd))
  R-ιʳ d t (rcl sh s r h) = rcl sh (∪zʳ t s) (R-ιʳ d t r) (λ η η′ dd → rwkʳ (R-ιʳ d t (h η η′ dd)))
  R-ιʳ d t (rwkˡ r) = rwkˡ (R-ιʳ d t r)
  R-ιʳ d t (rwkʳ r) = rwkʳ (R-ιʳ d t r)
  R-ιʳ {a = a} {e = e} d t (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek hg s f) =
    rΩ {r = r} {r′ = pl d r′} ek hg (∪zʳ t s)
       (λ ξ ξ′ dd z z′ l → rwkʳ (subst (λ u → Rᵒ a e (h ξ (intoU r z)) (ι d (h′ ξ′ u))) (sym (cv-into d r′ z′))
                                  (R-ιʳ d t (f ξ ξ′ dd z z′ l))))
  R-ιʳ d t (rev h) = rev (λ ok e ok′ e′ → R-ιʳ d t (h ok e ok′ (proj₁ e′)))
```

## §5 尾巴与 $\dot\Omega$

```agda
  R-tl : ∀ {c c′ k₁ k₂} {cv : ∀ {w} → Evt w (floᵗ k₁) → Simᴵ k₁ (w 0)} {cv′ : ∀ {w} → Evt w (floᵗ k₂) → Simᴵ k₂ (w 0)} {a : Ordˢ k₁} {b : Ordˢ k₂} →
         a ≅ˢ b → Rᵒ c c′ (tl (floᵗ k₁) cv a) (tl (floᵗ k₂) cv′ b)
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

  R-tlΩ : ∀ {c c′ η η′ φ φ′} {cv : ∀ {w} → Evt w φ → Simᴵ η (w 0)} {cv′ : ∀ {w} → Evt w φ′ → Simᴵ η′ (w 0)} → η ≅ᴵ η′ → φ ∼ₛ φ′ → Rᵒ c c′ (tl φ cv (Ωˢ η)) (tl φ′ cv′ (Ωˢ η′))
  R-tlΩ z≅ s = rs s rz
  R-tlΩ (s≅ e) s = ri e (λ x y d → rwk (R-tl d))
  R-tlΩ (l≅ h) s = rl (λ n → rwk (R-tl (Ωˢ-≅ (h n))))

  RΩ̇ : ∀ {a b} → a ≈ b → Hg a → Rᵒ a b (Ω̇ a) (Ω̇ b)
  RΩ̇ z≈ hg = rs (frefl _) rz
  RΩ̇ b≈ hg = rcl hg (frefl _) (R-tlΩ (≅ᴵ-refl (suc zero)) (frefl _)) (λ η η′ d → R-tlΩ d (∪∼ (frefl Fl₀) (tk∼ d)))
  RΩ̇ (s≈ e) hg = rΩ e hg (frefl Fl₀) (λ ξ ξ′ d z z′ l → rwk (R-ι ds ds (frefl tz) l))
  RΩ̇ (l≈ h) hg = rl (λ n → rwk (R-ι (dl n) (dl n) (frefl tz) (RΩ̇ (h n) (hg n))))
  RΩ̇ (o≈ refl h) (s₀ , hg) = rcl s₀ (frefl Fl₀) (rwk (R-ι df df (frefl tz) (RΩ̇ (h one one (≅ᴵ-refl one)) (hg one))))
    (λ η η′ d → R-ι (db η) (db η′) (tk∼ d) (RΩ̇ (h η η′ d) (hg η)))
```

## §6 搬运不改变关系

```agda
  R-trˡ  : ∀ {a a′ b φ ψ} (e : a ≈ a′) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a′ b (trO e x) y
  R-tr⁻ˡ : ∀ {a a′ b φ ψ} (e : a′ ≈ a) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a′ b (tr⁻O e x) y
  R-resˡ : ∀ {j a a′ b ξ ξ′} (q : j <ᴸ a) (e : a ≈ a′) {z : O (repO (resO q e)) ξ} {y : O b ξ′} → Rᵒ _ b z y → Rᵒ j b (backO (resO q e) z) y
  R-res⁻ˡ : ∀ {j a a′ b ξ ξ′} (q : j <ᴸ a) (e : a′ ≈ a) {z : O (repO (res⁻O q e)) ξ} {y : O b ξ′} → Rᵒ _ b z y → Rᵒ j b (backO (res⁻O q e) z) y

  R-trˡ e rz = rz
  R-trˡ e (rs sa r) = rs sa (R-trˡ e r)
  R-trˡ e (rl h) = rl (λ m → R-trˡ e (h m))
  R-trˡ e (ri ej h) = ri ej (λ x y d → R-trˡ e (h x y d))
  R-trˡ e (rŝ ec r h) = rŝ ec (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
  R-trˡ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
  R-trˡ e (rcl sh s r h) = rcl sh s (R-trˡ e r) (λ η η′ d → R-trˡ e (h η η′ d))
  R-trˡ e (rwkˡ r) = rwkˡ (R-trˡ e r)
  R-trˡ e (rwkʳ r) = rwkʳ (R-trˡ e r)
  R-trˡ {a′ = a′} {b} e (rΩ {φ = φ} {ψ} {r = q} {r′} {h = h} {h′ = h′} ek hg s f) =
    rΩ {r = ltO (resO q e)} (≈-trans (≈-sym (eqO (resO q e))) ek) (Hg-≈ (eqO (resO q e)) hg) s
       (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a′ b (trO e (h ξ (intoU q (backO (resO q e) w)))) (h′ ξ′ (intoU r′ z′))) (sym (out-intoU (ltO (resO q e)) z))
                                (R-trˡ e (f ξ ξ′ d _ z′ (intoR q (R-resˡ q e (outR (ltO (resO q e)) l))))))
  R-trˡ e (rev h) = rev (λ ok d ok′ d′ → R-trˡ e (h ok d ok′ d′))

  R-tr⁻ˡ e rz = rz
  R-tr⁻ˡ e (rs sa r) = rs sa (R-tr⁻ˡ e r)
  R-tr⁻ˡ e (rl h) = rl (λ m → R-tr⁻ˡ e (h m))
  R-tr⁻ˡ e (ri ej h) = ri ej (λ x y d → R-tr⁻ˡ e (h x y d))
  R-tr⁻ˡ e (rŝ ec r h) = rŝ ec (R-tr⁻ˡ e r) (λ η ee η′ e′ d → R-tr⁻ˡ e (h η ee η′ e′ d))
  R-tr⁻ˡ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ˡ e r) (λ η ee η′ e′ d → R-tr⁻ˡ e (h η ee η′ e′ d))
  R-tr⁻ˡ e (rcl sh s r h) = rcl sh s (R-tr⁻ˡ e r) (λ η η′ d → R-tr⁻ˡ e (h η η′ d))
  R-tr⁻ˡ e (rwkˡ r) = rwkˡ (R-tr⁻ˡ e r)
  R-tr⁻ˡ e (rwkʳ r) = rwkʳ (R-tr⁻ˡ e r)
  R-tr⁻ˡ {a′ = a′} {b} e (rΩ {φ = φ} {ψ} {r = q} {r′} {h = h} {h′ = h′} ek hg s f) =
    rΩ {r = ltO (res⁻O q e)} (≈-trans (≈-sym (eqO (res⁻O q e))) ek) (Hg-≈ (eqO (res⁻O q e)) hg) s
       (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a′ b (tr⁻O e (h ξ (intoU q (backO (res⁻O q e) w)))) (h′ ξ′ (intoU r′ z′))) (sym (out-intoU (ltO (res⁻O q e)) z))
                                (R-tr⁻ˡ e (f ξ ξ′ d _ z′ (intoR q (R-res⁻ˡ q e (outR (ltO (res⁻O q e)) l))))))
  R-tr⁻ˡ e (rev h) = rev (λ ok d ok′ d′ → R-tr⁻ˡ e (h ok d ok′ d′))

  R-resˡ zero      (s≈ e) l = R-tr⁻ˡ e l
  R-resˡ (suc q)   (s≈ e) l = R-resˡ q e l
  R-resˡ (lim n q) (l≈ h) l = R-resˡ q (h n) l
  R-resˡ (fst q)   (o≈ _ h) l = R-resˡ q (h one one (≅ᴵ-refl one)) l
  R-resˡ (bra η q) (o≈ _ h) l = R-resˡ q (h η η (≅ᴵ-refl η)) l

  R-res⁻ˡ zero      (s≈ e) l = R-trˡ e l
  R-res⁻ˡ (suc q)   (s≈ e) l = R-res⁻ˡ q e l
  R-res⁻ˡ (lim n q) (l≈ h) l = R-res⁻ˡ q (h n) l
  R-res⁻ˡ (fst q)   (o≈ _ h) l = R-res⁻ˡ q (h one one (≅ᴵ-refl one)) l
  R-res⁻ˡ (bra η q) (o≈ _ h) l = R-res⁻ˡ q (h η η (≅ᴵ-refl η)) l

  R-trʳ  : ∀ {a b b′ φ ψ} (e : b ≈ b′) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a b′ x (trO e y)
  R-tr⁻ʳ : ∀ {a b b′ φ ψ} (e : b′ ≈ b) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a b′ x (tr⁻O e y)
  R-resʳ : ∀ {j a b b′ ξ ξ′} (q : j <ᴸ b) (e : b ≈ b′) {z : O a ξ} {y : O (repO (resO q e)) ξ′} → Rᵒ a _ z y → Rᵒ a j z (backO (resO q e) y)
  R-res⁻ʳ : ∀ {j a b b′ ξ ξ′} (q : j <ᴸ b) (e : b′ ≈ b) {z : O a ξ} {y : O (repO (res⁻O q e)) ξ′} → Rᵒ a _ z y → Rᵒ a j z (backO (res⁻O q e) y)

  R-trʳ e rz = rz
  R-trʳ e (rs sa r) = rs sa (R-trʳ e r)
  R-trʳ e (rl h) = rl (λ m → R-trʳ e (h m))
  R-trʳ e (ri ej h) = ri ej (λ x y d → R-trʳ e (h x y d))
  R-trʳ e (rŝ ec r h) = rŝ ec (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
  R-trʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
  R-trʳ e (rcl sh s r h) = rcl sh s (R-trʳ e r) (λ η η′ d → R-trʳ e (h η η′ d))
  R-trʳ e (rwkˡ r) = rwkˡ (R-trʳ e r)
  R-trʳ e (rwkʳ r) = rwkʳ (R-trʳ e r)
  R-trʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h = h} {h′ = h′} ek hg s f) =
    rΩ {r = r} {r′ = ltO (resO q e)} (≈-trans ek (eqO (resO q e))) hg s
       (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a b′ (h ξ (intoU r z)) (trO e (h′ ξ′ (intoU q (backO (resO q e) w))))) (sym (out-intoU (ltO (resO q e)) z′))
                                (R-trʳ e (f ξ ξ′ d z _ (intoR r (R-resʳ q e (outR r l))))))
  R-trʳ e (rev h) = rev (λ ok d ok′ d′ → R-trʳ e (h ok d ok′ d′))

  R-tr⁻ʳ e rz = rz
  R-tr⁻ʳ e (rs sa r) = rs sa (R-tr⁻ʳ e r)
  R-tr⁻ʳ e (rl h) = rl (λ m → R-tr⁻ʳ e (h m))
  R-tr⁻ʳ e (ri ej h) = ri ej (λ x y d → R-tr⁻ʳ e (h x y d))
  R-tr⁻ʳ e (rŝ ec r h) = rŝ ec (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
  R-tr⁻ʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
  R-tr⁻ʳ e (rcl sh s r h) = rcl sh s (R-tr⁻ʳ e r) (λ η η′ d → R-tr⁻ʳ e (h η η′ d))
  R-tr⁻ʳ e (rwkˡ r) = rwkˡ (R-tr⁻ʳ e r)
  R-tr⁻ʳ e (rwkʳ r) = rwkʳ (R-tr⁻ʳ e r)
  R-tr⁻ʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h = h} {h′ = h′} ek hg s f) =
    rΩ {r = r} {r′ = ltO (res⁻O q e)} (≈-trans ek (eqO (res⁻O q e))) hg s
       (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a b′ (h ξ (intoU r z)) (tr⁻O e (h′ ξ′ (intoU q (backO (res⁻O q e) w))))) (sym (out-intoU (ltO (res⁻O q e)) z′))
                                (R-tr⁻ʳ e (f ξ ξ′ d z _ (intoR r (R-res⁻ʳ q e (outR r l))))))
  R-tr⁻ʳ e (rev h) = rev (λ ok d ok′ d′ → R-tr⁻ʳ e (h ok d ok′ d′))

  R-resʳ zero      (s≈ e) l = R-tr⁻ʳ e l
  R-resʳ (suc q)   (s≈ e) l = R-resʳ q e l
  R-resʳ (lim n q) (l≈ h) l = R-resʳ q (h n) l
  R-resʳ (fst q)   (o≈ _ h) l = R-resʳ q (h one one (≅ᴵ-refl one)) l
  R-resʳ (bra η q) (o≈ _ h) l = R-resʳ q (h η η (≅ᴵ-refl η)) l

  R-res⁻ʳ zero      (s≈ e) l = R-trʳ e l
  R-res⁻ʳ (suc q)   (s≈ e) l = R-res⁻ʳ q e l
  R-res⁻ʳ (lim n q) (l≈ h) l = R-res⁻ʳ q (h n) l
  R-res⁻ʳ (fst q)   (o≈ _ h) l = R-res⁻ʳ q (h one one (≅ᴵ-refl one)) l
  R-res⁻ʳ (bra η q) (o≈ _ h) l = R-res⁻ʳ q (h η η (≅ᴵ-refl η)) l
```

## §7 折叠: 比较跨世界一致

```agda
  R-rep : ∀ {a b φ ψ} {X : O a φ} {X′ : O b ψ} → φ ∼ₛ ψ → Rᵒ a b X X′ → ∀ n → Rᵒ a b (repᵒ X n) (repᵒ X′ n)
  R-rep s r zero = rz
  R-rep s r (suc zero) = r
  R-rep s r (suc (suc n)) = rwk (R-⊕ s (R-rep s r (suc n)) r)

  module _ {a b : LI} (cf : Cf a) (cf′ : Cf b) where
    open Fold cf using () renaming (ψᵒ to ψL; ψΩ to ψΩL; ψ̄ to ψ̄L)
    open Fold cf′ using () renaming (ψᵒ to ψR; ψΩ to ψΩR; ψ̄ to ψ̄R)

    R-ψ : ∀ {t t′ χ χ′ φ ψ} (q : t <ᴸ a) (q′ : t′ <ᴸ b) {fl : ∀ {w} → Evt w χ → Evt w Fl₀} {aq : ∀ {w} → Evt w χ → Adm w q}
          {fl′ : ∀ {w} → Evt w χ′ → Evt w Fl₀} {aq′ : ∀ {w} → Evt w χ′ → Adm w q′} → t ≈ t′ → Hg t → χ ∼ₛ χ′ →
          {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ t t′ (ψL q fl aq x) (ψR q′ fl′ aq′ x′)
    R-ψΩ : ∀ {t t′ χ χ′ φ ψ k k′} (q : t <ᴸ a) (q′ : t′ <ᴸ b) {fl : ∀ {w} → Evt w χ → Evt w Fl₀} {aq : ∀ {w} → Evt w χ → Adm w q}
          {fl′ : ∀ {w} → Evt w χ′ → Evt w Fl₀} {aq′ : ∀ {w} → Evt w χ′ → Adm w q′} → t ≈ t′ → Hg t → χ ∼ₛ χ′ →
          {fe : ∀ {w} → Evt w φ → Evt w Fl₀} {fe′ : ∀ {w} → Evt w ψ → Evt w Fl₀} {r : k <ᴸ a} {r′ : k′ <ᴸ b}
          {ac : ∀ {w} → Evt w φ → Adm w r} {ac′ : ∀ {w} → Evt w ψ → Adm w r′}
          {h : ∀ ξ → Us a r ξ → O a (ξ ∪ φ)} {h′ : ∀ ξ → Us b r′ ξ → O b (ξ ∪ ψ)} → k ≈ k′ → Hg k → φ ∼ₛ ψ →
          (∀ ξ ξ′ → ξ ∼ₛ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → LRᵒ a r z z′ → Rᵒ a b (h ξ (intoU r z)) (h′ ξ′ (intoU r′ z′))) →
          (T : Tri r q) (T′ : Tri r′ q′) → Rᵒ t t′ (ψΩL q fl aq fe r ac h T) (ψΩR q′ fl′ aq′ fe′ r′ ac′ h′ T′)
    chRR : ∀ {χ χ′ φ ψ k k′} {fl : ∀ {w} → Evt w χ → Evt w Fl₀} {fl′ : ∀ {w} → Evt w χ′ → Evt w Fl₀} → χ ∼ₛ χ′ →
          {fe : ∀ {w} → Evt w φ → Evt w Fl₀} {fe′ : ∀ {w} → Evt w ψ → Evt w Fl₀} {r : k <ᴸ a} {r′ : k′ <ᴸ b}
          {ac : ∀ {w} → Evt w φ → Adm w r} {ac′ : ∀ {w} → Evt w ψ → Adm w r′}
          {h : ∀ ξ → Us a r ξ → O a (ξ ∪ φ)} {h′ : ∀ ξ → Us b r′ ξ → O b (ξ ∪ ψ)} → k ≈ k′ → Hg k → φ ∼ₛ ψ →
          (∀ ξ ξ′ → ξ ∼ₛ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → LRᵒ a r z z′ → Rᵒ a b (h ξ (intoU r z)) (h′ ξ′ (intoU r′ z′))) →
          ∀ n → Rᵒ k k′ (Fold.chR cf fl fe r ac h n) (Fold.chR cf′ fl′ fe′ r′ ac′ h′ n)

    R-ψ q q′ et hgt sχ rz = rwk (RΩ̇ et hgt)
    R-ψ q q′ et hgt sχ (rs sa r) = rl (R-rep (∪∼ sχ sa) (R-ψ q q′ et hgt sχ r))
    R-ψ q q′ et hgt sχ (rl h) = rl (λ n → R-ψ q q′ et hgt sχ (h n))
    R-ψ q q′ et hgt sχ (ri e h) = ri e (λ x y d → R-ψ q q′ et hgt sχ (h x y d))
    R-ψ q q′ et hgt sχ (rŝ e r h) = rŝ e (R-ψ q q′ et hgt sχ r) (λ η ee η′ e′ d → R-ψ q q′ et hgt sχ (h η ee η′ e′ d))
    R-ψ q q′ et hgt sχ (rĉ e dz dg r h) = rĉ e dz dg (R-ψ q q′ et hgt sχ r) (λ η ee η′ e′ d → R-ψ q q′ et hgt sχ (h η ee η′ e′ d))
    R-ψ q q′ et hgt sχ (rcl sh s r h) = rcl sh (∪∼ sχ s) (R-ψ q q′ et hgt sχ r) (λ η η′ d → rwk (R-ψ q q′ et hgt sχ (h η η′ d)))
    R-ψ q q′ et hgt sχ (rwkˡ r) = rwkˡ (R-ψ q q′ et hgt sχ r)
    R-ψ q q′ et hgt sχ (rwkʳ r) = rwkʳ (R-ψ q q′ et hgt sχ r)
    R-ψ q q′ et hgt sχ (rev h) = rev (λ ok e ok′ e′ → R-ψ q q′ et hgt sχ (h ok (proj₂ e) ok′ (proj₂ e′)))
    R-ψ q q′ et hgt sχ (rΩ {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f) =
      rev (λ {w} {w′} ok e ok′ e′ → R-ψΩ q q′ et hgt sχ {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f _ _)

    R-ψΩ {t} {t′} q q′ {aq = aq} {aq′ = aq′} et hgt sχ {r = r} {r′ = r′} {h = h} {h′ = h′} ek hg s f (tlt (viaᴸ d p u)) (tlt (viaᴸ d′ p′ u′)) =
      rΩ {r = p} {r′ = p′} (≈-trans (≈-sym d) (≈-trans ek d′)) (Hg-≈ d hg) (∪∼ sχ s)
        (λ ξ ξ′ dd z z′ l → rwk (subst₂ (λ v v′ → Rᵒ t t′ (ψL q _ aq (h ξ (intoU r (tr⁻O d v)))) (ψR q′ _ aq′ (h′ ξ′ (intoU r′ (tr⁻O d′ v′))))) (sym (out-intoU p z)) (sym (out-intoU p′ z′))
           (R-ψ q q′ et hgt sχ (f ξ ξ′ dd _ _ (intoR r (R-tr⁻ˡ d (R-tr⁻ʳ d′ (outR p l))))))))
    R-ψΩ q q′ et hgt sχ ek hg s f (tlt (viaᴸ d p u)) (tgt (viaᴸ d′ p′ u′)) = ⊥-elim (clashL ek et d p d′ p′)
    R-ψΩ q q′ et hgt sχ ek hg s f (tlt (viaᴸ d p u)) (teq c) = ⊥-elim (clashE ek et d p c)
    R-ψΩ q q′ et hgt sχ ek hg s f (tgt (viaᴸ d′ p′ u′)) (tlt (viaᴸ d p u)) = ⊥-elim (clashL (≈-sym ek) (≈-sym et) d p d′ p′)
    R-ψΩ q q′ et hgt sχ ek hg s f (teq c) (tlt (viaᴸ d p u)) = ⊥-elim (clashE (≈-sym ek) (≈-sym et) d p c)
    R-ψΩ {χ = χ} {χ′ = χ′} {φ = φ} {ψ = ψ} q q′ {fl = fl} {fl′ = fl′} et hgt sχ {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f (tgt _) (tgt _) =
      rl (λ n → rwk (R-ψ q q′ et hgt sχ (f (χ ∪ φ) (χ′ ∪ ψ) (∪∼ sχ s) _ _ (intoR r (chRR sχ {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f n)))))
    R-ψΩ {χ = χ} {χ′ = χ′} {φ = φ} {ψ = ψ} q q′ {fl = fl} {fl′ = fl′} et hgt sχ {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f (tgt _) (teq _) =
      rl (λ n → rwk (R-ψ q q′ et hgt sχ (f (χ ∪ φ) (χ′ ∪ ψ) (∪∼ sχ s) _ _ (intoR r (chRR sχ {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f n)))))
    R-ψΩ {χ = χ} {χ′ = χ′} {φ = φ} {ψ = ψ} q q′ {fl = fl} {fl′ = fl′} et hgt sχ {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f (teq _) (tgt _) =
      rl (λ n → rwk (R-ψ q q′ et hgt sχ (f (χ ∪ φ) (χ′ ∪ ψ) (∪∼ sχ s) _ _ (intoR r (chRR sχ {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f n)))))
    R-ψΩ {χ = χ} {χ′ = χ′} {φ = φ} {ψ = ψ} q q′ {fl = fl} {fl′ = fl′} et hgt sχ {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f (teq _) (teq _) =
      rl (λ n → rwk (R-ψ q q′ et hgt sχ (f (χ ∪ φ) (χ′ ∪ ψ) (∪∼ sχ s) _ _ (intoR r (chRR sχ {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f n)))))

    chRR sχ ek hg s f zero = rwk (RΩ̇ ek hg)
    chRR {χ = χ} {χ′ = χ′} {φ = φ} {ψ = ψ} sχ {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f (suc n) =
      rwk (R-ψ r r′ ek hg s (f (χ ∪ φ) (χ′ ∪ ψ) (∪∼ sχ s) _ _ (intoR r (chRR sχ {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f n))))

    chRE : ∀ {φ ψ k k′} {fe : ∀ {w} → Evt w φ → Evt w Fl₀} {fe′ : ∀ {w} → Evt w ψ → Evt w Fl₀} {r : k <ᴸ a} {r′ : k′ <ᴸ b}
           {ac : ∀ {w} → Evt w φ → Adm w r} {ac′ : ∀ {w} → Evt w ψ → Adm w r′}
           {h : ∀ ξ → Us a r ξ → O a (ξ ∪ φ)} {h′ : ∀ ξ → Us b r′ ξ → O b (ξ ∪ ψ)} → k ≈ k′ → Hg k → φ ∼ₛ ψ →
           (∀ ξ ξ′ → ξ ∼ₛ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → LRᵒ a r z z′ → Rᵒ a b (h ξ (intoU r z)) (h′ ξ′ (intoU r′ z′))) →
           ∀ n → Rᵒ k k′ (chainᵒ fe (λ z → owk (λ v → v , (v , v)) (ψL r fe ac (h φ (intoU r z)))) n) (chainᵒ fe′ (λ z → owk (λ v → v , (v , v)) (ψR r′ fe′ ac′ (h′ ψ (intoU r′ z)))) n)
    chRE ek hg s f zero = rwk (RΩ̇ ek hg)
    chRE {φ = φ} {ψ = ψ} {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f (suc n) =
      rwk (R-ψ r r′ ek hg s (f φ ψ s _ _ (intoR r (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f n))))
```

## §8 计值

```agda
    r∅ : ∀ {φ ψ} → Fold.ψ̄ cf {φ} o0 ≈ᵗ Fold.ψ̄ cf′ {ψ} o0
    r∅ ok ev p ok′ ev′ p′ ei = Ωˢ-≅ ei

    R→≈ : ∀ {φ ψ} {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → ψ̄L x ≈ᵗ ψ̄R x′
    R→≈ rz = r∅
    R→≈ (rs s r) = sucT (R→≈ r)
    R→≈ (rl h) = limT (λ n → R→≈ (h n))
    R→≈ (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} e h) = limᵢT {ac = ac} {ac′ = ac′} {H = λ x → ψ̄L (f x)} {H′ = λ x → ψ̄R (f′ x)} e (λ x y d → R→≈ (h x y d))
    R→≈ (rŝ e r h) = ŝT e (R→≈ r) (λ η ee η′ e′ d → R→≈ (h η ee η′ e′ d))
    R→≈ (rĉ e dz dg r h) = ĉT e dz dg (R→≈ r) (λ η ee η′ e′ d → R→≈ (h η ee η′ e′ d))
    R→≈ (rcl {h = h} {t = t} {t′} {g} {g′} sh s r f) = cloT h {t = ψ̄L t} {g = λ η → ψ̄L (g η)} {t′ = ψ̄R t′} {g′ = λ η → ψ̄R (g′ η)} (s h sh) (R→≈ r) (λ η η′ d → R→≈ (f η η′ d))
    R→≈ (rwkˡ {le = le} r) = wkT le (λ e → e) (R→≈ r)
    R→≈ (rwkʳ {le′ = le′} r) = wkT (λ e → e) le′ (R→≈ r)
    R→≈ (rΩ {φ = φ} {ψ} {fe = fe} {fe′} {r} {r′} {ac} {ac′} {h} {h′} ek hg s f) =
      limT (λ n → wkT (λ v → v , v) (λ v → v , v) (R→≈ (f φ ψ s _ _ (intoR r (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek hg s f n)))))
    R→≈ (rev h) ok ev p ok′ ev′ p′ ei = R→≈ (h ok ev ok′ ev′) ok ev p ok′ ev′ p′ ei
```
