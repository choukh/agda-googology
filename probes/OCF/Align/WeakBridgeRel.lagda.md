# 不带高度的树接上带高度的树 (二): 关系 `C`

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). `C M x y`: 左边 $x$ 是 [GuardTightTree](GuardTightTree.lagda.md) 的 `O A π`, 右边 $y$ 是 [LadderInfTree](LadderInfTree.lagda.md) 在实例 ℕ 的高度 0 上的 `Q 0 B φ χ`, 即 $\Omega_{\Omega+B}$. 与 [GuardCertHi](GuardCertHi.lagda.md) 的 `Rc` 的差别:
>
> 1. **下标 `M` 是界, 不是层.** 负出现 (`cΩ` 的前提) 对界递归, 右边的层 `B` 是隐式的, 不进递归. 所以右边的 `ι`, `trQ`, `tr⁻Q` 换了层, 关系不用换下标 (`R-ιQ`, `R-trQ`, `R-tr⁻Q`).
> 2. **高层的节点 `cΩ`.** 前提对一切 `ξ`, `ξ̂` 带 `CvL ξ ξ̂`, 不再要 `Emp ξ`. 这就是 `keep-Ω+2` 要的 ([GuardCertHt](GuardCertHt.lagda.md)).
> 3. **`omk`.** 左边的 `ι` 读 `omk` 的 $z$, 右边的 `ι` 把 `omk` 丢掉. 所以 `cm` 记下: $z$ 与 $\hat z$ 有关系, 右边 $y$ 是 $\hat z$ 经一串右边的运算 `Ops` 的结果, 模 `≃`. `cml` 是低层的同一件事, $y$ 来自 `tl`, 关系是 [GuardCertRel](GuardCertRel.lagda.md) 的 `Rs`.
>
> `_≃_`: 右边的结合律, 与 `Rc` 相同, 加 `≃Ω` (同一条路径, 逐点) 与 `omk`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ; Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; out-intoˢ; Ωˢ)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; flo; cvFlo; toFlo)
import OCF.Free.Tree as FT
open import OCF.Align.GuardBridgeZ using (_≲ᶻ_; zl; sl; ll; ĉl)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙; _⊙_)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardWeakRel using (⌜_⌝; Emp; out-intoU; out-intoC; out-intoV; cv-into)
open import OCF.Align.LadderInfNat using (HSℕ)
open import OCF.Align.WeakBridgeBase
import OCF.Align.LadderInfTree
module I = OCF.Align.LadderInfTree HSℕ
open I using (q0; qs; ql; qi; qŝ; qĉ; qclo; qwk; qΩ) renaming (omk to qmk; _⊞_ to _⊞_)
```

## §1 地板

```agda
QQ : Ordᴵ → Flr → I.Fv → Set
QQ B φ χ = I.Q 0 B φ χ

CvL : Fl → Flr → Set
CvL π φ = ∀ f → Mem π f → ∀ {ℓ} → Ev ℓ φ → fη f ⊑ᴵ ℓ

cvL-∪ : ∀ {π ρ φ ψ} → CvL π φ → CvL ρ ψ → CvL (π ∪ ρ) (φ ⊔ ψ)
cvL-∪ a b f (ml m) e = a f m (proj₁ e)
cvL-∪ a b f (mr m) e = b f m (proj₂ e)

cvL-emp : ∀ {π φ} → Emp π → CvL π φ
cvL-emp em f m e = ⊥-elim (em m)

cvL-wk : ∀ {π ρ φ} → Wk π ρ → CvL ρ φ → CvL π φ
cvL-wk w c f m e = c f (w m) e

Nz : LG → Set
Nz Lv.zero = ⊥
Nz (Lv.suc _) = ⊤
Nz (Lv.lim _) = ⊤
Nz (Lv.lc _ _ _) = ⊤

nz-≈ : ∀ {a b} → a ≈ b → Nz a → Nz b
nz-≈ (Lv.s≈ _) n = tt
nz-≈ (Lv.l≈ _) n = tt
nz-≈ (Lv.o≈ _ _ _) n = tt

nz-c : ∀ θ → Nz (c⁺ θ)
nz-c zero = tt
nz-c (suc θ) = tt
nz-c (lim f s) = tt
```

## §2 右边的运算

```agda
data Op : Ordᴵ → Ordᴵ → Set where
  oι   : ∀ {a b} → a ◃ b → Op a b
  otr  : ∀ {a b} → a ≅ᴵ b → Op a b
  otr⁻ : ∀ {a b} → b ≅ᴵ a → Op a b

ap₁ : ∀ {a b φ χ} → Op a b → QQ a φ χ → QQ b φ χ
ap₁ (oι r) y = I.ι r y
ap₁ (otr e) y = I.trQ e y
ap₁ (otr⁻ e) y = I.tr⁻Q e y

infixr 5 _∷ᵒ_
data Ops : Ordᴵ → Ordᴵ → Set where
  []ᵒ  : ∀ {a} → Ops a a
  _∷ᵒ_ : ∀ {a b d} → Op b d → Ops a b → Ops a d

ap : ∀ {a b φ χ} → Ops a b → QQ a φ χ → QQ b φ χ
ap []ᵒ y = y
ap (o ∷ᵒ l) y = ap₁ o (ap l y)
```

## §3 右边的 `≃`

方向: `y ≃ y′` 把 `x ~ y` 变成 `x ~ y′`, 所以地板的搬运是 `Ev φ′ → Ev φ`.

```agda
infix 4 _≃_
data _≃_ {B : Ordᴵ} : ∀ {φ φ′ χ χ′} → QQ B φ χ → QQ B φ′ χ′ → Set where
  ≃id : ∀ {φ χ} {y : QQ B φ χ} → y ≃ y
  ≃z  : ∀ {φ φ′ χ χ′} → q0 {φ = φ} {χ = χ} ≃ q0 {φ = φ′} {χ = χ′}
  ≃s  : ∀ {φ φ′ χ χ′} {y : QQ B φ χ} {y′ : QQ B φ′ χ′} → (∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ) → y ≃ y′ → qs y ≃ qs y′
  ≃l  : ∀ {φ φ′ χ χ′} {H : ℕ → QQ B φ χ} {H′ : ℕ → QQ B φ′ χ′} → (∀ n → H n ≃ H′ n) → ql H ≃ ql H′
  ≃i  : ∀ {φ φ′ χ χ′ j} {ac : ∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ} {ac′ : ∀ {ℓ} → Ev ℓ φ′ → j <ᴵ ℓ} {f : Ordˢ j → QQ B φ χ} {f′ : Ordˢ j → QQ B φ′ χ′} →
        (∀ x → f x ≃ f′ x) → qi ac f ≃ qi ac′ f′
  ≃ŝ  : ∀ {φ φ′ χ χ′ c₀} {t : QQ B φ χ} {t′ : QQ B φ′ χ′} {g : ∀ η → c₀ ⊑ᴵ η → QQ B φ χ} {g′ : ∀ η → c₀ ⊑ᴵ η → QQ B φ′ χ′} →
        t ≃ t′ → (∀ η e → g η e ≃ g′ η e) → qŝ c₀ t g ≃ qŝ c₀ t′ g′
  ≃ĉ  : ∀ {φ φ′ χ χ′ c₀ z zg} {t : QQ B φ χ} {t′ : QQ B φ′ χ′} {g : ∀ η → c₀ ⊑ᴵ η → QQ B φ χ} {g′ : ∀ η → c₀ ⊑ᴵ η → QQ B φ′ χ′} →
        t ≃ t′ → (∀ η e → g η e ≃ g′ η e) → qĉ c₀ z zg t g ≃ qĉ c₀ z zg t′ g′
  ≃c  : ∀ {φ φ′ χ χ′} {t : QQ B (φ ⊔ fk zero) χ} {t′ : QQ B (φ′ ⊔ fk zero) χ′} {g : ∀ η → QQ B (φ ⊔ fk η) χ} {g′ : ∀ η → QQ B (φ′ ⊔ fk η) χ′} →
        (∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ) → t ≃ t′ → (∀ η → g η ≃ g′ η) → qclo t g ≃ qclo t′ g′
  ≃wl : ∀ {φ φ₀ φ′ χ χ₀ χ′} {le : ∀ {ℓ} → Ev ℓ φ → Ev ℓ φ₀} {le′ : I.Sub 0 χ χ₀} {y : QQ B φ₀ χ₀} {y′ : QQ B φ′ χ′} → y ≃ y′ → qwk le le′ y ≃ y′
  ≃wr : ∀ {φ φ₀ φ′ χ χ₀ χ′} {le : ∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ₀} {le′ : I.Sub 0 χ′ χ₀} {y : QQ B φ χ} {y′ : QQ B φ₀ χ₀} → y ≃ y′ → y ≃ qwk le le′ y′
  ≃ml : ∀ {φ φ′ χ χ′ k} {r : k ◃₁ B} {z : I.Us 0 k (◃₁→◃ r) φ χ} {y : QQ B φ χ} {y′ : QQ B φ′ χ′} → y ≃ y′ → qmk r z y ≃ y′
  ≃mr : ∀ {φ φ′ χ χ′ k} {r : k ◃₁ B} {z : I.Us 0 k (◃₁→◃ r) φ′ χ′} {y : QQ B φ χ} {y′ : QQ B φ′ χ′} → y ≃ y′ → y ≃ qmk r z y′
  ≃Ω  : ∀ {φ φ′ χ χ′ k} {fe : ∀ {ℓ} → Ev ℓ φ → Ev ℓ FT.Fl} {fe′ : ∀ {ℓ} → Ev ℓ φ′ → Ev ℓ FT.Fl} (q : k <ᴵ B)
          {h : ∀ ξ ζ → I.Us 0 k (<→◃ q) ξ ζ → QQ B (ξ ⊔ φ) (I.lo 0 ζ I.∪ χ)} {h′ : ∀ ξ ζ → I.Us 0 k (<→◃ q) ξ ζ → QQ B (ξ ⊔ φ′) (I.lo 0 ζ I.∪ χ′)} →
        (∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ) → (∀ ξ ζ z → h ξ ζ z ≃ h′ ξ ζ z) → qΩ fe q h ≃ qΩ fe′ q h′

≃-trans : ∀ {B φ φ′ φ″ χ χ′ χ″} {x : QQ B φ χ} {y : QQ B φ′ χ′} {w : QQ B φ″ χ″} → x ≃ y → y ≃ w → x ≃ w
≃-trans ≃id E = E
≃-trans E ≃id = E
≃-trans (≃wl E) E′ = ≃wl (≃-trans E E′)
≃-trans (≃ml E) E′ = ≃ml (≃-trans E E′)
≃-trans E (≃wr E′) = ≃wr (≃-trans E E′)
≃-trans E (≃mr E′) = ≃mr (≃-trans E E′)
≃-trans (≃wr E) (≃wl E′) = ≃-trans E E′
≃-trans (≃mr E) (≃ml E′) = ≃-trans E E′
≃-trans ≃z ≃z = ≃z
≃-trans (≃s f E) (≃s f′ E′) = ≃s (λ e → f (f′ e)) (≃-trans E E′)
≃-trans (≃l H) (≃l H′) = ≃l (λ n → ≃-trans (H n) (H′ n))
≃-trans (≃i H) (≃i H′) = ≃i (λ x → ≃-trans (H x) (H′ x))
≃-trans (≃ŝ E H) (≃ŝ E′ H′) = ≃ŝ (≃-trans E E′) (λ η d → ≃-trans (H η d) (H′ η d))
≃-trans (≃ĉ E H) (≃ĉ E′ H′) = ≃ĉ (≃-trans E E′) (λ η d → ≃-trans (H η d) (H′ η d))
≃-trans (≃c f E H) (≃c f′ E′ H′) = ≃c (λ e → f (f′ e)) (≃-trans E E′) (λ η → ≃-trans (H η) (H′ η))
≃-trans (≃Ω q f H) (≃Ω .q f′ H′) = ≃Ω q (λ e → f (f′ e)) (λ ξ ζ z → ≃-trans (H ξ ζ z) (H′ ξ ζ z))
```

**运算保持 `≃`.**

```agda
≃-ι : ∀ {B B′ φ φ′ χ χ′} (r : B ◃ B′) {y : QQ B φ χ} {y′ : QQ B φ′ χ′} → y ≃ y′ → I.ι r y ≃ I.ι r y′
≃-ι r ≃id = ≃id
≃-ι r ≃z = ≃z
≃-ι r (≃s f e) = ≃s f (≃-ι r e)
≃-ι r (≃l h) = ≃l (λ n → ≃-ι r (h n))
≃-ι r (≃i h) = ≃i (λ x → ≃-ι r (h x))
≃-ι r (≃ŝ e h) = ≃ŝ (≃-ι r e) (λ η d → ≃-ι r (h η d))
≃-ι r (≃ĉ e h) = ≃ĉ (≃-ι r e) (λ η d → ≃-ι r (h η d))
≃-ι r (≃c f e h) = ≃c f (≃-ι r e) (λ η → ≃-ι r (h η))
≃-ι r (≃wl e) = ≃wl (≃-ι r e)
≃-ι r (≃wr e) = ≃wr (≃-ι r e)
≃-ι r (≃ml {y = y₀} e) = ≃-ι r {y = y₀} e
≃-ι r (≃mr {y′ = y₀} e) = ≃-ι r {y′ = y₀} e
≃-ι r (≃Ω q f h) = ≃Ω (FT.<◃ q r) f (λ ξ ζ z → ≃-ι r (h ξ ζ (I.intoU (<→◃ q) (I.outU (<→◃ (FT.<◃ q r)) z))))

≃-trQ : ∀ {a b φ φ′ χ χ′} (d : a ≅ᴵ b) {y : QQ a φ χ} {y′ : QQ a φ′ χ′} → y ≃ y′ → I.trQ d y ≃ I.trQ d y′
≃-tr⁻Q : ∀ {a b φ φ′ χ χ′} (d : a ≅ᴵ b) {y : QQ b φ χ} {y′ : QQ b φ′ χ′} → y ≃ y′ → I.tr⁻Q d y ≃ I.tr⁻Q d y′
≃-trQ d ≃id = ≃id
≃-trQ d ≃z = ≃z
≃-trQ d (≃s f e) = ≃s f (≃-trQ d e)
≃-trQ d (≃l h) = ≃l (λ n → ≃-trQ d (h n))
≃-trQ d (≃i h) = ≃i (λ x → ≃-trQ d (h x))
≃-trQ d (≃ŝ e h) = ≃ŝ (≃-trQ d e) (λ η c → ≃-trQ d (h η c))
≃-trQ d (≃ĉ e h) = ≃ĉ (≃-trQ d e) (λ η c → ≃-trQ d (h η c))
≃-trQ d (≃c f e h) = ≃c f (≃-trQ d e) (λ η → ≃-trQ d (h η))
≃-trQ d (≃wl e) = ≃wl (≃-trQ d e)
≃-trQ d (≃wr e) = ≃wr (≃-trQ d e)
≃-trQ (s≅ d) (≃ml {r = zero} e) = ≃ml (≃-trQ (s≅ d) e)
≃-trQ (l≅ h) (≃ml {r = self n} e) = ≃ml (≃-trQ (l≅ h) e)
≃-trQ (s≅ d) (≃mr {r = zero} e) = ≃mr (≃-trQ (s≅ d) e)
≃-trQ (l≅ h) (≃mr {r = self n} e) = ≃mr (≃-trQ (l≅ h) e)
≃-trQ d (≃Ω q f h) = ≃Ω (I.ltQ (I.resQ q d)) f (λ ξ ζ z → ≃-trQ d (h ξ ζ (I.intoU (<→◃ q) (I.backQ (I.resQ q d) (I.outU (<→◃ (I.ltQ (I.resQ q d))) z)))))

≃-tr⁻Q d ≃id = ≃id
≃-tr⁻Q d ≃z = ≃z
≃-tr⁻Q d (≃s f e) = ≃s f (≃-tr⁻Q d e)
≃-tr⁻Q d (≃l h) = ≃l (λ n → ≃-tr⁻Q d (h n))
≃-tr⁻Q d (≃i h) = ≃i (λ x → ≃-tr⁻Q d (h x))
≃-tr⁻Q d (≃ŝ e h) = ≃ŝ (≃-tr⁻Q d e) (λ η c → ≃-tr⁻Q d (h η c))
≃-tr⁻Q d (≃ĉ e h) = ≃ĉ (≃-tr⁻Q d e) (λ η c → ≃-tr⁻Q d (h η c))
≃-tr⁻Q d (≃c f e h) = ≃c f (≃-tr⁻Q d e) (λ η → ≃-tr⁻Q d (h η))
≃-tr⁻Q d (≃wl e) = ≃wl (≃-tr⁻Q d e)
≃-tr⁻Q d (≃wr e) = ≃wr (≃-tr⁻Q d e)
≃-tr⁻Q (s≅ d) (≃ml {r = zero} e) = ≃ml (≃-tr⁻Q (s≅ d) e)
≃-tr⁻Q (l≅ h) (≃ml {r = self n} e) = ≃ml (≃-tr⁻Q (l≅ h) e)
≃-tr⁻Q (s≅ d) (≃mr {r = zero} e) = ≃mr (≃-tr⁻Q (s≅ d) e)
≃-tr⁻Q (l≅ h) (≃mr {r = self n} e) = ≃mr (≃-tr⁻Q (l≅ h) e)
≃-tr⁻Q d (≃Ω q f h) = ≃Ω (I.ltQ (I.res⁻Q q d)) f (λ ξ ζ z → ≃-tr⁻Q d (h ξ ζ (I.intoU (<→◃ q) (I.backQ (I.res⁻Q q d) (I.outU (<→◃ (I.ltQ (I.res⁻Q q d))) z)))))

≃-ap₁ : ∀ {a b φ φ′ χ χ′} (o : Op a b) {y : QQ a φ χ} {y′ : QQ a φ′ χ′} → y ≃ y′ → ap₁ o y ≃ ap₁ o y′
≃-ap₁ (oι r) e = ≃-ι r e
≃-ap₁ (otr d) e = ≃-trQ d e
≃-ap₁ (otr⁻ d) e = ≃-tr⁻Q d e
```

**结合律.**

```agda
≃⊕l : ∀ {B φa φa′ φ χa χa′ χ} {a : QQ B φa χa} {a′ : QQ B φa′ χa′} (c : QQ B φ χ) → (∀ {ℓ} → Ev ℓ φa′ → Ev ℓ φa) → a ≃ a′ → (a ⊞ c) ≃ (a′ ⊞ c)
≃⊕l q0 m E = ≃wl (≃wr E)
≃⊕l (qs c) m E = ≃s (λ e → m (proj₁ e) , proj₂ e) (≃⊕l c m E)
≃⊕l (ql F) m E = ≃l (λ n → ≃⊕l (F n) m E)
≃⊕l (qi ac f) m E = ≃i (λ x → ≃⊕l (f x) m E)
≃⊕l (qŝ c₀ t g) m E = ≃ŝ (≃⊕l t m E) (λ η d → ≃⊕l (g η d) m E)
≃⊕l (qĉ c₀ z zg o₀ o) m E = ≃ĉ (≃⊕l o₀ m E) (λ η d → ≃⊕l (o η d) m E)
≃⊕l (qclo t g) m E = ≃wl (≃wr (≃c (λ e → m (proj₁ e) , proj₂ e) (≃wl (≃wr (≃⊕l t m E))) (λ η → ≃wl (≃wr (≃⊕l (g η) m E)))))
≃⊕l (I.qcl () ψ s t g) m E
≃⊕l (qwk le le′ c) m E = ≃wl (≃wr (≃⊕l c m E))
≃⊕l (I.qΩ↓ () fe ac h) m E
≃⊕l (qΩ fe q h) m E = ≃Ω q (λ e → m (proj₁ e) , proj₂ e) (λ ξ ζ z → ≃wl (≃wr (≃⊕l (h ξ ζ z) m E)))
≃⊕l (qmk r z x) m E = ≃⊕l x m E

≃as : ∀ {B φa φb φ χa χb χ} (a : QQ B φa χa) (b : QQ B φb χb) (c : QQ B φ χ) → (a ⊞ (b ⊞ c)) ≃ ((a ⊞ b) ⊞ c)
≃as a b q0 = ≃wl (≃wr ≃id)
≃as a b (qs c) = ≃s (λ { ((u , v) , w) → u , (v , w) }) (≃as a b c)
≃as a b (ql F) = ≃l (λ n → ≃as a b (F n))
≃as a b (qi ac f) = ≃i (λ x → ≃as a b (f x))
≃as a b (qŝ c₀ t g) = ≃ŝ (≃as a b t) (λ η d → ≃as a b (g η d))
≃as a b (qĉ c₀ z zg o₀ o) = ≃ĉ (≃as a b o₀) (λ η d → ≃as a b (o η d))
≃as a b (qclo t g) =
  ≃wl (≃wl (≃wr (≃c (λ { ((u , v) , w) → u , (v , w) }) (≃wl (≃wl (≃wr (≃as a b t)))) (λ η → ≃wl (≃wl (≃wr (≃as a b (g η))))))))
≃as a b (I.qcl () ψ s t g)
≃as a b (qwk le le′ c) = ≃wl (≃wr (≃as a b c))
≃as a b (I.qΩ↓ () fe ac h)
≃as a b (qΩ fe q h) = ≃Ω q (λ { ((u , v) , w) → u , (v , w) }) (λ ξ ζ z → ≃wl (≃wl (≃wr (≃as a b (h ξ ζ z)))))
≃as a b (qmk r z x) = ≃as a b x

rep≃ : ∀ {B φ χ} (ŷ : QQ B φ χ) n → (ŷ ⊞ I.repᵠ ŷ n) ≃ I.repᵠ ŷ (suc n)
rep≃ ŷ zero = ≃wl ≃id
rep≃ ŷ (suc zero) = ≃wr ≃id
rep≃ ŷ (suc (suc n)) = ≃wl (≃wr (≃-trans (≃as ŷ (I.repᵠ ŷ (suc n)) ŷ) (≃⊕l ŷ (λ e → e , e) (rep≃ ŷ (suc n)))))
```
