# 序数高度的世界: 折叠保结构等价

> 不含记号, 不含累加 (`Nx` 是模块参数). 结论写在 [CumHt](CumHt.lagda.md). `ψQ`: 目标模 `≈ᴴ`, `≈ᴬ` 相同, 项 `≈`, 则输出 `≈`. 运行世界 $v$ 不进结论: 输出闭包的世界是规范的 (`m≈`). 对两边的项同时递归. 与 [CumUpPsi](CumUpPsi.lagda.md) 同形, 差别: 高度模等价, 两边的 `cmpH` 分开算, 交叉的情形由 `clashᴴ`, `no-<≈` 排除.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumHtBase using (Nx)
module OCF.Align.CumHtPsi (𝓝 : Nx) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; z⊲; ≪∘; ≪S; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumHtBase
open import OCF.Align.CumHtTree
open import OCF.Align.CumHtEq
open import OCF.Align.CumHtW 𝓝
open Nx 𝓝
```

## §1 链保等价

```agda
ixs≈ : ∀ {m m′} (gm : Gw m) (gm′ : Gw m′) {y₀ y₀′ : Ord₀} {val : Ix m → Ord₀} {val′ : Ix m′ → Ord₀} → m ≈ᴬ m′ → y₀ ≅ y₀′ →
       (∀ i i′ → Ix.η i ≈ᴬ Ix.η i′ → val i ≅ val′ i′) → ∀ n → Ix.η (ixs gm y₀ val n) ≈ᴬ Ix.η (ixs gm′ y₀′ val′ n)
ixs≈ gm gm′ e e₀ h zero = nxt-≈ e e₀
ixs≈ gm gm′ e e₀ h (suc n) = nxt-≈ (ixs≈ gm gm′ e e₀ h n) (h _ _ (ixs≈ gm gm′ e e₀ h n))

yss≅ : ∀ {m m′} (gm : Gw m) (gm′ : Gw m′) {y₀ y₀′ : Ord₀} {val : Ix m → Ord₀} {val′ : Ix m′ → Ord₀} → m ≈ᴬ m′ → y₀ ≅ y₀′ →
       (∀ i i′ → Ix.η i ≈ᴬ Ix.η i′ → val i ≅ val′ i′) → ∀ n → yss gm y₀ val n ≅ yss gm′ y₀′ val′ n
yss≅ gm gm′ e e₀ h zero = e₀
yss≅ gm gm′ e e₀ h (suc n) = h _ _ (ixs≈ gm gm′ e e₀ h n)

plus≅ : ∀ {a a′ b b′ : Ord₀} → a ≅ a′ → b ≅ b′ → a +₀ b ≅ a′ +₀ b′
plus≅ e z≅ = e
plus≅ e (s≅ d) = s≅ (plus≅ e d)
plus≅ e (l≅ h) = l≅ (λ n → plus≅ e (h n))
plus≅ e (lᵢ≅ {p = ()} d h)
plus≅ e (upˡ {r = ()} d)
plus≅ e (upʳ {r = ()} d)

rep₀≅ : ∀ {y y′ : Ord₀} → y ≅ y′ → ∀ n → rep₀ y n ≅ rep₀ y′ n
rep₀≅ e zero = z≅
rep₀≅ e (suc zero) = e
rep₀≅ e (suc (suc m)) = plus≅ (rep₀≅ e (suc m)) e

em≈ : ∀ {u u′} {a b : Ord₀} → u ≈ᴬ u′ → a ≅ b → em {u} a ≈ em {u′} b
em≈ eu z≅ = tt
em≈ eu (s≅ e) = (refl , z≈) , z≈ , eu , em≈ eu e
em≈ eu (l≅ h) = λ n → em≈ eu (h n)
em≈ eu (lᵢ≅ {p = ()} e h)
em≈ eu (upˡ {r = ()} e)
em≈ eu (upʳ {r = ()} e)


```

## §2 `ψQ`

`NL q t`: 目标不是第 0 层. 第 0 层的目标走 `ψ₀`.

```agda
data NL : Ht → A → Set where
  ns  : ∀ {s y t} → NL ⟨ suc s , y ⟩ t
  zps : ∀ {b t} → NL ⟨ zero , asuc b ⟩ t
  zpl : ∀ {f t} → NL ⟨ zero , alim f ⟩ t
  zs  : ∀ {t} → NL H₀ (asuc t)
  zl  : ∀ {f} → NL H₀ (alim f)

ψ⁰Q : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (nl′ : NL q′ t′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → Mis m u (pp q) t (pp p) a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q′) t′ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ (pp q′) t′ (pp p′) a′ →
      q ≈ᴴ q′ → t ≈ᴬ t′ → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψ⁰ q′ t′ y gu′ m′ gm′ um′ tm′ am′

ψmQ : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (nl′ : NL q′ t′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : D⊲ (pp q) t v) (av : D⊲ (pp p) a v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : D⊲ (pp q′) t′ v′) (av′ : D⊲ (pp p′) a′ v′) →
     q ≈ᴴ q′ → t ≈ᴬ t′ → x ≈ y → ψᵐ q t x gu v gv uv tv av ≈ ψᵐ q′ t′ y gu′ v′ gv′ uv′ tv′ av′

ψ₀Q : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      v (gv : Gw v) (uv : u ⊲ v) (av : D⊲ (pp p) a v)
      v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (av′ : D⊲ (pp p′) a′ v′) → x ≈ y → ψ₀ x gu v gv uv av ≅ ψ₀ y gu′ v′ gv′ uv′ av′

ψQ : ∀ {p a u p′ a′ u′ q q′ t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : D⊲ (pp q) t v) (av : D⊲ (pp p) a v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : D⊲ (pp q′) t′ v′) (av′ : D⊲ (pp p′) a′ v′) →
     q ≈ᴴ q′ → t ≈ᴬ t′ → x ≈ y → ψ q t x gu v gv uv tv av ≈ ψ q′ t′ y gu′ v′ gv′ uv′ tv′ av′
ψQ {q = ⟨ suc s , y ⟩} {q′ = ⟨ .(suc s) , y′ ⟩} x z gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq@(refl , _) et e = ψmQ ns ns x z gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq et e
ψQ {q = ⟨ zero , asuc b ⟩} {q′ = ⟨ .zero , asuc b′ ⟩} x z gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq@(refl , s≈ _) et e = ψmQ zps zps x z gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq et e
ψQ {q = ⟨ zero , alim f ⟩} {q′ = ⟨ .zero , alim f′ ⟩} x z gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq@(refl , l≈ _) et e = ψmQ zpl zpl x z gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq et e
ψQ {q = ⟨ zero , azero ⟩} {q′ = ⟨ .zero , azero ⟩} x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (refl , z≈) z≈ e =
  ≈ow (em _) (pos gv′) g₀ (em _) (em≈ (≈ᴬ-refl one) (ψ₀Q x y gu gu′ v gv uv av v′ gv′ uv′ av′ e))
ψQ {q = ⟨ zero , azero ⟩} {q′ = ⟨ .zero , azero ⟩} x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq@(refl , z≈) et@(s≈ _) e = ψmQ zs zs x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq et e
ψQ {q = ⟨ zero , azero ⟩} {q′ = ⟨ .zero , azero ⟩} x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq@(refl , z≈) et@(l≈ _) e = ψmQ zl zl x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq et e

ψmQ {q = q} {q′ = q′} {t} {t′} nl nl′ x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ eq et e
  with mx gu gv uv tv av | mx gu′ gv′ uv′ tv′ av′ 
... | mx′ m gm um tm am mv is | mx′ m′ gm′ um′ tm′ am′ mv′ is′ =
  ≈ow (ψ⁰ q t x gu m gm um tm am) mv′ gm′ (ψ⁰ q′ t′ y gu′ m′ gm′ um′ tm′ am′) (ψ⁰Q nl nl′ x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e)

-- 左边是包装: 走进去
ψ⁰lm : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (nl′ : NL q′ t′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q′) t′ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ (pp q′) t′ (pp p′) a′ →
      q ≈ᴴ q′ → t ≈ᴬ t′ → x ≈ y → ψᵐ q t x gu m gm um tm am ≈ ψ⁰ q′ t′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰rm : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (nl′ : NL q′ t′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → Mis m u (pp q) t (pp p) a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q′) t′ m′) (am′ : D⊲ (pp p′) a′ m′) →
      q ≈ᴴ q′ → t ≈ᴬ t′ → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψᵐ q′ t′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰l : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (nl′ : NL q′ t′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q′) t′ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ (pp q′) t′ (pp p′) a′ →
      q ≈ᴴ q′ → t ≈ᴬ t′ → x ≈ y → ψ q t x gu m gm um tm am ≈ ψ⁰ q′ t′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰l ns nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰lm ns nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e
ψ⁰l zps nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰lm zps nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e
ψ⁰l zpl nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰lm zpl nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e
ψ⁰l zs nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰lm zs nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e
ψ⁰l zl nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰lm zl nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e

ψ⁰lm nl nl′ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ eq et e with mx gu gm um tm am 
... | mx′ m₁ g₁ u₁ t₁ a₁ _ is₁ = ψ⁰Q nl nl′ x y gu gu′ m₁ g₁ u₁ t₁ a₁ is₁ m′ gm′ um′ tm′ am′ is′ eq et e

ψ⁰r : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (nl′ : NL q′ t′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → Mis m u (pp q) t (pp p) a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q′) t′ m′) (am′ : D⊲ (pp p′) a′ m′) →
      q ≈ᴴ q′ → t ≈ᴬ t′ → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψ q′ t′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰r nl ns x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e = ψ⁰rm nl ns x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e
ψ⁰r nl zps x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e = ψ⁰rm nl zps x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e
ψ⁰r nl zpl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e = ψ⁰rm nl zpl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e
ψ⁰r nl zs x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e = ψ⁰rm nl zs x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e
ψ⁰r nl zl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e = ψ⁰rm nl zl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e

ψ⁰rm {q = q} {q′ = q′} {t} {t′} nl nl′ x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ eq et e with mx gu′ gm′ um′ tm′ am′ 
... | mx′ m₁ g₁ u₁ t₁ a₁ mv is₁ = ≈ow (ψ⁰ q t x gu m gm um tm am) mv g₁ (ψ⁰ q′ t′ y gu′ m₁ g₁ u₁ t₁ a₁) (ψ⁰Q nl nl′ x y gu gu′ m gm um tm am is m₁ g₁ u₁ t₁ a₁ is₁ eq et e)

ψLl : ∀ {p h k u p′ a′ u′ q q′ t t′} (nl : NL q t) (nl′ : NL q′ t′) (j : h <ᴴ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (km : D⊲ (pp h) k m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q′) t′ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ (pp q′) t′ (pp p′) a′ →
      q ≈ᴴ q′ → t ≈ᴬ t′ → ELl j x y → ψL q t j x gu m gm um tm km ≈ ψ⁰ q′ t′ y gu′ m′ gm′ um′ tm′ am′
ψLl nl nl′ hs0 (bx x) y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰l nl nl′ x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e
ψLl nl nl′ (hl0 n₀) (bx x) y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰l nl nl′ x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e
ψLl nl nl′ hr0 (bx x) y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰l nl nl′ x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e
ψLl nl nl′ (hsS j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e = ψLl nl nl′ j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e
ψLl nl nl′ (hlS n₀ j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e = ψLl nl nl′ j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e
ψLl nl nl′ (hrS j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e = ψLl nl nl′ j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ eq et e

ψLr : ∀ {p a u p′ h k u′ q q′ t t′} (nl : NL q t) (nl′ : NL q′ t′) (x : 𝓞 p a u) (j : h <ᴴ p′) (y : Low p′ j k u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → Mis m u (pp q) t (pp p) a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q′) t′ m′) (km′ : D⊲ (pp h) k m′) →
      q ≈ᴴ q′ → t ≈ᴬ t′ → ELr x j y → ψ⁰ q t x gu m gm um tm am ≈ ψL q′ t′ j y gu′ m′ gm′ um′ tm′ km′
ψLr nl nl′ x hs0 (bx y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e = ψ⁰r nl nl′ x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e
ψLr nl nl′ x (hl0 n₀) (bx y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e = ψ⁰r nl nl′ x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e
ψLr nl nl′ x hr0 (bx y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e = ψ⁰r nl nl′ x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e
ψLr nl nl′ x (hsS j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e = ψLr nl nl′ x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e
ψLr nl nl′ x (hlS n₀ j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e = ψLr nl nl′ x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e
ψLr nl nl′ x (hrS j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e = ψLr nl nl′ x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ eq et e

-- 左边包装
ψ⁰Q nl nl′ (oe es x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰l nl nl′ x y gu gu′ m gm um tm (Dr (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′ eq et e
ψ⁰Q nl nl′ (oe (el n) x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰l nl nl′ x y gu gu′ m gm um tm (Dr (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′ eq et e
ψ⁰Q nl nl′ (oL j k e₁ x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψLl nl nl′ j x y gu gu′ m gm um tm (dE j e₁ um (d₁ am)) m′ gm′ um′ tm′ am′ is′ eq et e
ψ⁰Q nl nl′ (ow p g x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰l nl nl′ x y g gu′ m gm (⊲-tr p um) tm am m′ gm′ um′ tm′ am′ is′ eq et e
ψ⁰Q nl nl′ X@o0 (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) eq et e
ψ⁰Q nl nl′ X@o0 (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) eq et e
ψ⁰Q nl nl′ X@o0 (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψLr nl nl′ X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (dE j₂ e₂ um′ (d₁ am′)) eq et e
ψ⁰Q nl nl′ X@o0 (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ eq et e
ψ⁰Q nl nl′ X@(os x) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) eq et e
ψ⁰Q nl nl′ X@(os x) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) eq et e
ψ⁰Q nl nl′ X@(os x) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψLr nl nl′ X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (dE j₂ e₂ um′ (d₁ am′)) eq et e
ψ⁰Q nl nl′ X@(os x) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ eq et e
ψ⁰Q nl nl′ X@(ol F) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) eq et e
ψ⁰Q nl nl′ X@(ol F) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) eq et e
ψ⁰Q nl nl′ X@(ol F) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψLr nl nl′ X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (dE j₂ e₂ um′ (d₁ am′)) eq et e
ψ⁰Q nl nl′ X@(ol F) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ eq et e
ψ⁰Q nl nl′ X@(oi r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) eq et e
ψ⁰Q nl nl′ X@(oi r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) eq et e
ψ⁰Q nl nl′ X@(oi r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψLr nl nl′ X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (dE j₂ e₂ um′ (d₁ am′)) eq et e
ψ⁰Q nl nl′ X@(oi r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ eq et e
ψ⁰Q nl nl′ X@(od j k r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) eq et e
ψ⁰Q nl nl′ X@(od j k r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) eq et e
ψ⁰Q nl nl′ X@(od j k r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψLr nl nl′ X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (dE j₂ e₂ um′ (d₁ am′)) eq et e
ψ⁰Q nl nl′ X@(od j k r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ eq et e
ψ⁰Q nl nl′ X@(oc x f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) eq et e
ψ⁰Q nl nl′ X@(oc x f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) eq et e
ψ⁰Q nl nl′ X@(oc x f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψLr nl nl′ X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (dE j₂ e₂ um′ (d₁ am′)) eq et e
ψ⁰Q nl nl′ X@(oc x f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ψ⁰r nl nl′ X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ eq et e
-- 对角
ψ⁰Q {q = q} nl nl′ o0 o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e = ≈-Ωat gm gm′ eq et
ψ⁰Q nl nl′ (os x) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et (ep , ea , eu , e) =
  λ n → rep≈ eq et (m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea)) (ψQ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ eq et e) gm gm′ n
ψ⁰Q nl nl′ (ol F) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et e =
  λ n → ψQ (F n) (G n) gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ eq et (e n)
ψ⁰Q {p = p} {p′ = p′} {q = q} {q′ = q′} {t = t} {t′ = t′} nl nl′ (oi {k = k} r f) (oi {k = k′} r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et (ep , ea , eu , ek , N) with cmpH p q (d₁ am) (d₁ tm) (lgw gm) | cmpH p′ q′ (d₁ am′) (d₁ tm′) (lgw gm′)
... | injᵃ i | injᵃ i′ = eq , ep , et , m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea) , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (D-tr tm w) (D-tr am w) v′ g′ C.self (D-tr tm′ w′) (D-tr am′ w′) eq et
         (nI {r = r} {r′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i′ y y′ d)))
... | injᵃ i | injᵇ i′ = ⊥-elim (clashᴴ i i′ ep eq)
... | injᵃ i | injᶜ refl = ⊥-elim (no-<≈ i (≈ᴴ-trans ep (≈ᴴ-sym eq)))
... | injᵇ i | injᵃ i′ = ⊥-elim (clashᴴ i′ i (≈ᴴ-sym ep) (≈ᴴ-sym eq))
... | injᵇ i | injᶜ refl = ⊥-elim (no-<≈ i (≈ᴴ-trans eq (≈ᴴ-sym ep)))
... | injᶜ refl | injᵃ i′ = ⊥-elim (no-<≈ i′ (≈ᴴ-trans (≈ᴴ-sym ep) eq))
... | injᶜ refl | injᵇ i′ = ⊥-elim (no-<≈ i′ (≈ᴴ-trans (≈ᴴ-sym eq) ep))
... | injᵇ _ | injᵇ _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ eq et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea)
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (Dr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p′ k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (Dr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat gm gm′ ep ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (Dr (≪⊲ r) am) am m′ gm′ C.self (Dr (≪⊲ r′) am′) am′ ep ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
... | injᶜ refl | injᶜ refl with cmpN (≪∘ r (d₂ am)) (d₂ tm) (lgw gm) | cmpN (≪∘ r′ (d₂ am′)) (d₂ tm′) (lgw gm′)
...   | keep s | keep s′ = eq , et , m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea) , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (D-tr tm w) (D-tr am w) v′ g′ C.self (D-tr tm′ w′) (D-tr am′ w′) eq et
         (nI {r = r} {r′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q₁ = ⊥-elim (clash s q₁ ek et)
...   | rise q₁ | keep s′ = ⊥-elim (clash s′ q₁ (≈ᴬ-sym ek) (≈ᴬ-sym et))
...   | rise _ | rise _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ eq et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea)
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (Dr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p′ k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (Dr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat gm gm′ ep ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (Dr (≪⊲ r) am) am m′ gm′ C.self (Dr (≪⊲ r′) am′) am′ ep ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ⁰Q {q = q} {q′ = q′} {t = t} {t′ = t′} nl nl′ (od {h = h₀} j k r f) (od {h = h₁} j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et (ep , eh , ea , eu , ek , N) with cmpH h₀ q (d₁ (dR j r um (d₁ am))) (d₁ tm) (lgw gm) | cmpH h₁ q′ (d₁ (dR j′ r′ um′ (d₁ am′))) (d₁ tm′) (lgw gm′)
... | injᵃ i | injᵃ i′ = eq , eh , et , m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea) , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (D-tr tm w) (D-tr am w) v′ g′ C.self (D-tr tm′ w′) (D-tr am′ w′) eq et
         (nD {j = j} {j′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i′ y y′ d)))
... | injᵃ i | injᵇ i′ = ⊥-elim (clashᴴ i i′ eh eq)
... | injᵃ i | injᶜ refl = ⊥-elim (no-<≈ i (≈ᴴ-trans eh (≈ᴴ-sym eq)))
... | injᵇ i | injᵃ i′ = ⊥-elim (clashᴴ i′ i (≈ᴴ-sym eh) (≈ᴴ-sym eq))
... | injᵇ i | injᶜ refl = ⊥-elim (no-<≈ i (≈ᴴ-trans eq (≈ᴴ-sym eh)))
... | injᶜ refl | injᵃ i′ = ⊥-elim (no-<≈ i′ (≈ᴴ-trans (≈ᴴ-sym eh) eq))
... | injᶜ refl | injᵇ i′ = ⊥-elim (no-<≈ i′ (≈ᴴ-trans (≈ᴴ-sym eq) eh))
... | injᵇ _ | injᵇ _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ eq et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea)
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (dR j r um (d₁ am)) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₁ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (dR j′ r′ um′ (d₁ am′)) am′) n
  ch zero = ≈-Ωat gm gm′ eh ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (dR j r um (d₁ am)) am m′ gm′ C.self (dR j′ r′ um′ (d₁ am′)) am′ eh ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
... | injᶜ refl | injᶜ refl with cmpN (≪∘ (r₂ r) um) (d₂ tm) (lgw gm) | cmpN (≪∘ (r₂ r′) um′) (d₂ tm′) (lgw gm′)
...   | keep s | keep s′ = eq , et , m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea) , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (D-tr tm w) (D-tr am w) v′ g′ C.self (D-tr tm′ w′) (D-tr am′ w′) eq et
         (nD {j = j} {j′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q₁ = ⊥-elim (clash s q₁ ek et)
...   | rise q₁ | keep s′ = ⊥-elim (clash s′ q₁ (≈ᴬ-sym ek) (≈ᴬ-sym et))
...   | rise _ | rise _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ eq et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea)
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (dR j r um (d₁ am)) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₁ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (dR j′ r′ um′ (d₁ am′)) am′) n
  ch zero = ≈-Ωat gm gm′ eh ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (dR j r um (d₁ am)) am m′ gm′ C.self (dR j′ r′ um′ (d₁ am′)) am′ eh ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ⁰Q nl nl′ (oc x f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et (ep , ea , eu , e , N) =
  eq , et , m≈ is is′ um tm am um′ tm′ am′ eu (Hd eq et) (Hd ep ea) , ψQ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ eq et e ,
  (λ {v} {v′} w w′ g g′ vv → ψQ (f (⊲-tr um w) g) (f′ (⊲-tr um′ w′) g′) g g′ v g C.self (D-tr tm w) (D-tr am w) v′ g′ C.self (D-tr tm′ w′) (D-tr am′ w′) eq et (N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv))
ψ⁰Q nl nl′ o0 (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ o0 (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ o0 (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ o0 (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ o0 (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (os x) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (os x) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (os x) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (os x) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (os x) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (ol F) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (ol F) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (ol F) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (ol F) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (ol F) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oi r f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oi r f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oi r f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oi r f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oi r f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (od j k r f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (od j k r f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (od j k r f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (od j k r f) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (od j k r f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oc x f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oc x f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oc x f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oc x f) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()
ψ⁰Q nl nl′ (oc x f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ eq et ()

-- 第 0 层
ψ₀⁰Q : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
       m (gm : Gw m) (um : u ⊲ m) (am : D⊲ (pp p) a m) → Mis m u azero azero (pp p) a →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ azero azero (pp p′) a′ →
       x ≈ y → ψ₀⁰ x gu m gm um am ≅ ψ₀⁰ y gu′ m′ gm′ um′ am′

ψ₀Q x y gu gu′ v gv uv av v′ gv′ uv′ av′ e
  with mx gu gv uv (Dz v) av | mx gu′ gv′ uv′ (Dz v′) av′ 
... | mx′ m gm um tm am mv is | mx′ m′ gm′ um′ tm′ am′ mv′ is′ = ψ₀⁰Q x y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e

ψ₀l : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (am : D⊲ (pp p) a m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ azero azero (pp p′) a′ →
      x ≈ y → ψ₀ x gu m gm um am ≅ ψ₀⁰ y gu′ m′ gm′ um′ am′
ψ₀l x y gu gu′ m gm um am m′ gm′ um′ am′ is′ e with mx gu gm um (Dz m) am 
... | mx′ m₁ g₁ u₁ t₁ a₁ _ is₁ = ψ₀⁰Q x y gu gu′ m₁ g₁ u₁ a₁ is₁ m′ gm′ um′ am′ is′ e

ψ₀r : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (am : D⊲ (pp p) a m) → Mis m u azero azero (pp p) a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : D⊲ (pp p′) a′ m′) →
      x ≈ y → ψ₀⁰ x gu m gm um am ≅ ψ₀ y gu′ m′ gm′ um′ am′
ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ am′ e with mx gu′ gm′ um′ (Dz m′) am′ 
... | mx′ m₁ g₁ u₁ t₁ a₁ _ is₁ = ψ₀⁰Q x y gu gu′ m gm um am is m₁ g₁ u₁ a₁ is₁ e

ψ₀Ll : ∀ {p h k u p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
       m (gm : Gw m) (um : u ⊲ m) (km : D⊲ (pp h) k m)
       m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ azero azero (pp p′) a′ →
       ELl j x y → ψ₀L j x gu m gm um km ≅ ψ₀⁰ y gu′ m′ gm′ um′ am′
ψ₀Ll hs0 (bx x) y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (hl0 n₀) (bx x) y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll hr0 (bx x) y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (hsS j) x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (hlS n₀ j) x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (hrS j) x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e

ψ₀Lr : ∀ {p a u p′ h k u′} (x : 𝓞 p a u) (j : h <ᴴ p′) (y : Low p′ j k u′) (gu : Gw u) (gu′ : Gw u′)
       m (gm : Gw m) (um : u ⊲ m) (am : D⊲ (pp p) a m) → Mis m u azero azero (pp p) a →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (km′ : D⊲ (pp h) k m′) →
       ELr x j y → ψ₀⁰ x gu m gm um am ≅ ψ₀L j y gu′ m′ gm′ um′ km′
ψ₀Lr x hs0 (bx y) gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (hl0 n₀) (bx y) gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x hr0 (bx y) gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (hsS j) y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀Lr x j y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (hlS n₀ j) y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀Lr x j y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (hrS j) y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀Lr x j y gu gu′ m gm um am is m′ gm′ um′ km′ e

ψ₀⁰Q (oe es x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um (Dr (C.suc C.self) am) m′ gm′ um′ am′ is′ e
ψ₀⁰Q (oe (el n) x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um (Dr (C.lim n C.self) am) m′ gm′ um′ am′ is′ e
ψ₀⁰Q (oL j k e₁ x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um (dE j e₁ um (d₁ am)) m′ gm′ um′ am′ is′ e
ψ₀⁰Q (ow p g x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀l x y g gu′ m gm (⊲-tr p um) am m′ gm′ um′ am′ is′ e
ψ₀⁰Q X@o0 (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.suc C.self) am′) e
ψ₀⁰Q X@o0 (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.lim n C.self) am′) e
ψ₀⁰Q X@o0 (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (dE j₂ e₂ um′ (d₁ am′)) e
ψ₀⁰Q X@o0 (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(os x) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.suc C.self) am′) e
ψ₀⁰Q X@(os x) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.lim n C.self) am′) e
ψ₀⁰Q X@(os x) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (dE j₂ e₂ um′ (d₁ am′)) e
ψ₀⁰Q X@(os x) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(ol F) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.suc C.self) am′) e
ψ₀⁰Q X@(ol F) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.lim n C.self) am′) e
ψ₀⁰Q X@(ol F) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (dE j₂ e₂ um′ (d₁ am′)) e
ψ₀⁰Q X@(ol F) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(oi r f) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.suc C.self) am′) e
ψ₀⁰Q X@(oi r f) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.lim n C.self) am′) e
ψ₀⁰Q X@(oi r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (dE j₂ e₂ um′ (d₁ am′)) e
ψ₀⁰Q X@(oi r f) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(od j k r f) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.suc C.self) am′) e
ψ₀⁰Q X@(od j k r f) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.lim n C.self) am′) e
ψ₀⁰Q X@(od j k r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (dE j₂ e₂ um′ (d₁ am′)) e
ψ₀⁰Q X@(od j k r f) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(oc x f) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.suc C.self) am′) e
ψ₀⁰Q X@(oc x f) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (Dr (C.lim n C.self) am′) e
ψ₀⁰Q X@(oc x f) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (dE j₂ e₂ um′ (d₁ am′)) e
ψ₀⁰Q X@(oc x f) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q o0 o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = s≅ z≅
ψ₀⁰Q (os x) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (ep , ea , eu , e) = l≅ (rep₀≅ (ψ₀Q x y gu gu′ m gm um am m′ gm′ um′ am′ e))
ψ₀⁰Q (ol F) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = l≅ (λ n → ψ₀Q (F n) (G n) gu gu′ m gm um am m′ gm′ um′ am′ (e n))
ψ₀⁰Q {p = p} {p′ = p′} (oi {k = k} r f) (oi {k = k′} r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (ep , ea , eu , ek , N) =
  l≅ (λ n → ψ₀Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self am m′ gm′ C.self am′ (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n)))
  where
  M = m≈ is is′ um (Dz m) am um′ (Dz m′) am′ eu D≈-z (Hd ep ea)
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (Dr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p′ k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (Dr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat gm gm′ ep ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (Dr (≪⊲ r) am) am m′ gm′ C.self (Dr (≪⊲ r′) am′) am′ ep ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ₀⁰Q (od {h = h₀} j k r f) (od {h = h₁} j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (ep , eh , ea , eu , ek , N) =
  l≅ (λ n → ψ₀Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self am m′ gm′ C.self am′ (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n)))
  where
  M = m≈ is is′ um (Dz m) am um′ (Dz m′) am′ eu D≈-z (Hd ep ea)
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (dR j r um (d₁ am)) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₁ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (dR j′ r′ um′ (d₁ am′)) am′) n
  ch zero = ≈-Ωat gm gm′ eh ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (dR j r um (d₁ am)) am m′ gm′ C.self (dR j′ r′ um′ (d₁ am′)) am′ eh ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ₀⁰Q (oc x f) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (ep , ea , eu , e , N) =
  l≅ (yss≅ gm gm′ (m≈ is is′ um (Dz m) am um′ (Dz m′) am′ eu D≈-z (Hd ep ea)) (ψ₀Q x y gu gu′ m gm um am m′ gm′ um′ am′ e)
    (λ i i′ ei → ψ₀Q (f (⊲-tr um (Ix.up i)) (Ix.gη i)) (f′ (⊲-tr um′ (Ix.up i′)) (Ix.gη i′)) (Ix.gη i) (Ix.gη i′)
        (Ix.η i) (Ix.gη i) C.self (D-tr am (Ix.up i)) (Ix.η i′) (Ix.gη i′) C.self (D-tr am′ (Ix.up i′))
        (N (⊲-tr um (Ix.up i)) (⊲-tr um′ (Ix.up i′)) (Ix.gη i) (Ix.gη i′) ei)))
ψ₀⁰Q o0 (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q o0 (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q o0 (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q o0 (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q o0 (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
```
