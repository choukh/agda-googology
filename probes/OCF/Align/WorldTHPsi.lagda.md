# 带高度的世界: 折叠保结构等价

> 不含记号. 结论写在 [WorldTH](WorldTH.lagda.md). `ψQ`: 目标模 `≈ᴬ` 相同, 项 `≈`, 则输出 `≈`. 运行世界 $v$ 不进结论: 输出闭包的世界是规范的 (`m≈`). 对两边的项同时递归.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldTHPsi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; z⊲; ≪∘; ≪S; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀; next; _⊞_; cumA; cs)
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀)
open import OCF.Align.WorldTHW
open import OCF.Align.WorldTHEq
```

## §1 累加保等价

```agda
⊞≈ : ∀ {a a′ b b′} → a ≈ᴬ a′ → b ≈ᴬ b′ → a ⊞ b ≈ᴬ a′ ⊞ b′
⊞≈ e z≈ = e
⊞≈ e (s≈ d) = s≈ (⊞≈ e d)
⊞≈ e (l≈ h) = l≈ (λ n → ⊞≈ e (h n))

cs≈ : ∀ {g g′} → (∀ n → g n ≈ᴬ g′ n) → ∀ n → cs g n ≈ᴬ cs g′ n
cs≈ h zero = h 0
cs≈ h (suc n) = ⊞≈ (cs≈ h n) (s≈ (h (suc n)))

cum≈ : ∀ {y y′ : Ord₀} → y ≅ y′ → cumA y ≈ᴬ cumA y′
cum≈ z≅ = z≈
cum≈ (s≅ e) = s≈ (cum≈ e)
cum≈ (l≅ h) = l≈ (cs≈ (λ n → cum≈ (h n)))
cum≈ (lᵢ≅ {p = ()} e h)
cum≈ (upˡ {r = ()} e)
cum≈ (upʳ {r = ()} e)

next≈ : ∀ {η η′} {y y′ : Ord₀} → η ≈ᴬ η′ → y ≅ y′ → next η y ≈ᴬ next η′ y′
next≈ e d = ⊞≈ e (s≈ (cum≈ d))

ord≅ : ∀ {u u′} (x : 𝓞 (ht azero) azero u) (y : 𝓞 (ht azero) azero u′) → x ≈ y → ord x ≅ ord y
ord≅ (ow p g x) y e = ord≅ x y e
ord≅ (oe () _) y e
ord≅ (oL () _ _ _) y e
ord≅ (oi () _) y e
ord≅ (od () _ _ _) y e
ord≅ X@o0 (ow p g y) e = ord≅ X y e
ord≅ o0 (oe () _) e
ord≅ o0 (oL () _ _ _) e
ord≅ o0 (oi () _) e
ord≅ o0 (od () _ _ _) e
ord≅ X@(os x) (ow p g y) e = ord≅ X y e
ord≅ (os x) (oe () _) e
ord≅ (os x) (oL () _ _ _) e
ord≅ (os x) (oi () _) e
ord≅ (os x) (od () _ _ _) e
ord≅ X@(ol F) (ow p g y) e = ord≅ X y e
ord≅ (ol F) (oe () _) e
ord≅ (ol F) (oL () _ _ _) e
ord≅ (ol F) (oi () _) e
ord≅ (ol F) (od () _ _ _) e
ord≅ X@(oc x h) (ow p g y) e = ord≅ X y e
ord≅ (oc x h) (oe () _) e
ord≅ (oc x h) (oL () _ _ _) e
ord≅ (oc x h) (oi () _) e
ord≅ (oc x h) (od () _ _ _) e
ord≅ o0 o0 e = z≅
ord≅ (os x) (os y) (_ , _ , _ , e) = s≅ (ord≅ x y e)
ord≅ (ol F) (ol G) e = l≅ (λ n → ord≅ (F n) (G n) (e n))
ord≅ (oc x h) (oc y h′) (_ , _ , _ , e , _) = ord≅ x y e
ord≅ o0 (os y) ()
ord≅ o0 (ol G) ()
ord≅ o0 (oc y h′) ()
ord≅ (os x) o0 ()
ord≅ (os x) (ol G) ()
ord≅ (os x) (oc y h′) ()
ord≅ (ol F) o0 ()
ord≅ (ol F) (os y) ()
ord≅ (ol F) (oc y h′) ()
ord≅ (oc x h) o0 ()
ord≅ (oc x h) (os y) ()
ord≅ (oc x h) (ol G) ()

em≈ : ∀ {u u′} {a b : Ord₀} → u ≈ᴬ u′ → a ≅ b → em {u} a ≈ em {u′} b
em≈ eu z≅ = tt
em≈ eu (s≅ e) = ht≈ z≈ , z≈ , eu , em≈ eu e
em≈ eu (l≅ h) = λ n → em≈ eu (h n)
em≈ eu (lᵢ≅ {p = ()} e h)
em≈ eu (upˡ {r = ()} e)
em≈ eu (upʳ {r = ()} e)

ixs≈ : ∀ {m m′} (gm : Gw m) (gm′ : Gw m′) {y₀ y₀′ : Ord₀} {val : Ix m → Ord₀} {val′ : Ix m′ → Ord₀} → m ≈ᴬ m′ → y₀ ≅ y₀′ →
       (∀ i i′ → Ix.η i ≈ᴬ Ix.η i′ → val i ≅ val′ i′) → ∀ n → Ix.η (ixs gm y₀ val n) ≈ᴬ Ix.η (ixs gm′ y₀′ val′ n)
ixs≈ gm gm′ e e₀ h zero = next≈ e e₀
ixs≈ gm gm′ e e₀ h (suc n) = next≈ (ixs≈ gm gm′ e e₀ h n) (h _ _ (ixs≈ gm gm′ e e₀ h n))

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
```

## §2 `ψQ`

`NL q t`: 目标不是第 0 层. 第 0 层的目标走 `ψ₀`.

```agda
data NL : Hg → A → Set where
  nzs : ∀ {t} → NL (ht azero) (asuc t)
  nzl : ∀ {f} → NL (ht azero) (alim f)
  ns  : ∀ {q t} → NL (ht (asuc q)) t
  nh  : ∀ {f t} → NL (ht (alim f)) t
  nt  : ∀ {f t} → NL (tφ f) t

ψ⁰Q : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → Mis m u q t p a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q′ t′ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ q′ t′ p′ a′ →
      (q ≈ᴴ q′) × (t ≈ᴬ t′) → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψ⁰ q′ t′ y gu′ m′ gm′ um′ tm′ am′

ψmQ : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (av : LB p a v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : LB q′ t′ v′) (av′ : LB p′ a′ v′) →
     (q ≈ᴴ q′) × (t ≈ᴬ t′) → x ≈ y → ψᵐ q t x gu v gv uv tv av ≈ ψᵐ q′ t′ y gu′ v′ gv′ uv′ tv′ av′

ψ₀Q : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      v (gv : Gw v) (uv : u ⊲ v) (av : LB p a v)
      v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (av′ : LB p′ a′ v′) → x ≈ y → ψ₀ x gu v gv uv av ≅ ψ₀ y gu′ v′ gv′ uv′ av′

ψQ : ∀ {p a u p′ a′ u′ q q′ t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (av : LB p a v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : LB q′ t′ v′) (av′ : LB p′ a′ v′) →
     (q ≈ᴴ q′) × (t ≈ᴬ t′) → x ≈ y → ψ q t x gu v gv uv tv av ≈ ψ q′ t′ y gu′ v′ gv′ uv′ tv′ av′
ψQ x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (ht≈ z≈ , z≈) e =
  ≈ow (em _) (pos gv′) g₀ (em _) (em≈ (≈ᴬ-refl one) (ψ₀Q x y gu gu′ v gv uv av v′ gv′ uv′ av′ e))
ψQ x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (ht≈ z≈ , s≈ d) e = ψmQ nzs x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (ht≈ z≈ , s≈ d) e
ψQ x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (ht≈ z≈ , l≈ d) e = ψmQ nzl x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (ht≈ z≈ , l≈ d) e
ψQ x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (ht≈ (s≈ d) , et) e = ψmQ ns x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (ht≈ (s≈ d) , et) e
ψQ x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (ht≈ (l≈ d) , et) e = ψmQ nh x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (ht≈ (l≈ d) , et) e
ψQ x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (tφ≈ d , et) e = ψmQ nt x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ (tφ≈ d , et) e

ψmQ {q = q} {q′} {t} {t′} nl x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e =
  ≈ow (ψ⁰ q t x gu (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M)) (Mx.mv M′) (Mx.gm M′) (ψ⁰ q′ t′ y gu′ (Mx.m M′) (Mx.gm M′) (Mx.um M′) (Mx.tm M′) (Mx.am M′))
    (ψ⁰Q nl x y gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu gv uv tv av) (Mx.m M′) (Mx.gm M′) (Mx.um M′) (Mx.tm M′) (Mx.am M′) (mx-is gu′ gv′ uv′ tv′ av′) et e)
  where
  M = mx gu gv uv tv av
  M′ = mx gu′ gv′ uv′ tv′ av′

-- 左边是包装: 走进去
ψ⁰lm : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q′ t′ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ q′ t′ p′ a′ →
      (q ≈ᴴ q′) × (t ≈ᴬ t′) → x ≈ y → ψᵐ q t x gu m gm um tm am ≈ ψ⁰ q′ t′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰rm : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → Mis m u q t p a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q′ t′ m′) (am′ : LB p′ a′ m′) →
      (q ≈ᴴ q′) × (t ≈ᴬ t′) → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψᵐ q′ t′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰l : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q′ t′ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ q′ t′ p′ a′ →
      (q ≈ᴴ q′) × (t ≈ᴬ t′) → x ≈ y → ψ q t x gu m gm um tm am ≈ ψ⁰ q′ t′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰l nzs x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm nzs x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰l nzl x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm nzl x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰l ns x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm ns x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰l nh x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm nh x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰l nt x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm nt x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e

ψ⁰lm nl x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e =
  ψ⁰Q nl x y gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu gm um tm am) m′ gm′ um′ tm′ am′ is′ et e
  where
  M = mx gu gm um tm am

ψ⁰r : ∀ {p a u p′ a′ u′ q q′ t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → Mis m u q t p a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q′ t′ m′) (am′ : LB p′ a′ m′) →
      (q ≈ᴴ q′) × (t ≈ᴬ t′) → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψ q′ t′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰r nzs x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (ht≈ z≈ , s≈ d) e = ψ⁰rm nzs x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (ht≈ z≈ , s≈ d) e
ψ⁰r nzl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (ht≈ z≈ , l≈ d) e = ψ⁰rm nzl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (ht≈ z≈ , l≈ d) e
ψ⁰r ns x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (ht≈ (s≈ d) , et) e = ψ⁰rm ns x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (ht≈ (s≈ d) , et) e
ψ⁰r nh x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (ht≈ (l≈ d) , et) e = ψ⁰rm nh x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (ht≈ (l≈ d) , et) e
ψ⁰r nt x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (tφ≈ d , et) e = ψ⁰rm nt x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (tφ≈ d , et) e

ψ⁰rm {q = q} {q′} {t} {t′} nl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e =
  ≈ow (ψ⁰ q t x gu m gm um tm am) (Mx.mv M) (Mx.gm M) (ψ⁰ q′ t′ y gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M))
    (ψ⁰Q nl x y gu gu′ m gm um tm am is (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu′ gm′ um′ tm′ am′) et e)
  where
  M = mx gu′ gm′ um′ tm′ am′

ψLl : ∀ {p h k u p′ a′ u′ q q′ t t′} (nl : NL q t) (j : h <ᴴ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (km : LB h k m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q′ t′ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ q′ t′ p′ a′ →
      (q ≈ᴴ q′) × (t ≈ᴬ t′) → ELl j x y → ψL q t j x gu m gm um tm km ≈ ψ⁰ q′ t′ y gu′ m′ gm′ um′ tm′ am′
ψLl nl here x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl nl (lh n₉) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl nl (tp a₉) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl nl (st j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl nl j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl nl (ll n₉ j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl nl j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl nl (tq a₉ j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl nl j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e

ψLr : ∀ {p a u p′ h k u′ q q′ t t′} (nl : NL q t) (x : 𝓞 p a u) (j : h <ᴴ p′) (y : Low p′ j k u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → Mis m u q t p a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q′ t′ m′) (km′ : LB h k m′) →
      (q ≈ᴴ q′) × (t ≈ᴬ t′) → ELr x j y → ψ⁰ q t x gu m gm um tm am ≈ ψL q′ t′ j y gu′ m′ gm′ um′ tm′ km′
ψLr nl x here y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψ⁰r nl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr nl x (lh n₉) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψ⁰r nl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr nl x (tp a₉) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψ⁰r nl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr nl x (st j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψLr nl x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr nl x (ll n₉ j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψLr nl x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr nl x (tq a₉ j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψLr nl x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e

-- 左边包装
ψ⁰Q nl (oe es x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y gu gu′ m gm um tm (lbS (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q nl (oe (el n) x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y gu gu′ m gm um tm (lbS (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q nl (oL j k e₁ x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLl nl j x y gu gu′ m gm um tm (lbe j e₁ um am) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q nl (ow p g x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y g gu′ m gm (⊲-tr p um) tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q nl X@o0 (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.suc C.self) am′) et e
ψ⁰Q nl X@o0 (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.lim n C.self) am′) et e
ψ⁰Q nl X@o0 (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbe j₂ e₂ um′ am′) et e
ψ⁰Q nl X@o0 (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(os x) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.suc C.self) am′) et e
ψ⁰Q nl X@(os x) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.lim n C.self) am′) et e
ψ⁰Q nl X@(os x) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbe j₂ e₂ um′ am′) et e
ψ⁰Q nl X@(os x) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(ol F) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.suc C.self) am′) et e
ψ⁰Q nl X@(ol F) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.lim n C.self) am′) et e
ψ⁰Q nl X@(ol F) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbe j₂ e₂ um′ am′) et e
ψ⁰Q nl X@(ol F) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(oi r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.suc C.self) am′) et e
ψ⁰Q nl X@(oi r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.lim n C.self) am′) et e
ψ⁰Q nl X@(oi r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbe j₂ e₂ um′ am′) et e
ψ⁰Q nl X@(oi r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(od j k r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.suc C.self) am′) et e
ψ⁰Q nl X@(od j k r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.lim n C.self) am′) et e
ψ⁰Q nl X@(od j k r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbe j₂ e₂ um′ am′) et e
ψ⁰Q nl X@(od j k r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(oc x f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.suc C.self) am′) et e
ψ⁰Q nl X@(oc x f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.lim n C.self) am′) et e
ψ⁰Q nl X@(oc x f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbe j₂ e₂ um′ am′) et e
ψ⁰Q nl X@(oc x f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
-- 对角
ψ⁰Q nl o0 o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ≈-Ωat gm gm′ (proj₁ et) (proj₂ et)
ψ⁰Q nl (os x) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (ep , ea , eu , e) =
  λ n → rep≈ (ho→ht (proj₂ tm)) (ho→ht (proj₂ tm′)) (proj₁ et) (proj₂ et) (m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea)) (ψQ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e) gm gm′ n
ψ⁰Q nl (ol F) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e =
  λ n → ψQ (F n) (G n) gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et (e n)
ψ⁰Q {p} {a} {p′ = p′} {a′ = a′} {q = q} {q′} {t} {t′} nl (oi {k = k} r f) (oi {k = k′} r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (ep , ea , eu , ek , N)
  with hcmp p q (proj₂ am) (proj₂ tm) (lgw gm) | hcmp p′ q′ (proj₂ am′) (proj₂ tm′) (lgw gm′) | hc≈ ep (proj₁ et) (proj₂ am) (proj₂ tm) (lgw gm) (proj₂ am′) (proj₂ tm′) (lgw gm′)
... | hlt i b | hlt i′ b′ | al-l = proj₁ et , ep , proj₂ et , m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea) , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (lb↑ tm w) (lb↑ am w) v′ g′ C.self (lb↑ tm′ w′) (lb↑ am′ w′) et
         (nI {r = r} {r′} {f} {f′}  N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i′ y y′ d)))
... | hgt _ | hgt _ | al-g = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ (m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea)) _ _ (ch n))
  where
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p′ k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (lb≪ r′ am′) am′) n
  ch zero = ≈-Ωat gm gm′ ep ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (lb≪ r am) am m′ gm′ C.self (lb≪ r′ am′) am′ (ep , ek)
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ (m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea)) _ _ (ch n))
... | hlt _ _ | hgt _ | ()
... | hlt _ _ | heq _ | ()
... | hgt _ | hlt _ _ | ()
... | hgt _ | heq _ | ()
... | heq _ | hlt _ _ | ()
... | heq _ | hgt _ | ()
... | heq refl | heq refl | al-e with cmpN (≪∘ r (proj₁ am)) (proj₁ tm) (lgw gm) | cmpN (≪∘ r′ (proj₁ am′)) (proj₁ tm′) (lgw gm′)
...   | keep s | keep s′ = proj₁ et , proj₂ et , m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea) , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (lb↑ tm w) (lb↑ am w) v′ g′ C.self (lb↑ tm′ w′) (lb↑ am′ w′) et
         (nI {r = r} {r′} {f} {f′}  N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q₁ = ⊥-elim (clash s q₁ ek (proj₂ et))
...   | rise q₁ | keep s′ = ⊥-elim (clash s′ q₁ (≈ᴬ-sym ek) (≈ᴬ-sym (proj₂ et)))
...   | rise _ | rise _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ (m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea)) _ _ (ch n))
  where
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p′ k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (lb≪ r′ am′) am′) n
  ch zero = ≈-Ωat gm gm′ ep ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (lb≪ r am) am m′ gm′ C.self (lb≪ r′ am′) am′ (ep , ek)
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ (m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea)) _ _ (ch n))
ψ⁰Q {p} {a} {p′ = p′} {a′ = a′} {q = q} {q′} {t} {t′} nl (od {h = h₀} j k r f) (od {h = h₁} j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (ep , eh , ea , eu , ek , N)
  with hcmp h₀ q (hmm j (proj₂ r) um (proj₂ am)) (proj₂ tm) (lgw gm) | hcmp h₁ q′ (hmm j′ (proj₂ r′) um′ (proj₂ am′)) (proj₂ tm′) (lgw gm′) | hc≈ eh (proj₁ et) (hmm j (proj₂ r) um (proj₂ am)) (proj₂ tm) (lgw gm) (hmm j′ (proj₂ r′) um′ (proj₂ am′)) (proj₂ tm′) (lgw gm′)
... | hlt i b | hlt i′ b′ | al-l = proj₁ et , eh , proj₂ et , m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea) , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (lb↑ tm w) (lb↑ am w) v′ g′ C.self (lb↑ tm′ w′) (lb↑ am′ w′) et
         (nD {j = j} {j′} {f} {f′}  N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i′ y y′ d)))
... | hgt _ | hgt _ | al-g = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ (m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea)) _ _ (ch n))
  where
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (lbd j r um am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₁ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (lbd j′ r′ um′ am′) am′) n
  ch zero = ≈-Ωat gm gm′ eh ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (lbd j r um am) am m′ gm′ C.self (lbd j′ r′ um′ am′) am′ (eh , ek)
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ (m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea)) _ _ (ch n))
... | hlt _ _ | hgt _ | ()
... | hlt _ _ | heq _ | ()
... | hgt _ | hlt _ _ | ()
... | hgt _ | heq _ | ()
... | heq _ | hlt _ _ | ()
... | heq _ | hgt _ | ()
... | heq refl | heq refl | al-e with cmpN (≪∘ (proj₁ r) um) (proj₁ tm) (lgw gm) | cmpN (≪∘ (proj₁ r′) um′) (proj₁ tm′) (lgw gm′)
...   | keep s | keep s′ = proj₁ et , proj₂ et , m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea) , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (lb↑ tm w) (lb↑ am w) v′ g′ C.self (lb↑ tm′ w′) (lb↑ am′ w′) et
         (nD {j = j} {j′} {f} {f′}  N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q₁ = ⊥-elim (clash s q₁ ek (proj₂ et))
...   | rise q₁ | keep s′ = ⊥-elim (clash s′ q₁ (≈ᴬ-sym ek) (≈ᴬ-sym (proj₂ et)))
...   | rise _ | rise _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ (m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea)) _ _ (ch n))
  where
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (lbd j r um am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₁ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (lbd j′ r′ um′ am′) am′) n
  ch zero = ≈-Ωat gm gm′ eh ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (lbd j r um am) am m′ gm′ C.self (lbd j′ r′ um′ am′) am′ (eh , ek)
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ (m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea)) _ _ (ch n))
ψ⁰Q nl (oc x f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (ep , ea , eu , e , N) =
  proj₁ et , proj₂ et , m≈ is is′ um tm am um′ tm′ am′ eu et (ep , ea) , ψQ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e ,
  (λ {v} {v′} w w′ g g′ vv → ψQ (f (⊲-tr um w) g) (f′ (⊲-tr um′ w′) g′) g g′ v g C.self (lb↑ tm w) (lb↑ am w) v′ g′ C.self (lb↑ tm′ w′) (lb↑ am′ w′) et (N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv))

-- 第 0 层
ψ₀⁰Q : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
       m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) → Mis m u (ht azero) azero p a →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ (ht azero) azero p′ a′ →
       x ≈ y → ψ₀⁰ x gu m gm um am ≅ ψ₀⁰ y gu′ m′ gm′ um′ am′

ψ₀Q x y gu gu′ v gv uv av v′ gv′ uv′ av′ e =
  ψ₀⁰Q x y gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.am M) (mx-is gu gv uv (lb0 v) av) (Mx.m M′) (Mx.gm M′) (Mx.um M′) (Mx.am M′) (mx-is gu′ gv′ uv′ (lb0 v′) av′) e
  where
  M = mx gu gv uv (lb0 v) av
  M′ = mx gu′ gv′ uv′ (lb0 v′) av′

ψ₀l : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (am : LB p a m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ (ht azero) azero p′ a′ →
      x ≈ y → ψ₀ x gu m gm um am ≅ ψ₀⁰ y gu′ m′ gm′ um′ am′
ψ₀l x y gu gu′ m gm um am m′ gm′ um′ am′ is′ e =
  ψ₀⁰Q x y gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.am M) (mx-is gu gm um (lb0 m) am) m′ gm′ um′ am′ is′ e
  where
  M = mx gu gm um (lb0 m) am

ψ₀r : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) → Mis m u (ht azero) azero p a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : LB p′ a′ m′) →
      x ≈ y → ψ₀⁰ x gu m gm um am ≅ ψ₀ y gu′ m′ gm′ um′ am′
ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ am′ e =
  ψ₀⁰Q x y gu gu′ m gm um am is (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.am M) (mx-is gu′ gm′ um′ (lb0 m′) am′) e
  where
  M = mx gu′ gm′ um′ (lb0 m′) am′

ψ₀Ll : ∀ {p h k u p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
       m (gm : Gw m) (um : u ⊲ m) (km : LB h k m)
       m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ (ht azero) azero p′ a′ →
       ELl j x y → ψ₀L j x gu m gm um km ≅ ψ₀⁰ y gu′ m′ gm′ um′ am′
ψ₀Ll here x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (lh n₉) x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (tp a₉) x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (st j) x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (ll n₉ j) x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (tq a₉ j) x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e

ψ₀Lr : ∀ {p a u p′ h k u′} (x : 𝓞 p a u) (j : h <ᴴ p′) (y : Low p′ j k u′) (gu : Gw u) (gu′ : Gw u′)
       m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) → Mis m u (ht azero) azero p a →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (km′ : LB h k m′) →
       ELr x j y → ψ₀⁰ x gu m gm um am ≅ ψ₀L j y gu′ m′ gm′ um′ km′
ψ₀Lr x here y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (lh n₉) y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (tp a₉) y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (st j) y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀Lr x j y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (ll n₉ j) y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀Lr x j y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (tq a₉ j) y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀Lr x j y gu gu′ m gm um am is m′ gm′ um′ km′ e

ψ₀⁰Q (oe es x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um (lbS (C.suc C.self) am) m′ gm′ um′ am′ is′ e
ψ₀⁰Q (oe (el n) x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um (lbS (C.lim n C.self) am) m′ gm′ um′ am′ is′ e
ψ₀⁰Q (oL j k e₁ x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um (lbe j e₁ um am) m′ gm′ um′ am′ is′ e
ψ₀⁰Q (ow p g x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀l x y g gu′ m gm (⊲-tr p um) am m′ gm′ um′ am′ is′ e
ψ₀⁰Q X@o0 (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.suc C.self) am′) e
ψ₀⁰Q X@o0 (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.lim n C.self) am′) e
ψ₀⁰Q X@o0 (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (lbe j₂ e₂ um′ am′) e
ψ₀⁰Q X@o0 (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(os x) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.suc C.self) am′) e
ψ₀⁰Q X@(os x) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.lim n C.self) am′) e
ψ₀⁰Q X@(os x) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (lbe j₂ e₂ um′ am′) e
ψ₀⁰Q X@(os x) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(ol F) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.suc C.self) am′) e
ψ₀⁰Q X@(ol F) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.lim n C.self) am′) e
ψ₀⁰Q X@(ol F) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (lbe j₂ e₂ um′ am′) e
ψ₀⁰Q X@(ol F) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(oi r f) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.suc C.self) am′) e
ψ₀⁰Q X@(oi r f) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.lim n C.self) am′) e
ψ₀⁰Q X@(oi r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (lbe j₂ e₂ um′ am′) e
ψ₀⁰Q X@(oi r f) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(od j k r f) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.suc C.self) am′) e
ψ₀⁰Q X@(od j k r f) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.lim n C.self) am′) e
ψ₀⁰Q X@(od j k r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (lbe j₂ e₂ um′ am′) e
ψ₀⁰Q X@(od j k r f) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(oc x f) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.suc C.self) am′) e
ψ₀⁰Q X@(oc x f) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (lbS (C.lim n C.self) am′) e
ψ₀⁰Q X@(oc x f) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (lbe j₂ e₂ um′ am′) e
ψ₀⁰Q X@(oc x f) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q o0 o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = s≅ z≅
ψ₀⁰Q (os x) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (_ , ea , eu , e) = l≅ (rep₀≅ (ψ₀Q x y gu gu′ m gm um am m′ gm′ um′ am′ e))
ψ₀⁰Q (ol F) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = l≅ (λ n → ψ₀Q (F n) (G n) gu gu′ m gm um am m′ gm′ um′ am′ (e n))
ψ₀⁰Q {p} {a} {p′ = p′} (oi {k = k} r f) (oi {k = k′} r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (ep , ea , eu , ek , N) =
  l≅ (λ n → ψ₀Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self am m′ gm′ C.self am′ (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n)))
  where
  M = m≈ is is′ um (lb0 m) am um′ (lb0 m′) am′ eu (ht≈ z≈ , z≈) (ep , ea)
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p′ k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (lb≪ r′ am′) am′) n
  ch zero = ≈-Ωat gm gm′ ep ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (lb≪ r am) am m′ gm′ C.self (lb≪ r′ am′) am′ (ep , ek)
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ₀⁰Q (od {h = h₀} j k r f) (od {h = h₁} j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (ep , eh , ea , eu , ek , N) =
  l≅ (λ n → ψ₀Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self am m′ gm′ C.self am′ (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n)))
  where
  M = m≈ is is′ um (lb0 m) am um′ (lb0 m′) am′ eu (ht≈ z≈ , z≈) (ep , ea)
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (lbd j r um am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₁ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (lbd j′ r′ um′ am′) am′) n
  ch zero = ≈-Ωat gm gm′ eh ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (lbd j r um am) am m′ gm′ C.self (lbd j′ r′ um′ am′) am′ (eh , ek)
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ₀⁰Q (oc x f) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (ep , ea , eu , e , N) =
  l≅ (yss≅ gm gm′ (m≈ is is′ um (lb0 m) am um′ (lb0 m′) am′ eu (ht≈ z≈ , z≈) (ep , ea)) (ψ₀Q x y gu gu′ m gm um am m′ gm′ um′ am′ e)
    (λ i i′ ei → ψ₀Q (f (⊲-tr um (Ix.up i)) (Ix.gη i)) (f′ (⊲-tr um′ (Ix.up i′)) (Ix.gη i′)) (Ix.gη i) (Ix.gη i′)
        (Ix.η i) (Ix.gη i) C.self (lb↑ am (Ix.up i)) (Ix.η i′) (Ix.gη i′) C.self (lb↑ am′ (Ix.up i′))
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
