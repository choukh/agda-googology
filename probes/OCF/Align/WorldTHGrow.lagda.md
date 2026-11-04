# 高度进世界: 严格增长

> 不含记号. 入口 [WorldTH](WorldTH.lagda.md). **定理 `T-strict`: 对一切不在 $(0,0)$ 的 $(p,a)$ (`NL p a`), 含顶, $\psi_0(\Omega_{\ldots+a})\prec\psi_0(\Omega_{\ldots+a+1})$. 不按阶段定制.** `top-val`: 顶行第 $i$ 个下标上的值 $\cong$ 第 $\eta_i$ 行; 下标 $\eta_i$ 由前一项的值回灌 (`WorldTHInst` 的 `vₛ`).

**为什么要这一篇.** `HS` 只说树合法, 不说树大; 很小的树也 `HS`. 这里的第 1 项 $\psi_0(\psi_u(\Omega_u))$ 里, 里层的 $\psi_u(\Omega_u)$ 是闭包 `oc`, 第一支是 $\psi_u(1)$, 它是 $\omega$ 个 $\Omega_u$ 的和. 所以第 2 项 $\Omega_u+\Omega_u$ 已经高过 $\Omega_u+1$, 而 $\psi_0(\Omega_u+1)\succ\psi_0(\Omega_u)$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldTHGrow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Free.Level using (_≺_; ≺z; ≺s; ≺l; ≺i; ≺u; _⊑⁰_; _≅_; ≅-refl⁰; ≅-trans; ≅-sym)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumReadW using (one; Gw; pos; g₀)
open import OCF.Align.WorldTHW
open import OCF.Align.WorldTHEq
open import OCF.Align.WorldTHPsi
open import OCF.Align.WorldTHLe
open import OCF.Align.WorldTHMain
```

## §1 第 0 层: 后继把值抬高

```agda
≺L : ∀ {ℓ₀ ℓ₁ ℓ₂} {c′ : FL.Ordᶜ ℓ₀} {c : FL.Ordᶜ ℓ₁} {a : FL.Ordᶜ ℓ₂} → c′ ≅ c → c ≺ a → c′ ≺ a
≺L d (≺z e) = ≺z (≅-trans d e)
≺L d (≺s h) = ≺s (≺L d h)
≺L d (≺l n h) = ≺l n (≺L d h)
≺L d (≺i x ex h) = ≺i x ex (≺L d h)
≺L d (≺u h) = ≺u (≺L d h)

≺+ : ∀ y z → FL.suc FL.zero ⊴₀ z → y ≺ y +₀ z
≺+ y z d = ⊴₀→⊑⁰ (+⊴ y d) (≺z (≅-refl⁰ y))

one⊴ψ₀ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : LB p a v) → FL.suc FL.zero ⊴₀ ψ₀ x gu v gv uv av
one⊴ψ₀ x gu v gv uv av = M₀.tp₀ (z⊴ {p₀ = ht azero} {a₀ = azero} {u₀ = v} x) gv gu v gv C.self (lb0 v) v gv uv av

ψ₀-os : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) → ψ₀ x gu m gm um am ≺ ψ₀⁰ (os x) gu m gm um am
ψ₀-os x gu m gm um am = ≺l 2 (≺+ (ψ₀ x gu m gm um am) (ψ₀ x gu m gm um am) (one⊴ψ₀ x gu m gm um am))
```

## §2 $1$ 是一切 $\Omega$ 的第一位置

```agda
X₁ : 𝓞 (ht azero) azero one
X₁ = Ω̇ (ht azero) azero

one⊴Ω : ∀ p a → X₁ ⊴ Ω̇ p a
one⊴Ω p (asuc c) = ni (λ q g → eR {stp = es} (rw (one⊴Ω p c)))
one⊴Ω p (alim f) = l 0 (eR {stp = el 0} (one⊴Ω p (f 0)))
one⊴Ω (ht azero) azero = rf (Ω≈ (ht≈ z≈) z≈)
one⊴Ω (ht (asuc q)) azero = fc (rL (one⊴Ω (ht q) one))
one⊴Ω (ht (alim f)) azero = l 0 (rL (one⊴Ω (ht (f 0)) azero))
one⊴Ω (tφ f) azero = fc (rL (one⊴Ω (f azero) azero))
```

## §3 $W+1\trianglelefteq W+W$

`rel`: $1$ 所在的层 $(0,0)$ 相对目标 $(p,a)$ 的关系. 不是 `Good`, 只是把 "1 比任何目标都低" 写成 `Rel`.

```agda
z<s : ∀ a → ht azero <ᴴ ht (asuc a)
z<l : ∀ f → ht azero <ᴴ ht (alim f)
z<s azero = here
z<s (asuc b) = st (z<s b)
z<s (alim f) = st (z<l f)
z<l f with zz (f 0)
  where
  zz : ∀ a → (a ≡ azero) ⊎ (ht azero <ᴴ ht a)
  zz azero = inj₁ refl
  zz (asuc a) = inj₂ (z<s a)
  zz (alim g) = inj₂ (z<l g)
... | inj₁ e = subst (λ x → ht x <ᴴ ht (alim f)) e (lh 0)
... | inj₂ j = ll 0 j

rel : ∀ {p a} → HT p → NL p a → Rel (ht azero) azero p a
rel H nzs = sa (z⊲ _)
rel H nzl = sa (z⊲ _)
rel H (ns {q}) = lw (z<s q)
rel H (nh {f}) = lw (z<l f)
rel refl nt = lw (tp azero)

relB : ∀ {p a} (H : HT p) (nl : NL p a) v → BW (rel H nl) v
relB H nzs v = lb0 v , H
relB H nzl v = lb0 v , H
relB H ns v = lb0 v , H
relB H nh v = lb0 v , H
relB refl nt v = lb0 v , refl

module Rep {p a m₁} (nl : NL p a) (H : HT p) (g₁ : Gw m₁) (Y : 𝓞 p a m₁) (E : Y ≈ Y) (d : X₁ ⊴ Y) where
  O₁ : 𝓞 (ht azero) azero one
  O₁ = o0

  -- W + 0: 一层包装里还是 W
  x″ : 𝓞 p a m₁
  x″ = add Y g₁ (rel H nl) O₁ g₀ m₁ g₁ C.self (pos g₁) (relB H nl m₁)

  E″ : Y ≈ x″
  E″ = ≈ow Y _ _ _ (≈ow Y _ _ _ E)

  -- W + 1 ⊴ W + W
  D⁰ : os x″ ⊴ rep H Y g₁ 2
  D⁰ = AddM.mR Y g₁ (hrefl H) E d (rel H nl) (sa C.self) g₀ g₁ m₁ g₁ C.self (pos g₁) (relB H nl m₁) (iu refl) m₁ g₁ C.self C.self (lb0 m₁ , H)

  -- 世界抽象: 不展开 mx
  stepR : ∀ v (gv : Gw v) (uv : m₁ ⊲ v) (av : LB p a v) → Mis v m₁ (ht azero) azero p a →
          ψ₀ Y g₁ v gv uv av ≺ ψ₀⁰ (ol (rep H Y g₁)) g₁ v gv uv av
  stepR v gv uv av is = ≺l 2 (⊴₀→⊑⁰ (M₀.mR D⁰ g₁ g₁ v gv uv av is v gv uv av)
      (≺L (ψ₀Q Y x″ g₁ g₁ v gv uv av v gv uv av E″) (ψ₀-os x″ g₁ v gv uv av)))
```

## §4 目标进 `ψᵐ`

```agda
unψ : ∀ {p a p₀ a₀ u v} (nl : NL p a) (P : 𝓞 p a v → Set) (x : 𝓞 p₀ a₀ u) (gu : Gw u) (gv : Gw v) (uv : u ⊲ v) (tv : LB p a v) (av : LB p₀ a₀ v) →
      P (ψᵐ p a x gu v gv uv tv av) → P (ψ p a x gu v gv uv tv av)
unψ nzs P x gu gv uv tv av r = r
unψ nzl P x gu gv uv tv av r = r
unψ ns P x gu gv uv tv av r = r
unψ nh P x gu gv uv tv av r = r
unψ nt P x gu gv uv tv av r = r

reψ : ∀ {p a p₀ a₀ u v} (nl : NL p a) (P : 𝓞 p a v → Set) (x : 𝓞 p₀ a₀ u) (gu : Gw u) (gv : Gw v) (uv : u ⊲ v) (tv : LB p a v) (av : LB p₀ a₀ v) →
      P (ψ p a x gu v gv uv tv av) → P (ψᵐ p a x gu v gv uv tv av)
reψ nzs P x gu gv uv tv av r = r
reψ nzl P x gu gv uv tv av r = r
reψ ns P x gu gv uv tv av r = r
reψ nh P x gu gv uv tv av r = r
reψ nt P x gu gv uv tv av r = r

O₀ : 𝓞 (ht azero) azero one
O₀ = o0

Y₁ : ∀ {p a} (t : Gw one) m (gm : Gw m) (um : one ⊲ m) (tm : LB p a m) (am : LB (ht azero) azero m) → 𝓞 p a m
Y₁ {p} {a} t m gm um tm am = ψ p a O₀ t m gm um tm am

Y₁ᵐ : ∀ {p a} (t : Gw one) m (gm : Gw m) (um : one ⊲ m) (tm : LB p a m) (am : LB (ht azero) azero m) → 𝓞 p a m
Y₁ᵐ {p} {a} t m gm um tm am = ψᵐ p a O₀ t m gm um tm am

-- ψ_(p,a)(0) 字面就是 Ω
X⊴Y : ∀ {p a m} (nl : NL p a) (gm : Gw m) (um : one ⊲ m) (tm : LB p a m) (am : LB (ht azero) azero m) → X₁ ⊴ Y₁ g₀ m gm um tm am
X⊴Y {p} {a} nl gm um tm am = unψ nl (X₁ ⊴_) O₀ g₀ gm um tm am (rw (rw (one⊴Ω p a)))

Ω≈Y : ∀ {p a m} (nl : NL p a) (gm : Gw m) (um : one ⊲ m) (tm : LB p a m) (am : LB (ht azero) azero m) → Ω̇ p a ≈ Y₁ g₀ m gm um tm am
Ω≈Y {p} {a} nl gm um tm am = unψ nl (Ω̇ p a ≈_) O₀ g₀ gm um tm am (≈ow (Ω̇ p a) _ _ _ (≈ow (Ω̇ p a) _ _ _ (Ω≈ (proj₁ (rfB tm)) (≈ᴬ-refl a))))
```

## §5 第 1 项

世界全部抽象, 只在最后代入 `mx`. 这样类型检查不用展开 `mx` 的嵌套.

```agda
T-gen₂ : ∀ {p a} (nl : NL p a) u₀ (g : Gw u₀) (e : LB p a u₀) m (gm : Gw m) (um : one ⊲ m) (am : LB p (asuc a) m) →
         ∀ m₃ (g₃ : Gw m₃) (u₃ : one ⊲ m₃) (t₃ : LB p a m₃) (a₃ : LB (ht azero) azero m₃) → Mis m₃ one p a (ht azero) azero →
         Tψ p a u₀ g e ≺ ψ₀⁰ (Ω̇ p (asuc a)) g₀ m gm um am
T-gen₂ {p} {a} nl u₀ g e m gm um am m₃ g₃ u₃ t₃ a₃ is₃ =
  ≺l 1 (⊴₀→⊑⁰ (M₀.mR d₂ g₃ gm m₃ g₃ C.self t₃ (iu refl) m gm C.self am)
    (≺L (ψ₀Q (Ω̇ p a) Y g₀ g₃ u₀ g (pos g) e m₃ g₃ C.self t₃ (Ω≈Y nl g₃ u₃ t₃ a₃))
      (Rep.stepR nl (ho→ht (proj₂ t₃)) g₃ Y (ψQ O₀ O₀ g₀ g₀ m₃ g₃ u₃ t₃ a₃ m₃ g₃ u₃ t₃ a₃ (rfB t₃) tt)
        (X⊴Y nl g₃ u₃ t₃ a₃) m₃ g₃ C.self t₃ (iu refl))))
  where
  t : LB p a m
  t = lb≪ C.zero am
  Y = Y₁ {p} {a} g₀ m₃ g₃ u₃ t₃ a₃
  Z₀ : 𝓞 p a m
  Z₀ = Ω̇at p a gm
  d₀ : X₁ ⊴ oe {R = C.ss C.self} es Z₀
  d₀ = eR {stp = es} (rw (one⊴Ω p a))
  d₁ : ψ⁰ p a X₁ g₀ m₃ g₃ u₃ t₃ a₃ ⊴ ψ p a (oe {R = C.ss C.self} es Z₀) gm m gm C.self t am
  d₁ = tR nl d₀ g₀ gm m₃ g₃ u₃ t₃ a₃ is₃ m gm C.self t am
  d₂ : ψ⁰ p a X₁ g₀ m₃ g₃ u₃ t₃ a₃ ⊴ oe {R = C.ss C.self} es (ψ p a (oe {R = C.ss C.self} es Z₀) gm m gm C.self t am)
  d₂ = eR {stp = es} d₁

T-gen : ∀ {p a} (nl : NL p a) u₀ (g : Gw u₀) (e : LB p a u₀) m (gm : Gw m) (um : one ⊲ m) (am : LB p (asuc a) m) →
        Tψ p a u₀ g e ≺ ψ₀⁰ (Ω̇ p (asuc a)) g₀ m gm um am
T-gen {p} {a} nl u₀ g e m gm um am =
  T-gen₂ nl u₀ g e m gm um am (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is g₀ gm (pos gm) (lb≪ C.zero am) (lb0 m))
  where
  M = mx g₀ gm (pos gm) (lb≪ C.zero am) (lb0 m)
```

**定理.** 不按阶段定制: $p$ 是任何合法的高度, 含顶.

```agda
T-strict : ∀ {p a} (nl : NL p a) u₀ (g : Gw u₀) (e : LB p a u₀) u₁ (g′ : Gw u₁) (e′ : LB p (asuc a) u₁) →
           Tψ p a u₀ g e ≺ Tψ p (asuc a) u₁ g′ e′
T-strict nl u₀ g e u₁ g′ e′ = T-gen nl u₀ g e (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.am M)
  where
  M = mx g₀ g′ (pos g′) (lb0 u₁) e′
```

## §6 闭包的基本列是行

顶行的分支: $\psi_0$ 在第 $i$ 个下标上的值 $\cong$ 第 `ht (η i)` 行的 $\psi_0(\Omega_{\Omega\cdot\eta_i})$. 只对顶行写, 高度行同理.

```agda
top-val : ∀ m (gm : Gw m) (um : one ⊲ m) (am : LB top azero m) (i : Ix m) (e : LB (ht (Ix.η i)) azero (Ix.η i)) →
          Tψ (ht (Ix.η i)) azero (Ix.η i) (Ix.gη i) e ≅
          ψ₀ (oL (tp (Ix.η i)) azero (z⊲ (Ix.η i) , hbv ht (Ix.η i)) (ow (pos (Ix.gη i)) g₀ (Ω̇ (ht (Ix.η i)) azero)))
             (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (lb↑ am (Ix.up i))
top-val m gm um am i e =
  ψ₀Q (Ω̇ (ht v) azero) (oL (tp v) azero (z⊲ v , hbv ht v) (ow (pos gi) g₀ (Ω̇ (ht v) azero))) g₀ gi v gi (pos gi) e v gi C.self (lb↑ am (Ix.up i))
    (≈oL (Ω̇ (ht v) azero) (tp v) (z⊲ v , hbv ht v) (ow (pos gi) g₀ (Ω̇ (ht v) azero)) (≈ow (Ω̇ (ht v) azero) (pos gi) g₀ (Ω̇ (ht v) azero) (Ω≈ (ht≈ (≈ᴬ-refl v)) z≈)))
  where
  v = Ix.η i
  gi = Ix.gη i
```

行之间的单调: 行号沿 $\triangleleft$ 上升, 值不降. 顶的第 0 行高于第 0 个高度行.

```agda
row-mono : ∀ {a b u₀ u₁} (g : Gw u₀) (g′ : Gw u₁) (e : LB (ht a) azero u₀) (e′ : LB (ht b) azero u₁) → a ⊲ b → Tψ (ht a) azero u₀ g e ⊑⁰ Tψ (ht b) azero u₁ g′ e′
row-mono {u₀ = u₀} {u₁} g g′ e e′ d = ⊴₀→⊑⁰ (M₀.tp₀ (Ωh⊴ d) g₀ g₀ u₀ g (pos g) e u₁ g′ (pos g′) e′)

row⊑top : ∀ {u₀ u₁} (g : Gw u₀) (g′ : Gw u₁) (e : LB (ht azero) azero u₀) (e′ : LB top azero u₁) → Tψ (ht azero) azero u₀ g e ⊑⁰ Tψ top azero u₁ g′ e′
row⊑top {u₀} {u₁} g g′ e e′ = ⊴₀→⊑⁰ (M₀.tp₀ (one⊴Ω top azero) g₀ g₀ u₀ g (pos g) e u₁ g′ (pos g′) e′)
```
