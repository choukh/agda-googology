# 没有闭包的世界: 闭包定理, 第一位置上的单调

> 不含记号. 结论写在 [CumRead](CumRead.lagda.md). **`ψL`: 折叠保字面第一位置. `ψW`: 折叠保 `WF`. 两条定理对一切层, 一切目标, 一步, 不用支配论证, 不问输出高于下标 (`Vis`, `Hon` 在这里不出现).**
>
> - `x ⊴ y`: $x$ 模 `≈` 是 $y$ 的第一位置. `nd`: 节点的第一位置是 $h(\Omega_k)$. 层可以不同, 懒嵌入透明.
> - `WF x`: 极限的相邻项 `⊴`, 分支单调. 输入要 `WF` 才谈得上输出 `WF`, 但 `ψL` 与 `ψQ` 不问 `WF`.
> - `ord`, `HS-ord`, `⊴→⊑⁰`: 第 0 层的树是 `OCF.Free.Level` 的序数, 相邻项的 `⊑⁰` 由 `⊴` 给. **这里没有用到 `OCF.Free` 的 `Goodᴺ`.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumReadCFThm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)
open import OCF.Free.Level using (Ordᶜ; HS; hz; hs; hl; _⊑⁰_; _≅_; ≺s; ≺l; ≺z; z≅; s≅; l≅; ≅→⊑; FGH)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF
open import OCF.Align.CumReadCFEq
```

## §1 第一位置

```agda
infix 4 _⊴_
data _⊴_ : ∀ {a b} → O a → O b → Set where
  rf : ∀ {a b} {x : O a} {y : O b} → x ≈ y → x ⊴ y
  s  : ∀ {a b} {x : O a} {y : O b} → x ⊴ y → x ⊴ os y
  l  : ∀ {a b} {x : O a} {F : ℕ → O b} n → x ⊴ F n → x ⊴ ol F
  nd : ∀ {a b k} {x : O a} {r : k ≪ b} {h : Vs b (≪S r) → O b} → x ⊴ h (inS (≪S r) (Ω̇ k)) → x ⊴ oi r h
  eR : ∀ {a b c} {x : O a} {R : Strict c b} {y : Vs b R} → x ⊴ outS R y → x ⊴ oe R y
  eL : ∀ {a b c} {R : Strict c a} {x : Vs a R} {y : O b} → outS R x ⊴ y → oe R x ⊴ y

Ω⊴ : ∀ {a b} → a ⊲ b → Ω̇ a ⊴ Ω̇ b
Ω⊴ {a} self = rf (Ω≈ a)
Ω⊴ (suc P) = nd (eR (Ω⊴ P))
Ω⊴ (lim n P) = l n (eR (Ω⊴ P))

z⊴ : ∀ {a b} (x : O b) → o0 {a} {Vs a} ⊴ x
z⊴S : ∀ {a L b} (R : Strict b L) (x : Vs L R) → o0 {a} {Vs a} ⊴ outS R x
z⊴C : ∀ {a L b} (R : b ⊲ L) (x : Vc L R) → o0 {a} {Vs a} ⊴ outC R x
z⊴ o0 = rf tt
z⊴ (os x) = s (z⊴ x)
z⊴ (ol F) = l 0 (z⊴ (F 0))
z⊴ (oi r h) = nd (z⊴ (h _))
z⊴ (oe R x) = eR (z⊴S R x)
z⊴S (ss P) x = z⊴C P x
z⊴S (sl n P) x = z⊴C P x
z⊴C self x = z⊴ x
z⊴C (suc P) x = z⊴C P x
z⊴C (lim n P) x = z⊴C P x
```

## §2 加法

`W ⊴ W + y`; 右边单调. 都不用 `WF`.

```agda
add⊴ : ∀ {L a} {W : O L} (e : W ≈ W) (P : a ⊲ L) (y : O a) → W ⊴ add W P y
add⊴S : ∀ {L b a} {W : O L} (e : W ≈ W) (P : b ⊲ L) (R : Strict a b) (y : Vs b R) → W ⊴ addS W P R y
add⊴C : ∀ {L b a} {W : O L} (e : W ≈ W) (P : b ⊲ L) (R : a ⊲ b) (y : Vc b R) → W ⊴ addC W P R y
add⊴ e P o0 = rf e
add⊴ e P (os y) = s (add⊴ e P y)
add⊴ e P (ol F) = l 0 (add⊴ e P (F 0))
add⊴ {W = W} e P (oi {k = k} r h) =
  nd (subst (λ z → W ⊴ add W P (h (inS (≪S r) z))) (sym (out-inS (≪S (≪∘ r P)) (Ω̇ k))) (add⊴ e P (h (inS (≪S r) (Ω̇ k)))))
add⊴ e P (oe R y) = add⊴S e P R y
add⊴S e P (ss R) y = add⊴C e _ R y
add⊴S e P (sl n R) y = add⊴C e _ R y
add⊴C e P self y = add⊴ e P y
add⊴C e P (suc R) y = add⊴C e _ R y
add⊴C e P (lim n R) y = add⊴C e _ R y

add-mono : ∀ {L L′ a b} {W : O L} {W′ : O L′} (P : a ⊲ L) (Q : b ⊲ L′) → W ≈ W′ → {x : O a} {y : O b} → x ⊴ y → add W P x ⊴ add W′ Q y
add-mono P Q E {x} {y} (rf e) = rf (add≈ P Q E x y e)
add-mono P Q E (s d) = s (add-mono P Q E d)
add-mono P Q E (l n d) = l n (add-mono P Q E d)
add-mono {W = W} {W′} P Q E {x} (nd {k = k} {r = r} {h = h} d) =
  nd (subst (λ z → add W P x ⊴ add W′ Q (h (inS (≪S r) z))) (sym (out-inS (≪S (≪∘ r Q)) (Ω̇ k))) (add-mono P Q E d))
add-mono {W = W} {W′} P Q E {x} (eR {R = R} {y = y} d) =
  subst (λ z → add W P x ⊴ z) (sym (addSe W′ Q R y)) (add-mono P _ E d)
add-mono {W = W} {W′} P Q E {y = y} (eL {R = R} {x = x} d) =
  subst (λ z → z ⊴ add W′ Q y) (sym (addSe W P R x)) (add-mono _ Q E d)
```

## §3 折叠保第一位置

对推导递归. 节点: 上升时第 0 项就是 $h(\Omega_k)$; 保留时第一位置也是 $h(\Omega_k)$. **没有比较两个分支, 没有地板.**

```agda
ψL : ∀ {t a b} {x : O a} {y : O b} (T : Tg t a) (w : Lg a) (T′ : Tg t b) (w′ : Lg b) → x ⊴ y → ψ t T w x ⊴ ψ t T′ w′ y
ψL {x = x} {y} T w T′ w′ (rf e) = rf (ψQ x y T w T′ w′ e)
ψL T w T′ w′ (s d) = l 1 (ψL T w T′ w′ d)
ψL T w T′ w′ (l n d) = l n (ψL T w T′ w′ d)
ψL {t} {x = x} T w T′ w′ (nd {k = k} {r = r} {h = h} d) with rkT r T′ w′
... | keep s′ = nd (subst (λ z → ψ t T w x ⊴ ψ t T′ w′ (h (inS (≪S r) z))) (sym (out-inS (≪S s′) (Ω̇ k))) (ψL T w T′ w′ d))
... | rise q = l 0 (ψL T w T′ w′ d)
ψL {t} {x = x} T w T′ w′ (eR {R = R} {y = y} d) =
  subst (λ z → ψ t T w x ⊴ z) (sym (ψSe t R (tgS R T′ w′) (lgS R w′) y)) (ψL T w _ _ d)
ψL {t} {y = y} T w T′ w′ (eL {R = R} {x = x} d) =
  subst (λ z → z ⊴ ψ t T′ w′ y) (sym (ψSe t R (tgS R T w) (lgS R w) x)) (ψL _ _ T′ w′ d)
```

## §4 `WF`

```agda
WF : ∀ {L} → O L → Set
WFS : ∀ {L a} (R : Strict a L) → Vs L R → Set
WFC : ∀ {L a} (P : a ⊲ L) → Vc L P → Set
WF o0 = ⊤
WF (os a) = WF a
WF (ol F) = (∀ n → F n ⊴ F (suc n)) × (∀ n → WF (F n))
WF (oi r h) =
  (∀ y y′ → outS (≪S r) y ⊴ outS (≪S r) y′ → h y ⊴ h y′) ×
  (∀ y → outS (≪S r) y ≈ outS (≪S r) y → WFS (≪S r) y → WF (h y))
WF (oe R x) = WFS R x
WFS (ss P) x = WFC P x
WFS (sl n P) x = WFC P x
WFC self x = WF x
WFC (suc P) x = WFC P x
WFC (lim n P) x = WFC P x

S→W : ∀ {L a} (R : Strict a L) (x : Vs L R) → WFS R x → WF (outS R x)
C→W : ∀ {L a} (P : a ⊲ L) (x : Vc L P) → WFC P x → WF (outC P x)
S→W (ss P) x u = C→W P x u
S→W (sl n P) x u = C→W P x u
C→W self x u = u
C→W (suc P) x u = C→W P x u
C→W (lim n P) x u = C→W P x u

W→S : ∀ {L a} (R : Strict a L) (x : Vs L R) → WF (outS R x) → WFS R x
W→C : ∀ {L a} (P : a ⊲ L) (x : Vc L P) → WF (outC P x) → WFC P x
W→S (ss P) x u = W→C P x u
W→S (sl n P) x u = W→C P x u
W→C self x u = u
W→C (suc P) x u = W→C P x u
W→C (lim n P) x u = W→C P x u

-- 把分支写成 O k 的值
hW : ∀ {b k} {r : k ≪ b} {h : Vs b (≪S r) → O b} → WF (oi r h) → (z : O k) → z ≈ z → WF z → WF (h (inS (≪S r) z))
hW {r = r} (_ , p) z e u =
  p _ (subst₂ _≈_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r) z)) e) (W→S (≪S r) _ (subst WF (sym (out-inS (≪S r) z)) u))

hM : ∀ {b k} {r : k ≪ b} {h : Vs b (≪S r) → O b} → WF (oi r h) → {z z′ : O k} → z ⊴ z′ → h (inS (≪S r) z) ⊴ h (inS (≪S r) z′)
hM {r = r} (m , _) {z} {z′} d = m _ _ (subst₂ _⊴_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r) z′)) d)

ΩW : ∀ L → Lg L → WF (Ω̇ L)
ΩW azero w = tt
ΩW (asuc a) w = (λ y y′ d → eL (eR d)) , (λ y _ u → u)
ΩW (alim f) (st , w) = (λ n → eL (eR (Ω⊴ (st n)))) , (λ n → ΩW (f n) (w n))
```

**加法与 $y\cdot n$ 保 `WF`.**

```agda
addW : ∀ {L a} {W : O L} (e : W ≈ W) → WF W → (P : a ⊲ L) (y : O a) → WF y → WF (add W P y)
addWS : ∀ {L b a} {W : O L} (e : W ≈ W) → WF W → (P : b ⊲ L) (R : Strict a b) (y : Vs b R) → WFS R y → WF (addS W P R y)
addWC : ∀ {L b a} {W : O L} (e : W ≈ W) → WF W → (P : b ⊲ L) (R : a ⊲ b) (y : Vc b R) → WFC R y → WF (addC W P R y)
addW e u P o0 v = u
addW e u P (os y) v = addW e u P y v
addW e u P (ol F) (st , v) = (λ n → add-mono P P e (st n)) , (λ n → addW e u P (F n) (v n))
addW {W = W} e u P (oi {k = k} r h) v =
  (λ y y′ d → add-mono P P e (hM {r = r} v (subst₂ _⊴_ refl refl d))) ,
  (λ y py uy → addW e u P (h _) (hW {r = r} v _ py (S→W (≪S (≪∘ r P)) y uy)))
addW e u P (oe R y) v = addWS e u P R y v
addWS e u P (ss R) y v = addWC e u _ R y v
addWS e u P (sl n R) y v = addWC e u _ R y v
addWC e u P self y v = addW e u P y v
addWC e u P (suc R) y v = addWC e u _ R y v
addWC e u P (lim n R) y v = addWC e u _ R y v

repW : ∀ {L} {y : O L} → y ≈ y → WF y → ∀ n → WF (rep y n)
repW e u zero = tt
repW e u (suc zero) = u
repW {y = y} e u (suc (suc m)) = addW (rep≈ e (suc m)) (repW e u (suc m)) self y u

rep⊴ : ∀ {L} {y : O L} → y ≈ y → ∀ n → rep y n ⊴ rep y (suc n)
rep⊴ {y = y} e zero = z⊴ y
rep⊴ {y = y} e (suc m) = add⊴ (rep≈ e (suc m)) self y
```

## §5 闭包定理

对项递归. 上升时链 $z_n$ 的 `WF`, 相邻的 `⊴` 都是这条定理自己: $z_0=\Omega_k$ 是 $\psi_k$ 的任何值的第一位置 (`ψL` 用在 `z⊴` 上). **与阶段无关.**

```agda
ψW : ∀ {t L} (x : O L) (T : Tg t L) (w : Lg L) → Lg t → x ≈ x → WF x → WF (ψ t T w x)
ψWS : ∀ {t L a} (R : Strict a L) (x : Vs L R) (T : Tg t a) (w : Lg a) → Lg t → outS R x ≈ outS R x → WFS R x → WF (ψS t R T w x)
ψWC : ∀ {t L a} (R : a ⊲ L) (x : Vc L R) (T : Tg t a) (w : Lg a) → Lg t → outC R x ≈ outC R x → WFC R x → WF (ψC t R T w x)

ψW {t} o0 T w wt e u = ΩW t wt
ψW {t} (os a) T w wt e u =
  (λ n → rep⊴ (ψQ a a T w T w e) n) , (λ n → repW (ψQ a a T w T w e) (ψW a T w wt e u) n)
ψW (ol F) T w wt e (st , u) =
  (λ n → ψL T w T w (st n)) , (λ n → ψW (F n) T w wt (e n) (u n))
ψW {t} {L} (oi {k = k} r h) T w wt e u with rkT r T w
... | keep s′ =
  (λ y y′ d → ψL T w T w (hM {r = r} u d)) ,
  (λ y py uy → ψW (h _) T w wt (node≈ {r = r} {r} {h} {h} e _ _ py) (hW {r = r} u _ py (S→W (≪S s′) y uy)))
... | rise q = (λ n → ψL T w T w (hM {r = r} u (zS n))) , (λ n → ψW (h _) T w wt (node≈ {r = r} {r} {h} {h} e _ _ (zP n)) (hW {r = r} u _ (zP n) (zW n)))
  where
  Tk : Tg k L
  Tk = inj₁ (≪⊲ r)
  wk : Lg k
  wk = lg⊲ (≪⊲ r) w
  z : ℕ → O k
  z = chainᵒ (λ z₁ → ψ k Tk w (h (inS (≪S r) z₁)))
  zP : ∀ n → z n ≈ z n
  zP zero = Ω≈ k
  zP (suc n) = ψQ (h _) (h _) Tk w Tk w (node≈ {r = r} {r} {h} {h} e _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩW k wk
  zW (suc n) = ψW (h _) Tk w wk (node≈ {r = r} {r} {h} {h} e _ _ (zP n)) (hW {r = r} u _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = ψL Tk w Tk w (z⊴ (h _))
  zS (suc n) = ψL Tk w Tk w (hM {r = r} u (zS n))
ψW (oe R x) T w wt e u = ψWS R x (tgS R T w) (lgS R w) wt (oe≈ (outS R x) R x (L→ R x e)) u

ψWS (ss R) x T w wt e u = ψWC R x T w wt e u
ψWS (sl n R) x T w wt e u = ψWC R x T w wt e u
ψWC self x T w wt e u = ψW x T w wt e u
ψWC (suc R) x T w wt e u = ψWC R x T w wt e u
ψWC (lim n R) x T w wt e u = ψWC R x T w wt e u
```

## §6 第 0 层

```agda
Ord₀ : Set
Ord₀ = Ordᶜ FL.zero

ord : O azero → Ord₀
ord o0 = FL.zero
ord (os x) = FL.suc (ord x)
ord (ol F) = FL.lim (λ n → ord (F n))
ord (oi () h)
ord (oe () x)

≈→≅ : (x y : O azero) → x ≈ y → ord x ≅ ord y
≈→≅ o0 o0 e = z≅
≈→≅ (os x) (os y) e = s≅ (≈→≅ x y e)
≈→≅ (ol F) (ol G) e = l≅ (λ n → ≈→≅ (F n) (G n) (e n))
≈→≅ (oi () h) y e
≈→≅ (oe () x) y e
≈→≅ o0 (oi () h) e
≈→≅ o0 (oe () y) e
≈→≅ (os x) (oi () h) e
≈→≅ (os x) (oe () y) e
≈→≅ (ol F) (oi () h) e
≈→≅ (ol F) (oe () y) e

⊴→⊑⁰ : {x y : O azero} → x ⊴ y → ord x ⊑⁰ ord y
⊴→⊑⁰ {x} {y} (rf e) = ≅→⊑ (≈→≅ x y e)
⊴→⊑⁰ (s d) c = ≺s (⊴→⊑⁰ d c)
⊴→⊑⁰ (l n d) c = ≺l n (⊴→⊑⁰ d c)
⊴→⊑⁰ (nd {r = ()} d)
⊴→⊑⁰ (eR {R = ()} d)
⊴→⊑⁰ (eL {R = ()} d)

HS-ord : (x : O azero) → WF x → HS (ord x)
HS-ord o0 u = hz
HS-ord (os x) u = hs (HS-ord x u)
HS-ord (ol F) (st , u) = hl (λ n → HS-ord (F n) (u n)) (λ n → ⊴→⊑⁰ (st n))
HS-ord (oi () h) u
HS-ord (oe () x) u
```

## §7 $\psi_0(\Omega_\eta)$

**定理.** 对任何字面合法的 $\eta$, $\psi_0(\Omega_\eta)$ 是 `HS` 序数; $\eta$ 的字面第一位置给 `⊑⁰`. 这里 $\eta$ **不必是链点**, 不必低于输出.

```agda
Y : ∀ η → Lg η → Ord₀
Y η w = ord (ψ₀Ω η w)

HS-Y : ∀ η (w : Lg η) → HS (Y η w)
HS-Y η w = HS-ord _ (ψW (Ω̇ η) _ w tt (Ω≈ η) (ΩW η w))

Y-mono : ∀ {a b} (wa : Lg a) (wb : Lg b) → a ⊲ b → Y a wa ⊑⁰ Y b wb
Y-mono wa wb p = ⊴→⊑⁰ (ψL _ wa _ wb (Ω⊴ p))
```
