# 树的算子语言 (八): 高度 0 的树就是旧折叠

> 不含记号. 入口 [TLOps](TLOps.lagda.md). `T₀≅Y`: **高度 $0$ 的 `Tᵖ azero a` 与 [CumReadCF](CumReadCF.lagda.md) 的 `Y a` 结构互模拟**, 没有世界, 没有前缀的差. 这条以前只有有限测试 (`NoCumAccept.okᴺ`). 所以 $\psi_0(\Omega_a)$ 这一段不需要世界, 世界只服务闭包.
>
> `Sm x y`: 左边 `𝓞 azero L u`, 右边 `O b`. `oe`, `ow` 左透明, `oe` 右透明. 闭包 `oc` 没有规则: 高度 0 的项走不到它.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsSim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
import OCF.Free.Level as FL
open FL using (_≅_; z≅; s≅; l≅)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ≪S; ≪⊲; ≪∘; ⊲-tr; z⊲; lg⊲; Rk; keep; rise; cmpN; Tg; rkT; tgS; lgS)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadCFThm using (ord; Y)
open import OCF.Align.NoCumLit using (Ord₀; _≈ᴬ_; ≈ᴬ-refl; ≈ᴬ-sym)
open import OCF.Align.TLOpsW
open import OCF.Align.TLOpsEq using (clash)
open import OCF.Align.TLOpsPre using (G; force; g0; gs; gl; gw; gc; G-Tᵖ)
```

## §1 关系

```agda
private
  𝓟 : A → A → Set
  𝓟 a u = 𝓞 azero a u

module _ (L : A) (S< : ∀ {a} (R : Strict a L) {u} → Vs azero L R u → ∀ {b} → C.O b → Set) where
  data Sm₊ : ∀ {b u} → 𝓟 L u → C.O b → Set where
    sz : ∀ {b u} → Sm₊ {b} {u} o0 C.o0
    su : ∀ {b u} {x : 𝓟 L u} {y : C.O b} → Sm₊ x y → Sm₊ (os x) (C.os y)
    sL : ∀ {b u} {F : ℕ → 𝓟 L u} {G₁ : ℕ → C.O b} → (∀ n → Sm₊ (F n) (G₁ n)) → Sm₊ (ol F) (C.ol G₁)
    si : ∀ {b u k} {r : k ≪ L} {r′ : k ≪ b} {h : ∀ {v} → u ⊲ v → Gw v → Vs azero L (≪S r) v → 𝓟 L v} {g : C.Vs b (≪S r′) → C.O b} →
         (∀ {v} (w : u ⊲ v) (gv : Gw v) (x : 𝓟 k v) (y : C.O k) → S< (≪S r) (inS (≪S r) x) y → Sm₊ (h w gv (inS (≪S r) x)) (g (C.inS (≪S r′) y))) →
         Sm₊ (oi r h) (C.oi r′ g)
    se : ∀ {b u a} {R : Strict a L} {stp : Stp R} {x : Vs azero L R u} {y : C.O b} → S< R x y → Sm₊ (oe stp x) y
    sw : ∀ {b u v} {p : u ⊲ v} {g′ : Gw u} {x : 𝓟 L u} {y : C.O b} → Sm₊ x y → Sm₊ (ow p g′ x) y
    sE : ∀ {b c u} {R : Strict c b} {x : 𝓟 L u} {y : C.Vs b R} → Sm₊ x (C.outS R y) → Sm₊ x (C.oe R y)

Sm : ∀ {L b u} → 𝓟 L u → C.O b → Set
SS : ∀ L {a} (R : Strict a L) {u} → Vs azero L R u → ∀ {b} → C.O b → Set
SC : ∀ L {a} (P : a ⊲ L) {u} → Vc azero L P u → ∀ {b} → C.O b → Set
Sm {L} = Sm₊ L (SS L)
SS (asuc b) (ss P) x y = SC b P x y
SS (alim f) (sl n P) x y = SC (f n) P x y
SC a C.self x y = Sm x y
SC (asuc b) (C.suc P) x y = SC b P x y
SC (alim f) (C.lim n P) x y = SC (f n) P x y

C→Sm : ∀ {L a u b} (P : a ⊲ L) {x : 𝓟 a u} {y : C.O b} → SC L P (inC P x) y → Sm x y
C→Sm C.self d = d
C→Sm (C.suc P) d = C→Sm P d
C→Sm (C.lim n P) d = C→Sm P d

Sm→C : ∀ {L a u b} (P : a ⊲ L) {x : 𝓟 a u} {y : C.O b} → Sm x y → SC L P (inC P x) y
Sm→C C.self d = d
Sm→C (C.suc P) d = Sm→C P d
Sm→C (C.lim n P) d = Sm→C P d

S→Sm : ∀ {L a u b} (R : Strict a L) {x : 𝓟 a u} {y : C.O b} → SS L R (inS R x) y → Sm x y
S→Sm (ss P) d = C→Sm P d
S→Sm (sl n P) d = C→Sm P d

Sm→S : ∀ {L a u b} (R : Strict a L) {x : 𝓟 a u} {y : C.O b} → Sm x y → SS L R (inS R x) y
Sm→S (ss P) d = Sm→C P d
Sm→S (sl n P) d = Sm→C P d
```

## §2 $\Omega$, 加法, 倍数

```agda
Sm-Ω : ∀ L → Sm (Ω̇ azero L) (C.Ω̇ L)
Sm-Ω azero = su sz
Sm-Ω (asuc c) = si (λ w gv x y d → se {stp = es} (sE {R = ss C.self} d))
Sm-Ω (alim f) = sL (λ n → se {stp = el n} (sE {R = sl n C.self} (Sm-Ω (f n))))

Sm-Ωat : ∀ L {v} (g : Gw v) → Sm (Ω̇at azero L g) (C.Ω̇ L)
Sm-Ωat L g = sw (Sm-Ω L)

-- 加法: 右边的左分量 W 对齐
module AddS {L u₀ b} {W : 𝓟 L u₀} {W′ : C.O b} (gu : Gw u₀) (dW : Sm W W′) where
  sq⁰ : ∀ {a w c} (P : a ⊲ L) (Q : c ⊲ b) {x : 𝓟 a w} {y : C.O c} (gx : Gw w) → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : azero ⊲ m) → Sm x y → Sm (add⁰ W gu (sa P) x gx m gm um tm am) (C.add W′ Q y)
  sq  : ∀ {a w c} (P : a ⊲ L) (Q : c ⊲ b) {x : 𝓟 a w} {y : C.O c} (gx : Gw w) → ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : azero ⊲ v) → Sm x y → Sm (add W gu (sa P) x gx v gv uv xv bv) (C.add W′ Q y)
  rS  : ∀ {a w c d} (P : a ⊲ L) (Q : c ⊲ b) (R : Strict d c) {x : 𝓟 a w} {y : C.Vs c R} (gx : Gw w) → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : azero ⊲ m) → Sm x (C.outS R y) → Sm (add⁰ W gu (sa P) x gx m gm um tm am) (C.addS W′ Q R y)
  rC  : ∀ {a w c d} (P : a ⊲ L) (Q : c ⊲ b) (R : d ⊲ c) {x : 𝓟 a w} {y : C.Vc c R} (gx : Gw w) → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : azero ⊲ m) → Sm x (C.outC R y) → Sm (add⁰ W gu (sa P) x gx m gm um tm am) (C.addC W′ Q R y)

  sq P Q gx v gv uv xv bv d with mx gu gv uv xv bv
  ... | mx′ m gm um tm am mv = sw (sq⁰ P Q gx m gm um tm am d)

  rS P Q (ss R) gx m gm um tm am d = rC P (⊲-tr (C.suc C.self) Q) R gx m gm um tm am d
  rS P Q (sl n R) gx m gm um tm am d = rC P (⊲-tr (C.lim n C.self) Q) R gx m gm um tm am d
  rC P Q C.self gx m gm um tm am d = sq⁰ P Q gx m gm um tm am d
  rC P Q (C.suc R) gx m gm um tm am d = rC P (⊲-tr (C.suc C.self) Q) R gx m gm um tm am d
  rC P Q (C.lim n R) gx m gm um tm am d = rC P (⊲-tr (C.lim n C.self) Q) R gx m gm um tm am d

  sq⁰ P Q gx m gm um tm am (sE {R = R} d) = rS P Q R gx m gm um tm am d
  sq⁰ P Q gx m gm um tm am sz = sw dW
  sq⁰ P Q gx m gm um tm am (su d) = su (sq P Q gx m gm um tm am d)
  sq⁰ P Q gx m gm um tm am (sL h) = sL (λ n → sq P Q gx m gm um tm am (h n))
  sq⁰ P Q gx m gm um tm am (si {r = r} {r′ = r′} {h = h} {g = g} H) =
    si (λ {v} w gv x y dxy →
      subst₂ (λ u₁ v₁ → Sm (add W gu (sa P) (h (⊲-tr tm w) gv (inS (≪S r) u₁)) gv v gv (⊲-tr um w) C.self (z⊲ v)) (C.add W′ Q (g (C.inS (≪S r′) v₁))))
             (sym (out-inS (≪S (≪∘ r P)) x)) (sym (C.out-inS (≪S (≪∘ r′ Q)) y))
             (sq P Q gv v gv (⊲-tr um w) C.self (z⊲ v) (H (⊲-tr tm w) gv _ _ (Sm→S (≪S r) (S→Sm (≪S (≪∘ r P)) dxy)))))
  sq⁰ P Q gx m gm um tm am (se {stp = es} d) = sq (⊲-tr (C.suc C.self) P) Q gx m gm um tm am d
  sq⁰ P Q gx m gm um tm am (se {stp = el n} d) = sq (⊲-tr (C.lim n C.self) P) Q gx m gm um tm am d
  sq⁰ P Q gx m gm um tm am (sw {p = p} {g′ = g′} d) = sq P Q g′ m gm um (⊲-tr p tm) am d

rep~ : ∀ {t u b} {y : 𝓟 t u} {y′ : C.O b} (g : Gw u) → Sm y y′ → ∀ n → Sm (rep y g n) (C.rep y′ n)
rep~ g d zero = sz
rep~ g d (suc zero) = d
rep~ {u = u} g d (suc (suc m)) = AddS.sq g (rep~ g d (suc m)) C.self C.self g u g C.self C.self (z⊲ u) d
```

## §3 折叠

目标是高度 0 的 $t$, 右边的 `Tg` 任意. 比较的结果在两边一致: `clash`.

```agda
Sψ⁰ : ∀ {t L u b} {x : 𝓟 L u} {y : C.O b} (H : Hk azero azero) (gu : Gw u) → ∀ m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : L ⊲ m) (T : Tg t b) (w : Lg b) → Sm x y → Sm (ψ⁰ azero t H x gu m gm um tm am) (C.ψ t T w y)
Sψ  : ∀ {t L u b} {x : 𝓟 L u} {y : C.O b} (H : Hk azero azero) (gu : Gw u) → ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : L ⊲ v) (T : Tg t b) (w : Lg b) → Sm x y → Sm (ψ azero t H x gu v gv uv tv av) (C.ψ t T w y)
pS  : ∀ {t L u b a} {x : 𝓟 L u} (R : Strict a b) {y : C.Vs b R} (H : Hk azero azero) (gu : Gw u) → ∀ m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : L ⊲ m) (T : Tg t a) (w : Lg a) → Sm x (C.outS R y) → Sm (ψ⁰ azero t H x gu m gm um tm am) (C.ψS t R T w y)
pC  : ∀ {t L u b a} {x : 𝓟 L u} (R : a ⊲ b) {y : C.Vc b R} (H : Hk azero azero) (gu : Gw u) → ∀ m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : L ⊲ m) (T : Tg t a) (w : Lg a) → Sm x (C.outC R y) → Sm (ψ⁰ azero t H x gu m gm um tm am) (C.ψC t R T w y)

pS (ss R) H gu m gm um tm am T w d = pC R H gu m gm um tm am T w d
pS (sl n R) H gu m gm um tm am T w d = pC R H gu m gm um tm am T w d
pC C.self H gu m gm um tm am T w d = Sψ⁰ H gu m gm um tm am T w d
pC (C.suc R) H gu m gm um tm am T w d = pC R H gu m gm um tm am T w d
pC (C.lim n R) H gu m gm um tm am T w d = pC R H gu m gm um tm am T w d

Sψ H gu v gv uv tv av T w d with mx gu gv uv tv av
... | mx′ m gm um tm am mv = sw (Sψ⁰ H gu m gm um tm am T w d)

Sψ⁰ H gu m gm um tm am T w (sE {R = R} d) = pS R H gu m gm um tm am (tgS R T w) (lgS R w) d
Sψ⁰ {t = t} H gu m gm um tm am T w sz = Sm-Ωat t gm
Sψ⁰ H gu m gm um tm am T w (su d) = sL (rep~ gm (Sψ H gu m gm um tm am T w d))
Sψ⁰ H gu m gm um tm am T w (sL h) = sL (λ n → Sψ H gu m gm um tm am T w (h n))
Sψ⁰ H gu m gm um tm am T w (se {stp = es} d) = Sψ H gu m gm um tm (⊲-tr (C.suc C.self) am) T w d
Sψ⁰ H gu m gm um tm am T w (se {stp = el n} d) = Sψ H gu m gm um tm (⊲-tr (C.lim n C.self) am) T w d
Sψ⁰ H gu m gm um tm am T w (sw {p = p} {g′ = g′} d) = Sψ H g′ m gm (⊲-tr p um) tm am T w d
Sψ⁰ {t = t} H gu m gm um tm am T w (si {k = k} {r = r} {r′ = r′} {h = h} {g = g} I) with trH H
... | tlt ()
... | tgt ()
... | teq with cmpN (≪∘ r am) tm (lgw gm) | rkT r′ T w
...   | keep s | keep s′ =
  si (λ {v} w₁ gv x y dxy →
    subst₂ (λ u₁ v₁ → Sm (ψ azero t H (h (⊲-tr um w₁) gv (inS (≪S r) u₁)) gv v gv C.self (⊲-tr tm w₁) (⊲-tr am w₁)) (C.ψ t T w (g (C.inS (≪S r′) v₁))))
           (sym (out-inS (≪S s) x)) (sym (C.out-inS (≪S s′) y))
           (Sψ H gv v gv C.self (⊲-tr tm w₁) (⊲-tr am w₁) T w (I (⊲-tr um w₁) gv _ _ (Sm→S (≪S r) (S→Sm (≪S s) dxy)))))
...   | keep s | rise q′ = ⊥-elim (clash s q′ (≈ᴬ-refl k) (≈ᴬ-refl t))
...   | rise q′ | keep s′ = ⊥-elim (clash s′ q′ (≈ᴬ-refl k) (≈ᴬ-refl t))
...   | rise _ | rise _ = sL (λ n → Sψ H gm m gm C.self tm am T w (I um gm _ _ (Sm→S (≪S r) (ch n))))
  where
  ch : ∀ n → Sm (chainᵒ gm (λ z₁ → ψ azero k (hkR H) (h um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n)
                (C.chainᵒ (λ z → C.ψ k (inj₁ (≪⊲ r′)) w (g (C.inS (≪S r′) z))) n)
  ch zero = Sm-Ωat k gm
  ch (suc n) = Sψ (hkR H) gm m gm C.self (⊲-tr (≪⊲ r) am) am (inj₁ (≪⊲ r′)) w (I um gm _ _ (Sm→S (≪S r) (ch n)))
```

## §4 第 0 层

```agda
Sm₀ : ∀ {u} {x : 𝓟 azero u} {y : C.O azero} → Sm x y → (d : G x) → force d ≅ ord y
Sm₀ sz g0 = z≅
Sm₀ (su e) (gs d) = s≅ (Sm₀ e d)
Sm₀ (sL h) (gl Gs st) = l≅ (λ n → Sm₀ (h n) (Gs n))
Sm₀ (sw e) (gw d) = Sm₀ e d
Sm₀ (si {r = ()} I) d
Sm₀ (se {stp = ()} e) d
Sm₀ (sE {R = ()} e) d

T₀≅Y : ∀ a (g : Gw a) → force (G-Tᵖ azero a a tt g C.self) ≅ Y a (lgw g)
T₀≅Y a g = Sm₀ (Sψ (hk₀ tt) g₀ a g (pos g) (z⊲ a) C.self (inj₁ (z⊲ a)) (lgw g) (Sm-Ω a)) (G-Tᵖ azero a a tt g C.self)
```
