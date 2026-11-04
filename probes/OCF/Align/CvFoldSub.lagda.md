# 折叠输出与 `Cv` (一): 和对加数的值同余

> 不含记号. 入口 [CvFold](CvFold.lagda.md). `S q l b y` ($b+y$, [LayerTrOne](LayerTrOne.lagda.md)) 的值只依赖 $b$ 的值与 $0+y$ 的值:
>
> - `Sub b t t′`: $t'$ 是把 $t$ 的底 $0$ (及其抬升) 换成 $b$ 的树. `Sub-S`: `S` 保持它, 对一切第 1 层差树 (含 `ni`, `nκ`, 任意世界).
> - `Sub-mono`: `Sub` 两边的 $\preccurlyeq$ 搬过去. 只要被比较的右边所在世界合法.
> - **`S-congʸ`**: $0+y\preccurlyeq 0+y'$ (同一世界) 推出 $b+y\preccurlyeq b+y'$.
> - `Cv⁰`, `Cv⁰→Cv`: 所以 `LayerTrRound.Cv` 只要对 $0$ 为底验, 即分支的值 (`toB` 的值) 对规范坐标不变.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CvFoldSub where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; z⊲; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; tailP)
open import OCF.Align.BrwMidZero using (dif)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne
open import OCF.Align.LayerTrRound using (Cv; cw)
```

## §1 换底

```agda
data Sub {W} (b : B₁ W) : ∀ {V} → B₁ V → B₁ V → Set where
  sz : Sub b bz b
  ss′ : ∀ {V} {t t′ : B₁ V} → Sub b t t′ → Sub b (bs t) (bs t′)
  sl : ∀ {V} {f g : ℕ → B₁ V} → (∀ n → Sub b (f n) (g n)) → Sub b (bl f) (bl g)
  si : ∀ {V} {f g : ∀ {V′} → V ⊲ V′ → Lg V′ → (y : A) → Lg y → B₁ V′} →
       (∀ {V′} p l y ly → Sub b (f {V′} p l y ly) (g p l y ly)) → Sub b (bi f) (bi g)
  sκ : ∀ {V} {f g : ∀ {c} → V ⊲ c → Lg c → B₁ c} → (∀ {c} p l → Sub b (f {c} p l) (g p l)) → Sub b (bκ f) (bκ g)
  sw : ∀ {V₀ V} {p : V₀ ⊲ V} {t t′ : B₁ V₀} → Sub b t t′ → Sub b (bw p t) (bw p t′)
```

## §2 `S` 保持换底

```agda
Sub-I  : ∀ {W W₀ V} {b : B₁ W} (e e′ : D azero V → B₁ V → B₁ V) → (∀ w {c c′} → Sub b c c′ → Sub b (e w c) (e′ w c′)) →
         (z : D azero W₀) (q : W₀ ⊲ V) → ∀ w {c c′} → Sub b c c′ → Sub b (I e z q w c) (I e′ z q w c′)
Sub-Ip : ∀ {W W₀ V} {b : B₁ W} (e e′ : D azero V → B₁ V → B₁ V) → (∀ w {c c′} → Sub b c c′ → Sub b (e w c) (e′ w c′)) →
         (d : ℕ → D azero W₀) (q : W₀ ⊲ V) → ∀ w {c c′} → Sub b c c′ → ∀ n → Sub b (Ip e d q w c n) (Ip e′ d q w c′ n)
Sub-I e e′ h n0 q w s = s
Sub-I e e′ h n1 q w s = h w s
Sub-I e e′ h (x ⨾ y) q w s = Sub-I e e′ h y q _ (Sub-I e e′ h x q w s)
Sub-I e e′ h (nl d) q w s = sl (Sub-Ip e e′ h d q w s)
Sub-I e e′ h (ni () u) q w s
Sub-I e e′ h (nκ () u) q w s
Sub-I e e′ h (nw p x) q w s = Sub-I e e′ h x (⊲-tr p q) w s
Sub-Ip e e′ h d q w s zero = s
Sub-Ip e e′ h d q w s (suc n) = Sub-I e e′ h (d n) q _ (Sub-Ip e e′ h d q w s n)

Sub-S  : ∀ {W W₀ V} {b : B₁ W} (q : W₀ ⊲ V) (l : Lg V) (y : D one W₀) {t t′ : B₁ V} → Sub b t t′ → Sub b (S q l t y) (S q l t′ y)
Sub-Sp : ∀ {W W₀ V} {b : B₁ W} (q : W₀ ⊲ V) (l : Lg V) (d : ℕ → D one W₀) {t t′ : B₁ V} → Sub b t t′ → ∀ n → Sub b (Sp q l t d n) (Sp q l t′ d n)
Sub-K  : ∀ {W W₀} {b : B₁ W} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) c {a} (p : a ⊲ c) (aW : W₀ ⊲ a) (lc : Lg c) {t t′ : B₁ a} →
         Sub b t t′ → Sub b (K u c p aW lc t) (K u c p aW lc t′)
Sub-KR : ∀ {W W₀} {b : B₁ W} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) →
         ∀ {a n} (p : a ⊲ f n) (aW : W₀ ⊲ a) {t t′ : B₁ a} → Sub b t t′ → ∀ m → Sub b (KR u f st wl p aW t m) (KR u f st wl p aW t′ m)
Sub-S q l n0 s = s
Sub-S q l n1 s = ss′ s
Sub-S q l (x ⨾ y) s = Sub-S q l y (Sub-S q l x s)
Sub-S q l (nl d) s = sl (Sub-Sp q l d s)
Sub-S q l (ni (ss C.self) u) s =
  si (λ p l′ y ly → Sub-I _ _ (λ w s′ → Sub-S C.self l′ (u (⊲-tr q p) l′ w) s′) (dif y (z⊲ y) ly) C.self n0 (sw s))
Sub-S q l (nκ zz u) s = sκ (λ p lc → Sub-S C.self lc (u (⊲-tr q p) lc) (Sub-K u _ p q lc s))
Sub-S q l (nw p x) s = Sub-S (⊲-tr p q) l x s
Sub-Sp q l d s zero = s
Sub-Sp q l d s (suc n) = Sub-S q l (d n) (Sub-Sp q l d s n)
Sub-K u c C.self aW lc s = s
Sub-K u (asuc c) (C.suc p) aW lc s = sw (Sub-S C.self lc (u (⊲-tr aW p) lc) (Sub-K u c p aW lc s))
Sub-K u (alim f) (C.lim n p) aW (st , wl) s = sl (λ m → sw (Sub-KR u f st wl p aW s m))
Sub-KR u f st wl p aW s zero = Sub-K u (f _) p aW (wl _) s
Sub-KR u f st wl {n = n} p aW s (suc m) =
  Sub-K u (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) (Sub-KR u f st wl p aW s m)
```

## §3 换底保持 $\preccurlyeq$

```agda
≼-suc : ∀ {W W′} {a : B₁ W} {b : B₁ W′} → a ≼ b → a ≼ bs b
≼-suc z≼ = z≼
≼-suc (s≼s p) = s≼s (≼-suc p)
≼-suc (≼l {f = f} n p) = ≼-trans (≼-suc p) (s≼s (≼l n (≼-refl (f n))))
≼-suc (l≼ p) = l≼ (λ n → ≼-suc (p n))
≼-suc (≼i {f = f} r l y ly p) = ≼-trans (≼-suc p) (s≼s (≼i r l y ly (≼-refl (f r l y ly))))
≼-suc (i≼ p) = i≼ (λ r l y ly → ≼-suc (p r l y ly))
≼-suc (≼κ {g = g} r l p) = ≼-trans (≼-suc p) (s≼s (≼κ r l (≼-refl (g r l))))
≼-suc (κ≼ p) = κ≼ (λ r l → ≼-suc (p r l))
≼-suc (≼w {b = b} p) = ≼-trans (≼-suc p) (s≼s (≼w (≼-refl b)))
≼-suc (w≼ p) = w≼ (≼-suc p)

-- 底在换过的树之下
base≼ : ∀ {W V} {b : B₁ W} {u u′ : B₁ V} → Sub b u u′ → Lg V → b ≼ u′
base≼ sz l = ≼-refl _
base≼ (ss′ s) l = ≼-suc (base≼ s l)
base≼ (sl h) l = ≼l 0 (base≼ (h 0) l)
base≼ (si h) l = ≼i C.self l azero tt (base≼ (h C.self l azero tt) l)
base≼ (sκ h) l = ≼κ C.self l (base≼ (h C.self l) l)
base≼ (sw {p = p} s) l = ≼w (base≼ s (lg⊲ p l))

Sub-mono : ∀ {W V V′} {b : B₁ W} {t t′ : B₁ V} {u u′ : B₁ V′} → Sub b t t′ → Sub b u u′ → Lg V′ → t ≼ u → t′ ≼ u′
Sub-mono sz su l z≼ = base≼ su l
Sub-mono st (sl h) l (≼l n p) = ≼l n (Sub-mono st (h n) l p)
Sub-mono st (si h) l (≼i r l′ y ly p) = ≼i r l′ y ly (Sub-mono st (h r l′ y ly) l′ p)
Sub-mono st (sκ h) l (≼κ r l′ p) = ≼κ r l′ (Sub-mono st (h r l′) l′ p)
Sub-mono st (sw {p = r} s) l (≼w p) = ≼w (Sub-mono st s (lg⊲ r l) p)
Sub-mono (sl h) su l (l≼ p) = l≼ (λ n → Sub-mono (h n) su l (p n))
Sub-mono (si h) su l (i≼ p) = i≼ (λ r l′ y ly → Sub-mono (h r l′ y ly) su l (p r l′ y ly))
Sub-mono (sκ h) su l (κ≼ p) = κ≼ (λ r l′ → Sub-mono (h r l′) su l (p r l′))
Sub-mono (sw s) su l (w≼ p) = w≼ (Sub-mono s su l p)
Sub-mono (ss′ s) (ss′ s′) l (s≼s p) = s≼s (Sub-mono s s′ l p)
```

## §4 结论

```agda
S-congʸ : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (b : B₁ W) (y y′ : D one W₀) → S q l bz y ≼ S q l bz y′ → S q l b y ≼ S q l b y′
S-congʸ q l b y y′ h = Sub-mono (Sub-S q l y sz) (Sub-S q l y′ sz) l h

S-congʸ≈ : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (b : B₁ W) (y y′ : D one W₀) → S q l bz y ≈ S q l bz y′ → S q l b y ≈ S q l b y′
S-congʸ≈ q l b y y′ (h , h′) = S-congʸ q l b y y′ h , S-congʸ q l b y′ y h′

-- 只对底 0 验的 Cv
Cv⁰ : ∀ {W} → D one W → Set
Cv⁰ n0 = ⊤
Cv⁰ n1 = ⊤
Cv⁰ (x ⨾ y) = Cv⁰ x × Cv⁰ y
Cv⁰ (nl d) = ∀ n → Cv⁰ (d n)
Cv⁰ (ni (ss C.self) u) = ∀ {W′} p l w → Cv⁰ (u {W′} p l w) × (S C.self l bz (u p l (cw w)) ≈ S C.self l bz (u p l w))
Cv⁰ (nκ zz u) = ⊤
Cv⁰ (nw p x) = Cv⁰ x

Cv⁰→Cv : ∀ {W} (x : D one W) → Cv⁰ x → Cv x
Cv⁰→Cv n0 c = tt
Cv⁰→Cv n1 c = tt
Cv⁰→Cv (x ⨾ y) (c , c′) = Cv⁰→Cv x c , Cv⁰→Cv y c′
Cv⁰→Cv (nl d) c = λ n → Cv⁰→Cv (d n) (c n)
Cv⁰→Cv (ni (ss C.self) u) c = λ p l w →
  Cv⁰→Cv (u p l w) (proj₁ (c p l w)) , (λ b → S-congʸ≈ C.self l b (u p l (cw w)) (u p l w) (proj₂ (c p l w)))
Cv⁰→Cv (nκ zz u) c = tt
Cv⁰→Cv (nw p x) c = Cv⁰→Cv x c
```
