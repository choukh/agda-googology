# 加法保持 `⊴`, 对任何定义域

> 不含记号. 结论写在 [DomFold](DomFold.lagda.md). `ad a y`: $a+y$, 对 $y$ 结构递归, 闭包的下界不变. **定理 `WFˢ-ad`, `ad≈`:** 对任何 `Dom`, 无条件, 所以 $\Omega_2\cdot2$ 这样的层号在 `Next` 上有 `WFˢ`. 这是在第 1 层上走到 `bra` 对 `bra` (`bd′` 真的被读) 的第一个带真证书的层号. 转移用帧的来源 (`cov`), 同 [DomFoldNext](DomFoldNext.lagda.md) 的 `emb⊴`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.GuardTightLv using (Dom; module Lv)

module OCF.Align.DomFoldAdd (𝔻 : Dom) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open Lv 𝔻

module Ad (a : LG) where
  ad : LG → LG
  ad zero = a
  ad (suc y) = suc (ad y)
  ad (lim f) = lim (λ n → ad (f n))
  ad (lc c t g) = lc c (ad t) (λ η e → ad (g η e))

  a⊴ : a ≈ a → ∀ y → a ⊴ ad y
  a⊴ sf zero = ≈→⊴ sf
  a⊴ sf (suc y) = ⊴-suc-r (a⊴ sf y)
  a⊴ sf (lim f) = ⊴-lim-r 0 (a⊴ sf (f 0))
  a⊴ sf (lc c t g) = ⊴-fst (a⊴ sf t)

  ad≈ : a ≈ a → ∀ {y y′} → y ≈ y′ → ad y ≈ ad y′
  ad≈ sf z≈ = sf
  ad≈ sf (s≈ e) = s≈ (ad≈ sf e)
  ad≈ sf (l≈ h) = l≈ (λ n → ad≈ sf (h n))
  ad≈ sf (o≈ d e h) = o≈ d (ad≈ sf e) (λ η e₁ η′ e₂ k → ad≈ sf (h η e₁ η′ e₂ k))

  ad< : ∀ {k y} → k < y → ad k < ad y
  ad< zero = zero
  ad< (suc r) = suc (ad< r)
  ad< (lim n r) = lim n (ad< r)
  ad< (fst r) = fst (ad< r)
  ad< (bra η e r) = bra η e (ad< r)

  ad≪ : ∀ {k y} → k ≪ y → ad k ≪ ad y
  ad≪ zero = zero
  ad≪ (suc r) = suc (ad≪ r)
  ad≪ (lim n r) = lim n (ad≪ r)
  ad≪ (fst r) = fst (ad≪ r)

  adC : ∀ {k y} → Cp k y → Cp (ad k) (ad y)
  adC self = self
  adC (suc r) = suc (adC r)
  adC (lim n r) = lim n (adC r)
  adC (fst r) = fst (adC r)
  adC (bra η e r) = bra η e (adC r)

  adCᶠ : ∀ {k y} → Cpᶠ k y → Cpᶠ (ad k) (ad y)
  adCᶠ self = self
  adCᶠ (suc r) = suc (adCᶠ r)
  adCᶠ (lim n r) = lim n (adCᶠ r)
  adCᶠ (fst r) = fst (adCᶠ r)
```

**拉回.** $a+y$ 里的路径: 要么是 $y$ 里路径的像 (`pA`), 要么落在第一份 $a$ 里 (`pB`).

```agda
  data PullA (y : LG) {k : LG} (r : k < ad y) : Set where
    pA : ∀ {k₀} → k ≡ ad k₀ → (q : k₀ < y) → (∀ E → Adm E r → Adm E (ad< q)) → PullA y r
    pB : (s : k < a) → (∀ E → Adm E r → Adm E s) → PullA y r

  pullA : ∀ y {k} (r : k < ad y) → PullA y r
  pullA zero r = pB r (λ _ x → x)
  pullA (suc y) zero = pA refl zero (λ _ _ → tt)
  pullA (suc y) (suc r) with pullA y r
  ... | pA e q u = pA e (suc q) u
  ... | pB s u = pB s u
  pullA (lim f) (lim n r) with pullA (f n) r
  ... | pA e q u = pA e (lim n q) u
  ... | pB s u = pB s u
  pullA (lc c t g) (fst r) with pullA t r
  ... | pA e q u = pA e (fst q) u
  ... | pB s u = pB s u
  pullA (lc c t g) (bra η e′ r) with pullA (g η e′) r
  ... | pA e q u = pA e (bra η e′ q) (λ E x → proj₁ x , u E (proj₂ x))
  ... | pB s u = pB s (λ E x → u E (proj₂ x))

  data PullF (y : LG) {k : LG} (r : k ≪ ad y) : Set where
    fA : ∀ {k₀} → k ≡ ad k₀ → (q : k₀ ≪ y) → PullF y r
    fB : (s : k ≪ a) → PullF y r

  pullF : ∀ y {k} (r : k ≪ ad y) → PullF y r
  pullF zero r = fB r
  pullF (suc y) zero = fA refl zero
  pullF (suc y) (suc r) with pullF y r
  ... | fA e q = fA e (suc q)
  ... | fB s = fB s
  pullF (lim f) (lim n r) with pullF (f n) r
  ... | fA e q = fA e (lim n q)
  ... | fB s = fB s
  pullF (lc c t g) (fst r) with pullF t r
  ... | fA e q = fA e (fst q)
  ... | fB s = fB s

  data PullKf (y : LG) (c′ : D) (t′ : LG) (g′ : (η : D) → c′ ⊑ᴰ η → LG) : Set where
    kA : ∀ {c₀ t₀ g₀} → lc c′ t′ g′ ≈ ad (lc c₀ t₀ g₀) → Cpᶠ (lc c₀ t₀ g₀) y → PullKf y c′ t′ g′
    kB : Cpᶠ (lc c′ t′ g′) a → PullKf y c′ t′ g′

  pullKf : ∀ y {c t g} → Cpᶠ (lc c t g) (ad y) → lc c t g ≈ lc c t g → PullKf y c t g
  pullKf zero Q sf = kB Q
  pullKf (suc y) (suc Q) sf with pullKf y Q sf
  ... | kA e q = kA e (suc q)
  ... | kB s = kB s
  pullKf (lim f) (lim n Q) sf with pullKf (f n) Q sf
  ... | kA e q = kA e (lim n q)
  ... | kB s = kB s
  pullKf (lc c t g) self sf = kA sf self
  pullKf (lc c t g) (fst Q) sf with pullKf t Q sf
  ... | kA e q = kA e (fst q)
  ... | kB s = kB s

  data PullK′ (y : LG) {c′ : D} {t′ : LG} {g′ : (η : D) → c′ ⊑ᴰ η → LG} (p : Cp (lc c′ t′ g′) (ad y)) : Set where
    KA : ∀ {c₀ t₀ g₀} → lc c′ t′ g′ ≈ ad (lc c₀ t₀ g₀) → (q : Cp (lc c₀ t₀ g₀) y) → (∀ E → AdmC E p → AdmC E (adC q)) → PullK′ y p
    KB : (s : Cp (lc c′ t′ g′) a) → (∀ E → AdmC E p → AdmC E s) → PullK′ y p

  pullK′ : ∀ y {c t g} (p : Cp (lc c t g) (ad y)) → lc c t g ≈ lc c t g → PullK′ y p
  pullK′ zero p sf = KB p (λ _ x → x)
  pullK′ (suc y) (suc p) sf with pullK′ y p sf
  ... | KA e q u = KA e (suc q) u
  ... | KB s u = KB s u
  pullK′ (lim f) (lim n p) sf with pullK′ (f n) p sf
  ... | KA e q u = KA e (lim n q) u
  ... | KB s u = KB s u
  pullK′ (lc c t g) self sf = KA sf self (λ _ _ → tt)
  pullK′ (lc c t g) (fst p) sf with pullK′ t p sf
  ... | KA e q u = KA e (fst q) u
  ... | KB s u = KB s u
  pullK′ (lc c t g) (bra η e′ p) sf with pullK′ (g η e′) p sf
  ... | KA e q u = KA e (bra η e′ q) (λ E x → proj₁ x , u E (proj₂ x))
  ... | KB s u = KB s (λ E x → u E (proj₂ x))
```

**转移.** 同 `emb⊴`: 下层的转移对 `cov (帧)` 成立, 搬运后路径的分支值都在原路径上.

```agda
  pFp : ∀ {x y} → x < y → Fl
  pFp zero = tz
  pFp (suc r) = pFp r
  pFp (lim n r) = pFp r
  pFp (fst r) = pFp r
  pFp (bra {c = c} {t = t} {g = g} η e r) = tk (frm c t g η e) ∪ pFp r

  admWk : ∀ {π ρ x y} → Wk π ρ → (r : x < y) → Adm (cov π) r → Adm (cov ρ) r
  admWk w zero _ = tt
  admWk w (suc r) x = admWk w r x
  admWk w (lim n r) x = admWk w r x
  admWk w (fst r) x = admWk w r x
  admWk w (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , x) = (c₁ , t₁ , g₁ , e₁ , w m , k) , admWk w r x

  admPp : ∀ {x y} (r : x < y) → Adm (cov (pFp r)) r
  admPp zero = tt
  admPp (suc r) = admPp r
  admPp (lim n r) = admPp r
  admPp (fst r) = admPp r
  admPp (bra {c = c} {t = t} {g = g} η e r) = (c , t , g , e , ml hr , inj₂ refl) , admWk mr r (admPp r)

  belFr : ∀ E {x y} (q : x < y) → Adm E (ad< q) → ∀ {f} → Mem (pFp q) f → Bel E (ad (κ f)) (fη f)
  belFr E zero u ()
  belFr E (suc q) u m = belFr E q u m
  belFr E (lim n q) u m = belFr E q u m
  belFr E (fst q) u m = belFr E q u m
  belFr E (bra η e q) (b , u) (ml hr) = b
  belFr E (bra η e q) (b , u) (mr m) = belFr E q u m

  belLift : a ≈ a → ∀ E {φ y η} → CovB φ y η → (∀ {f} → Mem φ f → Bel E (ad (κ f)) (fη f)) → Bel E (ad y) η
  belLift sf E (c₁ , t₁ , g₁ , e₁ , m , inj₁ d) H = Bel-resp {E} (ad≈ sf (≈-sym d)) (H m)
  belLift sf E (c₁ , t₁ , g₁ , e₁ , m , inj₂ refl) H = H m

  liftA : a ≈ a → ∀ E {φ k y} (s : k < y) → Adm (cov φ) s → (∀ {f} → Mem φ f → Bel E (ad (κ f)) (fη f)) → Adm E (ad< s)
  liftA sf E zero _ H = tt
  liftA sf E (suc s) x H = liftA sf E s x H
  liftA sf E (lim n s) x H = liftA sf E s x H
  liftA sf E (fst s) x H = liftA sf E s x H
  liftA sf E (bra η e s) (b , x) H = belLift sf E b H , liftA sf E s x H

  pFc : ∀ {x y} → Cp x y → Fl
  pFc self = tz
  pFc (suc r) = pFc r
  pFc (lim n r) = pFc r
  pFc (fst r) = pFc r
  pFc (bra {c = c} {t = t} {g = g} η e r) = tk (frm c t g η e) ∪ pFc r

  admWkC : ∀ {π ρ x y} → Wk π ρ → (r : Cp x y) → AdmC (cov π) r → AdmC (cov ρ) r
  admWkC w self _ = tt
  admWkC w (suc r) x = admWkC w r x
  admWkC w (lim n r) x = admWkC w r x
  admWkC w (fst r) x = admWkC w r x
  admWkC w (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k) , x) = (c₁ , t₁ , g₁ , e₁ , w m , k) , admWkC w r x

  admPc : ∀ {x y} (r : Cp x y) → AdmC (cov (pFc r)) r
  admPc self = tt
  admPc (suc r) = admPc r
  admPc (lim n r) = admPc r
  admPc (fst r) = admPc r
  admPc (bra {c = c} {t = t} {g = g} η e r) = (c , t , g , e , ml hr , inj₂ refl) , admWkC mr r (admPc r)

  belFrC : ∀ E {x y} (q : Cp x y) → AdmC E (adC q) → ∀ {f} → Mem (pFc q) f → Bel E (ad (κ f)) (fη f)
  belFrC E self u ()
  belFrC E (suc q) u m = belFrC E q u m
  belFrC E (lim n q) u m = belFrC E q u m
  belFrC E (fst q) u m = belFrC E q u m
  belFrC E (bra η e q) (b , u) (ml hr) = b
  belFrC E (bra η e q) (b , u) (mr m) = belFrC E q u m

  liftC : a ≈ a → ∀ E {φ k y} (s : Cp k y) → AdmC (cov φ) s → (∀ {f} → Mem φ f → Bel E (ad (κ f)) (fη f)) → AdmC E (adC s)
  liftC sf E self _ H = tt
  liftC sf E (suc s) x H = liftC sf E s x H
  liftC sf E (lim n s) x H = liftC sf E s x H
  liftC sf E (fst s) x H = liftC sf E s x H
  liftC sf E (bra η e s) (b , x) H = belLift sf E b H , liftC sf E s x H

  selfCp : ∀ {x y} → y ≈ y → Cp x y → x ≈ x
  selfCp e self = e
  selfCp (s≈ e) (suc p) = selfCp e p
  selfCp (l≈ h) (lim n p) = selfCp (h n) p
  selfCp (o≈ d e h) (fst p) = selfCp e p
  selfCp (o≈ d e h) (bra η e₁ p) = selfCp (h η e₁ η e₁ (≅ᴰ-refl η)) p

  selfCpᶠ : ∀ {x y} → y ≈ y → Cpᶠ x y → x ≈ x
  selfCpᶠ e self = e
  selfCpᶠ (s≈ e) (suc p) = selfCpᶠ e p
  selfCpᶠ (l≈ h) (lim n p) = selfCpᶠ (h n) p
  selfCpᶠ (o≈ d e h) (fst p) = selfCpᶠ e p

  ad⊴ : a ≈ a → ∀ {y y′} → y ≈ y → y ⊴ y′ → ad y ⊴ ad y′
  ad⊴ sf {y} {y′} sy x = ⊴i pp ff kk KK
    where
    up = a⊴ sf y′
    pp : ad y ⊑ ad y′
    pp r with pullA y r
    ... | pA refl q u with ⊴p x q
    ...   | viaᴸ d s t = viaᴸ (ad≈ sf d) (ad< s) (λ E A → liftA sf E s (t (cov (pFp q)) (admPp q)) (belFr E q (u E A)))
    pp r | pB s u with ⊴p up s
    ...   | viaᴸ d s′ t = viaᴸ d s′ (λ E A → t E (u E A))
    ff : ad y ⊑ᶠ ad y′
    ff r with pullF y r
    ... | fA refl q with ⊴f x q
    ...   | preᶠ d p = preᶠ (ad≈ sf d) (ad≪ p)
    ff r | fB s = ⊴f up s
    kk : ad y ⊑ᵏ ad y′
    kk Q with pullKf y Q (selfCpᶠ (ad≈ sf sy) Q)
    ... | kA e q with ⊴k x q
    ...   | viaᵏ d p = viaᵏ (≈-trans e (ad≈ sf d)) (adCᶠ p)
    kk Q | kB s = ⊴k up s
    KK : ad y ⊑ᴷ ad y′
    KK Q with pullK′ y Q (selfCp (ad≈ sf sy) Q)
    ... | KA e q u with ⊴K x q
    ...   | viaᴷ d p t = viaᴷ (≈-trans e (ad≈ sf d)) (adC p) (λ E A → liftC sf E p (t (cov (pFc q)) (admPc q)) (belFrC E q (u E A)))
    KK Q | KB s u with ⊴K up s
    ...   | viaᴷ d p t = viaᴷ d p (λ E A → t E (u E A))

  WFˢ-ad : WFˢ a → a ≈ a → ∀ y → WFˢ y → y ≈ y → WFˢ (ad y)
  WFˢ-ad wa sf zero w sy = wa
  WFˢ-ad wa sf (suc y) w (s≈ sy) = WFˢ-ad wa sf y w sy
  WFˢ-ad wa sf (lim f) (st , w) (l≈ sy) = (λ n → ad⊴ sf (sy n) (st n)) , (λ n → WFˢ-ad wa sf (f n) (w n) (sy n))
  WFˢ-ad wa sf (lc c t g) (tg , dir , wt , wg) (o≈ d se sh) =
    (λ η e → ad⊴ sf se (tg η e)) ,
    (λ η e η′ e′ k → ad⊴ sf (sh η e η e (≅ᴰ-refl η)) (dir η e η′ e′ k)) ,
    WFˢ-ad wa sf t wt se ,
    (λ η e → WFˢ-ad wa sf (g η e) (wg η e) (sh η e η e (≅ᴰ-refl η)))
```
