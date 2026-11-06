# Third (三): 洗法的实例 `Er`

> 不含记号. 入口 [Third](Third.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **实例.** `sf m κ`: 按种类的结构 (不读坐标, 不比较) 看它是否穿过高度的 $\Omega$-结点. 没穿过的种类在一切世界里有位置, 留下; 穿过的结点**整个换成 $0$** (`san`). 地板 `tpS`: 穿过 $\Omega$-结点时取 `bot` 分量 (位置由 `botBd`, 与世界无关). 否定一路 `NegThirdIf.no-wash` 说保根种类的洗法推出 LPO; 这里换根种类, 不在它的范围内. 代价 (判断): 留下的结点的坐标里, 穿过 $\Omega$-分量的种类都丢了 (§ 见入口的读法).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase
module OCF.Lean.ThirdSan (U : KS) (w : Wd U) (lw : LgW U w) (fb : HB U) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdPS
open import OCF.Lean.ThirdFold U w lw

sf : ∀ m κ → Pos U w m κ ⊎ ⊤
sf hz κ = inj₁ tt
sf (hs x) (inj₁ κ) = sf x κ
sf (hs x) (inj₂ _) = inj₁ tt
sf (hl f) (n , κ) = sf (f n) κ
sf (hΩ κ₀ g) _ = inj₂ tt

san : ∀ m → HB (T m) → HB (T m)
sN : ∀ m κ (g : E (T m) κ → HB (T m)) → Pos U w m κ ⊎ ⊤ → HB (T m)
san m hz = hz
san m (hs x) = hs (san m x)
san m (hl f) = hl (λ n → san m (f n))
san m (hΩ κ g) = sN m κ g (sf m κ)
sN m κ g (inj₁ p) = hΩ κ (λ e → san m (g e))
sN m κ g (inj₂ _) = hz

gd-san : ∀ m c → Gd m (san m c)
gN : ∀ m κ (g : E (T m) κ → HB (T m)) r → Gd m (sN m κ g r)
gd-san m hz = tt
gd-san m (hs x) = gd-san m x
gd-san m (hl f) = λ n → gd-san m (f n)
gd-san m (hΩ κ g) = gN m κ g (sf m κ)
gN m κ g (inj₁ p) = p , λ e _ → gd-san m (g e)
gN m κ g (inj₂ _) = tt

gd-z : ∀ h → Gd hz h
gd-z hz = tt
gd-z (hs h) = gd-z h
gd-z (hl f) = λ n → gd-z (f n)
gd-z (hΩ κ g) = tt , λ e _ → gd-z (g e)

Gd-up : ∀ x e → Gd x e → Gd (hs x) (up e)
Gd-up x hz p = tt
Gd-up x (hs e) p = Gd-up x e p
Gd-up x (hl f) p = λ n → Gd-up x (f n) (p n)
Gd-up x (hΩ κ g) (ev , p) = ev , λ e a → Gd-up x (g e) (p e a)

Gd-ιL : ∀ f n c → Gd (f n) c → Gd (hl f) (ι {ℕ} {λ n → T (f n)} n c)
Gd-ιL f n hz p = tt
Gd-ιL f n (hs c) p = Gd-ιL f n c p
Gd-ιL f n (hl h) p = λ k → Gd-ιL f n (h k) (p k)
Gd-ιL f n (hΩ κ g) (ev , p) = ev , λ e a → Gd-ιL f n (g e) (p e a)

Gd-ιO : ∀ κ₀ g c → Gd (g (bot U κ₀)) c → Gd (hΩ κ₀ g) (ι {E U κ₀} {λ e → T (g e)} (bot U κ₀) c)
Gd-ιO κ₀ g hz p = tt
Gd-ιO κ₀ g (hs c) p = Gd-ιO κ₀ g c p
Gd-ιO κ₀ g (hl h) p = λ k → Gd-ιO κ₀ g (h k) (p k)
Gd-ιO κ₀ g (hΩ κ h) (ev , p) = (botBd U κ₀ w , ev) , λ e a → Gd-ιO κ₀ g (h e) (p e a)

tpS : ∀ m → HB (T m)
ΣS : (f : ℕ → HB U) → ℕ → HB (T (hl f))
tpS hz = fb
tpS (hs x) = hΩ (inj₂ tt) (λ c → up (san x c))
tpS (hl f) = hl (ΣS f)
tpS (hΩ κ g) = ι {E U κ} {λ e → T (g e)} (bot U κ) (tpS (g (bot U κ)))
ΣS f zero = ι 0 (tpS (f 0))
ΣS f (suc n) = ΣS f n ⊞ ι (suc n) (tpS (f (suc n)))

gd-tp : ∀ m → Gd m (tpS m)
gd-ΣS : ∀ f n → Gd (hl f) (ΣS f n)
gd-tp hz = gd-z fb
gd-tp (hs x) = tt , λ c _ → Gd-up x (san x c) (gd-san x c)
gd-tp (hl f) = gd-ΣS f
gd-tp (hΩ κ g) = Gd-ιO κ g (tpS (g (bot U κ))) (gd-tp (g (bot U κ)))
gd-ΣS f zero = Gd-ιL f 0 _ (gd-tp (f 0))
gd-ΣS f (suc n) = Gd-⊞ (ΣS f n) _ (gd-ΣS f n) (Gd-ιL f (suc n) _ (gd-tp (f (suc n))))

Er : San
Er = record { san = san ; gd-san = gd-san ; tp = tpS ; gd-tp = gd-tp }

module Ph {P : Po} (Q : PS P U) (O : Po.W P → Set) (ptl : ∀ B → O B → PH Q B fb) where
  L = PSL Q

  ph-san : ∀ j {V} c → PH (L j) V c → PH (L j) V (san j c)
  pN : ∀ j {V} κ g r → PH (L j) V (hΩ κ g) → PH (L j) V (sN j κ g r)
  ph-san j hz p = tt
  ph-san j (hs c) p = ph-san j c p
  ph-san j (hl f) p = λ n → ph-san j (f n) (p n)
  ph-san j (hΩ κ g) p = pN j κ g (sf j κ) p
  pN j κ g (inj₁ q) (ev , p) = ev , λ e a → ph-san j (g e) (p e a)
  pN j κ g (inj₂ _) p = tt

  ph-tp : ∀ j V → O V → PH (L j) V (tpS j)
  ph-ΣS : ∀ f V → O V → ∀ n → PH (L (hl f)) V (ΣS f n)
  ph-tp hz V o = ptl V o
  ph-tp (hs x) V o = tt , λ c a → PH-up (L x) (san x c) (ph-san x c (proj₂ (proj₂ a)))
  ph-tp (hl f) V o = ph-ΣS f V o
  ph-tp (hΩ κ g) V o = PH-ι (λ e → L (g e)) (bot U κ) _ (ph-tp (g (bot U κ)) V o)
  ph-ΣS f V o zero = PH-ι (λ n → L (f n)) 0 _ (ph-tp (f 0) V o)
  ph-ΣS f V o (suc n) = PH-⊞ (L (hl f)) (ΣS f n) _ (ph-ΣS f V o n) (PH-ι (λ k → L (f k)) (suc n) _ (ph-tp (f (suc n)) V o))
```
