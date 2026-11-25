# 比 Le 宽的底关系: 左边放宽
不读记号；工具。关系 `WS` 在 `YiVRRel.LeS` 上加一条左规则 `Ω≼`: Ω 结点的每个分支都在右边之下, 结点就在右边之下 (题设 "分支被极限链某项支配" 是它的特例, `chain≼`)。遗传版 `W` (分支关系也是 `W`) 与沿用 Le 分支关系的版本 `Wᴸ`。
编译定理：`Le ⊆ Wᴸ` (`le→wᴸ`)；第 0 层 `W` 推出值序 (`w→v₀`)，不以值序作前提；`Wᴸ` 严格宽于 `Le` (`wide`, `narrow`)。遗传版 `W` 的分支关系在反变位置, 是否包含 `Le` 未判定。
不否定什么；在实际前缀 2 的底上的否定在 [YiWBNeg](YiWBNeg.lagda.md)。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWBRel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiVRRel as R
import OCF.Lean.YiVWVal as V
```

## 一层之内

与 `R.LeS` 逐条相同, 多一条 `Ω≼`。

```agda
data WS (S : Sg) (RB : (p : P S) → B S p → B S p → Set) (RD : (c : C S) → D S c → D S c → Set)
     : T S → T S → Set where
  z≼  : ∀ {b} → WS S RB RD zero b
  s≼s : ∀ {a b} → WS S RB RD a b → WS S RB RD (suc a) (suc b)
  ≼s  : ∀ {a b} → WS S RB RD a b → WS S RB RD a (suc b)
  ≼l  : ∀ {a f r} (n : ℕ) → WS S RB RD a (f n) → WS S RB RD a (lim f r)
  l≼  : ∀ {f r b} → ((n : ℕ) → WS S RB RD (f n) b) → WS S RB RD (lim f r) b
  ≼w  : ∀ {a p g} → WS S RB RD a (g (b₀ S p)) → WS S RB RD a (Ω p g)
  w≼w : ∀ {p g g′} → ((z z′ : B S p) → RB p z z′ → WS S RB RD (g z) (g′ z′)) → WS S RB RD (Ω p g) (Ω p g′)
  Ω≼  : ∀ {p g b} → ((z : B S p) → WS S RB RD (g z) b) → WS S RB RD (Ω p g) b
  ≼u  : ∀ {a x c y e} → WS S RB RD a x → WS S RB RD a (up x c y e)
  u≼u : ∀ {x x′ c y y′ e e′} → WS S RB RD x x′ → RD c y y′ → WS S RB RD (up x c y e) (up x′ c y′ e′)

chain≼ : ∀ {S RB RD p g f r} → ((z : B S p) → Σ ℕ λ n → WS S RB RD (g z) (f n)) → WS S RB RD (Ω p g) (lim f r)
chain≼ h = Ω≼ (λ z → ≼l (proj₁ (h z)) (proj₂ (h z)))
```

## 各层: 遗传版与沿用 Le 分支关系的版本

遗传版是爬升要的那一个 (底只按 `W` 相关时, 回灌出来的分支也只按 `W` 相关)。

```agda
mutual
  WB : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Br ℓ p → Set
  WB (nd s h)      (inj₂ (c , t)) = WB⁼ (h c) t
  WB (nd (sΩ k) h) (inj₁ t)       = WB⁼ k t

  WB⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Br⁼ a t → Set
  WB⁼ a (inj₁ _) = WS (Sig a) (WB a) (WC a)
  WB⁼ a (inj₂ p) = WB a p

  WC : (ℓ : L) (c : CH ℓ) → ChT ℓ c → ChT ℓ c → Set
  WC (nd s h) c = WS (Sig (h c)) (WB (h c)) (WC (h c))

W : (ℓ : L) → Tr ℓ → Tr ℓ → Set
W ℓ = WS (Sig ℓ) (WB ℓ) (WC ℓ)

mutual
  WCᴸ : (ℓ : L) (c : CH ℓ) → ChT ℓ c → ChT ℓ c → Set
  WCᴸ (nd s h) c = Wᴸ (h c)

  Wᴸ : (ℓ : L) → Tr ℓ → Tr ℓ → Set
  Wᴸ ℓ = WS (Sig ℓ) (R.LB ℓ) (WCᴸ ℓ)
```

## 与 Le 的关系

分支关系不变时, `LeS` 的推导逐条搬过来; 孩子树上的关系沿层号递归。

```agda
mapLW : ∀ {S RB RD} {RD′ : (c : C S) → D S c → D S c → Set}
      → (∀ c {y y′} → RD c y y′ → RD′ c y y′)
      → ∀ {x y} → R.LeS S RB RD x y → WS S RB RD′ x y
mapLW fd R.z≼ = z≼
mapLW fd (R.s≼s d) = s≼s (mapLW fd d)
mapLW fd (R.≼s d) = ≼s (mapLW fd d)
mapLW fd (R.≼l n d) = ≼l n (mapLW fd d)
mapLW fd (R.l≼ h) = l≼ (λ n → mapLW fd (h n))
mapLW fd (R.≼w d) = ≼w (mapLW fd d)
mapLW fd (R.w≼w h) = w≼w (λ z z′ r → mapLW fd (h z z′ r))
mapLW fd (R.≼u d) = ≼u (mapLW fd d)
mapLW fd (R.u≼u {c = c} d r) = u≼u (mapLW fd d) (fd c r)

mutual
  le→wᴸ : (ℓ : L) {x y : Tr ℓ} → R.Le ℓ x y → Wᴸ ℓ x y
  le→wᴸ ℓ = mapLW (lc→wc ℓ)

  lc→wc : (ℓ : L) (c : CH ℓ) {y y′ : ChT ℓ c} → R.LC ℓ c y y′ → WCᴸ ℓ c y y′
  lc→wc (nd s h) c = le→wᴸ (h c)
```

严格更宽: 第 1 层上分支全为零的 Ω 结点在 1 之下, `Le` 没有这一条。

```agda
L1 : L
L1 = nd sS (λ _ → zero)

s₀ : Pos L1
s₀ = inj₂ (tt , inj₁ tt)

wide : W L1 (Ω s₀ (λ _ → zero)) (suc zero)
wide = Ω≼ (λ _ → z≼)

wideᴸ : Wᴸ L1 (Ω s₀ (λ _ → zero)) (suc zero)
wideᴸ = Ω≼ (λ _ → z≼)

narrow : R.Le L1 (Ω s₀ (λ _ → zero)) (suc zero) → ⊥
narrow (R.≼s ())
```

## 第 0 层: 推出值序

第 0 层没有槽位与孩子, 分支关系与孩子关系任取。

```agda
w→v₀ : ∀ {RB RD} {x y : Tr zero} → WS (Sig zero) RB RD x y → V.val zero x V.≼ V.val zero y
w→v₀ z≼ = V.z≼
w→v₀ (s≼s d) = V.s≼s (w→v₀ d)
w→v₀ (≼s d) = V.≼-suc (w→v₀ d)
w→v₀ (≼l n d) = V.≼l n (w→v₀ d)
w→v₀ (l≼ h) = V.l≼ (λ n → w→v₀ (h n))
w→v₀ (≼w {p = ()} d)
w→v₀ (w≼w {p = ()} h)
w→v₀ (Ω≼ {p = ()} h)
w→v₀ (≼u {c = ()} d)
w→v₀ (u≼u {c = ()} dx dy)

wrefl₀ : (z : Tr zero) → W zero z z
wrefl₀ zero = z≼
wrefl₀ (suc z) = s≼s (wrefl₀ z)
wrefl₀ (lim f a) = l≼ (λ n → ≼l n (wrefl₀ (f n)))
```
