# 跨段, 下一步 (二): 两条修法的通用形式

> 入口 [CrossNext](CrossNext.lagda.md). **判决: HOLDS (编译过, 无条件), 都是对任意分支族的定理, 不看塔.** 这是 [CrossM](CrossM.lagda.md) 报告的障碍 (b) 的两条修法.
>
> - **修法一, 链上带码 (`Along`).** 分支对一切码给出, 链是 `Node` 的累加链 `C`, 字面的公共上界由链写出. 单调性由分支族自己给 (`u`). 输出是 `Z.lim`. 换一族同值的分支, 值不变 (`T̂≅`).
> - **修法二, 分支字面地加上上一个输出 (`Sum`).** 对 **任何** 分支族 `b : Ordᴵ → Z`, 只要每支有证书, `ĉᴸ zero t₀ S t₀ S` 就有已有的 `Goodᴺ`, 不要任何单调性, $S\,\eta=(\hat\eta+1)\oplus b\,\eta$. 没有新构造子. 这个定理本身就说明代价: 它对任何 `b` 成立, 所以这个闭包点的单调性不再是关于 `b` 的信息, 输出的基本列每一项都顶着上一个输出.
> - **修法三, 链带前缀, 输出不带 (`Sum.Out`).** 链的生成器是 `S`, 输出是另一族 `o`. 单调性要自己证 (`step`), 由 `lvG-path` 帮忙: 带前缀时下一个高度的码以上一个高度的码为字面初始段, 差一个 `≋` (`ofZ-≋`). 输出的基本列没有前缀, 前缀留在高度上.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossNextSum where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; outsᴺ)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos using (Code; cs; cz)
open import OCF.Align.LadderOrdCode using (_ᶜ+_; ⌈_⌉; _≼_; z≼; s≼; s≼ʳ; l≼; l≼ʳ; ≼-trans; ≼-refl)
open import OCF.Align.CrossMUp using (_⊂_; ⊂r; es; el)
open import OCF.Align.CrossNextEq using (_≋_; cz≋; cs≋; cl≋)
open import OCF.Align.CrossMUpTree using (≺-≅ˡ)
open import OCF.Align.CrossMNode using (≺-trans; ≺→⊑; Node; node; br; Gbr; yv; C; νT)
```

## §1 修法一: 沿累加链

```agda
module Along (𝒩 : Node) (b : Code → Z) (G : ∀ M → Goodᴺ (b M))
  (u : ∀ M N → forceᴺ _ (G M) ⊑⁰ forceᴺ _ (G (M ᶜ+ cs N)))
  (h : ∀ M → yv 𝒩 M ≅ forceᴺ _ (G M)) (M₀ : Code) where

  Ĉ : ℕ → Code
  Ĉ = C 𝒩 M₀

  Ẑ : Z
  Ẑ = Z.lim (λ n → b (Ĉ n))

  Ĝ : Goodᴺ Ẑ
  Ĝ = gl (λ n → G (Ĉ n)) (λ n → u (Ĉ n) _)

  T̂ : Ordᶜ zero
  T̂ = forceᴺ _ Ĝ

  ĤS : HS T̂
  ĤS = forceᴺ-HS _ Ĝ

  T̂≅ : νT 𝒩 M₀ ≅ T̂
  T̂≅ = l≅ (λ n → h (Ĉ n))
```

## §2 序数值的和

```agda
infixl 6 _⊕_
_⊕_ : Ordᶜ zero → Ordᶜ zero → Ordᶜ zero
a ⊕ zero = a
a ⊕ suc x = suc (a ⊕ x)
a ⊕ lim f = lim (λ n → a ⊕ f n)
a ⊕ limᵢ () f
a ⊕ up () x

⊕-≅ʳ : ∀ a {x y} → x ≅ y → a ⊕ x ≅ a ⊕ y
⊕-≅ʳ a z≅ = ≅-refl⁰ a
⊕-≅ʳ a (s≅ e) = s≅ (⊕-≅ʳ a e)
⊕-≅ʳ a (l≅ h) = l≅ (λ n → ⊕-≅ʳ a (h n))
⊕-≅ʳ a (lᵢ≅ {p = ()} e h)
⊕-≅ʳ a (upˡ {r = ()} e)
⊕-≅ʳ a (upʳ {r = ()} e)

⊕-≺ : ∀ a {x y : Ordᶜ zero} → x ≺ y → a ⊕ x ≺ a ⊕ y
⊕-≺ a (≺z e) = ≺z (⊕-≅ʳ a e)
⊕-≺ a (≺s r) = ≺s (⊕-≺ a r)
⊕-≺ a (≺l n r) = ≺l n (⊕-≺ a r)
⊕-≺ a (≺i {p = ()} x ex r)
⊕-≺ a (≺u {r = ()} r)

⊑⊕ : ∀ a y → a ⊑⁰ a ⊕ y
⊑⊕ a zero h = h
⊑⊕ a (suc y) h = ≺s (⊑⊕ a y h)
⊑⊕ a (lim f) h = ≺l 0 (⊑⊕ a (f 0) h)
⊑⊕ a (limᵢ () f) h
⊑⊕ a (up () x) h

⊕-⊑ʳ : ∀ a x y → x ⊑⁰ y → a ⊕ x ⊑⁰ a ⊕ y
⊕-⊑ʳ a zero y k h = ⊑⊕ a y h
⊕-⊑ʳ a (suc x) y k (≺z e) = ≺-≅ˡ e (⊕-≺ a (k (≺z (≅-refl⁰ x))))
⊕-⊑ʳ a (suc x) y k (≺s r) = ≺-trans r (⊕-≺ a (k (≺z (≅-refl⁰ x))))
⊕-⊑ʳ a (lim f) y k (≺l n r) = ⊕-⊑ʳ a (f n) y (λ q → k (≺l n q)) r
⊕-⊑ʳ a (limᵢ () f) y k h
⊕-⊑ʳ a (up () x) y k h

w≼-suc : ∀ a y → a ≺ suc a ⊕ y
w≼-suc a y = ⊑⊕ (suc a) y (≺z (≅-refl⁰ a))
```

## §3 `Z` 上的和

`ĉᴸ` 的链不动, 只加在输出上.

```agda
addZ : Z → Z → Z
addZ A Z.zero = A
addZ A (Z.suc z) = Z.suc (addZ A z)
addZ A (Z.lim f) = Z.lim (λ n → addZ A (f n))
addZ A (Z.ĉᴸ c t₀ g o₀ o) = Z.ĉᴸ c t₀ g (addZ A o₀) (λ η e → addZ A (o η e))

addG  : ∀ {A z} (GA : Goodᴺ A) (G : Goodᴺ z) → Goodᴺ (addZ A z)
addG≅ : ∀ {A z} (GA : Goodᴺ A) (G : Goodᴺ z) → forceᴺ _ (addG GA G) ≅ forceᴺ _ GA ⊕ forceᴺ _ G

⊑-≅ : ∀ {a a′ b b′ : Ordᶜ zero} → a ≅ a′ → b ≅ b′ → a′ ⊑⁰ b′ → a ⊑⁰ b
⊑-≅ ea eb k h = ≺-respʳ (k (≺-respʳ h ea)) (≅-sym eb)

addG GA gz = GA
addG GA (gs G) = gs (addG GA G)
addG GA (gl G st) = gl (λ n → addG GA (G n)) (λ n → ⊑-≅ (addG≅ GA (G n)) (addG≅ GA (G (suc n))) (⊕-⊑ʳ _ _ _ (st n)))
addG GA (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  gc ys hy dy G₀ l₀ Gg lE (addG GA Go₀) (λ k → addG GA (Go k))
     (⊑-≅ (addG≅ GA Go₀) (addG≅ GA (Go 0)) (⊕-⊑ʳ _ _ _ mo₀))
     (λ k → ⊑-≅ (addG≅ GA (Go k)) (addG≅ GA (Go (suc k))) (⊕-⊑ʳ _ _ _ (mo k)))

addG≅ GA gz = ≅-refl⁰ _
addG≅ GA (gs G) = s≅ (addG≅ GA G)
addG≅ GA (gl G st) = l≅ (λ n → addG≅ GA (G n))
addG≅ GA (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = l≅ go
  where
  go : ∀ n → outsᴺ (forceᴺ _ (addG GA Go₀)) (λ k → forceᴺ _ (addG GA (Go k))) n ≅ forceᴺ _ GA ⊕ outsᴺ (forceᴺ _ Go₀) (λ k → forceᴺ _ (Go k)) n
  go zero = addG≅ GA Go₀
  go (suc k) = addG≅ GA (Go k)
```

## §4 层号回到树

```agda
ofL : Ordᴵ → Ordᶜ zero
ofL zero = zero
ofL (suc a) = suc (ofL a)
ofL (lim f s) = lim (λ n → ofL (f n))

ofZ : Ordᴵ → Z
ofZ zero = Z.zero
ofZ (suc a) = Z.suc (ofZ a)
ofZ (lim f s) = Z.lim (λ n → ofZ (f n))

ofL-≅ : ∀ {a b} → a ≅ᴵ b → ofL a ≅ ofL b
ofL-≅ z≅ = z≅
ofL-≅ (s≅ e) = s≅ (ofL-≅ e)
ofL-≅ (l≅ h) = l≅ (λ n → ofL-≅ (h n))

ofL-≺ : ∀ {a b} → a <ᴵ b → ofL a ≺ ofL b
ofL-≺ {a} zero = ≺z (≅-refl⁰ (ofL a))
ofL-≺ (suc q) = ≺s (ofL-≺ q)
ofL-≺ (lim n q) = ≺l n (ofL-≺ q)

ofL-⊑ : ∀ {a b} → a ⊑ᴵ b → ofL a ⊑⁰ ofL b
ofL-⊑ z⊑ ()
ofL-⊑ (s⊑ e q) (≺z d) = ≺-≅ˡ (≅-trans d (ofL-≅ e)) (ofL-≺ q)
ofL-⊑ (s⊑ e q) (≺s r) = ≺-trans r (≺-≅ˡ (ofL-≅ e) (ofL-≺ q))
ofL-⊑ (l⊑ h) (≺l n r) = ofL-⊑ (h n) r

G-ofZ : ∀ η → Goodᴺ (ofZ η)
ofZ≅ : ∀ η → forceᴺ _ (G-ofZ η) ≅ ofL η
G-ofZ zero = gz
G-ofZ (suc a) = gs (G-ofZ a)
G-ofZ (lim f s) = gl (λ n → G-ofZ (f n)) (λ n → ⊑-≅ (ofZ≅ (f n)) (ofZ≅ (f (suc n))) (ofL-⊑ (s n)))
ofZ≅ zero = z≅
ofZ≅ (suc a) = s≅ (ofZ≅ a)
ofZ≅ (lim f s) = l≅ (λ n → ofZ≅ (f n))

ofL-lvl : (y : Ordᶜ zero) (h : HS y) → ofL (toLevel y h) ≅ y
ofL-lvl zero h = z≅
ofL-lvl (suc y) h = s≅ (ofL-lvl y (hs⁻ h))
ofL-lvl (lim f) h = l≅ (λ n → ofL-lvl (f n) (hl₁ h n))
ofL-lvl (limᵢ () f) h
ofL-lvl (up () x) h
```

## §5 前缀的码是字面初始段

`lvG-path` 对证书归纳: 和的码以左边的码为字面初始段, 不用函数外延, 也不看右边是什么. `ofZ-≋`: 树转一圈回来的码与原来逐点相同.

```agda
lvG-path : ∀ {A z} (GA : Goodᴺ A) (G : Goodᴺ z) → ⌈ lvG GA ⌉ ⊂ ⌈ lvG (addG GA G) ⌉
lvG-path GA gz = ⊂r
lvG-path GA (gs G) = es (lvG-path GA G)
lvG-path GA (gl G st) = el (lvG-path GA (G 0))
lvG-path GA (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = el (lvG-path GA Go₀)

-- 右加数的层号不超过和的层号
lvG-≼ : ∀ {A z} (GA : Goodᴺ A) (G : Goodᴺ z) → lvG G ≼ lvG (addG GA G)
lvG-≼ GA gz = z≼
lvG-≼ GA (gs G) = s≼ (lvG-≼ GA G)
lvG-≼ GA (gl G st) = l≼ (λ n → l≼ʳ n (lvG-≼ GA (G n)))
lvG-≼ GA (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = l≼ go
  where
  go : ∀ n → _ ≼ _
  go zero = l≼ʳ 0 (lvG-≼ GA Go₀)
  go (suc k) = l≼ʳ (suc k) (lvG-≼ GA (Go k))

ofZ-≋ : ∀ η → ⌈ lvG (G-ofZ η) ⌉ ≋ ⌈ η ⌉
ofZ-≋ zero = cz≋
ofZ-≋ (suc a) = cs≋ (ofZ-≋ a)
ofZ-≋ (lim f s) = cl≋ (λ n → ofZ-≋ (f n))
```

## §6 修法二: 分支加上上一个输出

对任何分支族. 链点读回层号, 上一个输出 $y$ 是下一支 $(\hat\eta+1)\oplus b\,\eta$ 的字面前缀 (`pre≺`), 所以 `mo` 不看 `b`.

```agda
module Sum (b : Ordᴵ → Z) (G : ∀ η → Goodᴺ (b η)) {t₀ : Z} (G₀ : Goodᴺ t₀) where
  S : Ordᴵ → Z
  S η = addZ (Z.suc (ofZ η)) (b η)

  GS : ∀ η → Goodᴺ (S η)
  GS η = addG (gs (G-ofZ η)) (G η)

  GS≅ : ∀ η → forceᴺ _ (GS η) ≅ suc (forceᴺ _ (G-ofZ η)) ⊕ forceᴺ _ (G η)
  GS≅ η = addG≅ (gs (G-ofZ η)) (G η)

  pre≺ : (y : Ordᶜ zero) (h : HS y) → y ≺ forceᴺ _ (GS (toLevel y h))
  pre≺ y h = ≺-respʳ (≺-≅ˡ (≅-trans (≅-sym (ofL-lvl y h)) (≅-sym (ofZ≅ (toLevel y h)))) (w≼-suc (forceᴺ _ (G-ofZ (toLevel y h))) (forceᴺ _ (G (toLevel y h)))))
                     (≅-sym (GS≅ (toLevel y h)))

  yh : ℕ → Σ (Ordᶜ zero) HS
  yh zero = forceᴺ _ G₀ , forceᴺ-HS _ G₀
  yh (suc m) = forceᴺ _ (GS (toLevel (proj₁ (yh m)) (proj₂ (yh m)))) , forceᴺ-HS _ (GS (toLevel (proj₁ (yh m)) (proj₂ (yh m))))

  ys : ℕ → Ordᶜ zero
  ys m = proj₁ (yh m)

  hy : ∀ m → HS (ys m)
  hy m = proj₂ (yh m)

  η : ℕ → Ordᴵ
  η m = toLevel (ys m) (hy m)

  ẐS : Z
  ẐS = Z.ĉᴸ zero t₀ (λ x _ → S x) t₀ (λ x _ → S x)

  ĜS : Goodᴺ ẐS
  ĜS = gc ys hy (λ m → z⊑) G₀ (≅-refl⁰ _) (λ m → GS (η m)) (λ m → ≅-refl⁰ _) G₀ (λ k → GS (η k))
          (≺→⊑ (pre≺ (ys 0) (hy 0))) (λ k → ≺→⊑ (pre≺ (ys (suc k)) (hy (suc k))))

  T̃ : Ordᶜ zero
  T̃ = forceᴺ _ ĜS

  H̃S : HS T̃
  H̃S = forceᴺ-HS _ ĜS

  -- 分支带前缀时, 下一个高度的码以上一个高度的码为字面初始段
  Aˢ : Ordᴵ → Code
  Aˢ x = ⌈ lvG (G-ofZ x) ⌉

  path : ∀ x → cs (Aˢ x) ⊂ ⌈ lvG (GS x) ⌉
  path x = lvG-path (gs (G-ofZ x)) (G x)

  -- 修法三: 链由 S 生成, 输出是另一族 o, 没有前缀
  module Out (o : Ordᴵ → Z) (Go : ∀ x → Goodᴺ (o x)) {o₀ : Z} (Go₀ : Goodᴺ o₀) (mo₀ : forceᴺ _ Go₀ ⊑⁰ forceᴺ _ (Go (η 0)))
    (step : ∀ x → forceᴺ _ (Go x) ⊑⁰ forceᴺ _ (Go (lvG (GS x)))) where
    o₀≼ₜ : Set
    o₀≼ₜ = lvG Go₀ ≼ lvG G₀

    ẐO : Z
    ẐO = Z.ĉᴸ zero t₀ (λ x _ → S x) o₀ (λ x _ → o x)

    ĜO : Goodᴺ ẐO
    ĜO = gc ys hy (λ m → z⊑) G₀ (≅-refl⁰ _) (λ m → GS (η m)) (λ m → ≅-refl⁰ _) Go₀ (λ k → Go (η k)) mo₀ (λ k → step (η k))

    T̄ : Ordᶜ zero
    T̄ = forceᴺ _ ĜO

    H̄S : HS T̄
    H̄S = forceᴺ-HS _ ĜO

    -- 带前缀与不带前缀, 值互相 ≼. 只要第 0 行的值不低于高度 (dom)
    T̄≼T̃ : o₀≼ₜ → (∀ x → lvG (Go x) ≼ lvG (GS x)) → lvG ĜO ≼ lvG ĜS
    T̄≼T̃ z₀ br≼ = l≼ go
      where
      go : ∀ n → _ ≼ _
      go zero = l≼ʳ 0 z₀
      go (suc k) = l≼ʳ (suc k) (br≼ (η k))

    T̃≼T̄ : (∀ x → x ≼ lvG (Go x)) → lvG ĜS ≼ lvG ĜO
    T̃≼T̄ dom = l≼ go
      where
      go : ∀ n → _ ≼ _
      go zero = l≼ʳ 1 (dom (η 0))
      go (suc k) = l≼ʳ (suc (suc k)) (dom (η (suc k)))
```
