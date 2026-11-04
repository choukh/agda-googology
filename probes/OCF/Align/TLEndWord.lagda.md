# 世界内的构造有没有封顶 (三): 不带外部输入的类

> 入口 [TLEnd](TLEnd.lagda.md). **判决: HOLDS (编译过, 无条件).** 不读记号. 这是把外部输入去掉之后的类.
>
> **类, 一句话.** 从起点 $x_0$ 起, 反复用两个算子: 高度回灌 `F x` (`cs ⌈x⌉` 顶上第 0 行的层号) 和下一个闭包点 `N x` (`νT 𝒯 (cs ⌈x⌉)` 的层号). 类 `𝓦ʷ` 是这样走到的层号, 对后继和下方封闭.
>
> | 定理 | 陈述 |
> | --- | --- |
> | `Cap`, `G-Cap` | 带证书的闭项, 对起点参数化 |
> | `word<` | 一切操作序列的结果严格低于 `Cap` |
> | `capʷ`, `cap≺` | `𝓦ʷ` 的一切 $x$ 被某个序列盖住; `suc x ≼ lvCap` |
> | `F-closed`, `N-closed` | 类对两个算子封闭: 这是由定义得到的, 所以 `lvCap` 在类的意义下是闭包点 |
> | `esc` | `F` 喂 `lvCap` 就过了 `lvCap` |
>
> `Cap` 有上界是平凡的 (`diag`): 可数类总有上界. **这个定理的内容不在上界, 在 `Cap` 对这些算子闭合而且不提任何记号.** 它是否有分辨力, 看正对照 ([TLEndTop](TLEndTop.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLEndWord where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (⌈_⌉; _≼_; z≼; s≼; s≼ʳ; l≼; l≼ʳ; ≼-trans; ≼-refl; dom₀)
open import OCF.Align.LadderOrdCert using (ev₀; Tᵖ; Gᵖ)
open import OCF.Align.CrossMInst using (𝒯; val≼T)
open import OCF.Align.CrossNextSum using (addZ; addG; lvG-≼; ofZ; G-ofZ)
open import OCF.Align.TLEndNeg using (module Diag)
```

## §1 算子

对抽象的算子写 (`F-above` 是唯一的前提), 实例在文末. 理由同 [TLEndCap](TLEndCap.lagda.md): 闭合世界上比较计值要化简证书, 第一版这个文件在 10G 堆内耗尽.

```agda
lvG-left : ∀ {A z} (GA : Goodᴺ A) (G : Goodᴺ z) → lvG GA ≼ lvG (addG GA G)
lvG-left GA gz = ≼-refl _
lvG-left GA (gs G) = s≼ʳ (lvG-left GA G)
lvG-left GA (gl G st) = l≼ʳ 0 (lvG-left GA (G 0))
lvG-left GA (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = l≼ʳ 0 (lvG-left GA Go₀)

ofZ≽ : ∀ x → x ≼ lvG (G-ofZ x)
ofZ≽ zero = z≼
ofZ≽ (suc x) = s≼ (ofZ≽ x)
ofZ≽ (lim f s) = l≼ (λ n → l≼ʳ n (ofZ≽ (f n)))

module Ops (zF : Ordᴵ → Z) (GF : ∀ x → Goodᴺ (zF x)) (zN : Ordᴵ → Z) (GN : ∀ x → Goodᴺ (zN x))
  (F-above : ∀ x → suc x ≼ lvG (GF x)) where

  F N : Ordᴵ → Ordᴵ
  F x = lvG (GF x)
  N x = lvG (GN x)

  -- 一个操作序列
  run : List Bool → Ordᴵ → Ordᴵ
  run [] x = x
  run (true ∷ w) x = run w (F x)
  run (false ∷ w) x = run w (N x)
```

## §2 深度 $d$ 的全部序列的和

`S d x`: 从 $x$ 起长度恰为 $d$ 的序列的结果都不超过它. 只用和: 两边都盖住.

```agda
  Sz : ℕ → Ordᴵ → Z
  SG : ∀ d x → Goodᴺ (Sz d x)
  Sz zero x = ofZ x
  Sz (suc d) x = addZ (Sz d (F x)) (Sz d (N x))
  SG zero x = G-ofZ x
  SG (suc d) x = addG (SG d (F x)) (SG d (N x))

  S≽ : ∀ w x → run w x ≼ lvG (SG (length w) x)
  S≽ [] x = ofZ≽ x
  S≽ (true ∷ w) x = ≼-trans (S≽ w (F x)) (lvG-left (SG (length w) (F x)) (SG (length w) (N x)))
  S≽ (false ∷ w) x = ≼-trans (S≽ w (N x)) (lvG-≼ (SG (length w) (F x)) (SG (length w) (N x)))
```

## §3 封顶

```agda
  module Top (x₀ : Ordᴵ) where
    private module D = Diag (λ d → Sz d x₀) (λ d → SG d x₀)

    G-Cap : Goodᴺ (Z.lim D.zA)
    G-Cap = D.Ĝ

    Cap : Ordᶜ zero
    Cap = forceᴺ _ G-Cap

    HS-Cap : HS Cap
    HS-Cap = forceᴺ-HS _ G-Cap

    lvCap : Ordᴵ
    lvCap = lvG G-Cap

    word< : ∀ w → suc (run w x₀) ≼ lvCap
    word< w = ≼-trans (s≼ (S≽ w x₀)) (D.diag (length w))

    data 𝓦ʷ : Ordᴵ → Set where
      w-word : ∀ w → 𝓦ʷ (run w x₀)
      w-suc  : ∀ {x} → 𝓦ʷ x → 𝓦ʷ (suc x)
      w-dn   : ∀ {x y} → y ≼ x → 𝓦ʷ x → 𝓦ʷ y

    -- 后继: 用 F 一步盖住
    capʷ : ∀ {x} → 𝓦ʷ x → Σ (List Bool) λ w → x ≼ run w x₀
    capʷ (w-word w) = w , ≼-refl _
    capʷ (w-suc h) = step (capʷ h)
      where
      step : ∀ {x} → (Σ (List Bool) λ w → x ≼ run w x₀) → Σ (List Bool) λ w → suc x ≼ run w x₀
      step (w , d) = snoc w , ≼-trans (s≼ d) (snoc≽ w x₀)
        where
        snoc : List Bool → List Bool
        snoc [] = true ∷ []
        snoc (b ∷ w) = b ∷ snoc w
        snoc≽ : ∀ w x → suc (run w x) ≼ run (snoc w) x
        snoc≽ [] x = F-above x
        snoc≽ (true ∷ w) x = snoc≽ w (F x)
        snoc≽ (false ∷ w) x = snoc≽ w (N x)
    capʷ (w-dn d h) = proj₁ (capʷ h) , ≼-trans d (proj₂ (capʷ h))

    cap≺ : ∀ {x} → 𝓦ʷ x → suc x ≼ lvCap
    cap≺ h = ≼-trans (s≼ (proj₂ (capʷ h))) (word< (proj₁ (capʷ h)))

    -- 类对两个算子封闭 (序列接一步)
    F-closed : ∀ w → suc (F (run w x₀)) ≼ lvCap
    F-closed w = ≼-trans (s≼ (eq w x₀)) (word< (w ++′ (true ∷ [])))
      where
      _++′_ : List Bool → List Bool → List Bool
      [] ++′ v = v
      (b ∷ u) ++′ v = b ∷ (u ++′ v)
      eq : ∀ u x → F (run u x) ≼ run (u ++′ (true ∷ [])) x
      eq [] x = ≼-refl _
      eq (true ∷ u) x = eq u (F x)
      eq (false ∷ u) x = eq u (N x)

    N-closed : ∀ w → suc (N (run w x₀)) ≼ lvCap
    N-closed w = ≼-trans (s≼ (eq w x₀)) (word< (w ++′ (false ∷ [])))
      where
      _++′_ : List Bool → List Bool → List Bool
      [] ++′ v = v
      (b ∷ u) ++′ v = b ∷ (u ++′ v)
      eq : ∀ u x → N (run u x) ≼ run (u ++′ (false ∷ [])) x
      eq [] x = ≼-refl _
      eq (true ∷ u) x = eq u (F x)
      eq (false ∷ u) x = eq u (N x)

    -- 喂自己就过了自己
    esc : suc lvCap ≼ F lvCap
    esc = F-above lvCap
```

## §4 实例

```agda
open import OCF.Align.CrossMNode using (νZ; Gν)

above-F : ∀ x → suc x ≼ lvG (Gᵖ (cs ⌈ x ⌉) end zero)
above-F x = ≼-trans (s≼ (dom₀ x)) (val≼T (cs ⌈ x ⌉))

open Ops (λ x → toZ (Tᵖ (cs ⌈ x ⌉) end zero ev₀ zero)) (λ x → Gᵖ (cs ⌈ x ⌉) end zero) (λ x → νZ 𝒯 (cs ⌈ x ⌉)) (λ x → Gν 𝒯 (cs ⌈ x ⌉)) above-F public
```
