# 原第一层 Int 的上下文关系合同

继承旧 R，但 ni 的低坐标使用允许单侧 nw 的 E₀。
两边共享 A 路径与其合法证明，历史后缀可以不同。
这不要求任意原数据自相关，分支相容由关系显式携带。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCtxIf where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (D₁)
open import OCF.Align.EventReturnCoordIf

data R₁ (a : A) (H H′ : Hist) : D₁ (a , H) → D₁ (a , H′) → Set where
  rz : R₁ a H H′ n0 n0
  ro : R₁ a H H′ n1 n1
  ra : ∀ {x y x′ y′} → R₁ a H H′ x x′ → R₁ a H H′ y y′ → R₁ a H H′ (x ⨾ y) (x′ ⨾ y′)
  rl : ∀ {f g} → (∀ n → R₁ a H H′ (f n) (g n)) → R₁ a H H′ (nl f) (nl g)
  rw : ∀ {b J J′} {x : D₁ (b , J)} {y : D₁ (b , J′)}
       (p : b ⊲ a) (s : Suf J H) (s′ : Suf J′ H′) → R₁ b J J′ x y →
       R₁ a H H′ (nw (p , s) x) (nw (p , s′) y)
  rk : ∀ {u : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H)}
         {v : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H′)} →
       (∀ {c} (p : a ⊲ c) lc → R₁ c H H′ (u p lc) (v p lc)) → R₁ a H H′ (nκ tt u) (nκ tt v)
  ri : ∀ {u : ∀ {W} → (a , H) ≤ W → LgWε W → D₀ W → D₁ W}
         {v : ∀ {W} → (a , H′) ≤ W → LgWε W → D₀ W → D₁ W} →
       (∀ {b J J′} (p : a ⊲ b) (s : Suf H J) (s′ : Suf H′ J′) (lb : Lg b)
          {x : D₀ (b , J)} {y : D₀ (b , J′)} → E₀ x y →
          R₁ b J J′ (u (p , s) (lb , tt) x) (v (p , s′) (lb , tt) y)) →
       R₁ a H H′ (ni (ss hself) u) (ni (ss hself) v)

Mk₁ : Wε → Set
Mk₁ W = ∀ {V j} → W ≤ V → StH V j (hs hz) → StH V j (hs hz)

UH : ∀ {a H H′} →
  (∀ {V} → (a , H) ≤ V → LgWε V → D₁ V → D₁ V) →
  (∀ {V} → (a , H′) ≤ V → LgWε V → D₁ V → D₁ V) → Set
UH {a} {H} {H′} u v = ∀ {b J J′} (p : a ⊲ b)
  (s : Suf H J) (s′ : Suf H′ J′) (lb : Lg b) {x : D₁ (b , J)} {y : D₁ (b , J′)} →
  R₁ b J J′ x y → R₁ b J J′ (u (p , s) (lb , tt) x) (v (p , s′) (lb , tt) y)

record Internal : Set₁ where
  field
    preserve : ∀ {a b H H′ J J′} (ac ac′ : AccY (hs hz))
      {x : D₁ (a , H)} {y : D₁ (a , H′)} → R₁ a H H′ x y →
      (p : a ⊲ b) (s : Suf H J) (s′ : Suf H′ J′) (lb : Lg b)
      (mk : Mk₁ (b , J)) (mk′ : Mk₁ (b , J′))
      {u : ∀ {V} → (b , J) ≤ V → LgWε V → D₁ V → D₁ V}
      {v : ∀ {V} → (b , J′) ≤ V → LgWε V → D₁ V → D₁ V} → UH u v →
      ∀ {w w′} → R₁ b J J′ w w′ →
      R₁ b J J′
        (Int ac x (p , s) (lb , tt) tt (λ _ z → z) mk u w)
        (Int ac′ y (p , s′) (lb , tt) tt (λ _ z → z) mk′ v w′)
```

合同只要求原 D₁→D₁ Int；不把 D₂ 的 nε 历史走法顺带列作已实现。
