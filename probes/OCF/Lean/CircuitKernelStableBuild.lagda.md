# 未来证书的投影、再基址与实际种子

只给结构闭包，不改变原 ThirdFold。旧 Gd 的单调性没有作为前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitKernelStableBuild where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)
open import OCF.Lean.ThirdTw using (topT; Sb; fl)
import OCF.Lean.ThirdFold as F
import OCF.Lean.CircuitKernelStableIf as I

module For (U : KS) where
  open I.For U public

  compose : ∀ {u v w} → Future u v → Future v w → Future u w
  compose stay q = q
  compose p stay = p
  compose (grow p) (grow q) = grow (≤w-tr U p q)

  pos-up : ∀ m κ {w v} → Future w v → Pos U w m κ → Pos U v m κ
  pos-up m κ stay p = p
  pos-up hz κ (grow q) p = tt
  pos-up (hs m) (inj₁ κ) (grow q) p = pos-up m κ (grow q) p
  pos-up (hs m) (inj₂ _) (grow q) p = tt
  pos-up (hl f) (n , κ) (grow q) p = pos-up (f n) κ (grow q) p
  pos-up (hΩ κ₀ f) (e , κ) (grow q) (b , p) = Bd↑ U q b , pos-up (f e) κ (grow q) p

  rebase : ∀ m {w v} h → Future w v → Stable m w h → Stable m v h
  rebase m hz q s = tt
  rebase m (hs h) q s = rebase m h q s
  rebase m (hl f) q s = λ n → rebase m (f n) q (s n)
  rebase m (hΩ κ g) q (p , s) = pos-up m κ q p , λ r lv e a → s (compose q r) lv e a

  current : ∀ m {w} (lw : LgW U w) h → Stable m w h → F.Gd U w lw m h
  current m lw hz s = tt
  current m lw (hs h) s = current m lw h s
  current m lw (hl f) s = λ n → current m lw (f n) (s n)
  current m lw (hΩ κ g) (p , s) = p , λ e a → current m lw (g e) (s stay lw e a)

  add : ∀ m {w} a b → Stable m w a → Stable m w b → Stable m w (a ⊞ b)
  add m a hz pa pb = pa
  add m a (hs b) pa pb = add m a b pa pb
  add m a (hl f) pa pb = λ n → add m a (f n) pa (pb n)
  add m a (hΩ κ g) pa (p , pb) = p , λ q lv e ae →
    add m a (g e) (rebase m a q pa) (pb q lv e ae)

  base : ∀ {w} (a : HB U) → Stable hz w a
  base hz = tt
  base (hs a) = base a
  base (hl f) = λ n → base (f n)
  base (hΩ κ g) = tt , λ q lv e ae → base (g e)

  upward : ∀ m {w} a → Stable m w a → Stable (hs m) w (up a)
  upward m hz p = tt
  upward m (hs a) p = upward m a p
  upward m (hl f) p = λ n → upward m (f n) (p n)
  upward m (hΩ κ g) (p , q) = p , λ r lv e ae → upward m (g e) (q r lv e ae)

  -- 同一原 topT：新 Ω 的分支是全部原低层树的 up，并非常零。
  first-floor : ∀ fb {w} → Stable (hs hz) w (topT U fb (hs hz))
  first-floor fb = tt , λ q lv e ae → upward hz e (base e)

module Actual (n : _) where
  open For (Sb n)
  seed : ∀ {w} → Stable (hs hz) w (topT (Sb n) (fl n) (hs hz))
  seed = first-floor (fl n)
```

Actual.seed 对所有原底 Sb n 给非零 Ω 地板，但只在塔高度 1；
没有将它当成全部高度或全 fl/gtX 的反馈闭包。
