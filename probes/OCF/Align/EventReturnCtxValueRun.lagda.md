# 第二层观察与单侧迁回

同时包含 ni 的两种低坐标与 κ₀ 事件闭包。回调只消费同步后缀及
相关坐标；移植改变基底不改变后缀关系。这里不假定任意 D₂ 自相关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCtxValueRun where

open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (Lg; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.HtTowerCont using (nbᴮ)
open import OCF.Align.HtTowerNRead using (nbAᵗ)
open import OCF.Align.EventReturnHistory
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)
import OCF.Align.EventReturnCodeBuild as Code
import OCF.Align.EventReturnCoordBuild as E
import OCF.Align.EventReturnCtxActual as Low
open import OCF.Align.EventReturnCtxValueIf

rebase-left : ∀ {H H′ J J′} {p : Suf H J} {q : Suf H′ J′} →
  Suffix p q → ∀ K → Suffix (tp-suf p K) q
rebase-left done K = done
rebase-left (next e p) K = next e (rebase-left p K)

left : ∀ {a H H′ J x y} → R₂ a H H′ x y → R₂ a J H′ (drp₂ x) y
left rz = rz
left ro = ro
left (ra p q) = ra (left p) (left q)
left (rl p) = rl (λ n → left (p n))
left (rw p s s′ r) = rw p here s′ (left r)
left (rk p) = rk (λ q lc → left (p q lc))
left {H = H} (ri₀ p) = ri₀ (λ q s s′ sr lc r →
  left (p q (tp-suf s H) s′ (rebase-left sr H) lc (E.drop-left r)))
left {H = H} (ri₁ p) = ri₁ (λ q s s′ sr lc r →
  left (p q (tp-suf s H) s′ (rebase-left sr H) lc (Low.left r)))
left {H = H} (re p) = re (λ q s s′ sr lc →
  left (p q (tp-suf s H) s′ (rebase-left sr H) lc))

nb-shape : ∀ {b b′ : H₁} {s s′ : H₀ → H₁ → H₁} → Shape b b′ →
  (∀ c {v v′} → Shape v v′ → Shape (s c v) (s′ c v′)) →
  ∀ d → Shape (nbᴮ b s d) (nbᴮ b′ s′ d)
nb-shape p q hz = p
nb-shape p q (hs d) = q d (nb-shape p q d)
nb-shape p q (hl f) = sl (λ n → nb-shape p q (f n))
nb-shape p q (hΩ κ f) = so (λ e → nb-shape p q (f e))

nbA-shape : ∀ {b b′ s s′} → Shape b b′ →
  (∀ c {v v′} → Shape v v′ → Shape (s c v) (s′ c v′)) →
  ∀ d → Shape (nbAᵗ b s d) (nbAᵗ b′ s′ d)
nbA-shape p q C.azero = p
nbA-shape p q (C.asuc d) = q d (nbA-shape p q d)
nbA-shape p q (C.alim f) = sl (λ n → nbA-shape p q (f n))

mutual
  observe : ∀ {a H H′ x y b b′} → (la : Lg a) → R₂ a H H′ x y → Shape b b′ →
    Shape (rd₂ (la , tt) b x) (rd₂ (la , tt) b′ y)
  observe la rz p = p
  observe la ro p = ss p
  observe la (ra {x} {y} {x′} {y′} r s) p =
    observe {x = y} {y = y′} la s (observe {x = x} {y = x′} la r p)
  observe la (rl r) p = sl (λ n → partials la r p n)
  observe la (rw q s s′ r) p = observe (lg⊲ q la) r p
  observe {a} la (rk r) p = so (nbA-shape p
    (λ c q → observe (lwκ c la) (r (pwκ a c) (lwκ c la)) q))
  observe la (ri₀ r) p = so (nbA-shape p
    (λ c q → observe la (r C.self here here done la (E.encoded₀ c)) q))
  observe la (ri₁ r) p = so (nb-shape p
    (λ x q → observe la (r C.self here here done la (Low.code (Code.encoded x))) q))
  observe {a} {H} {H′} la (re r) p = so (nb-shape p
    (λ x q → observe la
      (r C.self (Data.Product.proj₂ (≤x {a , H} (la , tt) x))
        (Data.Product.proj₂ (≤x {a , H′} (la , tt) x)) (observed-suffix la x) la) q))

  partials : ∀ {a H H′ f g b b′} → (la : Lg a) →
    (∀ n → R₂ a H H′ (f n) (g n)) → Shape b b′ → ∀ n →
    Shape (rdp₂ (la , tt) b f n) (rdp₂ (la , tt) b′ g n)
  partials la r p zero = p
  partials la r p (suc n) = observe la (r n) (partials la r p n)

returned : ∀ {a H H′ x y} (la : Lg a) → R₂ a H H x y → ∀ b →
  Shape (rd₂ {a , H′} (la , tt) b (drp₂ x)) (rd₂ {a , H} (la , tt) b y)
returned la p b = observe la (left p) (Code.shape-self b)
```

`returned` 的自相关前提必须由原生成方式提供。后续仍需证明原
Run 的状态及实际回调给出 R₂；本篇没有把此义务改成任意函数公理。
