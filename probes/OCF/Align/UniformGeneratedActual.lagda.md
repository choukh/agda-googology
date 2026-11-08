# 原 Ωd 全族与真实 Int 生成闭包

实填统一保持定理的源、外回调和前缀，原 Ωd 可含任意种类与任意高度。
action 并不重新实现 Int。其源和前缀均取原 Ωd，外回调为实际恒等函数；
因此 ni 的新回调保留原前缀和内层 Int，而不是常量生成示例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformGeneratedActual where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
import OCF.Align.GenFoldTree as GT
open import OCF.Align.EventReturnCodeIf using (Shape)
open import OCF.Align.EventReturnCodeBuild using (shape-self)
import OCF.Align.UniformGeneratedBuild as B
import OCF.Align.UniformGeneratedInt as I
import OCF.Align.EventReturnValueZero as V

module Original (T : KS) (tp : TopG (step T)) where
  module P = GT.Tree T
  module O = P.Om tp
  module G = B.General (step T) (ZK T)
  module F = B.Original T tp
  module M = I.Original T
  open G

  identity : ∀ {L L′ W} → M.Callback L L′ L L′ W (λ _ _ x → x) (λ _ _ x → x)
  identity p lw xy = xy

  action : ∀ L {W} → LgW (step T) W → D L W
  action L lw = P.Int (GT.accL L) (O.Ωd L) P.≤rf lw
    (λ κ z → z) (λ p r → r) (λ p lv x → x) (O.Ωd L)

  action-related : ∀ {L L′} → Shape L L′ → ∀ {W} (lw : LgW (step T) W) →
    R (action L lw) (action L′ lw)
  action-related {L} {L′} p lw = M.preserve (GT.accL L) (GT.accL L′)
    (F.omega-related p) P.≤rf lw (λ κ z → z) (λ κ z → z)
    (λ q r → r) (λ q r → r) identity (F.omega-related p)

  action-self : ∀ L {W} (lw : LgW (step T) W) → R (action L lw) (action L lw)
  action-self L lw = action-related (shape-self L) lw

  sum-related : ∀ {W} {x y : D hz W} {a b} → R x y → V.Same a b →
    V.Same (P.sum a x) (P.sum b y)
  partial-related : ∀ {W} {f g : ℕ → D hz W} {a b} → (∀ n → R (f n) (g n)) →
    V.Same a b → ∀ n → V.Same (P.pt a f n) (P.pt b g n)
  sum-related rz p = p
  sum-related ro p = V.ss p
  sum-related (ra {a = x} {b = y} {a′ = x′} {b′ = y′} r s) p =
    sum-related {x = y} {y = y′} s (sum-related {x = x} {y = x′} r p)
  sum-related (rl r) p = V.sl (partial-related r p)
  sum-related (rw {x = x} {y = y} r) p = sum-related {x = x} {y = y} r p
  sum-related (ri {r = ()} q h) p
  sum-related (rc {κ = inj₁ κ} {z = ()} h) p
  sum-related (rc {κ = inj₂ κ} {z = ()} h) p
  partial-related r p zero = p
  partial-related {f = f} {g = g} r p (suc n) =
    sum-related {x = f n} {y = g n} (r n) (partial-related r p n)
```

sum-related 比较原零层读回的完整基本列（继而有旧 Same 的双向值界），
不是把高层关系直接当序数值相等。高层读回/迁回及 EvFold 双历史事件回灌仍待衔接。
统一关系适用于任意 S/Z；本篇原 Int 与 Ωd 的实际程序实例限定 step T/ZK T，
不能据此宣称原双事件数据与通用 DataG 字面相同。
