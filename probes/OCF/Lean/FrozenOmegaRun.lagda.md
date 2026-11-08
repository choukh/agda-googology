# Ω 层上的受限种类直接折叠

对任意 U、固定合法外层世界、合法高度 m，一条总定义。
分支仍返回整个源塔的受限树，并未假装落回所属分量。
保留时目标坐标直接经 dcl 的 fr 进入源分支；不洗坐标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.FrozenOmegaRun where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Dc; keep; same; above; cl; dcl)
open import OCF.Lean.FrozenOmegaIf
open import OCF.Lean.TowerCollapseIf using (module Ops)

module _ {A B : KS} where
  chain : (HB A → HB A) → ℕ → HB A
  chain k zero = hs hz
  chain k (suc n) = chain k n ⊞ k (chain k n)
  diagonal : (HB A → HB A) → (HB A → HB B) → HB B
  diagonal k f = Ops.sum B (λ n → f (chain k n))

module Run (U : KS) (w : Wd U) (lw : LgW U w) (m : HB U) (lm : LgB m) where
  Source = HB (SafeTw U w m)
  Target : HB U → Set
  Target t = HB (SafeTw U w t)

  fold : ∀ t → t ⊲[ w ] m → Source → Target t
  fold t pt hz = hs hz
  fold t pt (hs a) = Ops.repeat (SafeTw U w t) (fold t pt a)
  fold t pt (hl f) = hl (λ n → fold t pt (f n))
  fold t pt (hΩ (κ , p) g) with dcl pt lw lm (cl m κ p)
  ... | keep κ′ p′ fr = hΩ (κ′ , p′) (λ c → fold t pt (g (fr c)))
  ... | same to = diagonal
      (λ c → erase (fold t pt (g (to c))))
      (λ c → fold t pt (g (to c)))
  ... | above i pi ti to = diagonal
      (λ c → erase (fold i (⊲ᴮ-tr (hsuc hself) pi) (g (to c))))
      (λ c → fold t pt (g (to c)))

  instance-direct : Direct U w lw m lm
  instance-direct = record { fold = fold }
```

此处没有合法性与值定理。冻结世界取消更新，但限制种类的代价落在输入
可构造性：任意原始地板坐标不一定可嵌入 Source。
