# 实际反馈轨道没有使用 Ω 节点

输入分支允许 Ω 坐标，不意味着实际运行到过这些坐标。本篇直接检验
`FrozenOmegaClosed.intermediate`，不改变构造。`OF` 是已有谓词：树中
没有 Ω 节点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.FrozenLegalPure where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (OF)
open import OCF.Lean.FrozenOmegaIf
open import OCF.Lean.FrozenOmegaRun using (chain)
open import OCF.Lean.FrozenOmegaClosed using (U; w; M; input; intermediate; module F)
open import OCF.Lean.FrozenLegalIf using (act)
open import OCF.Lean.FrozenLegalClosed using (next)
open import OCF.Lean.TowerCollapseIf using (module Ops)

module _ {S : KS} where
  add-pure : ∀ (a b : HB S) → OF a → OF b → OF (a ⊞ b)
  add-pure a hz pa pb = pa
  add-pure a (hs b) pa pb = add-pure a b pa pb
  add-pure a (hl f) pa pb = λ n → add-pure a (f n) pa (pb n)
  add-pure a (hΩ κ g) pa ()
  partial-pure : ∀ f → (∀ n → OF (f n)) → ∀ n → OF (Ops.partial S f n)
  partial-pure f p zero = p zero
  partial-pure f p (suc n) = add-pure _ _ (partial-pure f p n) (p (suc n))

act-pure : ∀ c → OF c → OF (act c)
act-pure hz p = tt
act-pure (hs c) p = partial-pure _ (λ n → act-pure c p)
act-pure (hl f) p = λ n → act-pure (f n) (p n)
act-pure (hΩ κ g) ()

module _ {S : KS} {v : Wd S} {m : HB S} where
  erase-pure : ∀ a → OF a → OF (erase {S} {v} {m} a)
  erase-pure hz p = tt
  erase-pure (hs a) p = erase-pure a p
  erase-pure (hl f) p = λ n → erase-pure (f n) (p n)
  erase-pure (hΩ κ g) ()

next-pure : ∀ c → OF c → OF (next c)
next-pure c p = erase-pure (act c) (act-pure c p)

orbit-pure : ∀ n → OF (chain {B = SafeTw U w hz} next n)
orbit-pure zero = tt
orbit-pure (suc n) = add-pure _ _ (orbit-pure n) (next-pure _ (orbit-pure n))

safe-intermediate-pure : OF (F.fold hz (z⊲ᴮ M) input)
safe-intermediate-pure = partial-pure _ (λ n → act-pure _ (orbit-pure n))

intermediate-pure : OF intermediate
intermediate-pure = erase-pure _ safe-intermediate-pure
```

因此这个实际闭项的反馈轨道只走纯可数坐标；它不证明高层坐标回灌已
发生。输入合法与中间输出合法仍然成立，但不能算使用了 Ω 分支的强度。
