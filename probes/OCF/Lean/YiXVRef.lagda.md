# YiXV：BTBO 参照列的吸收
> 验收文件。编译定理：参照列严格步进，后一项吸收前一项乘 ω；不包含源树的逐项上界。
> 来源：`BTBOFullV3.Fstep`、`Fmul` 与 `Level.Ψ⁰-mono`；算术采用 `YiCeilRead.ωx`。
> 最小源实例与未证上界的类型见 `YiXVStart`。不改树、折叠或合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVRef where

open import Data.Nat using (ℕ; zero; suc)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ⊑→≼)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.BTBOFullV3 using (Fstep; Fmul)
open import OCF.Lean.YiCeilRead using (ωx)

ref-strict : (n : ℕ) → D.γ n L.≺ D.γ (suc n)
ref-strict zero = L.≺l 0 (L.≺l 2 (L.≺z (L.s≅ L.z≅)))
ref-strict (suc n) =
  L.Ψ⁰-mono
    (L.s⊑′ (L.toLevel-≺ (D.cert n) (D.cert (suc n)) (ref-strict n)))
    (Fstep (D.L n))

ref-absorb : (n : ℕ) → ωx (D.γ (suc n)) ≼ D.γ (suc (suc n))
ref-absorb n =
  ≼-trans (⊑→≼ (ωx (D.γ (suc n))) (Fmul (D.L n)))
    (⊑→≼ (L.ψ⁰ (L.Ω (L.suc (D.L n))))
      (L.Ψ⁰-mono
        (L.s⊑′ (L.toLevel-≺ (D.cert n) (D.cert (suc n)) (ref-strict n)))))
```
