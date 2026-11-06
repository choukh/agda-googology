# NegRaise (五): 对照构造一路的实例

> 不含记号. 入口 [NegRaise](NegRaise.lagda.md). 导入构造一路 `RaiseCBd` (只读) 与本路的模块. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 构造一路没有无条件的 `RaiseA` 实例. 它的条件实例 `RaiseCBd.dec→Raise d` (前提: 子项关系可判定, 推出 LPO) 对照本路划出的边界:
>
> - **是选择子** (`decR-sel`): 值是 $a$ 或 $v$. 与 `NegRaiseSel.sel→LPO` 相合 (它的前提本来就是 LPO 档).
> - **不满足** `Mono0`, `Cont0`, `Flip` (任何 `RaiseA` 都不满足, `NegRaiseBnd`); 这里只把定理套上去 (`decR-no-mono0` 等).
>
> 本路自己的部分实例 `NegRaiseFin.raiseFin 1` **不是**选择子: 在 $v=\omega$ 处输出既不是 $1$ 也不是 $\omega$ (`fin-not-1`, `fin-not-ω`). 所以 "值在 $\{a,v\}$ 里" 是构造一路的写法带来的, 不是接口逼的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRaiseCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_)
open import OCF.Align.RaiseIf using (RaiseA; R)
open import OCF.Align.RaiseCBd using (Rd; dec→Raise)
open import OCF.Align.NegRaiseBnd using (no-mono0; no-cont0; no-flip; Mono0; Cont0; Flip)
open import OCF.Align.NegRaiseSel using (Sel)
open import OCF.Align.NegRaiseFin using (nat; nat-deq; ω; module Search; raiseFin; Rₐ)
```

## §1 `dec→Raise` 是选择子

```agda
module _ (d : ∀ a v → Dec (a ⊲ v)) where
  rd-sel : ∀ a v → (Rd d a v ≡ a) ⊎ (Rd d a v ≡ v)
  rd-sel a v with d a v
  ... | yes _ = inj₂ refl
  ... | no _ = inj₁ refl

  decR-sel : Sel (dec→Raise d)
  decR-sel {a} {v} _ _ = rd-sel a v

  decR-no-mono0 : ¬ Mono0 (dec→Raise d)
  decR-no-mono0 = no-mono0 (dec→Raise d)

  decR-no-cont0 : ¬ Cont0 (dec→Raise d)
  decR-no-cont0 = no-cont0 (dec→Raise d)

  decR-no-flip : ¬ Flip (dec→Raise d)
  decR-no-flip = no-flip (dec→Raise d)
```

## §2 `raiseFin 1` 不是选择子

```agda
R₁ω : A
R₁ω = Rₐ (raiseFin 1) ω

fin-not-1 : ¬ (R₁ω ≡ nat 1)
fin-not-1 ()

hd : A → A
hd (alim f) = f 0
hd x = x

fin-not-ω : ¬ (R₁ω ≡ ω)
fin-not-ω e with cong hd e
... | ()
```
