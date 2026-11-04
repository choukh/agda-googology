# 不带高度的树接上带高度的树 (八): $\Omega\cdot2$ 的第一个具体差别

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). `c₂`: 闭包 $\lambda\eta.\,c_1+\eta$, 第一支 $c_1+1$, 是 $\Omega\cdot2$ 的形状. `cf₂`: 它是好层号, 由 `⊴⁺` 给 (定理). `keep-Ω·2`: 帧的位置是 `self` (键是 $c_2$) 时, `keepP` 对高层节点也答 `false`, 所以 [WeakBridgeSel](WeakBridgeSel.lagda.md) 的 "`keepP` 只看节点的类" (`keepP-hi`) 到 $c_2$ 上不成立, 要分键. `n₂`: 节点 $c_1+1$ 的路径在分支 $\eta=2$ 里, 不是 `c⁺` 的字面路径, 所以 `pull⁺` 那样的节点分类要多一层. **这些只是计算, 不是否定, 不否定 $\Omega\cdot2$ 上的桥.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeNext where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (false)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase using (Tc)
open import OCF.Align.GuardWeakRd using (Tc-Ω₁)
open import OCF.Align.GuardWeakTree using (module FoldW)
open import OCF.Align.WeakBridgeBase

one : Ordᴵ
one = suc zero

c₂ : LG
c₂ = Lv.lc one (c⁺ one) (λ η _ → c⁺ η)

wf₂ : WFˢ c₂
wf₂ = (λ η e → ⊴⁺ e) , (λ η e η′ e′ d → ⊴⁺ d) , wf⁺ one , (λ η e → wf⁺ η)

sf₂ : c₂ ≈ c₂
sf₂ = Lv.o≈ (≅ᴵ-refl one) (sf⁺ one) (λ η e η′ e′ k → c⁺-≈ k)

cf₂ : Cfˢ c₂
cf₂ = wf₂ , sf₂

two : Ordᴵ
two = suc one

e₂ : one ⊑ᴵ two
e₂ = s⊑ z≅ (suc zero)

-- 节点 c₁+1, 在分支 2 里
n₂ : c⁺ one < c₂
n₂ = Lv.bra two e₂ Lv.zero

module K (tc : Tc c₂) = FoldW c₂ wf₂ sf₂ tc

keep-Ω·2 : ∀ (tc : Tc c₂) {E : Ents} (ad : Adm (tab E) n₂) → K.keepP tc {E = E} wf₂ sf₂ Lv.self n₂ tt ad ≡ false
keep-Ω·2 tc ad = refl
```
