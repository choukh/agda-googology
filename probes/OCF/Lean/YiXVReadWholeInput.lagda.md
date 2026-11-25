# YiXVReadWholeInput
> 验收文件。档位：编译定理。统一当前位置与严格槽位的读回关系，含自然极限原 wh 推送入口实例。
> 跟踪 YiLegPath 的原计算；不改树、折叠、UR、比较器。未交完整极限／节点世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadWholeInput where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiLegPath as P
import OCF.Align.Level as L
open import OCF.Align.Value using (z≼)
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadOmegaInput as Ω
slot : ∀ r → S.Pos⁼ (J.ℓ r) → S.Tr S.zero
slot r (inj₁ _) = r
slot r (inj₂ p) = J.slot r p
Rel : ∀ r (p : S.Pos⁼ (J.ℓ r)) → S.Br⁼ (J.ℓ r) p → L.Ordᶜ (T.lvl (slot r p)) → Set
Rel r (inj₁ _) a X = U.UR r a X
Rel r (inj₂ p) a X = U.Fam r p a X
model₀ : Rel S.zero (inj₁ tt) S.zero (L.Ω L.zero)
model₀ = z≼
model₁ : Rel (S.suc S.zero) (inj₂ (inj₁ tt)) S.zero (L.Ω L.zero)
model₁ = z≼
model-ω : Rel Ω.ω (P.psh (T.wh Ω.ω) (inj₁ tt)) S.zero (L.Ω L.zero)
model-ω = z≼
```
