# YiXVReadEmbedInput
> 验收文件。档位：编译定理。原嵌入及其非零证据组成的输入，含零、一层与自然极限完整实例。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadEmbedInput where
open import Data.Product using (Σ; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadOmegaInput as Ω

NZ : S.L → Set
NZ j = Σ (S.Tr j) (λ a → j S.⊢ S.zero ◃ a)
raise : ∀ j (c : S.Ch j) → NZ (S.chL j c) → NZ j
raise S.zero () z
raise (S.suc j) c (a , na) = S.up S.zero c a na , S.◃u S.zero c a na
raise (S.lim f) n (a , na) = S.up S.zero n a na , S.◃u S.zero n a na
raise (S.Ωₗ k h) c (a , na) = S.up S.zero c a na , S.◃u S.zero c a na
emb : ∀ {cur orig v} → R.Route cur orig v → NZ (J.ℓ orig) → NZ (J.ℓ cur)
emb {cur} {orig} {v} rv (a , na) = P.emb (J.ℓ cur) (T.εh cur) v a na , P.emb-nz (J.ℓ cur) (T.εh cur) v a na

one : NZ S.zero
one = S.suc S.zero , S.◃s
model₀ : emb {cur = S.zero} R.here one ≡ one
model₀ = refl
model₁ : emb R.model₁ one ≡
  (S.up S.zero tt (S.suc S.zero) S.◃s , S.◃u S.zero tt (S.suc S.zero) S.◃s)
model₁ = refl
model-ω : emb R.model-ω one ≡
  (S.up S.zero 0 (S.suc S.zero) S.◃s , S.◃u S.zero 0 (S.suc S.zero) S.◃s)
model-ω = refl
```
