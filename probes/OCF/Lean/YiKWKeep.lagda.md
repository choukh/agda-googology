# 保留行的变量换型规格
验收文件；编译定理：保留时输出第 1 层的 Ω 结点，保留实际换型函数。
不要求换型为恒等，不构造分支关系；实际实例见 YiKWObjects。
来源：变量上展开 YiRWFold.node⁺；第 1 层常量复用 YiBVRows。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKWKeep where
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiBVRows as V
Keep : Set
Keep = F.Keep V.one (B.Tr B.zero) B.zero
Good : Keep → Set
Good (just _) = ⊤
Good nothing = ⊥
cv : Keep → B.Tr B.zero → B.Tr B.zero
cv (just (inj₁ () , _))
cv (just (inj₂ (tt , inj₂ ()) , _))
cv (just (inj₂ (tt , inj₁ tt) , f , _)) = f
cv nothing = λ d → d
node-row : (k : Keep) (g : B.Tr B.zero → O.Tr⁺ V.one) (f : B.Tr B.zero → B.Tr B.zero)
  → Good k → proj₁ (F.node⁺ k g f) ≡ B.Ω V.q1 (λ d → proj₁ (g (cv k d)))
node-row (just (inj₁ () , _)) g f ok
node-row (just (inj₂ (tt , inj₂ ()) , _)) g f ok
node-row (just (inj₂ (tt , inj₁ tt) , c , _)) g f ok = refl
node-row nothing g f ()
prepend : (x y : B.Tr V.one) (g : B.Tr B.zero → B.Tr V.one)
  → y ≡ B.Ω V.q1 g → x O.+ y ≡ B.Ω V.q1 (λ d → x O.+ g d)
prepend x .(B.Ω V.q1 g) g refl = refl
```
