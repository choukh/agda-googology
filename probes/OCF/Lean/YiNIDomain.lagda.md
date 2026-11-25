# 第 0 层孩子的 Ω 结点：带证据的请求域
不读记号；这里只定义读回证据、指定结点及字面公共界，不陈述全合法域的值律。
偏移来自规范源层上的树；padding 保留原对象的零前缀，避免假设函数外延。
来源：规范源域复用 YiCNDomain；树、路径、表和标准底均复用主线。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNIDomain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiMTTab as MT
open import OCF.Lean.YiCNDomain using (Cn)

record Readback (k : B.L) : Set where
  field
    source : B.L
    canonical : Cn source
    code : B.Tr source
    reads : k ≡ B.↑ source code

zeros : ℕ → B.L → B.L
zeros zero a = a
zeros (suc n) a = B.zero B.⊕ zeros n a

record Node : Set where
  field
    offset : B.L
    readback : Readback offset
    padding : ℕ
    tail : B.Tr B.zero → B.Tr B.zero
  child : B.Tr B.zero → B.L
  child d = offset B.⊕ zeros padding (B.↑ B.zero (tail d))
  layer : B.L
  layer = B.nd (B.sΩ B.zero) child
  field
    okay : P.Ok layer

record Common (i j : B.L) : Set where
  field
    top : B.L
    left : i P.≤ top
    right : j P.≤ top

offset-child : (d : Node) (c : B.Tr B.zero) → Node.offset d P.≤ Node.child d c
offset-child d c = P.lift (Node.offset d) (zeros (Node.padding d) (B.↑ B.zero (Node.tail d c)))

offset-bound : (d : Node) → Common (Node.offset d) B.zero
offset-bound d = record
  { top = Node.layer d ; left = P.inc B.zero (offset-child d B.zero) ; right = P.ink P.self }

child-bound : (d : Node) (c : B.Tr B.zero) → Common (Node.child d c) B.zero
child-bound d c = record { top = Node.layer d ; left = P.inc c P.self ; right = P.ink P.self }

opaque
  output : Node → B.Tr B.zero
  output d = proj₁ (MT.ψ₀ᶻ (Node.layer d) (Node.okay d) (proj₁ (O.Ωt (Node.layer d))))
  output-eq : ∀ d → output d ≡ proj₁
    (MT.ψ₀ᶻ (Node.layer d) (Node.okay d) (proj₁ (O.Ωt (Node.layer d))))
  output-eq d = refl
```
