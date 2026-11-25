# 把树值的比较证据编成整个地址线序的嵌入

第四层。给定有效的 x≼y 证据，同时为源节点的所有孩子排列目标副本。所得映射在全部合法地址上保严格顺序，能处理换到较早兄弟的下降。程序、真实下降步及相邻键的严格性由 Agda 检查，全序嵌入的组合论证见文末。

```agda
{-# OPTIONS --safe --without-K #-}
module Survey.W4PTOOrderMap where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; _+_; _^_; s≤s; z≤n)
open import Data.Nat.DivMod using (_/_; _%_)
import Data.Nat.Properties as N
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (refl; inspect; [_])
open import WVOne using (T₀)
open import OCF.Align.Value using (_≼_; ≼-trans)
import Survey.W4PTOAddresses as A

-- 解正数 2^a(2b+1)。零键不编码合法票据。
unpair : ℕ → ℕ → ℕ × ℕ
unpair zero m = 0 , 0
unpair (suc f) m with m % 2
... | zero = let a , b = unpair f (m / 2) in suc a , b
... | suc _ = 0 , m / 2

unroute : ℕ → ℕ → List ℕ
unroute zero m = []
unroute (suc f) zero = []
unroute (suc f) (suc m) = let a , b = unpair (suc m) (suc m) in a ∷ unroute f b

codeRoute : ℕ → List ℕ
codeRoute k = let a = proj₁ (unpair k k) in unroute a a

record Step (y : T₀) : Set where
  constructor chosen
  field
    src dst : T₀
    hop : A.Hop y dst
    fits : src ≼ dst

select : ∀ {x y} → x ≼ y → List ℕ → Maybe (Step y)
select {x} {y} d ns with A.land x ns | inspect (A.land x) ns
... | nothing | _ = nothing
... | just z | [ found ] = just (chosen z q e h)
  where
  actual = proj₁ (A.recover x ns found)
  picked = A.pick {x = z} {y = y} (≼-trans {b = x} (A.below actual) d)
  q = proj₁ picked
  e = proj₁ (proj₂ picked)
  h = proj₂ (proj₂ picked)

shape : ∀ {x y} → x ≼ y → ℕ → ℕ
shape d k with select d (codeRoute k)
... | nothing = 0
... | just s = A.pathCode (A.route (Step.hop s))

module Siblings (a : ℕ → ℕ) where
  copy : ℕ → ℕ
  copy zero = 0
  copy (suc k) = suc (A.pair (a k) (copy k))
  out = λ k → A.pair (a k) (copy k)

  power-positive : ∀ n → 1 ≤ 2 ^ n
  power-positive zero = N.≤-refl
  power-positive (suc n) = N.≤-trans (power-positive n) (N.m≤m+n (2 ^ n) _)
  copy≤key : ∀ a b → b ≤ A.pair a b
  copy≤key a b = N.≤-trans (N.≤-trans (N.m≤m+n b b) (N.n≤1+n (b + b)))
    (N.≤-trans (N.m≤m+n (suc (b + b)) 0) (N.*-monoˡ-≤ (suc (b + b)) (power-positive a)))
  rising : ∀ k → out k < out (suc k)
  rising k = copy≤key (a (suc k)) (copy (suc k))

encode : ∀ {x y} → x ≼ y → A.Trail → Maybe A.Trail
encode d [] = just []
encode d (p ∷ ps) with select d (proj₁ p)
... | nothing = nothing
... | just s with encode (Step.fits s) ps
...   | nothing = nothing
...   | just qs = just ((A.route (Step.hop s) , Siblings.copy (shape d) (A.key p)) ∷ qs)

address : ∀ {x y} → x ≼ y → A.Node → Maybe A.Node
address d nothing = just nothing
address d (just []) = nothing
address d (just (p ∷ ps)) with encode d (p ∷ ps)
... | nothing = nothing
... | just qs = just (just qs)
```

对任意票 p，codeRoute(key(p)) 是其原路径。对正数 m，偶数时除以 2，奇数时返回奇部的一半向下取整；每次递归输入严格缩小。解出非空路径的尾码也严格小于路径码，因此两个自然数燃料都够用。无效的零键在排号时可以占一位，合法票的键都为正。

固定一个已到达的节点对及其比较证据。Agda 的 select 用源端真实一步得到严格余量，从目标取一次真实下降，并保留端点的比较证据。真实票的输出键就是 out(k)，因为改变副本号不改变地址求值。rising 保证整个兄弟次序严格保持，即使中间有未使用的整数键。相同输入前缀得到相同输出前缀；首个不同键处严格保序，真延长仍是真延长，另加的最小元映到最小元。有限长度归纳同时给出合法性和单射。因此对可执行树及可执行的比较证据，address 是 Aₓ 到 Aᵧ 的递归严格保序嵌入，其在所有合法有限输入上停机、保域及保序是一条真算术句。ACA₀ 配合这条算术事实可以逐项转换任意降链，包括无限次换兄弟的假想降链。[原地址序](W4PTOAddresses.lagda.md)
