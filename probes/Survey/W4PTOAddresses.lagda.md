# W4 下降地址的可计算线序

第四层。对零层读值，地址的一步由有限个极限分支号及一次取前驱组成。给出有效性判定、与真实步的双向对应、严格比较见证的地址提取，并在原 W4 闭项上实填。线序的序型在文末作经典计算。

```agda
{-# OPTIONS --safe --without-K #-}
module Survey.W4PTOAddresses where

open import Data.Nat.Base as N using (ℕ; zero; suc; _+_; _*_; _^_; _<ᵇ_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Bool.Base using (Bool; false; true; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import WVOne using (T₀; read)
import W4Fold as W
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼; z≼; s≼s; ≼-refl)

data Hop : T₀ → T₀ → Set where
  pred : ∀ {x} → Hop (L.suc x) x
  via : ∀ {f y} (n : ℕ) → Hop (f n) y → Hop (L.lim f) y

route : ∀ {x y} → Hop x y → List ℕ
route pred = []
route (via n h) = n ∷ route h

land : T₀ → List ℕ → Maybe T₀
land L.zero ns = nothing
land (L.suc x) [] = just x
land (L.suc x) (_ ∷ _) = nothing
land (L.lim f) [] = nothing
land (L.lim f) (n ∷ ns) = land (f n) ns

exact : ∀ {x y} (e : Hop x y) → land x (route e) ≡ just y
exact pred = refl
exact (via n e) = exact e

recover : ∀ x ns {y} → land x ns ≡ just y → Σ (Hop x y) (λ e → route e ≡ ns)
recover L.zero ns ()
recover (L.suc x) [] refl = pred , refl
recover (L.suc x) (_ ∷ _) ()
recover (L.lim f) [] ()
recover (L.lim f) (n ∷ ns) eq with recover (f n) ns eq
... | e , d = via n e , cong (n ∷_) d

below : ∀ {x y} → Hop x y → L.suc y ≼ x
below pred = ≼-refl _
below (via n e) = ≼l n (below e)

least : ∀ (x y : T₀) → (∀ {z} → Hop x z → L.suc z ≼ y) → x ≼ y
least L.zero y f = z≼
least (L.suc x) y f = f pred
least (L.lim xs) y f = l≼ λ n → least (xs n) y (λ e → f (via n e))

pick : ∀ {x y : T₀} → L.suc x ≼ y → Σ T₀ (λ z → Hop y z × x ≼ z)
pick (s≼s d) = _ , pred , d
pick (≼l n d) with pick d
... | z , e , h = z , via n e , h

Ticket = List ℕ × ℕ
Trail = List Ticket

follow : T₀ → Trail → Maybe T₀
follow x [] = just x
follow x ((ns , _) ∷ ps) with land x ns
... | nothing = nothing
... | just y = follow y ps

after : ∀ x ps {y} → follow x ps ≡ just y → ∀ {z} (e : Hop y z) i →
  follow x (ps ++ ((route e , i) ∷ [])) ≡ just z
after x [] refl e i rewrite exact e = refl
after x ((ns , a) ∷ ps) eq e i with land x ns
... | just y = after y ps eq e i
... | nothing with eq
...   | ()

-- nothing 编码另加的最小元，空链仅用作读取程序的初始状态。
Node = Maybe Trail

inhabited : Maybe T₀ → Bool
inhabited nothing = false
inhabited (just _) = true

member : T₀ → Node → Bool
member x nothing = true
member x (just []) = false
member x (just (p ∷ ps)) = inhabited (follow x (p ∷ ps))

pair : ℕ → ℕ → ℕ
pair a b = (2 ^ a) * suc (b + b)

pathCode : List ℕ → ℕ
pathCode [] = 0
pathCode (n ∷ ns) = pair n (pathCode ns)

key : Ticket → ℕ
key (ns , i) = pair (pathCode ns) i

kb : Trail → Trail → Bool
kb [] ys = false
kb (x ∷ xs) [] = true
kb (x ∷ xs) (y ∷ ys) with key x <ᵇ key y | key y <ᵇ key x
... | true | _ = true
... | false | true = false
... | false | false = kb xs ys

less : Node → Node → Bool
less nothing nothing = false
less nothing (just _) = true
less (just _) nothing = false
less (just xs) (just ys) = kb xs ys

self-less : ∀ i → (i <ᵇ i) ≡ false
self-less zero = refl
self-less (suc i) = self-less i

extension : ∀ ps p → kb (ps ++ (p ∷ [])) ps ≡ true
extension [] p = refl
extension (a ∷ ps) p rewrite self-less (key a) = extension ps p

W4-domain = member (read W.EBOᶜ)
W4-order = less
```

**经典纸面计算。** `pair` 用正整数的 2 进赋值编码第一坐标、奇部编码第二坐标。有限列表的空码为 0，非空码严格大于尾码，故可递归解码并检查规范编码。对固定一步，改变副本号会产生无穷多个不同的自然数键。有限链的验收通过 `land`、`follow` 进行。`exact` 与 `recover` 保证每一步恰好走到指定的真实前驱。`read W.EBOᶜ` 是闭合的可执行树；把有限列表输入上述布尔程序，可按其有限定义的归约规则求值。由此得到 W4 地址域和序的递归表示。需要原始递归的谓词时，给每个域元素附上确定性验收机首次停机接受的完整计算记录，局部逐步核验，比较时略去记录。键比较和核对记录都是原始递归的。这里的有效性只对该闭项及同样给出有效数据的树作断言。

令 α 为根的序数值。由 `below`、`least`，α 等于一步后继值 β 的 β+1 的上确界，所以无穷严格延长不可能。按 α 归纳计算所有非空合法链的 Kleene–Brouwer 序型。α=0 时此序为空。α>0 时，按首键的自然数顺序求块之和：一步到达值 β 的子树贡献其非空链再加该节点，每块在 ω^β 与 ω^β+1 之间。任何有限部分和严格低于 ω^α。同一 β 的块出现无穷次，整和至少为 ω^(β+1)，故恰为 ω^α。在最前面加一个最小元后，α=0 时得到 1，α>0 时仍为 ω^α。由此得到原 W4 地址线序的序型 **ω^Y**。[原地址构造](../LOG.md#w4-kb-comparison)
