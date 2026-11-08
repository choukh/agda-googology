# 原高层闭项分支的生成实例

全部定理按原坐标结构递归，含 Ω；不要求任意 g 自然性。
原 Ω₃² 及 top₃ 的固定前缀未删除。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedBuild where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldClosed
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)
open import OCF.Align.EventReturnCodeBuild using (shape-self)
open import OCF.Align.EventGeneratedIf

add : ∀ {S} {a a′ b b′ : HB S} → Shape a a′ → Shape b b′ → Shape (a ⊞ b) (a′ ⊞ b′)
add p sz = p
add p (ss q) = ss (add p q)
add p (sl q) = sl (λ n → add p (q n))
add p (so q) = so (λ c → add p (q c))

low : ∀ {x y} → Shape x y → Shape (nb₀ x) (nb₀ y)
low sz = sz
low (ss p) = ss (low p)
low (sl p) = sl (λ n → low (p n))
low (so {κ = tt} p) = so (λ c → low (p c))

nb : ∀ {b b′ s s′} → Shape b b′ →
  (∀ {x y h h′} → Shape x y → Shape h h′ → Shape (s x h) (s′ y h′)) →
  ∀ {x y} → Shape x y → Shape (nbᴱ b s x) (nbᴱ b′ s′ y)
nb p f sz = p
nb p f (ss q) = f q (nb p f q)
nb p f (sl q) = sl (λ n → nb p f (q n))
nb p f (so {κ = inj₁ tt} q) = so (λ c → nb p f (q c))
nb p f (so {κ = inj₂ tt} q) = so (λ c → nb p f (q c))

make : ∀ κ g → LgB (At.source κ g) →
  (∀ {x y} → Shape x y → Shape (g x) (g y)) → At.Generated κ g
make κ g l f = record
  { legal-source = l ; branch = f
  ; pair = λ a H J r → record
    { layers = f r ; left-bound = At.position κ g a H ; right-bound = At.position κ g a J } }

second : At.Generated κ₀ nb₀
second = make κ₀ nb₀ Lg-Ω₂ᴱ low

third : At.Generated κ₁ (nbᴱ hz (λ _ h → hs h))
third = make κ₁ _ Lg-Ω₃ᴱ (nb sz (λ _ p → ss p))

square : At.Generated κ₁ (nbᴱ hz (λ _ h → h ⊞ Ω₃ᴱ))
square = make κ₁ _ Lg-Ω₃² (nb sz (λ _ p → add p (shape-self Ω₃ᴱ)))

prefix : ∀ κ g → At.Generated κ g → At.Generated κ (λ c → three ⊞ g c)
prefix κ g h = make κ _ (Lg-top₃ (At.source κ g) (At.Generated.legal-source h))
  (λ p → add (shape-self three) (At.Generated.branch h p))

-- 最终 fgh 的原高层源正是此项，而不是只测一个低节点。
closed-square : At.Generated κ₁ (λ c → three ⊞ nbᴱ hz (λ _ h → h ⊞ Ω₃ᴱ) c)
closed-square = prefix κ₁ _ square
```
