# YiXVReadFinitePath
> 验收文件。档位：编译定理。有限末段的复合、偏移与转成原层间路径的交换律；不使用函数外延。
> 跟踪 YiLegPath 的原计算；不改树、折叠、UR、比较器。未交完整极限／节点世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadFinitePath where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiXVReadFinitePathInput as F

compose : ∀ {a b c} {p : a P.⊑ b} {q : b P.⊑ c} → F.Finite p → F.Finite q → F.Finite (P.⊑-trans p q)
compose fp F.self = fp
compose fp (F.ins fq) = F.ins (compose fp fq)
compose fp (F.inl {f = f} n fq) = F.inl {f = f} n (compose fp fq)
map : ∀ a {b c} {q : b P.⊑ c} → F.Finite q → F.Finite (P.⊕⊑ a q)
map a F.self = F.self
map a (F.ins fq) = F.ins (map a fq)
map a (F.inl {f = f} n fq) = F.inl {f = λ n → a S.⊕ f n} n (map a fq)

map-compose : ∀ a {b c d} (p : b P.⊑ c) {q : c P.⊑ d} → F.Finite q →
  P.⊕⊑ a (P.⊑-trans p q) ≡ P.⊑-trans (P.⊕⊑ a p) (P.⊕⊑ a q)
map-compose a p F.self = refl
map-compose a p (F.ins fq) = cong P.ins (map-compose a p fq)
map-compose a p (F.inl n fq) = cong (P.inl n) (map-compose a p fq)
to-compose : ∀ {a b c} (p : a P.⊑ b) {q : b P.⊑ c} → F.Finite q →
  P.⊑→≤ (P.⊑-trans p q) ≡ P._∙_ (P.⊑→≤ p) (P.⊑→≤ q)
to-compose p F.self = refl
to-compose p (F.ins fq) = cong P.ins (to-compose p fq)
to-compose p (F.inl n fq) = cong (P.inl n) (to-compose p fq)
```
