# YiWall：只读树的两个恒分支检验

本篇只提取所求 ψ 必须通过的检验，不构造 ψ。两棵根的第一支同为 1，
分支分别恒为 1 和 2；二者不读守卫证据，Legal.irr 均为 refl。
下界合法时，它们都是原 Carry／Legal／Only0 域的真实源。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiWallTree where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; false; true)
open import Data.Unit.Base using (tt)
import Data.Empty
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as C
import OCF.Align.YiK2Base as A
import OCF.Align.YiK2bBase as B
import OCF.Align.YiK2cIrr as I
import OCF.Align.YiK2Stop as S
open import OCF.Align.YiDispBase using (one; e-first)
open F using (module G)

unitLF doubleLF : F.LF
unitLF = F.suc F.zero
doubleLF = F.suc unitLF

child : Bool → F.LF
child false = unitLF
child true = doubleLF

child-carry : ∀ b → C.Carry (child b)
child-carry false = tt
child-carry true = tt

child-legal : ∀ b → V.Legal (child b)
child-legal false = tt
child-legal true = tt

child-only : ∀ b → B.Only0 (child b)
child-only false = tt
child-only true = tt

first-child : ∀ b → V.CP unitLF (child b)
first-child false = V.self
first-child true = V.suc V.self

node : A.R → Bool → F.LF
node c b = F.lc F.zero c unitLF (λ η e → child b)

node-legal : ∀ c b → V.Legal (node c b)
node-legal c b = tt , (λ η e → first-child b) ,
  (λ η e η′ e′ d → V.self) , (λ η e e′ → refl) , tt ,
  (λ η e → child-legal b)

node-carry : ∀ c b → F.Lgl F.zero c → C.Carry (node c b)
node-carry c b lc =
  ((one e-first , tt , tt , (λ η e → C.forget (child-carry b))) ,
   lc , tt , (λ η e bounds → child-carry b))

node-only : ∀ c b → B.Only0 (node c b)
node-only c b = tt , (λ η e → child-only b)

node-source : ∀ c b → F.Lgl F.zero c → B.Source0
node-source c b lc = I.pack (node c b) (node-carry c b lc)
  (node-legal c b) (node-only c b)

-- 全层起点等价；证书恰好提供反向所需的下界合法性。
start-iff : ∀ k c →
  (C.Point k c → F.Lgl k c) × (F.Lgl k c → C.Point k c)
start-iff k c =
  (λ { (η , p , lη) → F.lgl-cp k p lη }) ,
  (λ lc → c , (inj₁ refl , lc))

good-closed-source : B.Source0
good-closed-source = node-source A.one false tt

-- 原全 Legal 域的否定仍然成立；这个坏源不在 Carry 域。
bad-node-legal : V.Legal (node S.bad-bound false)
bad-node-legal = node-legal S.bad-bound false

bad-node-no-carry : C.Carry (node S.bad-bound false) → Data.Empty.⊥
bad-node-no-carry r = S.no-bound-legal (C.lower r)
```

## 从完整目标抽取检验，保留“只读树”的字面含义

`ProbeRows run` 仅要求 run 在 1、2 的指定值，以及上述恒分支根的 gt 行。
它是必要子集，不是替换旧接口。只读树前提写成整个算子
`ψ ≡ (λ s → run (term (original s)))`；这个等式仅运输算子，不用外延。

```agda
record ProbeRows (run : F.LF → A.R) : Set where
  field
    unit-row : run unitLF ≡ A.successor A.one
    double-row : run doubleLF ≡ A.successor (A.successor A.one)
    constant-gt : ∀ c b → F.Lgl F.zero c →
      run (node c b) ≡ G.lim (λ n → run (child b))

from-fold : ∀ run (d : B.FoldRows0) →
  B.FoldRows0.ψ d ≡ (λ s → run (C.term (B.original s))) → ProbeRows run
from-fold run d tree = record
  { unit-row = unit-row
  ; double-row = double-row
  ; constant-gt = constant-gt
  }
  where
  ψ = B.FoldRows0.ψ d

  term-call : ∀ x r l q → ψ (I.pack x r l q) ≡ run x
  term-call x r l q = cong (λ h → h (I.pack x r l q)) tree

  zero-row : run F.zero ≡ A.one
  zero-row = trans (sym (term-call F.zero tt tt tt))
    (B.FoldRows0.zero-row d tt tt tt)

  unit-row : run unitLF ≡ A.successor A.one
  unit-row = trans (sym (term-call unitLF tt tt tt))
    (trans (B.FoldRows0.suc-row d F.zero tt tt tt)
      (cong A.successor (trans (term-call F.zero tt tt tt) zero-row)))

  double-row : run doubleLF ≡ A.successor (A.successor A.one)
  double-row = trans (sym (term-call doubleLF tt tt tt))
    (trans (B.FoldRows0.suc-row d unitLF tt tt tt)
      (cong A.successor (trans (term-call unitLF tt tt tt) unit-row)))

  constant-gt : ∀ c b → F.Lgl F.zero c →
    run (node c b) ≡ G.lim (λ n → run (child b))
  constant-gt c b lc = trans
    (sym (term-call (node c b) r l q))
    (trans (B.FoldRows0.gt-row d c unitLF (λ η e → child b) r l q)
      (cong (λ h → G.lim (λ n → h (B.branch0 r l q
        (C.iterate (B.FoldRows0.gt-generator d c unitLF
          (λ η e → child b) r l q) (C.start0-B r) n)))) tree))
    where
    r = node-carry c b lc
    l = node-legal c b
    q = node-only c b
```

`good-closed-source` 实填合法下界的正面源，`bad-node-legal` 则给原 Legal
并不含起点的闭实例。二者不把全 `FoldRows0` 冒称非空。
下篇的全域 ProbeRows 可满足性只给经典外延模型说明，并明确标纸面档。
