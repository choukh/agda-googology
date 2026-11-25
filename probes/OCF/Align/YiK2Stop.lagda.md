# K2 止损：原 Legal 不保证 gt 链有初项

**本篇检验的是原块全 `Legal` 域，不是规范 Ω 塔或 EBO 实际轨道。**
gt 行调用 `g γₙ eₙ`，所以不论加法步进选什么形状，都必须先有
`e₀ : Gd zero c γ₀`。原 Legal 的下界字段没有 `Lgl zero c`。
下面给出结点层恰为 0、完全合法、但没有任何可入坐标的源。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2Stop where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
open F using (module G)
open import OCF.Align.YiK2Base using (R; one; Point)

coordinate→bound-legal : ∀ c → Point c → F.Lgl F.zero c
coordinate→bound-legal c (η , p , lη) = F.lgl-cp F.zero p lη

bound-legal→coordinate : ∀ c → F.Lgl F.zero c → Point c
bound-legal→coordinate c lc = c , (inj₁ refl , lc)

bad-columns : ℕ → R
bad-columns zero = one
bad-columns (suc n) = G.zero

bad-bound : R
bad-bound = G.lim bad-columns

no-bound-legal : F.Lgl F.zero bad-bound → ⊥
no-bound-legal (st , lf) with st zero
... | inj₁ ()
... | inj₂ ()

no-coordinate : Point bad-bound → ⊥
no-coordinate p = no-bound-legal (coordinate→bound-legal bad-bound p)

body : (η : R) → F.Gd F.zero bad-bound η → F.LF
body η e = F.zero

source : F.LF
source = F.lc F.zero bad-bound F.zero body

source-legal : V.Legal source
source-legal = tt , (λ η e → V.self) , (λ η e η′ e′ d → V.self) ,
  (λ η e e′ → refl) , tt , (λ η e → tt)

record GtChain (c : R) : Set where
  field
    points : ℕ → R
    guards : ∀ n → F.Gd F.zero c (points n)

no-gt-chain : GtChain bad-bound → ⊥
no-gt-chain p = no-coordinate (GtChain.points p zero , GtChain.guards p zero)

-- 全 Legal 域上的必要接口；这里只要求初项，没有预设增长或 ψ 的方程。
record StartAll : Set where
  field
    initial : ∀ c t (g : (η : R) → F.Gd F.zero c η → F.LF) →
      V.Legal (F.lc F.zero c t g) → Point c

no-start-all : StartAll → ⊥
no-start-all p = no-coordinate (StartAll.initial p bad-bound F.zero body source-legal)
```

否定前提的可满足性：`source-legal` 是闭证明；`bad-bound` 是闭 Raw 0；
第 0 层比较只涉及 `one` 与 `zero` 的构造子反演，不调用全局比较器。
`StartAll` 本身正是被否定的必要接口，不将它冒称可满足的条件。
已有可入节点的接口有 [Base](YiK2Base.lagda.md) 的 `start` 实例。

**止损范围。** 失败在 gt 行“合法源能够启动原守卫链”这一前提，
不是加法增长失败，也不是已构造输出不合法。`no-gt-chain` 对任意链成立，
因此允许的一次链写法更换也无法给这个源补出初项；本轮不消耗这次更换。
不加 `Lgl c` 到 Legal，不改守卫、不用空分支默认值或 D8；
不将此否定外推为乙线、规范生成域或加法链本身不可能。

两条一般引理还精确给出缺口：有可入坐标当且仅当下界 `Lgl`。
若未来只在携带此证据的输入上做折叠，本反例不适用；那是输入域的选择，
不在本轮擅自把此字段加入原 Legal，也不声称该附加域的完整递归保持已证。
