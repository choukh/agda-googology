# 路线乙 O1：带字面公共上界的链支配接口

**第 4 层的接口草案。** 这里的 `ChainDom` 只要求实际生成域内、实际链步
上的支配，不要求折叠对任意同值输入单调。`Frame` 是一次折叠调用的
环境：目标层与源层都是同一合法界的字面位置。候选必须把 `Position`
实例化为自身的字面位置关系，不能把任意值序命名为位置后算作验收。

值前沿仍为 ψ₀(Ω_{Ω·ω²})。本篇不新造闭项，不给任何候选新增值下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO1Chain where

open import OCF.Lean.CRwBase using (Cd)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.NegFold1Base using (≤ᵛ-trans)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase using (hs)
open import OCF.Align.EboLeanDef using (T; cof; c1; cω; pred; fsn; EBOψ)
open import OCF.Align.TerminalFoldAccept using (reference)
open import OCF.Align.TreeLevelsO1Cover using (GeneratedCover; module Generated)

record TreeSystem : Set₁ where
  field
    Level World : Set
    Position : World → Level → Level → Set
    LegalBound : World → Level → Set
    Object : World → Level → Set
    observe : ∀ {w i} → Object w i → Cd

record Frame (S : TreeSystem) : Set where
  open TreeSystem S
  field
    world : World
    bound : Level
    legal : LegalBound world bound
    target source : Level
    target-in : Position world target bound
    source-in : Position world source bound

module Types (S : TreeSystem) where
  open TreeSystem S
  open Frame
  Input : Frame S → Set
  Input F = Object (world F) (source F)
  Output : Frame S → Set
  Output F = Object (world F) (target F)

record FoldSystem : Set₁ where
  field
    trees : TreeSystem
  open Types trees
  field
    fold : (F : Frame trees) → Input F → Output F
    Generated : (F : Frame trees) → Input F → Set
    ChainStep : (F : Frame trees) → Input F → Input F → Set

record ChainDom (S : FoldSystem) : Set where
  open FoldSystem S
  open TreeSystem trees
  open Types trees
  field
    chain-lower : (F : Frame trees) (x y : Input F) →
      Generated F x → Generated F y → ChainStep F x y →
      observe (fold F x) ≤ᵛ observe (fold F y)
```

`LimCall` 将记号的一个基本列步与树侧的一次真实链步联系起来。
左右两端的比较是值比较；里面的层号对仅出现在 `Frame` 的共同界下。
它没有把完整 EBO 下界当作字段。实际 γ 链的生成与回灌证明属于候选实填。

```agda
record LimCall (S : FoldSystem) (a b : Cd) : Set where
  open FoldSystem S
  open TreeSystem trees
  open Types trees
  field
    frame : Frame trees
    left right : Input frame
    left-generated : Generated frame left
    right-generated : Generated frame right
    step : ChainStep frame left right
    lower : a ≤ᵛ observe (fold frame left)
    upper : observe (fold frame right) ≤ᵛ b

module Dom (S : FoldSystem) (D : ChainDom S) where
  open FoldSystem S
  open ChainDom D
  open LimCall

  limit-lower : ∀ {a b} → LimCall S a b → a ≤ᵛ b
  limit-lower c = ≤ᵛ-trans (lower c)
    (≤ᵛ-trans
      (chain-lower (frame c) (left c) (right c)
        (left-generated c) (right-generated c) (step c))
      (upper c))
```

## 从本地链调用导出阶段无关的覆盖条件

`ChainInterpretation` 的解释、域封闭及后继律不从 `ChainDom` 免费得到。
尤其全塔上界须由候选另证；只写出下面的条件定理，不能宣称候选已经
容纳了 EBO 解释的值。

```agda
record ChainInterpretation (S : FoldSystem) (A : Set) (observe : A → Cd) : Set₁ where
  field
    Domain : T → Set
    ι : ∀ {t} → Domain t → A
    predecessor : ∀ {t} → Domain t → cof t ≡ c1 → Domain (pred t)
    branch : ∀ {t} → Domain t → cof t ≡ cω → ∀ n → Domain (fsn t n)
    tower : ∀ k → Domain (EBOψ k)
    successor-law : ∀ {t} (d : Domain t) (e : cof t ≡ c1) →
      hs (observe (ι (predecessor d e))) ≤ᵛ observe (ι d)
    limit-call : ∀ {t} (d : Domain t) (e : cof t ≡ cω) n →
      LimCall S (observe (ι (branch d e n))) (observe (ι d))

module Accept {S : FoldSystem} {A : Set} {observe : A → Cd}
  (I : ChainInterpretation S A observe) where
  open ChainInterpretation I

  as-cover : ChainDom S → GeneratedCover A observe
  as-cover D = record
    { Domain = Domain
    ; ι = ι
    ; predecessor = predecessor
    ; branch = branch
    ; tower = tower
    ; successor-law = successor-law
    ; limit-law = λ d e n → Dom.limit-lower S D (limit-call d e n)
    }

  terminal : (D : ChainDom S) → ∀ {X : Cd} →
    (∀ k → observe (ι (tower k)) ≤ᵛ X) → reference ≤ᵛ X
  terminal D = Generated.terminal (as-cover D)
```

**封顶清单（草案审计）。** `Level`、`World`、`Object` 都是结构参数；
没有固定到 `Ht` 或某个高层 `HB S₀`。`observe` 的值域 `Cd` 是终点的
可数输出观察，不用作高层回灌坐标。此版尚不处理输出回灌改变世界的
调用，因此不宣称它已经适用于全部三候选；候选需要这种调用时另给
带运输证据的接口，不能默默把高层输出经 `Cd` 送回去。
