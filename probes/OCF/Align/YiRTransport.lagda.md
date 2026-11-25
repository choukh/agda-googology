# γ 证明缺少的扩界运输与种子兼容

本篇审查本轮采用原 Gd 域的分支相对 Path，不返回第五轮的全树单界。
先给具有实际前提实例的反例：Path 不能只凭旧界到新界的 CP 全局运输。
再检查非 Small 层 ν=Ω 的标准γ种子。失败是单个选定分支与旧环境不兼容，
不是要求两个不同分支共享一棵新界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRTransport where

open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All as A using ()
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (Raw; Gd)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (CP; CP-tr)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
import OCF.Align.YiCtxStep as S
import OCF.Align.YiCtxFork as W
open import OCF.Align.YiSpineCommon using (Common; common→spinal)
open import OCF.Align.YiRBase
open import OCF.Align.YiRCountable using (Small; raw0-small)
open import OCF.Align.YiRStep using (ΩΩ; omega-omega)

one-in-b : CP (F.suc F.zero) (Y.tree W.b-level)
one-in-b = V.lim 1 V.self

b-small : Small (Y.tree W.b-level)
b-small = raw0-small (G.lim W.raw-nat)

no-b-path : Path W.b-level (Y.tree ΩΩ) → ⊥
no-b-path (root , first , branches) with branches W.ηa W.guard-a
... | B′ , p , q = W.no-common
  (B′ , CP-tr (V.suc V.self) (proj₁ q) , p)

Monotone : Set
Monotone = ∀ B B′ → CP (Y.tree B) (Y.tree B′) → ∀ t → Path B t → Path B′ t

no-unconditional-raise : Monotone → ⊥
no-unconditional-raise raise = no-b-path
  (raise (Y.suc Y.zero) W.b-level one-in-b (Y.tree ΩΩ) omega-omega)
```

omega-omega 已实填旧 Path，one-in-b 已实填界扩展；二者同时成立。
这里没有把 Monotone 当作定理加入接口。

```agda
ν : Y.Level
ν = S.Ω₁

ν-not-small : Small (Y.tree ν) → ⊥
ν-not-small ()

ν-not-finite : W.Finite (Y.tree ν) → ⊥
ν-not-finite ()

ν-not-a : CP (Y.tree ν) W.a → ⊥
ν-not-a (V.lim n p) = ν-not-finite (W.finite-position p (W.fs (W.nat-finite n)))

a-not-ν : CP W.a (Y.tree ν) → ⊥
a-not-ν (V.fst p) = W.lim-not-finite (W.finite-position p (W.fs W.fz))

no-common-ν-a : Common ν W.a-level → ⊥
no-common-ν-a c with common→spinal {a = ν} {b = W.a-level} c
... | inj₁ p = ν-not-a p
... | inj₂ p = a-not-ν p

seed : Raw (Y.tree ν)
seed = G.top

seed-guard : Gd (Y.tree ν) (V.cO (Y.tree ν)) seed
seed-guard = inj₁ refl , tt

seed-tree : Y.Level
seed-tree = Y.Ω ν

seed-read : V.up (Y.tree ν) seed ≡ Y.tree seed-tree
seed-read = refl

target-position : ∀ {E} (c : K.Ctx (ν ∷ E)) → CP (Y.tree ν) (Y.tree (K.bound c))
target-position c with K.env-pos c
... | p A.∷ ps = p

no-gamma-seed : ∀ {E} → InvR (ν ∷ E) seed-tree → ⊥
no-gamma-seed i with proj₂ (proj₂ (path i)) W.ηa W.guard-a
... | B′ , p , q = no-common-ν-a
  (B′ , CP-tr (target-position (context i)) p , CP-tr (V.suc V.self) (proj₁ q))

seed-context : K.Ctx (ν ∷ Y.zero ∷ [])
seed-context = K.ctx (Y.suc ν)
  (V.suc V.self A.∷ V.suc (V.fst (V.suc V.self)) A.∷ A.[])

gamma-source : Y.Level
gamma-source = Y.Ω (Y.suc ν)

no-gamma-source : ∀ {E} → InvR E gamma-source → ⊥
no-gamma-source i = no-gamma-seed
  (relative (S.adjoin (context i) ν (CP-tr (V.suc V.self) (proj₁ (path i))))
    (proj₁ (proj₂ (path i))))
```

标准种子 seed 本身有合法守卫，seed-tree 与 gamma-source 都由合法 Ω 构造，
seed-context 也实填。不能认证的是它们组合后的 Path：在目标 ν 已留在环境中时，
进入 seed-tree 的单个合法零层 ηa 支，就须同时容纳 ν 与该支字段 a。
no-common-ν-a 排除任何合法新界，即使不同分支完全允许不同界也不能补这一个支。

这没有给出“具有 InvR 输入的某个实际 γ 步输出不保 InvR”的反例。
no-gamma-source 恰说明这个候选排除了所需的更高正规源；不能把空的输入域
当成全层 γ 保持定理。一般 γ 的保持本轮仍未完成。
若改用依赖当前上下文的 Ad／shift，须另给实际坐标的可入性及相应运输律；
本篇没有为此把任意高层界塞进 Raw 0，也没有改树或继续写 ψ。
