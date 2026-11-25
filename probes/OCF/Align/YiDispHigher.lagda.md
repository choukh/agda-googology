# 合法性与一次保留证据不足以覆盖高层坐标

这里检验推广的前提，不否定两类证据本身。取一个合法的Ω节点作层号 j，
第一支与所有分支均为0；目标 i=suc(suc j)。suc j 是 i 的真后继位置，
初始派发严格保留。Raw j 的合法 top 支读回 Ω_j，下一根却没有两类 DispEv。
失败已在第一支／top支的直接根，不依赖 Field 的额外下标或深层量词。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiDispHigher where

open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (Raw; Gd; Pre)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
open import OCF.Align.YiSpineCommon using (Common; common→spinal)
open import OCF.Align.YiRCountable using (Small)
open import OCF.Align.YiDispBase renaming (one to path)

one : Y.Level
one = Y.suc Y.zero

j : Y.Level
j = Y.node one (V.cO (Y.tree one)) Y.zero (λ _ _ → Y.zero)
  (λ _ _ → V.self) (λ _ _ _ _ _ → V.self) (λ _ _ _ → refl)

i source : Y.Level
i = Y.suc (Y.suc j)
source = Y.Ω (Y.suc j)

initial : DispEv (Y.tree i) (Y.tree j)
initial = structural (path e-suc)

initial-keep : choice initial ≡ keep
initial-keep = refl

initial-common : Common (Y.suc j) i
initial-common = i , V.suc V.self , V.self

root-slot : Pre (Y.tree j)
root-slot = inj₁ (inj₁ tt)

top : Raw (Y.tree j)
top = G.top

top-guard : Gd (Y.tree j) (V.cO (Y.tree j)) top
top-guard = inj₁ refl , tt

top-read : V.up (Y.tree j) top ≡ Y.tree (Y.Ω j)
top-read = refl

top-not-small : Small (V.up (Y.tree j) top) → ⊥
top-not-small ()

first-root : K.Field (Y.tree one) (Y.tree (Y.Ω j))
first-root = K.at

top-root : K.Field (Y.tree one) (V.up (Y.tree j) top)
top-root = K.at

two-not-i : CP (F.suc (Y.tree one)) (Y.tree i) → ⊥
two-not-i (V.suc (V.suc (V.fst ())))

i-not-two : CP (Y.tree i) (F.suc (Y.tree one)) → ⊥
i-not-two (V.suc (V.suc ()))

no-common : Common (Y.suc one) i → ⊥
no-common c with common→spinal {a = Y.suc one} {b = i} c
... | inj₁ p = two-not-i p
... | inj₂ p = i-not-two p

no-below-zero : ∀ {a} → Below a F.zero → ⊥
no-below-zero (path ())
no-below-zero (more p ())

no-below-j : Below (F.suc (Y.tree one)) (Y.tree j) → ⊥
no-below-j (path ())
no-below-j (more p e-first) = no-below-zero p
no-below-j (more p (e-branch η e)) = no-below-zero p

no-below-sj : Below (F.suc (Y.tree one)) (F.suc (Y.tree j)) → ⊥
no-below-sj (path ())
no-below-sj (more p e-suc) = no-below-j p

no-below : Below (F.suc (Y.tree one)) (Y.tree i) → ⊥
no-below (path ())
no-below (more p e-suc) = no-below-sj p

no-next-ev : DispEv (Y.tree i) (Y.tree one) → ⊥
no-next-ev (bounded B pj pi) = no-common (B , pj , pi)
no-next-ev (structural p) = no-below p

no-retained-domain : RetainedDomain (Y.tree i) j → ⊥
no-retained-domain r = no-next-ev (branch r top top-guard top-root)

-- 更弱的“只覆盖第一支的直接根”也失败，不靠Field的过量量词。
no-first-root : (DispEv (Y.tree i) (Y.tree one)) → ⊥
no-first-root = no-next-ev

-- 即使把lc.k也作为普通子树路径加入，派发量2仍未出现在目标i中。
data FullPos (a : F.LF) : F.LF → Set where
  p-self : FullPos a a
  p-suc : ∀ {x} → FullPos a x → FullPos a (F.suc x)
  p-lim : ∀ {f} n → FullPos a (f n) → FullPos a (F.lim f)
  p-index : ∀ {k c t g} → FullPos a k → FullPos a (F.lc k c t g)
  p-first : ∀ {k c t g} → FullPos a t → FullPos a (F.lc k c t g)
  p-branch : ∀ {k c t g} η e → FullPos a (g η e) → FullPos a (F.lc k c t g)

no-full-zero : FullPos (F.suc (Y.tree one)) F.zero → ⊥
no-full-zero ()

no-full-one : FullPos (F.suc (Y.tree one)) (Y.tree one) → ⊥
no-full-one (p-suc p) = no-full-zero p

no-full-j : FullPos (F.suc (Y.tree one)) (Y.tree j) → ⊥
no-full-j (p-index p) = no-full-one p
no-full-j (p-first p) = no-full-zero p
no-full-j (p-branch η e p) = no-full-zero p

no-full-position : FullPos (F.suc (Y.tree one)) (Y.tree i) → ⊥
no-full-position (p-suc (p-suc p)) = no-full-j p
```

所有 Level 都随构造有 Legal；initial、initial-common、top-guard 均已实填。
root-slot 确实存在，却不提供派发量2到i的真子树路径。
no-full-position还排除了包含lc.k的普通子树路径；不能把槽位的Raw类型
或节点标注直接当成该后继层号的方向证据。
这是树侧全合法域上的保留递归反例，不是从 EBOψ k 提取的 Actual 反例，
也没有证明在合法性之外再携带覆盖证据的生成域不可能。
