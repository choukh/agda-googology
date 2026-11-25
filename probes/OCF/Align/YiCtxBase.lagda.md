# 单一合法上下文界：Ctx 与全分支 Inv 的共同接口

本篇只读树，不读记号，也不导入 C 线模块。
Ctx 保存一个合法界及有限树环境中所有成员的 CP 位置。
Inv 进一步要求当前合法树的所有 Ω 字段都在这个界上，包括所有合法分支内的字段。

lc k 的共尾度是 Ω_{k+1}，故实际派发字段取 suc k；新增γ目标为它的前驱 k。
Field 记录字段 k 的语法位置，field-pos 给 suc k 的 CP，不把两者混同。
该接口定稿后只增不改；全分支量词不缩成仅活动路径或另一个可入域。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCtxBase where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as A using (All)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.YiLevelBase as Y

data Field (k : LF) : LF → Set where
  at : ∀ {c t g} → Field k (F.lc k c t g)
  in-suc : ∀ {t} → Field k t → Field k (F.suc t)
  in-lim : ∀ {f} n → Field k (f n) → Field k (F.lim f)
  in-index : ∀ {j c t g} → Field k j → Field k (F.lc j c t g)
  in-first : ∀ {j c t g} → Field k t → Field k (F.lc j c t g)
  in-branch : ∀ {j c t g} (η : Raw j) (e : Gd j c η) →
    Field k (g η e) → Field k (F.lc j c t g)

record Ctx (Env : List Y.Level) : Set where
  constructor ctx
  field
    bound : Y.Level
    env-pos : All (λ x → CP (Y.tree x) (Y.tree bound)) Env
open Ctx public

record Inv (Env : List Y.Level) (current : Y.Level) : Set where
  constructor invariant
  field
    context : Ctx Env
    field-pos : ∀ {k} → Field k (Y.tree current) → CP (F.suc k) (Y.tree (bound context))
open Inv public
```

Env 在树侧取 List Level，每个成员随身合法；这里没有给原始树事后补码。
所有比较都需从这份共享界位置证据取参数，不能只凭按值在界之下。
