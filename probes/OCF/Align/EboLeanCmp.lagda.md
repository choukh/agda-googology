# EboLeanCmp: 精简版与现有 `WfFsn.EBO-tree` 逐点相同

> **记号侧验收工作**, 读记号与标签, 不进成品, **不计入** [EboLean](EboLean.lagda.md) 的行数表 (它导入旧路线, 只为核对).
>
> **结论 (编译过的定理).**
>
> 1. `fsn≡ : fsn t n ≡ E.fsn t n` 对一切项: 精简版的裸值基本列与 EBO 带证书版本去掉证书的值相同.
> 2. `tree≅ : ⟦ EBO-tree′ ⟧ ≅ WfFsn.EBO-tree` (`Ordᶜ zero` 上的 $\cong$), 于是 `fgh≡ : FGH EBO-tree′ n ≡ FGH WfFsn.EBO-tree n` 对一切 $n$. 证明: 精简版的树经 `⟦_⟧` 搬到 `Ordᶜ zero` 后有现有的 `Lab` (`lab⟦⟧`), 再用 `Lab-uniq`.
>
> 编译要把归档拷贝加进 `-i` (只因 `WfFsn` 导入归档). `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLeanCmp where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import OCF.Align.EBO as E
open import OCF.Align.EboLeanDef
import OCF.Align.EboLeanTree as LT
open LT using (Ord; tree; hc-tower; EBO-tree′)
open import OCF.BTBO using (module Ord-Ord)
import OCF.Align.Level as L
open import OCF.Align.Correspond using (Lab; l0; l1; lω)
open import OCF.Align.Stage2 using (Lab-uniq)
import OCF.Align.WfFsn as W
```

## §1 `fsn` 的值相同

```agda
fsn≡  : ∀ t n → fsn t n ≡ E.fsn t n
fsn≡ˣ : ∀ x xs n → fsn (x ∷ xs) n ≡ E.trm (E.fsn↓ x xs n)
fsn≡0 : ∀ w ws c (e : cof (w ∷ ws) ≡ c) n → fsn0 (w ∷ ws) c n ≡ E.trm (E.fsn↓0 w ws c e n)
fsn≡₊ : ∀ u y ys c (e : cof (y ∷ ys) ≡ c) n → fsn₊ u (y ∷ ys) c n ≡ E.trm (E.fsn↓₊ u y ys c e n)
fsn≡c : ∀ u y ys ν (e : cof (y ∷ ys) ≡ cΩ ν) m n → fsnc u (y ∷ ys) ν m n ≡ E.trm (E.fsn↓c u y ys ν e m n)

fsn≡ [] n = refl
fsn≡ (x ∷ xs) n = fsn≡ˣ x xs n

fsn≡ˣ x (y ∷ ys) n = cong (x ∷_) (fsn≡ˣ y ys n)
fsn≡ˣ (ψ u (y ∷ ys)) [] n = fsn≡₊ u y ys (cof (y ∷ ys)) refl n
fsn≡ˣ (ψ (w ∷ ws) []) [] n = fsn≡0 w ws (cof (w ∷ ws)) refl n
fsn≡ˣ 𝟏 [] n = refl

fsn≡0 w ws c0 e n = refl
fsn≡0 w ws c1 e n = refl
fsn≡0 w ws cω e n = cong (λ z → ψ z [] ∷ []) (fsn≡ˣ w ws n)
fsn≡0 w ws (cΩ ν) e n = cong (λ z → ψ z [] ∷ []) (sym (E.fsT↓-trm (w ∷ ws) e (E.natT<Ωs n ν)))

fsn≡₊ u y ys c0 e n = refl
fsn≡₊ u y ys c1 e n = sym (E.rep-trm u (E.pred-< (y ∷ ys) e) n)
fsn≡₊ u y ys cω e n = cong (λ z → ψ u z ∷ []) (fsn≡ˣ y ys n)
fsn≡₊ u y ys (cΩ ν) e n = fsn≡c u y ys ν e (cmpᵀ (sucT ν) u) n

fsn≡c u y ys ν e gt n =
  cong (λ z → ψ u z ∷ [])
       (sym (trans (E.fsT↓-trm (y ∷ ys) e (E.dec (E.γ↓ (y ∷ ys) ν e n))) (cong (fsT (y ∷ ys)) (E.γ↓-trm (y ∷ ys) ν e n))))
fsn≡c u y ys ν e lt n = cong (λ z → ψ u z ∷ []) (sym (E.fsT↓-trm (y ∷ ys) e (E.natT<Ωs n ν)))
fsn≡c u y ys ν e eq n = cong (λ z → ψ u z ∷ []) (sym (E.fsT↓-trm (y ∷ ys) e (E.natT<Ωs n ν)))
```

## §2 树搬到 `Ordᶜ zero`, 标签, 与 `WfFsn.EBO-tree` 比较

```agda
⟦_⟧ : Ord → L.Ordᶜ L.zero
⟦ LT.zero ⟧  = L.zero
⟦ LT.suc a ⟧ = L.suc ⟦ a ⟧
⟦ LT.lim f ⟧ = L.lim (λ n → ⟦ f n ⟧)

iter≡ : ∀ {f g : ℕ → ℕ} → (∀ m → f m ≡ g m) → ∀ a k → Ord-Ord.iter f a k ≡ iter g a k
iter≡ h a zero    = refl
iter≡ {g = g} h a (suc k) = trans (h _) (cong g (iter≡ h a k))

FGH-⟦⟧ : ∀ a n → L.FGH ⟦ a ⟧ n ≡ LT.FGH a n
FGH-⟦⟧ LT.zero    n = refl
FGH-⟦⟧ (LT.suc a) n = iter≡ (FGH-⟦⟧ a) n n
FGH-⟦⟧ (LT.lim f) n = FGH-⟦⟧ (f n) n

lab⟦⟧ : ∀ {t} (h : HC t) → Lab ⟦ tree h ⟧ t
lab⟦⟧ (h0 e)   = l0 e L.z≅
lab⟦⟧ (h1 e h) = l1 e (L.≅-refl⁰ _) (lab⟦⟧ h)
lab⟦⟧ {t} (hω e h) = lω e (L.≅-refl⁰ _) (λ n → subst (Lab ⟦ tree (h n) ⟧) (fsn≡ t n) (lab⟦⟧ (h n)))

tree≅ : ⟦ EBO-tree′ ⟧ L.≅ W.EBO-tree
tree≅ = L.l≅ (λ k → Lab-uniq (lab⟦⟧ (hc-tower k)) (W.ebo-lab k))

fgh≡ : ∀ n → LT.FGH EBO-tree′ n ≡ L.FGH W.EBO-tree n
fgh≡ n = trans (sym (FGH-⟦⟧ EBO-tree′ n)) (L.FGH-≅ tree≅ n)
```
