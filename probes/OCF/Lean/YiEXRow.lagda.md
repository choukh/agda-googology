# 出口的低三行接到终点闭项

> 验收文件 (读记号与标签). 编译定理, 无前提: `row₂-btbo : Rt (hc-tower 2) ≼ D.BTBOᴵ` (记号树与 BTBO 参照同标签, `Lab-uniq`), 于是出口第 2 行对主线合法块 F2 的终点闭项成立 (`row₂`); 第 0, 1 行沿记号的第 0 个基本列项下降得出 (`row₀`, `row₁`), 汇总为 `rows`.
> `fsn≡` 重写自 `EboLeanCmp` (那里导入归档才编译), 不改原文. 两处 `T₀` 与 `≼` 同一个, 由 `endpoint-at` 与 `row₂` 的类型检查确认.
> 不否定什么, 不涉及上界; 第 k ≥ 3 行未证 (`endpoint-from` 是以它们为前提的条件定理). 出口在 [YiRefTw2](YiRefTw2.lagda.md), 终点下界在 [YiEBBtbo](YiEBBtbo.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEXRow where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import OCF.Align.EBO as E
open import OCF.Align.EboLeanDef using (T; ψ; Cof; c0; c1; cω; cΩ; cof; cmpᵀ; sucT; fsT; gt; lt; eq;
  fsn; fsn0; fsn₊; fsnc; HC; h0; h1; hω; EBOψ)
open import OCF.Align.EboLeanTree using (hc-tower; EBO-tree′)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
open import OCF.Align.Correspond using (Lab; l0; l1; lω)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; fs≼; tree-≼; endpoint)
import OCF.Lean.YiFreshValRead as F
import OCF.Lean.YiLSRead as S
open S using (read)
open import OCF.Lean.YiLegFold using (EBOᶜ)
open import OCF.Lean.YiEBBtbo using (btbo-EBO)
```

## `T₀` 同一个

```agda
_ : F.T₀ ≡ S.T₀
_ = refl

_ : S.T₀ ≡ L.Ordᶜ L.zero
_ = refl
```

## 精简版的基本列与 EBO 的相同 (重写自 `EboLeanCmp` §1)

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
fsn≡ˣ E.𝟏 [] n = refl

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

## 参照树带标签, 与同标签的树 `≼`

`labR h`: `Rt h` 的基本列与记号逐项一致 (对 `toL` 重做 `EboLeanCmp.lab⟦⟧`).

```agda
labR : ∀ {t} (h : HC t) → Lab (Rt h) t
labR (h0 e)   = l0 e L.z≅
labR (h1 e h) = l1 e (L.≅-refl⁰ _) (labR h)
labR {t} (hω e h) = lω e (L.≅-refl⁰ _) (λ n → subst (Lab (Rt (h n))) (fsn≡ t n) (labR (h n)))

Rt≼Lab : ∀ {t X} (h : HC t) → Lab X t → Rt h ≼ X
Rt≼Lab h l = ≅→≼ (Lab-uniq (labR h) l)
```

## 第 2 行

```agda
row₂-btbo : Rt (hc-tower 2) ≼ D.BTBOᴵ
row₂-btbo = Rt≼Lab (hc-tower 2) BTBO-label

row₂ : Rt (hc-tower 2) ≼ read EBOᶜ
row₂ = ≼-trans row₂-btbo btbo-EBO
```

## 第 0, 1 行

记号一侧 `fsn (EBOψ (k+1)) 0 ≡ EBOψ k` 对 k = 0, 1 是 `refl`, 所以参照树逐行由第 0 个基本列项下降.

```agda
down₁ : Rt (hc-tower 1) ≼ Rt (hc-tower 2)
down₁ = ≼-trans (tree-≼ refl (hc-tower 1) (hω-inv (hc-tower 2) refl 0)) (fs≼ (hc-tower 2) refl 0)

down₀ : Rt (hc-tower 0) ≼ Rt (hc-tower 1)
down₀ = ≼-trans (tree-≼ refl (hc-tower 0) (hω-inv (hc-tower 1) refl 0)) (fs≼ (hc-tower 1) refl 0)

row₁ : Rt (hc-tower 1) ≼ read EBOᶜ
row₁ = ≼-trans down₁ row₂

row₀ : Rt (hc-tower 0) ≼ read EBOᶜ
row₀ = ≼-trans down₀ row₁

rows : ∀ k → k ≤ 2 → Rt (hc-tower k) ≼ read EBOᶜ
rows zero z≤n = row₀
rows (suc zero) (s≤s z≤n) = row₁
rows (suc (suc zero)) (s≤s (s≤s z≤n)) = row₂
rows (suc (suc (suc _))) (s≤s (s≤s ()))
```

## 接进出口 (条件, 前提是未证的行)

`endpoint-at`: 出口在 `Y = read EBOᶜ` 处的实例 (类型检查确认两处 `T₀` 与 `≼` 同一个). `endpoint-from`: 前提只剩第 k ≥ 3 行; 它是否可满足就是未证的那部分, 这里不说.

```agda
endpoint-at : (∀ k → Rt (hc-tower k) ≼ read EBOᶜ) → toL EBO-tree′ ≼ read EBOᶜ
endpoint-at = endpoint (read EBOᶜ)

endpoint-from : (∀ k → Rt (hc-tower (suc (suc (suc k)))) ≼ read EBOᶜ) → toL EBO-tree′ ≼ read EBOᶜ
endpoint-from r = endpoint (read EBOᶜ) go
  where
  go : ∀ k → Rt (hc-tower k) ≼ read EBOᶜ
  go zero = row₀
  go (suc zero) = row₁
  go (suc (suc zero)) = row₂
  go (suc (suc (suc k))) = r k
```
