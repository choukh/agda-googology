# 塔第 2 项一站: 值参照与陈述

> 验收文件 (读记号). 参照是记号沿基本列造的树 `Rt` (不经 `OCF.Align.Level` 的层号, 那里没有 Ω 结点层号). 塔第 2 项 `Tw₂ = twᶜ 2` 一站的陈述: `Row₂` (参照 ψ₀(Ω_{Ω_Ω}), 即出口 `ebo-lower` 在 k = 3 的一行), 小站 `Step₂⁺` (ψ₀(Ω_{Ω+1})) 与 `Step₂` (ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})); 都只是 `Set`, 未证.
> 编译定理, 无前提: 三个参照都带标签 (`lab₃`, `lab₃₁`, `lab₊`); 典范一族 `PH` 对基本列封闭 (`closed-PH`), 逐行下界给出 EBO 参照树的下界 (`endpoint`); `Row₂` 推出 `Step₂` 与 BTBO 那一行 (`row₂→step`, `row₂→btbo`), `Step₂⁺` 推出 BTBO 那一行 (`step⁺→btbo`). 有限测试: 塔层号与槽位的读法, 记号基本列的头两项.
> 不否定什么, 不涉及上界. 参照的读法来自记号项; 树侧闭项 `twᶜ n` 的读法是判断. 出口在 [YiMonoExit](YiMonoExit.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRefTw2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import OCF.Lean.YiFreshBlock renaming (L to LF; T to TF)
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshValRead using (T₀; read)
open import OCF.Lean.YiUpLegal using (twᶜ; EBOᶜ)
open import OCF.Lean.YiUpValTw1 using (Tw1′)

import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; cof; cω; fsn; EBOψ; []<)
open import OCF.Align.EboLeanBase using (NF; n[]; n∷; nψ; GB; GB[]; gp; gtl; gh; gw; gc; c∷; c[]; lt→<ᴾ)
open import OCF.Align.EboLeanTree using (tree; hc; hc-tower; EBO-tree′)
import OCF.Align.EboLeanLab as LL
open import OCF.Lean.YiMonoExit using (toL; Closed; ebo-lower)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans)
```

## 闭项与层号的读法 (有限测试)

塔第 n 项的闭项是 `twᶜ n`; 第 1 项就是 `YiUpValTw1` 的 `Tw1′`. 第 2 项的层号是以第 1 层的树为分支的 Ω 结点, 第 1 项的层号是以可数树为分支的 Ω 结点; 第 0 支恰是 `tw 1`.

```agda
Tw₂ : Tr zero
Tw₂ = twᶜ 2

_ : twᶜ 1 ≡ Tw1′
_ = refl

_ : tw 2 ≡ Ωₗ (tw 1) (λ c → tw 1 ⊕ ↑ (tw 1) c)
_ = refl

_ : at (tw 2) (inj₁ (inj₁ tt)) ≡ tw 1
_ = refl

_ : Br (tw 2) (inj₁ (inj₁ tt)) ≡ Tr (tw 1)
_ = refl

_ : Br (tw 1) (inj₁ (inj₁ tt)) ≡ Tr zero
_ = refl

_ : tw 1 ⊕ ↑ (tw 1) zero ≡ tw 1
_ = refl

_ : Ωt (tw 2) ≡ Ω (inj₁ (inj₁ tt)) (λ c → up zero c (Ωt (tw 1 ⊕ ↑ (tw 1) c)))
_ = refl
```

## 参照: 记号沿基本列造的树

`Rt h` 是 `HC` 推导造的树搬到参照框架的第 0 层, 与 `read` 的值域相同. 具体的参照一律写成 `Rt` 作用在推导上, 引理对推导一般地陈述再代入: 给具体参照另起名字, 比较时检查器会沿良基证明展开 `hc-tower` (实测 6G 堆耗尽).

```agda
Rt : ∀ {t} → HC t → T₀
Rt h = toL (tree h)

hω-inv : ∀ {t} → HC t → cof t ≡ cω → ∀ n → HC (fsn t n)
hω-inv (h0 e)   w n with trans (sym e) w
... | ()
hω-inv (h1 e _) w n with trans (sym e) w
... | ()
hω-inv (hω _ h) w n = h n

fs≼ : ∀ {t} (h : HC t) (w : cof t ≡ cω) n → Rt (hω-inv h w n) ≼ Rt h
fs≼ (h0 e)   w n with trans (sym e) w
... | ()
fs≼ (h1 e _) w n with trans (sym e) w
... | ()
fs≼ (hω _ h) w n = ≼l n (≼-refl (Rt (h n)))

tree-≼ : ∀ {t t′} → t ≡ t′ → (h : HC t) (h′ : HC t′) → Rt h ≼ Rt h′
tree-≼ refl (h0 _)   h′ = z≼
tree-≼ refl (h1 e h) (h0 e′) with trans (sym e) e′
... | ()
tree-≼ refl (h1 e h) (h1 _ h′) = s≼s (tree-≼ refl h h′)
tree-≼ refl (h1 e h) (hω e′ _) with trans (sym e) e′
... | ()
tree-≼ refl (hω e h) (h0 e′) with trans (sym e) e′
... | ()
tree-≼ refl (hω e h) (h1 e′ _) with trans (sym e) e′
... | ()
tree-≼ refl (hω _ h) (hω _ h′) = l≼ (λ n → ≼l n (tree-≼ refl (h n) (h′ n)))
```

## 出口的典范一族

`PH t X`: t 有 `HC` 推导, 其树不高于 X. 它对 `pred`/`fsn` 封闭, 所以 `ebo-lower` 的前提化为逐行的 `Rt (hc-tower k) ≼ Y`.

```agda
PH : E.T → T₀ → Set
PH t X = Σ (HC t) λ h → Rt h ≼ X

PH-Rt : ∀ {t} (h : HC t) → PH t (Rt h)
PH-Rt h = h , ≼-refl (Rt h)

closed-PH : Closed PH
closed-PH = record { step1 = st1 ; stepω = stω }
  where
  st1 : ∀ {t X} → PH t X → cof t ≡ E.c1 → Σ T₀ λ X′ → PH (E.pred t) X′ × (L.suc X′ ≼ X)
  st1 (h0 e , q) w with trans (sym e) w
  ... | ()
  st1 (h1 _ h , q) w = Rt h , PH-Rt h , q
  st1 (hω e _ , q) w with trans (sym e) w
  ... | ()
  stω : ∀ {t X} → PH t X → cof t ≡ cω → ∀ n → Σ T₀ λ X′ → PH (fsn t n) X′ × (X′ ≼ X)
  stω (h , q) w n = Rt (hω-inv h w n) , PH-Rt (hω-inv h w n) , ≼-trans (fs≼ h w n) q

endpoint : (Y : T₀) → (∀ k → Rt (hc-tower k) ≼ Y) → toL EBO-tree′ ≼ Y
endpoint Y r = ebo-lower closed-PH Y (λ k → Rt (hc-tower k) , PH-Rt (hc-tower k) , r k)

endpoint-sat : ∀ k → Rt (hc-tower k) ≼ toL EBO-tree′
endpoint-sat k = ≼l k (≼-refl (Rt (hc-tower k)))
```

## ψ₀(Ω_{Ω+1}) 的标准形

`G₀` 收集到的参数都是 0, 所以条件全是 `[]<`.

```agda
t₊ : E.T
t₊ = E.ψ [] (E.Ωs (E.Ωt (E.natT 1))) ∷ []

nf₊ : NF t₊
nf₊ = n∷ (nψ n[] nfA g₀) tt n[]
  where
  nf1 : NF (E.natT 1)
  nf1 = n∷ (nψ n[] n[] GB[]) tt n[]
  nfS : NF (E.sucT (E.Ωt (E.natT 1)))
  nfS = n∷ (nψ nf1 n[] GB[]) (inj₁ (lt→<ᴾ E.𝟏 (E.ψ (E.natT 1) []) refl)) nf1
  nfA : NF (E.Ωs (E.Ωt (E.natT 1)))
  nfA = n∷ (nψ nfS n[] GB[]) tt n[]
  g₀ : GB [] (E.Ωs (E.Ωt (E.natT 1))) (E.Ωs (E.Ωt (E.natT 1)))
  g₀ (gp (gh _)) = []<
  g₀ (gp (gw _ (gp (gh _)))) = []<
  g₀ (gp (gw _ (gp (gw _ (gp (gh _)))))) = []<
  g₀ (gp (gw _ (gp (gw _ (gp (gw _ ()))))))
  g₀ (gp (gw _ (gp (gw _ (gp (gc _ ()))))))
  g₀ (gp (gw _ (gp (gw _ (gtl ())))))
  g₀ (gp (gw _ (gp (gc _ ()))))
  g₀ (gp (gw _ (gtl (gp (gh _))))) = []<
  g₀ (gp (gw _ (gtl (gp (gw _ ())))))
  g₀ (gp (gw _ (gtl (gp (gc _ ())))))
  g₀ (gp (gw _ (gtl (gtl ()))))
  g₀ (gp (gc _ ()))
  g₀ (gtl ())

h₊ : HC t₊
h₊ = hc nf₊ (c∷ c[])
```

三个参照都带记号的标签 (树的基本列与记号逐项一致), 由 `EboLeanLab.lab-tree` 直接给出.

```agda
lab₃ : LL.Labᴸ (tree (hc-tower 3)) (EBOψ 3)
lab₃ = LL.lab-tree (hc-tower 3)

lab₃₁ : LL.Labᴸ (tree (hω-inv (hc-tower 3) refl 1)) (fsn (EBOψ 3) 1)
lab₃₁ = LL.lab-tree (hω-inv (hc-tower 3) refl 1)

lab₊ : LL.Labᴸ (tree h₊) t₊
lab₊ = LL.lab-tree h₊
```

## 一站的陈述

`Row₂`: 出口在 k = 3 的一行落在塔第 2 项之下. `Step₂`: 那一行的第 1 个基本列项 (第 0 项是 BTBO 那一行). `Step₂⁺`: ψ₀(Ω_{Ω+1}). `Into n`: 塔第 n 项不高于 ψ₀(Λ) 的闭项, 把行搬到终点 `endpoint (read EBOᶜ)` 要它.

```agda
Row₂ : Set
Row₂ = Rt (hc-tower 3) ≼ read Tw₂

Step₂ : Set
Step₂ = Rt (hω-inv (hc-tower 3) refl 1) ≼ read Tw₂

Step₂⁺ : Set
Step₂⁺ = Rt h₊ ≼ read Tw₂

Into : ℕ → Set
Into n = read (twᶜ n) ≼ read EBOᶜ
```

## 陈述之间的推出

```agda
row₂-exit : Row₂ → Σ T₀ λ X → PH (EBOψ 3) X × (X ≼ read Tw₂)
row₂-exit r = Rt (hc-tower 3) , PH-Rt (hc-tower 3) , r

row₂→step : Row₂ → Step₂
row₂→step r = ≼-trans (fs≼ (hc-tower 3) refl 1) r

row₂→btbo : Row₂ → Rt (hc-tower 2) ≼ read Tw₂
row₂→btbo r = ≼-trans (tree-≼ refl (hc-tower 2) (hω-inv (hc-tower 3) refl 0)) (≼-trans (fs≼ (hc-tower 3) refl 0) r)

step⁺→btbo : Step₂⁺ → Rt (hc-tower 2) ≼ read Tw₂
step⁺→btbo r = ≼-trans (tree-≼ refl (hc-tower 2) (hω-inv h₊ refl 0)) (≼-trans (fs≼ h₊ refl 0) r)
```

## 记号一侧 (有限测试)

两个参照的第 0 个基本列项都是 BTBO 那一行 ψ₀(Ω_Ω); 第 1 项分别是 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}}) 与 ψ₀(ψ_Ω(Ω_Ω)), 后者已经塌缩到层 Ω.

```agda
_ : cof (EBOψ 3) ≡ cω
_ = refl

_ : fsn (EBOψ 3) 0 ≡ EBOψ 2
_ = refl

_ : fsn (EBOψ 3) 1 ≡ E.ψ [] (E.Ωt (E.Ωt (EBOψ 2))) ∷ []
_ = refl

_ : cof t₊ ≡ cω
_ = refl

_ : fsn t₊ 0 ≡ EBOψ 2
_ = refl

_ : fsn t₊ 1 ≡ E.ψ [] (E.ψ (E.Ωt (E.natT 1)) (E.Ωt (E.Ωt (E.natT 1))) ∷ []) ∷ []
_ = refl
```
