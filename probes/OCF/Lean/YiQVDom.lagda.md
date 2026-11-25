# 统一读回域 (一): 可达状态, 最小的树域, 以及树域被迫取全体

> 验收文件 (读记号). 判决: 编译定理, 不改树、折叠、合法性. 可达状态 `Reach` (根与嵌入一步生成) 上 `Good` 成立; `YiSOLow.Domˢ` 的最小实例 `minˢ` (含塔各项的 Ω 树, 含于任何带 `RootIn` 的域).
> 审查 F 路 G7 的回答 (编译): Ω 树的结点槽位只有下标侧顶槽位与后继形状孩子侧顶槽位 (`Ωt-sΩ`, `Ωt-sS`); 但被折叠的树不都在 Ω 树一族里: 后继形状孩子层上最小域含全体树 (`full-succ`), 塔第 2 项里一个层号为 `tw 1` (Ω 形状) 的可达状态上含全体树 (`full₂`). 所以任何可用的 `Domˢ` 在该状态上都是全体 (`dom-full₂`), `RebRow` 在其上就是对一切材料的陈述 (`reb-forced`).
> 不否定什么: 没有值的否定; 说的是 `Domˢ` 这种 "随状态的树域" 收不窄, 不是换基候选掉值. `root-bdᴰ`: 读法取读回域 `Dom` 时根状态的槽位条件对一切 n 成立. 入口: [YiQVUni](YiQVUni.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQVDom where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiGTGen using (weakenᴿ)
open import OCF.Lean.YiGIInst using (pre)
open import OCF.Lean.YiGLDom using (Dom; dom-top)
open import OCF.Lean.YiWREnd using (baseᴮ; rbΛ; ψ-⊵ᴮ)
open import OCF.Lean.YiSOLow
open import OCF.Lean.YiSOEnd using (rootˢ; module End)
```

## 可达状态

```agda
data Reach : ∀ {a} → Stˢ a → Set where
  rt : ∀ n → Reach (rootˢ n)
  sp : ∀ {s h} {st : Stˢ (nd s h)} → Reach st → (c : Ch s) (x : Tr (nd s h)) → Reach (stepˢ st c x)

reach-good : ∀ {a} {st : Stˢ a} → Reach st → Good a (proj₁ (proj₂ st))
reach-good (rt n) = good-tw n
reach-good (sp {s} {h} {st} rc c x) = good-ch s h (proj₁ (proj₂ st)) (reach-good rc) c
```

## 最小的树域

`Mn st x`: 由塔各项根状态上的 Ω 树出发, 按 `Domˢ` 的四条封闭 (`lowAll` 的递归实际用到的四条) 生成. 它是 `Domˢ` 的实例, 含于任何带 `RootIn` 的域; 状态都可达.

```agda
data Mn : ∀ {a} → Stˢ a → Tr a → Set where
  m-rt : ∀ n → Mn (rootˢ n) (proj₁ (Ωt (tw n)))
  m-dw : ∀ {a} {st : Stˢ a} {x x′ : Tr a} → a ⊢ x ◃ x′ → Mn st x′ → Mn st x
  m-nd : ∀ {a} {st : Stˢ a} (p : Pos a) (g : Br a p → Tr a) → Mn st (Ω p g) → ∀ c → Mn st (g c)
  m-ch : ∀ {s h} {st : Stˢ (nd s h)} (c : Ch s) (x : Tr (nd s h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
       → Mn st (up x c y e) → Mn (stepˢ st c x) y
  m-em : ∀ {g} {st : Stˢ (nd sL g)} (m n : ℕ) (x : Tr (nd sL g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y) (u : g m ≤ g n)
       → Mn st (up x m y e) → Mn (stepˢ st n x) (proj₁ (emb (g n) (proj₂ (proj₁ st) n) u (y , e)))

minˢ : Domˢ
minˢ = record { Dm = Mn ; dw = λ _ → m-dw ; dnd = λ _ → m-nd ; dch = λ _ → m-ch ; dem = λ _ → m-em }

min-root : End.RootIn minˢ
min-root = m-rt

min-least : (𝒟 : Domˢ) → End.RootIn 𝒟 → ∀ {a} {st : Stˢ a} {x : Tr a} → Mn st x → Domˢ.Dm 𝒟 st x
min-least 𝒟 ri (m-rt n) = ri n
min-least 𝒟 ri (m-dw d m) = Domˢ.dw 𝒟 _ d (min-least 𝒟 ri m)
min-least 𝒟 ri (m-nd p g m c) = Domˢ.dnd 𝒟 _ p g (min-least 𝒟 ri m) c
min-least 𝒟 ri (m-ch c x y e m) = Domˢ.dch 𝒟 _ c x y e (min-least 𝒟 ri m)
min-least 𝒟 ri (m-em m n x y e u d) = Domˢ.dem 𝒟 _ m n x y e u (min-least 𝒟 ri d)

mn-reach : ∀ {a} {st : Stˢ a} {x : Tr a} → Mn st x → Reach st
mn-reach (m-rt n) = rt n
mn-reach (m-dw d m) = mn-reach m
mn-reach (m-nd p g m c) = mn-reach m
mn-reach (m-ch c x y e m) = sp (mn-reach m) c x
mn-reach (m-em m n x y e u d) = sp (mn-reach d) n x
```

## G7: Ω 树的结点槽位, 与被迫进域的树

Ω 树的顶结点: Ω 形状上是下标侧顶槽位, 分支是孩子的 Ω 树嵌入 (左部为零); 后继形状上是孩子侧顶槽位, 分支是 `suc c` 的嵌入, c 取遍孩子层的一切树. 后一条使孩子层的一切树进域.

```agda
Ωt-sΩ : ∀ k h → proj₁ (Ωt (nd (sΩ k) h)) ≡ Ω (inj₁ (inj₁ tt)) (λ c → up zero c (proj₁ (Ωt (h c))) (proj₂ (Ωt (h c))))
Ωt-sΩ k h = refl

Ωt-sS : ∀ h → proj₁ (Ωt (nd sS h)) ≡ Ω (inj₂ (tt , inj₁ tt)) (λ c → up zero tt (suc c) (z◃ c ◃s))
Ωt-sS h = refl

Ω-child : ∀ {k h} {st : Stˢ (nd (sΩ k) h)} → Mn st (proj₁ (Ωt (nd (sΩ k) h))) → ∀ c → Mn (stepˢ st c zero) (proj₁ (Ωt (h c)))
Ω-child {k} {h} m c = m-ch c zero (proj₁ (Ωt (h c))) (proj₂ (Ωt (h c))) (m-nd (inj₁ (inj₁ tt)) _ m c)

full-succ : ∀ {h} {st : Stˢ (nd sS h)} → Mn st (proj₁ (Ωt (nd sS h))) → (c′ : Tr (h tt)) → Mn (stepˢ st tt zero) c′
full-succ m c′ = m-dw ◃s (m-ch tt zero (suc c′) (z◃ c′ ◃s) (m-nd (inj₂ (tt , inj₁ tt)) _ m c′))
```

塔第 1 项: 孩子 `suc x` 的孩子层 (层号 `↑ zero x`) 上的可达状态含该层一切树. 塔第 2 项: 孩子 `suc zero` 的孩子层就是 `tw 1` (Ω 形状, 带换基证据), 该可达状态含 `tw 1` 的一切树.

```agda
st₁ : (x : Tr zero) → Stˢ (zero ⊕ ↑ zero x)
st₁ x = stepˢ (stepˢ (rootˢ 1) (suc x) zero) tt zero

full₁ : ∀ x (c′ : Tr (zero ⊕ ↑ zero x)) → Mn (st₁ x) c′
full₁ x = full-succ (Ω-child (m-rt 1) (suc x))

st₂ : Stˢ (tw 1)
st₂ = stepˢ (stepˢ (rootˢ 2) (suc zero) zero) tt zero

full₂ : (c′ : Tr (tw 1)) → Mn st₂ c′
full₂ = full-succ (Ω-child (m-rt 2) (suc zero))

dom-full₂ : (𝒟 : Domˢ) → End.RootIn 𝒟 → (c′ : Tr (tw 1)) → Domˢ.Dm 𝒟 st₂ c′
dom-full₂ 𝒟 ri c′ = min-least 𝒟 ri (full₂ c′)
```

## 后果: 任何可用域上的 `RebRow` 含它在 `st₂` 上对一切材料的实例

`st₂` 的换基证据是塔第 1 项的 `Schema` (地板第 0 层). `RebAll`: `YiSOLow.Sys.RebRow` 在一个状态上去掉域前提的陈述.

```agda
S₁ : Schema zero (λ c → zero ⊕ ↑ zero c)
S₁ = schema (tw 0) (↑ (tw 0)) (Ok-tw 0) self (OkO↑ (tw 0) (tw 0) (Ok-tw 0) self) (λ c → refl)

RebAll : ∀ {k h} (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rs : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h)) → Set
RebAll {k} {h} o S rs B = (c : Tr k) {u : E.T} (x : Tr (nd (sΩ k) h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ∀ j (c′ : Tr k) (v : j ≤ h c′) (fl : floor S ≤ j) (β′ : Tr⁺ j) κ K′ → GR.Rd j κ → GR.R j (E.ψ κ K′ ∷ []) (proj₁ β′)
  → GR.R (h c) u y
  → GR.R j (E.ψ κ (K′ ++ u) ∷ [])
      (proj₁ (seen S j (downOk (h c′) (proj₂ o c′) j v) fl β′ c ⊞ BS.ψ (h c) (proj₂ o c) (rs c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))

reb-forced : (𝒟 : Domˢ) → End.RootIn 𝒟 → Sys.RebRow 𝒟
  → RebAll (proj₁ st₂) S₁ (proj₂ (proj₁ (proj₂ st₂))) (proj₂ (proj₂ st₂))
reb-forced 𝒟 ri rr c x y e =
  rr (proj₁ st₂) S₁ (proj₂ (proj₁ (proj₂ st₂))) (proj₂ (proj₂ st₂)) c x y e (dom-full₂ 𝒟 ri (up x c y e))
```

## 根状态的槽位条件: 读法取读回域时对一切 n 成立

`YiSOEnd.RootBd` 对槽位层的一切 `GR.Nu` 读法量化; 读法落在 `YiGLDom.Dom` 里时它就是域上的 Leaf (`dom-top`) 加底不低于 Ω 树.

```agda
root-bdᴰ : ∀ n (p : Pos (tw n)) {κ} → Dom (at (tw n) p) κ
  → GR.R (at (tw n) p) (E.ψ κ [] ∷ []) (proj₁ (baseᴮ n (at (tw n) p) (posW (tw n) p)))
root-bdᴰ n p D = weakenᴿ (at (tw n) p) (dom-top D)
  (ψ-⊵ᴮ Λ Ok-Λ rbΛ (B₀ Λ) (at (tw n) p) (inc n (posW (tw n) p)) (Ωt (at (tw n) p)) (pre n))
```
