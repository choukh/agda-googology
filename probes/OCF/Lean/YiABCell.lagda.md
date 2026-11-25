# 塔第 1 项那一格: 变体的链吸收上下文前缀

> 验收文件 (读记号). 判决: 编译定理. `YiWCTw1` 的那一格 (替身顶结点, 槽位层就是目标层, 精确参照 Ω₂) 换成 [YiABFold](YiABFold.lagda.md) 的替身状态 `sV`: 链点依赖左项 (`z1`, `¬free`, 对照 `YiWCTw1.zᴬ-free`); 对一切前缀 P, 只要外层折叠在 x 上朝目标层的值对着 ψ_1(P) (`mb`), 较弱链形状成立 (`weak-tw1ᵛ`, 条件定理; 步是 `stepᵛ`).
> 前提可满足: 底为 `B₀` 时 P 空 (`mb-nil`, x 是零树), P = 1 (`mb-one`, x 是 1), P = Ω₂ (`mb-Ω₂`, x 是孩子 1 上的一次嵌入; 用替身在结点上的像 `seen-node`). 不给出什么: 一般的 x 上 `mb` 是主系统朝目标层的保持, 没有证; 原替身上 P 非空的情形没有编译的否定; 不涉及值.
> 第 1 层自身折叠的保持直接用 `YiWCTw1.Self₁.LF`, 不重证. 高于目标层的槽位见文末 `top-free`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiABCell where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
import OCF.Lean.YiRBSib as RB
open import OCF.Lean.YiBSBase using (Rb; rb-tw; raiseO; Schema; floor; offsets; ok-offsets)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
open import OCF.Lean.YiGTGen using (weakᴿ; closeᴿ; Ω≤ψ; nextψ)
open import OCF.Lean.YiBLFold using (Sₙ; rcₙ; route-tw1; module Aux)
import OCF.Lean.YiBLFold as BLF
open import OCF.Lean.YiVALeaf using (nzs)
open import OCF.Lean.YiTBRow using (h₁)
open import OCF.Lean.YiBALemma using (collψ; fsT++)
open import OCF.Lean.YiBAEbo
open import OCF.Lean.YiXTIface
open import OCF.Lean.YiBAWeak
open import OCF.Lean.YiWCIface
open import OCF.Lean.YiWCTw1 using (𝟙; top₁; module Self₁)
import OCF.Lean.YiABFold as V
open import OCF.Lean.YiABFold using (Low; subB; seenᵛ)
```

## 变体的替身状态

系统, 槽位 `pᴬ`, 分支函数 `gᴬ` 与 `YiWCTw1.Tw1W` 相同; 只有状态换成变体换基行交给辅助系统的那一个: 底是 `subB`, 底值是变体折叠在 x 上的像. `row-is`: 变体折叠在孩子 1 上的换基行逐字是这个状态在替身上的像加尾项.

```agda
module Tw1V (B : Base (tw 1)) (β : Tr⁺ j₁) (x : Tr (tw 1)) where
  KA : ∀ {a} → Aux.Stᴬ j₁ a → E.T × E.T → Set
  KA _ K = KeepAt j₁ (proj₁ K)

  KB : ∀ {a} → BLF.Main.Stᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B j₁ (suc zero) self
                 (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero)) a → E.T × E.T → Set
  KB _ K = KeepAt j₁ (proj₁ K)

  open Tw1Neg B (E.T × E.T) apE KA (E.T × E.T) apE KB
  open AuxNode β x using (pᴬ; gᴬ)
  open WithR _≤ᵀ_ weakᴱ limᴱ nodeᴱ zeroᴱ succᴱ embᴱ (leRᴱ {j = j₁}) genᴱ using (chᴬ)
  open W gradedᴱ domsᴱ using (RefChainʳ; nodeʳ)

  Dˣ : Low j₁
  Dˣ i u′ = V.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B i (inc (suc zero) u′) (B i (inc (suc zero) u′)) x

  β′ : Tr⁺ j₁
  β′ = V.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B j₁ (inc (suc zero) self) β x

  Bˢ : Base (j₁ ⊕ ↑ zero (suc zero))
  Bˢ = subB j₁ (↑ zero (suc zero)) (raiseO zero j₁ (↑ zero (suc zero)) (lift zero (↑ zero (suc zero))) (ok-offsets (Sₙ 0) (suc zero))) Dˣ

  sV : Aux.Stᴬ j₁ (j₁ ⊕ ↑ zero (suc zero))
  sV = Aux.rbs (↑ zero (suc zero)) (Mn.oᴮ (suc zero)) Bˢ β′

  row-is : ∀ y e → V.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B j₁ (inc (suc zero) self) β (up x (suc zero) y e)
    ≡ Aux.Φᴬ j₁ sV (proj₁ (Ωt (j₁ ⊕ ↑ zero (suc zero))))
      ⊞ V.ψ (h₁ (suc zero)) (proj₂ (Ok-tw 1) (suc zero)) (rcₙ 0 (suc zero)) (B₀ _) zero (z≤ _) (Ωt zero) y
  row-is y e = refl

  neV : Aux.Evᴬ j₁ sV pᴬ → ⊥
  neV = Aux.top-noEv j₁ sS (λ _ → zero) (Mn.oᴮ (suc zero)) Bˢ β′ tt

  zⱽ : ℕ → Tr j₁
  zⱽ = proj₁ (chᴬ sV pᴬ gᴬ tt neV)
```

`WeakAt P`: 这一格上前缀为 P 的较弱链形状 (只为下面的实例写出类型).

```agda
  WeakAt : E.T → Set
  WeakAt P = RefChainʳ sysᴬ sV (𝟙 , P) pᴬ gᴬ Ω₂ (chᴬ sV pᴬ gᴬ tt neV)
```

## 形状: 链点吸收左项

第 1 个链点是外层折叠在 x 上朝目标层的值 (`Dˣ j₁ self`) 的后继; 之后每个链点是以它为底值的第 1 层自身折叠.

```agda
  start : Tr⁺ j₁
  start = Dˣ j₁ self

  Fˢ : Tr j₁ → Tr⁺ j₁
  Fˢ = RB.ψ j₁ (proj₂ (Mn.oᴮ (suc zero)) tt) (proj₂ (RB.rb-no (j₁ ⊕ ↑ zero (suc zero))) tt)
         (λ i u → RB.ψ (j₁ ⊕ ↑ zero (suc zero)) (Mn.oᴮ (suc zero)) (RB.rb-no _) Bˢ i (inc tt u) (Bˢ i (inc tt u)) zero) j₁ self start

  z1 : zⱽ 1 ≡ proj₁ (next⁺ start)
  z1 = refl

  zS : ∀ m → zⱽ (suc m) ≡ proj₁ (next⁺ (Fˢ (zⱽ m)))
  zS m = refl
```

## 链的步 (条件: 起点对着 ψ_1(P))

`mb` 是外层折叠朝目标层的保持在 x 上的结论 (上下文 ψ_1(P + ·), P 已含 x 的参照). 参照链 γ k = `γT (P ++ Ω₂) 𝟙 k`; 第 k 项不高于第 k+1 个链点.

```agda
  module Step (P : E.T) (mb : GR.R j₁ (E.ψ 𝟙 P ∷ []) (proj₁ start)) where
    module S₁ = Self₁ (proj₂ (Mn.oᴮ (suc zero)) tt) (proj₂ (RB.rb-no (j₁ ⊕ ↑ zero (suc zero))) tt)
      (λ i u → RB.ψ (j₁ ⊕ ↑ zero (suc zero)) (Mn.oᴮ (suc zero)) (RB.rb-no _) Bˢ i (inc tt u) (Bˢ i (inc tt u)) zero) P start mb

    γ : ℕ → E.T
    γ = E.γT (P ++ Ω₂) 𝟙

    γS : ∀ k → γ (suc k) ≡ E.ψ 𝟙 (P ++ γ k) ∷ []
    γS k = cong (λ z → E.ψ 𝟙 z ∷ []) (fsT++ P _ [] (γ k))

    stepᵛ : ∀ k m → GR.R j₁ (γ k) (zⱽ m) → GR.R j₁ (γ (suc k)) (zⱽ (suc m))
    stepᵛ k m r = subst (λ τ → GR.R j₁ τ (zⱽ (suc m))) (sym (γS k)) (weakᴿ j₁ (S₁.LF r) (◃l zero))

    chainᵛ : ∀ k → GR.R j₁ (γ k) (zⱽ (suc k))
    chainᵛ zero    = weakᴿ j₁ (closeᴿ j₁ (Ω≤ψ 𝟙 P) mb) (◃l zero)
    chainᵛ (suc k) = stepᵛ k (suc k) (chainᵛ k)

    weak-tw1ᵛ : WeakAt P
    weak-tw1ᵛ = γ , proj₁ cl , proj₂ cl , λ k → suc k , chainᵛ k
      where cl = collψ 𝟙 P Ω₂ {κ = 𝟙} refl refl
```

替身在结点上的像由较弱链形状给出 (`YiBAWeak.nodeʳ`): 各支是以 `β′` 为底值的第 1 层自身折叠的后继. 这给出替身的像对着 ψ_1(P′ + Ω₂), 其中 P′ 是底值 `β′` 的前缀 (`mβ`).

```agda
    module Node (P′ : E.T) (mβ : GR.R j₁ (E.ψ 𝟙 P′ ∷ []) (proj₁ β′))
                (same : ∀ a → E.ψ 𝟙 (P′ ++ a) ∷ [] ≡ E.ψ 𝟙 (P ++ a) ∷ []) where
      module Sβ = Self₁ (proj₂ (Mn.oᴮ (suc zero)) tt) (proj₂ (RB.rb-no (j₁ ⊕ ↑ zero (suc zero))) tt)
        (λ i u → RB.ψ (j₁ ⊕ ↑ zero (suc zero)) (Mn.oᴮ (suc zero)) (RB.rb-no _) Bˢ i (inc tt u) (Bˢ i (inc tt u)) zero) P′ β′ mβ

      seen-node : GR.R j₁ (E.ψ 𝟙 (P ++ Ω₂) ∷ []) (proj₁ (Aux.Φᴬ j₁ sV (Ω pᴬ gᴬ)))
      seen-node = nodeʳ sysᴬ limᴱ sV (𝟙 , P) pᴬ gᴬ (chᴬ sV pᴬ gᴬ tt neV) weak-tw1ᵛ
        (λ η c r → subst (λ τ → GR.R j₁ τ (proj₁ (Aux.Φᴬ j₁ sV (gᴬ c)))) (same η) (weakᴿ j₁ (Sβ.LF r) (◃l zero)))
```

## 对照 `zᴬ-free`

底取 `B₀` 时, x 取零树与取 1, 第 1 个链点不同 (前者是 Ω 树的后继, 后者是 Ω 树的后继的后继; `next⁺` 的第 0 项分别是 Ω 结点与 ℕ 极限).

```agda
hd : ∀ {ℓ} → Tr ℓ → Tr ℓ
hd (lim f a) = f zero
hd x         = x

Ω≢lim : ∀ {ℓ} {p : Pos ℓ} {g : Br ℓ p → Tr ℓ} {f a} → Ω p g ≡ lim f a → ⊥
Ω≢lim ()

¬free : (β : Tr⁺ j₁) → Tw1V.zⱽ (B₀ (tw 1)) β zero 1 ≡ Tw1V.zⱽ (B₀ (tw 1)) β (suc zero) 1 → ⊥
¬free β e = Ω≢lim (cong hd e)
```

## 前提可满足

`mb` 在 P 空 (x 是零树), P = 1 (x 是 1), P = Ω₂ (x 是孩子 1 上的一次嵌入, 用上面的 `seen-node`) 三处实填, 底都是 `B₀`. P = Ω₂ 时参照链第 1 项是 ψ_1(Ω₂ + Ω₁).

```agda
module Inst (β : Tr⁺ j₁) where
  module V0 = Tw1V (B₀ (tw 1)) β zero
  module V1 = Tw1V (B₀ (tw 1)) β (suc zero)

  mb-nil : GR.R j₁ (E.ψ 𝟙 [] ∷ []) (proj₁ V0.start)
  mb-nil = top₁

  mb-one : GR.R j₁ (E.ψ 𝟙 𝟙 ∷ []) (proj₁ V1.start)
  mb-one = nextψ j₁ 𝟙 [] 𝟙 refl (Ωt j₁) top₁

  weak-nil : V0.WeakAt []
  weak-nil = V0.Step.weak-tw1ᵛ [] mb-nil

  weak-one : V1.WeakAt 𝟙
  weak-one = V1.Step.weak-tw1ᵛ 𝟙 mb-one

x₂ : Tr (tw 1)
x₂ = proj₁ (upz (suc zero) (Ωt j₁))

module InstΩ (β : Tr⁺ j₁) where
  module VΩ = Tw1V (B₀ (tw 1)) (Ωt j₁) zero
  module V2 = Tw1V (B₀ (tw 1)) β x₂

  mb-Ω₂ : GR.R j₁ (E.ψ 𝟙 Ω₂ ∷ []) (proj₁ V2.start)
  mb-Ω₂ = weakᴿ j₁ (VΩ.Step.Node.seen-node [] top₁ [] top₁ (λ a → refl))
    (+-mono _ (ι-mono j₁ (proj₂ (V.ψ (h₁ (suc zero)) (proj₂ (Ok-tw 1) (suc zero)) (rcₙ 0 (suc zero)) (B₀ _) zero (z≤ _) (Ωt zero) (proj₁ (Ωt j₁))))))

  weak-Ω₂ : V2.WeakAt Ω₂
  weak-Ω₂ = V2.Step.weak-tw1ᵛ Ω₂ mb-Ω₂
```

## 高于目标层的槽位: 起点仍是 Ω 树

`subB` 在偏移取尽处交出 `Low` 的那一项 (`leaf-start`), 在偏移未取尽的层 (严格高于 j) 交出 Ω 树, 与 `Low` 无关 (`above-start`, `top-free`). 所以替身里槽位层严格高于目标层的结点, 链的起点不吸收前缀.

```agda
leaf-start : ∀ j s (ob : OkO j (nd s (λ _ → zero))) (D : Low j) (c : Ch s)
  → subB j (nd s (λ _ → zero)) ob D j (inc c self) ≡ D j self
leaf-start j s ob D c = refl

above-start : ∀ j s h (ob : OkO j (nd s h)) (D : Low j) → subB j (nd s h) ob D (j ⊕ nd s h) self ≡ Ωt (j ⊕ nd s h)
above-start j s h ob D = refl

top-free : ∀ j s s′ h′ (ob : OkO j (nd s (λ _ → nd s′ h′))) (D : Low j) (c : Ch s)
  → subB j (nd s (λ _ → nd s′ h′)) ob D (j ⊕ nd s′ h′) (inc c self) ≡ Ωt (j ⊕ nd s′ h′)
top-free j s s′ h′ ob D c = refl
```
