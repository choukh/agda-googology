# 合流关系族在颈结点上的 LowKeep: 自身行有框架, 走链与保留进孩子都挡住

> 验收文件 (读记号)。编译定理, 无前提: `YiBVSmall.layer` 折到自身时框架有居民 (`frame-selfᵐ`); 折到第 0 层时颈槽位的保留判定是走链 (`frame-neck-zero`)。编译否定: 对 Leaf 的 Ω 树, 颈槽位的链在第 0 步就没有证据 (`no-chain-neck`, `Rᵉ` 同, `no-chainᵉ-neck`): 链要第一个迭代恰好读作 Ω_0, 而它是 ℕ 极限; 经孩子 0 折到孩子层号时颈槽位保留进下界前提的槽位, 框架为空 (`no-frame-neck-child`, 用 `YiELZero.slow`)。
> 为什么第 0 层槽位不处处取 `Ex⁰`: `Rᵉ` 在不含 Ω 形状的层号 `one` 上同样没有链的证据 (`no-chainᵉ-one`)。
> 只否定 `YiXPRows` 一路所需的证据 (链、框架) 在这些实例上有居民; 不否定 `Rᵐ` 上 `YiBVSmall.layer` 的 LowKeep, 不否定路线。第一个挡住的引理的较弱形式 `NeckLabChain` 只是陈述。入口: [YiMGRel](YiMGRel.lagda.md), [YiMGFrame](YiMGFrame.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMGNeck where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiRWOps using (iter)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiLKIface using (feed)
open import OCF.Lean.YiANFam using (Pen)
open import OCF.Lean.YiGTIndexNeg using (pen-gt)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBVSmall as S
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_)
open import OCF.Align.EboLean3Base using (sucT≤)
open import OCF.Lean.YiGLFrame using (≤→pen)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiELZero using (Ex⁰; Ω₁; lbl<Ω; slow; no-lbl-slow)
open import OCF.Lean.YiELOmega using (Lblᵒ; Lowᵉ)
open import OCF.Lean.YiMGRel using (Lowᵐ; noΩ-at⁼; noΩ-child; unemb)
```

## `Rᵐ` 的框架与链

照 `YiXPRows.KeepG`, `NodeFrame`, `ChainAt`, 分支前提换成 `Lowᵐ` (`Rᵉ` 的链换成 `Lowᵉ`)。

```agda
KeepGᵐ : ∀ j (ν : E.T) {X : Set} {x₀ : X} → (E.T → X → Set) → (κ : E.T) → Keep j X x₀ → Set
KeepGᵐ j ν LX κ nothing = E.cmpᵀ (E.sucT κ) ν ≡ E.gt
KeepGᵐ j ν LX κ (just (q , cv , eq)) =
  Pen (E.cmpᵀ (E.sucT κ) ν) × Lblᵒ (at j q) κ × (∀ η c → Lowᵐ j q η c → LX η (cv c))

NodeFrameᵐ : ∀ ℓ → Ok ℓ → ∀ j → j ≤ ℓ → E.T → Set
NodeFrameᵐ ℓ o j w ν = (p : Pos ℓ) (κ : E.T) → Lblᵒ (at ℓ p) κ
  → KeepGᵐ j ν (Lowᵐ ℓ p) κ (kp ℓ o p w)

ChainAtᵐ : ∀ ℓ → Ok ℓ → Rb ℓ → Base ℓ → E.T → E.T → (p : Pos ℓ) → E.T → (Br ℓ p → Tr ℓ) → Set
ChainAtᵐ ℓ o r B t a p κ g = ∀ n → Lowᵐ ℓ p (E.γT (t ++ a) κ n)
  (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))

ChainAtᵉ : ∀ ℓ → Ok ℓ → Rb ℓ → Base ℓ → E.T → E.T → (p : Pos ℓ) → E.T → (Br ℓ p → Tr ℓ) → Set
ChainAtᵉ ℓ o r B t a p κ g = ∀ n → Lowᵉ ℓ p (E.γT (t ++ a) κ n)
  (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))

neck : Pos S.layer
neck = inj₁ (inj₁ tt)

gL : Tr zero → Tr S.layer
gL c = proj₁ (O.upz c (O.Ωt (S.child c)))
```

## 自身行与折到第 0 层的保留判定

槽位的标签都低于 Ω₁: 颈槽位是 0, 孩子里的槽位不含 Ω 形状 (`YiELZero.lbl<Ω`)。

```agda
slot<Ω : (p : Pos S.layer) {κ : E.T} → Lblᵒ (at S.layer p) κ → κ <ᵀ Ω₁
slot<Ω (inj₁ (inj₁ tt)) refl = E.[]<
slot<Ω (inj₁ (inj₂ ()))
slot<Ω (inj₂ (d , t)) l =
  lbl<Ω (proj₁ (sl⁼ (S.child d) t)) (unemb _ (noΩ-at⁼ (S.child d) (noΩ-child d) t) l)

frame-selfᵐ : NodeFrameᵐ S.layer S.okay S.layer self Ω₁
frame-selfᵐ p κ l = ≤→pen (sucT≤ (slot<Ω p l)) , l , λ η c x → x

frame-neck-zero : KeepGᵐ zero [] (Lowᵐ S.layer neck) [] (kp S.layer S.okay neck (z≤ S.layer))
frame-neck-zero = refl
```

## 否定

链的第 0 步: `γT _ 0 = Ωt []` (cof 是 1), 第一个迭代是孩子 0 的 Ω 树经下标层侧折到第 0 层, 头部是 `lim`, 精确读回要 cof 是 ω。

```agda
private
  c1≢cω : E.c1 ≡ E.cω → ⊥
  c1≢cω ()

no-chain-neck : ∀ r B t a → ChainAtᵐ S.layer S.okay r B t a neck [] gL → ⊥
no-chain-neck r B t a ch = c1≢cω (proj₁ (ch 0))

no-chainᵉ-neck : ∀ r B t a → ChainAtᵉ S.layer S.okay r B t a neck [] gL → ⊥
no-chainᵉ-neck r B t a ch = c1≢cω (proj₁ (ch 0))

gOne : Tr zero → Tr K.one
gOne c = proj₁ (O.upz {s = sS} {h = λ _ → zero} tt (suc c , O.z◃ c ◃s))

no-chainᵉ-one : ∀ o r B t a → ChainAtᵉ K.one o r B t a K.q1 [] gOne → ⊥
no-chainᵉ-one o r B t a ch = c1≢cω (proj₁ (ch 0))
```

经孩子 0 折到孩子层号: 颈槽位沿下标层的路径推进孩子 0 的第 0 层槽位, 保留; 那里的分支前提是 `H.M⁰`, 颈槽位要 `Ex⁰`。孩子里的槽位一行同 `YiXPNeg.no-frame-Ωinc` (保留判定走链, 而标签更低)。

```agda
no-frame-neck-child : ∀ ν → NodeFrameᵐ S.layer S.okay (S.child zero) (inc zero self) ν → ⊥
no-frame-neck-child ν fr = no-lbl-slow [] (proj₂ (proj₂ (fr neck [] refl)) [] slow H.mz)

no-frame-Ωincᵐ : ∀ c {j} (v : j ≤ S.child c) {ν} (c′ : Tr zero) (t : Pos⁼ (S.child c′)) {κ}
  → Lblᵒ (proj₁ (sl⁼ (S.child c′) t)) κ → κ <ᵀ ν → NodeFrameᵐ S.layer S.okay j (inc c v) ν → ⊥
no-frame-Ωincᵐ c v c′ t l lt fr = pen-gt (≤→pen (sucT≤ lt)) (fr (inj₂ (c′ , t)) _ l)
```

## 第一个挡住的引理 (陈述, 没有居民)

精确等于 γ 链的一项已被 `no-chain-neck` 否定; 留下的较弱形式: 颈槽位链的每个迭代有精确读回, 且不低于 γ 链的对应项。有了它, 结点行还要记号一侧 `fsT` 对下标单调, 才能用向下封闭降到 γ 链的项。

```agda
NeckLabChain : Rb S.layer → Base S.layer → E.T → E.T → Set
NeckLabChain r B t a = ∀ n → Σ E.T λ μ
  → Ex⁰ μ (iter (feed S.layer S.okay r B neck gL) (fromBr S.layer neck zero) (suc n))
  × (E.γT (t ++ a) [] n ≤ᵀ μ)
```
