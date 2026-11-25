# 第 2 站归约到同步对象上的一条值引理
验收文件（读记号）；编译条件定理：`k2′-from-sync : Sᴱ.SyncLow → Kᴱ′ 2`，`k2ᶻ-from-sync : Sᶻ.SyncLow → Kᶻ′ 2`；上界一半 `Uᴱ`、`Uᶻ` 无前提。
同步对象是层号 `kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`：`Uᴱ` 从实际第 2 站第 1 个链点的孩子沿第一孩子降到它（`p*`，继承底），`Uᶻ` 即 `YiMTKeel.keelᶻ 1`（标准底）。
`SyncLow` 是对变量 γ、e 的前提：回灌与输出都保持 γ ↦ ψ₀(Ω_{Ω_γ})；本件不实填，小实例见 `YiSYSmall`。不否定什么。
被上界的是沿 `p*` 降下来的底 `Bᴱ` 上的折叠，不是 `Step 1` 在 c* = Ωt (tw 1) 处的输出（c* 不是链点，跨孩子比较没有编译的引理）。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSYReduce where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab using (rbᶻ; twᶻ)
open import OCF.Lean.YiKSDesc using (_⊑¹_; n¹; r¹; _∙¹_; ⊕⊑¹; up¹; kl; okl; ok¹)
open import OCF.Lean.YiMTKeel using (keelᶻ; F₀ᶻ)
open import OCF.Lean.YiGIInst using (baseᴱ; betaᴱ; pre; FΛ)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiKCSem using (rr≼; sem→M⁰)
open import OCF.Lean.YiKQSuff using (read≤)
open import OCF.Lean.YiKSRead using (fs-sup)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv)
open import OCF.Lean.YiExInst using (back; tree-back)
open import OCF.Lean.YiSYFrame using (Kᴱ′; Kᶻ′; twcᴱ)
open import OCF.Align.EboLeanTree using (hc-tower)
open import OCF.Align.Value using (_≼_; ≼-trans)
import OCF.Lean.YiSYDesc as D
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBRValue as BR
import OCF.Align.EboLeanDef as E
```

## 参照：第 3 行的基本列是同步映射 S 沿 γ 链

```agda
S : E.T → E.T
S γ = E.ψ [] (E.fsT (E.ΩTower 3) γ) ∷ []

γ : ℕ → E.T
γ = E.γT (E.ΩTower 3) []

fs-S : ∀ m → E.fsn (E.EBOψ 3) m ≡ S (γ m)
fs-S m = refl

γ-S : ∀ m → γ (suc m) ≡ S (γ m)
γ-S m = refl
```

## 前提与条件定理（对变量的形式）

层号 `nd (sΩ zero) a`：下标层是第 0 层，链 `chain` 在第 0 层（可数）。`Low X`：X 把 γ 的下界送到 S γ 的下界。

```agda
module Sync (a : Tr zero → L) (o : Ok (nd (sΩ zero) a)) (B : Base (nd (sΩ zero) a)) (β : Tr⁺ zero) where
  open D.Node zero a o B β public

  Low : (Tr zero → Tr zero) → Set
  Low X = ∀ γ e → K.M⁰ γ e → (h : E.HC (S γ)) → Rt h ≼ K.readRW (X e)

  SyncLow : Set
  SyncLow = Low feed × Low (λ e → proj₁ (out e))

  chain-rel : Low feed → ∀ m → K.M⁰ (γ m) (chain (suc m))
  chain-rel sf zero = K.pos⁰ (chain 1)
    (proj₂ (ψ (nd (sΩ zero) a) o (rbᶻ (nd (sΩ zero) a)) B zero (ink self) (B zero (ink self)) (g zero)))
  chain-rel sf (suc m) = sem→M⁰ (hω-inv (hc-tower 3) refl m) (feed (chain (suc m)))
    (sf (γ m) (chain (suc m)) (chain-rel sf m) (hω-inv (hc-tower 3) refl m))

  sync-bound : SyncLow → (h : E.HC (E.EBOψ 3)) → Rt h ≼ K.readRW (D.Fd (nd (sΩ zero) a) o B β)
  sync-bound (sf , so) h = fs-sup h refl λ m →
    ≼-trans (so (γ m) (chain (suc m)) (chain-rel sf m) (hω-inv h refl m))
      (≼-trans (read≤ (proj₁ (out (chain (suc m)))))
        (≼-trans (rowsᴮ (suc m)) (rr≼ (D.Fd (nd (sΩ zero) a) o B β))))
```

## 同步对象

```agda
h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

a₁ : Tr zero → L
a₁ c = tw 1 ⊕ ↑ (tw 1) (proj₁ (upz {s = sΩ zero} {h = h₁} c (Ωt (h₁ c))))

kl-shape : kl 1 ≡ nd (sΩ zero) a₁
kl-shape = refl
```

## 继承底：从实际第 2 站第 1 个链点的孩子降到同步对象

```agda
c₁ : Tr (tw 1)
c₁ = FR.Step.chain 1 1

b₁ β₂ : Tr⁺ (tw 1)
b₁ = baseᴱ 2 (tw 1) (ink self)
β₂ = ψ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) (tw 1) (inc 2 (ink self)) (Ωt (tw 1)) (FΛ 0)

p* : nd (sΩ zero) a₁ ⊑¹ FR.Step.child 1 c₁
p* = ⊕⊑¹ (tw 1) (n¹ r¹ ∙¹ (n¹ (up¹ (h₁ zero) (down stop zero) β₂ (proj₁ (Ωt (h₁ zero))))
  ∙¹ n¹ (up¹ (h₁ zero) (down stop zero) b₁ (proj₁ (Ωt (h₁ zero))))))

hiᴱ : D.Hi (baseᴱ 2)
hiᴱ i u d = K.⊴-◃ (ψ-⊵ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) i (inc 2 u) (Ωt i) (pre 2)) d

oᴱ : Ok (nd (sΩ zero) a₁)
oᴱ = ok¹ p* (proj₂ (Ok-tw 2) c₁)

Bᴱ : Base (nd (sΩ zero) a₁)
Bᴱ = D.dn¹ p* (D.dn (baseᴱ 2) c₁)

-- perf: C-9，实际站的上界与输出形状在变量 n、c 上陈述，只在 Uᴱ 一处代入。
upper-gen : ∀ n m → K.readRW (proj₁ (FR.Step.out n (FR.Step.chain n m))) ≼ K.readRW (twcᴱ (suc n))
upper-gen n m = FR.Step.branch-upper n m

out-gen : ∀ c → proj₁ (FR.Step.out 1 c) ≡ D.Fd (FR.Step.child 1 c) (proj₂ (Ok-tw 2) c) (D.dn (baseᴱ 2) c) (betaᴱ 2)
out-gen c = refl

Uᴱ : K.readRW (D.Fd (nd (sΩ zero) a₁) oᴱ Bᴱ (betaᴱ 2)) ≼ K.readRW (twcᴱ 2)
Uᴱ = ≼-trans (read≤ (D.Fd (nd (sΩ zero) a₁) oᴱ Bᴱ (betaᴱ 2)))
  (≼-trans (D.descᴮ p* (proj₂ (Ok-tw 2) c₁) (D.dn (baseᴱ 2) c₁) (betaᴱ 2) (λ i u → hiᴱ i (inc c₁ u)))
    (≼-trans (rr≼ (D.Fd (FR.Step.child 1 c₁) (proj₂ (Ok-tw 2) c₁) (D.dn (baseᴱ 2) c₁) (betaᴱ 2)))
      (subst (λ x → K.readRW x ≼ K.readRW (twcᴱ 2)) (out-gen c₁) (upper-gen 1 1))))

module Sᴱ = Sync a₁ oᴱ Bᴱ (betaᴱ 2)

k2′-from-sync : Sᴱ.SyncLow → Kᴱ′ 2
k2′-from-sync sl h = ≼-trans (tree-back h) (≼-trans (Sᴱ.sync-bound sl (back h)) Uᴱ)
```

## 标准底：同一对象在 `twᶻ 2` 之下（`keelᶻ 1`）

```agda
F₀-Fd : ∀ ℓ o → F₀ᶻ ℓ o ≡ D.Fd ℓ o (B₀ ℓ) (Ωt zero)
F₀-Fd ℓ o = refl

oᶻ : Ok (nd (sΩ zero) a₁)
oᶻ = okl 1

Uᶻ : K.readRW (D.Fd (nd (sΩ zero) a₁) oᶻ (B₀ (nd (sΩ zero) a₁)) (Ωt zero)) ≼ K.readRW (twᶻ 2)
Uᶻ = ≼-trans (read≤ (D.Fd (nd (sΩ zero) a₁) oᶻ (B₀ (nd (sΩ zero) a₁)) (Ωt zero)))
  (≼-trans (subst (λ x → BR.readRW x ≼ BR.readRW (twᶻ 2)) (F₀-Fd (nd (sΩ zero) a₁) oᶻ) (keelᶻ 1))
    (rr≼ (twᶻ 2)))

module Sᶻ = Sync a₁ oᶻ (B₀ (nd (sΩ zero) a₁)) (Ωt zero)

k2ᶻ-from-sync : Sᶻ.SyncLow → Kᶻ′ 2
k2ᶻ-from-sync sl h = ≼-trans (tree-back h) (≼-trans (Sᶻ.sync-bound sl (back h)) Uᶻ)
```
