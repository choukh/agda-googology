# 同步前提在 γ = 1 处成立；剩余前提与各站的形状
验收文件（读记号）；编译定理，无前提：继承底实例在 γ = 1 处回灌与输出两半都成立（`sf₁ᴱ`、`so₁ᴱ`），于是链的前两点（`chain-two`）与第 3 行第 0 项（`start-sync`）无前提；条件定理 `k2′-from-tail` 只剩 γ 链第 1 项起的 `Tail`。
`sf₁ᴱ` 的值来自 Ω 形状那一行的回退分支（底里出现 `twᶻ 1`），`so₁ᴱ` 来自继承的起点 `betaᴱ 2 = brᶻ 1`。来源：值链复用 `YiFRStations.k2` 与 `YiPCKeel.k1-value`。
形状（编译）：γ = 2 的输出层号 `a₁ 2` 的下标层是 `one`；`kl (suc n)` 的下标层是 `tw n`。不否定什么：`Tail` 未实填，也没有它的否定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSYSmall where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab using (rbᶻ; twᶻ)
open import OCF.Lean.YiKSDesc using (kl; okl)
open import OCF.Lean.YiMTKeel using (keelᶻ)
open import OCF.Lean.YiGIInst using (betaᴱ; FΛ)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiMTValue using (brᶻ; btbo-br1ᶻ)
open import OCF.Lean.YiEXRow using (row₂-btbo)
open import OCF.Lean.YiPCKeel using (k1-value)
open import OCF.Lean.YiKCSem using (rr≼; sem→M⁰)
open import OCF.Lean.YiKQSuff using (read≤)
open import OCF.Lean.YiKSRead using (fs-sup)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
open import OCF.Lean.YiExInst using (back; tree-back)
open import OCF.Lean.YiSYFrame using (Kᴱ′; twcᴱ)
open import OCF.Lean.YiSYReduce using (S; γ; module Sync; F₀-Fd; a₁; c₁; oᴱ; Bᴱ; Uᴱ)
open import OCF.Align.EboLeanTree using (hc-tower)
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; z≼; s≼s; l≼; ≼l)
import OCF.Lean.YiSYDesc as D
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBRValue as BR
import OCF.Align.EboLeanDef as E
```

## 第 0 层的小引理

```agda
+r : ∀ a y → K.readRW y ≼ K.readRW (a + y)
+r a zero          = z≼
+r a (suc y)       = s≼s (+r a y)
+r a (lim f _)     = l≼ (λ n → ≼l n (+r a (f n)))
+r a (Ω () _)
+r a (up _ () _ _)

ι-low : ∀ y → K.readRW y ≼ K.readRW (ι zero y)
ι-low zero          = z≼
ι-low (suc y)       = s≼s (ι-low y)
ι-low (lim f _)     = l≼ (λ n → ≼l n (ι-low (f n)))
ι-low (Ω () _)
ι-low (up _ () _ _)

⊴≼ : {x y : Tr zero} → x K.⊴ y → K.readRW x ≼ K.readRW y
⊴≼ K.⊴r     = ≼-refl _
⊴≼ (K.⊴◃ d) = K.◃→≼ d

-- perf: C-9，两个同体的名字 FΛ、Fᴧ 只在变量 n 上相遇。
beta-br : ∀ n → proj₁ (betaᴱ (suc n)) ≡ brᶻ n
beta-br n = refl

Low-at : E.T → (Tr zero → Tr zero) → Set
Low-at γ X = ∀ e → K.M⁰ γ e → (h : E.HC (S γ)) → Rt h ≼ K.readRW (X e)
```

## 对变量的底与起点：γ = 1 的两半与剩余前提

γ 0 = 1，S 1 = ψ₀(Ω_Ω) 即第 2 行；所以 γ = 1 的两半只要底（回灌）或起点（输出）不低于第 2 行。

```agda
-- perf: C-9/C-10，链点与行在变量的层号、底、起点上证明；具体的站只在下面一处代入（闭的链点比较 8G 堆耗尽）。
module Gen (a : Tr zero → L) (o : Ok (nd (sΩ zero) a)) (B : Base (nd (sΩ zero) a)) (β : Tr⁺ zero) where
  open Sync a o B β public

  Row₂ : Tr zero → Set
  Row₂ x = (h : E.HC (E.EBOψ 2)) → Rt h ≼ K.readRW x

  SF₁ SO₁ : Set
  SF₁ = Low-at (γ 0) feed
  SO₁ = Low-at (γ 0) (λ e → proj₁ (out e))

  so-from-β : Row₂ (proj₁ β) → SO₁
  so-from-β r e _ h = ≼-trans (r h)
    (⊴≼ (ψ-⊵ (nd (sΩ zero) a) o (rbᶻ (nd (sΩ zero) a)) B zero (z≤ (nd (sΩ zero) a)) β (g e)))

  sf-from-base : Row₂ (proj₁ (B zero (ink self))) → SF₁
  sf-from-base r e _ h = ≼-trans (r h)
    (⊴≼ (ψ-⊵ (nd (sΩ zero) a) o (rbᶻ (nd (sΩ zero) a)) B zero (ink self) (B zero (ink self)) (g e)))

  chain₀ : K.M⁰ (γ 0) (chain 1)
  chain₀ = K.pos⁰ (chain 1)
    (proj₂ (ψ (nd (sΩ zero) a) o (rbᶻ (nd (sΩ zero) a)) B zero (ink self) (B zero (ink self)) (g zero)))

  Two : Set
  Two = K.M⁰ (γ 1) (chain 2)

  chain₁ : SF₁ → Two
  chain₁ sf = sem→M⁰ (hω-inv (hc-tower 3) refl 0) (feed (chain 1))
    (sf (chain 1) chain₀ (hω-inv (hc-tower 3) refl 0))

  Tail : Set
  Tail = ∀ m → Low-at (γ (suc m)) feed × Low-at (γ (suc m)) (λ e → proj₁ (out e))

  chain-relᵗ : SF₁ → Tail → ∀ m → K.M⁰ (γ m) (chain (suc m))
  chain-relᵗ sf tl zero          = chain₀
  chain-relᵗ sf tl (suc zero)    = chain₁ sf
  chain-relᵗ sf tl (suc (suc m)) = sem→M⁰ (hω-inv (hc-tower 3) refl (suc m)) (feed (chain (suc (suc m))))
    (proj₁ (tl m) (chain (suc (suc m))) (chain-relᵗ sf tl (suc m)) (hω-inv (hc-tower 3) refl (suc m)))

  up-row : ∀ q → K.readRW (proj₁ (out (chain q))) ≼ K.readRW (D.Fd (nd (sΩ zero) a) o B β)
  up-row q = ≼-trans (read≤ (proj₁ (out (chain q))))
    (≼-trans (rowsᴮ q) (rr≼ (D.Fd (nd (sΩ zero) a) o B β)))

  start : SO₁
    → (h : E.HC (E.fsn (E.EBOψ 3) 0)) → Rt h ≼ K.readRW (D.Fd (nd (sΩ zero) a) o B β)
  start so h = ≼-trans (so (chain 1) chain₀ h) (up-row 1)

  boundᵗ : SF₁ → SO₁ → Tail
    → (h : E.HC (E.EBOψ 3)) → Rt h ≼ K.readRW (D.Fd (nd (sΩ zero) a) o B β)
  boundᵗ sf so tl h = fs-sup h refl λ
    { zero    → start so (hω-inv h refl 0)
    ; (suc m) → ≼-trans (proj₂ (tl m) (chain (suc (suc m))) (chain-relᵗ sf tl (suc m)) (hω-inv h refl (suc m)))
                        (up-row (suc (suc m))) }

  FirstMissing : Set
  FirstMissing = (h : E.HC (S (γ 1))) → Rt h ≼ K.readRW (proj₁ (out (chain 2)))

  first-missing : SF₁ → Tail → FirstMissing
  first-missing sf tl h = proj₂ (tl 0) (chain 2) (chain₁ sf) h
```

## 继承底的实例

`Bᴱ zero (ink self)` 经 Ω 形状层号 `tw 2` 的那一行：表在孩子 `zero` 与 `c₁` 间没有条目，走回退分支 `x ⊞ ψ₀ʳ (tw 1) …`，第二项就是 `twᶻ 1`（`fb` 由检查器展开确认）。

```agda
module Gᴱ = Gen a₁ oᴱ Bᴱ (betaᴱ 2)

Vᴱ : zero ≤ FR.Step.child 1 c₁
Vᴱ = inc zero (inc 0 (inc zero (inc 0 (inc 0 (ink self)))))

β″ : Tr⁺ zero
β″ = ψ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) zero (inc 2 (inc c₁ Vᴱ)) (Ωt zero) (FΛ 0)

fb : K.readRW (twᶻ 1) ≼ K.readRW (proj₁ (Bᴱ zero (ink self)))
fb = ≼-trans (ι-low (twᶻ 1)) (+r (proj₁ β″) (ι zero (twᶻ 1)))

base-row₂ : Gᴱ.Row₂ (proj₁ (Bᴱ zero (ink self)))
base-row₂ h = ≼-trans (k1-value h) (≼-trans (rr≼ (twᶻ 1)) fb)

β-row₂ : Gᴱ.Row₂ (proj₁ (betaᴱ 2))
β-row₂ h = subst (λ x → Rt h ≼ K.readRW x) (sym (beta-br 1))
  (≼-trans (tree-≼ refl h (hc-tower 2)) (≼-trans row₂-btbo (≼-trans btbo-br1ᶻ (rr≼ (brᶻ 1)))))

-- perf: C-1，实例的类型只用 Gᴱ 导出的名字（自写 `Low-at (γ 0) Gᴱ.feed` 时 8G 堆耗尽）。
sf₁ᴱ : Gᴱ.SF₁
sf₁ᴱ = Gᴱ.sf-from-base base-row₂

so₁ᴱ : Gᴱ.SO₁
so₁ᴱ = Gᴱ.so-from-β β-row₂

chain-two : Gᴱ.Two
chain-two = Gᴱ.chain₁ sf₁ᴱ

start-sync : (h : E.HC (E.fsn (E.EBOψ 3) 0)) → Rt h ≼ K.readRW (twcᴱ 2)
start-sync h = ≼-trans (Gᴱ.start so₁ᴱ h) Uᴱ

k2′-from-tail : Gᴱ.Tail → Kᴱ′ 2
k2′-from-tail tl h = ≼-trans (tree-back h) (≼-trans (Gᴱ.boundᵗ sf₁ᴱ so₁ᴱ tl (back h)) Uᴱ)
```

`FirstMissing` 是 `Tail` 第 0 项的输出一半在第 2 个链点处的实例：ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}}) 不高于那一点的输出。

```agda
first-missingᴱ : Gᴱ.Tail → Gᴱ.FirstMissing
first-missingᴱ = Gᴱ.first-missing sf₁ᴱ
```

## 形状：γ = 2 与一切站

```agda
two-shape : Σ (Tr (nd sS (λ _ → zero)) → L) λ hh → a₁ (suc (suc zero)) ≡ nd (sΩ (nd sS (λ _ → zero))) hh
two-shape = _ , refl

kl-index : ∀ n → Σ (Tr (tw n) → L) λ hh → kl (suc n) ≡ nd (sΩ (tw n)) hh
kl-index n = _ , refl

Uᶻ-all : ∀ n → K.readRW (D.Fd (kl n) (okl n) (B₀ (kl n)) (Ωt zero)) ≼ K.readRW (twᶻ (suc n))
Uᶻ-all n = ≼-trans (read≤ (D.Fd (kl n) (okl n) (B₀ (kl n)) (Ωt zero)))
  (≼-trans (subst (λ x → BR.readRW x ≼ BR.readRW (twᶻ (suc n))) (F₀-Fd (kl n) (okl n)) (keelᶻ n)) (rr≼ (twᶻ (suc n))))
```
