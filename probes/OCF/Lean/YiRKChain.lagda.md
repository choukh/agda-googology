# 真实链点 chain 1 上, 三种写法的那一格

> 判决: 编译定理, 形状档, 不读记号. 同步对象的链 (`feed`, `chain` 逐字同 `YiSYDesc.Node`, k = 第 0 层, 孩子 `a₁` 同 `YiSYReduce.a₁`; 为导入闭包干净而重写) 对一切层号证据与底, `chain 1` 的顶是 ℕ 极限 (`L₁`), 链孩子 `a₁ (chain 1)` 的层号是 ℕ 极限形状 (`child-L`).
> `YiRKCell` 的表在 d = `chain 1` 上逐格实例化 (C-9: 链点封进 `opaque`, 只交出 `L₁`): 顶结点保留, 现行行退到第 0 层, 上折回退进 `ψˡ`, 换基换成 `h₁ (chain 1) ⊕ ↑c`, 与 d = ω 同形.
> 不否定什么: 没有值的定理; 不给 `chain 1` 与非延伸孩子之间没有字面路径的否定. 入口 `Real`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRKChain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp⁼; node⁺)
open import OCF.Lean.YiTBRow using (h₁; nat) renaming (ψ to ψ₁)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiVALeaf using (NZ; nzs; nzl)
open import OCF.Lean.YiTBTab using (ωᶜ; ωᵉ)
open import OCF.Lean.YiBSBase using (rb-tw)
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiRKCell
```

## 同步对象与链

第 0 层上的结点 `node⁺` 不可能保留 (第 0 层没有槽位), 所以链的每一步的顶都是 ℕ 极限 (`l-node`), 不必展开层号证据里的路径.

```agda
a₁ : Tr zero → L
a₁ c = tw 1 ⊕ ↑ (tw 1) (proj₁ (upz {s = sΩ zero} {h = h₁} c (Ωt (h₁ c))))

L→NZ : ∀ {d} → IsL d → NZ d
L→NZ (isL f a) = nzl f a

a₁-L : ∀ {d} → IsL d → Σ (ℕ → L) λ g → a₁ d ≡ nd sL g
a₁-L (isL f a) = _ , refl

l-node : ∀ {X x₀} (m : Keep zero X x₀) (G : X → Tr⁺ zero) (s : X → X) → IsL (proj₁ (node⁺ m G s))
l-node (just (() , _)) G s
l-node nothing         G s = isL _ _

module Real (o : Ok (nd (sΩ zero) a₁)) (B : Base (nd (sΩ zero) a₁)) where
  feed : Tr zero → Tr zero
  feed z = proj₁ (ψ₁ (nd (sΩ zero) a₁) o (rbᶻ (nd (sΩ zero) a₁)) B zero (ink self) (B zero (ink self))
                    (proj₁ (upz {s = sΩ zero} {h = a₁} z (Ωt (a₁ z)))))

  chain : ℕ → Tr zero
  chain = iter feed zero

  opaque
    chain₁ : Tr zero
    chain₁ = chain 1

    L₁ : IsL chain₁
    L₁ = l-node _ _ _

  nz₁ : NZ chain₁
  nz₁ = L→NZ L₁

  child-L : Σ (ℕ → L) λ g → a₁ chain₁ ≡ nd sL g
  child-L = a₁-L L₁

  e-s₁ : Ext chain₁ (suc chain₁)
  e-s₁ = ◃s

  e-ω₁ : Ext chain₁ (chain₁ + ωᶜ)
  e-ω₁ = ◃l 0
```

## 表 (d = chain 1)

```agda
  top-c₁ : (B′ : Base (tw 1)) (β : Tr⁺ (h₁ chain₁))
    → Kept (proj₁ (ψ₁ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B′ (h₁ chain₁) (inc chain₁ self) β (proj₁ (Ωt (tw 1)))))
  top-c₁ = top₁ nz₁

  top-c₃ : (B′ : Base (tw 1)) (β : Tr⁺ (h₁ chain₁))
    → Kept (proj₁ (BS.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B′ (h₁ chain₁) (inc chain₁ self) β (proj₁ (Ωt (tw 1)))))
  top-c₃ = top₃ nz₁

  u1-s : Cell₁ chain₁ (suc chain₁)
  u1-s = w1 nz₁ (ext-nz e-s₁)
  u1-ω : Cell₁ chain₁ (chain₁ + ωᶜ)
  u1-ω = w1 nz₁ (ext-nz e-ω₁)
  u1-1 : Cell₁ chain₁ (nat 1)
  u1-1 = w1 nz₁ (nzs _)
  u1-e : Cell₁ chain₁ ωᵉ
  u1-e = w1 nz₁ (nzl _ _)

  u2-s : ∀ K → Cell₂ chain₁ (suc chain₁) K
  u2-s K = w2 K nz₁ (ext-nz e-s₁)
  u2-ω : ∀ K → Cell₂ chain₁ (chain₁ + ωᶜ) K
  u2-ω K = w2 K nz₁ (ext-nz e-ω₁)
  u2-1 : ∀ K → Cell₂ chain₁ (nat 1) K
  u2-1 K = w2 K nz₁ (nzs _)
  u2-e : ∀ K → Cell₂ chain₁ ωᵉ K
  u2-e K = w2 K nz₁ (nzl _ _)

  u3-s : Cell₃ chain₁ (suc chain₁)
  u3-s = w3 nz₁ (suc chain₁)
  u3-ω : Cell₃ chain₁ (chain₁ + ωᶜ)
  u3-ω = w3 nz₁ (chain₁ + ωᶜ)
  u3-1 : Cell₃ chain₁ (nat 1)
  u3-1 = w3 nz₁ (nat 1)
  u3-e : Cell₃ chain₁ ωᵉ
  u3-e = w3 nz₁ ωᵉ

  u3′ : ∀ c → Cell₃′ chain₁ c
  u3′ = w3′ nz₁

  keep-c₁ : ∀ c (o′ : Ok (h₁ chain₁ ⊕ ↑ zero c)) (q : Pos (h₁ chain₁))
    → KeptAt q (kp⁼ (h₁ chain₁ ⊕ ↑ zero c) o′ (psh (lift (h₁ chain₁) (↑ zero c)) (inj₂ q)) (lift (h₁ chain₁) (↑ zero c)))
  keep-c₁ c o′ q = keep-lift (h₁ chain₁) (↑ zero c) o′ q

  noΩ-c₁ : ∀ c → NoΩ (h₁ chain₁ ⊕ ↑ zero c)
  noΩ-c₁ c = noΩ-reb chain₁ c
```
