# 空白页候选 B: 形状测试与类型层的一致

> 有限测试 (`refl`) 与编译定理, 不读记号. 测试: 最小见证 ψ₀(Ω_Ω+Ω₂) 的折叠展开成沿孩子层 1 的对角链, 链的第 1 项就是 "把 Ω_Ω 折到孩子里的层 1" (带着 x); 这一步对基底的 Ω 极限给 `below`, 保留成层 1 里的 Ω 极限 (底认得 x); 两个孩子之间的比较对任意孩子树都是 `other`, 把孩子里的目标搬进任一个孩子都给同一个 `side` (只用基底). 定理: 位置与地址上的树类型与那一层的树类型相同 (`TrAt≡`, `TrCh≡`).
> 另: 目标高于 Ω 结点时孩子内部的 Ω 极限保留 (`abv`). 不涉及值; 值的判据在 [YiBPAccept](YiBPAccept.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBPShape where

open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiBPBlock
open import OCF.Lean.YiBPFold
```

## 最小见证的对角链

孩子地址 `A₁` 是 Ω 结点 `tw 1` 的第 1 个孩子 (层 z ⊞ 1, 读作 2); `t1` 是它里面的层 z ⊞ 0 (读作 1). 底 `botB`: 把 Ω_Ω 折到孩子 A₁ 里的目标.

```agda
A₁ : Ch (Ωₗ z)
A₁ = inj₂ (suc zero , inj₁ tt)

t1 base₁ : Pos (z ⊞ suc zero)
t1    = inj₂ (inj₁ tt)
base₁ = inj₁ (inj₁ tt)

topB : ∀ {ℓ} → Bot ℓ
topB {B = B} _ = top B

botB : Bot (z ⊞ suc zero)
botB T″ = ψc (Ωₗ z) (up (Ωₗ z) A₁ T″) topB ΩΩ

chB : ℕ → Tr (z ⊞ zero)
chB = itc (λ e → ψc (z ⊞ suc zero) (pos t1) botB (embS z zero e)) zero

_ : tB′ ≡ lim (λ n → ψc (z ⊞ suc zero) (pos base₁) botB (embS z zero (chB n)))
_ = refl

_ : ∀ n → chB (suc n) ≡ ψc (z ⊞ suc zero) (pos t1) botB (embS z zero (chB n))
_ = λ n → refl
```

链的第 1 项: 把 Ω_Ω 折到孩子里的层 1, 即 ψ₁(Ω_Ω + 0); 它对基底分支保留 Ω 极限.

```agda
_ : chB 1 ≡ ψc (Ωₗ z) (inch A₁ (pos t1)) topB ΩΩ
_ = refl

_ : ψc (Ωₗ z) (inch A₁ (pos t1)) topB ΩΩ
    ≡ Ω (inj₁ (inj₁ tt)) (λ c → ψc (Ωₗ z) (inch A₁ (pos t1)) topB (ex zero (inj₂ (c , inj₁ tt)) (topP z c)))
_ = refl
```

## 不比较两个孩子

对任意孩子树 c, c′ (包括相等的), 两个孩子位置的比较都是 `other`; 目标在孩子 A₁ 里时走进任一个孩子结点 (包括 A₁ 自己), 目标一律变成 `side sd`.

```agda
_ : ∀ c c′ → cmp (Ωₗ z) (inj₂ (c , inj₁ tt)) (inj₂ (c′ , inj₁ tt)) ≡ other
_ = λ c c′ → refl

_ : ∀ μ c (T : Tg (μ ⊞ c) μ) c′ x → cmpT (Ωₗ μ) (inch (inj₂ (c , inj₁ tt)) T) (inj₂ (c′ , x)) ≡ other
_ = λ μ c T c′ x → refl

_ : ∀ c → enter (Ωₗ z) (inj₂ (c , inj₁ tt)) (inch A₁ (pos t1)) ≡ side sd
_ = λ c → refl
```

走进第 0 个孩子 (层 z ⊞ 0, 读作 1) 的 Ω 树时, 它对基底的 Ω 极限低于目标, 由 `side` 字面地给 `below`; 对第 1 个孩子 (与 A₁ 相同) 也走同一个子句.

```agda
bot₀ : Bot (z ⊞ zero)
bot₀ T″ = ψc (Ωₗ z) (up (Ωₗ z) (inj₂ (zero , inj₁ tt)) T″) topB zero

_ : ψc (Ωₗ z) (inch A₁ (pos t1)) topB (ex zero (inj₂ (zero , inj₁ tt)) (topP z zero))
    ≡ Ω (inj₁ (inj₁ tt)) (λ e → ψc (z ⊞ zero) (side sd) bot₀ (emb⊞ z zero e))
_ = refl

_ : up (Ωₗ z) A₁ (pos base₁) ≡ pos (inj₁ (inj₁ tt))
_ = refl
```

## 目标高于 Ω 结点: 孩子内部的 Ω 极限保留为展平位置上的 Ω 极限

塔第 2 项上, 把基底 (塔第 1 项) 的孩子 c+1 的 Ω 树折到层 `tw 1`: 目标给 `abv`, 输出的头是 `tw 1` 里展平位置 (c+1, 层 z ⊞ c) 上的 Ω 极限.

```agda
headΩ : ∀ {ℓ} → Tr ℓ → Maybe (Pos ℓ)
headΩ (Ω p _) = just p
headΩ _       = nothing

_ : ∀ c → enter (tw 2) (inj₁ (inj₂ (c , inj₁ tt))) (pos (inj₁ (inj₁ tt))) ≡ abv (eC z c)
_ = λ c → refl

_ : ∀ c → headΩ (ψc (tw 2) (pos (inj₁ (inj₁ tt))) topB (ex zero (inj₁ (inj₂ (suc c , inj₁ tt))) (topP z (suc c))))
          ≡ just (inj₂ (suc c , inj₂ (inj₁ tt)))
_ = λ c → refl
```

## 塔 (有限测试)

```agda
_ : tw 2 ≡ Ωₗ (Ωₗ z)
_ = refl

_ : at Λ (2 , inj₂ (inj₁ (inj₁ tt))) ≡ tw 1
_ = refl
```

## 位置与地址上的树类型

```agda
mutual
  TrAt≡⁺ : ∀ μ b → TrAt⁺ μ b ≡ Tr (at⁺ μ b)
  TrAt≡⁺ μ (inj₁ _) = refl
  TrAt≡⁺ μ (inj₂ q) = TrAt≡ μ q

  TrAt≡ : ∀ ℓ p → TrAt ℓ p ≡ Tr (at ℓ p)
  TrAt≡ z ()
  TrAt≡ (μ ⊞ c) (inj₁ b)            = TrAt≡⁺ μ b
  TrAt≡ (μ ⊞ c) (inj₂ ip)           = TrI≡ μ c ip
  TrAt≡ (l f) (n , b)               = TrAt≡⁺ (f n) b
  TrAt≡ (Ωₗ μ) (inj₁ b)             = TrAt≡⁺ μ b
  TrAt≡ (Ωₗ μ) (inj₂ (c , inj₁ _))  = refl
  TrAt≡ (Ωₗ μ) (inj₂ (c , inj₂ ip)) = TrI≡ μ c ip

  TrI≡ : ∀ μ c ip → TrI μ c ip ≡ Tr (μ ⊞ sub μ c ip)
  TrI≡ μ (suc c) (inj₁ _)      = refl
  TrI≡ μ (suc c) (inj₂ ip)     = TrI≡ μ c ip
  TrI≡ μ (lim f) (n , inj₁ _)  = refl
  TrI≡ μ (lim f) (n , inj₂ ip) = TrI≡ μ (f n) ip
  TrI≡ μ (Ω q f) (e , inj₁ _)  = refl
  TrI≡ μ (Ω q f) (e , inj₂ ip) = TrI≡ μ (f e) ip
  TrI≡ μ (ex x a y) ip         = TrI≡ μ x ip

mutual
  TrCh≡ : ∀ ℓ a → TrCh ℓ a ≡ Tr (chAt ℓ a)
  TrCh≡ z ()
  TrCh≡ (μ ⊞ c) (inj₁ a)            = TrCh≡ μ a
  TrCh≡ (μ ⊞ c) (inj₂ ia)           = TrChI≡ μ c ia
  TrCh≡ (l f) (n , a)               = TrCh≡ (f n) a
  TrCh≡ (Ωₗ μ) (inj₁ a)             = TrCh≡ μ a
  TrCh≡ (Ωₗ μ) (inj₂ (c , inj₁ _))  = refl
  TrCh≡ (Ωₗ μ) (inj₂ (c , inj₂ ia)) = TrChI≡ μ c ia

  TrChI≡ : ∀ μ c ia → TrChI μ c ia ≡ Tr (μ ⊞ subC μ c ia)
  TrChI≡ μ (suc c) ia            = TrChI≡ μ c ia
  TrChI≡ μ (lim f) (n , ia)      = TrChI≡ μ (f n) ia
  TrChI≡ μ (Ω q f) (e , inj₁ _)  = refl
  TrChI≡ μ (Ω q f) (e , inj₂ ia) = TrChI≡ μ (f e) ia
  TrChI≡ μ (ex x a′ y) ia        = TrChI≡ μ x ia
```
