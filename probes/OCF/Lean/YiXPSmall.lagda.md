# 最小实例的孩子层号上的 LowKeep 与 Need 一类的结论

> 验收文件 (读记号)。编译定理: `YiBVSmall.child d` 对一切第 0 层的树 d 都不含 Ω 形状, 所以 `LowKeepAtˣ (child d)` 无条件成立 (`low-child`); 在 `Rˣ` 里, 对带底前缀 `Prefixˣ` 的底, 孩子带精确标签 λ 时, 对一切 η ≤ λ 有 `YiQLRead.Need` 形状的结论 (`needˣ`); d 取有限数 n (λ = n+3) 与 ω (λ = ω+1) 实填 (`need-fin`, `need-ω`), 取标准底与 Ω 树作底值时无前提 (`need₀-fin`, `need₀-ω`)。
> 与 `YiQLRead.Need` 的差: 结论在 `Rˣ` (带向下封闭) 而非 `YiCLFam.M 1`; 多一个前提 `Prefixˣ base []`; η 的范围是 η ≤ λ, 不是 `M⁰ η d`。三处都没有处理; 不否定什么。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXPSmall where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLKIface using (OK)
open import OCF.Lean.YiKVRel using (⊴r)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import OCF.Lean.YiGTGen using (app≤ν)
open import OCF.Lean.YiCLFam using (nat)
open import OCF.Lean.YiCLPhi using (ωᵀ)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiSQOmega as W
import OCF.Lean.YiQLRead as Q
open import OCF.Lean.YiGLFrame using (Lbl; lbl-fin)
open import OCF.Lean.YiGLExact using (Rˣ; Prefixˣ; LowKeepAtˣ; topˣ; prefixˣ-B₀)
open import OCF.Lean.YiGLOmega using (lbl-G; lbl-source)
open import OCF.Lean.YiXPFrame using (NoΩ)
open import OCF.Lean.YiXPExact using (lowKeepAt-noΩ)
```

## 孩子层号不含 Ω 形状

```agda
noΩ-↑ : (d : Tr zero) → NoΩ (↑ zero d)
noΩ-↑ zero = tt
noΩ-↑ (suc x) = noΩ-↑ x
noΩ-↑ (lim f a) n = noΩ-↑ (f n)
noΩ-↑ (Ω () g)
noΩ-↑ (up x () y e)

noΩ-⊕ : ∀ a b → NoΩ a → NoΩ b → NoΩ (a ⊕ b)
noΩ-⊕ a zero na nb = na
noΩ-⊕ a (nd sS h) na nb = noΩ-⊕ a (h tt) na nb
noΩ-⊕ a (nd sL g) na nb n = noΩ-⊕ a (g n) na (nb n)
noΩ-⊕ a (nd (sΩ k) h) na ()

noΩ-child : ∀ d → NoΩ (S.child d)
noΩ-child d = noΩ-⊕ K.two (↑ zero (suc d)) tt (noΩ-↑ (suc d))

low-child : ∀ d → LowKeepAtˣ (S.child d)
low-child d = lowKeepAt-noΩ (S.child d) (noΩ-child d)
```

## Need 一类的结论

目标层 `K.one` 的标签是 1; 源是孩子的 Ω 树, 对着孩子的精确标签 (`topˣ`), 再向下封闭到 η。`Q.Target η` 定义性地是 ψ₁(Ω_η) (`Q.formula`)。

```agda
Needˣ : E.T → Tr zero → Set
Needˣ η d = (o : Ok (S.child d)) (r : Rb (S.child d)) (base : Base (S.child d)) (beta : Tr⁺ K.one)
  → OK base → Prefixˣ base [] → Rˣ K.one (E.Ωt (E.natT 1)) (proj₁ beta)
  → Rˣ K.one (Q.Target η)
      (proj₁ (ψ (S.child d) o r base K.one (S.lower d) beta (proj₁ (Ωt (S.child d)))))

needˣ : ∀ d {λ′} → Lbl (S.child d) λ′ → ∀ η → η ≤ᵀ λ′ → Needˣ η d
needˣ d lλ η le o r base beta gb pref mb =
  H.mc (app≤ν (E.natT 1) [] (Ωt-mono le))
    (low-child d o r base (S.lower d) beta (E.natT 1) [] (lbl-fin 1) gb pref mb
      (topˣ (S.child d) lλ))

need-fin : ∀ n η → η ≤ᵀ E.natT (suc (suc (suc n))) → Needˣ η (nat n)
need-fin n = needˣ (nat n) (lbl-G (suc n))

need-ω : ∀ η → η ≤ᵀ E.sucT ωᵀ → Needˣ η W.ω
need-ω = needˣ W.ω lbl-source
```

## 无前提的实例: 标准底, 底值取目标层的 Ω 树

```agda
need₀ : ∀ d {λ′} → Lbl (S.child d) λ′ → ∀ η → η ≤ᵀ λ′
  → (o : Ok (S.child d)) (r : Rb (S.child d))
  → Rˣ K.one (Q.Target η)
      (proj₁ (ψ (S.child d) o r (B₀ (S.child d)) K.one (S.lower d) (Ωt K.one) (proj₁ (Ωt (S.child d)))))
need₀ d lλ η le o r = needˣ d lλ η le o r (B₀ (S.child d)) (Ωt K.one)
  (λ i u → ⊴r) (prefixˣ-B₀ (S.child d)) (topˣ K.one (lbl-fin 1))

need₀-fin : ∀ n (o : Ok (S.child (nat n))) (r : Rb (S.child (nat n)))
  → Rˣ K.one (Q.Target (E.natT (suc (suc (suc n)))))
      (proj₁ (ψ (S.child (nat n)) o r (B₀ (S.child (nat n))) K.one (S.lower (nat n)) (Ωt K.one)
        (proj₁ (Ωt (S.child (nat n))))))
need₀-fin n = need₀ (nat n) (lbl-G (suc n)) (E.natT (suc (suc (suc n)))) (inj₂ refl)

need₀-ω : (o : Ok (S.child W.ω)) (r : Rb (S.child W.ω))
  → Rˣ K.one (Q.Target (E.sucT ωᵀ))
      (proj₁ (ψ (S.child W.ω) o r (B₀ (S.child W.ω)) K.one (S.lower W.ω) (Ωt K.one)
        (proj₁ (Ωt (S.child W.ω)))))
need₀-ω = need₀ W.ω lbl-source (E.sucT ωᵀ) (inj₂ refl)
```
