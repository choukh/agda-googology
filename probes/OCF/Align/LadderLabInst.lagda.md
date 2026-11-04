# 高度上的标签 (三): 前缀结构的两个实例

> **判决: HOLDS (编译过, 无条件).** 结论写在 [LadderLab](LadderLab.lagda.md). 实例 ℕ∪{∞}: `fin n` 的前缀是 $\Omega\cdot(n+1)$, ∞ 的前缀是 $\psi_1(1)$. 实例 ω+ω: `top n` 的前缀是 $\psi_1(1)+\Omega\cdot n$. 字段全部成立, 没有假设; 第 0 行由 `view` 的三种写法对上: `fin 0` 是根层, `fin (n+1)`, `top (n+1)` 是闭包行 $\Omega_{\ldots+\Omega}[\theta]=\Omega_{\ldots+\theta}$, `∞`, `top 0` 是链行 $\psi_1(1)[n]=\Omega\cdot n$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import OCF.Align.EBO as E
open E using (T; natT; cmpᵀ; sucT; lt; gt; eq; cof; pred; fsn; fsT) renaming (ψ to ψᵗ)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.LadderLabZStandardOmega using (Ω₁; Ωᵐ; ψ¹; cof-Ωᵐ[]; cof-Ωᵐ+; pred-Ωᵐ+; fsn-Ωᵐ+; fsT-Ωᵐ; cof-ψ¹+; pred-ψ¹+; fsn-ψ¹+; fsn-ψ¹)
open import OCF.Align.LadderLabZSystemOmega using (TailOf; th; ts; oh; Ctbl-suc)
open import OCF.Align.LadderLabZDecouple using (Idx)
open import OCF.Align.LadderLabZGoodLBase using (Idx-Ctbl)
open import OCF.Align.LadderLabZUniform5Head using (ltμ; gtμ)
open import OCF.Align.LadderInfBase using (HtS)
open import OCF.Align.LadderLabBase
open import OCF.Align.LadderLabZNFWTree using (_<ᴸ_; zero; suc; dn; s<s)
open import OCF.Align.LadderLabZInfWTop using (HS∞; fin; ∞; inf) renaming (H to H∞)
open import OCF.Align.LadderLabZInfWTop2 using (HS₂; top; sw) renaming (H to H₂; fin to fin₂)
```

## §1 记号一侧的小引理

```agda
cmp≡ : ∀ n ν τ → cmpᵀ (sucT (Ωᵐ n ν)) (Ωᵐ n τ) ≡ cmpᵀ (sucT ν) τ
cmp≡ zero ν τ = refl
cmp≡ (suc n) ν τ = cmp≡ n ν τ

cmp-ltᵐ : ∀ {n H ν} τ → n <ᴸ H → Idx ν → cmpᵀ (sucT (Ωᵐ n ν)) (Ωᵐ H τ) ≡ lt
cmp-ltᵐ {n = zero} {H = suc H} τ q Iν = ltμ (Ωᵐ H τ) Iν
cmp-ltᵐ {n = suc n} {H = suc H} τ q Iν = cmp-ltᵐ {n = n} {H = H} τ (dn q) Iν

cmp-gtᵐ : ∀ {n H} ν {τ} → H <ᴸ n → Idx τ → cmpᵀ (sucT (Ωᵐ n ν)) (Ωᵐ H τ) ≡ gt
cmp-gtᵐ {n = suc n} {H = zero} ν q Iτ = gtμ (Ωᵐ n ν) Iτ
cmp-gtᵐ {n = suc n} {H = suc H} ν q Iτ = cmp-gtᵐ {n = n} {H = H} ν (dn q) Iτ

tailᵐ : ∀ {x} n τ → TailOf τ (x ∷ Ωᵐ n τ)
tailᵐ zero τ = th
tailᵐ (suc n) τ = ts (tailᵐ n τ)

-- 可数项对 ψ₁(1)+… 恒 lt, 反之恒 gt
cmp-Cψ : ∀ {v} → Ctbl v → ∀ X → cmpᵀ v (ψ¹ ∷ X) ≡ lt
cmp-Cψ c[] X = refl
cmp-Cψ (c∷ c) X = refl

cmp-ψC : ∀ {v} → Ctbl v → ∀ X → cmpᵀ (ψ¹ ∷ X) v ≡ gt
cmp-ψC c[] X = refl
cmp-ψC (c∷ c) X = refl
```

## §2 实例 ℕ∪{∞}

```agda
P∞ : H∞ → T → T
P∞ (fin n) τ = Ω₁ ∷ Ωᵐ n τ
P∞ ∞ τ = ψ¹ ∷ τ

row∞ : ∀ m → Row₀ HS∞ P∞ m (HtS.view HS∞ m)
row∞ (fin zero)    = rb refl
row∞ (fin (suc m)) = rc (fin zero) (cof-Ωᵐ[] (suc m)) (fsT-Ωᵐ (suc m))
row∞ ∞             = rl fin inf refl (fsn-ψ¹ 0) (λ i → fsn-ψ¹ (suc i))

Px∞ : PxS HS∞
Px∞ = record
  { P = P∞
  ; P-cof = λ { (fin n) w ws → cof-Ωᵐ+ n w ws ; ∞ w ws → refl }
  ; P-pred = λ { (fin n) w ws → pred-Ωᵐ+ n w ws ; ∞ w ws → refl }
  ; P-fsn = λ { (fin n) w ws k → fsn-Ωᵐ+ n w ws k ; ∞ w ws k → refl }
  ; P-tail = λ { (fin n) τ → tailᵐ n τ ; ∞ τ → th }
  ; P-occ = λ { (fin n) τ → oh ; ∞ τ → oh }
  ; P-lt = λ { (fin n) τ I → ltμ (Ωᵐ n τ) I ; ∞ τ I → cmp-Cψ (Ctbl-suc (Idx-Ctbl I)) τ }
  ; P-gt = λ { (fin n) ν I → gtμ (Ωᵐ n ν) I ; ∞ ν I → cmp-ψC (Idx-Ctbl I) (sucT ν) }
  ; P-cmp≡ = λ { (fin n) ν τ → cmp≡ n ν τ ; ∞ ν τ → refl }
  ; P-cmp-lt = cl∞
  ; P-cmp-gt = cg∞
  ; P-row = row∞
  }
  where
  open HtS HS∞ using () renaming (_<ᴸ_ to _<H_)
  cl∞ : ∀ {n H ν} τ → n <H H → Idx ν → cmpᵀ (sucT (P∞ n ν)) (P∞ H τ) ≡ lt
  cl∞ τ (fin q) I = cmp-ltᵐ {n = suc _} {H = suc _} τ (s<s q) I
  cl∞ τ (inf n) I = refl
  cg∞ : ∀ {n H} ν {τ} → H <H n → Idx τ → cmpᵀ (sucT (P∞ n ν)) (P∞ H τ) ≡ gt
  cg∞ ν (fin q) I = cmp-gtᵐ {n = suc _} {H = suc _} ν (s<s q) I
  cg∞ ν (inf n) I = refl
```

## §3 实例 ω+ω

```agda
P₂ : H₂ → T → T
P₂ (fin₂ n) τ = Ω₁ ∷ Ωᵐ n τ
P₂ (top n) τ = ψ¹ ∷ Ωᵐ n τ

row₂ : ∀ m → Row₀ HS₂ P₂ m (HtS.view HS₂ m)
row₂ (fin₂ zero)    = rb refl
row₂ (fin₂ (suc m)) = rc (fin₂ zero) (cof-Ωᵐ[] (suc m)) (fsT-Ωᵐ (suc m))
row₂ (top zero)     = rl fin₂ (λ i → sw i 0) refl (fsn-ψ¹ 0) (λ i → fsn-ψ¹ (suc i))
row₂ (top (suc m))  = rc (top zero) (cof-Ωᵐ[] m) (λ θ → cong (ψ¹ ∷_) (fsT-Ωᵐ m θ))

Px₂ : PxS HS₂
Px₂ = record
  { P = P₂
  ; P-cof = λ { (fin₂ n) w ws → cof-Ωᵐ+ n w ws ; (top n) w ws → cof-ψ¹+ n w ws }
  ; P-pred = λ { (fin₂ n) w ws → pred-Ωᵐ+ n w ws ; (top n) w ws → pred-ψ¹+ n w ws }
  ; P-fsn = λ { (fin₂ n) w ws k → fsn-Ωᵐ+ n w ws k ; (top n) w ws k → fsn-ψ¹+ n w ws k }
  ; P-tail = λ { (fin₂ n) τ → tailᵐ n τ ; (top n) τ → tailᵐ n τ }
  ; P-occ = λ { (fin₂ n) τ → oh ; (top n) τ → oh }
  ; P-lt = λ { (fin₂ n) τ I → ltμ (Ωᵐ n τ) I ; (top n) τ I → cmp-Cψ (Ctbl-suc (Idx-Ctbl I)) (Ωᵐ n τ) }
  ; P-gt = λ { (fin₂ n) ν I → gtμ (Ωᵐ n ν) I ; (top n) ν I → cmp-ψC (Idx-Ctbl I) (sucT (Ωᵐ n ν)) }
  ; P-cmp≡ = λ { (fin₂ n) ν τ → cmp≡ n ν τ ; (top n) ν τ → cmp≡ n ν τ }
  ; P-cmp-lt = cl₂
  ; P-cmp-gt = cg₂
  ; P-row = row₂
  }
  where
  open HtS HS₂ using () renaming (_<ᴸ_ to _<H_)
  cl₂ : ∀ {n H ν} τ → n <H H → Idx ν → cmpᵀ (sucT (P₂ n ν)) (P₂ H τ) ≡ lt
  cl₂ τ (fin₂ q) I = cmp-ltᵐ {n = suc _} {H = suc _} τ (s<s q) I
  cl₂ τ (sw n m) I = refl
  cl₂ τ (top q) I = cmp-ltᵐ τ q I
  cg₂ : ∀ {n H} ν {τ} → H <H n → Idx τ → cmpᵀ (sucT (P₂ n ν)) (P₂ H τ) ≡ gt
  cg₂ ν (fin₂ q) I = cmp-gtᵐ {n = suc _} {H = suc _} ν (s<s q) I
  cg₂ ν (sw n m) I = refl
  cg₂ ν {τ} (top q) I = cmp-gtᵐ ν {τ} q I
```
