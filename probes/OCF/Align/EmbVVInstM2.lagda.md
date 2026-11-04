# 值验收 (实例): 码 $\omega\cdot2$ 的第 $\alpha$ 行

> 入口 [EmbVV](EmbVV.lagda.md). 读记号. `Px-M₂`: 码 `ω·ᶜ 1` 上的前缀结构, 顶上开去头开关. `no-PxB-M₂` 否定的是不带开关的版本, 这里不矛盾: 去头之后第 0 行对上 $\psi_1(1)\cdot2$ 的基本列. `vv-M₂`: 主线的第 $\alpha$ 行过值验收, 读 $\psi_0(\Omega_{\psi_1(1)\cdot2+\theta})$. `vv-M₂-1`: $\alpha=1$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVInstM2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import OCF.Free.Level hiding (z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Align.EBO as E
open E using (T; natT; Ωt; cmpᵀ; sucT; lt; gt; eq; cof; pred; fsn; fsT) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.EmbVVLZStandardOmega using (Ω₁; Ωᵐ; ψ¹; pk; cof-Ωᵐ[]; cof-Ωᵐ+; pred-Ωᵐ+; fsn-Ωᵐ+; fsT-Ωᵐ; cof-ψ¹+; pred-ψ¹+; fsn-ψ¹+; fsn-ψ¹; NF₁)
open import OCF.Align.LadderLabZSystemOmega using (TailOf; th; ts; Occ; oh; Ctbl-suc)
open import OCF.Align.EmbVVOZDecouple using (Idx)
open import OCF.Align.EmbVVOZGoodLBase using (Idx-Ctbl; Lab→Ctbl; nf1; lab1)
open import OCF.Align.EmbVVOZUniform5Head using (ltμ; gtμ)
open import OCF.Align.EmbVVOZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.LadderNFTree using (_<ᴸ_; zero; suc; dn; s<s; z<s) renaming (tr< to trℕ)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.LadderOrdInst using (M₂)
open import OCF.Align.EmbVVBBase
open import OCF.Align.EmbVVMode using (HdM; keep; drop; repl)
open import OCF.Align.EmbVVEq using (_≃ᴵ_; z≃; s≃; ≃-reflᴵ)
open import OCF.Align.EmbVVNF using (NF-ψ⁺)
import OCF.Align.EmbVVTop
open import OCF.Align.ValLabPos using (VV)
```

## §1 记号的小引理

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

cmp-Cψ : ∀ {v} → Ctbl v → ∀ X → cmpᵀ v (ψ¹ ∷ X) ≡ lt
cmp-Cψ c[] X = refl
cmp-Cψ (c∷ c) X = refl

cmp-ψC : ∀ {v} → Ctbl v → ∀ X → cmpᵀ (ψ¹ ∷ X) v ≡ gt
cmp-ψC c[] X = refl
cmp-ψC (c∷ c) X = refl
```

## §2 三段高度

```agda
data H₃ : Set where
  fin : ℕ → H₃
  top : ℕ → H₃
  T̂   : H₃

infix 4 _<₃_
data _<₃_ : H₃ → H₃ → Set where
  fin : ∀ {n m} → n <ᴸ m → fin n <₃ fin m
  sw  : ∀ n m → fin n <₃ top m
  top : ∀ {n m} → n <ᴸ m → top n <₃ top m
  ft  : ∀ n → fin n <₃ T̂
  tt′ : ∀ n → top n <₃ T̂

Pc : H₃ → T → T
Pc (fin n) τ = Ω₁ ∷ Ωᵐ n τ
Pc (top n) τ = ψ¹ ∷ Ωᵐ n τ
Pc T̂ τ = ψ¹ ∷ ψ¹ ∷ τ

rk₃ : Pos (cs M₂) → H₃
rk₃ end = T̂
rk₃ (low (blk zero end)) = top 0
rk₃ (low (blk zero (low (blk j end)))) = fin j
rk₃ (low (blk zero (low (blk j (low ())))))
rk₃ (low (blk (suc j) end)) = top (suc j)
rk₃ (low (blk (suc j) (low ())))

ltℕ : ∀ j k → ltB (λ _ → cz) j k end end → j <ᴸ k
ltℕ zero (suc k) x = z<s k
ltℕ (suc j) (suc k) x = s<s (ltℕ j k x)

r< : ∀ p q → p <ᴾ q → rk₃ p <₃ rk₃ q
r< (low (blk zero end)) end x = tt′ 0
r< (low (blk zero (low (blk j end)))) end x = ft j
r< (low (blk zero (low (blk j (low ()))))) q x
r< (low (blk (suc j) end)) end x = tt′ (suc j)
r< (low (blk (suc j) (low ()))) q x
r< (low (blk zero end)) (low (blk zero end)) ()
r< (low (blk zero end)) (low (blk zero (low q))) ()
r< (low (blk zero end)) (low (blk (suc k) end)) x = top (z<s k)
r< (low (blk zero (low (blk j end)))) (low (blk zero end)) x = sw j 0
r< (low (blk zero (low (blk j end)))) (low (blk zero (low (blk k end)))) x = fin (ltℕ j k x)
r< (low (blk zero (low (blk j end)))) (low (blk zero (low (blk k (low ()))))) x
r< (low (blk zero (low (blk j end)))) (low (blk (suc k) end)) x = sw j (suc k)
r< (low (blk (suc j) end)) (low (blk zero q)) ()
r< (low (blk (suc j) end)) (low (blk (suc k) end)) x = top (s<s (ltℕ j k x))
r< p (low (blk (suc k) (low ()))) x

cl₃ : ∀ {n H ν} τ → n <₃ H → Idx ν → cmpᵀ (sucT (Pc n ν)) (Pc H τ) ≡ lt
cl₃ τ (fin q) I = cmp-ltᵐ {n = suc _} {H = suc _} τ (s<s q) I
cl₃ τ (sw n m) I = refl
cl₃ τ (top q) I = cmp-ltᵐ τ q I
cl₃ τ (ft n) I = refl
cl₃ τ (tt′ zero) I = cmp-Cψ (Ctbl-suc (Idx-Ctbl I)) τ
cl₃ τ (tt′ (suc n)) I = refl

cg₃ : ∀ {n H} ν {τ} → H <₃ n → Idx τ → cmpᵀ (sucT (Pc n ν)) (Pc H τ) ≡ gt
cg₃ ν (fin q) I = cmp-gtᵐ {n = suc _} {H = suc _} ν (s<s q) I
cg₃ ν (sw n m) I = refl
cg₃ ν {τ} (top q) I = cmp-gtᵐ ν {τ} q I
cg₃ ν (ft n) I = refl
cg₃ ν (tt′ zero) I = cmp-ψC (Idx-Ctbl I) (sucT ν)
cg₃ ν (tt′ (suc n)) I = refl
```

## §3 前缀结构

```agda
dr₂ : ∀ m → HdM (HB M₂) m
dr₂ end = drop
dr₂ (low _) = keep

fs-top : ∀ i → fsn (ψ¹ ∷ ψ¹ ∷ []) i ≡ ψ¹ ∷ Ωᵐ i []
fs-top i = cong (ψ¹ ∷_) (fsn-ψ¹ i)

row₃ : ∀ m → Row₀ (HB M₂) dr₂ (λ p → Pc (rk₃ p)) m (HtB.view (HB M₂) m) (dr₂ m)
row₃ end = rh _ _ refl λ { zero → fs-top 0 ; (suc i) → fs-top (suc i) }
row₃ (low (blk zero end)) = rl _ _ refl (fsn-ψ¹ 0) (λ i → fsn-ψ¹ (suc i))
row₃ (low (blk zero (low (blk zero end)))) = rb refl
row₃ (low (blk zero (low (blk (suc j) end)))) = rc _ (cof-Ωᵐ[] (suc j)) (fsT-Ωᵐ (suc j))
row₃ (low (blk zero (low (blk j (low ())))))
row₃ (low (blk (suc zero) end)) = rc _ (cof-Ωᵐ[] 0) (λ θ → cong (ψ¹ ∷_) (fsT-Ωᵐ 0 θ))
row₃ (low (blk (suc (suc j)) end)) = rc _ (cof-Ωᵐ[] (suc j)) (λ θ → cong (ψ¹ ∷_) (fsT-Ωᵐ (suc j) θ))
row₃ (low (blk (suc j) (low ())))

Px-M₂ : PxB (HB M₂) dr₂
Px-M₂ = record
  { P = λ p → Pc (rk₃ p)
  ; P-cof = λ m → f-cof (rk₃ m)
  ; P-pred = λ m → f-pred (rk₃ m)
  ; P-fsn = λ m → f-fsn (rk₃ m)
  ; P-tail = λ m → f-tail (rk₃ m)
  ; P-occ = λ m → f-occ (rk₃ m)
  ; P-lt = λ m → f-lt (rk₃ m)
  ; P-gt = λ m → f-gt (rk₃ m)
  ; P-cmp≡ = λ m → f-eq (rk₃ m)
  ; P-cmp-lt = λ {n} {H} {ν} τ q I → cl₃ τ (r< n H q) I
  ; P-cmp-gt = λ {n} {H} ν {τ} q I → cg₃ ν {τ} (r< H n q) I
  ; P-row = row₃
  }
  where
  f-cof : ∀ a w ws → cof (Pc a (w ∷ ws)) ≡ cof (w ∷ ws)
  f-cof (fin n) w ws = cof-Ωᵐ+ n w ws
  f-cof (top n) w ws = cof-ψ¹+ n w ws
  f-cof T̂ w ws = refl
  f-pred : ∀ a w ws → pred (Pc a (w ∷ ws)) ≡ Pc a (pred (w ∷ ws))
  f-pred (fin n) w ws = pred-Ωᵐ+ n w ws
  f-pred (top n) w ws = pred-ψ¹+ n w ws
  f-pred T̂ w ws = refl
  f-fsn : ∀ a w ws k → fsn (Pc a (w ∷ ws)) k ≡ Pc a (fsn (w ∷ ws) k)
  f-fsn (fin n) w ws k = fsn-Ωᵐ+ n w ws k
  f-fsn (top n) w ws k = fsn-ψ¹+ n w ws k
  f-fsn T̂ w ws k = refl
  f-tail : ∀ a τ → TailOf τ (Pc a τ)
  f-tail (fin n) τ = tailᵐ n τ
  f-tail (top n) τ = tailᵐ n τ
  f-tail T̂ τ = ts th
  f-occ : ∀ a τ → Occ (natT 1) (Pc a τ)
  f-occ (fin n) τ = oh
  f-occ (top n) τ = oh
  f-occ T̂ τ = oh
  f-lt : ∀ a τ {ν} → Idx ν → cmpᵀ (sucT ν) (Pc a τ) ≡ lt
  f-lt (fin n) τ I = ltμ (Ωᵐ n τ) I
  f-lt (top n) τ I = cmp-Cψ (Ctbl-suc (Idx-Ctbl I)) (Ωᵐ n τ)
  f-lt T̂ τ I = cmp-Cψ (Ctbl-suc (Idx-Ctbl I)) (ψ¹ ∷ τ)
  f-gt : ∀ a ν {w} → Idx w → cmpᵀ (sucT (Pc a ν)) w ≡ gt
  f-gt (fin n) ν I = gtμ (Ωᵐ n ν) I
  f-gt (top n) ν I = cmp-ψC (Idx-Ctbl I) (sucT (Ωᵐ n ν))
  f-gt T̂ ν I = cmp-ψC (Idx-Ctbl I) (ψ¹ ∷ sucT ν)
  f-eq : ∀ a ν τ → cmpᵀ (sucT (Pc a ν)) (Pc a τ) ≡ cmpᵀ (sucT ν) τ
  f-eq (fin n) ν τ = cmp≡ n ν τ
  f-eq (top n) ν τ = cmp≡ n ν τ
  f-eq T̂ ν τ = refl
```

## §4 第 $\alpha$ 行

```agda
private module Tp = OCF.Align.EmbVVTop (HB M₂) dr₂ Px-M₂

open import OCF.Align.ValLabLadder (HB M₂) using (V)

vv-M₂ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ ψ¹ ∷ Ω₁ ∷ [])) → ∀ {α} → α ≃ᴵ toLevel Y hY → VV (V end α) (ψ₀ᵗ (Ωt (ψ¹ ∷ ψ¹ ∷ θ)))
vv-M₂ Y hY lY nθ pm d = Tp.vv-row end Y hY lY nθ (NF-ψ⁺ 0 0 nθ (Lab→Ctbl lY nθ) pm) d

-- 第 1 行
vv-M₂-1 : VV (V end (suc zero)) (ψ₀ᵗ (Ωt (ψ¹ ∷ ψ¹ ∷ natT 1)))
vv-M₂-1 = vv-M₂ (suc zero) (hs hz) lab1 nf1 (E.hd< (E.ar< E.[]<)) (s≃ z≃)
```
