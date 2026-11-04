# 值验收 (实例): 码 $\omega^2$

> 入口 [EmbVV](EmbVV.lagda.md). 读记号. `Px-ω²`: 码 `ω²ᶜ` 上的前缀结构. 位置 `blk i end` (值 $\omega\cdot(i+1)$) 读 $\psi_1(1)\cdot(i+1)$, 位置 `blk i (blk j end)` 读 $\psi_1(1)\cdot i+\Omega\cdot(j+1)$, 顶读 $\psi_1(2)$. 链行 `blk (i+1) end` 的第 0 项换成 `blk i end` 的行 (`repl`), 其余逐项对上; 顶的第 0 项本来就对 (`keep`).
>
> - `vv-E`: 对一切 $i$, 一切 $\theta$: 位置 $\omega\cdot(i+2)$ 的第 $\alpha$ 行过值验收, 读 $\psi_0(\Omega_{\psi_1(1)\cdot(i+2)+\theta})$. 这是 $\omega\cdot n$ 的一般定理.
> - `vv-ω²`: **无条件**, $\psi_0(\Omega_{\psi_1(2)})$. `vv-ω²-if` 的前提由 `vv-E` 给出.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVInstO2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (_∷_; []; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Free.Level hiding (z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
open import OCF.Free.Force using (forceᴺ)
import OCF.Align.EBO as E
open E using (T; PT; natT; Ωt; cmpᵀ; sucT; lt; gt; eq; cof; cω; pred; fsn; fsT; 𝟏) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.Correspond using (fs-rep)
open import OCF.Align.EmbVVLZStandardOmega using (Ω₁; Ωᵐ; ψ¹; pk; cof-pk; pred-pk; fsn-pk; fsT-pk; pk-snoc; cof-Ωᵐ[]; cof-Ωᵐ+; pred-Ωᵐ+; fsn-Ωᵐ+; fsT-Ωᵐ; fsn-ψ¹; NF₁; n[])
open import OCF.Align.LadderLabZSystemOmega using (TailOf; th; ts; Occ; oh; Ctbl-suc)
open import OCF.Align.EmbVVOZDecouple using (Idx)
open import OCF.Align.EmbVVOZGoodLBase using (Idx-Ctbl; Lab→Ctbl; nf1; lab1)
open import OCF.Align.EmbVVOZUniform5Head using (ltμ; gtμ)
open import OCF.Align.EmbVVOZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0)
open import OCF.Align.LadderNFTree using (_<ᴸ_; zero; suc; dn; s<s; z<s)
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ωᶜ; ω²ᶜ)
open import OCF.Align.EmbVVBBase
open import OCF.Align.EmbVVMode using (HdM; keep; drop; repl)
open import OCF.Align.EmbVVEq using (_≃ᴵ_; z≃; s≃)
open import OCF.Align.EmbVVNF using (NF-ψ⁺)
open import OCF.Align.EmbVVInstM2 using (cmp≡; cmp-ltᵐ; cmp-gtᵐ; tailᵐ; cmp-Cψ; cmp-ψC; ltℕ)
import OCF.Align.EmbVVTop
open import OCF.Align.ValLabPos using (VV; module Chain; vv-ω²-if)
open import OCF.Align.ValueJudgeBase using (_≼_; _≈ᵛ_; ≼-trans; ≅→≼; ⊑→≼)
open import OCF.Align.OrdLabRead using (tω²; ψ²ᵗ; fsn-ψ₀Ω; ev₀; module C²)
open import OCF.Align.OrdLabReadTop using (top-row; head-ω²0; head-ω²1)
import OCF.Align.ValLabRow
module V² = OCF.Align.ValLabRow (HB ω²ᶜ)
```

## §1 记号

```agda
cof-pk′ : ∀ i x xs → cof (pk i (x ∷ xs)) ≡ cof (x ∷ xs)
cof-pk′ zero x xs = refl
cof-pk′ (suc i) x xs = cof-pk i x xs

pred-pk′ : ∀ i x xs → pred (pk i (x ∷ xs)) ≡ pk i (pred (x ∷ xs))
pred-pk′ zero x xs = refl
pred-pk′ (suc i) x xs = pred-pk i x xs

fsn-pk′ : ∀ i x xs k → fsn (pk i (x ∷ xs)) k ≡ pk i (fsn (x ∷ xs) k)
fsn-pk′ zero x xs k = refl
fsn-pk′ (suc i) x xs k = fsn-pk i x xs k

fsT-pk′ : ∀ i x xs η → fsT (pk i (x ∷ xs)) η ≡ pk i (fsT (x ∷ xs) η)
fsT-pk′ zero x xs η = refl
fsT-pk′ (suc i) x xs η = fsT-pk i x xs η

tl-pk : ∀ i {τ x r} → TailOf τ (x ∷ r) → TailOf τ (pk i (x ∷ r))
tl-pk zero t = t
tl-pk (suc i) t = ts (tl-pk i t)

cmp-pk : ∀ i a b → cmpᵀ (sucT (pk i a)) (pk i b) ≡ cmpᵀ (sucT a) b
cmp-pk zero a b = refl
cmp-pk (suc i) a b = cmp-pk i a b

-- 可数项对首项下标 1 的项恒 lt, 反之恒 gt
cmp-C1 : ∀ {v} → Ctbl v → ∀ a X → cmpᵀ v (ψᵗ (natT 1) a ∷ X) ≡ lt
cmp-C1 c[] a X = refl
cmp-C1 (c∷ c) a X = refl

cmp-1C : ∀ {v} → Ctbl v → ∀ a X → cmpᵀ (ψᵗ (natT 1) a ∷ X) v ≡ gt
cmp-1C c[] a X = refl
cmp-1C (c∷ c) a X = refl

-- 少一层前缀
ltp : ∀ {i i′} → i <ᴸ i′ → ∀ ν a B → Ctbl (sucT ν) → cmpᵀ (sucT (pk i (ψ¹ ∷ ν))) (pk i′ (ψᵗ (natT 1) a ∷ B)) ≡ lt
ltp {i = zero} {i′ = suc zero} q ν a B c = cmp-C1 c a B
ltp {i = zero} {i′ = suc (suc i′)} q ν a B c = cmp-C1 c (natT 1) (pk i′ (ψᵗ (natT 1) a ∷ B))
ltp {suc i} {suc i′} q ν a B c = ltp (dn q) ν a B c

gtp : ∀ {i i′} → i <ᴸ i′ → ∀ A a B → Ctbl B → cmpᵀ (sucT (pk i′ (ψᵗ (natT 1) a ∷ A))) (pk i (ψ¹ ∷ B)) ≡ gt
gtp {i = zero} {i′ = suc zero} q A a B c = cmp-1C c a (sucT A)
gtp {i = zero} {i′ = suc (suc i′)} q A a B c = cmp-1C c (natT 1) (sucT (pk i′ (ψᵗ (natT 1) a ∷ A)))
gtp {suc i} {suc i′} q A a B c = gtp (dn q) A a B c

ltΩ : ∀ {i i′} → i <ᴸ i′ → ∀ A a B → cmpᵀ (sucT (pk i (Ω₁ ∷ A))) (pk i′ (ψᵗ (natT 1) a ∷ B)) ≡ lt
ltΩ {i = zero} {suc i′} q A a B = refl
ltΩ {suc i} {suc i′} q A a B = ltΩ (dn q) A a B

gtΩ : ∀ {i i′} → i <ᴸ i′ → ∀ A a B → cmpᵀ (sucT (pk i′ (ψᵗ (natT 1) a ∷ A))) (pk i (Ω₁ ∷ B)) ≡ gt
gtΩ {i = zero} {suc i′} q A a B = refl
gtΩ {suc i} {suc i′} q A a B = gtΩ (dn q) A a B
```

## §2 高度

```agda
data H² : Set where
  Ê : ℕ → H²
  F̂ : ℕ → ℕ → H²
  T̂ : H²

infix 4 _<²_
data _<²_ : H² → H² → Set where
  ff : ∀ {i j k} → j <ᴸ k → F̂ i j <² F̂ i k
  fe : ∀ {i j} → F̂ i j <² Ê i
  ee : ∀ {i i′} → i <ᴸ i′ → Ê i <² Ê i′
  ef : ∀ {i i′ j} → i <ᴸ i′ → Ê i <² F̂ i′ j
  f′ : ∀ {i i′ j j′} → i <ᴸ i′ → F̂ i j <² F̂ i′ j′
  fe′ : ∀ {i i′ j} → i <ᴸ i′ → F̂ i j <² Ê i′
  eT : ∀ {i} → Ê i <² T̂
  fT : ∀ {i j} → F̂ i j <² T̂

ψ² : PT
ψ² = ψᵗ (natT 1) (natT 2)

Pc : H² → T → T
Pc (Ê i) τ = pk i (ψ¹ ∷ τ)
Pc (F̂ i j) τ = pk i (Ω₁ ∷ Ωᵐ j τ)
Pc T̂ τ = ψ² ∷ τ

rkb : ℕ → Pos (cs ωᶜ) → H²
rkb i end = Ê i
rkb i (low (blk j end)) = F̂ i j
rkb i (low (blk j (low ())))

rk² : Pos (cs ω²ᶜ) → H²
rk² end = T̂
rk² (low (blk i p)) = rkb i p

r-in : ∀ i p q → p <ᴾ q → rkb i p <² rkb i q
r-in i (low (blk j end)) end x = fe
r-in i (low (blk j (low ()))) q x
r-in i (low (blk j end)) (low (blk k end)) x = ff (ltℕ j k x)
r-in i (low (blk j end)) (low (blk k (low ()))) x

r-up : ∀ {i i′} → i <ᴸ i′ → ∀ p q → rkb i p <² rkb i′ q
r-up q end end = ee q
r-up q end (low (blk j end)) = ef q
r-up q end (low (blk j (low ())))
r-up q (low (blk j end)) end = fe′ q
r-up q (low (blk j end)) (low (blk k end)) = f′ q
r-up q (low (blk j end)) (low (blk k (low ())))
r-up q (low (blk j (low ()))) r

ltB-ω : ∀ i i′ p q → ltB (λ _ → ωᶜ) i i′ p q → (i <ᴸ i′) ⊎ Σ (i ≡ i′) (λ e → subst (λ _ → Pos (cs ωᶜ)) e p <ᴾ q)
ltB-ω zero zero p q x = inj₂ (refl , x)
ltB-ω zero (suc k) p q x = inj₁ (z<s k)
ltB-ω (suc i) (suc k) p q x with ltB-ω i k p q x
... | inj₁ l = inj₁ (s<s l)
... | inj₂ (refl , y) = inj₂ (refl , y)

r² : ∀ p q → p <ᴾ q → rk² p <² rk² q
r² (low (blk i end)) end x = eT
r² (low (blk i (low (blk j end)))) end x = fT
r² (low (blk i (low (blk j (low ()))))) end x
r² (low (blk i p)) (low (blk i′ q)) x with ltB-ω i i′ p q x
... | inj₁ l = r-up l p q
... | inj₂ (refl , y) = r-in i p q y

cl² : ∀ {n H ν} τ → n <² H → Idx ν → cmpᵀ (sucT (Pc n ν)) (Pc H τ) ≡ lt
cl² {F̂ i j} {F̂ i k} {ν} τ (ff q) I = trans (cmp-pk i (Ω₁ ∷ Ωᵐ j ν) (Ω₁ ∷ Ωᵐ k τ)) (cmp-ltᵐ {n = suc j} {H = suc k} τ (s<s q) I)
cl² {F̂ i j} {Ê i} {ν} τ fe I = trans (cmp-pk i (Ω₁ ∷ Ωᵐ j ν) (ψ¹ ∷ τ)) refl
cl² {Ê i} {Ê i′} {ν} τ (ee q) I = ltp q ν (natT 1) τ (Ctbl-suc (Idx-Ctbl I))
cl² {Ê i} {F̂ i′ j} {ν} τ (ef q) I = ltp q ν [] (Ωᵐ j τ) (Ctbl-suc (Idx-Ctbl I))
cl² {F̂ i j} {F̂ i′ j′} {ν} τ (f′ q) I = ltΩ q (Ωᵐ j ν) [] (Ωᵐ j′ τ)
cl² {F̂ i j} {Ê i′} {ν} τ (fe′ q) I = ltΩ q (Ωᵐ j ν) (natT 1) τ
cl² {Ê zero} τ eT I = refl
cl² {Ê (suc i)} τ eT I = refl
cl² {F̂ zero j} τ fT I = refl
cl² {F̂ (suc i) j} τ fT I = refl

cg² : ∀ {n H} ν {τ} → H <² n → Idx τ → cmpᵀ (sucT (Pc n ν)) (Pc H τ) ≡ gt
cg² {F̂ i k} {F̂ i j} ν {τ} (ff q) I = trans (cmp-pk i (Ω₁ ∷ Ωᵐ k ν) (Ω₁ ∷ Ωᵐ j τ)) (cmp-gtᵐ {n = suc k} {H = suc j} ν {τ} (s<s q) I)
cg² {Ê i} {F̂ i j} ν {τ} fe I = trans (cmp-pk i (ψ¹ ∷ ν) (Ω₁ ∷ Ωᵐ j τ)) refl
cg² {Ê i′} {Ê i} ν {τ} (ee q) I = gtp q ν (natT 1) τ (Idx-Ctbl I)
cg² {F̂ i′ j} {Ê i} ν {τ} (ef q) I = gtp q (Ωᵐ j ν) [] τ (Idx-Ctbl I)
cg² {F̂ i′ j′} {F̂ i j} ν {τ} (f′ q) I = gtΩ q (Ωᵐ j′ ν) [] (Ωᵐ j τ)
cg² {Ê i′} {F̂ i j} ν {τ} (fe′ q) I = gtΩ q ν (natT 1) (Ωᵐ j τ)
cg² {H = Ê zero} ν eT I = refl
cg² {H = Ê (suc i)} ν eT I = refl
cg² {H = F̂ zero j} ν fT I = refl
cg² {H = F̂ (suc i) j} ν fT I = refl
```

## §3 前缀结构

```agda
lt-suc : ∀ i → ltB (λ _ → ωᶜ) i (suc i) end end
lt-suc zero = tt
lt-suc (suc i) = lt-suc i

dr² : ∀ m → HdM (HB ω²ᶜ) m
dr² end = keep
dr² (low (blk zero end)) = keep
dr² (low (blk (suc i) end)) = repl (low (blk i end)) (lt-suc i)
dr² (low (blk i (low p))) = keep

rep-pk : ∀ i → replicate (suc i) ψ¹ ≡ pk i (ψ¹ ∷ [])
rep-pk zero = refl
rep-pk (suc i) = cong (ψ¹ ∷_) (rep-pk i)

fs-ψ² : ∀ i → fsn (ψ² ∷ []) (suc i) ≡ pk i (ψ¹ ∷ [])
fs-ψ² i = trans (fs-rep (natT 1) 𝟏 (𝟏 ∷ []) refl (suc i)) (rep-pk i)

row² : ∀ m → Row₀ (HB ω²ᶜ) dr² (λ p → Pc (rk² p)) m (HtB.view (HB ω²ᶜ) m) (dr² m)
row² end = rl _ _ refl (fs-rep (natT 1) 𝟏 (𝟏 ∷ []) refl 0) fs-ψ²
row² (low (blk zero end)) = rl _ _ refl (fsn-ψ¹ 0) (λ i → fsn-ψ¹ (suc i))
row² (low (blk (suc i) end)) =
  rr (lt-suc i) _ _ (cof-pk i ψ¹ [])
     (trans (fsn-pk i ψ¹ [] 0) (trans (cong (λ z → ψ¹ ∷ pk i z) (fsn-ψ¹ 0)) (pk-snoc i [])))
     (λ k → trans (fsn-pk i ψ¹ [] (suc k)) (cong (λ z → ψ¹ ∷ pk i z) (fsn-ψ¹ (suc k))))
row² (low (blk zero (low (blk zero end)))) = rb refl
row² (low (blk zero (low (blk (suc j) end)))) = rc _ (cof-Ωᵐ[] (suc j)) (fsT-Ωᵐ (suc j))
row² (low (blk (suc i) (low (blk zero end)))) = rc _ (cof-pk i Ω₁ []) (λ θ → trans (fsT-pk i Ω₁ [] θ) (pk-snoc i θ))
row² (low (blk (suc i) (low (blk (suc j) end)))) =
  rc _ (trans (cof-pk i Ω₁ (Ωᵐ (suc j) [])) (cof-Ωᵐ[] (suc j))) (λ θ → trans (fsT-pk i Ω₁ (Ωᵐ (suc j) []) θ) (cong (λ z → ψ¹ ∷ pk i z) (fsT-Ωᵐ (suc j) θ)))
row² (low (blk i (low (blk j (low ())))))

Px-ω² : PxB (HB ω²ᶜ) dr²
Px-ω² = record
  { P = λ p → Pc (rk² p)
  ; P-cof = λ m → f-cof (rk² m)
  ; P-pred = λ m → f-pred (rk² m)
  ; P-fsn = λ m → f-fsn (rk² m)
  ; P-tail = λ m → f-tail (rk² m)
  ; P-occ = λ m → f-occ (rk² m)
  ; P-lt = λ m → f-lt (rk² m)
  ; P-gt = λ m → f-gt (rk² m)
  ; P-cmp≡ = λ m → f-eq (rk² m)
  ; P-cmp-lt = λ {n} {H} {ν} τ q I → cl² τ (r² n H q) I
  ; P-cmp-gt = λ {n} {H} ν {τ} q I → cg² ν {τ} (r² H n q) I
  ; P-row = row²
  }
  where
  f-cof : ∀ a w ws → cof (Pc a (w ∷ ws)) ≡ cof (w ∷ ws)
  f-cof (Ê i) w ws = cof-pk′ i ψ¹ (w ∷ ws)
  f-cof (F̂ i j) w ws = trans (cof-pk′ i Ω₁ (Ωᵐ j (w ∷ ws))) (cof-Ωᵐ+ j w ws)
  f-cof T̂ w ws = refl
  f-pred : ∀ a w ws → pred (Pc a (w ∷ ws)) ≡ Pc a (pred (w ∷ ws))
  f-pred (Ê i) w ws = pred-pk′ i ψ¹ (w ∷ ws)
  f-pred (F̂ i j) w ws = trans (pred-pk′ i Ω₁ (Ωᵐ j (w ∷ ws))) (cong (pk i) (pred-Ωᵐ+ j w ws))
  f-pred T̂ w ws = refl
  f-fsn : ∀ a w ws k → fsn (Pc a (w ∷ ws)) k ≡ Pc a (fsn (w ∷ ws) k)
  f-fsn (Ê i) w ws k = fsn-pk′ i ψ¹ (w ∷ ws) k
  f-fsn (F̂ i j) w ws k = trans (fsn-pk′ i Ω₁ (Ωᵐ j (w ∷ ws)) k) (cong (pk i) (fsn-Ωᵐ+ j w ws k))
  f-fsn T̂ w ws k = refl
  f-tail : ∀ a τ → TailOf τ (Pc a τ)
  f-tail (Ê i) τ = tl-pk i th
  f-tail (F̂ i j) τ = tl-pk i (tailᵐ j τ)
  f-tail T̂ τ = th
  f-occ : ∀ a τ → Occ (natT 1) (Pc a τ)
  f-occ (Ê zero) τ = oh
  f-occ (Ê (suc i)) τ = oh
  f-occ (F̂ zero j) τ = oh
  f-occ (F̂ (suc i) j) τ = oh
  f-occ T̂ τ = oh
  f-lt : ∀ a τ {ν} → Idx ν → cmpᵀ (sucT ν) (Pc a τ) ≡ lt
  f-lt (Ê zero) τ I = cmp-C1 (Ctbl-suc (Idx-Ctbl I)) (natT 1) τ
  f-lt (Ê (suc i)) τ I = cmp-C1 (Ctbl-suc (Idx-Ctbl I)) (natT 1) (pk i (ψ¹ ∷ τ))
  f-lt (F̂ zero j) τ I = cmp-C1 (Ctbl-suc (Idx-Ctbl I)) [] (Ωᵐ j τ)
  f-lt (F̂ (suc i) j) τ I = cmp-C1 (Ctbl-suc (Idx-Ctbl I)) (natT 1) (pk i (Ω₁ ∷ Ωᵐ j τ))
  f-lt T̂ τ I = cmp-C1 (Ctbl-suc (Idx-Ctbl I)) (natT 2) τ
  f-gt : ∀ a ν {w} → Idx w → cmpᵀ (sucT (Pc a ν)) w ≡ gt
  f-gt (Ê zero) ν I = cmp-1C (Idx-Ctbl I) (natT 1) (sucT ν)
  f-gt (Ê (suc i)) ν I = cmp-1C (Idx-Ctbl I) (natT 1) (sucT (pk i (ψ¹ ∷ ν)))
  f-gt (F̂ zero j) ν I = cmp-1C (Idx-Ctbl I) [] (sucT (Ωᵐ j ν))
  f-gt (F̂ (suc i) j) ν I = cmp-1C (Idx-Ctbl I) (natT 1) (sucT (pk i (Ω₁ ∷ Ωᵐ j ν)))
  f-gt T̂ ν I = cmp-1C (Idx-Ctbl I) (natT 2) (sucT ν)
  f-eq : ∀ a ν τ → cmpᵀ (sucT (Pc a ν)) (Pc a τ) ≡ cmpᵀ (sucT ν) τ
  f-eq (Ê i) ν τ = cmp-pk i (ψ¹ ∷ ν) (ψ¹ ∷ τ)
  f-eq (F̂ i j) ν τ = trans (cmp-pk i (Ω₁ ∷ Ωᵐ j ν) (Ω₁ ∷ Ωᵐ j τ)) (cmp≡ j ν τ)
  f-eq T̂ ν τ = refl
```

## §4 第 $\alpha$ 行, $\omega\cdot n$

```agda
private module Tp = OCF.Align.EmbVVTop (HB ω²ᶜ) dr² Px-ω²
private module Ch = Chain (HB ω²ᶜ)

open V² using (V)

-- 位置 ω·(i+2)
vv-E : ∀ i {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ pk i (ψ¹ ∷ Ω₁ ∷ []))) → ∀ {α} → α ≃ᴵ toLevel Y hY →
       VV (V (low (blk (suc i) end)) α) (ψ₀ᵗ (Ωt (ψ¹ ∷ pk i (ψ¹ ∷ θ))))
vv-E i Y hY lY nθ pm d = Tp.vv-row (low (blk (suc i) end)) Y hY lY nθ (NF-ψ⁺ i 0 nθ (Lab→Ctbl lY nθ) pm) d

-- 第 0 行
vv-E₀ : ∀ i → VV (V (low (blk (suc i) end)) zero) (ψ₀ᵗ (Ωt (ψ¹ ∷ pk i (ψ¹ ∷ []))))
vv-E₀ i = vv-E i Ord₊.zero hz (l0 refl z≅₀) n[] E.[]< z≃
  where
  z≅₀ : zero ≅ zero
  z≅₀ = ≅-refl⁰ zero
```

## §5 $\psi_0(\Omega_{\psi_1(2)})$

第 $k+2$ 项由 `vv-E₀` 给. 第 0, 1 项是主线的项本身. 单调由主线的 `V-grow` 经同值搬到参照树.

```agda
fs-tω² : ∀ k → fsn tω² (suc (suc k)) ≡ ψ₀ᵗ (Ωt (ψ¹ ∷ pk k (ψ¹ ∷ [])))
fs-tω² k = trans (fsn-ψ₀Ω (ψ² ∷ []) refl (suc (suc k))) (cong (λ z → ψ₀ᵗ (Ωt z)) (fs-ψ² (suc k)))

module Assemble {X Y₀ : Ordᶜ zero} {Yr : ℕ → Ordᶜ zero} (Rw : C².ChainRow X Yr)
  (L₀ : Lab (C².ChainRow.h Rw 0) (fsn tω² 0)) (L₁ : Lab (C².ChainRow.h Rw 1) (fsn tω² 1))
  (e-r : ∀ i → Yr i ≅ V (low (blk i end)) zero) where
  h = C².ChainRow.h Rw
  Zk : ℕ → Ordᶜ zero
  Zk zero = h 0
  Zk (suc zero) = h 1
  Zk (suc (suc k)) = proj₁ (vv-E₀ k)

  LZ : ∀ n → Lab (Zk n) (fsn tω² n)
  LZ zero = L₀
  LZ (suc zero) = L₁
  LZ (suc (suc k)) = subst (Lab (Zk (suc (suc k)))) (sym (fs-tω² k)) (proj₁ (proj₂ (vv-E₀ k)))

  eq-1 : h 1 ≅ V (low (blk 0 end)) zero
  eq-1 = ≅-trans (C².ChainRow.rest Rw 0) (e-r 0)

  eZ : ∀ i → V (low (blk i end)) zero ≈ᵛ Zk (suc i)
  eZ zero = ≅→≼ (≅-sym eq-1) , ≅→≼ eq-1
  eZ (suc k) = proj₁ (proj₂ (proj₂ (vv-E₀ k))) , proj₂ (proj₂ (proj₂ (vv-E₀ k)))

  grow≼ : ∀ i → V (low (blk i end)) zero ≼ V (low (blk (suc i) end)) zero
  grow≼ i = ⊑→≼ (V (low (blk i end)) zero) (V².≺→⊑₀ (V².V-grow {low (blk i end)} {low (blk (suc i) end)} (lt-suc i)))

  stZ : ∀ n → Zk n ≼ Zk (suc n)
  stZ zero = ⊑→≼ (h 0) (C².ChainRow.step Rw 0)
  stZ (suc i) = ≼-trans (proj₂ (eZ i)) (≼-trans (grow≼ i) (proj₁ (eZ (suc i))))

vv-ω² : VV (V end zero) tω²
vv-ω² = Ch.vv-chain {end} {λ i → low (blk i end)} {λ i → tt} {tω²} refl refl 1 A.Zk A.LZ A.stZ A.eZ
  where
  Rw₀ = top-row ev₀ zero
  module A = Assemble {Y₀ = Ord₊.zero} Rw₀ (head-ω²0 ev₀ zero) (head-ω²1 ev₀ zero) (λ i → V².V-G (low (blk i end)) zero (V².GV (low (blk i end)) zero))

-- `vv-ω²-if` 的前提实例: 同一组 Z
vv-ω²-via : VV (V².V end zero) tω²
vv-ω²-via = vv-ω²-if A.Zk A.LZ A.stZ A.eZ
  where
  module A = Assemble {Y₀ = Ord₊.zero} (top-row ev₀ zero) (head-ω²0 ev₀ zero) (head-ω²1 ev₀ zero) (λ i → V².V-G (low (blk i end)) zero (V².GV (low (blk i end)) zero))
```

第 1 行, 对一切 $i$: 位置 $\omega\cdot(i+2)$, 读 $\psi_0(\Omega_{\psi_1(1)\cdot(i+2)+1})$.

```agda
vv-E-1 : ∀ i → VV (V (low (blk (suc i) end)) (suc zero)) (ψ₀ᵗ (Ωt (ψ¹ ∷ pk i (ψ¹ ∷ natT 1))))
vv-E-1 i = vv-E i (Ord₊.suc Ord₊.zero) (hs hz) lab1 nf1 (E.hd< (E.ar< E.[]<)) (s≃ z≃)
```
