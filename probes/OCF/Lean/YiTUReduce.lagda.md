# YiTU：第 2 站闭项的上界归约到链点上的行界

> 验收文件 (读记号：参照 `Level`/`Value` 与 `BTBOFull`)。编译定理：`ub→goalᶻ : (∀ n → UBᴱ (pt n)) → Goalᶻ`，`UBᴱ x` 是 "折叠 `G x` 不高于某个 ψ₀(Ω_a)，a 的前驱嵌进 lvl x + 1"；推论 `ubs→goalᶻ` 用 `UB x = read (G x) ≼ ψ₀(Ω_{lvl x+1})`。层号比较不要 `VMᴸ`：值序经 `V2`/`V3` 给前驱嵌入 (`emb↑`，同 `BTBOFull.Upp` 的写法)；部分和经 `YiCeilRead.limc≼lim` 与 `YiXVRef.ref-absorb`；新旧塔第 1 项经 `rel≅ twᶻ1-R`。
> 前提的前两个实例是定理：`ub0`、`ub1` (来自 `YiXVStart.row0-upper`、`YiXVNeedOne.row`)。未证：`UB (pt n)`，n ≥ 2；第一个是 `UB (pt 2)`，要对一切可数层号上的折叠给值上界。
> 不否定什么，不改树、折叠、合法性。`absorb-suc` 抄自 `YiXVRef.ref-absorb` 的后半。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTUReduce where

open import Data.Nat using (ℕ; zero; suc; _⊔_; s≤s; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; n≤1+n; ≤⇒≤′)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
open import OCF.Lean.YiLSRead using (read; ◃→≺; HSr)
open import OCF.Lean.YiLSTw1 using (G; G-nz; pt; KG; lvl)
open import OCF.Lean.YiCeilRead using (ωx; mul≼ωx; limc≼lim)
open import OCF.Lean.YiXVRef using (ref-strict; ref-absorb)
open import OCF.Lean.YiXVStart using (Goal; Goalᶻ; row0-upper)
import OCF.Lean.YiXVNeedOne as N1
open import OCF.Lean.YiMTValue using (twᶻ1-R; btbo-tw1ᶻ)
open import OCF.Lean.YiMTTab using (twᶻ)
open import OCF.Lean.YiBRValue using (readRW; rel≅)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; ≼-trans; ≼-refl; ≅→≼; ≼l; l≼; ⊑→≼; ≺→s≼)
import OCF.Align.NoCumsum as N
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValAbsorb using (St; stz; sts; stl)
open import OCF.Align.BTBOFullLv using (SV; SV-L; SV-toLevel)
open import OCF.Align.BTBOFull using (St-bk; tr₀-bk; bk≅γ)
open import OCF.Align.BTBOFullEb using (V2)
open import OCF.Align.BTBOFullV3 using (V3; bkᴵ)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.YiMonoEmb using (PEmb-∘; PEmb-suc; PEmb-⊑)
```

## 参照列与部分和

```agda
γ⁺-step : ∀ k → D.γ (suc k) ≼ D.γ (suc (suc k))
γ⁺-step k = ≼-trans (mul≼ωx (D.γ (suc k)) 1) (ref-absorb k)

γ⁺-mono : ∀ {m k} → m ≤′ k → D.γ (suc m) ≼ D.γ (suc k)
γ⁺-mono ≤′-refl     = ≼-refl _
γ⁺-mono (≤′-step d) = ≼-trans (γ⁺-mono d) (γ⁺-step _)

absorb-suc : ∀ k → L.ψ⁰ (L.Ω (L.suc (D.L k))) ≼ D.γ (suc (suc k))
absorb-suc k = ⊑→≼ (L.ψ⁰ (L.Ω (L.suc (D.L k))))
  (L.Ψ⁰-mono (L.s⊑′ (L.toLevel-≺ (D.cert k) (D.cert (suc k)) (ref-strict k))))
```

每一行有某个参照项作上界 (下标可以任意) 就够：取下标的累计最大值，参照列逐步吸收。

```agda
module FromRows (r : ∀ n → Σ ℕ (λ m → read (G (pt n)) ≼ D.γ (suc m))) where
  M : ℕ → ℕ
  M zero    = proj₁ (r zero)
  M (suc n) = suc (M n ⊔ proj₁ (r (suc n)))

  bnd : ∀ n → read (G (pt n)) ≼ D.γ (suc (M n))
  bnd zero    = proj₂ (r zero)
  bnd (suc n) = ≼-trans (proj₂ (r (suc n))) (γ⁺-mono (≤⇒≤′ (≤-trans (m≤n⊔m (M n) _) (n≤1+n _))))

  mono : ∀ n → D.γ (suc (M n)) ≼ D.γ (suc (M (suc n)))
  mono n = γ⁺-mono (≤⇒≤′ (≤-trans (m≤m⊔n (M n) _) (n≤1+n _)))

  absorb : ∀ n → ωx (D.γ (suc (M n))) ≼ D.γ (suc (M (suc n)))
  absorb n = ≼-trans (ref-absorb (M n)) (γ⁺-mono (≤⇒≤′ (s≤s (m≤m⊔n (M n) _))))

  goal : Goal
  goal = ≼-trans (limc≼lim (λ n → G (pt n)) (λ n → G-nz (pt n)) (λ n → D.γ (suc (M n))) bnd mono absorb)
                 (l≼ (λ n → ≼l (M n) (≼-refl _)))

rows→goal : (∀ n → Σ ℕ (λ m → read (G (pt n)) ≼ D.γ (suc m))) → Goal
rows→goal = FromRows.goal

goalᶻ : Goal → Goalᶻ
goalᶻ g = ≼-trans (≅→≼ (rel≅ twᶻ1-R)) g
```

## 层号：值序给前驱嵌入

第 0 层的树读回严格 (`St-read`)，所以 `V2` 的两侧前提都有；`V1` 把层号嵌进累加规范化的层号，`V3` 把参照一侧的规范化层号嵌进下一项的层号。

```agda
St-read : (x : S.Tr S.zero) → St (read x)
St-read S.zero          = stz
St-read (S.suc a)       = sts (St-read a)
St-read (S.lim f a)     = stl (λ n → St-read (f n)) (λ n → ≺→s≼ (◃→≺ (a n)))
St-read (S.Ω () _)
St-read (S.up _ () _ _)

SVl : (x : S.Tr S.zero) → SV (lvl x)
SVl x = SV-toLevel (read x) (HSr x) (St-read x)

emb↑ : ∀ x m → read x ≼ D.γ m → PEmb (lvl x) (D.L (suc m))
emb↑ x m w =
  PEmb-∘ (PW₃ (V1 (SVl x)))
  (PEmb-∘ (PW₁ (V2 (bkᴵ (lvl x)) (bkᴵ (N.L m)) (St-bk (SVl x)) (St-bk (SV-L m)) w′))
          (PW₂ (N.cert (suc m)) (V3 (SV-L m))))
  where
  w′ : tr₀ (bkᴵ (lvl x)) ≼ tr₀ (bkᴵ (N.L m))
  w′ = ≼-trans (≅→≼ (L.≅-trans (tr₀-bk (lvl x)) (L.forget-toLevel (read x) (HSr x))))
       (≼-trans w (≅→≼ (L.≅-sym (bk≅γ m))))
```

## 行界的形状与归约

```agda
UB : S.Tr S.zero → Set
UB x = read (G x) ≼ L.ψ⁰ (L.Ω (L.suc (lvl x)))

UBᴱ : S.Tr S.zero → Set
UBᴱ x = Σ L.Ordᴵ (λ a → (read (G x) ≼ L.ψ⁰ (L.Ω a)) × PEmb a (L.suc (lvl x)))

UB→UBᴱ : ∀ {x} → UB x → UBᴱ x
UB→UBᴱ {x} u = L.suc (lvl x) , u , PEmb-⊑ L.⊑ᴵ-refl

step : ∀ x m → UBᴱ x → read x ≼ D.γ m → read (G x) ≼ D.γ (suc (suc (suc m)))
step x m (a , u , e) w =
  ≼-trans u (≼-trans (Ψ-emb (PEmb-∘ e (PEmb-suc (emb↑ x m w)))) (absorb-suc (suc m)))

module FromUB (ub : ∀ n → UBᴱ (pt n)) where
  chain : ∀ n → Σ ℕ (λ m → read (pt n) ≼ D.γ m)
  chain zero    = 0 , z≼
  chain (suc n) = suc (suc (suc (proj₁ (chain n)))) ,
    ≼-trans (≅→≼ (KG (pt n))) (step (pt n) (proj₁ (chain n)) (ub n) (proj₂ (chain n)))

  row : ∀ n → Σ ℕ (λ m → read (G (pt n)) ≼ D.γ (suc m))
  row n = suc (suc (proj₁ (chain n))) , step (pt n) (proj₁ (chain n)) (ub n) (proj₂ (chain n))

ub→goal : (∀ n → UBᴱ (pt n)) → Goal
ub→goal ub = rows→goal (FromUB.row ub)

ub→goalᶻ : (∀ n → UBᴱ (pt n)) → Goalᶻ
ub→goalᶻ ub = goalᶻ (ub→goal ub)

ubs→goalᶻ : (∀ n → UB (pt n)) → Goalᶻ
ubs→goalᶻ ub = ub→goalᶻ (λ n → UB→UBᴱ (ub n))

ub→same : (∀ n → UBᴱ (pt n)) → (readRW (twᶻ 1) ≼ D.BTBOᴵ) × (D.BTBOᴵ ≼ readRW (twᶻ 1))
ub→same ub = ub→goalᶻ ub , btbo-tw1ᶻ
```

## 前提的前两个实例

`pt 1` 的层号逐项是有限层号 (`comp`)，所以 ω ⊑ lvl (pt 1) + 1。

```agda
ub0 : UB (pt 0)
ub0 = row0-upper

natT : ℕ → S.Tr S.zero
natT zero    = S.zero
natT (suc n) = S.suc (natT n)

one+ : ∀ k → S.suc S.zero O.+ natT k ≡ natT (suc k)
one+ zero    = refl
one+ (suc k) = cong S.suc (one+ k)

it≡ : ∀ n → O.iter (S.suc S.zero O.+_) (S.suc S.zero) n ≡ natT (suc n)
it≡ zero    = refl
it≡ (suc n) = subst (λ t → S.suc S.zero O.+ t ≡ natT (suc (suc n))) (sym (it≡ n)) (one+ (suc n))

rd≡ : ∀ k → read (natT k) ≡ L.natᶜ k
rd≡ zero    = refl
rd≡ (suc k) = cong L.suc (rd≡ k)

comp : ∀ n (h : L.HS (read (O.iter (S.suc S.zero O.+_) (S.suc S.zero) n))) →
  L.toLevel (read (O.iter (S.suc S.zero O.+_) (S.suc S.zero) n)) h ≡ L.natᴵ (suc n)
comp n h = N1.level-point (suc n) _ (subst (λ t → read t ≡ L.natᶜ (suc n)) (sym (it≡ n)) (rd≡ (suc n))) h

ω⊑ : L.ωᴵ L.⊑ᴵ L.suc (lvl (pt 1))
ω⊑ = L.Sim→⊑ᴵ (λ { (L.lim k q) → L.suc (L.lim k (subst (λ t → _ L.<ᴵ t) (sym (comp k _)) (L.suc q))) })

ub1 : UB (pt 1)
ub1 = ≼-trans N1.row (⊑→≼ _ (L.Ψ⁰-mono ω⊑))
```
