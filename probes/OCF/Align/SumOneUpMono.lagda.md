# `SumOne.T₁` 的上界 (五): 带标签的树按记号的序排列

> **验收文件, 定理与条件定理.** `lab-mono`: 两个标准形 (`NF₁`) 的带标签的树, 记号小的严格在下. 由 `StandardOmega.cofin₁` (共尾性) 对标签归纳, 不经过任何折叠的单调. 于是 `upper-lab : StageBelow → Upper`: `T₁` 的每一段只要被**某个**小于 $\psi_0(\Omega_{\Omega+1})$ 的标准形的带标签的树压住, 上界就成立. 前提的实例: `Sω-below`, `S¹-below`.
> `StageBelow` 没有证, 也没有反驳. 入口 [SumOneUp](SumOneUp.lagda.md). `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneUpMono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.Level hiding (below)
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-suc; ≼-refl; ≺→s≼)
import OCF.Align.EBO as E
open E using (T; _<ᵀ_; c0; c1; cω; pred; fsn)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; cof-ne)
open import OCF.Align.Closure using (lt→<)
open import OCF.Align.Bachmann using (<sucT)
open import OCF.Align.StandardOmega using (NF₁; NF₁-pred; NF₁-fsn; cofin₁; tO-NF; γ′-NF; nfts)
open import OCF.Align.Stage2 using (Lab-uniq; tO; ts; ts-label; γ′ᴱ; χ; χ1-label)
open import OCF.Align.TreeLevelsO8 using (reference-label-value; Upper; prefix; upper-from-positive-prefixes)
open import OCF.Align.TLRuleVar using (trA)
open import OCF.Align.SumOneUpStation using (Sω; Sω≈)
open import OCF.Align.SumOneUpChain using (S¹; S¹≈)
open import OCF.Align.SumOneUpRed using (Ref₁; S²; Open₂)
```

## §1 序的对应

对 `u` 的标签归纳. 后继: 离散性 (`<sucT`). 极限: 共尾性给出 $n$ 使 $v<u[n]$. 这是 `Bachmann.oc` 的写法, 换成一般的 `Lab` 与 `NF₁`.

```agda
lab-mono : ∀ {X u} → NF₁ u → Lab X u → ∀ {Y v} → NF₁ v → Lab Y v → v <ᵀ u → Y ≺ X
lab-mono {u = []} nu lx nv ly ()
lab-mono {u = x ∷ xs} nu (l0 c e) nv ly p = ⊥-elim (cof-ne x xs c)
lab-mono {u = x ∷ xs} nu (l1 c e l) {Y = Y} {v = v} nv ly p
  with <sucT (pred (x ∷ xs)) (subst (v <ᵀ_) (sym (E.pred-suc (x ∷ xs) c)) p)
... | inj₁ q = ≺-respʳ (≺s (lab-mono (NF₁-pred nu c) l nv ly q)) (≅-sym e)
... | inj₂ e′ = ≺-respʳ (≺z (Lab-uniq (subst (Lab Y) e′ ly) l)) (≅-sym e)
lab-mono {u = x ∷ xs} nu (lω c e h) nv ly p with cofin₁ nu c nv p
... | n , q = ≺-respʳ (≺l n (lab-mono (NF₁-fsn nu c n) (h n) nv ly q)) (≅-sym e)
```

## §2 上界的前提: 每一段在某个带标签的树之下

`Below X`: `X` 被一个标准形 `term` 的带标签的树压住, `term` 小于 $\psi_0(\Omega_{\Omega+1})$ (`tO`). 不要求 `term` 在参照树的基本列路径上.

```agda
record Below (X : Ordᶜ zero) : Set where
  constructor mkB
  field
    {tree} : Ordᶜ zero
    {term} : T
    nf  : NF₁ term
    lab : Lab tree term
    lt  : term <ᵀ tO
    le  : X ≼ tree
open Below

below→ref : ∀ {X} → Below X → X ≼ Ref₁
below→ref b = ≼-trans (le b) (≼-trans (≼-suc (≼-refl _)) (≺→s≼ (lab-mono tO-NF reference-label-value (nf b) (lab b) (lt b))))

StageBelow : Set
StageBelow = ∀ n → Below (trA (prefix (suc n)))

upper-lab : StageBelow → Upper
upper-lab P = upper-from-positive-prefixes (λ n → below→ref (P n))

Sω-below : Below (trA Sω)
Sω-below = mkB nfts ts-label (lt→< ts tO refl) (proj₁ Sω≈)

S¹-below : Below (trA S¹)
S¹-below = mkB (γ′-NF 1) χ1-label (lt→< (γ′ᴱ 1) tO refl) (proj₁ S¹≈)

-- 第一个未定的站, 写成同一形状
S²-target : Set
S²-target = Below (trA S²)

S²-target→ : S²-target → Open₂
S²-target→ = below→ref
```
