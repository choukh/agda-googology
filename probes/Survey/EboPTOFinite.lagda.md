# 可数初段上的有限下标

第四层，无条件。可数标准项严格低于本地 ψ₀(Ωₙ₊₁)，恰好当它的所有塌缩下标都是不超过 n 的自然数。在这个初段内，固定下标的嵌套塔给出 Buchholz 计算迭代归纳定义强度时所用的共尾列。
文献中的下标是符号，本地下标是项。恢复有限下标时须检查参数和和式的尾部。[Buchholz，§§2–3](https://epub.ub.uni-muenchen.de/3841/1/3841.pdf)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.EboPTOFinite where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (<-cmp; <⇒≱)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef using (T; ψ; natT; Ωt; _<ᵀ_; hd<; ar<; lv<; tl<; []<)
open import OCF.Align.EboLeanBase

data Indices (n : ℕ) : T → Set where
  empty : Indices n []
  cons  : ∀ {j a ts} → j ≤ n → Indices n a → Indices n ts → Indices n (ψ (natT j) a ∷ ts)

row : ℕ → T
row n = ψ [] (Ωt (natT (suc n))) ∷ []

below-numeral : ∀ {u} n → u <ᵀ natT n → Σ ℕ λ j → (u ≡ natT j) × (j < n)
below-numeral zero ()
below-numeral (suc n) []< = 0 , refl , s≤s z≤n
below-numeral (suc n) (hd< (lv< ()))
below-numeral (suc n) (hd< (ar< ()))
below-numeral (suc n) (tl< p) with below-numeral n p
... | j , refl , h = suc j , refl , s≤s h

numeral-strict : ∀ {i j} → i < j → natT i <ᵀ natT j
numeral-strict {i = zero} {j = suc _} _ = []<
numeral-strict {i = suc _} {j = suc _} (s≤s p) = tl< (numeral-strict p)

bottom : ∀ a → [] ≤ᵀ a
bottom [] = inj₂ refl
bottom (_ ∷ _) = inj₁ []<

index< : ∀ {w a ts i} → (ψ w a ∷ ts) <ᵀ Ωt i → w <ᵀ i
index< (hd< (lv< p)) = p
index< (hd< (ar< ()))
index< (tl< ())

inside : ∀ {t} n → NF t → t <ᵀ Ωt (natT (suc n)) → GB [] t (Ωt (natT (suc n))) → Indices n t
inside n n[] _ _ = empty
inside n (n∷ {x = ψ w a} (nψ nw na _) sort nts) p guard with below-numeral (suc n) (index< p)
... | j , refl , s≤s j≤n = cons j≤n
  (inside n na (guard (gp (gh active))) (λ g → guard (gp (gc active g))))
  (inside n nts (<ᵀ-trans (tail< _ _ sort nts) p) (λ g → guard (gtl g)))
  where active = bottom (natT j)

recover : ∀ {t} n → NF t → Ctbl t → t <ᵀ row n → Indices n t
recover n n[] _ _ = empty
recover n (n∷ (nψ _ na guard) sort nts) (c∷ cs) (hd< (ar< p)) =
  cons z≤n (inside n na p (λ g → <ᵀ-trans (guard g) p))
    (recover n nts cs (<ᵀ-trans (tail< _ _ sort nts) (hd< (ar< p))))
recover n (n∷ _ _ _) (c∷ _) (hd< (lv< ()))
recover n (n∷ _ _ _) (c∷ _) (tl< ())

small : ∀ {n t} → Indices n t → t <ᵀ Ωt (natT (suc n))
small empty = []<
small (cons p _ _) = hd< (lv< (numeral-strict (s≤s p)))

in-row : ∀ {n t} → Indices n t → Ctbl t → t <ᵀ row n
in-row empty c[] = []<
in-row (cons {j = zero} _ a _) (c∷ _) = hd< (ar< (small a))
in-row (cons {j = suc _} _ _ _) ()

tower : ℕ → ℕ → T
tower n zero = []
tower n (suc k) = ψ (natT n) (tower n k) ∷ []

collapsed : ℕ → ℕ → T
collapsed n k = ψ [] (tower n k) ∷ []

above : ∀ {n t} → Indices n t → Σ ℕ λ k → t <ᵀ tower n k
above empty = 1 , []<
above {n} (cons {j} p a _) with <-cmp j n
... | tri< j<n _ _ = 1 , hd< (lv< (numeral-strict j<n))
... | tri> _ _ n<j = ⊥-elim (<⇒≱ n<j p)
... | tri≈ _ refl _ with above a
...   | k , lt = suc k , hd< (ar< lt)

above-countable : ∀ {n t} → Indices n t → Ctbl t → Σ ℕ λ k → t <ᵀ collapsed n k
above-countable empty c[] = 0 , []<
above-countable (cons {j = zero} _ a _) (c∷ _) with above a
... | k , lt = k , hd< (ar< lt)
above-countable (cons {j = suc _} _ _ _) ()

cofinal : ∀ {t} n → NF t → Ctbl t → t <ᵀ row n → Σ ℕ λ k → t <ᵀ collapsed n k
cofinal n nt ct p = above-countable (recover n nt ct p) ct
```

下标为自然数的项在本地还有一层语法。检查其支撑时，读到的额外参数恒等于零。

```agda
open import Data.Nat.Properties using (≤-refl)
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import Survey.EboPTORank using (initial)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≈ᵛ_; _≼_; ≼l; l≼; ≼-trans; ≼-refl; ≼-suc)

nf-num : ∀ n → NF (natT n)
nf-num zero = n[]
nf-num (suc zero) = nf-Ω n[]
nf-num (suc (suc n)) = n∷ (nψ n[] n[] GB[]) (inj₂ refl) (nf-num (suc n))

num-support : ∀ {z} n → InG [] z (natT n) → z ≡ []
num-support (suc n) (gp (gh _)) = refl
num-support (suc n) (gp (gw _ ()))
num-support (suc n) (gp (gc _ ()))
num-support (suc n) (gtl g) = num-support n g

rise : ∀ n k → tower n k <ᵀ tower n (suc k)
rise n zero = []<
rise n (suc k) = hd< (ar< (rise n k))

tower-guard : ∀ n k → GB [] (tower n k) (tower n k)
tower-guard n (suc k) (gp (gh _)) = rise n k
tower-guard n (suc k) (gp (gw _ g)) rewrite num-support n g = []<
tower-guard n (suc k) (gp (gc _ g)) = <ᵀ-trans (tower-guard n k g) (rise n k)
tower-guard n (suc k) (gtl ())

nf-inner : ∀ n k → NF (tower n k)
nf-inner n zero = n[]
nf-inner n (suc k) = nf-ψ (nf-num n) (nf-inner n k)
  (λ g → tower-guard n k (G-mono (bottom (natT n)) g))

nf-collapsed : ∀ n k → NF (collapsed n k)
nf-collapsed n k = nf-ψ n[] (nf-inner n k) (tower-guard n k)

nf-row : ∀ n → NF (row n)
nf-row n = nf-collapsed (suc n) 1

tower-indices : ∀ n k → Indices n (tower n k)
tower-indices n zero = empty
tower-indices n (suc k) = cons ≤-refl (tower-indices n k) empty

opaque
  row-h : ∀ n → HC (row n)
  row-h n = hc (nf-row n) (c∷ c[])

  tower-h : ∀ n k → HC (collapsed n k)
  tower-h n k = hc (nf-collapsed n k) (c∷ c[])

row-sup : ∀ n → Rt (row-h n) ≈ᵛ L.lim (λ k → Rt (tower-h n k))
row-sup n = initial (nf-row n) (c∷ c[]) (row-h n) (L.lim (λ i → Rt (tower-h n i))) lower , l≼ upper
  where
  lower : ∀ {s} → NF s → Ctbl s → (hs : HC s) → s <ᵀ row n → L.suc (Rt hs) ≼ L.lim (λ k → Rt (tower-h n k))
  lower ns cs hs p with cofinal n ns cs p
  ... | k , lt = ≼l {f = λ k → Rt (tower-h n k)} k
    (mono<ⁿ ns (nf-collapsed n k) (c∷ c[]) hs (tower-h n k) lt)
  upper : ∀ k → Rt (tower-h n k) ≼ Rt (row-h n)
  upper k = ≼-trans {b = L.suc (Rt (tower-h n k))} (≼-suc (≼-refl (Rt (tower-h n k))))
    (mono<ⁿ (nf-collapsed n k) (nf-row n) (c∷ c[]) (tower-h n k) (row-h n)
      (hd< (ar< (small (tower-indices n k)))))
```

## 与有限迭代归纳定义的比较

**经典纸面证明。** 固定 $1\le n<\omega$。令 $c_{n,k}=D_0D_n^k0$，按 Buchholz 的规定将单个主项和单元素列视为同一个项。把符号 $D_j$ 译为本地以自然数项 $\bar j$ 为下标的 $\psi$。零、有限降序和、主项的字典序均双向保持。固定下标系统的 $G_u$ 在 $D_jb$ 处只检查 $b$。本地还检查下标 $\bar j$，其中能读到的额外参数只有零，如上面的 `num-support`。待检参数非空时零严格小于它，参数为空时两边的支撑均为空。故两边的标准形守卫等价。[本地自然数下标翻译](../OCF/Align/Translate.lagda.md) · [Buchholz，§2 的项、序与标准形](https://epub.ub.uni-muenchen.de/3841/1/3841.pdf)

在 Buchholz 的**完整**系统中，$t<c_{n,k}$ 的标准项同样只用下标 $\le n$。非零 $t$ 的每个顶层主项是 $D_0b$，且 $b<D_n^k0<D_{n+1}0$。守卫 $G_0(b)<b$ 检查 $b$ 中所有嵌套的参数。$b$ 本身和所有这些参数均小于 $D_{n+1}0$，其降序和中的每个首标都至多为 $n$。这也排除了文献的 $D_\omega$ 出现在深层的可能。本地方向由 `recover` 给出全部下标、`below-numeral` 给出唯一的自然数读法（自然数项的长度即该数）。故在 $c_{n,k}$ 下，两套标准形初段的翻译是序同构。这里没有比较两种基本列的同号分支。[Buchholz，引理 2.2、定理 2.3(b)](https://epub.ub.uni-muenchen.de/3841/1/3841.pdf)

对每个本地可数标准项 $t$，$\rho(\mathrm{Rt}(t))$ 等于它在可数标准形良序中的初段序型。沿证书对后继及极限分支的严格递减性归纳得上界，沿整个标准形初段对 `attains` 归纳得下界。由上述序同构，$\rho(\mathrm{Rt}(c_{n,k}))=o(c_{n,k})$。Buchholz 在定理 3.7 的证明中给出 $\sup_k o(c_{n,k})=|ID_n|$。结合 `row-sup`，得到全部正有限 $n$ 上的精确值 $\rho(\mathrm{Rt}(\mathrm{row}(n)))=|ID_n|$。这里 $ID_n$ 是 $n$ 次迭代的正归纳定义理论。[参照赋秩](EboPTORank.lagda.md) · [Buchholz，定理 3.7 及其证明中的式 (4)](https://epub.ub.uni-muenchen.de/3841/1/3841.pdf)
