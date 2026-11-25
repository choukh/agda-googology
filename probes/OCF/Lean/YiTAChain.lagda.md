# 去掉 `HdLe` 的加法读回与部分和链点

> 验收文件 (读记号)。编译定理, 无前提: 第 0 层的精确读回对树的加法封闭, 标签是记号一侧带吸收的和 (`ex-add′ : Ex⁰ α b → Ex⁰ β y → Ex⁰ (α ⊞ β) (b + y)`), `YiELChain.ex-add` 是它的推论 (`ex-add-noabs`); 部分和 `cum` 读作 `Σ⊞` (`ex-cum`), `limc⁺` 在基本列夹在部分和之下时读作目标 (`ex-limc`); 目标是主项时条件与 `lim` 结点逐字相同 (`lbl-limc`)。
> 实例: ω + ω² 读作 ω², ω² + ω 读作 ω²+ω; `limc⁺` (1, ω, ω, …) 读作 ω², 其第一步吸收, 不满足 `ex-add` 的 `HdLe` (`no-hdle`)。
> 不涉及折叠的链点 (`out (chain n)` 的标签); 入口: [YiTAAdd](YiTAAdd.lagda.md), 用法见 [YiTAReal](YiTAReal.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTAChain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open O using (_+_)
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<; hd<; tl<; lv<; ar<; 𝟏; ψ)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF; HdLe; nf-hd; ≤-<; ≤-trans′)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Lean.YiGLFrame using (Lbl)
open import OCF.Lean.YiELZero using (Ex⁰; lbl-lim; lbl-nf)
open import OCF.Lean.YiELChain using (ex-next; ex-ω′)
open import OCF.Lean.YiTAAdd
```

## 加法

对 y 递归。后继一条用 `⊞-pred`, 极限一条: 孩子的标签取 α ⊞ μₙ, 基本列一侧用 `fsn-⊞≤` 与 `⊞-≤ʳ`, 严格一侧用 `⊞-<ʳ`。

```agda
ex-add′ : ∀ (b y : Tr zero) {α β} → Ex⁰ α b → Ex⁰ β y → Ex⁰ (α ⊞ β) (b + y)
ex-add′ b zero eb refl = eb
ex-add′ b (suc y) {α} {β = []} eb (() , _)
ex-add′ b (suc y) {α} {z ∷ zs} eb (e , q) =
  trans (⊞-cof α z zs) e , subst (Lbl (↑ zero (b + y))) (sym (⊞-pred α (z ∷ zs) e)) (ex-add′ b y eb q)
ex-add′ b (lim f a) {α} {β = []} eb (() , _)
ex-add′ b (lim f a) {α} {z ∷ zs} eb (e , nf , la , k) =
  lbl-lim (trans (⊞-cof α z zs) e) (⊞-NF {α} {z ∷ zs} na nf) λ n →
    α ⊞ proj₁ (k n)
    , ex-add′ b (f n) eb (proj₁ (proj₂ (k n)))
    , ≤-trans′ (fsn-⊞≤ α n na (cl-fsn-NF nf e n) (inj₁ (≤-< (fl n) (μl n)))) (⊞-≤ʳ α (fl n))
    , ⊞-<ʳ α (μl n)
  where
  na = lbl-nf (↑ zero b) eb
  fl = λ n → proj₁ (proj₂ (proj₂ (k n)))
  μl = λ n → proj₂ (proj₂ (proj₂ (k n)))
ex-add′ b (Ω () _)
ex-add′ b (up _ () _ _)

ex-add-noabs : ∀ {p} (b y : Tr zero) {s} → Ex⁰ (p ∷ []) b → Ex⁰ s y → HdLe p s → Ex⁰ (p ∷ s) (b + y)
ex-add-noabs b y eb ey h = subst (λ ν → Ex⁰ ν (b + y)) (⊞-noabs h) (ex-add′ b y eb ey)
```

## 部分和与 `limc⁺`

```agda
ex-cum : ∀ (G : ℕ → Tr zero) {γ} → (∀ n → Ex⁰ (γ n) (G n)) → ∀ n → Ex⁰ (Σ⊞ γ n) (O.cum G n)
ex-cum G g zero = g zero
ex-cum G g (suc n) = ex-add′ (O.cum G n) (G (suc n)) (ex-cum G g n) (g (suc n))

ex-limc : ∀ {t} (G : ℕ → O.Tr⁺ zero) {γ} → (∀ n → Ex⁰ (γ n) (proj₁ (G n)))
  → NF t → E.cof t ≡ E.cω → (∀ n → E.fsn t n ≤ᵀ Σ⊞ γ n) → (∀ n → Σ⊞ γ n <ᵀ t)
  → Ex⁰ t (proj₁ (O.limc⁺ G))
ex-limc G {γ} g nf e lo hi = lbl-lim e nf λ n →
  Σ⊞ γ n , ex-cum (λ m → proj₁ (G m)) g n , lo n , hi n
```

目标是主项时, `limc⁺` 要的条件与 `lim` 结点 (`lbl-lim`) 逐字相同: 部分和由 `Σ⊞-ge`、`Σ⊞-<prin` 处理。

```agda
lbl-limc : ∀ {x} (G : ℕ → O.Tr⁺ zero) → NF (x ∷ []) → E.cof (x ∷ []) ≡ E.cω
  → (∀ n → Σ E.T λ μ → Ex⁰ μ (proj₁ (G n)) × (E.fsn (x ∷ []) n ≤ᵀ μ) × (μ <ᵀ x ∷ []))
  → Ex⁰ (x ∷ []) (proj₁ (O.limc⁺ G))
lbl-limc G nf e k = ex-limc G {γ = γ} (λ n → proj₁ (proj₂ (k n))) nf e
  (λ n → ≤-trans′ (proj₁ (proj₂ (proj₂ (k n)))) (Σ⊞-ge {γ = γ} nfγ n))
  (Σ⊞-<prin {γ = γ} (λ n → proj₂ (proj₂ (proj₂ (k n)))))
  where
  γ = λ n → proj₁ (k n)
  nfγ = λ n → lbl-nf (↑ zero (proj₁ (G n))) (proj₁ (proj₂ (k n)))
```

## 实例

```agda
ωtr ω²tr : O.Tr⁺ zero
ωtr  = O.next⁺ (O.Ωt zero)
ω²tr = O.next⁺ ωtr

ex-ω² : Ex⁰ ω²′ (proj₁ ω²tr)
ex-ω² = ex-next ωtr (nf-hd nf-ω′) nf-ω²′ refl (λ n → refl) ex-ω′

ex-ω+ω² : Ex⁰ ω²′ (proj₁ ωtr + proj₁ ω²tr)
ex-ω+ω² = ex-add′ (proj₁ ωtr) (proj₁ ω²tr) ex-ω′ ex-ω²

ex-ω²+ω : Ex⁰ (ψ [] (𝟏 ∷ 𝟏 ∷ []) ∷ ωh ∷ []) (proj₁ ω²tr + proj₁ ωtr)
ex-ω²+ω = ex-add′ (proj₁ ω²tr) (proj₁ ωtr) ex-ω² ex-ω′
```

`limc⁺` (1, ω, ω, …): 部分和 1, ω, ω·2, …, 第一步 1 ⊞ ω = ω 吸收。

```agda
G₁ : ℕ → O.Tr⁺ zero
G₁ zero    = O.Ωt zero
G₁ (suc n) = ωtr

γ₁ : ℕ → E.T
γ₁ zero    = 𝟏 ∷ []
γ₁ (suc n) = ω′

ex-G₁ : ∀ n → Ex⁰ (γ₁ n) (proj₁ (G₁ n))
ex-G₁ zero    = refl , refl
ex-G₁ (suc n) = ex-ω′

private
  tr-rep : ∀ k → tr ωh (replicate k ωh) ≡ replicate k ωh
  tr-rep zero = refl
  tr-rep (suc k) = cong (ωh ∷_) (tr-rep k)

  rep-snoc : ∀ k → replicate k ωh ++ (ωh ∷ []) ≡ replicate (suc k) ωh
  rep-snoc zero = refl
  rep-snoc (suc k) = cong (ωh ∷_) (rep-snoc k)

Σγ₁ : ∀ n → Σ⊞ γ₁ (suc n) ≡ replicate (suc n) ωh
Σγ₁ zero = refl
Σγ₁ (suc n) = trans (cong (_⊞ ω′) (Σγ₁ n))
  (trans (cong (_++ (ωh ∷ [])) (tr-rep (suc n))) (rep-snoc (suc n)))

private
  rep< : ∀ k → replicate (suc k) ωh <ᵀ ω²′
  rep< k = hd< (ar< (tl< []<))

ex-limc-ω² : Ex⁰ ω²′ (proj₁ (O.limc⁺ G₁))
ex-limc-ω² = ex-limc G₁ ex-G₁ nf-ω²′ refl lo hi
  where
  lo : ∀ n → E.fsn ω²′ n ≤ᵀ Σ⊞ γ₁ n
  lo zero = inj₁ []<
  lo (suc n) = inj₂ (sym (Σγ₁ n))
  hi : ∀ n → Σ⊞ γ₁ n <ᵀ ω²′
  hi zero = hd< (ar< []<)
  hi (suc n) = subst (_<ᵀ ω²′) (sym (Σγ₁ n)) (rep< n)

no-hdle : HdLe 𝟏 ω′ → ⊥
no-hdle (inj₁ (lv< ()))
no-hdle (inj₁ (ar< ()))
no-hdle (inj₂ ())
```
