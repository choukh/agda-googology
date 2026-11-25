# 出路 (b) 的可做部分: 后继行的链点带精确读回; `CofΩ` 归到实现前提

> 验收文件 (读记号)。编译定理, 无前提: 标准形的和上精确读回对树的加法封闭 (`ex-add`, 首项不被吸收的情形), 所以 `next⁺` 的输出带精确读回 (`ex-next`); 实例 `next⁺ (Ωt zero)` 读作 ω (`ex-ω′`)。
> 条件定理: 若每个低于 Ω₁ 的标准形都被某棵带精确读回的树盖住 (`Real`, 没有居民), 则共尾度 Ω₁ 的 ν 都满足 `YiELOmega.CofΩ` (`cofΩ-real`, 用 `YiELLim.cofinΩ`)。
> 没有做: 部分和 `limc⁺` (后项吸收前项时标签不是字面的和), 一般链点; 不否定它们。入口: [YiELOmega](YiELOmega.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiELChain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open O using (_+_; iter)
open import OCF.Lean.YiCLPhi using (ωᵀ)
import OCF.Lean.YiHCRel as H
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<; tl<; 𝟏)
open import OCF.Align.EboLeanBase
  using (_≤ᵀ_; NF; NFP; n∷; nf-hd; HdLe; hd-pred; hd-lt; ≤-<; <-≤; <ᵀ-asym; <ᵀ-irrefl)
open import OCF.Align.EboLeanView using (vΩ; fΩ; fΩ-eq; fΩ-mono)
open import OCF.Align.EboLeanTrian using (t<)
open import OCF.Align.EboLeanClosure using (trian-fsn)
open import OCF.Lean.YiGLFrame using (Lbl)
open import OCF.Lean.YiGLOmega using (nf-ω; nf-1)
open import OCF.Lean.YiELLim using (cofinΩ)
open import OCF.Lean.YiELZero
open import OCF.Lean.YiELOmega using (CofΩ)
```

## 加法与 `next⁺`

`ex-add`: b 读作单项 p, y 读作 s, p 不低于 s 的首项 (p ∷ s 仍是标准形的和), 则 b + y 读作 p ∷ s。对 y 递归, 三条与 `H.Gen.m-add` 对应。

```agda
ex-add : ∀ {p} (b y : Tr zero) {s} → NFP p → Ex⁰ (p ∷ []) b → Ex⁰ s y → HdLe p s → Ex⁰ (p ∷ s) (b + y)
ex-add b zero np eb refl h = eb
ex-add b (suc y) {s = []} np eb (() , q) h
ex-add b (suc y) {s = x ∷ xs} np eb (e , q) h = e , ex-add b y np eb q (hd-pred x xs h)
ex-add b (lim f a) {s = []} np eb (() , _) h
ex-add {p} b (lim f a) {s = x ∷ xs} np eb (e , nf , la , k) h = lbl-lim {ν = p ∷ x ∷ xs} e (n∷ np h nf) (λ n →
  p ∷ proj₁ (k n)
  , ex-add b (f n) np eb (proj₁ (proj₂ (k n))) (hd-lt h (proj₂ (proj₂ (proj₂ (k n)))))
  , H.∷≤ p (proj₁ (proj₂ (proj₂ (k n)))) , tl< (proj₂ (proj₂ (proj₂ (k n)))))
ex-add b (Ω () _)
ex-add b (up _ () _ _)

ex-rep : ∀ {p} (b : Tr zero) → NFP p → Ex⁰ (p ∷ []) b → ∀ n → Ex⁰ (replicate (suc n) p) (iter (b +_) b n)
ex-rep b np eb zero = eb
ex-rep b np eb (suc n) = ex-add b (iter (b +_) b n) np eb (ex-rep b np eb n) (inj₂ refl)

rep-lt : ∀ {p : E.PT} n → replicate n p <ᵀ replicate (suc n) p
rep-lt zero = []<
rep-lt (suc n) = tl< (rep-lt n)

ex-next : ∀ {t p} (b : O.Tr⁺ zero) → NFP p → NF t → (e : E.cof t ≡ E.cω)
  → (∀ n → E.fsn t n ≡ replicate n p) → Ex⁰ (p ∷ []) (proj₁ b) → Ex⁰ t (proj₁ (O.next⁺ b))
ex-next {t} {p} (b , nb) np nf e q eb = lbl-lim {ν = t} e nf (λ n →
  replicate (suc n) p , ex-rep b np eb n
  , subst (_≤ᵀ replicate (suc n) p) (sym (q n)) (inj₁ (rep-lt n))
  , subst (_<ᵀ t) (q (suc n)) (t< (trian-fsn nf e (suc n))))

ex-ω′ : Ex⁰ ωᵀ (proj₁ (O.next⁺ (O.Ωt zero)))
ex-ω′ = ex-next (O.Ωt zero) (nf-hd nf-1) nf-ω refl (λ n → refl) (refl , refl)
```

## `CofΩ` 与实现前提

`Real` 只是陈述。有了它, `CofΩ` 不必作字段逐个填。

```agda
Real : Set
Real = ∀ {η} → NF η → η <ᵀ Ω₁ → Σ (Tr zero) λ d → Σ E.T λ η′ → Ex⁰ η′ d × (η ≤ᵀ η′)

cofΩ-real : Real → ∀ {ν} (h : Tr zero → L) → E.cof ν ≡ E.cΩ [] → CofΩ h ν
cofΩ-real R {ν} h e {u′} nf′ _ lt big with cofinΩ (vΩ ν e) nf′ lt
... | η , nη , η< , q with R nη η<
...   | d , η′ , x , inj₁ p = <ᵀ-asym q (<ᵀ-trans′ (fΩ-mono (vΩ ν e) p)
          (subst (_<ᵀ u′) (fΩ-eq (vΩ ν e) η′) (big d η′ x)))
  where
  <ᵀ-trans′ : ∀ {a b c} → a <ᵀ b → b <ᵀ c → a <ᵀ c
  <ᵀ-trans′ a b = ≤-< (inj₁ a) b
...   | d , η′ , x , inj₂ refl = <ᵀ-asym q (subst (_<ᵀ u′) (fΩ-eq (vΩ ν e) η′) (big d η′ x))
```
