# 第 0 层的精确读回: 出口, 孩子层号的标签, 任意树没有标签

> 验收文件 (读记号)。编译定理, 无前提: 第 0 层的精确读回 `Ex⁰ η d = Lbl (↑ zero d) η` 推出下界关系 (`ex→M⁰`) 与值的出口 (`ex-lower`); 带精确读回的 d 上, 最小实例的孩子层号 `YiBVSmall.child d` 有精确标签且低于 Ω₁ (`child-lbl`)。
> 编译否定: 有一棵第 0 层的树 `slow` (0, ω, ω+1, … 的极限) 带下界证据而没有任何精确标签 (`no-lbl-slow`); 它否定 "对一切带 `M⁰` 证据的 d 给标签", 不否定出路 (a) (分支前提换成精确读回)。
> `Lbl` 的 ℕ 极限一条里 `LimAt` 不再是要填的字段 (`lbl-lim`, 用 `YiELLim.limAt`)。入口: [YiELLim](YiELLim.lagda.md); 关系族与 Ω 形状见 [YiELOmega](YiELOmega.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiELZero where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiCLFam using (nat)
open import OCF.Lean.YiANFam using (cof-nat; pred-nat)
open import OCF.Lean.YiRefTw2 using (Rt)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBVSmall as S
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<; hd<; tl<; lv<; ar<; 𝟏)
open import OCF.Align.EboLeanBase
  using (_≤ᵀ_; NF; n[]; n∷; nf-hd; nf-tl; nf-le; nf-Ω; HdLe; sub≤; ≤[]; <sucT; tri; ≤-<; <-≤; ≤-trans′; <ᵀ-trans; <ᵀ-irrefl; Ctbl; c[]; c∷)
open import OCF.Align.EboLean3Base using (sucT≤; nf-suc)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Align.EBO using (<-sucT) renaming (pred-suc to suc-pred)
open import OCF.Align.JiaAuditClosure using (cof-suc; pred-suc)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiGLFrame
open import OCF.Lean.YiGLOmega using (nf-ω; lim-ω)
open import OCF.Lean.YiELLim using (limAt; suc<Ωs)
```

## 精确读回与它的基本性质

`↑ zero d` 只有后继与 ℕ 极限形状, 所以 `Lbl` 在它上面就是 "d 逐结点对着 η"。标签是标准形, 低于 Ω₁, 可数。

```agda
Ex⁰ : E.T → Tr zero → Set
Ex⁰ η d = Lbl (↑ zero d) η

lbl-lim : ∀ {g ν} → E.cof ν ≡ E.cω → NF ν
  → (∀ n → Σ E.T λ μ → Lbl (g n) μ × (E.fsn ν n ≤ᵀ μ) × (μ <ᵀ ν)) → Lbl (nd sL g) ν
lbl-lim {ν = ν} e nf k = e , nf , limAt ν e , k

lbl-nf : ∀ a {ν} → Lbl a ν → NF ν
lbl-nf zero refl = n[]
lbl-nf (nd sS h) {ν} (e , q) = subst NF (suc-pred ν e) (nf-suc (lbl-nf (h tt) q))
lbl-nf (nd sL g) (e , nf , _) = nf
lbl-nf (nd (sΩ k) h) ()

Ω₁ : E.T
Ω₁ = E.Ωs []

nf-Ω₁ : NF Ω₁
nf-Ω₁ = nf-Ω (nf-suc n[])

private
  no-ω : E.cof Ω₁ ≡ E.cω → ⊥
  no-ω ()

lbl<Ω : ∀ a {ν} → Lbl a ν → ν <ᵀ Ω₁
lbl<Ω zero refl = []<
lbl<Ω (nd sS h) {ν} (e , q) = subst (_<ᵀ Ω₁) (suc-pred ν e) (suc<Ωs (lbl<Ω (h tt) q))
lbl<Ω (nd sL g) {ν} (e , nf , la , k) with tri ν Ω₁
... | inj₁ p = p
... | inj₂ (inj₁ refl) = ⊥-elim (no-ω e)
... | inj₂ (inj₂ p) = ⊥-elim (la nf-Ω₁ p (λ n →
  ≤-< (proj₁ (proj₂ (proj₂ (k n)))) (lbl<Ω (g n) (proj₁ (proj₂ (k n))))))
lbl<Ω (nd (sΩ k) h) ()

ctbl′ : ∀ {a} t → NF t → HdLe (E.ψ [] a) t → Ctbl t
ctbl′ [] _ _ = c[]
ctbl′ (E.ψ v b ∷ xs) nf h with ≤[] (sub≤ h)
... | refl = c∷ (ctbl′ xs (nf-tl nf) (nf-le nf))

ctbl< : ∀ {t} → NF t → t <ᵀ Ω₁ → Ctbl t
ctbl< nf []< = c[]
ctbl< {t = E.ψ v a ∷ xs} nf (hd< (lv< p)) with <sucT [] p
... | inj₂ refl = c∷ (ctbl′ xs (nf-tl nf) (nf-le nf))
```

## 出口

精确读回是下界关系的特例, 第 0 层关系 `H.M⁰` (即 `Rˣ zero`, `GR.R zero`) 不变。`H.exitᴴ` 在向下封闭一步上要的标准形与可数证据由标签给出。

```agda
ex→M⁰ : ∀ d {η} → Ex⁰ η d → H.M⁰ η d
ex→M⁰ zero refl = H.mz
ex→M⁰ (suc d) (e , q) = H.m1 e (ex→M⁰ d q)
ex→M⁰ (lim f a) (e , nf , la , k) = H.mL e (λ n →
  H.mc (proj₁ (proj₂ (proj₂ (k n)))) (H.mw (ex→M⁰ (f n) (proj₁ (proj₂ (k n)))) (◃l n)))
ex→M⁰ (Ω () _)
ex→M⁰ (up _ () _ _)

ex-Ex : ∀ d {η} (q : Ex⁰ η d) → H.Exᴴ (ex→M⁰ d q)
ex-Ex zero refl = tt
ex-Ex (suc d) (e , q) = ex-Ex d q
ex-Ex (lim f a) (e , nf , la , k) n = cl-fsn-NF nf e n , lbl-nf (↑ zero (f n)) (proj₁ (proj₂ (k n)))
  , ctbl< (lbl-nf (↑ zero (f n)) (proj₁ (proj₂ (k n)))) (lbl<Ω (↑ zero (f n)) (proj₁ (proj₂ (k n))))
  , ex-Ex (f n) (proj₁ (proj₂ (k n)))
ex-Ex (Ω () _)
ex-Ex (up _ () _ _)

ex-lower : ∀ d {η} → Ex⁰ η d → (h : E.HC η) → Rt h ≼ K.readRW d
ex-lower d q h = H.exitᴴ (ex→M⁰ d q) (ex-Ex d q) h
```

## 孩子层号的标签

`two ⊕ ↑ zero d` 的标签: d 有限时加 2, 否则与 d 的标签相同; 极限一条靠 "不高于" 吸收。只陈述成夹在 η 与 η+2 之间。

```agda
suc-mono : ∀ {a b} → a ≤ᵀ b → E.sucT a ≤ᵀ E.sucT b
suc-mono {b = b} (inj₁ p) = inj₁ (≤-< (sucT≤ p) (<-sucT b))
suc-mono (inj₂ refl) = inj₂ refl

private
  c1≢cω : E.c1 ≡ E.cω → ⊥
  c1≢cω ()

suc<lim : ∀ {y ν} → E.cof ν ≡ E.cω → y <ᵀ ν → E.sucT y <ᵀ ν
suc<lim {y} e p with sucT≤ p
... | inj₁ q = q
... | inj₂ refl = ⊥-elim (c1≢cω (subst (_≡ E.cω) (cof-suc y) e))

two⊕ : ∀ d {η} → Ex⁰ η d
  → Σ E.T λ μ → Lbl (K.two ⊕ ↑ zero d) μ × (η ≤ᵀ μ) × (μ ≤ᵀ E.sucT (E.sucT η))
two⊕ zero refl = E.natT 2 , (refl , refl , refl) , inj₁ []< , inj₂ refl
two⊕ (suc d) {η} (e , q) with two⊕ d q
... | μ , l , lo , hi = E.sucT μ , (cof-suc μ , subst (Lbl (K.two ⊕ ↑ zero d)) (sym (pred-suc μ)) l)
  , subst (_≤ᵀ E.sucT μ) (suc-pred η e) (suc-mono lo)
  , subst (λ z → E.sucT μ ≤ᵀ E.sucT (E.sucT z)) (suc-pred η e) (suc-mono hi)
two⊕ (lim f a) {η} (e , nf , la , k) = η , (e , nf , la , λ n →
  let μ = proj₁ (k n) ; r = two⊕ (f n) (proj₁ (proj₂ (k n))) in
  proj₁ r , proj₁ (proj₂ r)
  , ≤-trans′ (proj₁ (proj₂ (proj₂ (k n)))) (proj₁ (proj₂ (proj₂ r)))
  , ≤-< (proj₂ (proj₂ (proj₂ r))) (suc<lim e (suc<lim e (proj₂ (proj₂ (proj₂ (k n)))))))
  , inj₂ refl , inj₁ (<ᵀ-trans (<-sucT η) (<-sucT (E.sucT η)))
two⊕ (Ω () _)
two⊕ (up _ () _ _)

ex-suc : ∀ d {η} → Ex⁰ η d → Ex⁰ (E.sucT η) (suc d)
ex-suc d {η} q = cof-suc η , subst (Lbl (↑ zero d)) (sym (pred-suc η)) q

child-lbl : ∀ d {η} → Ex⁰ η d → Σ E.T λ μ → Lbl (S.child d) μ × (η ≤ᵀ μ) × (μ <ᵀ Ω₁)
child-lbl d {η} q with two⊕ (suc d) (ex-suc d q)
... | μ , l , lo , hi = μ , l , inj₁ (<-≤ (<-sucT η) lo) , lbl<Ω (S.child d) l
```

## 任意的 d 没有标签

`slow` 是 0, ω, ω+1, ω+2, … 的极限。它的标签只能是 ω·2 (`limAt` 排除更低的, 标签自带的 `LimAt` 排除更高的), 而 ω·2 的基本列第 0 项 ω 高于第 0 个孩子的标签 0。

```agda
ωt : Tr zero
ωt = lim nat (λ n → ◃s)

sn : ℕ → Tr zero
sn zero = ωt
sn (suc n) = suc (sn n)

sg′ : ℕ → Tr zero
sg′ zero = zero
sg′ (suc n) = sn n

adj : ∀ n → zero ⊢ sg′ n ◃ sg′ (suc n)
adj zero = ◃l 0
adj (suc n) = ◃s

slow : Tr zero
slow = lim sg′ adj

slow-low : H.M⁰ [] slow
slow-low = H.mz

ωh : E.PT
ωh = E.ψ [] (𝟏 ∷ [])

ω+ : ℕ → E.T
ω+ n = ωh ∷ E.natT n

ω2 : E.T
ω2 = ωh ∷ ωh ∷ []

nf-ω2 : NF ω2
nf-ω2 = n∷ (nf-hd nf-ω) (inj₂ refl) nf-ω

nat<ω : ∀ n → E.natT n <ᵀ ωᵀ
nat<ω zero = []<
nat<ω (suc n) = hd< (ar< []<)

ex-nat : ∀ n → Ex⁰ (E.natT n) (nat n)
ex-nat zero = refl
ex-nat (suc n) = cof-nat n , subst (Lbl (↑ zero (nat n))) (sym (pred-nat n)) (ex-nat n)

ex-ω : Ex⁰ ωᵀ ωt
ex-ω = lbl-lim refl nf-ω (λ n → E.natT n , ex-nat n , inj₂ (rep1 n) , nat<ω n)

ex-sn : ∀ n → Ex⁰ (ω+ n) (sn n)
ex-sn zero = ex-ω
ex-sn (suc n) = cof-nat n , subst (Lbl (↑ zero (sn n))) (sym (cong (ωh ∷_) (pred-nat n))) (ex-sn n)

private
  no-cons : ∀ {x : E.PT} {xs} → (x ∷ xs) ≡ [] → ⊥
  no-cons ()

module _ {ν : E.T} (k : ∀ n → Σ E.T λ μ → Lbl (↑ zero (sg′ n)) μ × (E.fsn ν n ≤ᵀ μ) × (μ <ᵀ ν)) where
  kid-eq : ∀ n → proj₁ (k (suc n)) ≡ ω+ n
  kid-eq n = uniq (↑ zero (sn n)) (proj₁ (proj₂ (k (suc n)))) (ex-sn n)

  kid< : ∀ n → ω+ n <ᵀ ν
  kid< n = subst (_<ᵀ ν) (kid-eq n) (proj₂ (proj₂ (proj₂ (k (suc n)))))

  kid0 : E.fsn ν 0 ≡ []
  kid0 = ≤[] (subst (E.fsn ν 0 ≤ᵀ_) (proj₁ (proj₂ (k 0))) (proj₁ (proj₂ (proj₂ (k 0)))))

  fs< : ∀ n → E.fsn ν n <ᵀ ω2
  fs< zero = subst (_<ᵀ ω2) (sym kid0) []<
  fs< (suc n) = ≤-< (subst (E.fsn ν (suc n) ≤ᵀ_) (kid-eq n) (proj₁ (proj₂ (proj₂ (k (suc n))))))
    (tl< (nat<ω n))

no-lbl-slow : ∀ ν → Ex⁰ ν slow → ⊥
no-lbl-slow ν (e , nf , la , k) with tri ν ω2
... | inj₁ p = limAt ω2 refl nf p (λ n → subst (_<ᵀ ν) (sym (cong (ωh ∷_) (rep1 n))) (kid< k n))
... | inj₂ (inj₁ refl) = no-cons (kid0 k)
... | inj₂ (inj₂ p) = la nf-ω2 p (fs< k)

no-all : (∀ d η → H.M⁰ η d → Σ E.T λ μ → Ex⁰ μ d) → ⊥
no-all f = no-lbl-slow _ (proj₂ (f slow [] slow-low))
```
