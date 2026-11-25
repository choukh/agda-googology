# 精确标签在 ℕ 极限层号上可满足: ω 孩子

> 验收文件 (读记号)。编译定理: 层号 `two ⊕ ↑ zero ω` 有精确标签 ω (`lbl-ω`, 孩子的标签是 n+2, 基本列的项是 n), `YiBVSmall.child ω` 有精确标签 ω+1 (`lbl-source`), 它折到顶槽位层的框架有居民 (`frameˣ-source`)。
> 做了什么: 实填 `YiGLFrame.Lbl` 的 ℕ 极限一条的全部字段, 含 ω 的正规性与极限性质 `LimAt ωᵀ`。对象就是 `YiOPCountable.no-omega-seed` 的层号 `W.Lω` 与 `source`。
> 不否定 `no-omega-seed` (那里的关系要求基本列逐项对着孩子的精确标签); 不给出折叠值的保持。入口: [YiGLFrame](YiGLFrame.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGLOmega where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiCLFam using (nat)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiANFam using (cof-nat; pred-nat)
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiSQOmega as W
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<; hd<; tl<; lv<; ar<; 𝟏)
open import OCF.Align.EboLeanBase
  using (_≤ᵀ_; NF; n[]; n∷; NFP; nψ; HdLe; GB; GB[]; gp; gtl; gh; gw; gc; nf-tl; nf-le; <ᵀ-irrefl)
open import OCF.Lean.YiGTNode using (NodeFrame)
open import OCF.Lean.YiGLFrame
```

## ω 的正规性与极限性质

低于 ω 的正规项是自然数: 首项只能是 𝟏, 正规性使其余各项也是 𝟏。

```agda
nf-1 : NF (𝟏 ∷ [])
nf-1 = n∷ (nψ n[] n[] GB[]) tt n[]

gb-ω : GB [] (𝟏 ∷ []) (𝟏 ∷ [])
gb-ω (gp (gh _)) = []<
gb-ω (gp (gw _ ()))
gb-ω (gp (gc _ ()))
gb-ω (gtl ())

nf-ω : NF ωᵀ
nf-ω = n∷ (nψ n[] nf-1 gb-ω) tt n[]

lt1 : ∀ {a} → a <ᵀ (𝟏 ∷ []) → a ≡ []
lt1 []< = refl
lt1 (hd< (lv< ()))
lt1 (hd< (ar< ()))
lt1 (tl< ())

head-ω : ∀ {x xs} → (x ∷ xs) <ᵀ ωᵀ → x ≡ 𝟏
head-ω (hd< (lv< ()))
head-ω (hd< (ar< p)) = cong (E.ψ []) (lt1 p)
head-ω (tl< ())

le1 : ∀ {y} → HdLe 𝟏 (y ∷ []) → y ≡ 𝟏
le1 (inj₁ (lv< ()))
le1 (inj₁ (ar< ()))
le1 (inj₂ e) = e

ones : ∀ {u} → NF u → HdLe 𝟏 u → Σ ℕ λ k → u ≡ E.natT k
ones n[] _ = 0 , refl
ones (n∷ {x} {xs} p hl nf) le with le1 {y = x} le
... | refl with ones nf hl
...   | k , refl = suc k , refl

fs-ω : ∀ n → E.fsn ωᵀ n ≡ E.natT n
fs-ω = rep1

lim-ω : LimAt ωᵀ
lim-ω {u′ = []} nf lt big = no (subst (_<ᵀ []) (fs-ω 1) (big 1))
  where
  no : E.natT 1 <ᵀ [] → ⊥
  no ()
lim-ω {u′ = x ∷ xs} nf lt big with head-ω lt
... | refl with ones (nf-tl nf) (nf-le nf)
...   | k , refl = <ᵀ-irrefl (subst (_<ᵀ E.natT (suc k)) (fs-ω (suc k)) (big (suc k)))
```

## ω 孩子的标签与框架

`Gω n` 的标签是 n+2, ω 的基本列第 n 项是 n: 用到 ℕ 极限一条里的 "不高于"。

```agda
Gω : ℕ → L
Gω n = K.two ⊕ ↑ zero (nat n)

Lω : L
Lω = nd sL Gω

Lω-eq : K.two ⊕ ↑ zero W.ω ≡ Lω
Lω-eq = refl

lbl-G : ∀ n → Lbl (Gω n) (E.natT (suc (suc n)))
lbl-G zero = lbl-fin 2
lbl-G (suc n) = cof-nat (suc (suc n)) , subst (Lbl (Gω n)) (sym (pred-nat (suc (suc n)))) (lbl-G n)

nat< : ∀ n → E.natT n <ᵀ E.natT (suc (suc n))
nat< zero = []<
nat< (suc n) = tl< (nat< n)

lbl-ω : Lbl Lω ωᵀ
lbl-ω = refl , nf-ω , lim-ω , λ n → E.natT (suc (suc n)) , lbl-G n
  , subst (_≤ᵀ E.natT (suc (suc n))) (sym (fs-ω n)) (inj₁ (nat< n)) , hd< (ar< []<)

source-eq : S.child W.ω ≡ nd sS (λ _ → Lω)
source-eq = refl

lbl-source : Lbl (S.child W.ω) (E.sucT ωᵀ)
lbl-source = refl , lbl-ω

frameˣ-source : (o : Ok (S.child W.ω)) → NodeFrameˣ (S.child W.ω) o Lω (inc tt self) ωᵀ
frameˣ-source o = frameˣ-S (λ _ → Lω) o lbl-ω

no-frame-source : (o : Ok (S.child W.ω)) (ν : E.T)
  → NodeFrame (S.child W.ω) o Lω (inc tt self) ν → ⊥
no-frame-source o ν = no-frame-child W.ω o ν
```
