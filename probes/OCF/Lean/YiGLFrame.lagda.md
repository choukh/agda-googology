# LowKeep 一侧: 槽位标签的定义域决定框架有无居民

> 验收文件 (读记号)。编译否定: 槽位标签取下界读法 `GR.Nu` 时, 任何后继形状层号对它的顶槽位层都没有 `YiGTNode.NodeFrame` (`no-frame-S`), 链点孩子 `YiBVSmall.child d` 没有 `IndexTree` (`no-tree-child`)。
> 编译定理 (配对的构造): 槽位标签取精确标签 `Lbl` 时同一处的框架有居民 (`frameˣ-S`); `Lbl` 是读法 (`lbl-rd`), 唯一 (`uniq`), 槽位的标签严格低于层号的标签 (`below`)。
> 只否定 "对一切下界读法的槽位标签都要框架" 这一证据域, 不否定 LowKeep、`SlotPres` 的陈述或路线; `Lbl` 在 ℕ 极限层号上的可满足性没有实填 (`LimAt` 是证据里的字段)。域与 Leaf 见 [YiGLDom](YiGLDom.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGLFrame where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Keep; kp)
open import OCF.Lean.YiTBRow using (Rb; rb-no)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiANFam using (Pen; cof-nat; pred-nat)
open import OCF.Lean.YiGTNode using (NodeFrame)
open import OCF.Lean.YiGTDirect using (IndexTree)
open import OCF.Lean.YiGTIndexNeg using (pen-gt)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBVSmall as S
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF; tri; ≤-<; <ᵀ-irrefl; <ᵀ-asym; <→lt; lt→<; eq→≡; cmpᵀ-refl)
open import OCF.Align.EboLean3Base using (sucT≤)
open import OCF.Align.EBO using (pred-suc; <-sucT)
```

## 否定: 下界读法作槽位标签

空读法 `[]` 是每个槽位的 `GR.Nu` 标签。后继形状层号 `nd sS h` 折到孩子 `h tt` 时, 顶槽位 (槽位层就是 `h tt`) 走链, 孩子里的槽位保留; 框架要前者 `cmpᵀ 1 ν ≡ gt`, 后者 `Pen (cmpᵀ 1 ν)`, 对任何 ν 都矛盾。
这是 `YiGTIndexNeg.no-frame₂` (层号 `fn 2`) 的一般形式: 孩子 `h tt` 是变量, 只要它有一个槽位。

```agda
mutual
  nu0 : ∀ ℓ p → GR.Nu ℓ p []
  nu0 (nd s h) (inj₂ (c , t)) = nu0⁼ (h c) t
  nu0 (nd (sΩ k) h) (inj₁ t) = nu0⁼ k t

  nu0⁼ : ∀ a t → GR.Nu⁼ a t []
  nu0⁼ a (inj₁ _) = GR.c0 refl
  nu0⁼ a (inj₂ p) = nu0 a p

no-frame-S : (h : ⊤ → L) (o : Ok (nd sS h)) (q : Pos (h tt)) (ν : E.T)
  → NodeFrame (nd sS h) o (h tt) (inc tt self) ν → ⊥
no-frame-S h o q ν fr = pen-gt
  (proj₁ (fr (inj₂ (tt , inj₂ q)) [] (nu0 (h tt) q)))
  (fr (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl))

pos-two : ∀ d → Pos (K.two ⊕ ↑ zero d)
pos-two zero = inj₂ (tt , inj₁ tt)
pos-two (suc d) = inj₂ (tt , inj₁ tt)
pos-two (lim f a) = inj₂ (0 , inj₁ tt)

no-frame-child : ∀ d (o : Ok (S.child d)) ν
  → NodeFrame (S.child d) o (K.two ⊕ ↑ zero d) (inc tt self) ν → ⊥
no-frame-child d o ν = no-frame-S (λ _ → K.two ⊕ ↑ zero d) o (pos-two d) ν

no-tree-child : ∀ d → IndexTree (S.child d) → ⊥
no-tree-child d it = no-frame-child d (proj₂ S.okay d) []
  (proj₁ (proj₁ it (proj₂ S.okay d) (rb-no (S.child d)) (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl)))
```

## 精确标签

`Lbl a ν`: ν 是没有 Ω 形状的层号 a 的精确标签。后继形状逐字对应; ℕ 极限形状只要求基本列逐项不高于孩子的标签, 孩子的标签严格低于 ν (容得下 "Ω 树是部分和": 孩子可以比基本列的项大), 另带 ν 的正规性与极限性质 `LimAt` 作证据。
`LimAt` 只对正规项陈述: 对非正规项它在 ω 上就不成立 (判断, 未编译: `𝟏 ∷ x ∷ []` 低于 ω 而高于一切自然数)。

```agda
LimAt : E.T → Set
LimAt u = ∀ {u′} → NF u′ → u′ <ᵀ u → (∀ n → E.fsn u n <ᵀ u′) → ⊥

Lbl : L → E.T → Set
Lbl zero ν = ν ≡ []
Lbl (nd sS h) ν = (E.cof ν ≡ E.c1) × Lbl (h tt) (E.pred ν)
Lbl (nd sL g) ν = (E.cof ν ≡ E.cω) × NF ν × LimAt ν
  × (∀ n → Σ E.T λ μ → Lbl (g n) μ × (E.fsn ν n ≤ᵀ μ) × (μ <ᵀ ν))
Lbl (nd (sΩ k) h) ν = ⊥

lbl-rd : ∀ a {ν} → Lbl a ν → GR.Rd a ν
lbl-rd zero refl = GR.c0 refl
lbl-rd (nd sS h) (e , q) = GR.ca (inj₂ (e , lbl-rd (h tt) q))
lbl-rd (nd sL g) (e , _ , _ , f) = GR.cL e (λ n →
  GR.cc (proj₁ (proj₂ (proj₂ (f n)))) (GR.rd-child sL g n (lbl-rd (g n) (proj₁ (proj₂ (f n))))))
lbl-rd (nd (sΩ k) h) ()

uniq : ∀ a {ν ν′} → Lbl a ν → Lbl a ν′ → ν ≡ ν′
uniq zero refl refl = refl
uniq (nd sS h) {ν} {ν′} (e , q) (e′ , q′) =
  trans (sym (pred-suc ν e)) (trans (cong E.sucT (uniq (h tt) q q′)) (pred-suc ν′ e′))
uniq (nd sL g) {ν} {ν′} (e , nf , la , f) (e′ , nf′ , la′ , f′) with tri ν ν′
... | inj₁ lt = ⊥-elim (la′ nf lt (λ n → ≤-< (proj₁ (proj₂ (proj₂ (f′ n))))
  (subst (_<ᵀ ν) (uniq (g n) (proj₁ (proj₂ (f n))) (proj₁ (proj₂ (f′ n)))) (proj₂ (proj₂ (proj₂ (f n)))))))
... | inj₂ (inj₁ eq) = eq
... | inj₂ (inj₂ gt) = ⊥-elim (la nf′ gt (λ n → ≤-< (proj₁ (proj₂ (proj₂ (f n))))
  (subst (_<ᵀ ν′) (uniq (g n) (proj₁ (proj₂ (f′ n))) (proj₁ (proj₂ (f n)))) (proj₂ (proj₂ (proj₂ (f′ n)))))))
uniq (nd (sΩ k) h) ()

pred< : ∀ ν → E.cof ν ≡ E.c1 → E.pred ν <ᵀ ν
pred< ν e = subst (E.pred ν <ᵀ_) (pred-suc ν e) (<-sucT (E.pred ν))

mutual
  below : ∀ a (q : Pos a) {κ ν} → Lbl (at a q) κ → Lbl a ν → κ <ᵀ ν
  below (nd sS h) (inj₁ ())
  below (nd sS h) (inj₂ (tt , t)) {ν = ν} lκ (e , q) = ≤-< (below⁼ (h tt) t lκ q) (pred< ν e)
  below (nd sL g) (inj₁ ())
  below (nd sL g) (inj₂ (n , t)) lκ (e , _ , _ , f) =
    ≤-< (below⁼ (g n) t lκ (proj₁ (proj₂ (f n)))) (proj₂ (proj₂ (proj₂ (f n))))
  below (nd (sΩ k) h) q lκ ()

  below⁼ : ∀ a (t : Pos⁼ a) {κ ν} → Lbl (proj₁ (sl⁼ a t)) κ → Lbl a ν → κ ≤ᵀ ν
  below⁼ a (inj₁ _) lκ lν = inj₂ (uniq a lκ lν)
  below⁼ a (inj₂ p) lκ lν = inj₁ (below a p lκ lν)

lbl-fin : ∀ n → Lbl (fn n) (E.natT n)
lbl-fin zero = refl
lbl-fin (suc n) = cof-nat n , subst (Lbl (fn n)) (sym (pred-nat n)) (lbl-fin n)
```

## 配对的构造: 精确标签下同一处的框架

框架改成只对精确标签量化 (`NodeFrameˣ`; 保留一支只记比较与槽位标签, 不带 `Low` 的搬运)。后继形状层号折到孩子, 目标下标取孩子的精确标签: 顶槽位的标签等于目标下标, 走链; 孩子里的槽位标签严格更低, 保留。

```agda
<→gt : ∀ {a b} → b <ᵀ a → E.cmpᵀ a b ≡ E.gt
<→gt {a} {b} p with E.cmpᵀ a b in e
... | E.gt = refl
... | E.lt = ⊥-elim (<ᵀ-asym p (lt→< a b e))
... | E.eq = ⊥-elim (<ᵀ-irrefl (subst (b <ᵀ_) (eq→≡ a b e) p))

≤→pen : ∀ {a b} → a ≤ᵀ b → Pen (E.cmpᵀ a b)
≤→pen (inj₁ p) = inj₁ (<→lt p)
≤→pen {a} (inj₂ refl) = inj₂ (cmpᵀ-refl a)

KeepSpecˣ : ∀ ℓ j (ν : E.T) (p : Pos ℓ) (κ : E.T) → Keep j (Br ℓ p) (fromBr ℓ p zero) → Set
KeepSpecˣ ℓ j ν p κ nothing = E.cmpᵀ (E.sucT κ) ν ≡ E.gt
KeepSpecˣ ℓ j ν p κ (just (q , cv , eq)) = Pen (E.cmpᵀ (E.sucT κ) ν) × Lbl (at j q) κ

NodeFrameˣ : ∀ ℓ → Ok ℓ → ∀ j → j ≤ ℓ → E.T → Set
NodeFrameˣ ℓ o j w ν = (p : Pos ℓ) (κ : E.T) → Lbl (at ℓ p) κ → KeepSpecˣ ℓ j ν p κ (kp ℓ o p w)

frameˣ-S : (h : ⊤ → L) (o : Ok (nd sS h)) {ν : E.T} → Lbl (h tt) ν
  → NodeFrameˣ (nd sS h) o (h tt) (inc tt self) ν
frameˣ-S h o lν (inj₁ ())
frameˣ-S h o {ν} lν (inj₂ (tt , inj₁ tt)) κ lκ =
  subst (λ z → E.cmpᵀ (E.sucT z) ν ≡ E.gt) (sym (uniq (h tt) lκ lν)) (<→gt (<-sucT ν))
frameˣ-S h o lν (inj₂ (tt , inj₂ q)) κ lκ = ≤→pen (sucT≤ (below (h tt) q lκ lν)) , lκ

frameˣ-fin : ∀ n (o : Ok (fn (suc n))) → NodeFrameˣ (fn (suc n)) o (fn n) (inc tt self) (E.natT n)
frameˣ-fin n o = frameˣ-S (λ _ → fn n) o (lbl-fin n)
```
