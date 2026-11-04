# 跨段 (七): 数据树上的跨段节点

> 入口 [CrossM](CrossM.lagda.md). **判决: PARTIAL. 定义编译过, 无条件; 没有 `Goodᴺ`, 也没有读回序数.** `T` 是高度在顶层 $\top$ (读作 $\Omega_{\psi_1(\Omega)+\alpha}$) 的数据树. 它有一个地板 $M$: 树里出现的低高度都在 $M$ 之下. 节点 `tH` 绑定高度: 对一切 `e : M ⊂ M′` 给一支, 这一支的地板升到 $M'$.
>
> - **公共上界.** `ΨT` 的目标高度 $H$ 在 $M$ 之下, 过 `tH` 时把 $H$ 上移成 `up e H`, 在 $M'$ 里继续比较: 两个下标都在 $M'$ 之下, $M'$ 字面地写在类型里; 比完由 `↓ᴾ` 拿回 $M$. 全程没有跨 $M$ 的比较.
> - **Kripke 分支.** 顶层节点 `tΩ` 的分支对一切 `M ⊂ M′` 给出, 否则上移算子过不了 `tΩ`: 输入在 $M'$ 上, 而 `T` 没有向下的算子 (里面可能有 `tH`). 低层节点 `tΩ↓` 不用, 有 `↓ᴾ`.
> - **新高度的默认地板是 `Fl`.** 否则 `ψᵀ` 过 `tH` 时 `Z*` 的转换写不出来.
> - **`Tᵀ M α : Run Fl`** 是闭项: $\psi_0(\Omega_{\psi_1(\Omega)+\alpha})$ (判断), 第 0 行 `Ω̇ᵀ M 0` 是 `tH`.
>
> **没有的.** `tH` 经 `ψ̄ᵀ` 落成已有的 `ŝ`, 它的链点只记得上一个 $\eta$, 分支的世界 `M ᶜ+ ⌈η⌉` 与下一个没有 `⊂` 关系. 所以这棵树连 $\alpha=0$ 也没有 `Goodᴺ`; 见 [CrossM](CrossM.lagda.md) 的第一个障碍. 种类检验不看界, 这个文件只说明定义的形状走得通, 不说明值对 (`noCert₂` 的教训).
>
> 记号无关: 不读记号; 形状读自 [LadderOrdTree](LadderOrdTree.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
open import OCF.Free.Floor using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun; bound; Bd; Fc; FB; evF; iF; liftEv; Top)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderOrdBase
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (_ᶜ+_; ⌈_⌉)
open import OCF.Align.CrossMUp
import OCF.Align.CrossMLift as L
import OCF.Align.LadderOrdTree

module 𝕎 {M : Code} = OCF.Align.LadderOrdTree (HB M)

Hᴹ : Code → Set
Hᴹ M = Pos (cs M)

Fvᴹ : Code → Set
Fvᴹ M = Hᴹ M → Flr

Qᴹ : ∀ M → Hᴹ M → Ordᴵ → Flr → Fvᴹ M → Set
Qᴹ M = 𝕎.Q {M}

infixl 5 _∪ᵀ_
_∪ᵀ_ : ∀ {M} → Fvᴹ M → Fvᴹ M → Fvᴹ M
(a ∪ᵀ b) n = a n ⊔ b n

Sub∞ : ∀ {M} → Fvᴹ M → Fvᴹ M → Set
Sub∞ a b = ∀ i {ℓ} → Ev ℓ (a i) → Ev ℓ (b i)
```

## §1 延拓

```agda
ok₁ : Ev (suc zero) Fl
ok₁ = tt , (λ q → q)

≤end : ∀ {M} (n : Hᴹ M) → (n ≡ end) ⊎ (n <ᴾ end)
≤end end = inj₁ refl
≤end (low p) = inj₂ tt

module Ext {M M′ : Code} (e : M ⊂ M′) where
  u : Hᴹ M → Hᴹ M′
  u = up e

  extT : {X : Set} → X → (Hᴹ M → X) → ∀ i′ → Tri _<ᴾ_ i′ (u end) → X
  extT d f i′ (tlt r) = f (proj₁ (up-down e {y = i′} {q = end} r))
  extT d f i′ (teq _) = f end
  extT d f i′ (tgt _) = d

  ext : {X : Set} → X → (Hᴹ M → X) → Hᴹ M′ → X
  ext d f i′ = extT d f i′ (<ᴾ-tri i′ (u end))

  ext-β : ∀ {X : Set} (d : X) (f : Hᴹ M → X) i → ext d f (u i) ≡ f i
  ext-β d f i with <ᴾ-tri (u i) (u end)
  ... | tlt r = cong f (sym (up-inj e (proj₁ (proj₂ (up-down e {y = u i} {q = end} r)))))
  ... | teq x = cong f (sym (up-inj e x))
  ... | tgt r = ⊥-elim (up-refl e {p = end} {q = i} r)

  ext-new : ∀ {X : Set} (d : X) (f : Hᴹ M → X) {i′} → u end <ᴾ i′ → ext d f i′ ≡ d
  ext-new d f {i′} r with <ᴾ-tri i′ (u end)
  ... | tlt r′ = ⊥-elim (irrᴾ {p = u end} (<ᴾ-trans (u end) i′ (u end) r r′))
  ... | teq x = ⊥-elim (no-self (sym x) r)
  ... | tgt _ = refl

  data Dc (i′ : Hᴹ M′) : Set where
    inn : ∀ i → i′ ≡ u i → Dc i′
    new : u end <ᴾ i′ → Dc i′

  dc : ∀ i′ → Dc i′
  dc i′ with <ᴾ-tri i′ (u end)
  ... | tlt r = inn (proj₁ (up-down e {y = i′} {q = end} r)) (proj₁ (proj₂ (up-down e {y = i′} {q = end} r)))
  ... | teq x = inn end x
  ... | tgt r = new r

  E : Fvᴹ M → Fvᴹ M′
  E = ext Fl

  lt-new : ∀ n {i′} → u end <ᴾ i′ → u n <ᴾ i′
  lt-new n r with ≤end n
  ... | inj₁ refl = r
  ... | inj₂ l = <ᴾ-trans (u n) (u end) _ (up-mono e {n} {end} l) r

  vi : ∀ {ℓ a b} → a ≡ b → Ev ℓ a → Ev ℓ b
  vi refl x = x

  vi⁻ : ∀ {ℓ a b} → a ≡ b → Ev ℓ b → Ev ℓ a
  vi⁻ refl x = x

  E-β : ∀ (χ : Fvᴹ M) i {ℓ} → Ev ℓ (E χ (u i)) → Ev ℓ (χ i)
  E-β χ i = vi (ext-β Fl χ i)

  E-β⁻ : ∀ (χ : Fvᴹ M) i {ℓ} → Ev ℓ (χ i) → Ev ℓ (E χ (u i))
  E-β⁻ χ i = vi⁻ (ext-β Fl χ i)

  E-n : ∀ (χ : Fvᴹ M) {i′} → u end <ᴾ i′ → ∀ {ℓ} → Ev ℓ (E χ i′) → Ev ℓ Fl
  E-n χ r = vi (ext-new Fl χ r)

  E-n⁻ : ∀ (χ : Fvᴹ M) {i′} → u end <ᴾ i′ → ∀ {ℓ} → Ev ℓ Fl → Ev ℓ (E χ i′)
  E-n⁻ χ r = vi⁻ (ext-new Fl χ r)

  -- 转换
  cE-wk : ∀ {a b : Fvᴹ M} → Sub∞ a b → Sub∞ (E a) (E b)
  cE-wk {a} {b} s i′ y with dc i′
  ... | inn i refl = E-β⁻ b i (s i (E-β a i y))
  ... | new r = E-n⁻ b r (E-n a r y)

  cE-∪ : ∀ (a b : Fvᴹ M) → Sub∞ (E (a ∪ᵀ b)) (E a ∪ᵀ E b)
  cE-∪ a b i′ y with dc i′
  ... | inn i refl = let z = E-β (a ∪ᵀ b) i y in E-β⁻ a i (proj₁ z) , E-β⁻ b i (proj₂ z)
  ... | new r = let z = E-n (a ∪ᵀ b) r y in E-n⁻ a r z , E-n⁻ b r z

  cE-Z : ∀ (χ : Fvᴹ M) → Sub∞ (E (𝕎.Z* χ)) (𝕎.Z* (E χ))
  cE-Z χ i′ y with dc i′
  ... | inn i refl = let z = E-β (𝕎.Z* χ) i y in proj₁ z , E-β⁻ χ i (proj₂ z)
  ... | new r = let z = E-n (𝕎.Z* χ) r y in z , E-n⁻ χ r z

  cE-upd : ∀ (χ : Fvᴹ M) n x → Sub∞ (𝕎.upd (E χ) (u n) x) (E (𝕎.upd χ n x))
  cE-upd χ n x i′ {ℓ} y with dc i′
  ... | inn i refl = E-β⁻ (𝕎.upd χ n x) i (vi (trans (L.upd-res e (E χ) n x i) (𝕎.upd-at n i (ext-β Fl χ i))) y)
  ... | new r = E-n⁻ (𝕎.upd χ n x) r (E-n χ r (vi (𝕎.upd-gt (E χ) x (lt-new n r)) y))

  cE-lo : ∀ (ζ′ : Fvᴹ M′) n (χ : Fvᴹ M) → Sub∞ (𝕎.lo (u n) ζ′ ∪ᵀ E χ) (E (𝕎.lo n (L.res e ζ′) ∪ᵀ χ))
  cE-lo ζ′ n χ i′ y with dc i′
  ... | inn i refl = E-β⁻ (𝕎.lo n (L.res e ζ′) ∪ᵀ χ) i (vi (L.lo-res e ζ′ n i) (proj₁ y) , E-β χ i (proj₂ y))
  ... | new r = E-n⁻ (𝕎.lo n (L.res e ζ′) ∪ᵀ χ) r (E-n χ r (proj₂ y))

open Ext using () renaming (E to Eᵉ)

cE-r : ∀ {M} (χ : Fvᴹ M) → Sub∞ χ (Eᵉ ⊂r χ)
cE-r χ i y = Ext.E-β⁻ ⊂r χ i y

cE-trans : ∀ {A B D} (a : A ⊂ B) (b : B ⊂ D) (χ : Fvᴹ A) → Sub∞ (Eᵉ b (Eᵉ a χ)) (Eᵉ (⊂-trans a b) χ)
cE-trans a b χ i″ y with Ext.dc b i″
... | Ext.new r = via′ (Ext.dc (⊂-trans a b) i″)
  where
  z = Ext.E-n b (Eᵉ a χ) r y
  via′ : Ext.Dc (⊂-trans a b) i″ → _
  via′ (Ext.new r′) = Ext.E-n⁻ (⊂-trans a b) χ r′ z
  via′ (Ext.inn i x) = ⊥-elim (no-up (subst (up b (up a end) <ᴾ_) x′ (r″)))
    where
    x′ : i″ ≡ up b (up a i)
    x′ = trans x (up-trans a b i)
    r″ : up b (up a end) <ᴾ i″
    r″ = with≤ (≤end (up a end))
      where
      with≤ : (up a end ≡ end) ⊎ (up a end <ᴾ end) → up b (up a end) <ᴾ i″
      with≤ (inj₁ d) = subst (λ w → up b w <ᴾ i″) (sym d) r
      with≤ (inj₂ l) = <ᴾ-trans (up b (up a end)) (up b end) i″ (up-mono b {up a end} {end} l) r
    no-up : up b (up a end) <ᴾ up b (up a i) → ⊥
    no-up q = up-refl a {p = end} {q = i} (up-refl b {p = up a end} {q = up a i} q)
... | Ext.inn i′ refl with Ext.dc a i′
...   | Ext.inn i refl = subst (λ w → Ev _ (Eᵉ (⊂-trans a b) χ w)) (up-trans a b i)
        (Ext.E-β⁻ (⊂-trans a b) χ i (Ext.E-β a χ i (Ext.E-β b (Eᵉ a χ) (up a i) y)))
...   | Ext.new r = via′ (Ext.dc (⊂-trans a b) (up b i′))
  where
  z = Ext.E-n a χ r (Ext.E-β b (Eᵉ a χ) i′ y)
  via′ : Ext.Dc (⊂-trans a b) (up b i′) → _
  via′ (Ext.new r′) = Ext.E-n⁻ (⊂-trans a b) χ r′ z
  via′ (Ext.inn i x) = ⊥-elim (L.no-self′ a (up-inj b (trans x (up-trans a b i))) r)
```

## §2 数据树

与 `Q₊` 同形, 差别: 高度全部低于顶层 (所以 `tcl`, `tΩ↓` 不带 $n<m$ 的证明, `twk` 的转换对一切高度), `tΩ` 是 Kripke 分支, 多一个 `tH`.

```agda
module _ (α : Ordᴵ) (U : ∀ M (i : Ordᴵ) → i ◃ α → Flr → Fvᴹ M → Set) where
  data T₊ : ∀ M → Flr → Fvᴹ M → Set where
    t0   : ∀ {M φ χ} → T₊ M φ χ
    ts   : ∀ {M φ χ} → T₊ M φ χ → T₊ M φ χ
    tl   : ∀ {M φ χ} → (ℕ → T₊ M φ χ) → T₊ M φ χ
    ti   : ∀ {M φ χ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → T₊ M φ χ) → T₊ M φ χ
    tŝ   : ∀ {M φ χ} (c₀ : Ordᴵ) → T₊ M φ χ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → T₊ M φ χ) → T₊ M φ χ
    tĉ   : ∀ {M φ χ} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → T₊ M φ χ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → T₊ M φ χ) → T₊ M φ χ
    tclo : ∀ {M φ χ} → T₊ M (φ ⊔ fk zero) χ → ((η : Ordᴵ) → T₊ M (φ ⊔ fk η) χ) → T₊ M (φ ⊔ fk zero) χ
    tcl  : ∀ {M φ χ} (n : Hᴹ M) (ψ : Flr) → (∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (ψ ⊔ fk zero)) → T₊ M φ χ → ((η : Ordᴵ) → T₊ M φ (𝕎.upd χ n (ψ ⊔ fk η))) → T₊ M φ χ
    twk  : ∀ {M φ φ′ χ χ′} → (∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ) → Sub∞ {M} χ′ χ → T₊ M φ χ → T₊ M φ′ χ′
    tΩ↓  : ∀ {M φ χ k} (n : Hᴹ M) → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (∀ {ℓ} → Ev ℓ (χ n) → k <ᴵ ℓ) → (∀ ξ ζ → Qᴹ M n k ξ ζ → T₊ M (ξ ⊔ φ) (𝕎.lo n ζ ∪ᵀ χ)) → T₊ M φ χ
    tΩ   : ∀ {M φ χ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : k <ᴵ α) → (∀ {M′} (e : M ⊂ M′) ξ ζ → U M′ k (<→◃ q) ξ ζ → T₊ M′ (ξ ⊔ φ) (ζ ∪ᵀ Eᵉ e χ)) → T₊ M φ χ
    tH   : ∀ {M φ χ} → T₊ M φ χ → (∀ {M′} (e : M ⊂ M′) → T₊ M′ φ (Eᵉ e χ)) → T₊ M φ χ
    tk   : ∀ {M φ χ k} (r : k ◃₁ α) → U M k (◃₁→◃ r) φ χ → T₊ M φ χ → T₊ M φ χ

QT : Ordᴵ → ∀ M → Flr → Fvᴹ M → Set
UT : ∀ {α} M (i : Ordᴵ) → i ◃ α → Flr → Fvᴹ M → Set
QT α M φ χ = T₊ α UT M φ χ
UT M i zero         φ χ = QT i M φ χ
UT M i (suc r)      φ χ = UT M i r φ χ
UT M _ (self {f} n) φ χ = QT (f n) M φ χ
UT M i (lim n r)    φ χ = UT M i r φ χ

outT : ∀ {M i α} (r : i ◃ α) {φ χ} → UT M i r φ χ → QT i M φ χ
outT zero      x = x
outT (suc r)   x = outT r x
outT (self n)  x = x
outT (lim n r) x = outT r x

intoT : ∀ {M i α} (r : i ◃ α) {φ χ} → QT i M φ χ → UT M i r φ χ
intoT zero      x = x
intoT (suc r)   x = intoT r x
intoT (self n)  x = x
intoT (lim n r) x = intoT r x
```

## §3 层间搬运

```agda
ιT : ∀ {M a b} (r : a ◃ b) {φ χ} → QT a M φ χ → QT b M φ χ
ιT r t0 = t0
ιT r (ts a) = ts (ιT r a)
ιT r (tl F) = tl (λ n → ιT r (F n))
ιT r (ti ac f) = ti ac (λ x → ιT r (f x))
ιT r (tŝ c₀ t g) = tŝ c₀ (ιT r t) (λ η e → ιT r (g η e))
ιT r (tĉ c₀ z zg o₀ o) = tĉ c₀ z zg (ιT r o₀) (λ η e → ιT r (o η e))
ιT r (tclo t g) = tclo (ιT r t) (λ η → ιT r (g η))
ιT r (tcl n ψ s t g) = tcl n ψ s (ιT r t) (λ η → ιT r (g η))
ιT r (twk le le′ t) = twk le le′ (ιT r t)
ιT r (tΩ↓ n fe ac h) = tΩ↓ n fe ac (λ ξ ζ z → ιT r (h ξ ζ z))
ιT r (tΩ fe q h) = tΩ fe (<◃ q r) (λ e ξ ζ z → ιT r (h e ξ ζ (intoT (<→◃ q) (outT (<→◃ (<◃ q r)) z))))
ιT r (tH t g) = tH (ιT r t) (λ e → ιT r (g e))
ιT r (tk q z x) = ιT r x

record RestrT (j b : Ordᴵ) : Set where
  constructor restrT
  field
    {repT′} : Ordᴵ
    eqT    : j ≅ᴵ repT′
    ltT    : repT′ <ᴵ b
    backT  : ∀ {M ξ ζ} → QT repT′ M ξ ζ → QT j M ξ ζ
open RestrT

trT  : ∀ {M a b φ χ} → a ≅ᴵ b → QT a M φ χ → QT b M φ χ
tr⁻T : ∀ {M a b φ χ} → a ≅ᴵ b → QT b M φ χ → QT a M φ χ
resT : ∀ {j a b} → j <ᴵ a → a ≅ᴵ b → RestrT j b
res⁻T : ∀ {j a b} → j <ᴵ b → a ≅ᴵ b → RestrT j a

trT e t0 = t0
trT e (ts a) = ts (trT e a)
trT e (tl F) = tl (λ n → trT e (F n))
trT e (ti ac f) = ti ac (λ x → trT e (f x))
trT e (tŝ c₀ t g) = tŝ c₀ (trT e t) (λ η d → trT e (g η d))
trT e (tĉ c₀ z zg o₀ o) = tĉ c₀ z zg (trT e o₀) (λ η d → trT e (o η d))
trT e (tclo t g) = tclo (trT e t) (λ η → trT e (g η))
trT e (tcl n ψ s t g) = tcl n ψ s (trT e t) (λ η → trT e (g η))
trT e (twk le le′ t) = twk le le′ (trT e t)
trT e (tΩ↓ n fe ac h) = tΩ↓ n fe ac (λ ξ ζ z → trT e (h ξ ζ z))
trT e (tΩ fe q h) = tΩ fe (ltT (resT q e)) (λ e′ ξ ζ z → trT e (h e′ ξ ζ (intoT (<→◃ q) (backT (resT q e) (outT (<→◃ (ltT (resT q e))) z)))))
trT e (tH t g) = tH (trT e t) (λ e′ → trT e (g e′))
trT (s≅ e) (tk zero z x) = tk zero (trT e z) (trT (s≅ e) x)
trT (l≅ h) (tk (self n) z x) = tk (self n) (trT (h n) z) (trT (l≅ h) x)

tr⁻T e t0 = t0
tr⁻T e (ts a) = ts (tr⁻T e a)
tr⁻T e (tl F) = tl (λ n → tr⁻T e (F n))
tr⁻T e (ti ac f) = ti ac (λ x → tr⁻T e (f x))
tr⁻T e (tŝ c₀ t g) = tŝ c₀ (tr⁻T e t) (λ η d → tr⁻T e (g η d))
tr⁻T e (tĉ c₀ z zg o₀ o) = tĉ c₀ z zg (tr⁻T e o₀) (λ η d → tr⁻T e (o η d))
tr⁻T e (tclo t g) = tclo (tr⁻T e t) (λ η → tr⁻T e (g η))
tr⁻T e (tcl n ψ s t g) = tcl n ψ s (tr⁻T e t) (λ η → tr⁻T e (g η))
tr⁻T e (twk le le′ t) = twk le le′ (tr⁻T e t)
tr⁻T e (tΩ↓ n fe ac h) = tΩ↓ n fe ac (λ ξ ζ z → tr⁻T e (h ξ ζ z))
tr⁻T e (tΩ fe q h) = tΩ fe (ltT (res⁻T q e)) (λ e′ ξ ζ z → tr⁻T e (h e′ ξ ζ (intoT (<→◃ q) (backT (res⁻T q e) (outT (<→◃ (ltT (res⁻T q e))) z)))))
tr⁻T e (tH t g) = tH (tr⁻T e t) (λ e′ → tr⁻T e (g e′))
tr⁻T (s≅ e) (tk zero z x) = tk zero (tr⁻T e z) (tr⁻T (s≅ e) x)
tr⁻T (l≅ h) (tk (self n) z x) = tk (self n) (tr⁻T (h n) z) (tr⁻T (l≅ h) x)

resT zero      (s≅ e) = restrT e zero (tr⁻T e)
resT (suc q)   (s≅ e) = restrT (eqT (resT q e)) (suc (ltT (resT q e))) (backT (resT q e))
resT (lim n q) (l≅ h) = restrT (eqT (resT q (h n))) (lim n (ltT (resT q (h n)))) (backT (resT q (h n)))

res⁻T zero      (s≅ e) = restrT (≅ᴵ-sym e) zero (trT e)
res⁻T (suc q)   (s≅ e) = restrT (eqT (res⁻T q e)) (suc (ltT (res⁻T q e))) (backT (res⁻T q e))
res⁻T (lim n q) (l≅ h) = restrT (eqT (res⁻T q (h n))) (lim n (ltT (res⁻T q (h n)))) (backT (res⁻T q (h n)))
```

## §4 上移与加法

`tΩ`, `tH` 的分支本来就是 Kripke 的, 上移不用进分支, 只复合路径.

```agda
↑T : ∀ α {M M′} (e : M ⊂ M′) {φ χ} → QT α M φ χ → QT α M′ φ (Eᵉ e χ)
↑Uᵀ : ∀ α {k} (r : k ◃ α) {M M′} (e : M ⊂ M′) {φ χ} → QT k M φ χ → QT k M′ φ (Eᵉ e χ)
↑Uᵀ (suc k) zero e x = ↑T k e x
↑Uᵀ (suc c) (suc r) e x = ↑Uᵀ c r e x
↑Uᵀ (lim f s) (self n) e x = ↑T (f n) e x
↑Uᵀ (lim f s) (lim n r) e x = ↑Uᵀ (f n) r e x

↑T α e t0 = t0
↑T α e (ts a) = ts (↑T α e a)
↑T α e (tl F) = tl (λ n → ↑T α e (F n))
↑T α e (ti ac f) = ti ac (λ x → ↑T α e (f x))
↑T α e (tŝ c₀ t g) = tŝ c₀ (↑T α e t) (λ η d → ↑T α e (g η d))
↑T α e (tĉ c₀ z zg o₀ o) = tĉ c₀ z zg (↑T α e o₀) (λ η d → ↑T α e (o η d))
↑T α e (tclo t g) = tclo (↑T α e t) (λ η → ↑T α e (g η))
↑T α e {χ = χ} (tcl n ψ s t g) =
  tcl (up e n) ψ (λ y → s (Ext.E-β e χ n y)) (↑T α e t) (λ η → twk (λ y → y) (Ext.cE-upd e χ n _) (↑T α e (g η)))
↑T α e (twk le lc t) = twk le (Ext.cE-wk e lc) (↑T α e t)
↑T α e {χ = χ} (tΩ↓ {k = k} n fe ac h) =
  tΩ↓ (up e n) fe (λ y → ac (Ext.E-β e χ n y))
    (λ ξ ζ′ z′ → twk (λ y → y) (Ext.cE-lo e ζ′ n χ) (↑T α e (h ξ (L.res e ζ′) (L.↓ᴾ e n k z′))))
↑T α e {χ = χ} (tΩ fe q h) =
  tΩ fe q (λ e′ ξ ζ z → twk (λ y → y) (λ i y → proj₁ y , cE-trans e e′ χ i (proj₂ y)) (h (⊂-trans e e′) ξ ζ z))
↑T α e {χ = χ} (tH t g) = tH (↑T α e t) (λ e′ → twk (λ y → y) (cE-trans e e′ χ) (g (⊂-trans e e′)))
↑T α e (tk r z x) = tk r (intoT (◃₁→◃ r) (↑Uᵀ α (◃₁→◃ r) e (outT (◃₁→◃ r) z))) (↑T α e x)

infixl 6 _⊞_
_⊞_ : ∀ {c M φ χ ψ ρ} → QT c M φ χ → QT c M ψ ρ → QT c M (φ ⊔ ψ) (χ ∪ᵀ ρ)
W ⊞ t0 = twk proj₁ (λ i → proj₁) W
W ⊞ ts a = ts (W ⊞ a)
W ⊞ tl F = tl (λ n → W ⊞ F n)
W ⊞ ti ac f = ti (λ e → ac (proj₂ e)) (λ x → W ⊞ f x)
W ⊞ tŝ c₀ t g = tŝ c₀ (W ⊞ t) (λ η e → W ⊞ g η e)
W ⊞ tĉ c₀ z zg o₀ o = tĉ c₀ z zg (W ⊞ o₀) (λ η e → W ⊞ o η e)
W ⊞ tclo t g = twk asl (λ i e → e) (tclo (twk asr (λ i e → e) (W ⊞ t)) (λ η → twk asr (λ i e → e) (W ⊞ g η)))
_⊞_ {χ = χ} W (tcl n ψ s t g) =
  tcl n (χ n ⊔ ψ) (λ e → (proj₁ e , proj₁ (s (proj₂ e))) , proj₂ (s (proj₂ e))) (W ⊞ t) (λ η → twk (λ e → e) (𝕎.as-upd {_} {χ} n η) (W ⊞ g η))
W ⊞ twk le le′ t = twk (λ e → proj₁ e , le (proj₂ e)) (λ i e → proj₁ e , le′ i (proj₂ e)) (W ⊞ t)
W ⊞ tΩ↓ n fe ac h = tΩ↓ n (λ e → fe (proj₂ e)) (λ e → ac (proj₂ e)) (λ ξ ζ z → twk swp (λ i → swp) (W ⊞ h ξ ζ z))
_⊞_ {c = c} {χ = χ} {ρ = ρ} W (tΩ fe q h) =
  tΩ (λ e → fe (proj₂ e)) q (λ e ξ ζ z → twk swp (λ i y → let d = Ext.cE-∪ e χ ρ i (proj₂ y) in proj₁ d , (proj₁ y , proj₂ d)) (↑T c e W ⊞ h e ξ ζ z))
_⊞_ {c = c} {χ = χ} {ρ = ρ} W (tH t g) = tH (W ⊞ t) (λ e → twk (λ y → y) (Ext.cE-∪ e χ ρ) (↑T c e W ⊞ g e))
W ⊞ tk r z x = W ⊞ x

repT : ∀ {c M φ χ} → QT c M φ χ → ℕ → QT c M φ χ
repT x zero          = t0
repT x (suc zero)    = x
repT x (suc (suc m)) = twk (λ e → e , e) (λ i e → e , e) (repT x (suc m) ⊞ x)
```

## §5 从低高度嵌入, 第 0 行

```agda
capS : ∀ {M} (n : Hᴹ M) {a b : Fvᴹ M} {x} → 𝕎.Sub n a b → Sub∞ (𝕎.cap a n x) (𝕎.cap b n x)
capS n s i e with <ᴾ-tri i n
... | tlt r = s i r e
... | teq _ = e
... | tgt _ = tt

ι↓T : ∀ {M n k α φ χ} → Qᴹ M n k φ χ → QT α M φ (𝕎.cap χ n (flo k))
ι↓T 𝕎.q0 = t0
ι↓T (𝕎.qs a) = ts (ι↓T a)
ι↓T (𝕎.ql F) = tl (λ i → ι↓T (F i))
ι↓T (𝕎.qi ac f) = ti ac (λ x → ι↓T (f x))
ι↓T (𝕎.qŝ c₀ t g) = tŝ c₀ (ι↓T t) (λ η e → ι↓T (g η e))
ι↓T (𝕎.qĉ c₀ z zg o₀ o) = tĉ c₀ z zg (ι↓T o₀) (λ η e → ι↓T (o η e))
ι↓T (𝕎.qclo t g) = tclo (ι↓T t) (λ η → ι↓T (g η))
ι↓T {n = n} {χ = χ} (𝕎.qcl {n = j} q ψ s t g) =
  tcl j ψ (λ e → s (subst (Ev _) (𝕎.cap-lt χ _ q) e)) (ι↓T t) (λ η → twk (λ e → e) (𝕎.c-sw {_} {χ} n q) (ι↓T (g η)))
ι↓T {n = n} (𝕎.qwk le le′ t) = twk le (capS n le′) (ι↓T t)
ι↓T {n = n} {χ = χ} (𝕎.qΩ↓ {n = j} q fe ac h) =
  tΩ↓ j fe (λ e → ac (subst (Ev _) (𝕎.cap-lt χ _ q) e)) (λ ξ ζ z → twk (λ e → e) (𝕎.c-∪ {_} {𝕎.lo j ζ} {χ} n) (ι↓T (h ξ ζ (𝕎.intoV q z))))
ι↓T {n = n} {k = k} {χ = χ} (𝕎.qΩ fe r h) =
  tΩ↓ n fe (λ e → cvFlo k (subst (Ev _) (𝕎.cap-self χ n _) e) r) (λ ξ ζ z → twk (λ e → e) (𝕎.c-∪ {_} {𝕎.lo n ζ} {χ} n) (ι↓T (h ξ ζ (𝕎.intoU (<→◃ r) z))))
ι↓T {n = n} {k = suc a} (𝕎.omk zero z x) = twk (λ e → e) (𝕎.cap-map n (λ e → toFlo a (λ q → e (suc q)))) (ι↓T z)
ι↓T {n = n} {k = lim f s} (𝕎.omk (self i) z x) = twk (λ e → e) (𝕎.cap-map n (λ e → toFlo (f i) (λ q → e (lim i q)))) (ι↓T z)

κ′ : ∀ {M} → Flr → Fvᴹ M
κ′ x _ = x

E-κ : ∀ {M M′} (e : M ⊂ M′) i′ {ℓ} → Ev ℓ (Eᵉ e (κ′ Fl) i′) → Ev ℓ Fl
E-κ e i′ y with Ext.dc e i′
... | Ext.inn i refl = Ext.E-β e (κ′ Fl) i y
... | Ext.new r = Ext.E-n e (κ′ Fl) r y

𝟏ᵀ : ∀ {M α} → QT α M Fl (κ′ Fl)
𝟏ᵀ = twk (λ _ → tt) (λ i _ → tt) (ts {φ = fz} {χ = κ′ fz} t0)

stepT : ∀ {M M′} (e : M ⊂ M′) → QT zero M′ Fl (Eᵉ e (κ′ Fl))
stepT e = twk (λ y → y) (λ i′ y → 𝕎.κ-cap end (λ _ → tt) i′ (E-κ e i′ y)) (ι↓T {n = end} (𝕎.Ω̇ end zero))

Ω̇ᵀ : ∀ M α → QT α M Fl (κ′ Fl)
Ω̇ᵀ M zero = tH 𝟏ᵀ stepT
Ω̇ᵀ M (suc α) = tΩ (λ e → e) zero (λ e ξ ζ z → twk proj₁ (λ i y → proj₁ y) (tk zero z (ιT zero z)))
Ω̇ᵀ M (lim f s) = tl (λ n → tk (self n) (Ω̇ᵀ M (f n)) (ιT (self n) (Ω̇ᵀ M (f n))))
```

## §6 折叠: 目标在顶层

```agda
chainT : ∀ {M k φ χ} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → Sub∞ {M} χ (κ′ Fl) → (QT k M φ χ → QT k M φ χ) → ℕ → QT k M φ χ
chainT {M} {k} fe fc f zero    = twk fe fc (Ω̇ᵀ M k)
chainT fe fc f (suc n) = f (chainT fe fc f n)

fcT : ∀ {M} {χ : Fvᴹ M} → Sub∞ (𝕎.Z* χ) (κ′ Fl)
fcT i = proj₁

cvT : ∀ {M} (χ : Fvᴹ M) → Sub∞ (𝕎.Z* χ) (𝕎.Z* (𝕎.Z* χ ∪ᵀ Eᵉ ⊂r χ))
cvT χ i y = proj₁ y , (y , cE-r χ i (proj₂ y))

ψᵀ : ∀ {M α t} → t <ᴵ α → ∀ {φ χ} → QT α M φ χ → QT t M (Fl ⊔ φ) (𝕎.Z* χ)
ψᵀ {M} {t = t} q t0 = twk proj₁ fcT (Ω̇ᵀ M t)
ψᵀ q (ts a) = tl (repT (ψᵀ q a))
ψᵀ q (tl F) = tl (λ n → ψᵀ q (F n))
ψᵀ q (ti ac f) = ti (λ e → ac (proj₂ e)) (λ x → ψᵀ q (f x))
ψᵀ q (tŝ c₀ t g) = tŝ c₀ (ψᵀ q t) (λ η e → ψᵀ q (g η e))
ψᵀ q (tĉ c₀ z zg o₀ o) = tĉ c₀ z zg (ψᵀ q o₀) (λ η e → ψᵀ q (o η e))
ψᵀ q (tclo t g) = twk asl (λ i e → e) (tclo (twk asr (λ i e → e) (ψᵀ q t)) (λ η → twk asr (λ i e → e) (ψᵀ q (g η))))
ψᵀ q {χ = χ} (tcl n ψ s t g) =
  tcl n (Fl ⊔ ψ) (λ e → (proj₁ e , proj₁ (s (proj₂ e))) , proj₂ (s (proj₂ e))) (ψᵀ q t) (λ η → twk (λ e → e) (𝕎.as-upd {_} {κ′ Fl} {χ} n η) (ψᵀ q (g η)))
ψᵀ q (twk le lc x) = twk (λ e → proj₁ e , le (proj₂ e)) (λ i e → proj₁ e , lc i (proj₂ e)) (ψᵀ q x)
ψᵀ q (tΩ↓ n fe ac h) = tΩ↓ n proj₁ (λ e → ac (proj₂ e)) (λ ξ ζ z → twk swp (λ i → swp) (ψᵀ q (h ξ ζ z)))
ψᵀ q {χ = χ} (tH t g) = tH (ψᵀ q t) (λ e → twk (λ y → y) (Ext.cE-Z e χ) (ψᵀ q (g e)))
ψᵀ q (tk r z x) = ψᵀ q x
ψᵀ q {φ} {χ} (tΩ fe r h) with <ᴵ-dec r q
... | injᵃ (via d s) = tΩ proj₁ s (λ e ξ ζ y → twk swp (λ i w → let c = Ext.cE-Z e χ i (proj₂ w) in proj₁ c , (proj₁ w , proj₂ c)) (ψᵀ q (h e ξ ζ (intoT (<→◃ r) (tr⁻T d (outT (<→◃ s) y))))))
... | injᵇ _ = tl (λ n → twk dupr2 (cvT χ) (ψᵀ q (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) (chainT proj₁ fcT (λ z → twk dupr2 (cvT χ) (ψᵀ r (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) z)))) n)))))
... | injᶜ _ = tl (λ n → twk dupr2 (cvT χ) (ψᵀ q (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) (chainT proj₁ fcT (λ z → twk dupr2 (cvT χ) (ψᵀ r (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) z)))) n)))))
```

## §7 折叠: 目标在低高度, 穿过节点

`EhT H w χ`: 高度不低于 $H$ 的格有证据. `tH` 这一行是这条路线的核心: 目标 $H$ 上移, 证据延拓 (新高度取 $w=1$), 在 $M'$ 里折叠, 由 `↓ᴾ` 拿回 $M$.

```agda
EhT : ∀ {M} → Hᴹ M → (Hᴹ M → Ordᴵ) → Fvᴹ M → Set
EhT H w χ = ∀ i → 𝕎.Hi H i → Ev (w i) (χ i)

EA : ∀ {M} → (Hᴹ M → Ordᴵ) → Fvᴹ M → Set
EA w χ = ∀ i → Ev (w i) (χ i)

e⁺ᵀ : ∀ {M H w} {χ : Fvᴹ M} (n : Hᴹ M) → 𝕎.Ok w → EhT H w χ → EhT H w (𝕎.lo n (𝕎.Z* χ) ∪ᵀ χ)
e⁺ᵀ {χ = χ} n ok e i h = 𝕎.Ev-lo {_} {𝕎.Z* χ} n i (ok i , e i h) , e i h

e-loᵀ : ∀ {M H w n} {χ : Fvᴹ M} (ζ : Fvᴹ M) → 𝕎.Hi n H → EhT H w χ → EhT H w (𝕎.lo n ζ ∪ᵀ χ)
e-loᵀ ζ le e i h = 𝕎.lo-triv ζ (𝕎.Hi-tr le h) , e i h

e↑ᵀ : ∀ {M H n w} {χ : Fvᴹ M} → H <ᴾ n → EhT H w χ → EhT n w χ
e↑ᵀ l e i h′ = e i (𝕎.Hi-up l h′)

eZᵀ : ∀ {M H w} {χ : Fvᴹ M} → 𝕎.Ok w → EhT H w χ → EhT H w (𝕎.Z* χ ∪ᵀ Eᵉ ⊂r χ)
eZᵀ {χ = χ} ok e i h = (ok i , e i h) , cE-r χ i (e i h)

module Raise {M M′ : Code} (e : M ⊂ M′) where
  open Ext e

  w′ : (Hᴹ M → Ordᴵ) → Hᴹ M′ → Ordᴵ
  w′ w = ext (suc zero) w

  ok′ : ∀ {w} → 𝕎.Ok w → 𝕎.Ok (w′ w)
  ok′ {w} ok i′ with dc i′
  ... | inn i refl = subst (λ l → Ev l Fl) (sym (ext-β (suc zero) w i)) (ok i)
  ... | new r = subst (λ l → Ev l Fl) (sym (ext-new (suc zero) w r)) ok₁

  Hi↓ : ∀ {H i} → 𝕎.Hi (u H) (u i) → 𝕎.Hi H i
  Hi↓ (inj₁ d) = inj₁ (up-inj e d)
  Hi↓ {H} {i} (inj₂ l) = inj₂ (up-refl e {p = H} {q = i} l)

  rise : ∀ {w} {χ : Fvᴹ M} {H} → EhT H w χ → EhT (u H) (w′ w) (E χ)
  rise {w} {χ} ev i′ h with dc i′
  ... | inn i refl = subst (λ l → Ev l (E χ (u i))) (sym (ext-β (suc zero) w i)) (E-β⁻ χ i (ev i (Hi↓ h)))
  ... | new r = subst (λ l → Ev l (E χ i′)) (sym (ext-new (suc zero) w r)) (E-n⁻ χ r ok₁)

  riseA : ∀ {w} {χ : Fvᴹ M} → EA w χ → EA (w′ w) (E χ)
  riseA {w} {χ} ev i′ with dc i′
  ... | inn i refl = subst (λ l → Ev l (E χ (u i))) (sym (ext-β (suc zero) w i)) (E-β⁻ χ i (ev i))
  ... | new r = subst (λ l → Ev l (E χ i′)) (sym (ext-new (suc zero) w r)) (E-n⁻ χ r ok₁)

  rise< : ∀ {w t H} → t <ᴵ w H → t <ᴵ w′ w (u H)
  rise< {w} {t} {H} p = subst (t <ᴵ_) (sym (ext-β (suc zero) w H)) p

  back : ∀ {H} (χ : Fvᴹ M) → 𝕎.Sub H (𝕎.Z* χ) (L.res e (𝕎.Z* (E χ)))
  back χ i r y = proj₁ y , E-β⁻ χ i (proj₂ y)

ΨT : ∀ {M α φ χ t w} (H : Hᴹ M) → 𝕎.Ok w → EhT H w χ → t <ᴵ w H → QT α M φ χ → Qᴹ M H t (Fl ⊔ φ) (𝕎.Z* χ)
ΨT {t = t} H ok e p t0 = 𝕎.qwk proj₁ 𝕎.fc* (𝕎.Ω̇ H t)
ΨT H ok e p (ts a) = 𝕎.ql (𝕎.repᵠ (ΨT H ok e p a))
ΨT H ok e p (tl F) = 𝕎.ql (λ n → ΨT H ok e p (F n))
ΨT H ok e p (ti ac f) = 𝕎.qi (λ u → ac (proj₂ u)) (λ x → ΨT H ok e p (f x))
ΨT H ok e p (tŝ c₀ x g) = 𝕎.qŝ c₀ (ΨT H ok e p x) (λ η d → ΨT H ok e p (g η d))
ΨT H ok e p (tĉ c₀ z zg o₀ o) = 𝕎.qĉ c₀ z zg (ΨT H ok e p o₀) (λ η d → ΨT H ok e p (o η d))
ΨT H ok e p (tclo x g) = 𝕎.qwk asl 𝕎.sub-id (𝕎.qclo (𝕎.qwk asr 𝕎.sub-id (ΨT H ok e p x)) (λ η → 𝕎.qwk asr 𝕎.sub-id (ΨT H ok e p (g η))))
ΨT H ok e p (twk le le′ x) = 𝕎.qwk (λ u → proj₁ u , le (proj₂ u)) (λ i r u → proj₁ u , le′ i (proj₂ u)) (ΨT H ok (λ i h → le′ i (e i h)) p x)
ΨT H ok e p (tk r z x) = ΨT H ok e p x
ΨT {M} {t = t} H ok e p (tH x g) =
  𝕎.qŝ zero (ΨT H ok e p x) (λ η d →
    let e₁ = ⊂+ M ⌈ η ⌉
    in 𝕎.qwk (λ u → u) (Raise.back e₁ _) (L.↓ᴾ e₁ H t (ΨT (up e₁ H) (Raise.ok′ e₁ ok) (Raise.rise e₁ e) (Raise.rise< e₁ p) (g e₁))))
ΨT {M} {χ = χ} {w = w} H ok e p (tcl n ψ s x g) with <ᴾ-tri n H
... | tlt l =
  𝕎.qcl l (Fl ⊔ ψ) (λ u → (proj₁ u , proj₁ (s (proj₂ u))) , proj₂ (s (proj₂ u))) (ΨT H ok e p x)
      (λ η → 𝕎.qwk (λ u → u) (𝕎.⇑ (𝕎.as-upd {_} {𝕎.κ Fl} {χ} n η))
         (ΨT H ok (λ i h → subst (Ev _) (sym (𝕎.upd-gt χ _ (𝕎.Hi-gt l h))) (e i h)) p (g η)))
... | teq refl =
  𝕎.qŝ (Bd B) (ΨT H ok e p x)
     (λ η d → 𝕎.qwk (λ u → u) (λ i r u → proj₁ u , subst (Ev _) (sym (𝕎.upd-lt χ _ r)) (proj₂ u))
              (ΨT H (𝕎.upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′)))
               (λ i h → 𝕎.upd-ev n i w χ (𝕎.evη {M} ψ B η d) (e i h))
               (subst (t′ <ᴵ_) (sym (𝕎.upd-self w n _)) (lim 0 (iF B))) (g η)))
  where
  B = bound (ψ ⊔ fk zero) (s (e n (inj₁ refl))) p
  t′ = _
... | tgt l =
  𝕎.qŝ (Bd B) (ΨT H ok e p x)
     (λ η d → 𝕎.qwk (λ u → u) (λ i r u → proj₁ u , subst (Ev _) (sym (𝕎.upd-lt χ _ (<ᴾ-trans i H n r l))) (proj₂ u))
              (ΨT H (𝕎.upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′)))
               (λ i h → 𝕎.upd-ev n i w χ (𝕎.evη {M} ψ B η d) (e i h))
               (subst (t′ <ᴵ_) (sym (𝕎.upd-lt w _ l)) p) (g η)))
  where
  B = bound (ψ ⊔ fk zero) (s (e n (inj₂ l))) (𝕎.zr ok n)
  t′ = _
ΨT {φ = φ} {χ = χ} H ok e p (tΩ↓ {k = k} n fe ac h) with <ᴾ-tri n H
... | tlt l = 𝕎.qΩ↓ l proj₁ (λ u → ac (proj₂ u)) (λ ξ ζ z → 𝕎.qwk swp (λ i r → swp) (ΨT H ok (e-loᵀ ζ (inj₂ l) e) p (h ξ ζ (𝕎.outV l z))))
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl))) p
...   | injᵃ (via d s) = 𝕎.qΩ proj₁ s (λ ξ ζ y → 𝕎.qwk swp (λ i r → swp) (ΨT H ok (e-loᵀ ζ (inj₁ refl) e) p (h ξ ζ (𝕎.tr⁻Q d (𝕎.outU (<→◃ s) y)))))
...   | injᵇ _ = 𝕎.ql (λ i → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* H)) (ΨT H ok (e⁺ᵀ H ok e) p (h (Fl ⊔ φ) (𝕎.Z* χ) (𝕎.chainᵠ proj₁ 𝕎.fc* (λ z → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* n)) (ΨT n ok (e⁺ᵀ n ok e) (ac (e n (inj₁ refl))) (h (Fl ⊔ φ) (𝕎.Z* χ) z))) i))))
...   | injᶜ _ = 𝕎.ql (λ i → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* H)) (ΨT H ok (e⁺ᵀ H ok e) p (h (Fl ⊔ φ) (𝕎.Z* χ) (𝕎.chainᵠ proj₁ 𝕎.fc* (λ z → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* n)) (ΨT n ok (e⁺ᵀ n ok e) (ac (e n (inj₁ refl))) (h (Fl ⊔ φ) (𝕎.Z* χ) z))) i))))
ΨT {φ = φ} {χ = χ} H ok e p (tΩ↓ {k = k} n fe ac h) | tgt l =
  𝕎.ql (λ i → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* n)) (ΨT H ok (e⁺ᵀ n ok e) p (h (Fl ⊔ φ) (𝕎.Z* χ) (𝕎.chainᵠ proj₁ 𝕎.fc* (λ z → 𝕎.qwk dupr2 (𝕎.⇑ (𝕎.cv* n)) (ΨT n ok (e⁺ᵀ n ok (e↑ᵀ l e)) (ac (e↑ᵀ l e n (inj₁ refl))) (h (Fl ⊔ φ) (𝕎.Z* χ) z))) i))))
ΨT {φ = φ} {χ = χ} H ok e p (tΩ fe r h) =
  𝕎.ql (λ i → 𝕎.qwk dupr2 (𝕎.⇑ (cvT χ)) (ΨT H ok (eZᵀ ok e) p (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) (chainT proj₁ fcT (λ z → twk dupr2 (cvT χ) (ψᵀ r (h ⊂r (Fl ⊔ φ) (𝕎.Z* χ) (intoT (<→◃ r) z)))) i)))))
```

## §8 折叠: 目标可数, 闭项

`tH` 落成已有的 `ŝ`: $\eta$ 绑定, 这一支的世界是 $M$ `ᶜ+` $\lceil\eta\rceil$. 这里只记住 $\eta$, 这正是第一个障碍.

```agda
ψ̄ᵀ : ∀ {M α φ χ w} → 𝕎.Ok w → EA w χ → QT α M φ χ → Run φ
ψ̄ᵀ ok e t0 = wk 0 (λ _ → tt) ∅ᴿ
ψ̄ᵀ ok e (ts a) = sucRun (ψ̄ᵀ ok e a)
ψ̄ᵀ ok e (tl F) = limA 0 (λ n → ψ̄ᵀ ok e (F n))
ψ̄ᵀ ok e (ti ac f) = limᵢA 0 ac (λ x → ψ̄ᵀ ok e (f x))
ψ̄ᵀ ok e (tŝ c₀ t g) = ŝA 0 c₀ (ψ̄ᵀ ok e t) (λ η d → ψ̄ᵀ ok e (g η d))
ψ̄ᵀ ok e (tĉ c₀ t₀ zg o₀ o) = ĉA 0 c₀ t₀ zg (ψ̄ᵀ ok e o₀) (λ η d → ψ̄ᵀ ok e (o η d))
ψ̄ᵀ ok e (tclo t g) = cloA 0 (ψ̄ᵀ ok e t) (λ η → ψ̄ᵀ ok e (g η))
ψ̄ᵀ {M} {χ = χ} {w = w} ok e (tcl n ψ s t g) =
  ŝA 0 (Bd B) (ψ̄ᵀ ok e t)
     (λ η d → ψ̄ᵀ (𝕎.upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))) (λ i → 𝕎.upd-ev n i w χ (𝕎.evη {M} ψ B η d) (e i)) (g η))
  where B = bound (ψ ⊔ fk zero) (s (e n)) (𝕎.zr ok n)
ψ̄ᵀ ok e (twk le le′ x) = wk 0 le (ψ̄ᵀ ok (λ i → le′ i (e i)) x)
ψ̄ᵀ ok e (tk r z x) = ψ̄ᵀ ok e x
ψ̄ᵀ {M} ok e (tH x g) = ŝA 0 zero (ψ̄ᵀ ok e x) (λ η d → ψ̄ᵀ (Raise.ok′ (⊂+ M ⌈ η ⌉) ok) (Raise.riseA (⊂+ M ⌈ η ⌉) e) (g (⊂+ M ⌈ η ⌉)))
ψ̄ᵀ {φ = φ} {χ = χ} ok e (tΩ↓ {k = k} n fe ac h) =
  limA 0 (λ i → wk 0 (λ v → v , v) (ψ̄ᵀ ok (λ j → 𝕎.Ev-lo {_} {𝕎.Z* χ} n j (ok j , e j) , e j) (h φ (𝕎.Z* χ) (𝕎.chainᵠ fe 𝕎.fc* (λ z → 𝕎.qwk (λ v → fe v , (v , v)) (𝕎.⇑ (𝕎.cv* n)) (ΨT n ok (e⁺ᵀ n ok (λ j′ _ → e j′)) (ac (e n)) (h φ (𝕎.Z* χ) z))) i))))
ψ̄ᵀ {φ = φ} {χ = χ} ok e (tΩ fe r h) =
  limA 0 (λ i → wk 0 (λ v → v , v) (ψ̄ᵀ ok (λ j → (ok j , e j) , cE-r χ j (e j)) (h ⊂r φ (𝕎.Z* χ) (intoT (<→◃ r) (chainT fe fcT (λ z → twk (λ v → fe v , (v , v)) (cvT χ) (ψᵀ r (h ⊂r φ (𝕎.Z* χ) (intoT (<→◃ r) z)))) i)))))

-- ψ₀(Ω_{ψ₁(Ω)+α}), 从最小的地板 M 起
Tᵀ : Code → Ordᴵ → Run Fl
Tᵀ M α = ψ̄ᵀ 𝕎.ok₀ (λ i → 𝕎.ok₀ i) (Ω̇ᵀ M α)
```
