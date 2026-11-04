# 带地板操作的定义域

> 不含记号. 结论写在 [DomFold](DomFold.lagda.md). `Dom` ([GuardTightLv](GuardTightLv.lagda.md)) 只有比较, 没有 "求界". [GuardTightTree](GuardTightTree.lagda.md) 的 `Fold` 求界时直接用 `Ordᴵ` 的 `Mlev`, `bound`, 所以绑死在 `Dom₀` 上. 这里把求界抽成接口 `Tp`, `bound`, 其余字段都只为读回与上升.
>
> `X₀`: `Dom₀` 的实例. 求界就是原来的 `OCF.Free.Floor.bound` 与 `Mlev`, 所以数值与 [GuardTightTree](GuardTightTree.lagda.md) 字面一致 (这条只有有限测试: [DomFoldAccept](DomFoldAccept.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DomFoldDom where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Free.Level using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; Simᴵ; ⊑ᴵ-trans; zero; suc; lim)
import OCF.Free.Level as Lvl
open import OCF.Free.Aux using (Mlev)
import OCF.Free.Floor as FF
open import OCF.Align.GuardTightLv
open import OCF.Align.GuardTightFeed using (ofL; Ωᴸ; Cf-Ωᴸ)
```

## §1 地板, 与求界的接口

`Ev ℓ φ`: 地板 $\varphi$ 的每一项都严格低于 $\ell$ (`<ᴰ`). `Tp ℓ φ`: 求界的结果. `Bd` 是新闭包的下界, 它压得住地板的每一项 (`Kb`). 对 `Bd ⊑ᴰ η`, `upX` 是一个字面的公共上界: 地板 (`upEv`) 与 $\eta$ (`up<`) 都在它之下. **这里没有比较两个任意元: `bound` 的入参 `Ev ℓ φ` 已经是一个公共上界.**

```agda
module FlrOf (𝔻 : Dom) where
  open Dom 𝔻

  infixl 5 _⊔_
  data Flr : Set where
    fz  : Flr
    fk  : D → Flr
    _⊔_ : Flr → Flr → Flr

  Ev : D → Flr → Set
  Ev ℓ fz      = ⊤
  Ev ℓ (fk K)  = K <ᴰ ℓ
  Ev ℓ (a ⊔ b) = Ev ℓ a × Ev ℓ b

  data InF (K : D) : Flr → Set where
    ink : InF K (fk K)
    inl : ∀ {a b} → InF K a → InF K (a ⊔ b)
    inr : ∀ {a b} → InF K b → InF K (a ⊔ b)

  evIn : ∀ {ℓ K φ} → Ev ℓ φ → InF K φ → K <ᴰ ℓ
  evIn e ink = e
  evIn (x , y) (inl i) = evIn x i
  evIn (x , y) (inr i) = evIn y i

  record Tp (ℓ : D) (φ : Flr) : Set where
    constructor tpr
    field
      Bd   : D
      Kb   : ∀ {K} → InF K φ → K ⊑ᴰ Bd
      upX  : ∀ {η} → Bd ⊑ᴰ η → D
      upEv : ∀ {η} (d : Bd ⊑ᴰ η) → Ev (upX d) φ
      up<  : ∀ {η} (d : Bd ⊑ᴰ η) → η <ᴰ upX d
  open Tp public
```

## §2 带求界的定义域

- `⊑-tr`, `self<`, `bound`: 折叠要的.
- `ht`: 这座塔到第几层 (`Dom₀` 是 0). `ix η`: 下标 $\eta$ 所在的层, 即闭包的共尾度是 $\Omega_{ix+1}$. 目标低于 `ix` 时闭包要带链 (判断的依据是 EBO 的规则 6, 这里只作定义).
- `nodeC j`, `nodeF j`, `emᵈ`: 读回第 $j$ 层节点 $\Omega_{j+1}$ 时用的下界, 第一支, 下标的嵌入.
- `base`: 下一层闭包的第一支, 带证书 (第 1 层是 $\Omega_1$).
- `bot`: 空表的默认值. 自然数目标不读表, 所以它的值不影响树 (判断); 这里不要求任何性质.

```agda
record DomX : Set₁ where
  field
    𝔻 : Dom
  open Dom 𝔻
  open FlrOf 𝔻
  open Lv 𝔻 using (LG; Cfˢ)
  field
    ⊑-tr   : ∀ {a b c} → a ⊑ᴰ b → b ⊑ᴰ c → a ⊑ᴰ c
    self<  : ∀ η → η <ᴰ sD η
    bound  : ∀ {ℓ K₀} (φ : Flr) → Ev ℓ φ → K₀ <ᴰ ℓ → Tp ℓ φ
    ht     : ℕ
    ix     : D → ℕ
    nodeC  : ℕ → D
    nodeF  : ℕ → LG
    emᵈ    : D → LG
    base   : Σ LG Cfˢ
    bot    : D
```

## §3 `Dom₀` 的实例

地板的项是分支值 $K$, 进旧地板时取 `pr K`: 这就是旧 `pick` 的 `fk (pr K)`.

```agda
private
  module F₀ = FlrOf Dom₀

toF : F₀.Flr → FF.Flr
toF F₀.fz = FF.fz
toF (F₀.fk K) = FF.fk (pr K)
toF (a F₀.⊔ b) = toF a FF.⊔ toF b

lit : ∀ {K ℓ} → K <ᴵ ℓ → Simᴵ (suc K) ℓ
lit q Lvl.zero = q
lit q (Lvl.suc r) = Lvl.<ᴵ-trans r q

toEv : ∀ {ℓ} (φ : F₀.Flr) → F₀.Ev ℓ φ → FF.Ev ℓ (toF φ)
toEv F₀.fz e = tt
toEv (F₀.fk K) e = lit e
toEv (a F₀.⊔ b) (x , y) = toEv a x , toEv b y

ofEv : ∀ {ℓ} (φ : F₀.Flr) → FF.Ev ℓ (toF φ) → F₀.Ev ℓ φ
ofEv F₀.fz e = tt
ofEv (F₀.fk K) e = e Lvl.zero
ofEv (a F₀.⊔ b) (x , y) = ofEv a x , ofEv b y

bound₀ : ∀ {ℓ K₀} (φ : F₀.Flr) → F₀.Ev ℓ φ → pr K₀ <ᴵ ℓ → F₀.Tp ℓ φ
bound₀ φ y q = F₀.tpr (FF.Bd B) kb
    (λ {η} d → Mlev (FF.Fc B) (suc η) (FF.FB B d))
    (λ {η} d → ofEv φ (FF.liftEv (toF φ) (λ r → Lvl.lim 0 r) (FF.evF B)))
    (λ {η} d → lt→pr (Lvl.lim 1 Lvl.zero))
  where
  B = FF.bound (toF φ) (toEv φ y) q
  kb : ∀ {K} → F₀.InF K φ → K ⊑ᴵ FF.Bd B
  kb i = ⊑ᴵ-trans (pr⊑ _ (F₀.evIn (ofEv φ (FF.evF B)) i)) (FF.FM B)

X₀ : DomX
X₀ = record
  { 𝔻 = Dom₀
  ; ⊑-tr = ⊑ᴵ-trans
  ; self< = λ η → lt→pr Lvl.zero
  ; bound = λ φ y q → bound₀ φ y q
  ; ht = 0
  ; ix = λ _ → 0
  ; nodeC = λ _ → suc zero
  ; nodeF = λ _ → Lv.suc Lv.zero
  ; emᵈ = ofL
  ; base = Ωᴸ , Cf-Ωᴸ
  ; bot = zero
  }
```
