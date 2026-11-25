# 抽象理论 (八): 分级模拟的接口

> 判决: 接口 (记录与律的陈述), 无定理; 只导入标准库, `YiAbsFrame`, `YiAbsSim`. 在 `Block`/`Fold` 之上加行的运算 (`Rows`), 带 Ω 余尾的参照系统 (`Ref`), 各层的关系与层号读法 (`Graded`), 量化域 (`Doms`); 律是按量化域陈述的谓词, 汇总成 `GSim` 与第 0 层的 `Base`.
> 律不比较两个指定孩子: 每条律至多出现一个孩子下标, 或对一切孩子一致; 没有头部观察 (`hd`) 与回退 (`Off`).
> 充分性在 [YiAbsGSuff](YiAbsGSuff.lagda.md), 行律在 [YiAbsGRow](YiAbsGRow.lagda.md), 模型在 [YiAbsGToy](YiAbsGToy.lagda.md), 否定在 [YiAbsGNeg](YiAbsGNeg.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsGIface where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
```

## 参照系统

`YiAbsSim.Exit` 的参照系统 (余尾 0, 1, ω; `pred`, `fsn`) 加上: 余尾 Ω_{κ+1} (`CΩ t κ`), 代入 `fsT t η`, 和 `⊕`, 以及 Ω_ν (`Ωr ν`).

```agda
record Ref : Set₁ where
  infixr 5 _⊕_
  field
    T        : Set
    C0 C1 Cω : T → Set
    CΩ       : T → T → Set
    pred     : T → T
    fsn      : T → ℕ → T
    fsT      : T → T → T
    _⊕_      : T → T → T
    Ωr       : T → T
```

## 行的运算

块上各行用到的树的运算: 后继 `sc`; 槽位 p 上的结点 `nd p g` (分支下标在槽位层 `slL ℓ p`, 换型 `slT` 同 `chT`); Ω 树 `Ωt`; 上折 `upf d β y` (沿下降 d 把低层的 y 折进本层, 底值 β).
层号的运算: 后继 `sucL`, Ω 形状 `ΩL k h`, 把第 k 层的树读成层号 `lift k x`.

```agda
record Rows (𝔹 : Block) (𝔽 : Fold 𝔹) : Set₁ where
  open Block 𝔹
  open Fold 𝔽
  field
    sc   : ∀ {ℓ} → Tr ℓ → Tr ℓ
    Sl   : Lv → Set
    slL  : (ℓ : Lv) → Sl ℓ → Lv
    SlT  : (ℓ : Lv) → Sl ℓ → Set
    slT  : (ℓ : Lv) (p : Sl ℓ) → SlT ℓ p → Tr (slL ℓ p)
    nd   : ∀ {ℓ} (p : Sl ℓ) → (SlT ℓ p → Tr ℓ) → Tr ℓ
    Ωt   : (ℓ : Lv) → Tr ℓ
    Dn   : Lv → Lv → Set
    upf  : ∀ {ℓ j} → Dn ℓ j → Bt ℓ → Tr j → Tr ℓ
    sucL : Lv → Lv
    ΩL   : (k : Lv) → (Tr k → Lv) → Lv
    lift : (k : Lv) → Tr k → Lv
```

## 分级的关系

`R ℓ t x`: 参照项 t 不高于第 ℓ 层的树 x 的证据. `Rd ℓ ν`: 参照下标 ν 不高于层号 ℓ. `Nu ℓ p κ`: 槽位 p 允许的余尾下标.
`cl ℓ t`: 参照一侧第 ℓ 层的折叠 (折到自身时的像). `Cx ℓ j`, `app`: 折到低层 j 时参照一侧的上下文 (目标下标与前缀); `Bd b w β K`: 底 b 与底值 β 对着上下文 K.

```agda
record Graded (𝔹 : Block) (𝔽 : Fold 𝔹) (ℜ : Rows 𝔹 𝔽) (𝕋 : Ref) (𝕍 : Val) : Set₁ where
  open Block 𝔹
  open Fold 𝔽
  open Rows ℜ
  open Ref 𝕋
  open Val 𝕍
  field
    ℓ₀  : Lv
    v   : Tr ℓ₀ → V
    R   : (ℓ : Lv) → T → Tr ℓ → Set
    Rd  : Lv → T → Set
    Nu  : (ℓ : Lv) → Sl ℓ → T → Set
    bt  : ∀ {j} → Bt j → Tr j
    cl  : Lv → T → T
    Cx  : Lv → Lv → Set
    app : ∀ {ℓ j} → Cx ℓ j → T → T
    Bd  : ∀ {ℓ j} → Bs ℓ → j ⊑ ℓ → Bt j → Cx ℓ j → Set
```

## 量化域

`Gx`: 树 (合法, 或规范的读回域); `Gb`: 底; `Wl`: 折到低层的律所管的路径; `Gl`: 读成层号的树.

```agda
record Doms (𝔹 : Block) (𝔽 : Fold 𝔹) : Set₁ where
  open Block 𝔹
  open Fold 𝔽
  field
    Gx : (ℓ : Lv) → Tr ℓ → Set
    Gb : (ℓ : Lv) → Bs ℓ → Set
    Wl : ∀ {j ℓ} → j ⊑ ℓ → Set
    Gl : (k : Lv) → Tr k → Set
```

## 律

```agda
module Laws {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
            (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Block 𝔹 public
  open Fold 𝔽 public
  open Rows ℜ public
  open Ref 𝕋 public
  open Val 𝕍 public
  open Graded 𝔾 public
  open Doms 𝔻 public
  open Exit 𝕍 {T = T} C0 C1 Cω pred fsn public using (HC; h0; h1; hω; tree; module Sim)

  infix 4 _⊴_
  _⊴_ : ∀ {ℓ} → Tr ℓ → Tr ℓ → Set
  x ⊴ y = (x ≡ y) ⊎ (x ◃ y)
```

关系的生成规则 (每层一份): 零, 后继, ℕ 极限 (不严格: 基本列逐项不高于同一棵树), 结点, 嵌入, 沿第一位置序放宽.

```agda
  Zero Succ Lim Weak Node Emb : Set
  Zero = ∀ {ℓ t x} → C0 t → R ℓ t x
  Succ = ∀ {ℓ t x} → C1 t → R ℓ (pred t) x → R ℓ t (sc x)
  Lim  = ∀ {ℓ t x} → Cω t → (∀ n → R ℓ (fsn t n) x) → R ℓ t x
  Weak = ∀ {ℓ t x x′} → R ℓ t x → x ◃ x′ → R ℓ t x′
  Node = ∀ {ℓ} (p : Sl ℓ) {t κ} (g : SlT ℓ p → Tr ℓ) → CΩ t κ → Nu ℓ p κ
       → (∀ η c → R (slL ℓ p) η (slT ℓ p c) → R ℓ (fsT t η) (g c)) → R ℓ t (nd p g)
  Emb  = ∀ {ℓ} (c : Ch ℓ) {t s x} (y : ChT ℓ c) → R ℓ t x → R (chL ℓ c) s (chT ℓ c y) → R ℓ (t ⊕ s) (up x c y)
```

折叠的三条保持: 折到自身 (带前缀 P), 上折, 折到低层 (带上下文 K).

```agda
  SelfKeep UpKeep LowKeep : Set
  SelfKeep = ∀ {ℓ} (b : Bs ℓ) (β : Bt ℓ) → Gb ℓ b → ∀ {P a x}
           → R ℓ (cl ℓ P) (bt β) → R ℓ a x → R ℓ (cl ℓ (P ⊕ a)) (ψ ℓ b ℓ self β x)
  UpKeep   = ∀ {ℓ j} (d : Dn ℓ j) (β : Bt ℓ) {t s y}
           → R ℓ (cl ℓ t) (bt β) → R j s y → R ℓ (cl ℓ (t ⊕ s)) (upf d β y)
  LowKeep  = ∀ {ℓ j} (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (K : Cx ℓ j) → Gb ℓ b → Wl w → Bd b w β K
           → ∀ {a x} → Gx ℓ x → R ℓ a x → R j (app K a) (ψ ℓ b j w β x)
```

层号读法的四条 (零, 后继, ℕ 极限, Ω 形状), Ω 树对着 Ω_ν (`Leaf`), 树读成层号 (`Lift`).

```agda
  Rd0 RdS RdL RdΩ Leaf Lift : Set
  Rd0  = ∀ {ℓ ν} → C0 ν → Rd ℓ ν
  RdS  = ∀ {ℓ ν} → C1 ν → Rd ℓ (pred ν) → Rd (sucL ℓ) ν
  RdL  = ∀ {ℓ ν} → Cω ν → (∀ n → Rd ℓ (fsn ν n)) → Rd ℓ ν
  RdΩ  = ∀ {k ν κ} (h : Tr k → Lv) → CΩ ν κ → Rd k κ → (∀ s c → R k s c → Rd (h c) (fsT ν s)) → Rd (ΩL k h) ν
  Leaf = ∀ {ℓ ν} → Rd ℓ ν → R ℓ (Ωr ν) (Ωt ℓ)
  Lift = ∀ {k s x} → Gl k x → R k s x → Rd (lift k x) s
```

第 0 层 (`ℓ₀`): `YiAbsSim.Sim` 的前提, 折叠取恒等. 余尾 1 处反演出严格的一步, 余尾 ω 处逐项反演出不严格的一步.

```agda
  record Base : Set₁ where
    infix 4 _⇝ˢ_ _⇝_
    field
      G₀     : Tr ℓ₀ → Set
      _⇝ˢ_   : Tr ℓ₀ → Tr ℓ₀ → Set
      _⇝_    : Tr ℓ₀ → Tr ℓ₀ → Set
      strict : ∀ {x y} → G₀ y → x ⇝ˢ y → vs (v x) ≼ v y
      weak   : ∀ {x y} → G₀ y → x ⇝ y → v x ≼ v y
      inv1   : ∀ {t x} → R ℓ₀ t x → G₀ x → C1 t → Σ (Tr ℓ₀) λ x′ → R ℓ₀ (pred t) x′ × G₀ x′ × (x′ ⇝ˢ x)
      invω   : ∀ {t x} → R ℓ₀ t x → G₀ x → Cω t → ∀ n → Σ (Tr ℓ₀) λ x′ → R ℓ₀ (fsn t n) x′ × G₀ x′ × (x′ ⇝ x)

  record GSim : Set where
    field
      zeroᴿ : Zero
      succᴿ : Succ
      limᴿ  : Lim
      weakᴿ : Weak
      nodeᴿ : Node
      embᴿ  : Emb
      selfᴷ : SelfKeep
      upᴷ   : UpKeep
      lowᴷ  : LowKeep
      rd0   : Rd0
      rdS   : RdS
      rdL   : RdL
      rdΩ   : RdΩ
      leaf  : Leaf
      liftᴿ : Lift
```

## 塔

塔的下一项是把本项的 Ω 树读成层号 (`tw-step` 留一步放宽). 参照一侧 `kt (n+1) = Ω_{kt n}`. 标准的底、路径、底值与上下文给出闭项 `twc n` 与参照行 `row n`.

```agda
  record Keel (𝔟 : Base) : Set where
    open Base 𝔟
    field
      tw      : ℕ → Lv
      κ₀      : T
      rd-tw0  : Rd (tw 0) κ₀
      tw-step : ∀ n {ν} → Rd (lift (tw n) (Ωt (tw n))) ν → Rd (tw (suc n)) ν
      gl      : ∀ n → Gl (tw n) (Ωt (tw n))
      b₀      : ∀ n → Bs (tw n)
      w₀      : ∀ n → ℓ₀ ⊑ tw n
      β₀      : ∀ n → Bt ℓ₀
      K₀      : ∀ n → Cx (tw n) ℓ₀
      gb      : ∀ n → Gb (tw n) (b₀ n)
      wl      : ∀ n → Wl (w₀ n)
      bd      : ∀ n → Bd (b₀ n) (w₀ n) (β₀ n) (K₀ n)
      gx      : ∀ n → Gx (tw n) (Ωt (tw n))
      g₀      : ∀ n → G₀ (ψ (tw n) (b₀ n) ℓ₀ (w₀ n) (β₀ n) (Ωt (tw n)))

    kt : ℕ → T
    kt zero    = κ₀
    kt (suc n) = Ωr (kt n)

    twc : ℕ → Tr ℓ₀
    twc n = ψ (tw n) (b₀ n) ℓ₀ (w₀ n) (β₀ n) (Ωt (tw n))

    row : ℕ → T
    row n = app (K₀ n) (Ωr (kt n))
```
