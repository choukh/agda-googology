# X₂ 与往 `tw n`, 否定一路 (三): 接口 `X2If` 的盲区

> 不含记号. 入口 [NegX2](NegX2.lagda.md). 只读导入接口 [X2If](X2If.lagda.md) 与构造一路的 [X1UpFold](X1UpFold.lagda.md) (`emb`), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 接口 `X2If` 给 $X_2$ 的种类一个分类 `cls` (低种类 = 底 $X_1$ 的种类 $\kappa_0$ 的视图, 带证据与坐标读入 `to`; 高种类 = 叠层 $X_1\oplus i$ 的种类, $i\sqsubset\mathrm{lvW}\,W$, 带坐标读入) 与逐种类的换层 (`cvK`, `cvE`). 接口约束了什么, 没约束什么?
>
> **结果 (都对一切实例).**
>
> 1. **`constOf`, `const-lo`, `const-up`, `const-cv` (构造与定理, 盲).** 把一切坐标读入 (`cls` 的 `to`, `cvE`) 换成常值 (种类结构的最小坐标 `bot`), 其余字段不动, 仍是实例. 接口不管读入是否保住分支 (同 `NegX1UpPay.constPayOf`, `NegPathOutIf.constShiftOf`).
> 2. **`allLoOf`, `all-lo` (构造与定理, 盲).** 只要底有一个 "无条件有证据" 的种类 $\kappa_0$ (对一切世界 $W$, `Ev W κ₀`), 就可以把**一切**种类都分成 $\kappa_0$ 的低种类视图, 仍是实例. 接口里没有 "分类与种类的读回层一致" 的律 (`PathOutIf.correct` 的对应物), 所以叠层的高种类可以被当成 $\Omega_1$ 处理. 前提实例: `IX₁` 的 $\Omega_1$ 种类 `κΩ`, 证据字面是 `⊤` (`free-κΩ`).
> 3. **`voidOf` (构造, 盲).** 证据恒空 (`Ev₂ = ⊥`), 换层恒不可 (`CvK = ⊥`), 仍是实例; 那时带路径的高度只有不含 $\Omega$-结点的树 (判断, 依据 `X2Fold.PH₂` 的定义: 结点要 `Ev₂`).
>
> **只否定什么.** 只说接口的字段不蕴含: 读入保值 (1), 分类正确 (2), 有非平凡的证据 (3). **不否定**: 构造一路的实例是否满足这些 (那要看实例, 见 [NegX2Inst](NegX2Inst.lagda.md)); 折叠 `Ψ₂` 与 `Sh-Ψ₂`. 本篇没有关闭任何路线. 建议增补的律 (判断): 分类正确 (低种类的读回层就是 $\kappa_0$ 的读回层; 高种类的读回层就是 $X_1\oplus i$), 写法同 `PathOutIf.correct`, 两个下标都带相对同一世界的证据.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX2If where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy using (KS; K; E; HB; bot)
open import OCF.Align.PathOutIf using (module PathOutIf)
open import OCF.Align.X1UpIf
import OCF.Align.X1UpFold as UF
open import OCF.Align.X2If
open import OCF.Align.PathOutX1 using (IX₁; κΩ; Ev₁)
```

## §1 读入换常值

```agda
module _ (V : X2If) where
  open X2If V
  open X1UpIf U using (P)
  open PathOutIf P using (XS; Wo)

  constCls : ∀ {W κ} → ClX U XS₂ lvW W κ → ClX U XS₂ lvW W κ
  constCls {κ = κ} (lo κ₀ ev to) = lo κ₀ ev (λ _ → bot XS₂ κ)
  constCls {κ = κ} (up i q to) = up i q (λ _ → bot XS₂ κ)

  constOf : X2If
  constOf = record V
    { cls = λ W κ ev → constCls (cls W κ ev)
    ; cvE = λ W κ k _ → bot XS₂ κ }

  -- 读入是常值
  ConstTo : ∀ {W κ} → ClX U XS₂ lvW W κ → Set
  ConstTo (lo κ₀ ev to) = ∀ e e′ → to e ≡ to e′
  ConstTo (up i q to) = ∀ b b′ → to b ≡ to b′

  const-to : ∀ {W κ} (c : ClX U XS₂ lvW W κ) → ConstTo (constCls c)
  const-to (lo κ₀ ev to) e e′ = refl
  const-to (up i q to) b b′ = refl

  const-cls : ∀ W κ ev → ConstTo (X2If.cls constOf W κ ev)
  const-cls W κ ev = const-to (cls W κ ev)

  const-cv : ∀ W κ k e e′ → X2If.cvE constOf W κ k e ≡ X2If.cvE constOf W κ k e′
  const-cv W κ k e e′ = refl
```

## §2 一切种类都当成同一个底种类

```agda
  module AllLo (κ₀ : K XS) (free : ∀ W → PathOutIf.Ev P W κ₀) where
    allLoOf : X2If
    allLoOf = record V { cls = λ W κ ev → lo κ₀ (free W) (λ _ → bot XS₂ κ) }

    IsLo : ∀ {W κ} → ClX U XS₂ lvW W κ → Set
    IsLo (lo κ₁ _ _) = κ₁ ≡ κ₀
    IsLo (up _ _ _) = ⊥

    all-lo : ∀ W κ ev → IsLo (X2If.cls allLoOf W κ ev)
    all-lo W κ ev = refl

-- 前提实例: IX₁ 的 Ω₁ 种类在一切世界里有证据
free-κΩ : ∀ B → Ev₁ B κΩ
free-κΩ B = tt
```

## §3 证据恒空

```agda
voidOf : X2If → X2If
voidOf V = record V
  { Ev₂ = λ _ _ → ⊥ ; cls = λ W κ () ; CvK = λ _ _ → ⊥ ; cvK = λ W κ () ; cvE = λ W κ () }
```

## 结论 (按档)

- **[定理]** `constCls`, `constOf`, `ConstTo`, `const-to`, **`const-cls`**, **`const-cv`**; `AllLo.allLoOf`, `IsLo`, **`AllLo.all-lo`**; `free-κΩ` (前提实例); `voidOf`.
- **[判断]** 建议增补的 "分类正确" 律; `voidOf` 上带路径的高度只有无结点的树.
