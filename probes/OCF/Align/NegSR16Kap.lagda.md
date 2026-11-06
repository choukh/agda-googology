# 第十六轮的否定 (一): 第 $0$ 层累计为空时, `nκ` 在第 $0$ 层目标上的读数为零, 而节点不为零

> 不读记号. 入口 [NegSR16](NegSR16.lagda.md). 本文只用折叠 (`HtFeedFold`) 与闭项的动作 (`HtFeedClosed`), **不依赖任何接口**: 它算两次运行在第 $0$ 层目标上的值. 接口相关的陈述 (三条新规则的语义) 在 [NegSR16Sem](NegSR16Sem.lagda.md).
>
> 实例 $\Lambda_\kappa=\mathrm{h\Omega}\,(\lambda\_\to 1)$ (合法, `lΛκ`): 它的第一位置只有 $0$, $1$, $\Lambda_\kappa$ 三层; $\Omega_{\Lambda_\kappa}$ 的 `nκ` 的分支是坐标层 $1$ 的节点. 这是含 $\Omega$-极限而层有限的最小例子 (所以 `TX` 对只有有限多种).
>
> 状态 `YN`: 每个目标 (层 $t$) 上读 $\omega\cdot(\Omega_t⨾0)$ (满足 `StrRel14J.NE`), 第 $0$ 层累计 `z` 是 `n0`. **`cvYN`: `cv q YN ≡ YN`** (定义性), 即 `YN` 本身就是换世界之后的状态; `cv` 把 `z` 置为 `n0` (`HtFeedFold.cv` 的字面), 所以任何对 `cv` 封闭 (`Lawcv`) 的状态不变量, 只要非空, 就含 `z = n0` 的状态.
>
> 1. **(定理) `Cells.cellZ`**: 树世界即运行世界 (路径 `self`) 且第 $0$ 格为空时, `nκ` 回灌的**每一格**都为空 (对 $n$ 归纳; 第 $0$ 格在 `z` 字面为 `n0` 或 `n0 ⨾ n0` 时定义性地为空).
> 2. **(定理) `¬NK`**: 层 $1$ 的节点 `xN` (坐标层 $0$, 分支 `n1`) 与层 $\Lambda_\kappa$ 的 `xK` (即 $\Omega_{\Lambda_\kappa}$ 去掉开头的 `n1`), 同一世界 $0$, 路径 `self`, 动作 `Act`, 上下文 `n0`, 状态 `YN`: 第 $0$ 层目标上左边的和 $\ge 1$ (`lowN`), 右边的和 $\le 0$ (`upK`). 原因: 节点在第 $0$ 层目标上上升, 链从状态的**差** `d` 在坐标层上的读数起 (非空); `nκ` 在第 $0$ 层目标上回灌, 走的是从树世界到 "运行世界 + 第 $0$ 层累计 `z`" 的格, `z` 为空时一格也没有.
> 3. **(定理) `¬NK₂`**: 同一对, 但两边都带开头的 `n1` (即 `Ωd 1` 对 `Ωd Λκ`, 第三条新规则本来要关联的那一对), 动作换成 `Az`: 第 $0$ 层累计字面为 `n0` 时输出零, 否则输出 `Step`. 左边 $\ge 1$, 右边 $\le 0$. 开头的 `n1` 在 `Az` 下不给累计加东西 (`n0 ⨾ n0`), 而节点的链里的状态累计已是 `n0 ⨾ n0`, 字面不是 `n0`, `Az` 给出 `Step`.
>
> **范围.** 两条都是关于具体运行的值的定理, 对任何关系族的推论 (`noRel`, `noRel₂`): 只要关系的第 $0$ 层分量值可靠 (`VS0`, 例如 `StrRel14If.RelX hz hz`, 由 `StrRel14NegNode.vsumX`), 这两对输出就不相关. `Az` 不尊重值 (它区分 `n0` 与 `n0 ⨾ n0`); 第 3 条只说明动作前提若只要求 "输入与状态相关 ⇒ 输出相关" 而不要求尊重值, 带开头 `n1` 的保护也不够 (它要配上 `HAW²` 型的前提才成为否定, 见 `NegSR16Sem`). 不否定: 带开头 `n1` 且动作是 `Act` 的那一对 (那时 `z` 非空, 本文不比较).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR16Kap where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; l≤; ≤-refl; ≤-trans; irr)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel13Val using (pt≤)
open import OCF.Align.StrRel13Later using (nzb; nzb-ok)
open import OCF.Align.HtFeedGrow using (nz≤)
```

## 1 实例与状态

```agda
Λκ : H
Λκ = hΩ (λ _ → hs hz)

lΛκ : LgH Λκ
lΛκ = (λ _ _ → hself) , (λ _ _ → tt)

module P = At Λκ lΛκ
open P using (Tg; tg; τ₀; St; st; Df; df; d; z; yc; Run; Act; Ig; LW; κc; κΔ; Cl; v; lv; wv; ap; av; co; Sv; Walk; cv; _⊕⟨_⟩_)

-- 状态: 每个目标 (层 t) 上读 ω⋅(Ω_t ⨾ 0), 第 0 层累计 n0
YN : ∀ {W} → St W
YN = st (df (λ {t} T → nl (λ _ → Ωd t ⨾ n0))) n0

-- cv 之后还是它自己
cvYN : ∀ {W W′} (q : W ⊲ W′) → cv q (YN {W}) ≡ YN
cvYN q = refl
```

## 2 `z` 为空时, 回灌的每一格都为空

```agda
-- 回灌的格: z = n0, 路径 self 时一切格都空
module Cells {ly W} (ac : AccY ly) (u : ∀ {c} → W ⊲ c → Lg c → D ly c) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W)
             (w : D ly W) (Y : St W) where
  cell : ℕ → Cl W W ly
  cell n = κc ac u C.self lW ll A₀ w Y n

  cellZ : yc (κΔ ac u ll A₀ (cell 0)) (τ₀ (lv (cell 0))) ≡ n0 → ∀ n → yc (κΔ ac u ll A₀ (cell n)) (τ₀ (lv (cell n))) ≡ n0
  cellZ h0 zero = h0
  cellZ h0 (suc n) = subst (λ X → G X ≡ n0) (sym (cellZ h0 n)) refl
    where
    c₀ = cell n
    b = v c₀
    G : (X : D₀ b) → D₀ (sum b X)
    G X = yc (Walk ac u (sum b X) (sum-fst b X) (⊲-tr (ap c₀) (av c₀)) (Lg-sum b X (lv c₀)) C.self (Lg-sum b X (lv c₀))
                 (⊲ᴴ↑ (⊲-tr (wv c₀) (sum-fst b X)) ll) (P.Ig↾ (⊲-tr (wv c₀) (sum-fst b X)) A₀)
                 (nw (sum-fst b X) (co c₀ ⨾ Cut u b (av c₀) (ap c₀) (lv c₀) C.self))
                 (cv (sum-fst b X) (Sv c₀ ⊕⟨ lv c₀ ⟩ κΔ ac u ll A₀ c₀)))
             (τ₀ (Lg-sum b X (lv c₀)))
```

## 3 节点对 `nκ`, 动作 `Act`

```agda
-- 两棵树: 层 1 的节点 (坐标层 0), 层 Λκ 的 nκ (分支是坐标层 1 的节点)
llN : LW (hs hz) azero
llN = hLim {c = azero} C.self hself

xN : D (hs hz) azero
xN = ni (ss hself) (λ _ _ _ → n1)

xK : D Λκ azero
xK = nκ tt (λ {c} _ _ → ni (sL {c = c} C.self hself) (λ _ _ _ → n1))

OutN OutK : D₀ azero
OutN = yc (Run (accL (hs hz)) xN C.self tt llN Act n0 YN) (τ₀ tt)
OutK = yc (Run (accL Λκ) xK C.self tt hself Act n0 YN) (τ₀ tt)

lowN : asuc azero ≤ sum azero OutN
lowN = nz≤ azero (nzb-ok OutN tt)

module CK = Cells (accL Λκ) (λ {c} _ _ → ni (sL {c = c} C.self hself) (λ _ _ _ → n1)) tt hself Act n0 (YN {azero})

upK : sum azero OutK ≤ azero
upK = l≤ (pt≤ azero _ (λ n → cong drp (CK.cellZ refl n)))

¬NK : ¬ (sum azero OutN ≤ sum azero OutK)
¬NK h = irr azero (≤-trans lowN (≤-trans h upK))
```

## 4 带开头 `n1` 的一对, 动作 `Az`

```agda
-- 按第 0 层累计是否字面为 n0 分情形的动作
Az′ : ∀ {W} → D₀ W → St W → Df W
Az′ n0 Y = P.zeroD
Az′ n1 Y = P.Step Y
Az′ (x ⨾ y) Y = P.Step Y
Az′ (nl e) Y = P.Step Y
Az′ (nw p x) Y = P.Step Y

Az : ∀ {ly W} → Ig ly W
Az p lW′ _ Y = Az′ (z Y) Y

OutN₂ OutK₂ : D₀ azero
OutN₂ = yc (Run (accL (hs hz)) (Ωd (hs hz)) C.self tt llN Az n0 YN) (τ₀ tt)
OutK₂ = yc (Run (accL Λκ) (Ωd Λκ) C.self tt hself Az n0 YN) (τ₀ tt)

lowN₂ : asuc azero ≤ sum azero OutN₂
lowN₂ = nz≤ azero (nzb-ok OutN₂ tt)

YZ : St azero
YZ = YN ⊕⟨ tt ⟩ P.zeroD

module CK₂ = Cells (accL Λκ) (λ {c} _ _ → ni (sL {c = c} C.self hself) (λ _ _ _ → n1)) tt hself Az (n0 ⨾ nw C.self n1) YZ

upK₂ : sum azero OutK₂ ≤ azero
upK₂ = l≤ (pt≤ azero _ (λ n → cong drp (CK₂.cellZ refl n)))

¬NK₂ : ¬ (sum azero OutN₂ ≤ sum azero OutK₂)
¬NK₂ h = irr azero (≤-trans lowN₂ (≤-trans h upK₂))
```

## 5 推论: 第 $0$ 层值可靠的关系族都不能关联这两对输出

```agda
RelT2 : Set₁
RelT2 = ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set

VS0 : RelT2 → Set
VS0 R = ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → R hz hz lV lV′ x x′ → sum azero x ≤ sum azero x′

noRel : ∀ R → VS0 R → ¬ R hz hz tt tt OutN OutK
noRel R vs h = ¬NK (vs h)

noRel₂ : ∀ R → VS0 R → ¬ R hz hz tt tt OutN₂ OutK₂
noRel₂ R vs h = ¬NK₂ (vs h)
```
