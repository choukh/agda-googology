# X₁ 上叠层, 否定一路 (六): 接口的盲区与边界

> 不含记号. 入口 [NegX1Up](NegX1Up.lagda.md). 对着接口 [X1UpIf](X1UpIf.lagda.md) ("接口定稿 2026-11-05 23:45 (首次编译通过)") 写, 只读导入, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **接口的内容 (读自 `X1UpIf`).** 对 `PathOutIf` 的增补: 世界的序 `_≼_` (自反, 传递), 证据随世界变大 `ev↑`, 可入随世界变小 `adm↓`, 进入不缩小世界 `≼-nxt`; 底层地板 `topX`, 合法 `Lg-topX`, 对一切世界带路径 `PH-topX`. 接口文首说: 上层折叠在目标 $X_1$ 上同层坍缩时链从 `topX` 起步 (回应 [NegX1UpFlat](NegX1UpFlat.lagda.md)).
>
> **结果.**
>
> 1. **`noΩ→PH` (定理, 对一切 `PathOutIf`).** 不含 $\Omega$-结点的树对一切世界带路径.
> 2. **`flatTopOf`, `hzTopOf` (构造, 盲; 对一切实例).** 把 `topX` 换成任一不含结点的合法树 (例如 $0$), 其余字段不动, 仍是实例 (`Lg-topX` 由所给, `PH-topX` 由 1). 所以接口**不保证**地板含 $\Omega$-结点: "链从 `topX` 起步" 这条防塌缩的安排在接口里没有律撑着; 与 `NegX1UpFlat.same-noΩ` 合起来, 链从 `hzTopOf` 的地板起步时同层一步的输出不含结点 (对构造一路的折叠, 要它的文件; 见 [NegX1UpInst](NegX1UpInst.lagda.md) 若已写). 建议增补的律 (判断): `topX` 的根是某个种类的结点, 或 `topX` 对每个种类 $\kappa$ 都有分支经过 $\kappa$.
> 3. **`voidX1` (构造, 盲).** 以 `NegPathOutIf.voidIf` (证据恒空) 为 `P`, 序取 $\top$, 地板取 $0$: 接口的全部律成立. 接口的律不要求任何种类带证据.
> 4. **`cJ`, `no-world-cJ`, `kripke-cJ`, `¬Lg-Bj` (定理, 边界; 对 PathOut 的实例 `IX₁`).** 合法的 $X_1$ 层值 `cJ` (根部两个种类, 坐标 $\lim\mathrm{od}$ 与 $\lim\mathrm{ev}$) 在**任何合法世界**里都不带路径 (由 `HtTowerNeg.no-joinᴮ`); 但在一个不合法的世界 `Bj W` 里带路径, 且 `W ⊲ Bj W` 对一切 $W$ (`kripke-cJ`). 构造一路告知的设计 (新种类的可入 `Adm W c = Σ W′ (W ≼ W′ × PHg W′ c)`, 进入后世界换成 $W'$) 若不要求 $W'$ 合法, `cJ` 对一切世界可入, 进入后的世界不合法; 若要求合法, `cJ` 对一切世界不可入. 二者择一 (判断: 前者让 `lg-nxt` 一类的律在新种类上不成立, 后者让新种类的分支在 `cJ` 一类坐标上不受 `PH` 约束).
>
> **前提实例.** 1: 任一 `P`. 2: 任一实例, 树 $0$ (`NoΩ`, `LgB` 都是 `tt`). 3: 无前提. 4: `cJ` 合法 (`Lg-cJ`); 世界 `Bj W` 对一切 $W$.
>
> **只否定什么.** 2, 3 只否定 "接口的律保证地板有结点 / 保证有证据". 4 只否定 "合法的 $X_1$ 层值都能在某个合法世界里带路径". **不否定**: 接口; 构造一路的实例 (实例的 `topX` 是 `topL`, 根是 $\Omega_1$-结点; 正面的检查见实例篇); 增补律. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX1UpIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupC using (Cd)
open import OCF.Align.PathOutIf using (PathOutIf; module PathOutIf)
import OCF.Align.PathOutFold as PF
open import OCF.Align.PathOutX1 using (IX₁; XS₁)
open import OCF.Align.X1UpIf
open import OCF.Align.NegPathOutIf using (voidIf)
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ; no-joinᴮ)
open import OCF.Align.NegX1UpFlat using (NoΩ)
```

## §1 不含结点的树带路径

```agda
noΩ→PH : ∀ (P : PathOutIf) W (h : HB (PathOutIf.XS P)) → NoΩ h → PF.PH P W h
noΩ→PH P W hz n = tt
noΩ→PH P W (hs h) n = noΩ→PH P W h n
noΩ→PH P W (hl f) n = λ m → noΩ→PH P W (f m) (n m)
noΩ→PH P W (hΩ _ _) ()
```

## §2 盲: 地板可以不含结点

```agda
flatTopOf : (I : X1UpIf) (t : HB (PathOutIf.XS (X1UpIf.P I))) → NoΩ t → LgB t → X1UpIf
flatTopOf I t nt lt = record
  { P = P ; _≼_ = _≼_ ; ≼-rf = ≼-rf ; ≼-tr = ≼-tr ; ev↑ = ev↑ ; adm↓ = adm↓ ; ≼-nxt = ≼-nxt
  ; topX = t ; Lg-topX = lt ; PH-topX = λ W → noΩ→PH P W t nt }
  where open X1UpIf I

hzTopOf : X1UpIf → X1UpIf
hzTopOf I = flatTopOf I hz tt tt

top-hz : ∀ I → X1UpIf.topX (hzTopOf I) ≡ hz
top-hz I = refl
```

## §3 盲: 证据恒空的实例

```agda
voidX1 : X1UpIf
voidX1 = record
  { P = voidIf ; _≼_ = λ _ _ → ⊤ ; ≼-rf = tt ; ≼-tr = λ _ _ → tt
  ; ev↑ = λ q ev → ev
  ; adm↓ = λ q ev a′ → ⊥-elim ev
  ; ≼-nxt = λ ev e a → tt
  ; topX = hz ; Lg-topX = tt ; PH-topX = λ W → tt }

void-noEv : ∀ W κ → ¬ PathOutIf.Ev (X1UpIf.P voidX1) W κ
void-noEv W κ ()
```

## §4 边界: 合法的值, 合法世界里不带路径

```agda
open PF IX₁ using (PH)

nd : Cd → HB XS₁
nd y = hΩ (inj₂ y , inj₂ tt) (λ _ → hz)

cJ : HB XS₁
cJ = hΩ (inj₂ (hl odᴴ) , inj₂ tt) (λ _ → nd (hl evᴴ))

Lg-cJ : LgB cJ
Lg-cJ = (λ _ _ _ _ → hself) , (λ _ _ → (λ _ _ _ _ → hself) , (λ _ _ → tt))

no-world-cJ : ∀ B → LgB B → ¬ PH B cJ
no-world-cJ B lB (od , k) with k hz tt
... | (ev , _) = no-joinᴮ {S⊥} {tt} tt (B , lB , ⊲ᴮ-tr (hsuc hself) ev , ⊲ᴮ-tr (hsuc hself) od)

-- 不合法的世界: 依次列出两个坐标的后继与 W
Bj : Cd → Cd
Bj W = hl j
  where
  j : ℕ → Cd
  j zero = hs (hl odᴴ)
  j (suc zero) = hs (hl evᴴ)
  j (suc (suc _)) = W

PH-Bj : ∀ W → PH (Bj W) cJ
PH-Bj W = hlim 0 hself , (λ _ _ → hlim 1 hself , (λ _ _ → tt))

kripke-cJ : ∀ W → Σ Cd (λ W′ → (W ⊲[ tt ] W′) × PH W′ cJ)
kripke-cJ W = Bj W , hlim 2 hself , PH-Bj W

¬Lg-Bj : ∀ W → ¬ LgB (Bj W)
¬Lg-Bj W l = no-world-cJ (Bj W) l (PH-Bj W)
```

## 结论 (按档)

- **[定理]** **`noΩ→PH`** (对一切 `P`); `top-hz`; `void-noEv`; `nd`, `cJ`, **`Lg-cJ`**, **`no-world-cJ`**, `Bj`, `PH-Bj`, **`kripke-cJ`**, **`¬Lg-Bj`**.
- **[构造, 盲]** **`flatTopOf`**, **`hzTopOf`** (对一切实例); **`voidX1`**.
- **[判断]** 建议增补的律 (`topX` 有结点); 4 的二者择一的后果.
