# $X_2$: 带底的 `lΩ` 层号的折叠, 接口

> 不含记号. 入口 [X2](X2.lagda.md). 构造一路 X2, 否定一路 NegX2 共用. 只读导入 [X1UpIf](X1UpIf.lagda.md) (与 [X1UpFold](X1UpFold.lagda.md) 的叠层 `LS`, 路径 `PHU`) 并只增. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> **这一篇做什么.** [X1Up](X1Up.lagda.md) 有了底 $X_1$ 上的可数叠层 $X_1\oplus m$ 与它的上层折叠 `ΦU` (底种类一律留, 新种类按叠层层号比较, 公共上界是 $m$), 输出带路径 (`PH-ΦU`). 下一站 $X_2=$ `lΩ lz (λ c → ls (ofU c))` (共尾度 $\Omega_1$, 分支 $c$ 是第 $X_1\oplus c$ 层之上一层) 是一个 `lΩ` 层号, 它的种类分两类:
>
> - **低种类** (`lo`): 读回层在 $X_1$ 之下或就是 $\Omega_1$ 的种类. 每个低种类是底 $X_1$ 的某个种类 $\kappa_0$ 的**视图**: 带 $\kappa_0$ 相对世界的证据 (`PathOutIf.Ev`), 与坐标的读入 `to : E XS κ₀ → E XS₂ κ`. 折叠对它照 `PathOutFold.Ψ` 做 (决定 `PathOutIf.dec`, 回灌 `shift`, 世界 `nxt`), 只是分支取在 `to` 之后.
> - **高种类** (`up`): 读回层是叠层 $X_1\oplus i$ 的种类. 带**字面证据** $i\sqsubset\mathrm{lvW}\,W$ (叠层层号在世界的界之下). 对 $X_1$ 之下的目标它一律 "在上": 先在第 $X_1\oplus i$ 层坍缩 (链从地板 `topU i` 起, 分支用 `ΦU` 从第 $X_1\oplus\mathrm{lvW}\,W$ 层折到第 $X_1\oplus i$ 层), 再用 **带底的可数折叠** (`X2Fold.ΦB` $=$ `Ψ ∘ ΦX`, 经底 $X_1$ 折到目标) 折下去.
>
> 高种类的分支要整个换成第 $X_1\oplus\mathrm{lvW}\,W$ 层的值才能交给 `ΦU`: 本接口给**逐种类**的换法 (`CvK`, `cvK`, `cvE`), 高度上的换法 `X2Fold.cv` 由它逐构造子搭出 (不是任意函数).
>
> **律带字面公共上界.** 低种类的决定是 `PathOutIf.dec`, 两个下标 (目标, 种类) 都带相对同一世界的证据 (继承). 高种类不与 $X_1$ 之下的目标比较 (一律在上), 它与叠层目标的比较在 `ΦU` 里, 公共上界是 $\mathrm{lvW}\,W$, 字面证据是 `up` 的 $i\sqsubset\mathrm{lvW}\,W$ 与 `cvK` 落在 `LS (lvW W)` 里; $\mathrm{lvW}\,W$ 合法 (`lgW`). 没有对裸下标的比较律.
>
> **关于推广 `TySupIf` (接手清单第 1 条).** `TySupIf` 的 `noK` 要求最低层无种类, 所以底 $X_1$ 上的叠层不是它的实例. 本接口不改 `TySupIf`: 叠层上的可数折叠就是 `X1UpFold.ΦU` (对一切 `X1UpIf`, 底种类一律留, 已无 `noK`); 新增的是从叠层**越过底**折到 $X_1$ 之下的目标 (`X2Fold.ΦB`), 它要输入带路径, 路径由 `PH-ΦU` 给出. `lΩ` 层号的折叠 (`X2Fold.Ψ₂`) 在 "在上" 之后调用 `ΦU` 与 `ΦB`.
>
> **接口定稿 2026-11-06 00:16 (首次编译通过).** 定稿后只增不改. 折叠 `X2Fold` 00:19 对它编译通过.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.X2If where

open import OCF.Align.HtTowerTy using (KS; K; E; HB; LgB)
open import OCF.Align.TySupC using (Cd; _⊏ᶜ_)
open import OCF.Align.PathOutIf using (module PathOutIf)
open import OCF.Align.X1UpIf
import OCF.Align.X1UpFold as UF
```

## §1 种类的两类

`ClX U Y lvW W κ`: 种类结构 `Y` 的种类 $\kappa$ 在世界 $W$ 里, 是底的种类 $\kappa_0$ 的视图 (带证据, 带坐标读入), 或是叠层 $X_1\oplus i$ 的种类 ($i$ 在世界的界 $\mathrm{lvW}\,W$ 之下, 坐标是第 $X_1\oplus i$ 层的值).

```agda
module _ (U : X1UpIf) where
  open X1UpIf U using (P)
  open PathOutIf P using (XS; Wo; Ev)

  data ClX (Y : KS) (lvW : Wo → Cd) (W : Wo) (κ : K Y) : Set where
    lo : (κ₀ : K XS) → Ev W κ₀ → (E XS κ₀ → E Y κ) → ClX Y lvW W κ
    up : (i : Cd) → i ⊏ᶜ lvW W → (HB (UF.LS U i) → E Y κ) → ClX Y lvW W κ
```

## §2 记录

```agda
record X2If : Set₁ where
  field
    U : X1UpIf
  open X1UpIf U using (P)
  open PathOutIf P using (Wo; LgWo)
  field
    XS₂ : KS
    -- 世界的界, 作叠层层号; 合法世界给合法层号
    lvW : Wo → Cd
    lgW : ∀ {W} → LgWo W → LgB (lvW W)
    -- 种类的证据与分类
    Ev₂ : Wo → K XS₂ → Set
    cls : ∀ W κ → Ev₂ W κ → ClX U XS₂ lvW W κ
    -- 逐种类换到第 X₁ ⊕ lvW W 层
    CvK : Wo → K XS₂ → Set
    cvK : ∀ W κ → CvK W κ → K (UF.LS U (lvW W))
    cvE : ∀ W κ (k : CvK W κ) → E (UF.LS U (lvW W)) (cvK W κ k) → E XS₂ κ
```
