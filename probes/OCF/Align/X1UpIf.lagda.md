# 在 $X_1$ 上叠层: 接口

> 不含记号. 入口 [X1Up](X1Up.lagda.md). 构造一路 X1Up, 否定一路 NegX1Up 共用. 只读导入 [PathOutIf](PathOutIf.lagda.md) 并只增. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> **这一篇做什么.** [PathOut](PathOut.lagda.md) 把 $X_1$ 层的值折到第 0 层 (`PathOutFold.Ψ`), 输入要带路径 (`PathOutFold.PH`). 在 $X_1$ 上叠可数层号 $m$ (层 $X_1\oplus m$) 后, 要一个**上层折叠**把第 $X_1\oplus m$ 层的值折到第 $X_1$ 层, 输出再交给 `Ψ`. 上层折叠的输出要带路径. 本接口把这件事要的东西写成记录, 都是对 `PathOutIf` 的世界与证据的**增补律**:
>
> - **世界的序** `_≼_` (实例: 界的字面第一位置 $B\lhd B'$), 自反, 传递.
> - **证据随世界变大** `ev↑`; **可入随世界变小** `adm↓`, 且进入后的世界仍有序 (`nxt` 单调); **进入不缩小世界** `≼-nxt`. 这三条让 "带路径" 对世界单调 (`X1UpFold.PH-mono`): 上层折叠把当前界传进留下的 $\Omega_1$ 结点的分支 (分支的世界是 `nxt`), 界的路径要搬过去.
> - **底层的地板** `topX` (实例: `PathOut.topL`, 读法 $\Omega_{\Omega_1}$), 合法 `Lg-topX`, 对一切世界带路径 `PH-topX`. 上层折叠在目标 $X_1$ 上 "同层" 坍缩时, 链从地板起步 (否定一路的提醒: 从 $0$ 起步则链里没有 $\Omega$-结点).
>
> **律带字面公共上界.** 律里成对出现的下标只有两个世界 $W, W'$, 都带字面证据 `W ≼ W′` (实例是 $B\lhd B'$). 上层折叠的留/坍缩比较的是种类的层号与目标层号, 两者都是叠层层号 $m$ 的字面第一位置, 公共上界是 $m$ (`TySupC` 的 `cmpB` 形状), 不进接口. 没有对裸下标的比较律.
>
> **带路径的结构 `PS`** (§1) 是 `PathOutIf` 的 (`Ev`, `Adm`, `nxt`) 加上同样三条律, 对任一种类结构; `PHg` 是对它的 "带路径的高度" (与 `PathOutFold.PH` 同式). 上层 $X_1\oplus m$ 的结构由它逐层搭出 (`X1UpFold.PSL`): 旧种类原样, 新种类的分支只对 "在更大的世界里带路径" 的坐标要求带路径 (Kripke 式, 这样 `adm↓` 对新种类成立).
>
> **关于 `constShiftOf`** (`NegPathOutIf`): 上层折叠不经 `shift`, 本接口不补 `shift` 的律. 判断: 实例的 `shift` ($B\boxplus\mathrm{leg}\,c$) 对坐标的字面第一位置不单调 (`leg` 取部分和), 所以 "shift 单调" 一类的律实例满足不了; 未编译反例, 只是判断.
>
> **接口定稿 2026-11-05 23:45 (首次编译通过).** 定稿后只增不改.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.X1UpIf where

open import Data.Unit using (⊤)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Align.HtTowerTy using (KS; K; E; HB; hz; hs; hl; hΩ; LgB)
open import OCF.Align.PathOutIf using (PathOutIf; module PathOutIf)
import OCF.Align.PathOutFold as PF
```

## §1 带路径的结构

对世界类型 `Wo` 与它的序 `_≼_`, 种类结构 `T` 上的路径结构: 证据, 可入, 进入后的世界, 三条律.

```agda
record PS {Wo : Set} (_≼_ : Wo → Wo → Set) (T : KS) : Set₁ where
  field
    Ev   : Wo → K T → Set
    Adm  : (W : Wo) (κ : K T) → E T κ → Set
    nxt  : (W : Wo) (κ : K T) → Ev W κ → (e : E T κ) → Adm W κ e → Wo
    ev↑  : ∀ {W W′} → W ≼ W′ → ∀ {κ} → Ev W κ → Ev W′ κ
    adm↓ : ∀ {W W′} (q : W ≼ W′) {κ} (ev : Ev W κ) {e} (a′ : Adm W′ κ e) →
           Σ (Adm W κ e) (λ a → nxt W κ ev e a ≼ nxt W′ κ (ev↑ q ev) e a′)
    ≼nx  : ∀ {W κ} (ev : Ev W κ) e (a : Adm W κ e) → W ≼ nxt W κ ev e a

module _ {Wo : Set} {_≼_ : Wo → Wo → Set} {T : KS} (Q : PS _≼_ T) where
  open PS Q
  PHg : Wo → HB T → Set
  PHg W hz = ⊤
  PHg W (hs h) = PHg W h
  PHg W (hl f) = ∀ n → PHg W (f n)
  PHg W (hΩ κ g) = Σ (Ev W κ) (λ ev → ∀ e (a : Adm W κ e) → PHg (nxt W κ ev e a) (g e))
```

## §2 记录

```agda
record X1UpIf : Set₁ where
  field
    P : PathOutIf
  open PathOutIf P
  field
    _≼_   : Wo → Wo → Set
    ≼-rf  : ∀ {W} → W ≼ W
    ≼-tr  : ∀ {U V W} → U ≼ V → V ≼ W → U ≼ W
    ev↑   : ∀ {W W′} → W ≼ W′ → ∀ {κ} → Ev W κ → Ev W′ κ
    adm↓  : ∀ {W W′} (q : W ≼ W′) {κ} (ev : Ev W κ) {e} (a′ : Adm W′ κ e) →
            Σ (Adm W κ e) (λ a → nxt W κ ev e a ≼ nxt W′ κ (ev↑ q ev) e a′)
    ≼-nxt : ∀ {W κ} (ev : Ev W κ) e (a : Adm W κ e) → W ≼ nxt W κ ev e a
    topX    : HB XS
    Lg-topX : LgB topX
    PH-topX : ∀ W → PF.PH P W topX
```
