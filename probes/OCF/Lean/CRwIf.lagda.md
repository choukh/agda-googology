# CRw: 接口 (世界的移动)

> 不含记号. 入口 [CRw](CRw.lagda.md). 构造一路 CRw, 否定一路 NegCRw 共用. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 [CRwBase](CRwBase.lagda.md).
>
> **接口定稿 2026-11-06 00:49 (首次编译通过).** 定稿后只增不改.
>
> **这一篇做什么.** 重写后的折叠 ([CRwFold](CRwFold.lagda.md)) 只有一份定义, 对层号递归; 层号有两类: 可数层号 `cn c` 与 "$\Omega_1$ 上叠可数层号" `xu m` (`xu hz` 是 $\Omega_1$ 这一层号, 即 PathOut 的 $X_1$). 折叠里的一切比较都是 `cmpB` (同一棵合法树的两个第一位置可比), 字面公共上界是:
>
> - 目标与种类同类 (`cn`/`cn` 或 `xu`/`xu`): 被折的层号本身 (可数树 $c$ 或 $m$);
> - 目标是可数层号而被折的是 `xu m`: **世界的界** $B$ (一棵合法的可数树). 目标带 $t\lhd B$, 种类 (第 $c+1$ 层以下的种类) 带 $c+1\lhd B$; 两者都是 $B$ 的第一位置.
>
> 这些都是折叠的定义, 不是接口的律. 接口只管**世界的移动**: 折叠进入 $\Omega_1$ 种类 (坐标是可数树) 的分支时, 坐标 $e$ 要 "可入" (`Adm₀ B e`), 进入后世界换成 `nxt₀ B e a`; 输出里留下或坍缩的 $\Omega_1$ 结点在任意坐标 $c$ 处的分支, 取输入在 `sh₀ B c` 处的分支 (回灌). 律:
>
> - `adm-sh`: 回灌的坐标可入 (世界合法时);
> - `nx-up`: 进入不缩小世界, 带字面证据 $B\lhd$ `nxt₀ B e a` (目标的证据 $t\lhd B$ 由它搬到新世界);
> - `lg-nx`: 进入保世界合法;
> - `adm↓`: 可入随世界变小, 进入后的世界有序. 律里成对的两个世界 $B, B'$ 都带字面证据 $B\lhd B'$.
>
> **没有对裸下标的比较律.** 律里出现的下标对只有 $(B, B')$ 与 $(B, \mathrm{nxt}_0\,B\,e\,a)$, 都带字面 $\lhd$ 证据.
>
> 实例 (`CRw.I₁`, 同 PathOut): `Adm₀ B e` $= B\lhd e\times$ `LgB e`, `nxt₀ B e a` $= e+1$, `sh₀ B c` $= B\boxplus\mathrm{leg}\,c$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CRwIf where

open import Data.Product using (Σ)
open import OCF.Lean.CRwBase

record CRwIf : Set₁ where
  field
    Adm₀   : Cd → Cd → Set
    nxt₀   : (B e : Cd) → Adm₀ B e → Cd
    sh₀    : Cd → Cd → Cd
    adm-sh : ∀ {B} c → LgB B → Adm₀ B (sh₀ B c)
    nx-up  : ∀ {B e} (a : Adm₀ B e) → B ⊲ nxt₀ B e a
    lg-nx  : ∀ {B e} (a : Adm₀ B e) → LgB B → LgB (nxt₀ B e a)
    adm↓   : ∀ {B B′} → B ⊲ B′ → ∀ {e} (a′ : Adm₀ B′ e) →
             Σ (Adm₀ B e) (λ a → nxt₀ B e a ⊲ nxt₀ B′ e a′)
```
