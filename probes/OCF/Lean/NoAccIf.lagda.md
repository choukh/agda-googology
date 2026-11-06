# NoAcc: 接口 (不累加的世界移动与折叠的契约)

> 不含记号. 构造一路 NoAcc, 否定一路 NegNoAcc 共用. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 [CRwBase](CRwBase.lagda.md) (种类结构, 高度, 第一位置 `⊲`, 合法 `LgB`, `⊞`).
>
> **接口定稿 2026-11-06 01:40 (首次编译通过).** 定稿后只增不改.
>
> **这一篇做什么.** 作者本轮 (原话) "去累加: 证书读输入合法". [CRw](CRw.lagda.md) 的世界移动 ([CRwIf](CRwIf.lagda.md)) 里, 回灌 `sh₀ B c = B ⊞ leg c` 用部分和 `leg` 把任意坐标变成合法坐标, 所以 `adm-sh` 对一切坐标成立, 证书可以不读输入. 本接口把这一条换成**读输入合法**: 回灌对一切坐标可入 (`adm-sh`), 但新世界合法只在坐标合法时成立 (`lg-sh`, `lg-nx` 多一个 `LgB c` / `LgB e` 前提), 并要求回灌对坐标保第一位置 (`sh-⊲`). 实例: `sh₀ B c = B ⊞ c` (不累加).
>
> 第二个记录 `PtFold` 是 "逐点的折叠, 证书读输入合法" 的契约 (对一个固定的折叠 $F$, 目标是可数树 `Cd`): ℕ-极限子句逐点 (`F-pt`), 单调 (`F-mono`), 保合法 (`F-lg`). 世界只取与折叠相容的 (`Cw`), 至少有一个 (`cw-ex`, 前提可满足).
>
> **律的定义域.** 律里出现的下标对: `nx-up` 的 $(B, \mathrm{nxt}_0\,B\,e\,a)$, `adm↓` 的 $(B, B')$ 带字面 $B\lhd B'$, `sh-⊲` 的 $(c, c')$ 带字面 $c\lhd c'$ (公共上界 $c'$), `F-mono` 的 $(a, b)$ 带字面 $a\lhd b$ (公共上界 $b$, 且 $b$ 合法). **没有裸下标的比较律.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NoAccIf where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase

record NoAccIf : Set₁ where
  field
    Adm₀   : Cd → Cd → Set
    nxt₀   : (B e : Cd) → Adm₀ B e → Cd
    sh₀    : Cd → Cd → Cd
    adm-sh : ∀ B c → Adm₀ B (sh₀ B c)
    lg-sh  : ∀ {B c} → LgB B → LgB c → LgB (sh₀ B c)
    sh-⊲   : ∀ B {c c′} → c ⊲ c′ → sh₀ B c ⊲ sh₀ B c′
    nx-up  : ∀ {B e} (a : Adm₀ B e) → B ⊲ nxt₀ B e a
    lg-nx  : ∀ {B e} (a : Adm₀ B e) → LgB B → LgB e → LgB (nxt₀ B e a)
    adm↓   : ∀ {B B′} → B ⊲ B′ → ∀ {e} (a′ : Adm₀ B′ e) →
             Σ (Adm₀ B e) (λ a → nxt₀ B e a ⊲ nxt₀ B′ e a′)

record PtFold (S : KS) : Set₁ where
  field
    F      : HB S → Cd
    Cw     : Wd S → Set
    cw-lg  : ∀ {w} → Cw w → LgW S w
    cw-ex  : Σ (Wd S) Cw
    F-pt   : ∀ f → F (hl f) ≡ hl (λ n → F (f n))
    F-mono : ∀ {w a b} → Cw w → LgB b → a ⊲[ w ] b → F a ⊲ F b
    F-lg   : ∀ h → LgB h → LgB (F h)
```
