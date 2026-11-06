# CRw 上底做成递归, 否定一路 (二): 接口 `RecBIf` 的盲区与范围

> 不含记号. 入口 [NegRecB](NegRecB.lagda.md). 只读导入构造一路的接口 [RecBIf](RecBIf.lagda.md) ("接口定稿 2026-11-06 01:53", 首次编译 01:48) 与 [CRwBase](CRwBase.lagda.md), 以及 NegCRw 的 [NegCRwIf](NegCRwIf.lagda.md) (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **接口.** `RecBIf` 有四个字段: `mv : CRwIf` (塔的每一层世界的移动, 即 CRw 的 7 个字段), 初始世界 `W₀ : Cd`, 证据 `o₀ : 1 ⊲ W₀`, `lW₀ : LgB W₀`. 文件头的设计 (构造一路的计划, 不是律): 层号是 $(n, m)$, $n:\mathbb N$ 是底的序号, $m$ 是可数高度, 读 $\Omega\cdot n+m$; 第 $n+1$ 个底是 $\sup_c$ `Tw (bS n) (hs c)`.
>
> **结果 (都对一切实例).**
>
> 1. **盲 (`mvOf`, `constShB`, `stayB`, `trivB`).** 把 `mv` 换成任一 `CRwIf` 仍是实例. 所以 `NegCRwIf` 的三条盲区原样落到本接口: 回灌与坐标无关 (`constShB`), 进入后世界不动 (`stayB`), 平凡移动 (`trivB`) 都是实例. 对实例 `CRw.I₁` 的后果已在 `NegCRwInst` 编译过: `stayOf I₁` 里 $\Omega_1$ 层的地板不带路径 (`stay-no-PH`), `constShOf I₁` 里同一闭项公式也有 `LgB` 证书且闭项不同 (`blind-TX`). 本接口没有新增排除它们的律.
> 2. **初始世界不定 (`W₀-free`, `w2B`, `wωB`).** 任一合法且 $1\lhd W$ 的 $W$ 都可作 `W₀`: 例如 $2$ 与 $\omega$. 接口不说初始世界是 $1$; 边界: `W₀` 不能是 $0$ (`W₀≢0`, 由 `o₀`).
> 3. **范围 (`worlds-are-Cd`, 读类型).** 接口里每一层的世界、界、坐标都是 `Cd` (只有 $0$, 后继, ℕ-极限的布劳威尔树): `mv` 的 `Adm₀`, `nxt₀`, `sh₀` 的类型是 `Cd → Cd → …`. 所以在这个接口下, 跨底比较的公共上界永远在第 0 层, `NegRecBPre` 的 `wdep-top`, `wdep-low`, `bound-wdep` (第 $k\geq1$ 层的现象) **不会**在这里出现; 反过来, 共尾度 $\Omega_2$ 及以上的层号 (坐标是第 1 层的值) 不在这个接口能描述的世界里. 定理 `worlds-are-Cd` 只是把类型写出来 (refl 级), 范围的结论是读类型.
>
> **前提实例.** 1: `CRw.I₁` (构造一路的实例 `J₁` 用的就是它); 2: `w2B`, `wωB` 的证据与合法都写出; `trivB` 的 `W₀` 取 $1$.
>
> **只否定什么.** 1, 2 不否定接口, 只说律不约束: 回灌依赖坐标, 进入后世界盖住坐标, 初始世界是 $1$. 3 不是否定定理, 是读类型: 本接口的世界是第 0 层的树. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegRecBIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.RecBIf
open import OCF.Lean.NegCRwIf using (constShOf; stayOf; trivIf)
open import OCF.Lean.CRw using (I₁)
```

## §1 换掉世界的移动仍是实例

```agda
mvOf : RecBIf → CRwIf → RecBIf
mvOf J I = record { mv = I ; W₀ = RecBIf.W₀ J ; o₀ = RecBIf.o₀ J ; lW₀ = RecBIf.lW₀ J }

J₁′ : RecBIf
J₁′ = record { mv = I₁ ; W₀ = hs hz ; o₀ = hself ; lW₀ = tt }

constShB stayB : RecBIf → RecBIf
constShB J = mvOf J (constShOf (RecBIf.mv J))
stayB J = mvOf J (stayOf (RecBIf.mv J))

trivB : RecBIf
trivB = record { mv = trivIf ; W₀ = hs hz ; o₀ = hself ; lW₀ = tt }

-- 回灌与坐标无关 (refl), 进入后世界不动 (refl)
constShB-const : ∀ J B c c′ → CRwIf.sh₀ (RecBIf.mv (constShB J)) B c ≡ CRwIf.sh₀ (RecBIf.mv (constShB J)) B c′
constShB-const J B c c′ = refl

stayB-stay : ∀ J B e a → CRwIf.nxt₀ (RecBIf.mv (stayB J)) B e a ≡ B
stayB-stay J B e a = refl
```

## §2 初始世界不定

```agda
W₀-free : ∀ (J : RecBIf) (W : Cd) → hs hz ⊲ W → LgB W → RecBIf
W₀-free J W o l = record { mv = RecBIf.mv J ; W₀ = W ; o₀ = o ; lW₀ = l }

two : Cd
two = hs (hs hz)

w2B : RecBIf
w2B = W₀-free J₁′ two (hsuc hself) tt

nat : ℕ → Cd
nat zero = hz
nat (suc n) = hs (nat n)

ω : Cd
ω = hl nat

Lg-ω : LgB ω
Lg-ω = (λ n → hsuc hself) , go
  where
  go : ∀ n → LgB (nat n)
  go zero = tt
  go (suc n) = go n

wωB : RecBIf
wωB = W₀-free J₁′ ω (hlim 1 hself) Lg-ω

W₀-is : RecBIf.W₀ w2B ≡ two × RecBIf.W₀ wωB ≡ ω
W₀-is = refl , refl

W₀≢0 : ∀ (J : RecBIf) → ¬ (RecBIf.W₀ J ≡ hz)
W₀≢0 J e = no (subst (λ z → hs hz ⊲ z) e (RecBIf.o₀ J))
  where
  no : ¬ (hs hz ⊲ hz)
  no ()
```

## §3 范围: 每一层的世界都是 `Cd`

把字段的类型写出来 (refl 级). 世界、坐标、回灌都在 `Cd` 里, 所以跨底比较的公共上界是第 0 层的树.

```agda
worlds-are-Cd : ∀ (J : RecBIf) →
  (CRwIf.Adm₀ (RecBIf.mv J) ≡ CRwIf.Adm₀ (RecBIf.mv J)) ×
  ((B e : Cd) (a : CRwIf.Adm₀ (RecBIf.mv J) B e) → Cd) × (Cd → Cd → Cd)
worlds-are-Cd J = refl , CRwIf.nxt₀ (RecBIf.mv J) , CRwIf.sh₀ (RecBIf.mv J)
```

## 结论 (按档)

- **[定理]** `mvOf`, `constShB`, `stayB`, `trivB`, `constShB-const`, `stayB-stay` (盲, 对一切实例); `W₀-free`, `w2B`, `wωB`, `W₀-is`, `W₀≢0`.
- **[读类型]** `worlds-are-Cd`: 世界是第 0 层的树.
- **[判断]** 本接口能描述的层号只到 $\Omega\cdot n+m$ (文件头的设计); 共尾度 $\Omega_2$ 的层号要以第 1 层的值作世界的界, 不在这个接口里. 对构造一路的层号与折叠的定理在 [NegRecBInst](NegRecBInst.lagda.md).
