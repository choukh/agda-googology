# RR4 实验 (五): 原块上 $\hat\Omega\,2$ 满足 `Reg`, 含一切合法守卫坐标 (退化的也在内)

> 第四次路线审查 (`probes/Survey/RR4-Fable52.md`) 的实验文件, 不进成品. 在**原** `LevelFixCore`/`LevelFixVal` 块上, 用第十轮冻结的 `YiRegBase.Reg`, 不改任何已有定义. 导入闭包不含记号.
>
> **要检验的问题.** 第十轮否定了 `Reg` 对一切合法树的 $\hat\Omega$ 保持 (`no-omega-preservation`), 第十一轮起转向严格化 (Reg₂, D7). 仓库里 `Reg` 的闭实例只到 $\hat\Omega\,1$ (`YiRegInstances.tower2-reg`). 问: 不加任何严格性, 下一个规范层 $\hat\Omega\,2$ 是否 `Reg`? 它的分支域是第 1 层的一切合法守卫坐标, 其中有常值分支的结点这类退化坐标.
>
> **结果.**
>
> 1. **`guarded-reg` (定理).** 第 1 层的任意坐标 $\eta$, 若合法且 `top` 在它的第一位置上 (即过守卫), 则读回 `up 1 η` 满足 `Reg`. 对 $\eta$ 结构递归. 用到的事实:
>    - `top` 之下的值只有 `top` 自己与 `em top₀` (`under-top-reg`);
>    - 极限的各项与 `top` 在公共界下用原块的 `cmpC` 比较 (公共界是极限的某一项, 字面的);
>    - 结点的第一支与各分支都在 `top` 之上, 所以读回里字面地有 $\hat\Omega\,1$, 其第一支就是 1.
> 2. **`Ω₂-reg : Reg (Ω̂ 2)` (定理, 无前提).**
> 3. **`junk-reg` (实例).** 常值分支的坐标 `lc slot raw1 top (λ → top)` 过守卫, 读回满足 `Reg`.
>
> **对照.** 第十一轮 `YiReg2Stop.no-reg₂-Ω₁`: 加了严格性的 `Reg₂` 在 $\hat\Omega\,1$ 上已失败. 不加严格性的 `Reg` 在 $\hat\Omega\,1$, $\hat\Omega\,2$ 上成立.
>
> **读法 (判断).** 派发证据 `Reg` 在规范层的读回域上不需要严格性; 第十轮的反例来自读回域之外 ([RR4CoordRoot](RR4CoordRoot.lagda.md) 的 `x-not-coordinate`). 本文只做到第 1 层坐标. 一般层 (任意 $k$ 的 `Raw k`, 以及 $\hat\Omega(\hat\Omega\,1)$ 的分支 $\hat\Omega(\mathtt{up}\,0\,\eta)$) 未证, 也未否定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RR4RegOmega2 where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Cp; Lgl)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiDispBase using (Edge; Below; one; more; e-suc; e-lim; e-first; e-branch)
open import OCF.Align.YiRegBase using (Reg)
```

## §1 基础

```agda
lv1 : LF
lv1 = F.suc F.zero

Ω₁ Ω₂ : LF
Ω₁ = V.Ω̂ lv1
Ω₂ = V.Ω̂ (F.suc lv1)

below-cp : ∀ {a b c} → Below a b → CP b c → Below a c
below-cp p V.self      = p
below-cp p (V.suc q)   = more (below-cp p q) e-suc
below-cp p (V.lim n q) = more (below-cp p q) (e-lim n)
below-cp p (V.fst q)   = more (below-cp p q) e-first

read0-reg : ∀ (η : Raw F.zero) → Reg (V.up F.zero η)
read0-reg G.zero         = tt
read0-reg (G.suc a)      = read0-reg a
read0-reg (G.lim f)      = λ n → read0-reg (f n)
read0-reg (G.lc () c t g)
read0-reg (G.em () T)
read0-reg G.top          = tt

one-below-Ω₁ : Below lv1 Ω₁
one-below-Ω₁ = one e-first

Ω₁-reg : Reg Ω₁
Ω₁-reg = one-below-Ω₁ , tt , tt , (λ η e → read0-reg η)
```

## §2 `top` 之下只有 `top` 与 `em top₀`

```agda
under-top-reg : ∀ (a : Raw lv1) → Cp lv1 a G.top → Reg (V.up lv1 a)
under-top-reg a (inj₁ refl) = Ω₁-reg
under-top-reg (G.em tt a′) (inj₂ (inj₁ refl)) = tt
under-top-reg (G.em tt a′) (inj₂ (inj₂ ()))
under-top-reg G.zero         (inj₂ ())
under-top-reg (G.suc a)      (inj₂ ())
under-top-reg (G.lim f)      (inj₂ ())
under-top-reg (G.lc r c t g) (inj₂ ())
under-top-reg G.top          (inj₂ ())
```

## §3 过守卫的坐标读回都 `Reg`

```agda
up-to : (f : ℕ → Raw lv1) → (∀ n → Cp lv1 (f n) (f (suc n))) →
  ∀ k m → Cp lv1 (f m) (f (k + m))
up-to f st zero    m = inj₁ refl
up-to f st (suc k) m = F.Cp-tr lv1 (up-to f st k m) (st (k + m))

guarded-reg : ∀ (η : Raw lv1) → Lgl lv1 η → Cp lv1 G.top η → Reg (V.up lv1 η)
guarded-reg G.zero l (inj₁ ())
guarded-reg G.zero l (inj₂ ())
guarded-reg (G.suc a) l (inj₁ ())
guarded-reg (G.suc a) l (inj₂ p) = guarded-reg a l p
guarded-reg (G.lim f) (st , lw) (inj₁ ())
guarded-reg (G.lim f) (st , lw) (inj₂ (n , p)) = term
  where
  term : ∀ m → Reg (V.up lv1 (f m))
  term m with F.cmpC lv1 (f (m + n))
                (subst (λ z → Cp lv1 (f m) (f z)) (+-comm n m) (up-to f st n m))
                (F.Cp-tr lv1 p (up-to f st m n))
                (lw (m + n))
  ... | inj₁ below-top = under-top-reg (f m) below-top
  ... | inj₂ above-top = guarded-reg (f m) (lw m) above-top
guarded-reg (G.lc (inj₁ tt) c t g) (tg , mono , irr , lt , lg) (inj₁ ())
guarded-reg (G.lc (inj₁ tt) c t g) (tg , mono , irr , lt , lg) (inj₂ p) =
    more (below-cp one-below-Ω₁ (V.cp→CP lv1 p)) e-first
  , tt
  , guarded-reg t lt p
  , (λ η e → guarded-reg (g η e) (lg η e) (F.Cp-tr lv1 p (tg η e)))
guarded-reg (G.lc (inj₂ ()) c t g) l p
guarded-reg (G.em tt a) l (inj₁ ())
guarded-reg (G.em tt a) l (inj₂ ())
guarded-reg G.top l p = Ω₁-reg
```

## §4 $\hat\Omega\,2$

根条件: 2 是 $\hat\Omega\,1$ 在坐标 `raw2` 处的分支, $\hat\Omega\,1$ 是 $\hat\Omega\,2$ 的第一支.

```agda
raw1 raw2 : Raw F.zero
raw1 = G.suc G.zero
raw2 = G.suc raw1

raw2-guard : Gd F.zero (V.cO F.zero) raw2
raw2-guard = inj₂ (inj₁ refl) , tt

two-below-Ω₂ : Below (F.suc lv1) Ω₂
two-below-Ω₂ = more (one (e-branch raw2 raw2-guard)) e-first

Ω₂-reg : Reg Ω₂
Ω₂-reg = two-below-Ω₂ , tt , Ω₁-reg , (λ η e → guarded-reg η (proj₂ e) (proj₁ e))
```

## §5 退化坐标的实例

```agda
junk : Raw lv1
junk = G.lc (inj₁ tt) raw1 G.top (λ _ _ → G.top)

junk-lgl : Lgl lv1 junk
junk-lgl = (λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) , (λ _ _ _ → refl) , tt , (λ _ _ → tt)

junk-guard : Gd lv1 (V.cO lv1) junk
junk-guard = inj₂ (inj₁ refl) , junk-lgl

junk-read : V.up lv1 junk ≡ F.lc F.zero raw1 Ω₁ (λ _ _ → Ω₁)
junk-read = refl

junk-reg : Reg (V.up lv1 junk)
junk-reg = guarded-reg junk junk-lgl (proj₁ junk-guard)
```

**范围.** 第 1 层坐标, 原块, 冻结的 `Reg`. `guarded-reg` 的三条事实里, "`top` 之下只有 `top` 与 `em top₀`" 是第 1 层专有的; 一般层的 `top` 之下是低层 `top` 的嵌入链, 要对层号归纳, 本文未做. 所以本文不说 `Reg` 在一切规范层上成立.
