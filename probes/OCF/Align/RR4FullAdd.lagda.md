# RR4 实验 (三): 四处严格块里, 链严格增长时同一个源的 gt 输出合法

> 第四次路线审查 (`probes/Survey/RR4-Fable52.md`) 的实验文件, 不进成品. 只导入 [YiLglFullCore](YiLglFullCore.lagda.md), [YiLglFullVal](YiLglFullVal.lagda.md), [YiLglFullStop](YiLglFullStop.lagda.md), 不改任何已有文件. 导入闭包不含记号.
>
> **要检验的问题.** D7 的硬止损由 `YiLglFullStop.no-fixed-output` / `YiLglFullZeroStep.no-faithful-preservation` 触发: 源 `source = lc 0 raw1 0 lower` 完全合法, 照 EBO 模板的链 $\gamma_{n+1}=\psi(f\,\gamma_n)$ 在种子处不动, gt 输出是常 1 列, 不满足严格的 `Legal`. 问: 对**同一个源**、同一个输出式 `lim (λ n → out go (points n) (guards n))`, 若链点按坐标严格增长 (加法链所保证的性质), 输出是否合法?
>
> **结果 (编译过的条件定理 `growing-output-legal`).** 是. 前提三条:
>
> 1. `grow`: 链点相邻两项在 Raw 坐标上严格 (`Dn`);
> 2. `StrictMap go`: 折叠把严格第一位置送到严格第一位置;
> 3. `LegalMap go`: 折叠保持 `Legal`.
>
> 证明只用源自己的合法性 (`lower-dn`, `lower-legal`), 不比较, 不判定.
>
> **前提可满足 (`instance-legal`).** 链取字面的 $1,2,3,\dots$; `go = (1 +ᴸ_)`, 它满足零行 `go 0 ≡ 1` (`go⁺-zero`), 严格 (`add-proper`), 保合法 (`Legal-add`). 这个 `go` **不是** $\psi$: 它不满足 gt 行. 实例只说明三条前提相容, 不说明完整的 $\psi$ 满足它们.
>
> **与原否定的关系.** `no-fixed-output` 的前提 `SeedChain` (链固定在种子) 与本文的 `grow` 互斥 (`not-both`). 两条定理合起来: 在这个源上, 输出不合法的原因恰是链不增长; 链严格增长时, 余下的义务是 `StrictMap go` 与 `LegalMap go` (完整折叠的互归纳, 仓库里未证), 以及把折叠输出作为 Raw 坐标并给出 `Dn` 增长 (本文未做).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RR4FullAdd where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import OCF.Align.YiLglFullCore as F
open F using (module G)
import OCF.Align.YiLglFullVal as V
import OCF.Align.YiLglFullStop as S
open S using (Raw0; One; seed; body; source; out; lower; lower-dn; lower-legal; guard-nonzero)

StrictMap LegalMap : (F.LF → F.LF) → Set
StrictMap go = ∀ {a b} → V.Properˢ a b → V.Properˢ (go a) (go b)
LegalMap go = ∀ x → V.Legal x → V.Legal (go x)

Grow : (points : ℕ → Raw0) → Set
Grow points = ∀ n → F.Dn F.zero (points n) (points (suc n))

growing-output-legal :
  ∀ (go : F.LF → F.LF) (points : ℕ → Raw0)
    (guards : ∀ n → F.Gd F.zero seed (points n)) →
  StrictMap go → LegalMap go → Grow points →
  V.Legal (F.lim (λ n → out go (points n) (guards n)))
growing-output-legal go points guards strict lawful grow =
  (λ n → strict (lower-dn (points (suc n)) (proj₂ (guards (suc n)))
                   (guard-nonzero (guards n)) (grow n))) ,
  (λ n → lawful (lower (points n)) (lower-legal (points n) (proj₂ (guards n))))
```

## 前提的实例

```agda
num : ℕ → Raw0
num zero    = seed
num (suc n) = G.suc (num n)

num-lgl : ∀ n → F.Lgl F.zero (num n)
num-lgl zero    = tt
num-lgl (suc n) = num-lgl n

num-cp : ∀ n → F.Cp F.zero seed (num n)
num-cp zero    = inj₁ refl
num-cp (suc n) = inj₂ (num-cp n)

num-guard : ∀ n → F.Gd F.zero seed (num n)
num-guard n = num-cp n , num-lgl n

num-grow : Grow num
num-grow n = inj₁ refl

go⁺ : F.LF → F.LF
go⁺ x = One V.+ᴸ x

go⁺-zero : go⁺ F.zero ≡ One
go⁺-zero = refl

go⁺-strict : StrictMap go⁺
go⁺-strict = V.add-proper One

go⁺-legal : LegalMap go⁺
go⁺-legal x w = V.Legal-add One x tt w

instance-legal : V.Legal (F.lim (λ n → out go⁺ (num n) (num-guard n)))
instance-legal = growing-output-legal go⁺ num num-guard go⁺-strict go⁺-legal num-grow
```

## 与原否定互斥

`SeedChain` 给出一切链点等于种子 (`S.points-fixed`); 种子到自己没有 `Dn`.

```agda
no-dn-seed : F.Dn F.zero seed seed → ⊥
no-dn-seed (inj₁ ())
no-dn-seed (inj₂ ())

not-both : ∀ step points guards → S.SeedChain step points guards → Grow points → ⊥
not-both step points guards chain grow =
  no-dn-seed (subst (λ z → F.Dn F.zero z seed)
                (S.points-fixed step points guards chain 0)
                (subst (F.Dn F.zero (points 0))
                  (S.points-fixed step points guards chain 1) (grow 0)))
```

## 范围

只对 `YiLglFullStop.source` 这一个源、第 0 层坐标、目标层 0 的输出式. 没有构造满足 gt 行的折叠, 没有证 `StrictMap`/`LegalMap` 对完整 $\psi$ 成立, 没有给出 "折叠输出读成 Raw 坐标且 `Dn` 增长" 的构造. 所以它不重开 D7, 只把 D7 最后一个反例的成因限定为链不增长.
