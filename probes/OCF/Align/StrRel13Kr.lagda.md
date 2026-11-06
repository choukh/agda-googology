# 结构关系, 第十三轮 (三): 左留右升, 结构关系里没有 "节点对极限" (否定)

> 不读记号. 入口 [StrRel13](StrRel13.lagda.md). 同 [StrRel13Val](StrRel13Val.lagda.md) 的实例与节点对 (`Λ₂`, `xL` 坐标层 $0$, `xR` 坐标层 $1$), 状态取空状态 `Y₀`, 目标取第 $1$ 层 (`T₁`). 目标层夹在两个坐标层之间 ($0\sqsubset 1\sqsubseteq 1$): 左边 `rkT` 是 `keep` (`rkL`), 右边是 `rise` (`rkR`), 这是 `StrRel13Rk.rk-mono` 的第三种. 于是左边的输出是第 $1$ 层的**节点** `ni …`, 右边的输出是坐标层 $1$ 的链的**极限** `nl …`.
>
> **`¬krX`**: 对任意关系族 $R$, 只要它没有 "左边 `ni`, 右边 `nl`" 的推导 (`NoNiNl R`), 这两个输出就不按 $R$ 相关. `StrRel12Rel.Rel` 满足 `NoNiNl` (`nn12`); 在它上面加任意多条 "`ni` 对 `ni`" 的跨层规则仍满足 (新规则的结论两边都是 `ni`). 推论 **`¬semKr`**: 用空状态也得到 `¬ SemW Λ₂ tt tt xL xR` (`StrRel13Val.¬semX` 用的是反例状态, 这里不用).
>
> **范围.** 否定的是: 结论层是一个结构关系族, 且其中没有 "节点 ≤ 极限" 的规则. 它不说这一对在值上不可比 (空状态下右边的链全是 `n0`, 左边是节点; 值的比较要看节点以后怎样被折叠, 本文不碰). 这是交接单说的 "一边升一边留, `rk-agree` 不再适用" 的编译形式: 结论层必须有一条把 "第 $t$ 层的节点" 放到 "链的极限" 之下的读法.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel13Kr where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; ss; StH; Vs; D; n0; nl; ni; accL)
open import OCF.Align.StrRel12Rel using (Rel; n0ᴸ)
open import OCF.Align.StrRel13Val using (Λ₂; module P; module S; module E₂; xL; xR; cp00)
```

## 1 第 1 层目标上的两种读数

```agda
T₁ : P.Tg azero (hs hz) azero
T₁ = P.tg C.self (hsuc hself) tt

rkL : P.rkT {hz} {hs hz} {azero} (hsuc (hsuc hself)) (hsuc hself) tt ≡ P.keep (ss hself)
rkL = refl

rkR : P.rkT {hs hz} {hs hz} {azero} (hsuc hself) (hsuc hself) tt ≡ P.rise
rkR = refl

-- rk-mono 的另两种也实际出现: 目标第 0 层两边升, 目标 Λ₂ 两边留
rk00 : P.rkT {hz} {hz} {azero} (hsuc (hsuc hself)) (hsuc (hsuc hself)) tt ≡ P.rise
rk00 = refl

rk10 : P.rkT {hs hz} {hz} {azero} (hsuc hself) (hsuc (hsuc hself)) tt ≡ P.rise
rk10 = refl

rk02 : P.rkT {hz} {Λ₂} {azero} (hsuc (hsuc hself)) hself tt ≡ P.keep (ss (hsuc hself))
rk02 = refl

rk12 : P.rkT {hs hz} {Λ₂} {azero} (hsuc hself) hself tt ≡ P.keep (ss hself)
rk12 = refl

OutL₁ OutR₁ : D (hs hz) azero
OutL₁ = P.yc (P.Run (accL Λ₂) xL C.self tt hself P.Act n0 P.Y₀) T₁
OutR₁ = P.yc (P.Run (accL Λ₂) xR C.self tt hself P.Act n0 P.Y₀) T₁
```

## 2 没有 "节点对极限" 的关系族

```agda
RelT : Set₁
RelT = ∀ L {V V′} → Lg V → Lg V′ → D L V → D L V′ → Set

NoNiNl : RelT → Set
NoNiNl R = ∀ {L V V′ k} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {d : ℕ → D L V′} → ¬ R L lV lV′ (ni r u) (nl d)

nn12 : NoNiNl Rel
nn12 ()

¬krX : ∀ R → NoNiNl R → ¬ R (hs hz) tt tt OutL₁ OutR₁
¬krX R nn h = nn h

¬semKr : ¬ S.SemW Λ₂ tt tt xL xR
¬semKr s = ¬krX Rel nn12
  (s tt tt (accL Λ₂) (accL Λ₂) hself hself C.self C.self cp00 P.Act P.Act (E₂.haAct tt Λ₂)
     n0 n0 n0ᴸ P.Y₀ P.Y₀ ((λ T T′ tc → n0ᴸ) , n0ᴸ) T₁ T₁ cp00)
```

## 3 附: 吸收进极限的第 0 段, 对齐给不出

若想用一条 "$x\le d(0)$ ⇒ $x\le\mathrm{nl}\,d$" 的规则让右边的链在第 $0$ 段吸收左边的节点, 它在第 $0$ 层也要成立 (语义的输出在一切目标上比, 含第 $0$ 层), 而第 $0$ 层的关系要生成 `nκ` 回灌用的对齐 (`StrRel12Rel.genAl`). `nl d` 的和的第一位置是 `lim 0 self` (`sum-fst`), `Al` 里没有把非空的左路径对到它的构造子 (`¬alLim0`, 对一切 $p$): 只有 `aRL`, 它要左边对齐到 `self`, 那只能是空路径. 所以这条规则要先给 `Al` 加构造子 (判断; 本文只编译 "现有的 `Al` 给不出").

```agda
open import OCF.Align.StrRel4Walk using (Al; aRL)

¬alLim0 : ∀ {L L′ a b} {f : ℕ → A} {p : a ⊲ b} {lb : Lg (asuc b)} {lf : Lg (alim f)} →
          ¬ Al L L′ (C.suc p) lb (C.lim {f = f} 0 C.self) lf
¬alLim0 (aRL ())
```
