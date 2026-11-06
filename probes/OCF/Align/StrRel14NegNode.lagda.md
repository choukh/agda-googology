# 结构关系, 第十四轮的否定 (一): 接口的 `NodeSound` 不成立

> 不读记号. 入口 [StrRel14Neg](StrRel14Neg.lagda.md). 对着 [StrRel14If](StrRel14If.lagda.md) 写 (定稿 10:18 的 §1–§5 与 10:40 增补的 §6).
>
> 接口 §4 的 `NodeSound` 是跨坐标层节点规则 `niˣ` 的可靠性: 坐标层 $k\sqsubseteq_\infty k'$, 分支在一切 `CP` 分支对与坐标关系上 `RelX` 相关 ⇒ 两个节点 `SemX` 相关. `SemX` 的状态前提是 `R∀X` (目标层相同的读数按 `RelX t t` 相关), 与 `StrRel12Sem.SemW` 的 `R∀c` 同形 (只是关系换成异质的); 接口 §2 的不变量 `Inv`/`J` **没有进入** `SemX`.
>
> **定理 `¬NodeSound : ¬ NodeSound`** (实例 $\Lambda_2=2$). 用 [StrRel13Val](StrRel13Val.lagda.md) 的同一对节点: 左 `xL` 坐标层 $0$, 右 `xR` 坐标层 $1$, 分支都是常数 `n1`, `u∞ s∞ : hz ⊑∞ hs hz` 是字面证据, 分支前提是 `n1ˣ`. 状态 `Yv` (第 $0$ 层读 `n1`, 别的层读 `n0`) 与自己按 `R∀X` 相关 (`hYvX`). 外层动作 `Act` 满足 `HAWX` (`haActX`, 对一切不含 $\Omega$-极限的 $\Lambda$). 于是 `NodeSound` 给出第 $0$ 层目标上 `RelX hz hz OutL OutR`, 由 `vsumX` (第 $0$ 层的异质关系值可靠) 得 $\Sigma_0\,\mathrm{OutL}\le\Sigma_0\,\mathrm{OutR}$, 与 `StrRel13Val.¬valX` 矛盾.
>
> 推论:
>
> - **`¬semX`**: `RelX Λ₂ Λ₂ tt tt xL xR` 有推导 (`relX`, 一条 `niˣ`), 但 `SemX Λ₂ Λ₂ tt tt xL xR` 不成立. 所以 "`RelX` ⇒ `SemX`" (接口 §3 的关系与语义要配成的那条可靠性) 不成立.
> - **`¬oblRR`, `¬oblRR⁼`**: 接口 `NodeObl` 的升升义务 `OblRR` (§4) 与按实际种类的 `OblRR⁼` (§6 增补, 10:40) 在参数 (`xL`, `xR`, 运行世界 $0$, 路径 `self`, 动作 `Act`, 上下文 `n0`, 状态 `Yv`) 上都不成立 (第 $0$ 层目标上两边的 `rkT` 实际都是 `rise`, 两个等式是 `refl`), 而这组参数满足 `SemX` 的全部前提. 所以升升义务不能只在 `R∀X` 的状态前提下证; 这是构造一路 `StrRel14Rk.node-red` 之后 "第一个障碍" (跨目标层的状态关系) 的编译形式.
>
> **构造一路为什么需要这条律.** `NodeSound` 是接手清单第 2 项 (`StrRel13` §3) 的可靠性陈述本身; 接口把它写成 `SemX` 的形式. `MonoStep Ωᴴ` 要的跨坐标层比较 (分支世界对 $c\le c'$ 给出坐标层 `emb c` 对 `emb c′`) 都经它.
>
> **前提可满足.** 全部给出: `relX` 的分支前提 `n1ˣ`, `cp00`, `haActX Λ₂ tt`, `n0ˣ`, `hYvX`, 目标对 `τ₀`, `cp00`.
>
> **范围.** 只否定接口里写成 `SemX` (状态前提 `R∀X`) 的 `NodeSound`, 及以 `R∀X` 为状态前提的 "`RelX` ⇒ `SemX`". 不否定把 `SemX` 的状态前提换成某个不变量 `J` 之后的版本; 那时哪些 `J` 也不行, 见 [StrRel14NegInv](StrRel14NegInv.lagda.md). 不否定 `niˣ` 这条规则作为关系的构造子 (它只是数据), 也不否定同层的 `StrRel14J.semJ`. 原因与 `StrRel13Val` 相同 (判断, 依据证明): `R∀X` 只比同一目标层上的读数, 而升升情形两边的链从状态在**各自坐标层**上的读数起.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel14NegNode where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.CumReadCF using (A; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (H; LgH; hz; hs; hl; hΩ; hself; hsuc; ss; sl; D; D₀; n0; n1; _⨾_; nl; ni; Ωd; accL;
  sum; pt; sum-fst)
open import OCF.Align.StrRel12 hz tt using (NoΩ; noΩ⊲)
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel13Val using (Λ₂; r₀; r₁; xL; xR; rdv; Yv; cp00; OutL; OutR; ¬valX)
```

## 1 与实例无关的三件: 第 0 层值可靠, $\Omega_t$ 自相关, `Act` 的 `HAWX`

```agda
module G (Λ : H) (lΛ : LgH Λ) where
  open If Λ lΛ
  open Rk Λ lΛ using (s∞)
  module Q = If.P Λ lΛ

  vsumX : ∀ {V V′ b b′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → RelX hz hz lV lV′ x x′ → b ≤ b′ → sum b x ≤ sum b′ x′
  vsumX {b′ = b′} {x′ = x′} n0ˣ h = ≤-trans h (⊲→≤ (sum-fst b′ x′))
  vsumX n1ˣ h = s≤ h
  vsumX {b = b} {b′} (⨾ˣ {x = x} {y} {x′} {y′} hx hy) h = vsumX {b = sum b x} {sum b′ x′} {x = y} {y′} hy (vsumX {x = x} {x′} hx h)
  vsumX {b = b} {b′} (nlˣ {d₁ = d} {d₁′ = d′} hd) h = l≤ (λ n → ≤l n (go n))
    where
    go : ∀ n → pt b d n ≤ pt b′ d′ n
    go zero = h
    go (suc n) = vsumX {b = pt b d n} {pt b′ d′ n} {x = d n} {d′ n} (hd n) (go n)
  vsumX {b = b} {b′} (prˣ {x = x} {x′ = x′} {y′} hx) h = ≤-trans (vsumX {b = b} {b′} {x = x} {x′} hx h) (⊲→≤ (sum-fst (sum b′ x′) y′))
  vsumX {b = b} {b′} (nwˣ {x = x} {x′} hp hx) h = vsumX {b = b} {b′} {x = x} {x′} hx h
  vsumX (niˣ {r = ()} _ _)
  vsumX (κˣ {zz = ()} _)

  ΩRX : ∀ t → NoΩ t → ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → RelX t t lW lW′ (Ωd t {W}) (Ωd t {W′})
  ΩRX hz o = n1ˣ
  ΩRX (hs b) o = ⨾ˣ n1ˣ (niˣ {r = ss hself} {r′ = ss hself} s∞ (λ p p′ lc lc′ cp y y′ hb → n1ˣ))
  ΩRX (hl f) o = ⨾ˣ n1ˣ (nlˣ (λ n → niˣ {r = sl n hself} {r′ = sl n hself} s∞ (λ p p′ lc lc′ cp y y′ hb → n1ˣ)))
  ΩRX (hΩ g) ()

  haActX : NoΩ Λ → ∀ L {W W′} {lW : Lg W} {lW′ : Lg W′} → HAWX L L lW lW′ Q.Act Q.Act
  haActX o L p p′ l l′ cp w w′ hw Y Y′ hY T T′ tc = nlˣ (λ _ → ⨾ˣ (ΩRX _ (noΩ⊲ (Q.tm T) o)) (proj₁ hY T T′ tc))
```

## 2 实例 $\Lambda_2$

```agda
open If Λ₂ tt
open G Λ₂ tt
open Rk Λ₂ tt using (s∞; u∞)

rrX : ∀ t {m m′} {lm : Lg m} {lm′ : Lg m′} → RelX t t lm lm′ (rdv t {m}) (rdv t {m′})
rrX hz = n1ˣ
rrX (hs b) = n0ˣ
rrX (hl f) = n0ˣ
rrX (hΩ g) = n0ˣ

hYvX : R∀X tt tt Yv Yv
hYvX = (λ {t} T T′ tc → rrX t) , n0ˣ

relX : RelX Λ₂ Λ₂ tt tt xL xR
relX = niˣ {r = r₀} {r′ = r₁} (u∞ s∞) (λ p p′ lc lc′ cp y y′ b → n1ˣ)

¬semX : ¬ SemX Λ₂ Λ₂ tt tt xL xR
¬semX s = ¬valX (vsumX (s tt tt (accL Λ₂) (accL Λ₂) hself hself C.self C.self cp00 P.Act P.Act (haActX tt Λ₂)
                          n0 n0 n0ˣ Yv Yv hYvX (P.τ₀ tt) (P.τ₀ tt) cp00) (≤-refl _))

¬NodeSound : ¬ NodeSound
¬NodeSound ns = ¬semX (ns r₀ r₁ {u = λ _ _ _ → n1} {u′ = λ _ _ _ → n1} (u∞ s∞) (λ p p′ lc lc′ cp y y′ b → n1ˣ))

-- 升升义务在这组参数上不成立
module O = NodeObl {lV = tt} {lV′ = tt} r₀ r₁ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL (hs hz))
                   C.self C.self hself hself P.Act P.Act n0 n0 Yv Yv

¬oblRR : ¬ O.OblRR
¬oblRR ob = ¬valX (vsumX (ob (P.τ₀ tt) (P.τ₀ tt) cp00) (≤-refl _))

-- §6 的按实际种类的版本: 第 0 层目标上两边的 rkT 实际都是 rise (refl), 所以同样不成立
module O⁼ = NodeObl⁼ {lV = tt} {lV′ = tt} r₀ r₁ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL (hs hz))
                     C.self C.self hself hself P.Act P.Act n0 n0 Yv Yv

¬oblRR⁼ : ¬ O⁼.OblRR⁼
¬oblRR⁼ ob = ¬valX (vsumX (ob (P.τ₀ tt) (P.τ₀ tt) cp00 refl refl) (≤-refl _))
```
