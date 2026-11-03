# 终局 (四): 壁垒检查. 接口的字段不碰壁垒的任何一种形式

> 不含记号. 结论写在 [EBOTop](EBOTop.lagda.md). 本文把壁垒的每种形式写成 "如果接口多了这样的字段, 就有 $\bot$ 或 WLPO", 全部是编译过的定理. `Stage` 没有这些字段. 反过来, `EBOTopLow.no-WLPO` 说 `Stage` 本身推不出 WLPO (否则 WLPO 可证).
>
> **逐字段.** `Stage` 没有一个字段的结论是 `Dec`, 三歧或全局函数到比较结果.
>
> | 字段 | 壁垒形式 | 为什么不碰 |
> |---|---|---|
> | `Lv`, `Tr`, `Ω`, `ψ₀`, `out` | `noBT`, `¬tri` | 折叠怎么派发不进接口. 低端实例在字面界内用 `<ᴵ-dec`, 塔上以 `S` 为参数, 不声称正确 |
> | `GoodL`, `GoodT` | `no-uniform`, `dec-A→WLPO` | 抽象谓词, 不要求可判定, 不要求含全部 `E a`. 下面的 `no-⊤`, `no-all-branch`, `bad-S`, `bad-dec` 说它不能取成什么 |
> | `cert` | | 结论是 `HS`, 只提第 0 层, 与比较无关 |
> | `feed`, `good-feed` | [Barrier](../Barrier.lagda.md) 的 `Ω-Extension` | 要证据. 壁垒要 "精确初始段 + 共尾元 + 有界三歧" 三件同在: `Ordᴵ` 没有共尾元 (`no-topᴵ`), 裸层号没有三歧 (`no-global`), 接口不要求同在 |
> | `_⊑_`, `infl`, `ub`, `lub`, `lub-Ω`, `Ω-Λ` | `¬tri-fix` | 前序, 不是全序. 不动点上三歧确实失败, 而这些字段都成立 |
> | `good-Λ` | | 只对塔. 不提其它序列 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EBOTopBarrier where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Barrier using (Ω-Extension; barrier; LPO)
open import OCF.Align.InaccTreeBase
open import OCF.Align.InaccFloorTree using (Sib; natL; module PF)
open import OCF.Align.InaccTree using (BT; noBT; L₁; zigzag)
open import OCF.Align.InaccSingularBase using (WLPO)
open import OCF.Align.InaccStrikeBase using (Funext)
open import OCF.Align.InaccFloorNeg using (dec-A→WLPO)
open import OCF.Align.InaccFloorBase using (Aℓ)
open import OCF.Align.InaccThetaNeg using (module Neg; E)
open import OCF.Align.InaccThetaEq using (module Eqv)
open import OCF.Align.Level as Lvl using
  (Ordᴵ; _≺ᴵ_; _≅ᴵ_; ≺ᴵ-irrefl; via; ωᴵ; natᴵ; natᴵ-step; suc; lim; l≅; ≅ᴵ-refl; ⊑ᴵ-refl)
open import OCF.Align.EBOTopRaw
import OCF.Align.EBOTopStage as St
```

## §1 全局与有界的比较

**字段 "好层号上任意两条路径可比" 不能有.** 塔的第 2 项就是 `L₁`, `noBT` 说以它为界的结构三歧直接是假的 (不只是推出 WLPO).

```agda
_ : tower 2 ≡ L₁
_ = refl

no-BT-field : (GL : Lv → Set) → (∀ ℓ → GL ℓ → BT ℓ) → GL (tower 2) → ⊥
no-BT-field GL cmp g = noBT (cmp L₁ g)
```

**字段 "层号全局可比" 不能有.** 在裸层号上, 不动点自己就是反例 (`¬tri-fix`). 在 `Ordᴵ` 上是 $\omega$ 与 $[1,2,3,\dots]$ (`¬triᴵ`, 与 [Uniform5Wall](Uniform5Wall.lagda.md) 的 `¬tri` 相同, 那个文件含记号, 所以这里重写).

```agda
no-global : (∀ a b → Trichʹ a b) → ⊥
no-global t = ¬tri-fix (t (next Λ) Λ)

private
  ω₁ : Ordᴵ
  ω₁ = lim (λ n → natᴵ (suc n)) (λ n → natᴵ-step (suc n))

  nl : ∀ m {f s} → lim f s Lvl.<ᴵ natᴵ m → ⊥
  nl zero ()
  nl (suc zero) (Lvl.suc ())
  nl (suc (suc m)) (Lvl.suc q) = nl (suc m) q

¬triᴵ : (∀ a b → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b) → ⊥
¬triᴵ t with t ωᴵ ω₁
... | inj₁ (via (l≅ h) (Lvl.lim n q)) = nl (suc n) q
... | inj₂ (inj₁ (via (l≅ h) (Lvl.lim n q))) = nl n q
... | inj₂ (inj₂ (l≅ h)) with h 0
...   | ()
```

**$\Omega$-共尾元与有界三歧只能选一个, 而接口两个都容许.** 低端实例的 `Ordᴵ` 有 `<ᴵ-dec` 而没有共尾元 (`no-topᴵ`). 裸层号有共尾元 (`cof`) 而没有 `BT`. `Stage` 不要求比较, 所以两者都是合法实例. 这就是 [Barrier](../Barrier.lagda.md) 的两难在接口上的样子; `barrier` 本身原样引用.

```agda
no-topᴵ : (c : Ordᴵ) → (∀ a → a ≺ᴵ c) → ⊥
no-topᴵ c h = ≺ᴵ-irrefl (h c)

barrier-form : Ω-Extension → LPO
barrier-form = barrier
```

## §2 好的谓词不能是全部, 也不能对全部分支封闭

```agda
module Good (S : Sib) where
  open Raw S

  ω₀ : Ordᴸ zero
  ω₀ = x 0

  -- 有限的一条路径: 第 0 项严格在第 1 项之下
  x₀≺x₁ : rd (x 0) St.≺⁰ rd (x 1)
  x₀≺x₁ = St.≺l 1 (St.≺l 2 (St.≺l 2 (St.≺l 1 (St.≺z (St.≅⁰-refl _)))))

  -- 层号 lim [1, 0, 0, …]
  zz : Lv
  zz = toLv zigzag

  -- GoodL = ⊤ 不行: 对一切裸层号 HS 是假的
  no-⊤ : (∀ ℓ → St.HS (rd (X ℓ))) → ⊥
  no-⊤ h with h zz
  ... | St.hl _ st = St.≺⁰-irrefl (st 0 x₀≺x₁)

  -- 好的谓词不能对全部分支封闭, 哪怕只对参数层 0. 分支必须限制到好输入
  no-all-branch : (GL : Lv → Set) → (∀ ℓ → GL ℓ → St.HS (rd (X ℓ))) →
                  (∀ k g → GL (limᴼ k g) → ∀ y → GL (g y)) → GL (tower 2) → ⊥
  no-all-branch GL gc ab g with gc zz (ab zero toLv g zigzag)
  ... | St.hl _ st = St.≺⁰-irrefl (st 0 x₀≺x₁)
```

## §3 原始判决与好输入的判定

`no-L3`: [InaccTheta](InaccTheta.lagda.md) 的好层号 `LvG` 在塔的第 3 项就推出 WLPO, 只要 $2$ 算好输入. 这是 `no-Ω₂` 经 $x_3$ 的分支 $y=2$ 的直接推论 (`level-Ω₂`). 所以**那个设计的好层号到不了塔的第 3 项**, 不只是 "第 5 站用不到它". `bad-S`: 字段 "`S` 对全部 `Ordᴵ` 层号正确" 推出 WLPO. `bad-dec`: 字段 "好输入可判定" 推出 WLPO.

```agda
module Forms (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Neg S B₀ using (no-uniform; no-Ω₂)
  open Eqv S B₀ using (LvG; LvT)

  no-L3 : B₀ (suc (suc zero)) → LvG (tower 3) → WLPO
  no-L3 b w = no-Ω₂ (proj₂ (proj₂ w) (suc (suc zero)) b)

  bad-S : (GL : Lv → Set) → (∀ a → GL (E a)) → (∀ ℓ → GL ℓ → LvT ℓ) → WLPO
  bad-S GL ga gt = no-uniform (λ a → gt (E a) (ga a))

bad-dec : Funext → (∀ x → Dec (Aℓ (Lvl.suc ωᴵ) zero x)) → WLPO
bad-dec = dec-A→WLPO
```
