# 全合法分支共用一个 CP 界的反例

本篇只审查冻结的 `YiCtxBase.Inv`，不写 ψ，也不改已有树。
两个合法零层坐标使原 Ω_Ω 的分支分别出现
a = lim (suc ∘ nat) 与 b = lim nat 作为根层号字段。
两列每步都是后继；它们的第一项不同，分支却全为有限树，因而 CP 不可比。
这排除的是全分支字段共用一个界的 Inv，不是否定 Ctx、所有表示或 S3。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCtxFork where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All as All using ()
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Lgl)
open import OCF.Align.LevelFixVal using (CP; Legal; CP-tr)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
open import OCF.Align.YiSpineCommon using (Common; common→spinal)
open import OCF.Align.YiSpinePrefix using (add; Ωprefix)

raw-nat : ℕ → Raw F.zero
raw-nat zero = G.zero
raw-nat (suc n) = G.suc (raw-nat n)

raw-nat-legal : ∀ n → Lgl F.zero (raw-nat n)
raw-nat-legal zero = tt
raw-nat-legal (suc n) = raw-nat-legal n

nat-read : ℕ → LF
nat-read n = V.up F.zero (raw-nat n)

nat-read-agrees : ∀ n → nat-read n ≡ V.natF n
nat-read-agrees zero = refl
nat-read-agrees (suc n) = cong F.suc (nat-read-agrees n)

a b : LF
a = F.lim (λ n → F.suc (nat-read n))
b = F.lim nat-read

ηa ηb : Raw F.zero
ηa = G.suc (G.lim (λ n → G.suc (raw-nat n)))
ηb = G.suc (G.lim raw-nat)

ηa-legal : Lgl F.zero ηa
ηa-legal = (λ n → inj₂ (inj₁ refl)) , raw-nat-legal

ηb-legal : Lgl F.zero ηb
ηb-legal = (λ n → inj₂ (inj₁ refl)) , raw-nat-legal

guard-a : Gd F.zero (V.cO F.zero) ηa
guard-a = inj₂ (inj₂ (0 , inj₁ refl)) , ηa-legal

guard-b : Gd F.zero (V.cO F.zero) ηb
guard-b = inj₂ (inj₂ (1 , inj₁ refl)) , ηb-legal

one old-current prefix-current : Y.Level
one = Y.suc Y.zero
old-current = Y.Ω (Y.Ω one)
prefix-current = Ωprefix (Ωprefix one)

field-a : K.Field a (Y.tree old-current)
field-a = K.in-branch ηa guard-a K.at

field-b : K.Field b (Y.tree old-current)
field-b = K.in-branch ηb guard-b K.at
```

`nat-read-agrees` 是逐 n 的等式；没有把两个 ℕ 函数或两个极限树整体相等
当作前提。反例字段就是实际读回的树，分支定位不需要函数外延。
下面只用它们各项有限及第零项不同；不靠值估计排除 CP。

```agda
data Finite : LF → Set where
  fz : Finite F.zero
  fs : ∀ {x} → Finite x → Finite (F.suc x)

nat-finite : ∀ n → Finite (nat-read n)
nat-finite zero = fz
nat-finite (suc n) = fs (nat-finite n)

finite-legal : ∀ {x} → Finite x → Legal x
finite-legal fz = tt
finite-legal (fs f) = finite-legal f

a-level b-level : Y.Level
a-level = Y.level a ((λ n → V.suc V.self) , (λ n → finite-legal (fs (nat-finite n))))
b-level = Y.level b ((λ n → V.suc V.self) , (λ n → finite-legal (nat-finite n)))

finite-position : ∀ {x y} → CP x y → Finite y → Finite x
finite-position V.self f = f
finite-position (V.suc p) (fs f) = finite-position p f
finite-position (V.lim n p) ()
finite-position (V.fst p) ()

lim-not-finite : ∀ {f} → Finite (F.lim f) → ⊥
lim-not-finite ()

sample : LF → LF
sample F.zero = F.zero
sample (F.suc x) = F.zero
sample (F.lim f) = f 0
sample (F.lc k c t g) = F.zero

at-limit : ∀ {x f} → CP x (F.lim f) →
  (x ≡ F.lim f) ⊎ Σ ℕ (λ n → CP x (f n))
at-limit V.self = inj₁ refl
at-limit (V.lim n p) = inj₂ (n , p)

lim-not-position : ∀ f g → (f 0 ≡ g 0 → ⊥) → (∀ n → Finite (g n)) →
  CP (F.lim f) (F.lim g) → ⊥
lim-not-position f g different finite p with at-limit p
... | inj₁ e = different (cong sample e)
... | inj₂ (n , q) = lim-not-finite (finite-position q (finite n))

one-not-zero : F.suc F.zero ≡ F.zero → ⊥
one-not-zero ()

a-not-b : CP a b → ⊥
a-not-b = lim-not-position (λ n → F.suc (nat-read n)) nat-read
  one-not-zero nat-finite

b-not-a : CP b a → ⊥
b-not-a = lim-not-position nat-read (λ n → F.suc (nat-read n))
  (λ e → one-not-zero (sym e)) (λ n → fs (nat-finite n))

no-common : Common a-level b-level → ⊥
no-common c with common→spinal {a = a-level} {b = b-level} c
... | inj₁ p = a-not-b p
... | inj₂ p = b-not-a p

no-inv : ∀ Env → K.Inv Env old-current → ⊥
no-inv Env i = no-common
  (K.bound (K.context i) ,
   CP-tr (V.suc V.self) (K.field-pos i field-a) ,
   CP-tr (V.suc V.self) (K.field-pos i field-b))
```

Inv 给的是派发字段 suc k 的位置；这里先用 k CP suc k 取回 a／b 的
位置，再用它们无公共界矛盾。只用 `in-branch` 与 `at`，不依赖 `in-index`。

## 当前前缀树同样不能满足该 Inv

在 Ωprefix(Ωprefix(1)) 中，同样两个合法坐标的分支根字段变成 1+a 与 1+b。
它们的分支仍全为有限树，第一项为 2 与 1，故同类证明仍适用。

```agda
prefix-nat : ℕ → LF
prefix-nat n = V._+ᴸ_ (Y.tree one) (nat-read n)

prefix-nat-finite : ∀ n → Finite (prefix-nat n)
prefix-nat-finite zero = fs fz
prefix-nat-finite (suc n) = fs (prefix-nat-finite n)

prefix-a prefix-b : LF
prefix-a = V._+ᴸ_ (Y.tree one) a
prefix-b = V._+ᴸ_ (Y.tree one) b

prefix-a-level prefix-b-level : Y.Level
prefix-a-level = add one a-level
prefix-b-level = add one b-level

prefix-field-a : K.Field prefix-a (Y.tree prefix-current)
prefix-field-a = K.in-branch ηa guard-a K.at

prefix-field-b : K.Field prefix-b (Y.tree prefix-current)
prefix-field-b = K.in-branch ηb guard-b K.at

two-not-one : F.suc (F.suc F.zero) ≡ F.suc F.zero → ⊥
two-not-one ()

prefix-a-not-b : CP prefix-a prefix-b → ⊥
prefix-a-not-b = lim-not-position (λ n → F.suc (prefix-nat n)) prefix-nat
  two-not-one prefix-nat-finite

prefix-b-not-a : CP prefix-b prefix-a → ⊥
prefix-b-not-a = lim-not-position prefix-nat (λ n → F.suc (prefix-nat n))
  (λ e → two-not-one (sym e)) (λ n → fs (prefix-nat-finite n))

prefix-no-common : Common prefix-a-level prefix-b-level → ⊥
prefix-no-common c with common→spinal {a = prefix-a-level} {b = prefix-b-level} c
... | inj₁ p = prefix-a-not-b p
... | inj₂ p = prefix-b-not-a p

prefix-no-inv : ∀ Env → K.Inv Env prefix-current → ⊥
prefix-no-inv Env i = prefix-no-common
  (K.bound (K.context i) ,
   CP-tr (V.suc V.self) (K.field-pos i prefix-field-a) ,
   CP-tr (V.suc V.self) (K.field-pos i prefix-field-b))

-- 环境与当前树各自都有实际实例；不把失败归咎于空环境合同或树非法。
zero-context : K.Ctx (Y.zero ∷ [])
zero-context = K.ctx Y.zero (All._∷_ V.self All.[])

old-current-legal : Legal (Y.tree old-current)
old-current-legal = Y.legal old-current

prefix-current-legal : Legal (Y.tree prefix-current)
prefix-current-legal = Y.legal prefix-current
```

这两条否定均只针对本轮“所有合法分支字段共享单一 CP 界”的 Inv。
没有否定只处理活动／可入路径的上下文，没有否定其它位置域或树表示；
也没有把这项局部矛盾冒称五堵墙中的任一已有接口已触发。
