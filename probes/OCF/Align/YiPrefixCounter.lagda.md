# (b)：前缀 Ω 仍不覆盖实际比较 Ω·2+1 与 ω

前缀表示的左端只有零、后继和 Ω 结点，右端为标准 lim natF。
两端都合法，但互不为第一位置；由公共界比较排除任何合法 CP 公共界。
这不是仅换一个更大界的问题，亦未否定其它树表示或 S3。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPrefixCounter where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)
open import OCF.Align.EboLeanDef using (T; ψ)
open import OCF.Align.LevelFixCore using (LF)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiPrefixNames
open import OCF.Align.YiSpineCommon
open import OCF.Align.YiSpineTrace using (Actual)
open import OCF.Align.YiPrefixWitness using (counter-call)

left right : Y.Level
left = ι_L left-name
right = ι_L nw

data Finite : LF → Set where
  fz : Finite F.zero
  fs : ∀ {a} → Finite a → Finite (F.suc a)

finite-nat : ∀ n → Finite (V.natF n)
finite-nat zero = fz
finite-nat (suc n) = fs (finite-nat n)

finite-of-position : ∀ {a b} → CP a b → Finite b → Finite a
finite-of-position V.self f = f
finite-of-position (V.suc p) (fs f) = finite-of-position p f
finite-of-position (V.lim n p) ()
finite-of-position (V.fst p) ()

left-not-finite : Finite (Y.tree left) → ⊥
left-not-finite (fs ())

left-not-right : CP (Y.tree left) (Y.tree right) → ⊥
left-not-right (V.lim n p) = left-not-finite (finite-of-position p (finite-nat n))

right-not-left : CP (Y.tree right) (Y.tree left) → ⊥
right-not-left (V.suc (V.fst (V.suc (V.suc (V.fst (V.suc (V.suc ())))))))

no-common : Common left right → ⊥
no-common c with common→spinal {a = left} {b = right} c
... | inj₁ p = left-not-right p
... | inj₂ p = right-not-left p

actual-counter : Actual left-code ω-code
actual-counter = counter-call

Coverage : Set
Coverage = ∀ {l r} → Actual l r → (nl : Name l) (nr : Name r) →
  CP (Y.tree (ι_L nr)) (Y.tree (ι_L nl))

no-coverage : Coverage → ⊥
no-coverage covers = right-not-left (covers actual-counter left-name nw)

extension-no-common : (M : Extension) →
  Common (read M left-code) (read M ω-code) → ⊥
extension-no-common M c with common→spinal {a = read M left-code} {b = read M ω-code} c
... | inj₁ p = left-not-right
  (subst (λ b → CP (Y.tree left) b) (agrees M nw)
    (subst (λ a → CP a (Y.tree (read M ω-code))) (agrees M left-name) p))
... | inj₂ p = right-not-left
  (subst (λ b → CP (Y.tree right) b) (agrees M left-name)
    (subst (λ a → CP a (Y.tree (read M left-code))) (agrees M nw) p))

extension-no-coverage : (M : Extension) →
  (∀ {l r} → Actual l r → CP (Y.tree (read M r)) (Y.tree (read M l))) → ⊥
extension-no-coverage M covers = extension-no-common M
  (spinal→common {a = read M left-code} {b = read M ω-code}
    (inj₂ (covers actual-counter)))
```

## 字面来源无关：目标不出现在 ν 的语法内

Pure 表示递归地仅含零参数 Ω 单项的有限和，所有 ψ 的第二参数为空。
Sub 明列 T 语法子项（自身、下标、参数、尾项、单项头）；不按值闭包。
因此“没有出现”说的是字面语法，不是没有码序关系。

```agda
data Pure : T → Set where
  pz : Pure []
  ph : ∀ {u xs} → Pure u → Pure xs → Pure (ψ u [] ∷ xs)

data Sub (a : T) : T → Set where
  here : Sub a a
  index : ∀ {u b xs} → Sub a u → Sub a (ψ u b ∷ xs)
  argument : ∀ {u b xs} → Sub a b → Sub a (ψ u b ∷ xs)
  tail : ∀ {u b xs} → Sub a xs → Sub a (ψ u b ∷ xs)
  head : ∀ {u b xs} → Sub a (ψ u b ∷ []) → Sub a (ψ u b ∷ xs)

pure-sub : ∀ {a b} → Sub a b → Pure b → Pure a
pure-sub here p = p
pure-sub (index s) (ph u xs) = pure-sub s u
pure-sub (argument s) (ph u xs) = pure-sub s pz
pure-sub (tail s) (ph u xs) = pure-sub s xs
pure-sub (head s) (ph u xs) = pure-sub s (ph u pz)

ν-pure : Pure ν-code
ν-pure = ph (ph pz pz) (ph (ph pz pz) pz)

ω-not-pure : Pure ω-code → ⊥
ω-not-pure ()

target-not-in-index : Sub ω-code ν-code → ⊥
target-not-in-index s = ω-not-pure (pure-sub s ν-pure)
```

目标 ω 不出现在 ν=Ω·2 的字面子项中；actual-gt 仍给 Ω·2+1 >ᵀ ω。
因此前缀 Ω 保证“自己的下标在自己的树内”，不能保证其它实际目标也在内。
主结果没有 Extension 前提；其加强版的合同由 structure-model 实填，
不靠任意正 ψ 的填值制造反例。

## 逐边覆盖不自动给全顶点链

下面只说明一项逻辑缺口，不是实际 EBO 比较图的模型或反例。
在同一套前缀树表示中取三个合法顶点 0、left、right，边为
0→left 及 0→right。图有共同下端、每条边都有所需 CP，
但两个上端不成链。因而不能用无向连通或共同下端代替共同后继。

```agda
data Fork : Set where
  base tipL tipR : Fork

fork-image : Fork → Y.Level
fork-image base = Y.zero
fork-image tipL = left
fork-image tipR = right

data ForkEdge : Fork → Fork → Set where
  toL : ForkEdge base tipL
  toR : ForkEdge base tipR

fork-edge-position : ∀ {a b} → ForkEdge a b →
  CP (Y.tree (fork-image a)) (Y.tree (fork-image b))
fork-edge-position toL = V.suc (V.fst (V.suc (V.suc (V.fst (V.suc (V.suc V.self))))))
fork-edge-position toR = V.lim 0 V.self

fork-not-chain : (∀ a b → Spinal (fork-image a) (fork-image b)) → ⊥
fork-not-chain all = no-common
  (spinal→common {a = left} {b = right} (all tipL tipR))
```

此有限图不替代 Actual。对所有实际层号的链结论仍须实际图自身的
共同后继／共同合法脊柱事实；本轮没有证出，也没有否定那项事实。
