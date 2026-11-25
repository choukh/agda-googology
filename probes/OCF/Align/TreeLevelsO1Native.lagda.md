# O1：在原候选初始环境中解释非自然数目标的卡点

**候选专属的结构诊断；没有交出完整 ι。** 本篇直接使用
`LevelNoKFold.ψ₀Λ` 的原始源层 Λ、合法证书与空表，不换折叠。
尝试把 ψ_u(b) 的目标解释为对应的树层，再调用原 `Fold.ψ`。
自然数目标可以走 `tn`；一般树目标须走 `tp`，并给可入的严格位置。

本篇检查第一个极限形目标 ω。在这个固定的初始源层与空表里，
它不只是“还没找到证据”：这里证明 Tg ∅ (toU ω) 无项。
这个否定只针对**固定源层、空表、目标直接按原层树解释**的尝试，
不否定更换解释环境、填表后解释、或其它候选内的 ι。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO1Native where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as L
open import OCF.Align.LevelFixVal
  using (Ω̂; tw; Λ; Legal-Λ; natF)
open import OCF.Align.LevelNoKU using (𝕌; toU; module U; XF; WF-U; self-U)
open import OCF.Align.LevelNoKBase XF using (Tc-id)
import OCF.Align.LevelNoKTree XF as Native

-- 只观察第一支；不把 Ω 分支视为无条件可入的位置。
data FiniteFirst : U.LG → Set where
  ff-zero : FiniteFirst U.zero
  ff-suc : ∀ {x} → FiniteFirst x → FiniteFirst (U.suc x)
  ff-lc : ∀ {c t g} → FiniteFirst t → FiniteFirst (U.lc c t g)

no-ff-limit : ∀ {f} → FiniteFirst (U.lim f) → ⊥
no-ff-limit ()

Ω-finite : ∀ x → FiniteFirst (toU x) → FiniteFirst (toU (Ω̂ x))
Ω-finite L.zero ff-zero = ff-suc ff-zero
Ω-finite (L.suc x) (ff-suc h) = ff-lc (Ω-finite x h)
Ω-finite (L.lim f) ()
Ω-finite (L.lc k c t g) (ff-lc h) = ff-lc (Ω-finite t h)

tower-finite : ∀ n → FiniteFirst (toU (tw n))
tower-finite zero = ff-zero
tower-finite (suc n) = Ω-finite (tw n) (tower-finite n)

no-adm-limit : ∀ {f x} → FiniteFirst x →
  (r : U.lim f U.< x) → U.Adm (U.tab U.∅) r → ⊥
no-adm-limit ff-zero ()
no-adm-limit (ff-suc h) U.zero a = no-ff-limit h
no-adm-limit (ff-suc h) (U.suc r) a = no-adm-limit h r a
no-adm-limit (ff-lc h) (U.fst r) a = no-adm-limit h r a
no-adm-limit (ff-lc h) (U.bra η e r) ((u , () , rest) , a)

no-adm-limit-in-Λ : ∀ {f} → (r : U.lim f U.< toU Λ) →
  U.Adm (U.tab U.∅) r → ⊥
no-adm-limit-in-Λ (U.lim n r) a = no-adm-limit (tower-finite n) r a

ωL : L.LF
ωL = L.lim natF

module Initial = Native.Fold (toU Λ) (WF-U Λ Legal-Λ)
  (self-U Λ Legal-Λ) (Tc-id (toU Λ))

no-limit-target′ : ∀ {t f} → Initial.Tg U.∅ t → t ≡ U.lim f → ⊥
no-limit-target′ (Initial.tn zero) ()
no-limit-target′ (Initial.tn (suc n)) ()
no-limit-target′ (Initial.tp r a) refl = no-adm-limit-in-Λ r a

no-ω-target : Initial.Tg U.∅ (toU ωL) → ⊥
no-ω-target t = no-limit-target′ t refl
```

这里的环境可满足：`Legal-Λ` 是原候选已编译的合法证书；每个有限塔的
`FiniteFirst` 由 `tower-finite` 实填。没有额外逻辑前提，也没有构造
裸层号比较器。Ω 分支不准在空表下穿越，正是 `Adm` 的原始定义，
不是本篇另加的限制。

**解释尝试的缺失结构。** 若按“所有主项共用候选初始源 Λ / 空表”
来递归解释，目标到了 ω 就不能调用原折叠。必须先有更丰富的解释环境，
给出实际表项、位置与分支合法性，并证明它们随子项与折叠输出保持。
只把 `tn` 的参数从自然数改写成树，或者只给源层的 `Legal`，均不够。
这不证明完整解释不能写，也不因这条定理修改原前三层。

## 实际解释调用的失败记录

仓库外实验 TreeLevelsO1Attempt.agda 在解释 ψ_ω(b) 的内部调用处，
先尝试复用原始自然数目标入口：

```text
ιψω : Native.O (toU Λ) U.tz → Native.O (toU ωL) U.tz
ιψω b = Initial.ψ U.∅ (Initial.tn ωL) (λ ()) b
```

实验带 `--safe --without-K --lossy-unification --cubical-compatible
--guardedness --hidden-argument-puns`，从仓库根用
agda --library-file=<库文件> -i src -i probes -i <实验目录> <实验目录>/TreeLevelsO1Attempt.agda +RTS -M6G -RTS
得到退出码 **42**。报错原文（路径位置行从略）：

```text
error: [UnequalTerms]
OCF.Align.LevelFixCore.LF !=< Agda.Builtin.Nat.Nat
when checking that the expression ωL has type Agda.Builtin.Nat.Nat
```

这个类型错误本身只说明 `tn` 不能接树目标；上面的 `no-ω-target`
进一步排除在**同一空表环境**中直接换 `tp` 来补齐。没有据此宣称完整
解释已经被否定。全记号项的真实 ι 和 ι-suc 仍未交出；本轮按作者
允许的失败交付，记录这一具体解释组织缺少的环境与可入性结构。
