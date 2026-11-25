# O3：差树作用给出读回的字面合法性

**结构性定理；尚未连接 `LevelNoKFold.ψ₀Λ` 的实际输出。**
`NoKCertNeg.no-HS→Lgl` 排除仅凭 `HS` 读回字面合法性。本篇改用
可执行的差树形状：一棵差树是对当前可数树的追加作用，复合连续作用，
极限取有限次追加所得的列。极限的每个后项实际以其前项为输入，
所以第一位置步进由构造给出，无须比较两个任意树。

本篇不改已有折叠或守卫，不把形状证书定义成 `Lgl` 的别名。
差树的字段只有差、复合与 ℕ 列，不读记号，也不按阶段分类。
所有层 `k` 共用同一个证明，没有函数外延或证据唯一性前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO3Shape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as F
open import OCF.Align.LevelFixCore using (LF; Cp; Cp-tr; Lgl; Gd)
open import OCF.Align.NoKCertEval using (Ord₀; rdR)

data Difference : Set where
  idle : Difference
  tick : Difference → Difference
  then : Difference → Difference → Difference
  limit : (ℕ → Difference) → Difference

act : Difference → Ord₀ → Ord₀
partial : (ℕ → Difference) → Ord₀ → ℕ → Ord₀
act idle a = a
act (tick d) a = F.suc (act d a)
act (then d e) a = act e (act d a)
act (limit ds) a = F.lim (partial ds a)
partial ds a zero = a
partial ds a (suc n) = act (ds n) (partial ds a n)

prefix-act : ∀ d k a → Cp k (rdR k a) (rdR k (act d a))
prefix-act idle k a = inj₁ refl
prefix-act (tick d) k a = inj₂ (prefix-act d k a)
prefix-act (then d e) k a = Cp-tr k (prefix-act d k a)
  (prefix-act e k (act d a))
prefix-act (limit ds) k a = inj₂ (zero , inj₁ refl)

Lgl-act : ∀ d k a → Lgl k (rdR k a) → Lgl k (rdR k (act d a))
Lgl-partial : ∀ ds k a → Lgl k (rdR k a) → ∀ n →
  Lgl k (rdR k (partial ds a n))
Lgl-act idle k a la = la
Lgl-act (tick d) k a la = Lgl-act d k a la
Lgl-act (then d e) k a la = Lgl-act e k (act d a) (Lgl-act d k a la)
Lgl-act (limit ds) k a la =
  (λ n → prefix-act (ds n) k (partial ds a n)) , Lgl-partial ds k a la
Lgl-partial ds k a la zero = la
Lgl-partial ds k a la (suc n) =
  Lgl-act (ds n) k (partial ds a n) (Lgl-partial ds k a la n)

record Shape (y : Ord₀) : Set where
  constructor shaped
  field
    difference : Difference
    exact : y ≡ act difference F.zero

Lgl-from-shape : ∀ k y → Shape y → Lgl k (rdR k y)
Lgl-from-shape k .(act d F.zero) (shaped d refl) = Lgl-act d k F.zero tt

generated-shape : ∀ d → Shape (act d F.zero)
generated-shape d = shaped d refl

record ShapeFrom (a y : Ord₀) : Set where
  constructor appended
  field
    difference : Difference
    exact : y ≡ act difference a

guard-from-shape : ∀ k c a y → Cp k c (rdR k a) →
  Lgl k (rdR k a) → ShapeFrom a y → Gd k c (rdR k y)
guard-from-shape k c a .(act d a) p la (appended d refl) =
  Cp-tr k p (prefix-act d k a) , Lgl-act d k a la
```

`prefix-act` 的唯一一对下标带着实际的字面位置证据；本篇没有判等或
全域比较律。`Shape` 的前提由 `generated-shape` 对每棵差树实填，
不是未知接口的空前提。

**实质进展的范围。** 已把“追加形状 ⇒ 每一层读回合法”写成阶段无关
定理，替代了已被否定的“仅有 HS ⇒ 合法”前提。尚未证明原候选的
`oŝ` / `oĉ` 计值输出具有这个形状；那需要把实际反馈轨道接到 `act`，
不能对原输出补一次部分和后声称原值或原基本列已保持。本篇不交新闭项，
不作新强度声明。

`guard-from-shape` 进一步给出原始的整个 `Gd`：下界已在初始树 `a`
的第一位置上，且 `a` 的读回合法时，随后所有追加结果同时保持这两项。
这仍要求真实反馈输出的 `ShapeFrom`。本篇覆盖 `gŝ` 所用的可数读回
`rdR`；`gĉ` 的高层 Raw j 链不因此获得形状或合法性。
