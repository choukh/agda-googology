# 完成闭项的真实有限高度整族

第1个外层采样坐标是ω。其合法化后的各项是有限部分和，原 θ 在这些
高度上逐项折叠。本篇把这一整族从原运行器中直接指出，不替换源树或路径。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionLowerFamily where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (Σ₀; leg)
open import OCF.Lean.Fold1If using (mul; _≤ᵛ_; ≤l; l≤; s≤s)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ʳ)
import OCF.Align.BoundedNativeValueFirst as V
import OCF.Align.BoundedNativeValueStrict as S
import OCF.Align.BoundedNativeFloor as N
import OCF.Align.BoundedNativeFoldRun as R
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedNativeCompletionClosed as C
import OCF.Lean.Fold1 as Old

height : ℕ → Cd
height n = hz ⊞ Σ₀ (λ j → leg (hz ⊞ mul V.one j)) n

sample : ℕ → Cd
sample n = T.fold V.feedback
  (R.fold V.B V.lB hz V.pt (N.θ (height n))
    (N.θ-path (height n) V.B (hsuc (hlim n hself))))

actual-first-output : V.Outer.C.oo 1 ≡ hl sample
actual-first-output = refl

sample-below-tree : ∀ n → sample n ≤ᵛ C.tree
sample-below-tree n = ≤-trans (≤l n (≤-refl _))
  (≤-trans (V.right≤ (V.Outer.C.oo 0) (V.Outer.C.oo 1))
    (≤-trans (≤l 1 (≤-refl _)) C.raw-lower))

whole-family-below-tree : hl sample ≤ᵛ C.tree
whole-family-below-tree = l≤ sample-below-tree

-- 真实全部外层项至少为1；旧下界之后可积累任意有限后继。
iterate : ℕ → Cd → Cd
iterate zero a = a
iterate (suc n) a = hs (iterate n a)

old-tail : ∀ n → iterate n Old.TΩ1 ≤ᵛ V.Outer.C.oO (suc n)
old-tail zero = S.old-in-first-sum
old-tail (suc n) = ≤-trans (s≤s (old-tail n))
  (⊞-≤ʳ (V.Outer.C.oO (suc n))
    (S.terminal-positive _ (T.native-branch (V.Outer.C.ce (suc (suc n))))))

old-plus-omega : hl (λ n → iterate n Old.TΩ1) ≤ᵛ C.tree
old-plus-omega = l≤ (λ n → ≤-trans (≤l (suc n) (old-tail n)) C.raw-lower)
```

`sample-below-tree`覆盖实际全部自然数采样，不是常值替身；它尚未将每项
与 EBO 塔参照比较。`old-plus-omega`是新粗下界（旧参照值右加ω的树），
来自全部外轨道而非前两项，但不将这一算术尾部误报为新的Ω塔站。
下一硬义务是这些有限高度的原fold与规范有限塔下降的带路径值模拟。

完成层本身还累加每个真实外层部分和，而全部这些部分和从第1项起
都支配旧闭项。因此可以证明整族旧闭项有限倍的下界；不是仅把旧下界
沿一次 inflation 搬运。

```agda
open import OCF.Lean.Fold1If using (≤s)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Align.FrozenValueFirst using (add-mono)

below-iterate : ∀ n (a : Cd) → a ≤ᵛ iterate n a
below-iterate zero a = ≤-refl a
below-iterate (suc n) a = ≤s (below-iterate n a)

old-below-completed-partial : ∀ n → Old.TΩ1 ≤ᵛ leg (V.Outer.C.oO (suc n))
old-below-completed-partial n = ≤-trans
  (≤-trans (below-iterate n Old.TΩ1) (old-tail n))
  (inflation (V.Outer.C.oO (suc n)))

completed-multiple : ∀ n → mul Old.TΩ1 n ≤ᵛ
  Σ₀ (λ j → leg (V.Outer.C.oO j)) (suc n)
completed-multiple zero = ≤-trans (old-below-completed-partial zero)
  (V.right≤ _ _)
completed-multiple (suc n) = add-mono (completed-multiple n)
  (old-below-completed-partial (suc n))

old-times-omega : hl (mul Old.TΩ1) ≤ᵛ C.tree
old-times-omega = l≤ (λ n → ≤l (suc n) (completed-multiple n))
```

`old-times-omega`的左边按原树加法为旧闭项的ω个右向累加。
这比前述尾部后继族给出了更完整的累加下界，但未将旧闭项的读法
假定为任何记号序数；也没有对接 EBO 的Ω塔各站。

下面把样本高度字面识别为自然数三角数，消除“含任意Cd就已覆盖任意
高层坐标”的误读。等式只作用于有限树，不使用函数外延。

```agda
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

num : ℕ → Cd
num zero = hz
num (suc n) = hs (num n)
plus : ℕ → ℕ → ℕ
plus a zero = a
plus a (suc b) = suc (plus a b)
tri : ℕ → ℕ
tri zero = 1
tri (suc n) = plus (tri n) (suc (suc n))

num-add : ∀ a b → num a ⊞ num b ≡ num (plus a b)
num-add a zero = refl
num-add a (suc b) = cong hs (num-add a b)
zero-num : ∀ n → hz ⊞ num n ≡ num n
zero-num zero = refl
zero-num (suc n) = cong hs (zero-num n)
leg-num : ∀ n → leg (num n) ≡ num n
leg-num zero = refl
leg-num (suc n) = cong hs (leg-num n)
mul-one : ∀ n → mul V.one n ≡ num (suc n)
mul-one zero = refl
mul-one (suc n) = cong hs (mul-one n)

summand-normal : ∀ n → leg (hz ⊞ mul V.one n) ≡ num (suc n)
summand-normal n = trans
  (cong (λ c → leg (hz ⊞ c)) (mul-one n))
  (trans (cong leg (zero-num (suc n))) (leg-num (suc n)))

partial-normal : ∀ n → Σ₀ (λ j → leg (hz ⊞ mul V.one j)) n ≡ num (tri n)
partial-normal zero = summand-normal zero
partial-normal (suc n) = trans
  (cong₂ _⊞_ (partial-normal n) (summand-normal (suc n)))
  (num-add (tri n) (suc (suc n)))

height-normal : ∀ n → height n ≡ num (tri n)
height-normal n = trans (cong (λ c → hz ⊞ c) (partial-normal n))
  (zero-num (tri n))
```

由 `height-normal`，本篇 sample 的源高度逐项为 1、3、6、10……。
这不构成 C 的值上界，也不否定 C；这里只限定已定位整族的实际类型。
EBO 参照 `WfFsn.EBO-tree` 则覆盖迭代Ω指标塔的全部站。
尚未证明前者下降值覆盖后者，不能把这两个整族合并记账。
