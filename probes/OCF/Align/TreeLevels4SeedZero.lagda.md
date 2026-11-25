# 第四轮：实际初值第零支的原 Lgl

**实际路径上的局部事实（该子树即 ω），不是第四轮 (a) 或 (b) 的完成。** 本篇仍用原
LevelNoKFold.ψ₀Λ、原 NoKCertEval.Goodᵁ / forceᵁ 和原 LevelFixCore.Lgl。
实际路径是：原程序的 ℕ 极限第 2 支 → ŝ 初值 → 初值的第 0 支。
最后这棵树仍是一整个 ℕ 极限，不是一个有限样本。

actual-seed-zero-good 为这棵实际子树构造原计值证书，
actual-seed-zero-Lgl 证明它的计值在任意层 k 读回都满足原 Lgl。
不假定原程序整体已经有 Goodᵁ，也不从 Goodᵁ 里投影一个已经假设的守卫。

Box 只把原 native 树的地板参数存在 Σ 式包装里；core、branch、initial
均为第 4 层选择器。read-core / read-branch / read-initial 逐个证明选择器
与原 rdZ 以及第三轮选择器相容，最后 omega-origin 接回第三轮的实际对象。
选择器虽然有默认零值，actual-natural 的 NatLimit 构造子要求命中实际
ol，且对每个自然数 n 给出第 n 支确为 n 的见证；默认零值没有这种实例。
NatLimit 是自然数形的证明辅助，主结论直接是原 Lgl，没有替换它。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevels4SeedZero where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import OCF.Align.LevelFixCore using (LF; Lgl; Cp; module G)
open import OCF.Align.LevelNoKU using (𝕌; module U)
import OCF.Align.LevelNoKFold as O
import OCF.Align.NoKCertEval as E
import OCF.Align.TreeLevels4Nat as S
import OCF.Align.TreeLevels3FeedbackShape as A
import OCF.Free.Level as F
open O.TT using (o0; os; ol; oŝ; oĉ; owk; ocv; omk; oΩ; ocl)
data Box : Set where
  box : ∀ {π} → O.O U.zero π → Box
floor : Box → U.Fl
floor (box {π} x) = π
one : ∀ {π} → O.O U.zero π
one {π} = owk {π = U.tz} {ρ = π} (λ ()) (os o0)
read : Box → E.Zᵁ
read (box x) = E.rdZ x
coreO : ∀ {π} → O.O U.zero π → Box
coreO (owk w x) = coreO x
coreO (ocv w x) = coreO x
coreO x = box x
core : Box → Box
core (box x) = coreO x
branchO : ∀ {π} → ℕ → O.O U.zero π → Box
branchO n (ol f) = box (f n)
branchO n (owk w x) = branchO n x
branchO n (ocv w x) = branchO n x
branchO n _ = box {U.tz} o0
branch : ℕ → Box → Box
branch n (box x) = branchO n x
initialO : ∀ {π} → O.O U.zero π → Box
initialO (oŝ c t g) = box t
initialO (owk w x) = initialO x
initialO (ocv w x) = initialO x
initialO _ = box {U.tz} o0
initial : Box → Box
initial (box x) = initialO x
read-coreO : ∀ {π} (x : O.O U.zero π) → read (coreO x) ≡ E.rdZ x
read-coreO (owk w x) = read-coreO x
read-coreO (ocv w x) = read-coreO x
read-coreO o0 = refl
read-coreO (os x) = refl
read-coreO (ol f) = refl
read-coreO (oŝ c t g) = refl
read-coreO (oĉ c z zg t g) = refl
read-coreO (omk () _ _ _ _)
read-coreO (oΩ () _ _)
read-coreO (ocl () _ _ _ _)
read-core : ∀ b → read (core b) ≡ read b
read-core (box x) = read-coreO x
read-branchO : ∀ {π} n (x : O.O U.zero π) → read (branchO n x) ≡ A.lim-at (E.rdZ x) n
read-branchO n o0 = refl
read-branchO n (os x) = refl
read-branchO n (ol f) = refl
read-branchO n (oŝ c t g) = refl
read-branchO n (oĉ c z zg t g) = refl
read-branchO n (owk w x) = read-branchO n x
read-branchO n (ocv w x) = read-branchO n x
read-branchO n (omk () _ _ _ _)
read-branchO n (oΩ () _ _)
read-branchO n (ocl () _ _ _ _)
read-branch : ∀ n b → read (branch n b) ≡ A.lim-at (read b) n
read-branch n (box x) = read-branchO n x
read-initialO : ∀ {π} (x : O.O U.zero π) → read (initialO x) ≡ A.first (E.rdZ x)
read-initialO o0 = refl
read-initialO (os x) = refl
read-initialO (ol f) = refl
read-initialO (oŝ c t g) = refl
read-initialO (oĉ c z zg t g) = refl
read-initialO (owk w x) = read-initialO x
read-initialO (ocv w x) = read-initialO x
read-initialO (omk () _ _ _ _)
read-initialO (oΩ () _ _)
read-initialO (ocl () _ _ _ _)
read-initial : ∀ b → read (initial b) ≡ A.first (read b)
read-initial (box x) = read-initialO x
opaque
  whole : Box
  whole = box O.ψ₀Λ
  origin : read whole ≡ A.whole
  origin = sym A.whole-origin
omegaBox : Box
omegaBox = core (branch 0 (initial (branch 2 whole)))
omega-origin : read omegaBox ≡ A.lim-at A.actual-seed 0
omega-origin = trans (read-core _) (trans (read-branch 0 _)
  (cong (λ x → A.lim-at x 0) (trans (read-initial _)
  (cong A.first (trans (read-branch 2 _) (cong (λ x → A.lim-at x 2) origin))))))
data NatLimit : Box → Set where
  nat-limit : ∀ {π} {f : ℕ → O.O U.zero π} → (∀ n → S.RN (f n) n) → NatLimit (box (ol f))
opaque
  unfolding whole
  actual-natural : NatLimit omegaBox
  actual-natural = nat-limit {π = floor omegaBox}
    {f = λ n → O.TT.repᵒ (one {floor omegaBox}) n}
    (λ n → S.rn-rep {π = floor omegaBox} {x = one {floor omegaBox}} (S.rw _ (S.rs S.r0)) n)

nat-good : ∀ {π} {x : O.O U.zero π} {n} → S.RN x n → E.Goodᵁ (E.rdZ x)
nat-good {n = n} p = subst E.Goodᵁ (sym (S.rd-n p)) (S.gn n)
nat-force : ∀ {π} {x : O.O U.zero π} {n} (p : S.RN x n) → E.forceᵁ (E.rdZ x) (nat-good p) ≡ S.natO n
nat-force {n = n} p = trans (S.force-subst (sym (S.rd-n p)) (S.gn n)) (S.gn-force n)
nat-step : ∀ n {a b} → a ≡ S.natO n → b ≡ S.natO (suc n) → a F.⊑⁰ b
nat-step n refl refl q = F.≺s q
limit-good : ∀ {b} → NatLimit b → E.Goodᵁ (read b)
limit-good (nat-limit p) = E.gl (λ n → nat-good (p n))
  (λ n → nat-step n (nat-force (p n)) (nat-force (p (suc n))))
nat-legal : ∀ k n {y} → y ≡ S.natO n → Lgl k (E.rdR k y)
nat-legal k zero refl = tt
nat-legal k (suc n) refl = nat-legal k n refl
nat-prefix : ∀ k n {a b} → a ≡ S.natO n → b ≡ S.natO (suc n) → Cp k (E.rdR k a) (E.rdR k b)
nat-prefix k n refl refl = inj₂ (inj₁ refl)
limit-legal : ∀ {b} (p : NatLimit b) k → Lgl k (E.rdR k (E.forceᵁ (read b) (limit-good p)))
limit-legal (nat-limit p) k =
  (λ n → nat-prefix k n (nat-force (p n)) (nat-force (p (suc n)))) ,
  (λ n → nat-legal k n (nat-force (p n)))
actual-seed-zero-good : E.Goodᵁ (A.lim-at A.actual-seed 0)
actual-seed-zero-good = subst E.Goodᵁ omega-origin (limit-good actual-natural)
actual-seed-zero-Lgl : ∀ k → Lgl k (E.rdR k (E.forceᵁ _ actual-seed-zero-good))
actual-seed-zero-Lgl k = subst (λ y → Lgl k (E.rdR k y))
  (sym (S.force-subst omega-origin (limit-good actual-natural)))
  (limit-legal actual-natural k)
```

**范围。** actual-natural 是全称自然数族的构造子证书；不是布尔深宽
测试。actual-seed-zero-Lgl 覆盖上述子树的全部支以及所有读回层。
但它只检查实际初值的第零支；尚未证明整棵 actual-seed 的相邻支有
字面步进，也未构造整棵初值的 Goodᵁ、完整 gŝ 证书或其后回灌。
因此不能说原初值已经合法，更不能说原 ψ₀Λ 的全部反馈合法。

**未走通处。** 第三轮那两条相邻极限的有限头不足以否定 Lgl。代码
分析表明此初值来自 riseΩ 的内外两次折叠：目标类型都是 U.zero，
内层带 tp 位置证据，外层是 tn 0；它们保留各自 stChain / stBody 与
trim / lowerSt 生成的地板。把二者直接换成同一个纯树函数还没有证明。
后续需要在这些实际参数下证明整条链的字面步进，并覆盖 goC.bodyG 的
填表与回灌；仅证明结构互模拟或仅数个链点不够。本篇未据此判断必须
改原定义，没有修改原树、折叠、Lgl 或 Shape。

**编译实验。** 直接比较整条具体基本列的最初版本单 6G 退出 251，
错误如下；这是堆墙，不能作为类型否定或通过：

```text
agda: Heap exhausted;
agda: Current maximum heap size is 6442450944 bytes (6144 MB).
agda: Use `+RTS -M<size>' to increase it.
```

固定 tz 的 ω 证书直接套实际子树时得到 UnequalTerms：实际地板是
lowerSt / trim 的输出。泛化地板、封住原闭项，并显式给出 one 的源地板
及重复函数的地板后，上面完整代码单 6G 检查退出 0。没有增加堆或引用
函数外延；最初未限制推断的中间实验主动中断为 130，不算通过。
另一次使用 Box 别名比较整条函数的实验在 180 秒后退出 124，仍无类型
结论；未使用这些失败或中止实验的 html / 切片。

```text
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevels4SeedZero.lagda.md +RTS -M6G -RTS
```
