# 值判据 (十二): 检验旧树

> **判决: HOLDS (一条定理, 其余是测试).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 只含检验: 把 `Reg⁰` 用在 `wrong-fold` 的树上 (定理), 在几棵对的树上走几步 (有限测试, 不是证明). 导入闭包见结论文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeCheck where

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.InaccTreeBase using (Lv; Ordᴸ; Tree)
import OCF.Align.InaccTreeBase as L
open import OCF.Align.InaccFloorTree using (Sib; natL)
open import OCF.Align.VerdictSpecReject using (module PW)
open import OCF.Align.TreeJudgeBase using (Tr; t0; ts; tl; Reg⁰; lim-const)
open import OCF.Free.Level using (Ordᶜ)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.ValueJudgeReg using (toTr; slowt)
import OCF.Align.LadderInfCert as Ce
import OCF.Free.Level as FL
```

## §1 `wrong-fold` 的树: `Reg⁰` 拒绝

`PW` 把上升的链丢掉: 第 $n$ 项不看 $n$. 所以输出是常值的极限. `lim-const`. 这是定理, 对任何 `S`. 这条也说明: `wrong-fold` 这种错不必动用值判据.

```agda
toTrᴸ : Ordᴸ L.zero → Tr
toTrᴸ Tree.zero    = t0
toTrᴸ (Tree.suc x) = ts (toTrᴸ x)
toTrᴸ (Tree.lim f) = tl (λ n → toTrᴸ (f n))
toTrᴸ (Tree.limᵢ () f)
toTrᴸ (Tree.up () x)

wrong-fold-not-reg : ∀ (S : Sib) → Reg⁰ (toTrᴸ (PW.Tʷ S (natL 2))) → ⊥
wrong-fold-not-reg S r = lim-const r
```

## §2 有限测试: 对的树上 1-走步

`inW f d y x`: 深度 $d$ 的结构比较下, $y$ 在 $x$ 的前 $f$ 步 1-走步上. 这是 `W⁰` 的取样. `reg? f d n t`: 极限节点的前 $n$ 对都过 `inW`. **测试, 不是证明.**

```agda
same : ℕ → Tr → Tr → Bool
same zero    _ _ = true
same (suc d) t0 t0 = true
same (suc d) (ts a) (ts b) = same d a b
same (suc d) (tl f) (tl g) = same d (f 0) (g 0) ∧ same d (f 1) (g 1)
same (suc d) _ _ = false

step1 : Tr → Tr
step1 t0 = t0
step1 (ts a) = a
step1 (tl f) = f 1

isZero : Tr → Bool
isZero t0 = true
isZero _ = false

inW : ℕ → ℕ → Tr → Tr → Bool
inW zero    d y x = false
inW (suc f) d y x with isZero x
... | true  = false
... | false = same d y (step1 x) ∨ inW f d y (step1 x)

pair? : ℕ → ℕ → (ℕ → Tr) → ℕ → Bool
pair? f d h n = inW f d (h n) (h (suc n))

first-pairs : ℕ → ℕ → Tr → Bool
first-pairs f d (tl h) = pair? f d h 0 ∧ pair? f d h 1
first-pairs f d _ = false

T₀∞ᵗ : Tr
T₀∞ᵗ = toTr (forceᴺ _ (Ce.G∞ FL.zero))

-- 递归地: 每个极限节点的前 3 对, 深 k 层
regD : ℕ → ℕ → ℕ → Tr → Bool
regD zero    f d t = true
regD (suc k) f d t0 = true
regD (suc k) f d (ts a) = regD k f d a
regD (suc k) f d (tl h) =
  pair? f d h 0 ∧ pair? f d h 1 ∧ pair? f d h 2 ∧ regD k f d (h 0) ∧ regD k f d (h 1) ∧ regD k f d (h 2)

T₁∞ᵗ T₂Ωᵗ : Tr
T₁∞ᵗ = toTr (forceᴺ _ (Ce.G∞ (FL.suc FL.zero)))
T₂Ωᵗ = toTr (forceᴺ _ (Ce.G₂ 1 FL.zero))
```

**记录 (测试).** $T_0^\infty$ 在深 2, 步数 8, 比较深度 3 上过. $T_1^\infty$ 顶层的前三对在比较深度 2 上过 (`t1-pair₀` 等), 但 `regD 2 8 3` 是 false, `T₂Ω` 也是 false (`t1-reg`, `t2-reg`): 没有定位是步数不够, 比较深度的假阴性, 还是真的不满足 `Reg⁰`; 把步数加到 60 的运行在 6G 内存, 280 秒内没有结果. 对照: `slowt 2` 是 false.

```agda
kids : Tr → ℕ → Tr
kids (tl h) n = h n
kids (ts a) n = a
kids t0 n = t0

t0-reg : regD 2 8 3 T₀∞ᵗ ≡ true
t0-reg = refl

t1-pair₀ : pair? 8 2 (kids T₁∞ᵗ) 0 ≡ true
t1-pair₀ = refl

t1-pair₁ : pair? 8 2 (kids T₁∞ᵗ) 1 ≡ true
t1-pair₁ = refl

t1-pair₂ : pair? 8 2 (kids T₁∞ᵗ) 2 ≡ true
t1-pair₂ = refl

t1-reg : regD 2 8 3 T₁∞ᵗ ≡ false
t1-reg = refl

t2-reg : regD 2 8 3 T₂Ωᵗ ≡ false
t2-reg = refl

slow-reg : regD 2 8 3 (toTr (slowt 2)) ≡ false
slow-reg = refl
```
