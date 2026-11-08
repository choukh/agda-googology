# 新运行的遗传严格性只需实际观察子树

在 target0，闭包的 seed 和反馈坐标影响所选观察子树，却不必本身
带 SV：只要所有可能被选中的观察子树均有本证书，实际运行就有 SV。
后继展开的原零起加法迭代也保留。该证书用于证明实际生成性，
不改变生产算法或追加原运行的输入前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailHighRegular (S : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ordˢ; Ord₊ˢ; toZ; _+ˢ_)
open import OCF.Align.TotalValueBuildStrict using (SV; svz; svs; SV-≅)
open import OCF.Align.TotalValueBuildRunStrict using (complete-sv; positive)
import OCF.Align.TotalValueNegPositive S as P
import OCF.Align.TotalValueTraceShape as Trace
import OCF.Free.TotalOrbitRun as R

-- 所有量化的坐标都仍带该节点自己的实际 c⊑η。
data Regular : Ordˢ zero → Set where
  rz : Regular Ord₊ˢ.zero
  rs : ∀ {a} → Regular a → Regular (Ord₊ˢ.suc a)
  rl : ∀ {f} → (∀ n → Regular (f n)) →
    (∀ n → P.Positive (toZ (f (suc n)))) → Regular (Ord₊ˢ.lim f)
  rsh : ∀ {c t g} → Regular t → (∀ η e → Regular (g η e)) →
    (∀ η e → P.Positive (toZ (g η e))) → Regular (Ord₊ˢ.ŝ c t g)
  rc : ∀ {c t g o₀ o} → Regular o₀ → (∀ η e → Regular (o η e)) →
    (∀ η e → P.Positive (toZ (o η e))) → Regular (Ord₊ˢ.ĉᴸ c t g o₀ o)

right-positive : ∀ (a b : Ordˢ zero) → P.Positive (toZ b) → P.Positive (toZ (a +ˢ b))
right-positive a Ord₊ˢ.zero ()
right-positive a (Ord₊ˢ.suc b) P.ps = P.ps
right-positive a (Ord₊ˢ.lim f) (P.pl n p) = P.pl n (right-positive a (f n) p)
right-positive a (Ord₊ˢ.limᵢ () f) p
right-positive a (Ord₊ˢ.up () x) p
right-positive a (Ord₊ˢ.ŝ c t g) (P.pc p) = P.pc (right-positive a t p)
right-positive a (Ord₊ˢ.ĉᴸ c t g o₀ o) (P.pc p) = P.pc (right-positive a o₀ p)

left-positive : ∀ (a b : Ordˢ zero) → P.Positive (toZ a) → P.Positive (toZ (a +ˢ b))
left-positive a Ord₊ˢ.zero p = p
left-positive a (Ord₊ˢ.suc b) p = P.ps
left-positive a (Ord₊ˢ.lim f) p = P.pl zero (left-positive a (f zero) p)
left-positive a (Ord₊ˢ.limᵢ () f) p
left-positive a (Ord₊ˢ.up () x) p
left-positive a (Ord₊ˢ.ŝ c t g) p = P.pc (left-positive a t p)
left-positive a (Ord₊ˢ.ĉᴸ c t g o₀ o) p = P.pc (left-positive a o₀ p)

add-regular : ∀ {a b} → Regular a → Regular b → Regular (a +ˢ b)
add-regular pa rz = pa
add-regular pa (rs pb) = rs (add-regular pa pb)
add-regular {a} pa (rl {f} pb pos) = rl (λ n → add-regular pa (pb n))
  (λ n → right-positive a (f (suc n)) (pos n))
add-regular {a} pa (rsh {g = g} pt pg pos) = rc (add-regular pa pt)
  (λ η e → add-regular pa (pg η e)) (λ η e → right-positive a (g η e) (pos η e))
add-regular {a} pa (rc {o = o} pt pg pos) = rc (add-regular pa pt)
  (λ η e → add-regular pa (pg η e)) (λ η e → right-positive a (o η e) (pos η e))

iter-regular : ∀ {a} → Regular a → ∀ n → Regular (iter (a +ˢ_) Ord₊ˢ.zero n)
iter-regular p zero = rz
iter-regular p (suc n) = add-regular p (iter-regular p n)
repeat-regular : ∀ {a} → Regular a → P.Positive (toZ a) →
  Regular (Ord₊ˢ.lim (iter (a +ˢ_) Ord₊ˢ.zero))
repeat-regular {a} p pos = rl (iter-regular p)
  (λ n → left-positive a (iter (a +ˢ_) Ord₊ˢ.zero n) pos)

value : ∀ {a} → Regular a → SV (R.run (toZ a))
value rz = svz
value (rs p) = svs (value p)
value (rl {f} p pos) = complete-sv (λ n → R.run (toZ (f n)))
  (λ n → value (p n)) (λ n → positive (P.value (pos n)))
value (rsh {c} {t} {g} p q pos) = SV-≅ N.shape
  (complete-sv N.outputs output-regular pos-out)
  where
  module N = Trace.Node c (toZ t) (λ η e → toZ (g η e)) (toZ t) (λ η e → toZ (g η e))
  output-regular : ∀ n → SV (N.outputs n)
  output-regular zero = value p
  output-regular (suc n) = value (q (N.η n) (N.bound n))
  pos-out = λ n → positive (P.value (pos (N.η n) (N.bound n)))
value (rc {c} {t} {g} {o₀} {o} p q pos) = SV-≅ N.shape
  (complete-sv N.outputs output-regular pos-out)
  where
  module N = Trace.Node c t g (toZ o₀) (λ η e → toZ (o η e))
  output-regular : ∀ n → SV (N.outputs n)
  output-regular zero = value p
  output-regular (suc n) = value (q (N.η n) (N.bound n))
  pos-out = λ n → positive (P.value (pos (N.η n) (N.bound n)))
```
