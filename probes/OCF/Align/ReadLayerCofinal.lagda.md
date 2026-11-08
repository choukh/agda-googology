# 分支后继的字面覆盖给出极限中的新种类位置

接续 [读回层的边界](ReadLayerBoundary.lagda.md)。若一个族给出实际
路径，保证每一分支的后继进入某个后续分支，就能在族的并里容纳
该分支的完整新增种类。这里复用旧 Emb 的恒等、后继、并和复合，
不判定裸下标，不合并拷贝，也不要求任意合法极限具有这个性质。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ReadLayerCofinal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvRdEmb using (Emb; idE; inj₁E; ιE; compE)

-- 只沿已有的字面位置构造；Ω 步的坐标和 Bd 见证已经给定。
along : ∀ {S : KS} {w : Wd S} {a b : HB S} →
  a ⊲[ w ] b → Emb (Lev a) (Lev b)
along {S} {a = a} hself = idE (Lev a)
along {S} {b = hs b} (hsuc p) = compE (along {S} p) (inj₁E (Lev b))
along {S} {b = hl f} (hlim n p) = compE (along {S} p) (ιE {ℕ} {λ n → Lev (f n)} n)
along {S} {b = hΩ κ g} (hLim {c = c} e p) = compE (along {S} p) (ιE {E S κ} {λ c → Lev (g c)} c)

record SuccessorCover {S : KS} (I : Set) (f : I → HB S) (w : Wd S) : Set where
  field
    next : (i : I) → Σ I (λ j → hs (f i) ⊲[ w ] f j)

-- 输出保留整个 HB(Lev(f i)) 坐标类型，不把它降回固定 Ht。
new-kind : ∀ {S : KS} {I : Set} {f : I → HB S} {w : Wd S} →
  SuccessorCover {S} I f w → ∀ i →
  Emb (step (Lev (f i))) (sup I (λ j → Lev (f j)))
new-kind {S} {I} {f} c i = compE (along {S} (proj₂ (SuccessorCover.next c i)))
                     (ιE {I} {λ j → Lev (f j)} (proj₁ (SuccessorCover.next c i)))

-- 结构参数实例：任意底树 x，反复取后继，而非只从有限数 0 出发。
tower : ∀ {S : KS} → HB S → ℕ → HB S
tower x zero = x
tower x (suc n) = hs (tower x n)

tower-cover : ∀ {S : KS} (x : HB S) (w : Wd S) → SuccessorCover ℕ (tower x) w
tower-cover x w = record { next = λ n → suc n , hself }

tower-kind : ∀ {S : KS} (x : HB S) (w : Wd S) n →
  Emb (step (Lev (tower x n))) (sup ℕ (λ j → Lev (tower x j)))
tower-kind x w = new-kind (tower-cover x w)
```

这个定理提供旧读回包泛化所需的一项充分结构信息，不是完整 reader。
尤其没有给定源世界到不同分量世界的相干更新、编码闭包或折叠模拟。
路径的存在是条件；tower-cover 实填该条件，不能将其升级成每个
合法 ℕ-极限自动成立，更不能以它要求树的所有基本列按值严格递增。
