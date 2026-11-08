# 上下文读回的一步后继扩张

本篇复用既有 `LvRdPkg.RG`，不重新实现运行器。不含记号。
这里的参数不是任意合法高度：原层必须有在任意种类嵌入下仍可用的
节点解释，以及原坐标树的编码。全有限层的实例直接取旧 `NF`。
结论保留新增种类的完整坐标类型 `HB T`；不声称迁回保值、内部 View
或全极限高度已经解决，也不把固定双事件世界改称全种类事件系统。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformReaderStep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
  using (Ht; D; Wd₂; LgW₂; StH; ss; sl; sL; Vs; inC; n1; ni)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.FamFoldRead using (ly)
open import OCF.Align.FamFoldLift using (≤r; le0; le1)
open import OCF.Align.LvRdIf using (RdC)
open import OCF.Align.LvRdEmb
open import OCF.Align.LvRdPkg using (NdI; pkgF; RdF)

record ContextReader (T : KS) (L : Ht) : Set₁ where
  field
    nodes : ∀ {V} → Emb T V → NdI V L
    encode : ∀ {W} → HB T → D L W

module Extend {T L} (P : ContextReader T L) {V} (e : Emb (step T) V) where
  open ContextReader P
  old : NdI V L
  old = nodes (compE (inj₁E T) e)

  branch : ∀ {W k} (q : k ⊲[ W ] L) → HB V →
           (D k W → HB V → HB V) → HB V
  branch hself b s = nodeH e b (λ x h → s (encode x) h)
  branch (hsuc q) b s = NdI.ndR old (ss q) b (λ y h → s (out y) h)
    where
    open import OCF.Align.HtTowerFTree using (outC)
    out = outC q
  branch (hlim n q) b s = NdI.ndR old (sl n q) b (λ y h → s (out y) h)
    where
    open import OCF.Align.HtTowerFTree using (outC)
    out = outC q
  branch (hLim d q) b s = NdI.ndR old (sL d q) b (λ y h → s (out y) h)
    where
    open import OCF.Align.HtTowerFTree using (outC)
    out = outC q

  first : ∀ {W k} (q : k ⊲[ W ] L) b s {w} → b ⊲[ w ] branch q b s
  first hself b s = fst-nodeH e b _
  first (hsuc q) b s = NdI.fsR old (ss q) b _
  first (hlim n q) b s = NdI.fsR old (sl n q) b _
  first (hLim d q) b s = NdI.fsR old (sL d q) b _

  legal : ∀ {W k} (q : k ⊲[ W ] L) {b s} →
          (∀ y h {w} → h ⊲[ w ] s y h) → LgB b →
          (∀ y h → LgB h → LgB (s y h)) → LgB (branch q b s)
  legal hself fs lb ls = Lg-nodeH e (λ x h → fs _ h) lb (λ x h → ls _ h)
  legal (hsuc q) fs lb ls = NdI.lgR old (ss q) (λ y h → fs _ h) lb (λ y h → ls _ h)
  legal (hlim n q) fs lb ls = NdI.lgR old (sl n q) (λ y h → fs _ h) lb (λ y h → ls _ h)
  legal (hLim d q) fs lb ls = NdI.lgR old (sL d q) (λ y h → fs _ h) lb (λ y h → ls _ h)

  next : NdI V (hs L)
  next = record
    { ndR = λ { (ss q) b s → branch q b (λ y h → s (inC q y) h) }
    ; fsR = λ { (ss q) b s → first q b _ }
    ; lgR = λ { (ss q) fs lb ls → legal q (λ y h → fs _ h) lb (λ y h → ls _ h) }
    ; eA = NdI.eA old ; eM = NdI.eM old }

reader : ∀ {T L} → ContextReader T L →
         ∀ {W} → LgW₂ W → HB (step T) → D (hs L) W → HB (step T)
reader {T} P = OCF.Align.LvRdPkg.RG.rdG (Extend.next P (idE (step T)))
```

## 全有限层的实际前提，不另造阶段运行器

```agda
finite : ∀ n → ContextReader (Sk (suc n)) (ly (suc (suc n)))
finite n = record
  { nodes = λ o → record
    { ndR = λ { (ss q) b s → OCF.Align.LvRdPkg.NF.ndF (pkgF n) o ≤r q b (λ y h → s (inC q y) h) }
    ; fsR = λ { (ss q) b s → OCF.Align.LvRdPkg.NF.fsF (pkgF n) o ≤r q b _ }
    ; lgR = λ { (ss q) fs lb ls → OCF.Align.LvRdPkg.NF.lgF (pkgF n) o ≤r q (λ y h → fs _ h) lb (λ y h → ls _ h) }
    ; eA = compE (lePE (le0 (suc n))) o
    ; eM = compE (lePE (le1 n)) o }
  ; encode = RdC.tr (RdF (suc n)) }

-- 原 ni 的完整坐标反馈。这里 u 不是常函数；它接收实际编码 x。
feedback : ∀ {T L} (P : ContextReader T L) {W} (lW : LgW₂ W)
  (b : HB (step T))
  (u : ∀ {W′} → W OCF.Align.HtTowerFTree.≤ W′ → LgW₂ W′ → D L W′ → D (hs L) W′) →
  reader P lW b (ni (ss hself) u) ≡
  nodeH (idE (step T)) b (λ x h → reader P lW h (u OCF.Align.HtTowerFTree.≤rf lW (ContextReader.encode P x)))
feedback P lW b u = refl
```

这是后继一步的精确构造子方程，对所有原回调 `u` 成立，不是只测试一个输入。
`finite n` 实填全部自然数参数的上下文解释与编码。继续到任意结构高度时，
还必须构造下一层编码以及极限处的上下文解释；本篇不以它们为已完成。

## 实际非零反馈族

把原回调取为一次增量 `n1` 后，读回仍保留完整新增 Ω 分支，
在坐标 `0` 与 `1` 处分別返回底与底的后继。不是固定取底分支。

```agda
tick : ∀ {T L} (P : ContextReader T L) {W} → D (hs L) W
tick P = ni (ss hself) (λ _ _ _ → n1)

tick-equation : ∀ {T L} (P : ContextReader T L) {W} (lW : LgW₂ W) b →
  reader P lW b (tick P) ≡
  hΩ (inj₂ tt) (λ x → nbHG (idE (step T)) b (λ _ h → hs h) x)
tick-equation P lW b = refl

tick-one : ∀ {T L} (P : ContextReader T L) (b : HB (step T)) →
  nbHG (idE (step T)) b (λ _ h → hs h) (hs hz) ≡ hs b
tick-one P b = refl

tick-legal : ∀ {T L} (P : ContextReader T L) {W} (lW : LgW₂ W) b →
  LgB b → LgB (reader P lW b (tick P))
tick-legal {T} P lW b lb =
  OCF.Align.LvRdPkg.RG.lgG (Extend.next P (idE (step T))) lW b (tick P) lb

-- 所有 n 的真实原读回层均有上述非零反馈，而非一个第三事件样本。
finite-tick : ∀ n {W} (lW : LgW₂ W) → HB (Sk (suc (suc n)))
finite-tick n lW = reader (finite n) lW hz (tick (finite n))

finite-tick-legal : ∀ n {W} (lW : LgW₂ W) → LgB (finite-tick n lW)
finite-tick-legal n lW = tick-legal (finite n) lW hz tt
```
