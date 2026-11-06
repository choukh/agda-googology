# 有内容的下降 (六): 代入 `KD` 的下降与无条件闭项

> 不含记号. 入口 [DnFold](DnFold.lagda.md), 接口 [DnFoldIf](DnFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项与证书 (§3) 无模块参数.
>
> **下降 `dnD : DnTower` 分站写:**
>
> - **第 0 站, 层号 $1$**: `Lev 1 = S₁`, `HB S₁ = Ht`, 下降取恒等 (无损; 别的层号取截断版的常数).
> - **第 1 站, 一切层号 $b$** (`dn₁`): 经求值 (D1). 对每个 $N$: 层号经 `μ′` 搬进 `Ht` (保合法), 高度经桥 `F N b` 搬进带有限外层世界 $a_N=(N,N)$ 的层 `LvH a_N (μ′ b)`, 经 `DnFoldRd` 的翻译读成第 `LyH (μ′ b)` 层的数据树, `Run` 求到第 2 层, 读回到 `Ht` (`DnFoldEv.toDn`). 各 $N$ 的输出按部分和取 ℕ-极限 (合法由 `⊞-fst` 给出).
> - **第 2 站起与极限站**: 截断版的常数 (`KcFoldTower.dn₀`, `dnL₀`). 第 2 站起的层号的头的坐标是 `HB (Lev X_s)` (`KcFoldTower.Shape.coord-new`), 数据树的层在 `Ht`, 装不下 (`ht-coords`); 这一步没有写.
>
> **形状定理 (对这一个下降, `refl`)**: 第 0 站回灌输出就是读回本身 (`Hs0-rd`, 含新种类 κH 的 $\Omega$-结点); 第 1 站回灌输出是各 $N$ 的求值的部分和 (`Hs1`), 求值的输入是读回经桥的像 (`rd-kept`: 读回的新种类结点原样留下, 分支是 `F ∘ up ∘ G`), 翻译成数据树后是一个过第 `LyH (μ′ X₀)` 层的 `ni` 结点, 分支在每个世界 $W'$ 与数据 $y$ 上是把 $y$ 读回、经桥、嵌入再翻译 (`tr₁`). 截断版第 0 站的输出是 `Ωtop S₀`, 不等于本下降的 (`diffD`).
>
> **这些形状定理不说大小.** 否定一路的 `NegDnFoldBlind.dnC` 满足接口 §5 的全部忠实律而回灌输出恒为 $2$; 本篇排除它的只有 "第 0 站输出等于读回" 与第 1 站求值输入的形状, 都不是值的界. 第 2 站起与截断版相同 (`HsSS`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DnFoldK where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import Data.Empty using (⊥)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; LgW₂; ≤rf; ≤tr; ni; n1; _⨾_; outS)
open import OCF.Align.HtTowerFClosed using (ord)
open import OCF.Align.LvKtIf
open import OCF.Align.LvKtInst using (module TrK)
open import OCF.Align.KcFoldIf
open import OCF.Align.KcFoldTower using (module KD; module Shape; dn₀; dnL₀)
open import OCF.Align.DnFoldIf
open import OCF.Align.DnFoldEv
open import OCF.Align.DnFoldRd
open import OCF.Align.DnFoldDc using (lgLyH; o1H; e2-of; module TrShape)
open import OCF.Align.DnFoldMu
open import OCF.Align.DnFoldBr
```

## §1 部分和

```agda
sumH : (ℕ → Ht) → ℕ → Ht
sumH h zero = h 0
sumH h (suc n) = sumH h n ⊞ h (suc n)

Lg-sumH : ∀ h → (∀ n → LgB (h n)) → ∀ n → LgB (sumH h n)
Lg-sumH h l zero = l 0
Lg-sumH h l (suc n) = Lg-⊞ (sumH h n) (h (suc n)) (Lg-sumH h l n) (l (suc n))

Lg-hlH : ∀ h → (∀ n → LgB (h n)) → LgB (hl (sumH h))
Lg-hlH h l = (λ n → ⊞-fst (sumH h n) (h (suc n))) , Lg-sumH h l
```

## §2 第 1 站的下降

```agda
ev₁ : ℕ → (b : HB K1) → LgB b → DnEv (Lev b)
ev₁ N b lb = record
  { Lw = LyH (μ′ b) ; lLw = lgLyH (μ′ b) (Lg-μ′ b lb) ; o1 = o1H (μ′ b)
  ; Wv = Br.aN N ; lWv = Br.laN N ; ev2 = e2-of (one⊲ b)
  ; tr = λ x → Rd.trN (Br.aN N) (Rd.pk (Br.aN N) (μ′ b)) (mapP (Br.F N b) x) (Br.aN N) ≤rf }

dn₁ : (b : HB K1) → LgB b → DnK (Lev b)
dn₁ b lb = (λ x → hl (sumH (λ N → proj₁ (toDn (ev₁ N b lb)) x)))
         , (λ x lx → Lg-hlH (λ N → proj₁ (toDn (ev₁ N b lb)) x) (λ N → proj₂ (toDn (ev₁ N b lb)) x lx))

dnD : DnTower
dnD zero (hs hz) lb = (λ x → x) , (λ x l → l)
dnD zero b lb = dn₀ zero b lb
dnD (suc zero) b lb = dn₁ b lb
dnD (suc (suc s)) b lb = dn₀ (suc (suc s)) b lb
```

## §3 无条件闭项

```agda
module KQ = KD dnD dnL₀

TD : A
TD = KQ.TΛ∞ω

Lg-TD : Lg TD
Lg-TD = KQ.Lg-TΛ∞ω

fghD : ℕ → ℕ
fghD = FLv.FGH (ord TD)

TD∞ : A
TD∞ = KQ.TΛ∞

Lg-TD∞ : Lg TD∞
Lg-TD∞ = KQ.Lg-TΛ∞
```

## §4 形状定理

```agda
-- 第 0 站: 回灌输出就是读回 (第 1 级的级顶后加 1, 新种类 κH 的 Ω-结点)
Hs0-rd : KQ.Hs 0 ≡ KQ.rts 0
Hs0-rd = refl

Hs0-shape : KQ.Hs 0 ≡ hs (Ωtop S₀)
Hs0-shape = refl

-- 与截断版不同 (第 0 站)
diffD : DiffTkc dnD dnL₀
diffD = 0 , (λ ())

-- 第 0 站的下降忠实 (接口 §5; 它是恒等, 有左逆)
faith0D : Faith0 dnD
faith0D e = hs≢ (cong pick e)
  where
  pick : Ht → Ht
  pick (hs (hΩ (inj₂ tt) g)) = g (hs hz)
  pick _ = hz
  hs≢ : ¬ (hs (hz {S₁}) ≡ hz)
  hs≢ ()

-- 第 1 站: 各 N 的求值的部分和
X₀ : HB (Kc 1)
X₀ = Shape.X dnD dnL₀ 0

H1N : ℕ → Ht
H1N N = proj₁ (toDn (ev₁ N (KQ.B 1) (KQ.lB 1))) (KQ.rts 1)

Hs1 : KQ.Hs 1 ≡ hl (sumH H1N)
Hs1 = refl

-- 求值的输入: 读回的新种类结点原样留下, 分支是 F ∘ up ∘ G
module _ (N : ℕ) where
  private
    a = Br.aN N
    T₁ = LvH a (μ′ (KQ.B 1))
    T₀ = LvH a (μ′ X₀)
    FB = mapP {Lev (KQ.B 1)} {T₁} (Br.F N (KQ.B 1))
    G0 = mapP {T₀} {Lev X₀} (Br.G N X₀)

  rd-kept : FB (KQ.rts 1) ≡ hs (hΩ (inj₂ tt) (λ z → FB (up {Lev X₀} (G0 z))))
  rd-kept = refl

  -- 翻译成数据树: 过第 LyH (μ′ X₀) 层的 ni 结点, 分支读回数据, 经桥与嵌入再翻译
  tr₁ : Rd.trN a (Rd.pk a (μ′ (KQ.B 1))) (FB (KQ.rts 1)) a ≤rf ≡
        ni (TrShape.R₀ a (μ′ X₀))
           (λ {W′} p lW′ y → Rd.trN a (Rd.pk a (μ′ (KQ.B 1)))
              (FB (up {Lev X₀} (G0 (Rd.rdc a (Rd.pk a (μ′ X₀)) W′ ≤rf lW′ (≤tr ≤rf p) hz (outS (TrShape.R₀ a (μ′ X₀)) y)))))
              W′ (≤tr ≤rf p))
        ⨾ n1
  tr₁ = refl

-- 第 2 站起与截断版相同
HsSS : ∀ s → KQ.Hs (suc (suc s)) ≡ TrK.Hs (suc (suc s))
HsSS s = refl
```

## §5 有限测试 (桥的可入判定)

`decH N y` 只在 $y$ 字面地是有限的 $k\le N$ 时给出证据. 测试, 不是证明.

```agda
IsL : ∀ {X Y : Set} → X ⊎ Y → Set
IsL (inj₁ _) = ⊤
IsL (inj₂ _) = ⊥

-- 有限下标 1 ≤ 2: 留下
t-keep : IsL (decH 2 (hs hz) {azero})
t-keep = tt

-- 下标 2 > 1: 丢掉
t-drop : ¬ IsL (decH 1 (hs (hs hz)) {azero})
t-drop ()

-- 下标 ω: 丢掉
t-dropω : ¬ IsL (decH 5 (hl (λ n → hz)) {azero})
t-dropω ()
```
