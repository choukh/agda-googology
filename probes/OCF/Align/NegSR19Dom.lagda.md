# 第十九轮的否定 (四): `DomZ` 的封闭性: 右边 `⊕` 封闭; `cv` 不封闭 (一般状态); 累计分量由 "累计 ≤ 自己的读数" 加传递性给出

> 不读记号. 入口 [NegSR19](NegSR19.lagda.md). 对着接口 [StrRel19If](StrRel19If.lagda.md) (定稿 2026-11-05 16:01) §3–§4 的 `OA⁺⁺`, `DomZ` 写. §1–§2 对一切 $\Lambda$, §3–§4 在 $\Lambda_2=2$ 上.
>
> 1. **(定理) `domZ⊕`**: `DomZ Y₀` 对右边再折叠状态向右加一段 (`Y′ ⊕ Δ′`) 封闭. 所以折叠的 `Run` 在同一世界里推进状态 (`⨾`, `nl`, 链) 时 `DomZ` 保持.
> 2. **(定理) `InvZ`, `invZ₀`, `invZcv`, `invZ⊕`**: 单个状态的不变量 "累计 $\le$ 自己在 $\tau_0$ 上的读数" (`RelX⁺⁺ hz hz`). 空状态与 `cv` 之后的状态满足它 (累计是 `n0`); `⊕` 保持它, 条件是加上的一段在 $\tau_0$ 上的读数与自己相关 (自反; 第 $0$ 层不含 `nw` 时总成立, 一般的 `nw` 要对齐的自反, 本文没有证).
> 3. **(条件定理, 条件 `Trans00⁺⁺`) `domZ-z`**: 若第 $0$ 层的 `RelX⁺⁺` 传递, 则 `DomZ` 的累计分量由三件事推出: 产生状态满足 `InvZ`, 差分量 (`OA⁺⁺ (d Y₀) (d Y′)`), 两个 $\tau_0$ 是 `TX` 对. 也就是说, 在满足 `InvZ` 的产生状态上, `DomZ` 比 `DomL` 去掉累计分量**不多要求什么**; 经 `cv` 的再折叠, 问题只剩差分量.
> 4. **(否定) `¬cvClosedZ`**: "`DomZ Y₀` 对右边再折叠状态的 `cv` 封闭" 对一般状态不成立. 反例: 右边状态 $Y_B$ 在世界 $0$ 的 $\tau_0$ 上读数大, 在世界 $1$ 的第 $0$ 层目标上读数只有 $\omega\cdot(1⨾0)$; `cv` 到世界 $1$ 之后读数变小. 产生状态的累计 $\omega+1$ 大于自己的读数 $\omega$, **不满足** `InvZ` (`¬invZ-Y₀`); 所以第 4 条与第 3 条不冲突.
> 5. **(定理) `domZY₁`, `domZ-cvY₁`**: 闭项的状态 $Y_1=Y_0\oplus\mathrm{Step}\,Y_0$ 满足 `InvZ`; `DomZ Y₁` 在 $(\,\cdot\,,Y_1)$ 上成立, 并且对 $Y_1$ 的任意 `cv` (任意路径, 任意世界) 也成立.
>
> **构造一路为什么需要这些.** `RkSoundZ`, `UpSoundZ`, `OblRRZ` 的结论只对满足 `DomZ` 的再折叠给出; 节点的语义沿链推进状态 (要第 1 条), 节点的分支、`nκ` 的格、`Kp`, `Kb` 都先 `cv` 再运行 (要 "`DomZ` 经 `cv`"). `DomL` 在 `cv` 之后不成立 (`NegSR17Time.¬domCv`); `DomZ` 的设计意图是让它经 `cv` 成立. 第 4 条说它不是对一切状态自动成立的; 第 3 条说加上不变量 `InvZ` 与 `Trans00⁺⁺` 后, 缺的只是差分量经 `cv` 的封闭 (判断: 那是 `TX` 对的对齐 `CP` 能否把右边的基础世界换小, `StrRel12Al.adm-lo` 给出 `Adm` 的一半, `Al` 的一半没有看).
>
> **只否定什么.** 第 4 条只否定无条件的 `CvClosedZ` (对一切产生状态与再折叠状态). 不否定 "产生状态满足 `InvZ`" 或 "再折叠状态的第 $0$ 层读数不依赖目标的世界" 之下的 `cv` 封闭 (第 3, 5 条是这一方向的正面结果). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** 第 4 条: `DomZ YB₀` 在 $(Y_B, Y_B)$ 上成立 (`domB`: 差分量由 `pr⁺⁺` 与 $\Omega$ 的比较, 累计分量由 `in⁺⁺`, `NE` 由 `left here`). 第 3 条的条件 `Trans00⁺⁺`: 本路没有实例 (构造一路对 `RelX⁺` 证明了 `StrRel18Tr.trans00⁺`; 判断: 右层为 $0$ 时 `up`, `rk⁺⁺` 都不出现, 可以照搬); 其余前提由第 5 条的 $Y_1$ 满足.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR19Dom where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; irr)
open import OCF.Align.HtFeedTree using (H; LgH; hz; D; D₀; n0; n1; _⨾_; nl; Ωd; sum; pt)
open import Data.Nat using (zero; suc)
open import OCF.Align.StrRel13Val using (Λ₂)
import OCF.Align.StrRel14J as J14
import OCF.Align.StrRel15If as If²
import OCF.Align.StrRel16If as If³
import OCF.Align.StrRel19If as If⁵
open import OCF.Align.StrRel15Fin using (fin⊲)
open import OCF.Align.StrRel16Lem using (sum-mono)
open import OCF.Align.NegSR19Lem using (module V0⁺⁺; module Fin⁺⁺)
```

## 1–2 一切 $\Lambda$: `⊕` 封闭; 不变量 `InvZ`; 累计分量的来源

```agda
module Gen (Λ : H) (lΛ : LgH Λ) where
  open If⁵ Λ lΛ
  open If² Λ lΛ using (TX)
  open If³.P Λ lΛ using (Tg; τ₀; St; st; Df; yc; d; z; cv; zeroD; _⊕⟨_⟩_)

  domZ⊕ : ∀ {W₀ W W′} {lW₀ : Lg W₀} {Y₀ : St W₀} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} →
          DomZ lW₀ Y₀ lW lW′ Y Y′ → ∀ (Δ′ : Df W′) → DomZ lW₀ Y₀ lW lW′ Y (Y′ ⊕⟨ lW′ ⟩ Δ′)
  domZ⊕ {lW′ = lW′} {Y′ = Y′} ((oa , rz) , (ne₀ , ne′)) Δ′ =
    ((λ T T′ tx → pr⁺⁺ (oa T T′ tx)) , pr⁺⁺ rz) , (ne₀ , J14.ne⊕ Λ lΛ {lW = lW′} Y′ Δ′ ne′)

  -- 单个状态: 累计 ≤ 自己在 τ₀ 上的读数
  InvZ : ∀ {W} → Lg W → St W → Set
  InvZ lW Y = RelX⁺⁺ hz hz lW lW (z Y) (yc (d Y) (τ₀ lW))

  invZ₀ : ∀ {W} (lW : Lg W) → InvZ lW (st zeroD n0)
  invZ₀ lW = n0⁺⁺

  invZcv : ∀ {W W₂} (q : W ⊲ W₂) (lW₂ : Lg W₂) (Y : St W) → InvZ lW₂ (cv q Y)
  invZcv q lW₂ Y = n0⁺⁺

  invZ⊕ : ∀ {W} (lW : Lg W) (Y : St W) (Δ : Df W) → InvZ lW Y → RelX⁺⁺ hz hz lW lW (yc Δ (τ₀ lW)) (yc Δ (τ₀ lW)) → InvZ lW (Y ⊕⟨ lW ⟩ Δ)
  invZ⊕ lW Y Δ h r = ⨾⁺⁺ h r

  Trans00⁺⁺ : Set
  Trans00⁺⁺ = ∀ {V V′ V″} {lV : Lg V} {lV′ : Lg V′} {lV″ : Lg V″} {x : D₀ V} {y : D₀ V′} {x″ : D₀ V″} →
              RelX⁺⁺ hz hz lV lV′ x y → RelX⁺⁺ hz hz lV′ lV″ y x″ → RelX⁺⁺ hz hz lV lV″ x x″

  -- DomZ 的累计分量: 由 InvZ, 差分量, τ₀ 的 TX 对, 第 0 层的传递性推出
  domZ-z : Trans00⁺⁺ → ∀ {W₀ W′} {lW₀ : Lg W₀} {lW′ : Lg W′} {Y₀ : St W₀} {Y′ : St W′} →
           InvZ lW₀ Y₀ → OA⁺⁺ lW₀ lW′ (d Y₀) (d Y′) → TX lW₀ lW′ (τ₀ lW₀) (τ₀ lW′) →
           RelX⁺⁺ hz hz lW₀ lW′ (z Y₀) (yc (d Y′) (τ₀ lW′))
  domZ-z tr {lW₀ = lW₀} {lW′} iz oa tx = tr iz (oa (τ₀ lW₀) (τ₀ lW′) tx)
```

## 3 $\Lambda_2$: 一般状态上 `cv` 不封闭

```agda
open If⁵ Λ₂ tt
open If³.P Λ₂ tt using (Tg; tg; wm; tm; τ₀; St; st; Df; df; yc; d; z; cv; zeroD; Step; _⊕⟨_⟩_)
open V0⁺⁺ Λ₂ tt using (vsum⁺⁺)
open Fin⁺⁺ Λ₂ tt tt using (ΩRX⁺⁺; dN; Ys; oaN; neN)
open Gen Λ₂ tt using (InvZ)

ωR : D₀ azero
ωR = nl (λ _ → n1 ⨾ n0)

big : D₀ azero
big = ωR ⨾ n1

-- 只在世界 0 的第 0 层目标 (路径 self) 上多读 big
ex : ∀ {t m} → azero ⊲ m → D t m
ex {t = hz} C.self = big
ex _ = n0

dB : Df azero
dB = df (λ {t} T → yc dN T ⨾ ex (wm T))

YB : St azero
YB = st dB n0

YB₀ : St azero
YB₀ = Ys big

reflBig : RelX⁺⁺ hz hz {azero} {azero} tt tt big big
reflBig = ⨾⁺⁺ (nl⁺⁺ (λ _ → ⨾⁺⁺ n1⁺⁺ n0⁺⁺)) n1⁺⁺

domB : DomZ tt YB₀ {azero} {azero} tt tt YB YB
domB = ((λ T T′ tx → pr⁺⁺ (oaN T T′ tx)) , in⁺⁺ reflBig (If³.inR here)) , (neN big , (λ T → n0 , J14.left J14.here))
  where open If³ Λ₂ tt using (here)

CvClosedZ : Set
CvClosedZ = ∀ {W₀ W W′ W₂} (lW₀ : Lg W₀) (Y₀ : St W₀) (lW : Lg W) (lW′ : Lg W′) (lW₂ : Lg W₂) (Y : St W) (Y′ : St W′) (q : W′ ⊲ W₂) →
            DomZ lW₀ Y₀ lW lW′ Y Y′ → DomZ lW₀ Y₀ lW lW₂ Y (cv q Y′)

sumBig : asuc (sum azero ωR) ≤ sum azero big
sumBig = ≤-refl _

-- 世界 1 上的同一棵树, 和相同
ωR₁ : D₀ (asuc azero)
ωR₁ = nl (λ _ → n1 ⨾ n0)

sumω₁ : sum azero ωR₁ ≤ sum azero ωR
sumω₁ = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt azero (λ _ → n1 ⨾ n0) n ≤ pt azero (λ _ → n1 ⨾ n0) n
  go zero = ≤-refl azero
  go (suc n) = s≤ (go n)

-- cv 到世界 1: 读数只剩 ωR ⨾ n0
¬cvClosedZ : ¬ CvClosedZ
¬cvClosedZ h = irr (sum azero ωR) (≤-trans sumBig (≤-trans (vsum⁺⁺ (proj₂ (proj₁ (h tt YB₀ tt tt tt YB YB (C.suc C.self) domB))) (≤-refl azero)) sumω₁))

-- 反例的产生状态不满足 InvZ
¬invZ-Y₀ : ¬ InvZ tt YB₀
¬invZ-Y₀ r = irr (sum azero ωR) (≤-trans sumBig (vsum⁺⁺ r (≤-refl azero)))
```

## 4 闭项的状态 $Y_1$

```agda
Y₁ : St azero
Y₁ = st zeroD n0 ⊕⟨ tt ⟩ Step (st zeroD n0)

invZY₁ : InvZ tt Y₁
invZY₁ = ⨾⁺⁺ n0⁺⁺ (nl⁺⁺ (λ _ → ⨾⁺⁺ n1⁺⁺ n0⁺⁺))

neY₁ : J14.NE Λ₂ tt Y₁
neY₁ T = n0 , J14.rgt0 J14.here

-- 右边是 Y₁ 本身
domZY₁ : ∀ {W} (lW : Lg W) (Y : St W) → DomZ tt Y₁ lW tt Y Y₁
domZY₁ lW Y =
  ((λ T T′ tx → ⨾⁺⁺ n0⁺⁺ (nl⁺⁺ (λ _ → ⨾⁺⁺ (ΩRX⁺⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺⁺))) , invZY₁) , (neY₁ , neY₁)

-- 右边是 Y₁ 经任意 cv
domZ-cvY₁ : ∀ {W W₂} (lW : Lg W) (Y : St W) (q : azero ⊲ W₂) (lW₂ : Lg W₂) → DomZ tt Y₁ lW lW₂ Y (cv q Y₁)
domZ-cvY₁ lW Y q lW₂ =
  ((λ T T′ tx → ⨾⁺⁺ n0⁺⁺ (nl⁺⁺ (λ _ → ⨾⁺⁺ (ΩRX⁺⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺⁺))) ,
   ⨾⁺⁺ n0⁺⁺ (nl⁺⁺ (λ _ → ⨾⁺⁺ n1⁺⁺ n0⁺⁺))) ,
  (neY₁ , J14.necv Λ₂ tt q Y₁ neY₁)
```
