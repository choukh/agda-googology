# 级回灌参数 `Fb`, 否定一路 (二): 闭包结点的种类只来自目标层的头 (折叠的数据不变式)

> 不含记号. 入口 [NegLeanFb](NegLeanFb.lagda.md). 本篇**不依赖**构造一路的接口, 只读导入 [LeanTTree](LeanTTree.lagda.md), [LeanTFold](LeanTFold.lagda.md), [LeanT](LeanT.lagda.md) 与 [NegLeanFbPre](NegLeanFbPre.lagda.md) 的 `AllK`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.
>
> **问题.** [LeanT](LeanT.lagda.md) §3 判断 "`TΛ′` 不经过新种类的回灌 `κc₁`", 依据是 `old-target` (定理) 加 "闭包结点的种类只由 `Ωd` 生出, 其余各行只复制已有闭包结点的种类" (读代码). [NegLeanFbPre](NegLeanFbPre.lagda.md) §2 的 "回灌行在 $\kappa$ 上执行 ⇒ $\kappa$ 是 $\Lambda$ 的某个第一位置的头" 也停在同一个判断上. 本篇把这个判断写成定理.
>
> **结果.**
>
> 1. **`KD P L x`** (数据上的谓词): 数据 $x$ 里每个闭包结点 `nc κ` 的种类满足 $P$, 沿一切分支 (`ni` 的分支对一切满足 `KD` 的输入). **`kd-Run`** (定理, 对一切折叠参数 $T$, `bk`, $\Lambda$, `fb`, 一切 $P$ 与 $\Lambda$ 上的 `AllK P Λ`): 输入的数据, 累计数据, 状态, 动作都保 `KD`, 则 `Run` 在**每个**目标上的输出满足 `KD`. 同时证了 `Int`, `drp₁`, `Rpt`, `RunNi`, `Ai`, `Chn`, `RKi`, `BNi`, `RunC`, `RKc`, `RKk`, `κc₁`, `κΔ₁` 各一条. 第 $0$ 层的数据没有闭包结点也没有结点 (`kd-hz`), 所以有损行, 级回灌行 (`RKa`, `κcF`, `κΔA`) 的输出自动满足.
> 2. **`kd-Stp`** (定理): 闭项的动作 "当前状态的一步" (`Stp`) 保 `KD`, 只要 `AllK P Λ` (它在目标 $t$ 上发出 $\Omega_t$, 头种类由 `hd-target` 给出).
> 3. **`TΛ′-old`** (定理): 闭项 `TΛ′` 的折叠 (`LeanT.ΨΩ` 里的那一次 `Run`) 在每个目标上的输出里, 一切闭包结点都是旧种类 (`inj₁ _`). **`TΛ′-in`** (定理): 同一次 `Run` 的输入 `Ωd Λ′`, 初始状态都满足同一谓词.
>
> **读法 (判断, 一行).** 折叠的 `Run` 只在 `nc κ` 子句里调 `RunC ac κ …`, 再到 `RKc ac κ …`: 种类就是输入数据里那个闭包结点的种类. 所以 "新种类的回灌 `κc₁` 被执行" 要求某次 `Run` 的输入里有 `nc (inj₂ tt) …`; 一切 `Run` 的输入都是 `Ωd Λ′`, 状态里的数据, 或某次 `Run` 的输出 (满足 `KD`), 所以在 `TΛ′` 上不执行. 原来的判断里 "其余各行只复制已有闭包结点的种类" 一句, 现在是定理 `kd-Run`; 剩下的读法只是 `Run` 的 `nc` 子句的一行.
>
> **只说什么, 不说什么.** 只说闭包结点的种类被保持 (必要条件): 回灌行在 $\kappa$ 上执行, $\kappa$ 必须是 $\Lambda$ 里某个第一位置的头 (取 $P$ = "在 $\Lambda$ 里出现"). **不说**某个回灌行真被执行 (充分条件, 要沿一条具体路径计算折叠); 不说回灌的值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanFbKD where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
import OCF.Lean.LeanTFold as FoldM
open import OCF.Lean.NegLeanFbPre using (AllK; allK-⊲; hd-target)
```

## §1 数据上的谓词

```agda
module KDM (T : KS) (P : K (step T) → Set) where
  open Tree T

  KD  : ∀ L {W} → D L W → Set
  KDs : ∀ L {W k u} (R : StH W k L) → Vs L R u → Set
  KDc : ∀ b {W a u} (Q : a ⊲[ W ] b) → Vc b Q u → Set
  KD L n0 = ⊤
  KD L n1 = ⊤
  KD L (x ⨾ y) = KD L x × KD L y
  KD L (nl d) = ∀ n → KD L (d n)
  KD L (ni r u) = ∀ {W′} p lW′ v → KDs L r v → KD L (u {W′} p lW′ v)
  KD L (nc κ z u) = P κ × (∀ {W′} p lW′ → KD L (u {W′} p lW′))
  KD L (nw p x) = KD L x
  KDs (hs b) (ss Q) v = KDc b Q v
  KDs (hl f) (sl n Q) v = KDc (f n) Q v
  KDs (hΩ κ g) (sL e Q) v = KDc (g _) Q v
  KDc a hself v = KD a v
  KDc (hs b) (hsuc Q) v = KDc b Q v
  KDc (hl f) (hlim n Q) v = KDc (f n) Q v
  KDc (hΩ κ g) (hLim e Q) v = KDc (g _) Q v

  kdOutC : ∀ {b W a u} (Q : a ⊲[ W ] b) (x : Vc b Q u) → KDc b Q x → KD a (outC Q x)
  kdOutC hself x k = k
  kdOutC (hsuc Q) x k = kdOutC Q x k
  kdOutC (hlim n Q) x k = kdOutC Q x k
  kdOutC (hLim e Q) x k = kdOutC Q x k

  kdInC : ∀ {b W a u} (Q : a ⊲[ W ] b) (x : D a u) → KD a x → KDc b Q (inC Q x)
  kdInC hself x k = k
  kdInC (hsuc Q) x k = kdInC Q x k
  kdInC (hlim n Q) x k = kdInC Q x k
  kdInC (hLim e Q) x k = kdInC Q x k

  kdOutS : ∀ {L W k u} (R : StH W k L) (x : Vs L R u) → KDs L R x → KD k (outS R x)
  kdOutS (ss Q) x k = kdOutC Q x k
  kdOutS (sl n Q) x k = kdOutC Q x k
  kdOutS (sL e Q) x k = kdOutC Q x k

  kdInS : ∀ {L W k u} (R : StH W k L) (x : D k u) → KD k x → KDs L R (inS R x)
  kdInS (ss Q) x k = kdInC Q x k
  kdInS (sl n Q) x k = kdInC Q x k
  kdInS (sL e Q) x k = kdInC Q x k
```

**第 0 层的数据都满足** (没有结点, 没有闭包结点). **`drp₁` 保持**.

```agda
  kd-hz : ∀ {W} (x : D hz W) → KD hz x
  kd-hz n0 = tt
  kd-hz n1 = tt
  kd-hz (x ⨾ y) = kd-hz x , kd-hz y
  kd-hz (nl d) = λ n → kd-hz (d n)
  kd-hz (ni () u)
  kd-hz (nc (inj₁ _) () u)
  kd-hz (nc (inj₂ _) () u)
  kd-hz (nw p x) = kd-hz x

  kd-drp₁ : ∀ {w₀ x y} (l : LgW L₀ (w₀ , x)) (t : D (hs hz) (w₀ , x)) → KD (hs hz) t → KD (hs hz) (drp₁ {y = y} l t)
  kd-drp₁ l n0 k = tt
  kd-drp₁ l n1 k = tt
  kd-drp₁ l (a ⨾ b) (ka , kb) = kd-drp₁ l a ka , kd-drp₁ l b kb
  kd-drp₁ l (nl d) k = λ n → kd-drp₁ l (d n) (k n)
  kd-drp₁ {x = x} l (ni (ss hself) u) k = λ q lW″ z kz →
    kd-drp₁ (proj₁ lW″ , proj₂ l) (u (proj₁ q , hself) (proj₁ lW″ , proj₂ l) (drp z))
      (k (proj₁ q , hself) (proj₁ lW″ , proj₂ l) (drp z) (kd-hz (drp z)))
  kd-drp₁ {x = x} l (nc (inj₁ κ) z u) (pκ , k) = pκ , λ q lW″ →
    kd-drp₁ (proj₁ lW″ , proj₂ l) (u (proj₁ q , hself) (proj₁ lW″ , proj₂ l))
      (k (proj₁ q , hself) (proj₁ lW″ , proj₂ l))
  kd-drp₁ l (nc (inj₂ _) () u) k
  kd-drp₁ l (nw p t) k = kd-drp₁ (lgDn L₀ p l) t k
```

**输入改写 `Int` 保持.**

```agda
  kd-Pre : ∀ {L W₀ W} (q₀ : W₀ ≤ W) (d : ℕ → D L W₀) → (∀ n → KD L (d n)) → ∀ n → KD L (Pre q₀ d n)
  kd-Pre q₀ d k zero = tt
  kd-Pre q₀ d k (suc n) = kd-Pre q₀ d k n , k n

  kd-Int : ∀ {ly k W₀ W} (ac : AccY k) (x : D k W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (zy : ∀ κ → ZK k κ → ZK ly κ)
           (mk : ∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly)
           (u : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → D k W′ → D ly W′) (w : D k W) →
           KD k x → (∀ {W′} (p : W ≤ W′) l z → KD k z → KD ly (u p l z)) → KD k w → KD ly (Int ac x q₀ lW zy mk u w)
  kd-Int ac n0 q₀ lW zy mk u w kx ku kw = tt
  kd-Int ac n1 q₀ lW zy mk u w kx ku kw = ku ≤rf lW w kw
  kd-Int ac (x ⨾ y) q₀ lW zy mk u w (kx , ky) ku kw =
    kd-Int ac x q₀ lW zy mk u w kx ku kw , kd-Int ac y q₀ lW zy mk u (w ⨾ nw q₀ x) ky ku (kw , kx)
  kd-Int ac (nl d) q₀ lW zy mk u w kx ku kw =
    λ n → kd-Int ac (d n) q₀ lW zy mk u (w ⨾ Pre q₀ d n) (kx n) ku (kw , kd-Pre q₀ d kx n)
  kd-Int ac (nw p x) q₀ lW zy mk u w kx ku kw = kd-Int ac x (≤tr p q₀) lW zy mk u w kx ku kw
  kd-Int (acc g) (ni R v) q₀ lW zy mk u w kx ku kw = λ p lW′ y ky →
    kd-Int (acc g) (v (≤tr q₀ p) lW′ (inS R (outS (mk ≤rf (Kup q₀ R)) y))) ≤rf lW′ zy (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′))
      (nw p w ⨾ Int (g R) (outS (mk ≤rf (Kup q₀ R)) y) ≤rf lW′ (zkS R) (mkOf R (≤tr q₀ p))
                  (λ p′ l′ z′ → v (≤tr (≤tr q₀ p) p′) l′ (inS R z′)) n0)
      (kx (≤tr q₀ p) lW′ (inS R (outS (mk ≤rf (Kup q₀ R)) y))
          (kdInS R (outS (mk ≤rf (Kup q₀ R)) y) (kdOutS (mk ≤rf (Kup q₀ R)) y ky)))
      (λ p′ l z kz → ku (≤tr p p′) l z kz)
      (kw , kd-Int (g R) (outS (mk ≤rf (Kup q₀ R)) y) ≤rf lW′ (zkS R) (mkOf R (≤tr q₀ p))
              (λ p′ l′ z′ → v (≤tr (≤tr q₀ p) p′) l′ (inS R z′)) n0
              (kdOutS (mk ≤rf (Kup q₀ R)) y ky)
              (λ p′ l′ z′ kz′ → kx (≤tr (≤tr q₀ p) p′) l′ (inS R z′) (kdInS R z′ kz′)) tt)
  kd-Int ac (nc κ z v) q₀ lW zy mk u w (pκ , kx) ku kw = pκ , λ p lW′ →
    kd-Int ac (v (≤tr q₀ p) lW′) ≤rf lW′ zy (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′)) (nw p w)
      (kx (≤tr q₀ p) lW′) (λ p′ l z kz → ku (≤tr p p′) l z kz) kw
```

## §2 折叠保持

```agda
module KDRun (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ)
  (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (fb : K T → FoldTy.Fb T Λ ⊎ ⊤)
  (P : K (step T) → Set) (hΛ : AllK P Λ) where
  open Tree T
  open FoldTy T Λ
  open FoldM T bk Λ lΛ one⊲ fb
  open Rd bk
  open KDM T P

  KDf : ∀ {W} → Df W → Set
  KDf {W} Δ = ∀ {t m} (Tq : Tg W t m) → KD t (yc Δ Tq)

  KDS : ∀ {W} → St W → Set
  KDS Y = KDf (d Y) × KD (hs hz) (z₁ Y)

  KDI : ∀ {ly W} → Ig ly W → Set
  KDI {ly} {W} A₀ = ∀ {W′} (p : W ≤ W′) (lW′ : LgW L₀ W′) (v : D ly W′) (Y′ : St W′) → KD ly v → KDS Y′ → KDf (A₀ p lW′ v Y′)

  KDB : ∀ {ly W₀} → Bu ly W₀ → Set
  KDB {ly} {W₀} u = ∀ {W′} (p : W₀ ≤ W′) (lW′ : LgW L₀ W′) → KD ly (u p lW′)

  KDN : ∀ {ly W₀ k} (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′) → Set
  KDN {ly} {W₀} r u = ∀ {W′} (p : W₀ ≤ W′) (lW′ : LgW L₀ W′) v → KDs ly r v → KD ly (u p lW′ v)

  kd-zeroD : ∀ {W} → KDf (zeroD {W})
  kd-zeroD Tq = tt

  kd-⨾ᴰ : ∀ {W} {a b : Df W} → KDf a → KDf b → KDf (a ⨾ᴰ b)
  kd-⨾ᴰ ka kb Tq = ka Tq , kb Tq

  kd-nlᴰ : ∀ {W} {F : ℕ → Df W} → (∀ n → KDf (F n)) → KDf (nlᴰ F)
  kd-nlᴰ k Tq n = k n Tq

  kd-⊕ : ∀ {W} (Y : St W) (lW : LgW L₀ W) (Δ : Df W) → KDS Y → KDf Δ → KDS (Y ⊕⟨ lW ⟩ Δ)
  kd-⊕ Y lW Δ kY kΔ = kd-⨾ᴰ (proj₁ kY) kΔ , (proj₂ kY , kΔ (τ₁ lW))

  kd-cv : ∀ {W W′} (q : W ≤ W′) (Y : St W) → KDS Y → KDS (cv q Y)
  kd-cv q Y kY = (λ Tq → proj₁ kY (tg↑ q Tq)) , tt

  kd-Ig↾ : ∀ {ly W W′} (p : W ≤ W′) (A₀ : Ig ly W) → KDI A₀ → KDI (Ig↾ p A₀)
  kd-Ig↾ p A₀ kA p′ = kA (≤tr p p′)
```

**$\Omega_L$ 与动作 `Stp`.**

```agda
  kd-Ωd : ∀ L {W} → AllK P L → KD L (Ωd L {W})
  kd-Ωd hz a = tt
  kd-Ωd (hs b) a = tt , (λ p l v k → tt)
  kd-Ωd (hl f) a = tt , (λ n p l v k → tt)
  kd-Ωd (hΩ κ g) a = tt , (proj₁ a , (λ p l p′ l′ v k → tt))

  kd-Stp : ∀ {W} {Y : St W} → KDS Y → KDf (Stp Y)
  kd-Stp kY {t} Tq n = kd-Ωd t (allK-⊲ P (tm Tq) hΛ) , proj₁ kY Tq
```

**折叠的各行.** 与 [LeanTFold](LeanTFold.lagda.md) §4 一一对应, 停机同原来 (数据结构递归, 结点经 `AccY`).

```agda
  kd-Run   : ∀ {ly W₀ W} (ac : AccY ly) (x : D ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
             KD ly x → KDI A₀ → KD ly w → KDS Y → KDf (Run ac x q₀ lW lL A₀ w Y)
  kd-Rpt   : ∀ {ly W₀ W} (ac : AccY ly) (F : ℕ → D ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
             (∀ n → KD ly (F n)) → KDI A₀ → KD ly w → KDS Y → ∀ n →
             KD ly (proj₁ (Rpt ac F q₀ lW lL A₀ w Y n)) × KDS (proj₂ (Rpt ac F q₀ lW lL A₀ w Y n))
  kd-RunNi : ∀ {ly W₀ W k} (ac : AccY ly) (ac′ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′)
             (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
             KDN r u → KDI A₀ → KD ly w → KDS Y → KDf (RunNi ac ac′ r u q₀ lW lL A₀ w Y)
  kd-Ai    : ∀ {ly W₀ W k} (ac : AccY ly) (ac′ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′)
             (q₀ : W₀ ≤ W) (hk : LW k W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) →
             KDN r u → KDI A₀ → KD ly w → KDI (Ai ac ac′ r u q₀ hk lL A₀ w)
  kd-Chn   : ∀ {k W} (ac′ : AccY k) (hk : LW k W) (lW : LgW L₀ W) (A² : Ig k W) (Y : St W) → KDI A² → KDS Y → ∀ n →
             KD k (proj₁ (Chn ac′ hk lW A² Y n)) × (KD k (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) × KDS (proj₂ (proj₂ (Chn ac′ hk lW A² Y n))))
  kd-RKi   : ∀ {ly W₀ W k t m} (ac : AccY ly) (ac′ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′)
             (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) (Tq : Tg W t m) (rk : Rk k t m) →
             KDN r u → KDI A₀ → KD ly w → KDS Y → KD t (RKi ac ac′ r u q₀ lW lL A₀ w Y Tq rk)
  kd-BNi   : ∀ {ly W₀ W k W′} (ac : AccY ly) (ac′ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′)
             (q₀ : W₀ ≤ W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) (hk : LW k W) (p : W ≤ W′) (lW′ : LgW L₀ W′) (zz : D k W′) →
             KDN r u → KDI A₀ → KD ly w → KDS Y → KD k zz → KDf (BNi ac ac′ r u q₀ lL A₀ w Y hk p lW′ zz)
  kd-RunC  : ∀ {ly W₀ W} (ac : AccY ly) (κ : K L₀) (zz : ZK ly κ) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
             P κ → KDB u → KDI A₀ → KD ly w → KDS Y → KDf (RunC ac κ zz u q₀ lW lL A₀ w Y)
  kd-RKc   : ∀ {ly W₀ W} (ac : AccY ly) (κ : K L₀) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
             P κ → KDB u → KDI A₀ → KD ly w → KDS Y → ∀ t {m} (Tq : Tg W t m) → KD t (RKc ac κ u q₀ lW lL A₀ w Y t Tq)
  kd-RKk   : ∀ {ly W₀ W t m} (ac : AccY ly) (κ : K L₀) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) (Tq : Tg W t m) (zt : ZK t κ) →
             P κ → KDB u → KDI A₀ → KD ly w → KDS Y → KD t (RKk ac κ u q₀ lL A₀ w Y Tq zt)
  kd-κc₁   : ∀ {ly W₀ W} (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
             KDB u → KDI A₀ → KD ly w → KDS Y → ∀ n →
             KD ly (co₁ (κc₁ ac u q₀ lW lL A₀ w Y n)) × KDS (Sv₁ (κc₁ ac u q₀ lW lL A₀ w Y n))
  kd-κΔ₁   : ∀ {ly W₀ W} (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (lL : LW ly W) (A₀ : Ig ly W) (c : Cl₁ W ly) →
             KDB u → KDI A₀ → KD ly (co₁ c) → KDS (Sv₁ c) → KDf (κΔ₁ ac u q₀ lW lL A₀ c)

  kd-Run ac n0 q₀ lW lL A₀ w Y kx kA kw kY = kd-zeroD
  kd-Run ac n1 q₀ lW lL A₀ w Y kx kA kw kY = kA ≤rf lW w Y kw kY
  kd-Run ac (x ⨾ y) q₀ lW lL A₀ w Y (kx , ky) kA kw kY =
    kd-⨾ᴰ (kd-Run ac x q₀ lW lL A₀ w Y kx kA kw kY)
      (kd-Run ac y q₀ lW lL A₀ (w ⨾ nw q₀ x) (Y ⊕⟨ lW ⟩ Run ac x q₀ lW lL A₀ w Y) ky kA (kw , kx)
        (kd-⊕ Y lW (Run ac x q₀ lW lL A₀ w Y) kY (kd-Run ac x q₀ lW lL A₀ w Y kx kA kw kY)))
  kd-Run ac (nl F) q₀ lW lL A₀ w Y kx kA kw kY =
    kd-nlᴰ (λ n → kd-Run ac (F n) q₀ lW lL A₀ (proj₁ (Rpt ac F q₀ lW lL A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW lL A₀ w Y n)) (kx n) kA
                    (proj₁ (kd-Rpt ac F q₀ lW lL A₀ w Y kx kA kw kY n)) (proj₂ (kd-Rpt ac F q₀ lW lL A₀ w Y kx kA kw kY n)))
  kd-Run ac (nw p x) q₀ lW lL A₀ w Y kx kA kw kY = kd-Run ac x (≤tr p q₀) lW lL A₀ w Y kx kA kw kY
  kd-Run (acc f) (ni r u) q₀ lW lL A₀ w Y kx kA kw kY = kd-RunNi (acc f) (f r) r u q₀ lW lL A₀ w Y kx kA kw kY
  kd-Run ac (nc κ zz u) q₀ lW lL A₀ w Y (pκ , ku) kA kw kY = kd-RunC ac κ zz u q₀ lW lL A₀ w Y pκ ku kA kw kY

  kd-Rpt ac F q₀ lW lL A₀ w Y kx kA kw kY zero = kw , kY
  kd-Rpt ac F q₀ lW lL A₀ w Y kx kA kw kY (suc n) =
    (proj₁ (kd-Rpt ac F q₀ lW lL A₀ w Y kx kA kw kY n) , kx n) ,
    kd-⊕ (proj₂ (Rpt ac F q₀ lW lL A₀ w Y n)) lW (Run ac (F n) q₀ lW lL A₀ (proj₁ (Rpt ac F q₀ lW lL A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW lL A₀ w Y n)))
      (proj₂ (kd-Rpt ac F q₀ lW lL A₀ w Y kx kA kw kY n))
      (kd-Run ac (F n) q₀ lW lL A₀ (proj₁ (Rpt ac F q₀ lW lL A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW lL A₀ w Y n)) (kx n) kA
         (proj₁ (kd-Rpt ac F q₀ lW lL A₀ w Y kx kA kw kY n)) (proj₂ (kd-Rpt ac F q₀ lW lL A₀ w Y kx kA kw kY n)))

  kd-RunNi ac ac′ r u q₀ lW lL A₀ w Y ku kA kw kY Tq =
    kd-RKi ac ac′ r u q₀ lW lL A₀ w Y Tq (rkT (⊲ᴮ↑ (wm Tq) (kk r q₀ lL)) (tm Tq) (lm Tq)) ku kA kw kY

  kd-Ai ac ac′ r u q₀ hk lL A₀ w ku kA kw {W′} p lW′ zz Y′ kzz kY′ =
    kd-Run ac (u (≤tr q₀ p) lW′ (inS r zz)) ≤rf lW′ (⊲ᴮ↑ p lL) (Ig↾ p A₀)
      (nw p w ⨾ Int ac′ zz ≤rf lW′ (zkS r) (mkOf r (≤tr q₀ p)) (λ p′ l′ z′ → u (≤tr (≤tr q₀ p) p′) l′ (inS r z′)) n0) Y′
      (ku (≤tr q₀ p) lW′ (inS r zz) (kdInS r zz kzz)) (kd-Ig↾ p A₀ kA)
      (kw , kd-Int ac′ zz ≤rf lW′ (zkS r) (mkOf r (≤tr q₀ p)) (λ p′ l′ z′ → u (≤tr (≤tr q₀ p) p′) l′ (inS r z′)) n0
              kzz (λ p′ l′ z′ kz′ → ku (≤tr (≤tr q₀ p) p′) l′ (inS r z′) (kdInS r z′ kz′)) tt)
      kY′

  kd-Chn ac′ hk lW A² Y kA kY zero = tt , (proj₁ kY (tg ≤rf hk lW) , kY)
  kd-Chn ac′ hk lW A² Y kA kY (suc n) =
    (proj₁ (kd-Chn ac′ hk lW A² Y kA kY n) , proj₁ (proj₂ (kd-Chn ac′ hk lW A² Y kA kY n))) ,
    (kd-Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ≤rf lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)))
       (proj₁ (proj₂ (kd-Chn ac′ hk lW A² Y kA kY n))) kA (proj₁ (kd-Chn ac′ hk lW A² Y kA kY n)) (proj₂ (proj₂ (kd-Chn ac′ hk lW A² Y kA kY n)))
       (tg ≤rf hk lW) ,
     kd-⊕ (proj₂ (proj₂ (Chn ac′ hk lW A² Y n))) lW
       (Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ≤rf lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n))))
       (proj₂ (proj₂ (kd-Chn ac′ hk lW A² Y kA kY n)))
       (kd-Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ≤rf lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)))
         (proj₁ (proj₂ (kd-Chn ac′ hk lW A² Y kA kY n))) kA (proj₁ (kd-Chn ac′ hk lW A² Y kA kY n)) (proj₂ (proj₂ (kd-Chn ac′ hk lW A² Y kA kY n)))))

  kd-RKi ac ac′ r u q₀ lW lL A₀ w Y Tq (keep R′) ku kA kw kY = λ p lW′ y ky →
    kd-BNi ac ac′ r u q₀ lL A₀ w Y (kk r q₀ lL) (≤tr (wm Tq) p) lW′ (outS R′ y) ku kA kw kY (kdOutS R′ y ky)
      (tg ≤rf (⊲ᴮ↑ p (tm Tq)) lW′)
  kd-RKi ac ac′ r u q₀ lW lL A₀ w Y Tq rise ku kA kw kY = λ n →
    kd-Run ac′ (proj₁ (proj₂ (Chn ac′ (kk r q₀ lL) lW (Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w) Y n))) ≤rf lW (kk r q₀ lL)
      (Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w)
      (proj₁ (Chn ac′ (kk r q₀ lL) lW (Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w) Y n))
      (proj₂ (proj₂ (Chn ac′ (kk r q₀ lL) lW (Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w) Y n)))
      (proj₁ (proj₂ (kd-Chn ac′ (kk r q₀ lL) lW (Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w) Y (kd-Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w ku kA kw) kY n)))
      (kd-Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w ku kA kw)
      (proj₁ (kd-Chn ac′ (kk r q₀ lL) lW (Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w) Y (kd-Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w ku kA kw) kY n))
      (proj₂ (proj₂ (kd-Chn ac′ (kk r q₀ lL) lW (Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w) Y (kd-Ai ac ac′ r u q₀ (kk r q₀ lL) lL A₀ w ku kA kw) kY n)))
      Tq

  kd-BNi ac ac′ r u q₀ lL A₀ w Y hk p lW′ zz ku kA kw kY kzz =
    kd-Ai ac ac′ r u q₀ hk lL A₀ w ku kA kw p lW′ zz
      (cv p Y ⊕⟨ lW′ ⟩ Run ac′ zz ≤rf lW′ (⊲ᴮ↑ p hk) (Ig↾ p (Ai ac ac′ r u q₀ hk lL A₀ w)) n0 (cv p Y))
      kzz
      (kd-⊕ (cv p Y) lW′ (Run ac′ zz ≤rf lW′ (⊲ᴮ↑ p hk) (Ig↾ p (Ai ac ac′ r u q₀ hk lL A₀ w)) n0 (cv p Y)) (kd-cv p Y kY)
        (kd-Run ac′ zz ≤rf lW′ (⊲ᴮ↑ p hk) (Ig↾ p (Ai ac ac′ r u q₀ hk lL A₀ w)) n0 (cv p Y)
          kzz (kd-Ig↾ p (Ai ac ac′ r u q₀ hk lL A₀ w) (kd-Ai ac ac′ r u q₀ hk lL A₀ w ku kA kw)) tt (kd-cv p Y kY)))

  kd-RunC ac κ zz u q₀ lW lL A₀ w Y pκ ku kA kw kY {t} Tq = kd-RKc ac κ u q₀ lW lL A₀ w Y pκ ku kA kw kY t Tq

  kd-RKc ac (inj₂ tt) u q₀ lW lL A₀ w Y pκ ku kA kw kY hz Tq = kd-hz (RKc ac (inj₂ tt) u q₀ lW lL A₀ w Y hz Tq)
  kd-RKc ac (inj₂ tt) u q₀ lW lL A₀ w Y pκ ku kA kw kY (hs hz) Tq = λ n →
    kd-drp₁ (proj₁ lW , lv₁ (κc₁ ac u q₀ lW lL A₀ w Y n))
      (yc (κΔ₁ ac u q₀ lW lL A₀ (κc₁ ac u q₀ lW lL A₀ w Y n)) (τ₁ (proj₁ lW , lv₁ (κc₁ ac u q₀ lW lL A₀ w Y n))))
      (kd-κΔ₁ ac u q₀ lW lL A₀ (κc₁ ac u q₀ lW lL A₀ w Y n) ku kA
         (proj₁ (kd-κc₁ ac u q₀ lW lL A₀ w Y ku kA kw kY n)) (proj₂ (kd-κc₁ ac u q₀ lW lL A₀ w Y ku kA kw kY n))
         (τ₁ (proj₁ lW , lv₁ (κc₁ ac u q₀ lW lL A₀ w Y n))))
  kd-RKc ac (inj₂ tt) u q₀ lW lL A₀ w Y pκ ku kA kw kY (hs (hs b)) Tq = kd-RKk ac (inj₂ tt) u q₀ lL A₀ w Y Tq tt pκ ku kA kw kY
  kd-RKc ac (inj₂ tt) u q₀ lW lL A₀ w Y pκ ku kA kw kY (hs (hl f)) Tq = kd-RKk ac (inj₂ tt) u q₀ lL A₀ w Y Tq tt pκ ku kA kw kY
  kd-RKc ac (inj₂ tt) u q₀ lW lL A₀ w Y pκ ku kA kw kY (hs (hΩ κ g)) Tq = kd-RKk ac (inj₂ tt) u q₀ lL A₀ w Y Tq tt pκ ku kA kw kY
  kd-RKc ac (inj₂ tt) u q₀ lW lL A₀ w Y pκ ku kA kw kY (hl f) Tq = kd-RKk ac (inj₂ tt) u q₀ lL A₀ w Y Tq tt pκ ku kA kw kY
  kd-RKc ac (inj₂ tt) u q₀ lW lL A₀ w Y pκ ku kA kw kY (hΩ κ g) Tq = kd-RKk ac (inj₂ tt) u q₀ lL A₀ w Y Tq tt pκ ku kA kw kY
  kd-RKc ac (inj₁ κ) u q₀ lW lL A₀ w Y pκ ku kA kw kY hz Tq = kd-hz (RKc ac (inj₁ κ) u q₀ lW lL A₀ w Y hz Tq)
  kd-RKc ac (inj₁ κ) u q₀ lW lL A₀ w Y pκ ku kA kw kY (hs b) Tq = kd-RKk ac (inj₁ κ) u q₀ lL A₀ w Y Tq tt pκ ku kA kw kY
  kd-RKc ac (inj₁ κ) u q₀ lW lL A₀ w Y pκ ku kA kw kY (hl f) Tq = kd-RKk ac (inj₁ κ) u q₀ lL A₀ w Y Tq tt pκ ku kA kw kY
  kd-RKc ac (inj₁ κ) u q₀ lW lL A₀ w Y pκ ku kA kw kY (hΩ κ′ g) Tq = kd-RKk ac (inj₁ κ) u q₀ lL A₀ w Y Tq tt pκ ku kA kw kY

  kd-RKk ac κ u q₀ lL A₀ w Y Tq zt pκ ku kA kw kY = pκ , λ q lW′ →
    kd-Run ac (u (≤tr (≤tr q₀ (wm Tq)) q) lW′) ≤rf lW′ (⊲ᴮ↑ (≤tr (wm Tq) q) lL) (Ig↾ (≤tr (wm Tq) q) A₀)
      (nw (≤tr (wm Tq) q) w) (cv (≤tr (wm Tq) q) Y)
      (ku (≤tr (≤tr q₀ (wm Tq)) q) lW′) (kd-Ig↾ (≤tr (wm Tq) q) A₀ kA) kw (kd-cv (≤tr (wm Tq) q) Y kY)
      (tg ≤rf (⊲ᴮ↑ q (tm Tq)) lW′)

  kd-κΔ₁ ac u q₀ lW lL A₀ c ku kA kco kS =
    kd-Run ac (u (≤tr q₀ (≤w-rf T , wv₁ c)) (proj₁ lW , lv₁ c)) ≤rf (proj₁ lW , lv₁ c)
      (⊲ᴮ↑ (≤w-rf T , wv₁ c) lL) (Ig↾ (≤w-rf T , wv₁ c) A₀) (co₁ c) (Sv₁ c)
      (ku (≤tr q₀ (≤w-rf T , wv₁ c)) (proj₁ lW , lv₁ c)) (kd-Ig↾ (≤w-rf T , wv₁ c) A₀ kA) kco kS

  kd-κc₁ {W = W} ac u q₀ lW lL A₀ w Y ku kA kw kY zero =
    kw , kd-cv (≤w-rf T , rd₁-fst lW (proj₂ W) (z₁ Y)) Y kY
  kd-κc₁ {W = W} ac u q₀ lW lL A₀ w Y ku kA kw kY (suc n) =
    proj₁ IH ,
    kd-cv (≤w-rf T , rd₁-fst lW₀ (v₁ c₀) Δ₁) (Sv₁ c₀ ⊕⟨ lW₀ ⟩ κΔ₁ ac u q₀ lW lL A₀ c₀)
      (kd-⊕ (Sv₁ c₀) lW₀ (κΔ₁ ac u q₀ lW lL A₀ c₀) (proj₂ IH) (kd-κΔ₁ ac u q₀ lW lL A₀ c₀ ku kA (proj₁ IH) (proj₂ IH)))
    where
    c₀ = κc₁ ac u q₀ lW lL A₀ w Y n
    IH = kd-κc₁ ac u q₀ lW lL A₀ w Y ku kA kw kY n
    lW₀ : LgW L₀ (proj₁ W , v₁ c₀)
    lW₀ = proj₁ lW , lv₁ c₀
    Δ₁ = yc (κΔ₁ ac u q₀ lW lL A₀ c₀) (τ₁ lW₀)
```

## §3 闭项 `TΛ′`: 一切闭包结点都是旧种类

$P$ 取 "是旧种类". `Λ′` 满足 `AllK` (由 [LeanT](LeanT.lagda.md) 的 `old-Λ′` 换写). 闭项的那一次 `Run` (与 `LeanT.ΨΩ` 里的同一个式子, 同一组模块参数) 的输出在每个目标上满足 `KD`.

```agda
OldK : ∀ {T : KS} → K (step T) → Set
OldK (inj₁ _) = ⊤
OldK (inj₂ _) = ⊥

open import OCF.Lean.LeanT as LT using (Λ′; lΛ′; one⊲; bkL; Old; old-Λ′)

old→all : ∀ {T : KS} (L : HB (step T)) → Old L → AllK (OldK {T}) L
old→all hz o = tt
old→all (hs h) o = old→all h o
old→all (hl f) o = λ n → old→all (f n) (o n)
old→all (hΩ (inj₁ _) g) o = tt , λ c → old→all (g c) (o c)
old→all (hΩ (inj₂ _) g) ()

module TΛOld where
  open Tree SL
  open FoldTy SL Λ′
  open FoldM SL bkL Λ′ lΛ′ one⊲ (λ _ → inj₂ tt)
  open KDM SL (OldK {SL})
  open KDRun SL bkL Λ′ lΛ′ one⊲ (λ _ → inj₂ tt) (OldK {SL}) (old→all {SL} Λ′ old-Λ′)

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  kd-Act : ∀ {ly W} → KDI (Act {ly} {W})
  kd-Act p lW′ v Y′ kv kY′ = kd-Stp {Y = Y′} kY′

  Y₀ : St (w₀ L₀)
  Y₀ = st zeroD n0 n0

  x₀ : D Λ′ (w₀ L₀)
  x₀ = Ωd Λ′

  TΛ′-in : KD Λ′ x₀ × KDS Y₀
  TΛ′-in = kd-Ωd Λ′ (old→all {SL} Λ′ old-Λ′) , ((λ Tq → tt) , tt)

  TΛ′-old : KDf (Run (accᴸ {S = L₀} {L = Λ′}) x₀ ≤rf (lw₀ L₀) hself (Act {Λ′} {w₀ L₀}) n0 Y₀)
  TΛ′-old = kd-Run (accᴸ {S = L₀} {L = Λ′}) x₀ ≤rf (lw₀ L₀) hself (Act {Λ′} {w₀ L₀}) n0 Y₀
              (proj₁ TΛ′-in) (kd-Act {Λ′} {w₀ L₀}) tt (proj₂ TΛ′-in)
```

## §4 结论 (按档)

- **[定理, 对一切折叠参数与一切 $P$]** `KD`, `kdOutS`, `kdInS`, `kd-hz`, `kd-drp₁`, `kd-Int`, **`kd-Run`** (及 `kd-Rpt`, `kd-RunNi`, `kd-Ai`, `kd-Chn`, `kd-RKi`, `kd-BNi`, `kd-RunC`, `kd-RKc`, `kd-RKk`, `kd-κc₁`, `kd-κΔ₁`), `kd-Ωd`, **`kd-Stp`** (前提 `AllK P Λ`).
- **[定理, 闭项]** **`TΛ′-old`**, `TΛ′-in`: `TΛ′` 的折叠的输入与每个目标上的输出里, 闭包结点都是旧种类. (这里的 `Act` 与 `LeanT.Act` 逐字相同, 在本模块里重新写出, 因为 `LeanT.Act` 的类型是对 `LeanT` 自己打开的模块写的; 两者是同一个模块应用, 判断.)
- **[判断, 一行读法]** `Run` 只在 `nc κ` 子句里调 `RunC ac κ`/`RKc ac κ`, 种类是输入数据里那个结点的种类; 所以 `TΛ′` 不执行 `κc₁` (新种类的回灌). 对一般的 `fb`: 回灌行 `RKa ac (fb κ)` 只在某次 `Run` 的输入含 `nc (inj₁ κ)` 时执行, 而这要求 `inj₁ κ` 是 $\Lambda$ 里某个第一位置的头 (取 $P$ = 在 $\Lambda$ 里出现, `AllK` 对 $\Lambda$ 自己成立).
- **前提可满足.** `AllK OldK Λ′` 由 `old-Λ′` 给出 (`old→all`); `KDI Act` 由 `kd-Stp`; 初始数据与状态 `TΛ′-in`.
