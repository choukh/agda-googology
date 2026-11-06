# 对一般种类结构的折叠 (一): 数据树的工具, $\Omega_L$, 输入改写

> 不含记号. 入口 [GenFold](GenFold.lagda.md), 接口 [GenFoldIf](GenFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 由 [HtTowerFTree](HtTowerFTree.lagda.md) §2–§5, §7 改写: 层的种类结构从 `S₁ = step S₀` 换成任意 `step T`, 世界从 `A × H₀` 换成 `Wd (step T)`. 改了两件:
>
> 1. **一个闭包结点 `nc κ` 对一切种类** (接口 §2). $\Omega_L$ 的 $\Omega$-行 (`Ωd`) 对一切种类一条: 分支在更大的世界 $W'$ 里过第 $g(\mathrm{top}\,\kappa\,W')$ 层 (结点证据 `topBd`). 两种种类时 κA 一行与 `nκ` 一行, κH 一行与 `nμ` 一行同形 (`HtTowerFTree.Ωd`).
> 2. **输入改写 `Int` 的闭包行不走前缀**: `HtTowerFTree.Int` 的 `nκ`/`nμ` 行先沿坐标从输入的世界走到当前世界 (`IW₀`/`IW₁`, `Cut₀`/`Cut₁`), 再接闭包. 这里只接闭包, 分支的上下文是 `nw p w`. **[判断] 这一步改了值, 不改合法与停机**: 数据树没有合法性, 合法由读回的形状给出 (`GenFoldRd`). 走前缀要对每个种类的坐标结构递归 (`A` 的路径, `HB _` 的路径), 坐标类型是抽象的 `E κ`; 本路没有写.
>
> 其余 (`StH` 的工具, `NZ` 的引理, `outC`/`inC`, `AccY`, `drp`, `sum`, `toD₀`) 逐行照 `HtTowerFTree`, 对一切种类结构.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenFoldTree where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
```

## §1 结点种类的工具 (对一切种类结构)

```agda
module _ {S : KS} where
  S→⊲ : ∀ {W k L} → StH {S} W k L → k ⊲[ W ] L
  S→⊲ (ss P) = hsuc P
  S→⊲ (sl n P) = hlim n P
  S→⊲ (sL e P) = hLim e P

  Kup : ∀ {W W′ k L} → _≤w_ S W W′ → StH {S} W k L → StH W′ k L
  Kup q (ss P) = ss (⊲ᴮ↑ q P)
  Kup q (sl n P) = sl n (⊲ᴮ↑ q P)
  Kup q (sL {κ = κ} e P) = sL (Bd↑ S {κ = κ} q e) (⊲ᴮ↑ q P)

  Sk : ∀ {W j k L} → StH {S} W j k → k ⊲[ W ] L → StH W j L
  Sk R hself = R
  Sk R (hsuc p) = ss (⊲ᴮ-tr (S→⊲ R) p)
  Sk R (hlim n p) = sl n (⊲ᴮ-tr (S→⊲ R) p)
  Sk R (hLim e p) = sL e (⊲ᴮ-tr (S→⊲ R) p)

  NZ-S : ∀ {W k L} → StH {S} W k L → NZ L
  NZ-S (ss P) = tt
  NZ-S (sl n P) = tt
  NZ-S (sL e P) = tt

  nz⊲ : ∀ {W k b} → k ⊲[ W ] b → NZ {S} k → NZ b
  nz⊲ hself z = z
  nz⊲ (hsuc p) z = tt
  nz⊲ (hlim n p) z = tt
  nz⊲ (hLim e p) z = tt

  nz₁→nz : ∀ (k : HB S) → NZ₁ k → NZ k
  nz₁→nz (hs b) _ = tt
  nz₁→nz (hl f) _ = tt
  nz₁→nz (hΩ κ g) _ = tt

  NZ₁-S : ∀ {W k L} → StH {S} W k L → NZ₁ k → NZ₁ L
  NZ₁-S {k = k} (ss P) z = nz⊲ P (nz₁→nz k z)
  NZ₁-S (sl n P) z = tt
  NZ₁-S (sL e P) z = tt

  accL : ∀ (L : HB S) → AccY L
  accC : ∀ (b : HB S) {W a} → a ⊲[ W ] b → AccY a
  accL hz = acc (λ ())
  accL (hs b) = acc (λ { (ss P) → accC b P })
  accL (hl f) = acc (λ { (sl n P) → accC (f n) P })
  accL (hΩ κ g) = acc (λ { (sL e P) → accC (g _) P })
  accC a hself = accL a
  accC (hs b) (hsuc P) = accC b P
  accC (hl f) (hlim n P) = accC (f n) P
  accC (hΩ κ g) (hLim e P) = accC (g _) P

  accᴸ : ∀ {L : HB S} → AccY L
  accᴸ {L} = accL L

-- 闭包许可沿结点上传 (ZK 对两类种类)
zkS : ∀ {T : KS} {W k L} → StH {step T} W k L → ∀ κ → ZK T k κ → ZK T L κ
zkS R (inj₁ _) z = NZ-S R
zkS R (inj₂ _) z = NZ₁-S R z

zΩ : ∀ {T : KS} (κ : K (step T)) {g : E (step T) κ → HB (step T)} → ZK T (hΩ κ g) κ
zΩ (inj₁ _) = tt
zΩ (inj₂ _) = tt
```

## §2 数据树的工具 (层的种类结构 `step T`)

```agda
module Tree (T : KS) where
  open DataG (step T) (ZK T) public

  L₀ : KS
  L₀ = step T

  infix 4 _≤_
  _≤_ : Wd L₀ → Wd L₀ → Set
  _≤_ = _≤w_ L₀

  ≤rf : ∀ {W} → W ≤ W
  ≤rf = ≤w-rf L₀

  ≤tr : ∀ {U V W} → U ≤ V → V ≤ W → U ≤ W
  ≤tr = ≤w-tr L₀

  outC : ∀ {b W a u} (P : a ⊲[ W ] b) → Vc b P u → D a u
  outC hself x = x
  outC (hsuc P) x = outC P x
  outC (hlim n P) x = outC P x
  outC (hLim e P) x = outC P x

  inC : ∀ {b W a u} (P : a ⊲[ W ] b) → D a u → Vc b P u
  inC hself x = x
  inC (hsuc P) x = inC P x
  inC (hlim n P) x = inC P x
  inC (hLim e P) x = inC P x

  outS : ∀ {L W k u} (R : StH W k L) → Vs L R u → D k u
  outS (ss P) x = outC P x
  outS (sl n P) x = outC P x
  outS (sL e P) x = outC P x

  inS : ∀ {L W k u} (R : StH W k L) → D k u → Vs L R u
  inS (ss P) x = inC P x
  inS (sl n P) x = inC P x
  inS (sL e P) x = inC P x
```

### 第 0 层

第 0 层的数据没有 `ni` (第 0 层没有第一位置) 与 `nc` (`ZK T hz κ` 对两类种类都是空的).

```agda
  D₀ : Wd L₀ → Set
  D₀ = D hz

  drp : ∀ {W W′} → D₀ W → D₀ W′
  drp n0 = n0
  drp n1 = n1
  drp (x ⨾ y) = drp x ⨾ drp y
  drp (nl d) = nl (λ n → drp (d n))
  drp (ni () u)
  drp (nc (inj₁ _) () u)
  drp (nc (inj₂ _) () u)
  drp (nw p x) = drp x

  pt  : ∀ {W} → A → (ℕ → D₀ W) → ℕ → A
  sum : ∀ {W} → A → D₀ W → A
  pt b d zero = b
  pt b d (suc n) = sum (pt b d n) (d n)
  sum b n0 = b
  sum b n1 = asuc b
  sum b (x ⨾ y) = sum (sum b x) y
  sum b (nl d) = alim (pt b d)
  sum b (ni () u)
  sum b (nc (inj₁ _) () u)
  sum b (nc (inj₂ _) () u)
  sum b (nw p x) = sum b x

  sum-fst : ∀ {W} b (x : D₀ W) → b ⊲ sum b x
  sum-fst b n0 = C.self
  sum-fst b n1 = C.suc C.self
  sum-fst b (x ⨾ y) = ⊲-tr (sum-fst b x) (sum-fst (sum b x) y)
  sum-fst b (nl d) = C.lim 0 C.self
  sum-fst b (ni () u)
  sum-fst b (nc (inj₁ _) () u)
  sum-fst b (nc (inj₂ _) () u)
  sum-fst b (nw p x) = sum-fst b x

  Lg-sum : ∀ {W} b (x : D₀ W) → Lg b → Lg (sum b x)
  Lg-pt  : ∀ {W} b (d : ℕ → D₀ W) n → Lg b → Lg (pt b d n)
  Lg-sum b n0 w = w
  Lg-sum b n1 w = w
  Lg-sum b (x ⨾ y) w = Lg-sum (sum b x) y (Lg-sum b x w)
  Lg-sum b (nl d) w = (λ n → sum-fst (pt b d n) (d n)) , (λ n → Lg-pt b d n w)
  Lg-sum b (ni () u) w
  Lg-sum b (nc (inj₁ _) () u) w
  Lg-sum b (nc (inj₂ _) () u) w
  Lg-sum b (nw p x) w = Lg-sum b x w
  Lg-pt b d zero w = w
  Lg-pt b d (suc n) w = Lg-sum (pt b d n) (d n) (Lg-pt b d n w)

  toD₀ : ∀ {W} → A → D₀ W
  toD₀ azero = n0
  toD₀ (asuc c) = toD₀ c ⨾ n1
  toD₀ (alim f) = nl (λ n → toD₀ (f n))
```

### $\Omega_L$: $\Omega$-行对一切种类一条

```agda
  module Om (tp : TopG L₀) where
    Ωd : ∀ L {W} → D L W
    Ωd hz = n1
    Ωd (hs b) = n1 ⨾ ni (ss hself) (λ _ _ _ → n1)
    Ωd (hl f) = n1 ⨾ nl (λ n → ni (sl n hself) (λ _ _ _ → n1))
    Ωd (hΩ κ g) = n1 ⨾ nc κ (zΩ κ) (λ {W′} _ _ → ni (sL {κ = κ} {c = top tp κ W′} (topBd tp κ W′) hself) (λ _ _ _ → n1))
```

### 前缀与输入改写 (闭包行不走前缀)

```agda
  Pre : ∀ {L W₀ W} → W₀ ≤ W → (ℕ → D L W₀) → ℕ → D L W
  Pre q₀ d zero = n0
  Pre q₀ d (suc n) = Pre q₀ d n ⨾ nw q₀ (d n)

  mkOf : ∀ {ly W₀ k} → StH W₀ k ly → ∀ {W} → W₀ ≤ W → ∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly
  mkOf R q p R′ = Sk {S = L₀} R′ (S→⊲ {S = L₀} (Kup {S = L₀} (≤tr q p) R))

  Int : ∀ {ly k W₀ W} → AccY k → D k W₀ → W₀ ≤ W → LgW L₀ W → (∀ κ → ZK T k κ → ZK T ly κ) →
        (∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly) →
        (∀ {W′} → W ≤ W′ → LgW L₀ W′ → D k W′ → D ly W′) → D k W → D ly W
  Int ac n0 q₀ lW zy mk u w = n0
  Int ac n1 q₀ lW zy mk u w = u ≤rf lW w
  Int ac (x ⨾ y) q₀ lW zy mk u w =
    Int ac x q₀ lW zy mk u w ⨾ Int ac y q₀ lW zy mk u (w ⨾ nw q₀ x)
  Int ac (nl d) q₀ lW zy mk u w =
    nl (λ n → Int ac (d n) q₀ lW zy mk u (w ⨾ Pre q₀ d n))
  Int ac (nw p x) q₀ lW zy mk u w = Int ac x (≤tr p q₀) lW zy mk u w
  Int (acc g) (ni R v) q₀ lW zy mk u w =
    ni (mk ≤rf (Kup {S = L₀} q₀ R)) (λ {W′} p lW′ y →
      Int (acc g) (v (≤tr q₀ p) lW′ (inS R (outS (mk ≤rf (Kup {S = L₀} q₀ R)) y))) ≤rf lW′ zy (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′))
        (nw p w ⨾ Int (g R) (outS (mk ≤rf (Kup {S = L₀} q₀ R)) y) ≤rf lW′ (zkS {T} R) (mkOf R (≤tr q₀ p))
                    (λ p′ l′ z′ → v (≤tr (≤tr q₀ p) p′) l′ (inS R z′)) n0))
  Int ac (nc κ z v) q₀ lW zy mk u w =
    nc κ (zy κ z) (λ {W′} p lW′ →
      Int ac (v (≤tr q₀ p) lW′) ≤rf lW′ zy (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′)) (nw p w))
```

## §3 顶坐标对 `step` 一步

```agda
topStepG : ∀ {S : KS} → TopG S → TopG (step S)
topStepG {S} tp = record { top = tp⁺ ; topBd = tb⁺ }
  where
  tp⁺ : (κ : K (step S)) → Wd (step S) → E (step S) κ
  tp⁺ (inj₁ κ) w = top tp κ (proj₁ w)
  tp⁺ (inj₂ _) w = proj₂ w
  tb⁺ : ∀ κ w → Bd (step S) κ (tp⁺ κ w) w
  tb⁺ (inj₁ κ) w = topBd tp κ (proj₁ w)
  tb⁺ (inj₂ _) w = hself
```
