# LeanT (三): 数据树, $\Omega_L$, 输入改写, 读回, 折叠的类型

> 不含记号. 入口 [LeanT](LeanT.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 重写 `GenFoldIf` §1, §2, §4, `GenFoldTree`, `GenFoldRd` §1–§4. 数据树、结点种类、$\Omega_L$、输入改写 `Int`、`sum`、读回 `rd₁`、`drp₁` 的式子与原来逐条相同. 差 (写法与数据表示):
>
> - 层的种类结构固定为 `step T` (原来 `DG₊`, `StH` 的工具对一切 `S`, 但只在 `step T` 上用).
> - 底种类 (`aK`, 坐标读成 `HB S⊥`) 单独成记录 `BotK`, 原来是 `GenK` 的四个字段; `GenK` 的其余字段 (`tpK`, `w₀`, `lw₀`) 已是 `KS` 的字段, `fbA` 换成折叠的级回灌参数 (`FoldTy.Fb`, 见下).
> - 读回的 $\mathbb N$-下标坐标是 `HB S⊥` (原来 `A`), 所以 `nbA` 对 `HB S⊥` 递归, `toD₀`, `sum` 输出 `HB S⊥`.
> - 不带 `rd₂`, `toD₁`, `encH` (读进 `Ht`, 闭项用不到).
>
> **级回灌参数 `Fb`** (§6): 旧种类在第 0 层目标下的回灌, 只要四件: 级层 `ℓ` (在 $\Lambda$ 之下), 起点数据 `d₀` (从状态取级层上的数据), 升界 `nx` (级层上的一段数据给出更大的合法世界), 与 `nx` 的两条律. `GenFoldRun` 的 A-回灌 (`ℓ = 0`, `d₀ = z`, `nx = rsA ∘ sum`) 与 `KindLvRun` 的按级回灌 (`d₀ = d` 在 `ℓ` 上的值, `nx = rs ∘ rd`) 都是它的实例 ([LeanTFb](LeanTFb.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanTTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.LeanTBase
```

## §1 结点种类, 第一层判据, 可达

`StH W k L`: $k$ 是 $L$ 的某个直接前驱的第一位置 (结点的证据). `NZ L`: $L\ne0$; `NZ₁ L`: $L\ge2$. `AccY`: 沿结点可达, 折叠对它递归.

```agda
module _ {S : KS} where
  data StH (W : Wd S) (k : HB S) : HB S → Set where
    ss : ∀ {b} → k ⊲[ W ] b → StH W k (hs b)
    sl : ∀ {f} n → k ⊲[ W ] f n → StH W k (hl f)
    sL : ∀ {κ g c} → Bd S κ c W → k ⊲[ W ] g c → StH W k (hΩ κ g)

  NZ : HB S → Set
  NZ hz = ⊥
  NZ _ = ⊤

  NZ₁ : HB S → Set
  NZ₁ hz = ⊥
  NZ₁ (hs b) = NZ b
  NZ₁ _ = ⊤

  data AccY (L : HB S) : Set where
    acc : (∀ {W k} → StH W k L → AccY k) → AccY L

  S→⊲ : ∀ {W k L} → StH W k L → k ⊲[ W ] L
  S→⊲ (ss P) = hsuc P
  S→⊲ (sl n P) = hlim n P
  S→⊲ (sL e P) = hLim e P

  Kup : ∀ {W W′ k L} → _≤w_ S W W′ → StH W k L → StH W′ k L
  Kup q (ss P) = ss (⊲ᴮ↑ q P)
  Kup q (sl n P) = sl n (⊲ᴮ↑ q P)
  Kup q (sL {κ = κ} e P) = sL (Bd↑ S {κ = κ} q e) (⊲ᴮ↑ q P)

  Sk : ∀ {W j k L} → StH W j k → k ⊲[ W ] L → StH W j L
  Sk R hself = R
  Sk R (hsuc p) = ss (⊲ᴮ-tr (S→⊲ R) p)
  Sk R (hlim n p) = sl n (⊲ᴮ-tr (S→⊲ R) p)
  Sk R (hLim e p) = sL e (⊲ᴮ-tr (S→⊲ R) p)

  NZ-S : ∀ {W k L} → StH W k L → NZ L
  NZ-S (ss P) = tt
  NZ-S (sl n P) = tt
  NZ-S (sL e P) = tt

  nz⊲ : ∀ {W k b} → k ⊲[ W ] b → NZ k → NZ b
  nz⊲ hself z = z
  nz⊲ (hsuc p) z = tt
  nz⊲ (hlim n p) z = tt
  nz⊲ (hLim e p) z = tt

  NZ₁-S : ∀ {W k L} → StH W k L → NZ₁ k → NZ₁ L
  NZ₁-S (ss P) z = nz⊲ P (nz₁→nz _ z)
    where
    nz₁→nz : ∀ (k : HB S) → NZ₁ k → NZ k
    nz₁→nz (hs b) _ = tt
    nz₁→nz (hl f) _ = tt
    nz₁→nz (hΩ κ g) _ = tt
  NZ₁-S (sl n P) z = tt
  NZ₁-S (sL e P) z = tt

  accC : ∀ {W a} b → a ⊲[ W ] b → AccY a
  accC b hself = acc (λ { (ss P) → accC _ P ; (sl n P) → accC _ P ; (sL e P) → accC _ P })
  accC (hs b) (hsuc P) = accC b P
  accC (hl f) (hlim n P) = accC (f n) P
  accC (hΩ κ g) (hLim e P) = accC (g _) P

  accᴸ : ∀ {L : HB S} → AccY L
  accᴸ {L} = accC {w₀ S} L hself
```

## §2 数据树

层在 `HB (step T)`. 七个构造子: `n0`, `n1`, `_⨾_`, `nl`, `ni` (过第 $k$ 层的结点, 分支以第 $k$ 层的数据为输入, 对一切更大的合法世界), `nc κ` (种类 $\kappa$ 的闭包, 分支对一切更大的合法世界), `nw` (世界变大). 第 $k$ 层的数据经结点证据懒地计算 (`Vs`, `Vc`), 所以 `D` 对层号结构递归. 闭包许可 `ZK`: 旧种类要 $L\ne0$, 新种类要 $L\ge2$.

```agda
module Tree (T : KS) where
  L₀ : KS
  L₀ = step T

  infix 4 _≤_
  _≤_ : Wd L₀ → Wd L₀ → Set
  _≤_ = _≤w_ L₀

  ≤rf : ∀ {W} → W ≤ W
  ≤rf = ≤w-rf L₀

  ≤tr : ∀ {U V W} → U ≤ V → V ≤ W → U ≤ W
  ≤tr = ≤w-tr L₀

  ZK : HB L₀ → K L₀ → Set
  ZK L (inj₁ _) = NZ L
  ZK L (inj₂ _) = NZ₁ L

  zkS : ∀ {W k L} → StH W k L → ∀ κ → ZK k κ → ZK L κ
  zkS R (inj₁ _) z = NZ-S R
  zkS R (inj₂ _) z = NZ₁-S R z

  zΩ : ∀ κ {g} → ZK (hΩ κ g) κ
  zΩ (inj₁ _) = tt
  zΩ (inj₂ _) = tt

  module _ (Kd : Wd L₀ → HB L₀ → Set) (V : ∀ {W k} → Kd W k → Wd L₀ → Set) (Z : K L₀ → Set) where
    infixl 6 _⨾_
    data DG₊ : Wd L₀ → Set where
      n0  : ∀ {W} → DG₊ W
      n1  : ∀ {W} → DG₊ W
      _⨾_ : ∀ {W} → DG₊ W → DG₊ W → DG₊ W
      nl  : ∀ {W} → (ℕ → DG₊ W) → DG₊ W
      ni  : ∀ {W k} (r : Kd W k) → (∀ {W′} → W ≤ W′ → LgW L₀ W′ → V r W′ → DG₊ W′) → DG₊ W
      nc  : ∀ {W} (κ : K L₀) → Z κ → (∀ {W′} → W ≤ W′ → LgW L₀ W′ → DG₊ W′) → DG₊ W
      nw  : ∀ {W₀ W} → W₀ ≤ W → DG₊ W₀ → DG₊ W

  D  : HB L₀ → Wd L₀ → Set
  Vs : ∀ L {W k} → StH W k L → Wd L₀ → Set
  Vc : ∀ b {W a} → a ⊲[ W ] b → Wd L₀ → Set
  D L = DG₊ (λ W k → StH W k L) (λ R → Vs L R) (ZK L)
  Vs (hs b) (ss P) u = Vc b P u
  Vs (hl f) (sl n P) u = Vc (f n) P u
  Vs (hΩ κ g) (sL e P) u = Vc (g _) P u
  Vc a hself u = D a u
  Vc (hs b) (hsuc P) u = Vc b P u
  Vc (hl f) (hlim n P) u = Vc (f n) P u
  Vc (hΩ κ g) (hLim e P) u = Vc (g _) P u

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

## §3 第 0 层: 求和成布劳威尔树

第 0 层的数据没有 `ni` 与 `nc`. `drp` 换世界; `sum b x`: 从 $b$ 起逐项加上 $x$.

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

  pt  : ∀ {W} → HB S⊥ → (ℕ → D₀ W) → ℕ → HB S⊥
  sum : ∀ {W} → HB S⊥ → D₀ W → HB S⊥
  pt b d zero = b
  pt b d (suc n) = sum (pt b d n) (d n)
  sum b n0 = b
  sum b n1 = hs b
  sum b (x ⨾ y) = sum (sum b x) y
  sum b (nl d) = hl (pt b d)
  sum b (ni () u)
  sum b (nc (inj₁ _) () u)
  sum b (nc (inj₂ _) () u)
  sum b (nw p x) = sum b x

  sum-fst : ∀ {W v} b (x : D₀ W) → b ⊲[ v ] sum b x
  sum-fst b n0 = hself
  sum-fst b n1 = hsuc hself
  sum-fst b (x ⨾ y) = ⊲ᴮ-tr (sum-fst b x) (sum-fst (sum b x) y)
  sum-fst b (nl d) = hlim 0 hself
  sum-fst b (ni () u)
  sum-fst b (nc (inj₁ _) () u)
  sum-fst b (nc (inj₂ _) () u)
  sum-fst b (nw p x) = sum-fst b x

  Lg-sum : ∀ {W} b (x : D₀ W) → LgB b → LgB (sum b x)
  Lg-pt  : ∀ {W} b (d : ℕ → D₀ W) n → LgB b → LgB (pt b d n)
  Lg-sum b n0 l = l
  Lg-sum b n1 l = l
  Lg-sum b (x ⨾ y) l = Lg-sum (sum b x) y (Lg-sum b x l)
  Lg-sum b (nl d) l = (λ n → sum-fst (pt b d n) (d n)) , (λ n → Lg-pt b d n l)
  Lg-sum b (ni () u) l
  Lg-sum b (nc (inj₁ _) () u) l
  Lg-sum b (nc (inj₂ _) () u) l
  Lg-sum b (nw p x) l = Lg-sum b x l
  Lg-pt b d zero l = l
  Lg-pt b d (suc n) l = Lg-sum (pt b d n) (d n) (Lg-pt b d n l)

  toD₀ : ∀ {W} → HB S⊥ → D₀ W
  toD₀ hz = n0
  toD₀ (hs c) = toD₀ c ⨾ n1
  toD₀ (hl f) = nl (λ n → toD₀ (f n))
  toD₀ (hΩ (() , _) g)
```

## §4 $\Omega_L$, 输入改写

$\Omega_L$ 的 $\Omega$-行对一切种类一条: 分支在更大的世界 $W'$ 里过第 $g(\mathrm{top}\,\kappa\,W')$ 层. 输入改写 `Int` 把第 $k$ 层的数据改写到第 $ly$ 层 (结点证据经 `mk` 搬上去, `n1` 换成 `u`); 闭包行不走前缀.

```agda
  Ωd : ∀ L {W} → D L W
  Ωd hz = n1
  Ωd (hs b) = n1 ⨾ ni (ss hself) (λ _ _ _ → n1)
  Ωd (hl f) = n1 ⨾ nl (λ n → ni (sl n hself) (λ _ _ _ → n1))
  Ωd (hΩ κ g) = n1 ⨾ nc κ (zΩ κ) (λ {W′} _ _ → ni (sL {κ = κ} {c = top L₀ κ W′} (topBd L₀ κ W′) hself) (λ _ _ _ → n1))

  Pre : ∀ {L W₀ W} → W₀ ≤ W → (ℕ → D L W₀) → ℕ → D L W
  Pre q₀ d zero = n0
  Pre q₀ d (suc n) = Pre q₀ d n ⨾ nw q₀ (d n)

  mkOf : ∀ {ly W₀ k} → StH {L₀} W₀ k ly → ∀ {W} → W₀ ≤ W → ∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly
  mkOf R q p R′ = Sk R′ (S→⊲ (Kup (≤tr q p) R))

  Int : ∀ {ly k W₀ W} → AccY k → D k W₀ → W₀ ≤ W → LgW L₀ W → (∀ κ → ZK k κ → ZK ly κ) →
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
    ni (mk ≤rf (Kup q₀ R)) (λ {W′} p lW′ y →
      Int (acc g) (v (≤tr q₀ p) lW′ (inS R (outS (mk ≤rf (Kup q₀ R)) y))) ≤rf lW′ zy (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′))
        (nw p w ⨾ Int (g R) (outS (mk ≤rf (Kup q₀ R)) y) ≤rf lW′ (zkS R) (mkOf R (≤tr q₀ p))
                    (λ p′ l′ z′ → v (≤tr (≤tr q₀ p) p′) l′ (inS R z′)) n0))
  Int ac (nc κ z v) q₀ lW zy mk u w =
    nc κ (zy κ z) (λ {W′} p lW′ →
      Int ac (v (≤tr q₀ p) lW′) ≤rf lW′ zy (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′)) (nw p w))
```

## §5 第 1 层: 读成 `HB T`, 与不看新种类的分量

**底种类** `BotK`: `T` 的一个种类, 坐标读成 `HB S⊥` (保合法、保第一位置). `rd₁`: 第 1 层的数据读成新种类的坐标 `HB T`; 过第 0 层的结点读成底种类的 $\Omega$-结点 (对 `HB S⊥` 坐标递归, `nbA`); 旧种类的闭包有损地读 (当前世界的分支). 合法由形状给出.

```agda
  record BotK : Set where
    field
      aK       : K T
      frE      : E T aK → HB S⊥
      frE-lg   : ∀ {w e} → LgW T w → Bd T aK e w → LgB (frE e)
      frE-mono : ∀ {w e e′} → LgW T w → Bd T aK e w → Bd T aK e′ w → Pr T aK w e e′ → ∀ {v} → frE e ⊲[ v ] frE e′

  module NbA {S : KS} (b : HB S) (s : HB S⊥ → HB S → HB S) where
    nbA : HB S⊥ → HB S
    nbA hz = b
    nbA (hs c) = s c (nbA c)
    nbA (hl f) = hl (λ n → nbA (f n))
    nbA (hΩ (() , _) g)

    module _ (fs : ∀ c h {w} → h ⊲[ w ] s c h) where
      nbA-mono : ∀ {v c c′} → c ⊲[ v ] c′ → ∀ {w} → nbA c ⊲[ w ] nbA c′
      nbA-mono hself = hself
      nbA-mono (hsuc p) = ⊲ᴮ-tr (nbA-mono p) (fs _ _)
      nbA-mono (hlim n p) = hlim n (nbA-mono p)
      nbA-mono (hLim {κ = () , _} e p)

      nbA-fst : ∀ c {w} → b ⊲[ w ] nbA c
      nbA-fst hz = hself
      nbA-fst (hs c) = ⊲ᴮ-tr (nbA-fst c) (fs _ _)
      nbA-fst (hl f) = hlim 0 (nbA-fst (f 0))
      nbA-fst (hΩ (() , _) g)

      Lg-nbA : LgB b → (∀ c h → LgB h → LgB (s c h)) → ∀ c → LgB c → LgB (nbA c)
      Lg-nbA lb ls hz _ = lb
      Lg-nbA lb ls (hs c) l = ls c _ (Lg-nbA lb ls c l)
      Lg-nbA lb ls (hl f) (st , l) = (λ n → nbA-mono (st {w₀ S⊥} n)) , (λ n → Lg-nbA lb ls (f n) (l n))
      Lg-nbA lb ls (hΩ (() , _) g) l
  open NbA

  module Rd (bk : BotK) where
    open BotK bk

    rd₁  : ∀ {W} → LgW L₀ W → HB T → D (hs hz) W → HB T
    rdp₁ : ∀ {W} → LgW L₀ W → HB T → (ℕ → D (hs hz) W) → ℕ → HB T
    rd₁ lW b n0 = b
    rd₁ lW b n1 = hs b
    rd₁ lW b (x ⨾ y) = rd₁ lW (rd₁ lW b x) y
    rd₁ lW b (nl d) = hl (rdp₁ lW b d)
    rd₁ lW b (ni (ss hself) u) = hΩ aK (λ e → nbA b (λ c h → rd₁ lW h (u ≤rf lW (toD₀ c))) (frE e))
    rd₁ lW b (nc (inj₁ κ) z u) = rd₁ lW b (u ≤rf lW)
    rd₁ lW b (nc (inj₂ _) () u)
    rd₁ lW b (nw p x) = rd₁ (lgDn L₀ p lW) b x
    rdp₁ lW b d zero = b
    rdp₁ lW b d (suc n) = rd₁ lW (rdp₁ lW b d n) (d n)

    rd₁-fst : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) {w} → b ⊲[ w ] rd₁ lW b x
    rd₁-fst lW b n0 = hself
    rd₁-fst lW b n1 = hsuc hself
    rd₁-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rd₁-fst lW b x) (rd₁-fst lW (rd₁ lW b x) y)
    rd₁-fst lW b (nl d) = hlim 0 hself
    rd₁-fst lW b (ni (ss hself) u) {w} =
      hLim {T} {κ = aK} {c = bot T aK} (botBd T aK w)
        (nbA-fst b _ (λ c h → rd₁-fst lW h (u ≤rf lW (toD₀ c))) (frE (bot T aK)))
    rd₁-fst lW b (nc (inj₁ κ) z u) = rd₁-fst lW b (u ≤rf lW)
    rd₁-fst lW b (nc (inj₂ _) () u)
    rd₁-fst lW b (nw p x) = rd₁-fst (lgDn L₀ p lW) b x

    Lg-rd₁  : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) → LgB b → LgB (rd₁ lW b x)
    Lg-rdp₁ : ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D (hs hz) W) → LgB b → ∀ n → LgB (rdp₁ lW b d n)
    Lg-rd₁ lW b n0 l = l
    Lg-rd₁ lW b n1 l = l
    Lg-rd₁ lW b (x ⨾ y) l = Lg-rd₁ lW (rd₁ lW b x) y (Lg-rd₁ lW b x l)
    Lg-rd₁ lW b (nl d) l = (λ n → rd₁-fst lW (rdp₁ lW b d n) (d n)) , Lg-rdp₁ lW b d l
    Lg-rd₁ lW b (ni (ss hself) u) l =
      (λ lw e e′ p → nbA-mono b _ fs (frE-mono lw e e′ p {w₀ S⊥})) ,
      (λ {c = e₀} lw e → Lg-nbA b _ fs l (λ c h lh → Lg-rd₁ lW h (u ≤rf lW (toD₀ c)) lh) (frE e₀) (frE-lg lw e))
      where
      fs : ∀ c h {w} → h ⊲[ w ] rd₁ lW h (u ≤rf lW (toD₀ c))
      fs c h = rd₁-fst lW h (u ≤rf lW (toD₀ c))
    Lg-rd₁ lW b (nc (inj₁ κ) z u) l = Lg-rd₁ lW b (u ≤rf lW) l
    Lg-rd₁ lW b (nc (inj₂ _) () u) l
    Lg-rd₁ lW b (nw p x) l = Lg-rd₁ (lgDn L₀ p lW) b x l
    Lg-rdp₁ lW b d l zero = l
    Lg-rdp₁ lW b d l (suc n) = Lg-rd₁ lW (rdp₁ lW b d n) (d n) (Lg-rdp₁ lW b d l n)

  drp₁ : ∀ {w₀ x y} → LgW L₀ (w₀ , x) → D (hs hz) (w₀ , x) → D (hs hz) (w₀ , y)
  drp₁ l n0 = n0
  drp₁ l n1 = n1
  drp₁ l (a ⨾ b) = drp₁ l a ⨾ drp₁ l b
  drp₁ l (nl d) = nl (λ n → drp₁ l (d n))
  drp₁ {x = x} l (ni (ss hself) u) =
    ni (ss hself) (λ {W″} q lW″ z → drp₁ (proj₁ lW″ , proj₂ l) (u {proj₁ W″ , x} (proj₁ q , hself) (proj₁ lW″ , proj₂ l) (drp z)))
  drp₁ {x = x} l (nc (inj₁ κ) z u) =
    nc (inj₁ κ) z (λ {W″} q lW″ → drp₁ (proj₁ lW″ , proj₂ l) (u {proj₁ W″ , x} (proj₁ q , hself) (proj₁ lW″ , proj₂ l)))
  drp₁ l (nc (inj₂ _) () u)
  drp₁ l (nw p t) = nw (proj₁ p , hself) (drp₁ (lgDn L₀ p l) t)
```

## §6 折叠的类型与级回灌参数

`Tg W t m`: 目标层 $t$ 与世界 $m\ge W$, $t$ 在 $\Lambda$ 之下 (公共上界). `Df W`: 对每个目标给出该层的数据. `St W`: 累计的输出, 与自当前世界以来第 0, 1 层的输出. `Fb`: 级回灌 (文件头).

```agda
module FoldTy (T : KS) (Λ : HB (step T)) where
  open Tree T

  record Tg (W : Wd L₀) (t : HB L₀) (m : Wd L₀) : Set where
    constructor tg
    field
      wm : W ≤ m
      tm : t ⊲[ m ] Λ
      lm : LgW L₀ m
  open Tg public

  record Df (W : Wd L₀) : Set where
    constructor df
    field
      yc : ∀ {t m} → Tg W t m → D t m
  open Df public

  record St (W : Wd L₀) : Set where
    constructor st
    field
      d  : Df W
      z  : D hz W
      z₁ : D (hs hz) W
  open St public

  Ig : HB L₀ → Wd L₀ → Set
  Ig ly W = ∀ {W′} → W ≤ W′ → LgW L₀ W′ → D ly W′ → St W′ → Df W′

  record Fb : Set where
    field
      ℓ    : HB L₀
      ℓ⊲   : ∀ {w} → ℓ ⊲[ w ] Λ
      d₀   : ∀ {W} → LgW L₀ W → St W → D ℓ W
      nx   : ∀ {W} → LgW L₀ W → D ℓ W → Wd T
      nx≤  : ∀ {W} (lW : LgW L₀ W) x → _≤w_ T (proj₁ W) (nx lW x)
      nxLg : ∀ {W} (lW : LgW L₀ W) x → LgW T (nx lW x)
  open Fb public
```
