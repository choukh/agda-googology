# 第 1 层差树的值语义 (一): 底座

> 不含记号. 入口 [L1Val](L1Val.lagda.md). 三条否定 ([L1ValShape](L1ValShape.lagda.md), [L1ValSup](L1ValSup.lagda.md), [L1ValKappa](L1ValKappa.lagda.md)) 共用的东西:
>
> - **场景.** 折叠就是 $\psi_0(\Omega_{\Omega+1})$ 计算里用的那一个 (`SumOneClosed`, $S=\cdot\omega$), 动作是 `Step` (链 `Chn` 在第 1 层上跑时, 顶层 `Ai` 归约到的正是它). 世界 $1$, 输入层 `cnt one`, 目标第 0 层. 起点状态 `Ys`: 各层的差都是 `n0 ⨾ (n0 ⨾ n1)`, 第 0 层的增长是 `n1`. `val x` 是第 0 层输出的和.
> - **零与一.** `Z`: 树里没有 `n1` (对一切差树族). `Z` 的第 0 层树的和不超过底 (`zup`); `has1` 判出的树的和至少是底加一 (`low`).
> - **停滞.** `RunZ`: 折叠走一棵 `Z` 的第 0 层树, 不管动作是什么, 输出 `Z`. 所以链 (`Chn`) 一旦有一个链点 `Z`, 以后都 `Z` (`chain-stall`). `Walk-Z`: 沿一条没有后继步的路径走层 (`SFP`, `SFL`), 输出 `Z`. 所以回灌 (`κc`) 一旦一格输出 `Z`, 以后都 `Z` (`κ-stall`). 两条都对一切输入成立, 是折叠本身的一步性质.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.L1ValBase where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.SumOneTree using (D₊; D; n0; n1; _⨾_; nl; ni; nκ; nw; cnt; sum; pt; sum-fst; Lg-sum; Lg-pt; drp)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one; S)
open import OCF.Align.LayerTrBase using (B₁; bz; _≼_)
open import OCF.Align.BrwMidZero using (toA)
```

## §1 零与一

```agda
module _ {Kd : A → A → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Zz : Set} where
  Z : ∀ {W} → D₊ Kd V′ Zz W → Set
  Z n0 = ⊤
  Z n1 = ⊥
  Z (x ⨾ y) = Z x × Z y
  Z (nl d) = ∀ n → Z (d n)
  Z (ni r u) = ∀ {W′} p l y → Z (u {W′} p l y)
  Z (nκ zz u) = ∀ {c} p l → Z (u {c} p l)
  Z (nw p x) = Z x

ZD : ∀ {W} → F.Df W → Set
ZD {W} Δ = ∀ {t} (τ : Tg t W) lt → Z (F.yc Δ τ lt)

has1 : ∀ {W} → D azero W → Bool
has1 n1 = true
has1 (x ⨾ y) = has1 x ∨ has1 y
has1 (nl d) = has1 (d 0)
has1 (nw p x) = has1 x
has1 _ = false

low : ∀ {W} b (x : D azero W) → has1 x ≡ true → asuc b ≤ sum b x
low b n1 h = ≤-refl (asuc b)
low b (x ⨾ y) h with has1 x in e
... | true = ≤-trans (low b x e) (⊲→≤ (sum-fst (sum b x) y))
... | false = ≤-trans (s≤ (⊲→≤ (sum-fst b x))) (low (sum b x) y h)
low b (nl d) h = ≤l 1 (low b (d 0) h)
low b (nw p x) h = low b x h
low b n0 ()

zup : ∀ {W} b b′ (x : D azero W) → Z x → b′ ≤ b → sum b′ x ≤ b
zpt : ∀ {W} b b′ (d : ℕ → D azero W) → (∀ n → Z (d n)) → b′ ≤ b → ∀ n → pt b′ d n ≤ b
zup b b′ n0 z h = h
zup b b′ (x ⨾ y) (zx , zy) h = zup b (sum b′ x) y zy (zup b b′ x zx h)
zup b b′ (nl d) z h = l≤ (zpt b b′ d z h)
zup b b′ (nw p x) z h = zup b b′ x z h
zup b b′ (ni () u) z h
zup b b′ (nκ () u) z h
zpt b b′ d z h zero = h
zpt b b′ d z h (suc n) = zup b (pt b′ d n) (d n) (z n) (zpt b b′ d z h n)

no10 : ¬ (asuc azero ≤ azero)
no10 ()

-- 下界与上界合起来: 不 ≤
sep : ∀ {W W′} (x : D azero W) (y : D azero W′) → has1 x ≡ true → Z y → ¬ (sum azero x ≤ sum azero y)
sep x y h z le = no10 (≤-trans (low azero x h) (≤-trans le (zup azero azero y z z≤)))

drp-Z : ∀ {W W′} (x : D azero W) → Z x → Z (drp {W} {W′} x)
drp-Z n0 z = tt
drp-Z (x ⨾ y) (zx , zy) = drp-Z x zx , drp-Z y zy
drp-Z (nl d) z = λ n → drp-Z (d n) (z n)
drp-Z (nw p x) z = drp-Z x z
drp-Z (ni () u) z
drp-Z (nκ () u) z
```

## §2 链的停滞

折叠走第 0 层的树, 只在 `n1` 处调动作. 没有 `n1`, 输出就是零.

```agda
RunZ : ∀ {W₀ W} (ac : F.AccY (cnt azero)) (z : D azero W₀) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : azero ⊲ W) (A₀ : F.Ig (cnt azero) W) w Y →
       Z z → ZD (F.Run ac z q₀ lW ll A₀ w Y)
RunZ ac n0 q₀ lW ll A₀ w Y z τ lt = tt
RunZ ac (x ⨾ y) q₀ lW ll A₀ w Y (zx , zy) τ lt =
  RunZ ac x q₀ lW ll A₀ w Y zx τ lt , RunZ ac y q₀ lW ll A₀ _ _ zy τ lt
RunZ ac (nl d) q₀ lW ll A₀ w Y z τ lt = λ n → RunZ ac (d n) q₀ lW ll A₀ _ _ (z n) τ lt
RunZ ac (nw p x) q₀ lW ll A₀ w Y z τ lt = RunZ ac x (⊲-tr p q₀) lW ll A₀ w Y z τ lt
RunZ (F.acc f) (ni () u) q₀ lW ll A₀ w Y z τ lt
RunZ ac (nκ () u) q₀ lW ll A₀ w Y z τ lt

-- 动作的输出总是零, 则走什么都是零
RunZA : ∀ {W₀ W} (ac : F.AccY (cnt azero)) (z : D azero W₀) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : azero ⊲ W) (A₀ : F.Ig (cnt azero) W) →
        (∀ {W′} (p : W ⊲ W′) l w Y → ZD (A₀ p l w Y)) → ∀ w Y → ZD (F.Run ac z q₀ lW ll A₀ w Y)
RunZA ac n0 q₀ lW ll A₀ hA w Y τ lt = tt
RunZA ac n1 q₀ lW ll A₀ hA w Y τ lt = hA C.self lW w Y τ lt
RunZA ac (x ⨾ y) q₀ lW ll A₀ hA w Y τ lt = RunZA ac x q₀ lW ll A₀ hA w Y τ lt , RunZA ac y q₀ lW ll A₀ hA _ _ τ lt
RunZA ac (nl d) q₀ lW ll A₀ hA w Y τ lt = λ n → RunZA ac (d n) q₀ lW ll A₀ hA _ _ τ lt
RunZA ac (nw p x) q₀ lW ll A₀ hA w Y τ lt = RunZA ac x (⊲-tr p q₀) lW ll A₀ hA w Y τ lt
RunZA (F.acc f) (ni () u) q₀ lW ll A₀ hA w Y τ lt
RunZA ac (nκ () u) q₀ lW ll A₀ hA w Y τ lt
```

**链的停滞** (对一切输入, 一切动作): 第 $n$ 个链点 $\delta_n$ 是 `Z`, 则第 $n$ 段输出与 $\delta_{n+1}$ 都是 `Z`.

```agda
module _ {W} (ac′ : F.AccY (cnt azero)) (kW : azero ⊲ W) (lW : Lg W) (lk : Lg azero) (A² : F.Ig (cnt azero) W) (Y : F.St W) where
  C′ : ℕ → D azero W × (D azero W × F.St W)
  C′ = F.Chn ac′ kW lW lk A² Y

  δ : ℕ → D azero W
  δ n = proj₁ (proj₂ (C′ n))

  seg : ℕ → F.Df W
  seg n = F.Run ac′ (δ n) C.self lW kW A² (proj₁ (C′ n)) (proj₂ (proj₂ (C′ n)))

  chain-stall : ∀ n → Z (δ n) → ZD (seg n) × Z (δ (suc n))
  chain-stall n z = RunZ ac′ (δ n) C.self lW kW A² _ _ z , RunZ ac′ (δ n) C.self lW kW A² _ _ z (inj₁ kW) lk

  -- 从某个链点起全部停滞
  stall-from : ∀ n → Z (δ n) → ∀ m → Z (δ (m + n))
  stall-from n z zero = z
  stall-from n z (suc m) = proj₂ (chain-stall (m + n) (stall-from n z m))
```

## §3 回灌的停滞

`SFP`: 路径没有后继步. `SFL`: 合法性证明里的相邻步都没有后继步 (遗传). 沿这样的路径, `Walk` 一次也不调用分支.

```agda
SFP : ∀ {a b} → a ⊲ b → Set
SFP C.self = ⊤
SFP (C.suc p) = ⊥
SFP (C.lim n p) = SFP p

SFL : ∀ b → Lg b → Set
SFL azero _ = ⊤
SFL (asuc b) l = SFL b l
SFL (alim f) (st , w) = (∀ n → SFP (st n)) × (∀ n → SFL (f n) (w n))

SFP-tr : ∀ {a b c} (p : a ⊲ b) (q : b ⊲ c) → SFP p → SFP q → SFP (⊲-tr p q)
SFP-tr p C.self sp sq = sp
SFP-tr p (C.lim n q) sp sq = SFP-tr p q sp sq

Walk-Z : ∀ {W₀ V₁} (ac : F.AccY (cnt one)) (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) b {a} (p : a ⊲ b) (ap : W₀ ⊲ a) (lb : Lg b) (bV : b ⊲ V₁) (lV : Lg V₁)
         (ll : one ⊲ V₁) (A₀ : F.Ig (cnt one) V₁) co Y → SFP p → SFL b lb → ZD (F.Walk ac u b p ap lb bV lV ll A₀ co Y)
Walk-Z ac u b C.self ap lb bV lV ll A₀ co Y sp sl τ lt = tt
Walk-Z ac u (alim f) (C.lim n p) ap (stp , wl) bV lV ll A₀ co Y sp (sst , swl) τ lt =
  Walk-Z ac u (f n) p ap (wl n) _ lV ll A₀ co Y sp (swl n) τ lt ,
  (λ m → Walk-Z ac u (f (suc (m + n))) (stp (m + n)) _ (wl (suc (m + n))) _ lV ll A₀ _ _ (sst (m + n)) (swl (suc (m + n))) τ lt)

sf-fst : ∀ {W} b (x : D azero W) → Z x → SFP (sum-fst b x)
sf-fst b n0 z = tt
sf-fst b (x ⨾ y) (zx , zy) = SFP-tr (sum-fst b x) (sum-fst (sum b x) y) (sf-fst b x zx) (sf-fst (sum b x) y zy)
sf-fst b (nl d) z = tt
sf-fst b (nw p x) z = sf-fst b x z
sf-fst b (ni () u) z
sf-fst b (nκ () u) z

sf-lg : ∀ {W} b (x : D azero W) (lb : Lg b) → Z x → SFL b lb → SFL (sum b x) (Lg-sum b x lb)
sf-pt : ∀ {W} b (d : ℕ → D azero W) (lb : Lg b) → (∀ n → Z (d n)) → SFL b lb → ∀ n → SFL (pt b d n) (Lg-pt b d n lb)
sf-lg b n0 lb z s = s
sf-lg b (x ⨾ y) lb (zx , zy) s = sf-lg (sum b x) y (Lg-sum b x lb) zy (sf-lg b x lb zx s)
sf-lg b (nl d) lb z s = (λ n → sf-fst (pt b d n) (d n) (z n)) , sf-pt b d lb z s
sf-lg b (nw p x) lb z s = sf-lg b x lb z s
sf-lg b (ni () u) lb z s
sf-lg b (nκ () u) lb z s
sf-pt b d lb z s zero = s
sf-pt b d lb z s (suc n) = sf-lg (pt b d n) (d n) (Lg-pt b d n lb) (z n) (sf-pt b d lb z s n)
```

**回灌的停滞** (对一切 `nκ` 的分支 $u$): 第 $n$ 格的输出是 `Z` 且它的层的合法性没有后继步, 则第 $n+1$ 格同样. 第 $n+1$ 格走的路径是 `sum-fst` 沿第 $n$ 格的第 0 层输出, 那棵树没有 `n1`, 所以路径没有后继步.

```agda
module _ {W₀ W} (ac : F.AccY (cnt one)) (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : one ⊲ W)
         (A₀ : F.Ig (cnt one) W) (w : D one W) (Y : F.St W) where
  cl : ℕ → F.Cl W W₀ (cnt one)
  cl = F.κc ac u q₀ lW ll A₀ w Y

  dl : ∀ n → F.Df (F.v (cl n))
  dl n = F.κΔ ac u ll A₀ (cl n)

  Rκ : ℕ → Set
  Rκ n = ZD (dl n) × SFL (F.v (cl n)) (F.lv (cl n))

  κ-stall : ∀ n → Rκ n → Rκ (suc n)
  κ-stall n (zd , sl) =
    Walk-Z ac u _ (sum-fst (F.v c) d₀) _ _ C.self _ _ _ _ _ (sf-fst (F.v c) d₀ z₀) sl′ ,
    sl′
    where
    c = cl n
    d₀ = F.yc (dl n) (inj₁ (z⊲ (F.v c))) tt
    z₀ : Z d₀
    z₀ = zd (inj₁ (z⊲ (F.v c))) tt
    sl′ = sf-lg (F.v c) d₀ (F.lv c) z₀ sl

  κ-from : ∀ n → Rκ n → ∀ m → Rκ (m + n)
  κ-from n r zero = r
  κ-from n r (suc m) = κ-stall (m + n) (κ-from n r m)
```

## §4 场景

`Mono u`: `ni` 的分支对坐标的第 0 层值单调 (同 `CvHighInst.Kn-mono`, `CvLayerInst.KL-mono` 的结论形状). 这是树侧的判据, 由 `LayerTrNeg.no-round` 与下面 [L1ValShape](L1ValShape.lagda.md) 逼出.

```agda
Mono : ∀ {W} → (∀ {W′} → W ⊲ W′ → Lg W′ → D azero W′ → D one W′) → Set
Mono {W} u = ∀ {W′} (p : W ⊲ W′) (l : Lg W′) (z z′ : D azero W′) →
             proj₁ (toA z) ≤ proj₁ (toA z′) → S C.self l bz (u p l z) ≼ S C.self l bz (u p l z′)
```

```agda
StepA₁ : F.Ig (cnt one) one
StepA₁ _ _ _ Y = F.Step Y

Ys : F.St one
Ys = F.st (F.df (λ τ lt → n0 ⨾ (n0 ⨾ n1)) n0) n1

out : D one one → D azero one
out x = F.yc (F.Run (F.accCn one) x C.self tt C.self StepA₁ n0 Ys) (inj₁ (z⊲ one)) tt

val : D one one → A
val x = sum azero (out x)
```
