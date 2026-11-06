# 带证据的回灌 (三): 站下标的子结构, 每站头种类的回灌, 无条件闭项

> 不含记号. 入口 [SLFb](SLFb.lagda.md), 接口 [SLFbIf](SLFbIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数.
>
> - **§1 子结构 `SN = SNᵢ kₙ`**, `kₙ n = ofHB (tw n)` 是 [LFReTower](LFReTower.lagda.md) 的第 $n$ 站层号. 种类 $(n,\kappa)$ 就是 `SL` 的种类 $(k_n,\kappa)$, 世界是 `SL` 的世界在站下标上的限制; 高度嵌入 `embN : HB SN → HB SL` 保第一位置 (`embN-⊲`, 世界取限制) 与合法 (`Lg-embN`). 证据是站号: $n\mapsto k_n$ 的像都是对角 $\Lambda$ 的字面第一位置 (`LFReTower.tw`, `FabLFReGen.stage-fst`), 站号之间的相等在 $\mathbb N$ 上判定.
> - **§2 `GenK`**: 顶坐标 `topV` (`SLFbKit`), 基世界逐分量取 `FabLFReGen.w₀Lv`, 底种类 $(0,\mathrm{new})$ (坐标 `HB S⊥`, 读成 `A` 用 `frE⊥`); A-回灌一律有损 (同 `FabLFReGen.GL`).
> - **§3 层**: $B_0=1$, $B_{n+1}=B_n\boxplus\Omega^N_n$, $\Omega^N_n$ = 种类 $(n,\mathrm{new})$ 的 $\Omega$-结点, 分支 $c\mapsto\iota_n(\mathrm{up}\,c)$ ($c$ 过第 $k_n$ 层的值). 最终层 $\Lambda^N=\mathrm{up}(\mathrm{hl}\,B)$.
> - **§4 按级回灌 `lvN`**: 头种类 $(n,\mathrm{new})$ 对**一切** $n$: 有 `KLv` (`headFb`); $n\ge1$ 时级层 $1$, 读回 `SLFbRd.rdQ` (第 1 层数据读进第 $k_n$ 层的值, 结点取该层里可读成 `A` 的种类), $n=0$ 时级层 $0$, 读回 $b\boxplus\mathrm{toB}(\mathrm{sum}\,0\,x)$. 升界: 世界在 $\mathbb N$ 下标 $n$ 处点更新, 换 `step` 的第二分量 (`SLFbKit.kcℕ`, `kcNew`). 深种类 $(n, \mathrm{old}\,\kappa)$: `SLFbKit.kcLv` 给回灌件时级层 $0$, 否则有损.
> - **§5 闭项** `TF`, `Lg-TF`, `fghF` (坍缩 `KindLvTw.collLv`, 折叠 `KindLvRun`).
> - **§6 形状定理** (对照 `fb-lossy`, `top-base`, `head-still-lossy`, `deep-lossy`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SLFbTm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; GenK; tpK; w₀; fbA; LgDn; FbLg; n1)
open import OCF.Align.GenFoldTree using (topStepG; module Tree)
open import OCF.Align.GenFoldInst using (topSupG; ldSup; ldStep)
import OCF.Align.KindLvIf as KI
open KI using (KLv; LvFb)
open import OCF.Align.KindLvTw using (collLv)
open import OCF.Align.LFReTy
open import OCF.Align.LFReTower using (tw; Ω̂)
open import OCF.Align.FabLFReGen using (LvΩ; ldLv; w₀Lv; lw₀Lv; frE⊥; frE⊥-⊲; frE⊥-lg)
open import OCF.Align.RsOwnIf using (rs; rs≤; rsLg; rs-top)
open import OCF.Align.SLFbIf
open import OCF.Align.SLFbKit
import OCF.Align.SLFbRd as SR
```

## §1 子结构

```agda
kₙ : ℕ → LH
kₙ n = ofHB (tw n)

FN : ℕ → KS
FN n = FL (kₙ n)

SN : KS
SN = SNᵢ kₙ

embN : HB SN → HB SL
embN hz = hz
embN (hs a) = hs (embN a)
embN (hl f) = hl (λ n → embN (f n))
embN (hΩ κ g) = hΩ (jN {kₙ} κ) (λ c → embN (g c))

embN-⊲ : ∀ {a b} {w : Wd SL} → a ⊲[ resN kₙ w ] b → embN a ⊲[ w ] embN b
embN-⊲ hself = hself
embN-⊲ (hsuc p) = hsuc (embN-⊲ p)
embN-⊲ (hlim n p) = hlim n (embN-⊲ p)
embN-⊲ (hLim e p) = hLim e (embN-⊲ p)

Lg-embN : ∀ a → LgB a → LgB (embN a)
Lg-embN hz l = tt
Lg-embN (hs a) l = Lg-embN a l
Lg-embN (hl f) (st , l) = (λ {w} n → embN-⊲ {w = w} (st n)) , (λ n → Lg-embN (f n) (l n))
Lg-embN (hΩ κ g) (mo , l) =
  (λ {w} lw e e′ p → embN-⊲ {w = w} (mo {resN kₙ w} (λ n → lw (kₙ n)) e e′ p)) , (λ c lc → Lg-embN (g c) (l c lc))

-- 界在限制下定义相等
res-Bd : ∀ (κ : K SN) c (w : Wd SL) → Bd SN κ c (resN kₙ w) ≡ Bd SL (jN {kₙ} κ) c w
res-Bd κ c w = refl
```

## §2 `GenK`

```agda
tpN : TopG SN
tpN = topSupG ℕ FN (λ n → topStepG (topV (kₙ n)))

GN : GenK SN
GN = record
  { tpK = tpN
  ; w₀ = λ n → w₀Lv (kₙ n) , hz
  ; lw₀ = λ n → lw₀Lv (kₙ n) , tt
  ; aK = 0 , inj₂ tt
  ; frE = frE⊥
  ; frE-lg = λ {e} le → frE⊥-lg e le
  ; frE-mono = λ lw e e′ p → frE⊥-⊲ p
  ; fbA = λ _ → inj₂ tt }

LdN : LgDn SN
LdN = ldSup ℕ FN (λ n → ldStep (ldLv (kₙ n)))

flN : FbLg GN
flN κ = tt
```

## §3 层

```agda
ιN : ∀ n → HB (FN n) → HB SN
ιN n = ι {ℕ} {FN} n

ΩN : ℕ → HB SN
ΩN n = hΩ (n , inj₂ tt) (λ c → ιN n (up c))

Lg-ΩN : ∀ n → LgB (ΩN n)
Lg-ΩN n = (λ {w} lw e e′ p → ι-⊲ {ℕ} {FN} {n} {w = w} (up-⊲ p)) , (λ c lc → Lg-ι n (up c) (Lg-up c lc))

B : ℕ → HB SN
B zero = hs hz
B (suc n) = B n ⊞ ΩN n

lB : ∀ n → LgB (B n)
lB zero = tt
lB (suc n) = Lg-⊞ (B n) (ΩN n) (lB n) (Lg-ΩN n)

ΛN : HB (step SN)
ΛN = up (hl B)

lΛN : LgB ΛN
lΛN = Lg-up (hl B) ((λ n → ⊞-fst (B n) (ΩN n)) , lB)

one⊲N : ∀ {w} → hs hz ⊲[ w ] ΛN
one⊲N = hlim 0 hself
```

## §4 按级回灌

```agda
open Tree SN using (sum; Lg-sum)

-- 第 0 级的回灌件给出级层 0 的 KLv
kc→KLv : ∀ {κ} → KC SN tpN κ → KLv SN tpN ΛN κ
kc→KLv K = record
  { ℓ = hz ; ℓ⊲ = λ {w} → z⊲ᴮ ΛN
  ; rd = λ lW b x → ad K b (sum azero x)
  ; rd-fst = λ {W} lW b x → ad-fst K {proj₁ W} b (sum azero x)
  ; rd-lg = λ lW b x lb → ad-lg K lb (Lg-sum azero x tt)
  ; rs = rs (rk K) ; rs≤ = rs≤ (rk K) ; rsLg = rsLg (rk K) ; rs-top = rs-top (rk K) }

-- 头种类的升界件: ℕ 下标 n 处点更新, 换 step 的第二分量
hdKit : ∀ n → KC SN tpN (n , inj₂ tt)
hdKit n = kcℕ FN (λ m → topStepG (topV (kₙ m))) n (kcNew (topV (kₙ n)))

-- 深种类的回灌件 (路径不经坐标下标时)
dpKit : ∀ n κ → KC (Lv (kₙ n)) (topV (kₙ n)) κ → KC SN tpN (n , inj₁ κ)
dpKit n κ K = kcℕ FN (λ m → topStepG (topV (kₙ m))) n (kcOld (topV (kₙ n)) K)

-- 头种类, 级层 1: 第 1 层的数据读进第 kₙ n 层的值
KH₁ : ∀ n → AK (Lv (kₙ n)) → KLv SN tpN ΛN (n , inj₂ tt)
KH₁ n a = record
  { ℓ = hs hz ; ℓ⊲ = λ {w} → one⊲N {w}
  ; rd = λ lW b x → SR.rdQ SN GN LdN a lW b x
  ; rd-fst = λ lW b x → SR.rdQ-fst SN GN LdN a lW b x
  ; rd-lg = λ lW b x lb → SR.Lg-rdQ SN GN LdN a lW b x lb
  ; rs = rs (rk (hdKit n)) ; rs≤ = rs≤ (rk (hdKit n)) ; rsLg = rsLg (rk (hdKit n)) ; rs-top = rs-top (rk (hdKit n)) }

KH : ∀ n → AK (Lv (kₙ n)) ⊎ ⊤ → KLv SN tpN ΛN (n , inj₂ tt)
KH n (inj₁ a) = KH₁ n a
KH n (inj₂ _) = kc→KLv (hdKit n)

KHn : ∀ n → KLv SN tpN ΛN (n , inj₂ tt)
KHn n = KH n (akV (kₙ n))

lvN : LvFb SN tpN ΛN
lvN (n , inj₂ tt) = inj₁ (KHn n)
lvN (n , inj₁ κ) = mapS (λ K → kc→KLv (dpKit n κ K)) (kcLv (kₙ n) κ)
```

## §5 无条件闭项

```agda
collN : Σ A Lg
collN = collLv GN LdN flN ΛN lΛN one⊲N lvN

TF : A
TF = proj₁ collN

Lg-TF : Lg TF
Lg-TF = proj₂ collN

ordF : A → FLv.Ordᶜ FLv.zero
ordF azero = FLv.zero
ordF (asuc a) = FLv.suc (ordF a)
ordF (alim f) = FLv.lim (λ n → ordF (f n))

fghF : ℕ → ℕ
fghF = FLv.FGH (ordF TF)
```

## §6 形状定理

**每站头种类有回灌 (对照 `RsOwnTm.head-still-lossy`, `FabLFReGen.fb-lossy`).** 接口 §3 `HdFb` 的实例, 对一切站号.

```agda
headFb : HdFb kₙ tpN ΛN lvN
headFb n = KHn n , refl
```

**第 $n\ge2$ 站的层号含函数分支, 头种类仍有回灌.** 先证塔的形状: 第 $m+2$ 项的头是第 0 层新种类的 $\Omega$-结点.

```agda
tw-shape : ∀ m → Σ (HB (Lv lz) → HB SL) (λ g → tw (suc (suc m)) ≡ hΩ (νL lz) g)
tw-shape zero = _ , refl
tw-shape (suc m) = (λ c → Ω̂ (proj₁ (tw-shape m) c)) , cong Ω̂ (proj₂ (tw-shape m))

stage-lΩ : ∀ m → Σ (HB (Lv lz) → LH) (λ h → kₙ (suc (suc m)) ≡ lΩ lz h)
stage-lΩ m = (λ c → ofHB (proj₁ (tw-shape m) c)) , cong ofHB (proj₂ (tw-shape m))

-- 第 n+1 站 (n ≥ 0) 的层里有可读成 A 的种类
HasAK : LH → Set
HasAK k = Σ (AK (Lv k)) (λ a → akV k ≡ inj₁ a)

akV-suc : ∀ m → HasAK (kₙ (suc m))
akV-suc zero = akNew , refl
akV-suc (suc m) = subst HasAK (sym (proj₂ (stage-lΩ m))) (_ , refl)

ℓ-of : ∀ n (s : AK (Lv (kₙ n)) ⊎ ⊤) → Σ (AK (Lv (kₙ n))) (λ a → s ≡ inj₁ a) → KI.ℓ (KH n s) ≡ hs hz
ℓ-of n .(inj₁ a) (a , refl) = refl

-- 第 n+1 站起头种类的级层是 1 (读回 rdQ), 第 0 站是 0
head-ℓ1 : ∀ m → KI.ℓ (KHn (suc m)) ≡ hs hz
head-ℓ1 m = ℓ-of (suc m) (akV (kₙ (suc m))) (akV-suc m)

head-ℓ0 : KI.ℓ (KHn 0) ≡ hz
head-ℓ0 = refl

-- 升界后头种类的顶恰是 v (精确, 对一切站号, 含层号含函数的站)
head-rs-top : ∀ n w v → top tpN (n , inj₂ tt) (KI.rs (KHn n) w v) ≡ v
head-rs-top n w v = KI.rs-top (KHn n)
```

**深种类 (对照 `NegStratTw.deep-lossy`).** 第 2 站层号是 `lΩ lz _`: 读回分量 `inj₂ c` (下标是坐标) 之下的一切种类有损; 左分量 `inj₁ tt` 的新种类 (第 0 层值的种类, 坐标 `HB S⊥`) 有回灌, 级层 0.

```agda
deep2-lossy : ∀ c κ → lvN (2 , inj₁ (inj₂ c , κ)) ≡ inj₂ tt
deep2-lossy c κ = refl

deep2-left-fed : Σ (KLv SN tpN ΛN (2 , inj₁ (inj₁ tt , inj₂ tt))) (λ L → lvN (2 , inj₁ (inj₁ tt , inj₂ tt)) ≡ inj₁ L)
deep2-left-fed = _ , refl

-- A-回灌仍一律有损 (同 fb-lossy); 回灌全部经 lv
fb-lossyN : ∀ κ → fbA GN κ ≡ inj₂ tt
fb-lossyN κ = refl
```

**基世界的顶是底 (对照 `FabLFReGen.top-base`).** 回灌之前的世界与 `SL` 的一样; 升高靠折叠里的 `rs`.

```agda
top-base-V : ∀ k κ → top (topV k) κ (w₀Lv k) ≡ bot (Lv k) κ
top-base-V lz ()
top-base-V (ls x) (inj₁ κ) = top-base-V x κ
top-base-V (ls x) (inj₂ _) = refl
top-base-V (ll f) (n , κ) = top-base-V (f n) κ
top-base-V (lΩ k g) (inj₁ _ , inj₁ κ) = top-base-V k κ
top-base-V (lΩ k g) (inj₁ _ , inj₂ _) = refl
top-base-V (lΩ k g) (inj₂ c , κ) = top-base-V (g c) κ

top-baseN : ∀ κ → top tpN κ (w₀ GN) ≡ bot SN κ
top-baseN (n , inj₁ κ) = top-base-V (kₙ n) κ
top-baseN (n , inj₂ _) = refl
```

**读回看见数据 (不是常数; 对照接口头的 "盲").** 对一切站号, 头种类的读回把数据 `n1` (后继) 读成 $b+1$.

```agda
rd-n1-at : ∀ n (s : AK (Lv (kₙ n)) ⊎ ⊤) {W} (lW : LgW (step SN) W) b → KI.rd (KH n s) lW b n1 ≡ hs b
rd-n1-at n (inj₁ a) lW b = refl
rd-n1-at n (inj₂ _) lW b = refl

rd-n1 : ∀ n {W} (lW : LgW (step SN) W) b → KI.rd (KHn n) lW b n1 ≡ hs b
rd-n1 n lW b = rd-n1-at n (akV (kₙ n)) lW b
```

**嵌入到 `SL`: 头结点是 `SL` 的站新种类.**

```agda
emb-head : ∀ n → embN (ΩN n) ≡ hΩ (νL (kₙ n)) (λ c → embN (ιN n (up c)))
emb-head n = refl
```
