# RecB (一): 底对 $n$ 递归, 一份同底折叠, 一份跨底折叠

> 不含记号. 入口 [RecB](RecB.lagda.md), 接口 [RecBIf](RecBIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 对任一满足接口的 `J` 一条定义. 从 [CRwFold](CRwFold.lagda.md) 导入塔 `Tw`, 种类分类 `cl`, 嵌入, `pick`, `dcl`, 策略 `Po`, 路径 `PS`/`PH`, 累加与形状 (不改原文件).
>
> **与 CRw 的差.**
>
> 1. **底对 $n$ 递归.** 第 $n+1$ 个底 `Sb (suc n) = XSof (Sb n)`: 下标 `Ix` 是 "指标分量" `ix` 或 "第 $c$ 个分量" `cp c`; 指标分量是只含 $\Omega_1$ 的结构 `step S⊥` (这一层的共尾度 $\Omega_1$, 坐标是可数树), 第 $c$ 个分量是第 $n$ 个底上的塔 `Tw (Sb n) (hs c)`. 指标分量的形状同 `LFReTy.Lv (lΩ k g)` 的 `step (Lv k)` 分量 ($k$ 取第 $0$ 层). 层号 $(n, m)$ 读 $\Omega\cdot n+m$.
> 2. **两个折叠, 都对一切底一份.** 同底 `ΦS S fb`: 对任一种类结构 $S$ (底的地板 `fb`), 第 $m$ 层折到第 $t$ 层, 与 CRw 的 `sm` 子句同形. 跨底 `ΦX n`: 从第 $n+1$ 个底折到第 $n$ 个底上的第 $t$ 层, 带世界的界 $B$ 与路径. 第 $c$ 个分量的种类: 底种类一律留; 塔的新种类以 $B$ 为公共上界比较 (`dcx`, 带证据 $c+1\lhd B$). 指标种类 ($\Omega_1$): $n=0$ 时与 $t$ 以 $B$ 为公共上界比较, $n\ge 1$ 时留, 嵌成第 $n$ 个底的指标种类.
> 3. **只有指标种类移动世界** (接口的 `Adm₀`/`nxt₀`/`sh₀`); 分量里的一切种类 (包括下层的 $\Omega_1$) 不动世界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.RecBIf
module OCF.Lean.RecBFold (J : RecBIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open RecBIf J
open CRwIf mv
open import OCF.Lean.CRwFold mv
  using (Tw; Cl; bas; nw; cl; emb; frE; along; frA; Dc; keep; same; above; caseDc; pick; dcl;
         Po; module Po; poΩ; poF; PS; module PS; PH; mul; chain; Σ⁺; lg↓; ⊏⊑; topT;
         Sh; Sh-⊞; Sh-mul; Sh-chain; Sh-Σ; Sh-case)
```

## §1 底

```agda
data Ix : Set where
  ix : Ix
  cp : Cd → Ix

FX : KS → Ix → KS
FX S ix = step S⊥
FX S (cp c) = Tw S (hs c)

XSof : KS → KS
XSof S = sup Ix (FX S)

Sb : ℕ → KS
Sb zero = S⊥
Sb (suc n) = XSof (Sb n)

-- 指标种类 (这一层的 Ω₁)
ιK : ∀ {S} → K (XSof S)
ιK = ix , inj₂ tt
```

**地板.** 第 $n+1$ 个底的地板是指标种类的结点, 分支 $y\mapsto\sum_{c<y}\iota_c(\Omega_{c+1}$ 的结点$)$ (第 $c$ 个分量的地板). $n=0$ 时同 CRw 的 `topL`.

```agda
fl : ∀ n → HB (Sb n)
gtX : ∀ n → Cd → HB (Sb (suc n))
fl zero = hz
fl (suc n) = hΩ ιK (gtX n)
gtX n hz = hz
gtX n (hs c) = gtX n c ⊞ ι {Ix} {FX (Sb n)} (cp c) (topT (Sb n) (fl n) (hs c))
gtX n (hl f) = hl (λ k → gtX n (f k))
gtX n (hΩ () _)

top : ∀ n m → HB (Tw (Sb n) m)
top n = topT (Sb n) (fl n)
```

## §2 世界: 只有指标种类移动

```agda
open Po

pX : ∀ {S} (κ : K (XSof S)) → Po (E (XSof S) κ)
pX (ix , inj₂ _) = poΩ
pX (ix , inj₁ ())
pX (cp _ , _) = poF

PSX : ∀ n → PS (Sb (suc n))
PSX n = record
  { Ev = Ev′ ; Ad = λ B κ → pAd (pX κ) B ; nx = λ B κ → pnx (pX κ) B
  ; ev↑ = ev↑′ ; ad↓ = λ q {κ} → pad↓ (pX κ) q ; nx↑ = λ {B} {κ} → pnx↑ (pX κ) }
  where
  Ev′ : Cd → K (Sb (suc n)) → Set
  Ev′ B (ix , _) = hs hz ⊲ B
  Ev′ B (cp c , _) = hs c ⊲ B
  ev↑′ : ∀ {B B′} → B ⊲ B′ → ∀ {κ} → Ev′ B κ → Ev′ B′ κ
  ev↑′ q {ix , _} ev = ⊲ᴮ-tr ev q
  ev↑′ q {cp c , _} ev = ⊲ᴮ-tr ev q
```

## §3 决定

```agda
-- 第 c 个分量的种类: 底种类留, 新种类以 B 为公共上界比较
dcx : ∀ {S B t c} {κ : K (Tw S (hs c))} → LgB B → t ⊲ B → hs c ⊲ B →
      Cl {S} (hs c) κ → Dc (Tw S) B t (E (Tw S (hs c)) κ)
dcx {t = t} lB pt ev (bas κ₀ to) = keep (emb t κ₀) (λ c′ → to (frE t κ₀ c′))
dcx {S} lB pt ev (nw j pj to) = pick S to (⊲ᴮ-tr pj ev) (cmpB (⊲ᴮ-tr pj ev) pt tt lB)

-- 指标种类: 第 0 个底上与 t 比较; 更高的底上留, 嵌成下一层的指标种类
dcI : ∀ n {B t} → LgB B → t ⊲ B → hs hz ⊲ B → Dc (Tw (Sb n)) B t Cd
dcI zero lB pt o = pick S⊥ (λ c → c) o (cmpB o pt tt lB)
dcI (suc n) {t = t} lB pt o = keep (emb t ιK) (frE t ιK)
```

## §4 同底折叠 (对一切种类结构)

```agda
data AccC (m : Cd) : Set where
  acc : (∀ i → hs i ⊲ m → AccC i) → AccC m

wfC : ∀ m → AccC m
gC : ∀ m i → hs i ⊲ m → AccC i
wfC m = acc (gC m)
gC (hs x) .x hself = wfC x
gC (hs x) i (hsuc p) = gC x i p
gC (hl f) i (hlim n p) = gC (f n) i p
gC (hΩ () _) i _

ΦS : ∀ S (fb : HB S) m → AccC m → LgB m → ∀ t → t ⊲ m → HB (Tw S t) → HB (Tw S m) → HB (Tw S t)
ΦS S fb m a lm t pt b hz = hs hz
ΦS S fb m a lm t pt b (hs h) = hl (mul (ΦS S fb m a lm t pt b h))
ΦS S fb m a lm t pt b (hl f) = hl (Σ⁺ (λ n → ΦS S fb m a lm t pt b (f n)))
ΦS S fb m (acc rs) lm t pt b (hΩ κ g) = caseDc (dcl pt lm (cl m κ))
  (λ κ′ fr → hΩ κ′ (λ c → ΦS S fb m (acc rs) lm t pt b (g (fr c))))
  (λ to → hl (chain b (λ b′ → ΦS S fb m (acc rs) lm t pt b′ (g (to b′)))))
  (λ i pi q to → ΦS S fb i (rs i pi) (lg↓ pi lm) t q b
     (hl (chain (topT S fb i) (λ b′ → ΦS S fb m (acc rs) lm i (⊏⊑ pi) b′ (g (to b′))))))
```

## §5 跨底折叠 (对一切 $n$)

`ΦX n t B lB pt b h nd`: 把第 $n+1$ 个底的高度 $h$ 折到第 $n$ 个底上的第 $t$ 层; 世界的界 $B$ (合法, $t\lhd B$), 当前界 $b$, $h$ 在 $B$ 里带路径 `nd`. 指标种类的分支先回灌再进入新世界; 分量里的种类不动世界.

```agda
ΦX : ∀ n t B → LgB B → t ⊲ B → HB (Tw (Sb n) t) → (h : HB (Sb (suc n))) → PH (PSX n) B h → HB (Tw (Sb n) t)
ΦX n t B lB pt b hz nd = hs hz
ΦX n t B lB pt b (hs h) nd = hl (mul (ΦX n t B lB pt b h nd))
ΦX n t B lB pt b (hl f) nd = hl (Σ⁺ (λ k → ΦX n t B lB pt b (f k) (nd k)))
ΦX n t B lB pt b (hΩ (ix , inj₁ ()) g) nd
ΦX n t B lB pt b (hΩ (ix , inj₂ _) g) (o , pg) = caseDc (dcI n lB pt o)
  (λ κ′ fr → hΩ κ′ (λ c′ →
     ΦX n t (nB (fr c′)) (lN (fr c′)) (⊲ᴮ-tr pt (up′ (fr c′))) b (g (sh₀ B (fr c′))) (pg _ (aS (fr c′)))))
  (λ to → hl (chain b (λ b′ →
     ΦX n t (nB (to b′)) (lN (to b′)) (⊲ᴮ-tr pt (up′ (to b′))) b′ (g (sh₀ B (to b′))) (pg _ (aS (to b′))))))
  (λ i pi q to → ΦS (Sb n) (fl n) i (wfC i) (lg↓ pi lB) t q b
     (hl (chain (top n i) (λ b′ →
        ΦX n i (nB (to b′)) (lN (to b′)) (⊲ᴮ-tr (⊏⊑ pi) (up′ (to b′))) b′ (g (sh₀ B (to b′))) (pg _ (aS (to b′)))))))
  where
  aS : ∀ e → Adm₀ B (sh₀ B e)
  aS e = adm-sh e lB
  nB : Cd → Cd
  nB e = nxt₀ B (sh₀ B e) (aS e)
  lN : ∀ e → LgB (nB e)
  lN e = lg-nx (aS e) lB
  up′ : ∀ e → B ⊲ nB e
  up′ e = nx-up (aS e)
ΦX n t B lB pt b (hΩ (cp c , κ) g) (ev , pg) = caseDc (dcx lB pt ev (cl (hs c) κ))
  (λ κ′ fr → hΩ κ′ (λ c′ → ΦX n t B lB pt b (g (fr c′)) (pg _ tt)))
  (λ to → hl (chain b (λ b′ → ΦX n t B lB pt b′ (g (to b′)) (pg _ tt))))
  (λ i pi q to → ΦS (Sb n) (fl n) i (wfC i) (lg↓ pi lB) t q b
     (hl (chain (top n i) (λ b′ → ΦX n i B lB (⊏⊑ pi) b′ (g (to b′)) (pg _ tt)))))
```

## §6 形状给出的合法

```agda
Sh-ΦS : ∀ S fb m a lm t pt b h → Sh (ΦS S fb m a lm t pt b h)
Sh-ΦS S fb m a lm t pt b hz = tt
Sh-ΦS S fb m a lm t pt b (hs h) = Sh-mul _ (Sh-ΦS S fb m a lm t pt b h)
Sh-ΦS S fb m a lm t pt b (hl f) = Sh-Σ _ (λ n → Sh-ΦS S fb m a lm t pt b (f n))
Sh-ΦS S fb m (acc rs) lm t pt b (hΩ κ g) = Sh-case (dcl pt lm (cl m κ))
  (λ κ′ fr c → Sh-ΦS S fb m (acc rs) lm t pt b (g (fr c)))
  (λ to → Sh-chain b _ (λ b′ → Sh-ΦS S fb m (acc rs) lm t pt b′ (g (to b′))))
  (λ i pi q to → Sh-ΦS S fb i (rs i pi) (lg↓ pi lm) t q b _)

Sh-ΦX : ∀ n t B lB pt b h nd → Sh (ΦX n t B lB pt b h nd)
Sh-ΦX n t B lB pt b hz nd = tt
Sh-ΦX n t B lB pt b (hs h) nd = Sh-mul _ (Sh-ΦX n t B lB pt b h nd)
Sh-ΦX n t B lB pt b (hl f) nd = Sh-Σ _ (λ k → Sh-ΦX n t B lB pt b (f k) (nd k))
Sh-ΦX n t B lB pt b (hΩ (ix , inj₁ ()) g) nd
Sh-ΦX n t B lB pt b (hΩ (ix , inj₂ _) g) (o , pg) = Sh-case (dcI n lB pt o)
  (λ κ′ fr c′ → Sh-ΦX n t _ _ _ b _ _)
  (λ to → Sh-chain b _ (λ b′ → Sh-ΦX n t _ _ _ b′ _ _))
  (λ i pi q to → Sh-ΦS (Sb n) (fl n) i (wfC i) (lg↓ pi lB) t q b _)
Sh-ΦX n t B lB pt b (hΩ (cp c , κ) g) (ev , pg) = Sh-case (dcx lB pt ev (cl (hs c) κ))
  (λ κ′ fr c′ → Sh-ΦX n t B lB pt b _ _)
  (λ to → Sh-chain b _ (λ b′ → Sh-ΦX n t B lB pt b′ _ _))
  (λ i pi q to → Sh-ΦS (Sb n) (fl n) i (wfC i) (lg↓ pi lB) t q b _)
```
