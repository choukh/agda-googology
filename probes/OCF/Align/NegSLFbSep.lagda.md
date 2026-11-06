# `SL` 上带证据的回灌, 否定一路 (一): 在一个含函数的站号上 "升一份留别份" 是分离子

> 不含记号. 入口 [NegSLFb](NegSLFb.lagda.md). 本篇**不依赖**构造一路的接口 `SLFbIf` (接口定稿之前写的部分). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FEΩ` (只对 `HB (Lv k) → LH`) 只在标 "条件" 的定理里作前提.
>
> **问题.** [FabLFReGen](FabLFReGen.lagda.md) §4 的判断: `SL` 的世界是以层号 `LH` 为下标的积 (`Wd SL = (k : LH) → Wd (FL k)`), 第 $n$ 站 ($n\ge2$) 的层号 `ofHB (tw n)` 的头是 `lΩ lz (λ c → …)`, 所以 "恰好升这一站的分量, 别处不动" 落在 `upd₁-sep`, `updHΛ-sep` 一族的定义域里. 本篇把它写成定理, 并比已有的几条更窄地划定前提:
>
> - **只要一个固定的下标.** 已有的 `upd₁-sep`, `updH₁-sep` 要求对**一族**下标 `jx f` 一致地点更新. 这里只要求在**一个**固定的层号 $s=\mathrm{l\Omega}\,k\,g$ 上: 有一个世界操作把 $\Omega_{s+1}$ (`νL s`, 坐标 `HB (Lv s)`, 是高度) 的界升到 $1$ 以上, 而对一切 $k'\neq s$ 不升 `νL k′` 的界. 证明里用到的别的下标是 $s$ 的 "补丁" `kα k g α = lΩ k (patch α g)`: 在坐标 `num n` 处, $\alpha\,n$ 为真时把分支换成 `ls (g c)`.
> - **世界可以带证据.** 世界类型限制到任一满足 `P` 的世界, 只要基世界 `w₀ GL` 满足 `P` (`updP-sep`). 所以给世界加证据 (同界, 上界等) 躲不开这一条, 只要基世界仍在里面.
> - **每一站 $n\ge2$ 都是这种下标** (`tw-hΩ`, `stage-lΩ`: `ofHB (tw (n+2)) ≡ lΩ lz g`, 定理). 第 $0, 1$ 站 (`lz`, `ls lz`) 的点更新是构造 (`updLz`, `updLs`, 按模式).
>
> **只否定什么.** 只否定: 在 `SL` 的世界 (或其任一含基世界的子类) 上, 同时满足 "升 `νL s` 到 $1$ 以上" 与 "对裸下标 $k'\neq s$ 不升 `νL k′`" 的操作, 其中 $s$ 的头是 `lΩ`. **不否定**: 只升不留 (`upAllL`, 一切分量一起升); 只留不升 (`stayL`); 下标可判定处的点更新 (`updLz`, `updLs`); 带公共上界或带证据的 "一起升" (本篇不碰, 见 [NegSLFbSh](NegSLFbSh.lagda.md)); 有损回灌. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSLFbSep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy
open import OCF.Align.LFReTower using (tw; Ω̂)
open import OCF.Align.FabLFReGen using (GL; w₀Lv)
open import OCF.Align.GenFoldIf using (w₀)
open import OCF.Align.ColimWNeg using (WLPO)
open import OCF.Align.NegKindLvUpd using (notz; one⊀z)
```

## §0 层号上的工具

`ls` 没有不动点 (结构递归, 不用外延). `dep`: 层号前面 `ls` 的个数. `num n`: 任一种类结构里的有限高度 $n$; `nat`: 数出前面的 `hs`.

```agda
unls : LH → LH
unls (ls y) = y
unls y = y

dep : LH → ℕ
dep (ls y) = suc (dep y)
dep _ = zero

suc≢ : ∀ n → ¬ (suc n ≡ n)
suc≢ zero ()
suc≢ (suc n) e = suc≢ n (cong pred e)
  where pred : ℕ → ℕ
        pred zero = zero
        pred (suc m) = m

num : ∀ {S : KS} → ℕ → HB S
num zero = hz
num (suc n) = hs (num n)

nat : ∀ {S : KS} → HB S → ℕ
nat (hs c) = suc (nat c)
nat _ = zero

nat-num : ∀ {S : KS} n → nat {S} (num {S} n) ≡ n
nat-num zero = refl
nat-num (suc n) = cong suc (nat-num n)
```

## §1 补丁: 一个固定的 `lΩ`-层号旁边的一族层号

`patch α g c`: $\alpha$ 在 `nat c` 处为真时把分支换成 `ls (g c)`, 否则原样. `kα k g α = lΩ k (patch α g)`. 不用外延就能从 `kα k g α ≡ lΩ k g` 读出 $\alpha$ 全假 (`eq→F`): 在坐标 `num n` 处比较 `dep`. 反方向要外延 (`F→eq`, 条件).

```agda
sel : Bool → LH → LH
sel true y = ls y
sel false y = y

patch : ∀ {k : LH} → (ℕ → Bool) → (HB (Lv k) → LH) → HB (Lv k) → LH
patch α g c = sel (α (nat c)) (g c)

kα : (k : LH) → (HB (Lv k) → LH) → (ℕ → Bool) → LH
kα k g α = lΩ k (patch {k} α g)

-- 在 lΩ 节点的第 n 个有限坐标处读 dep (对一切 k, 不必比较 k)
depAt : LH → ℕ → ℕ
depAt (lΩ k h) n = dep (h (num n))
depAt _ n = zero

sel-dep : ∀ b y → dep (sel b y) ≡ dep y → b ≡ false
sel-dep true y e = ⊥-elim (suc≢ (dep y) e)
sel-dep false y e = refl

eq→F : ∀ k g α → kα k g α ≡ lΩ k g → ∀ n → α n ≡ false
eq→F k g α e n = sel-dep (α n) (g (num n)) (subst (λ m → dep (sel (α m) (g (num n))) ≡ dep (g (num n))) (nat-num {Lv k} n) (cong (λ x → depAt x n) e))

-- 函数外延, 只对 HB (Lv k) → LH, 只作前提
FEΩ : Set
FEΩ = ∀ (k : LH) (g g′ : HB (Lv k) → LH) → (∀ c → g c ≡ g′ c) → g ≡ g′

F→eq : FEΩ → ∀ k g α → (∀ n → α n ≡ false) → kα k g α ≡ lΩ k g
F→eq fe k g α h = cong (lΩ k) (fe k (patch {k} α g) g pt)
  where
  pt : ∀ c → patch {k} α g c ≡ g c
  pt c = cong (λ b → sel b (g c)) (h (nat c))
```

**分离子.** `SepAt k g`: 对一切 $\alpha$, 或 $\alpha$ 全假, 或补丁不等于原层号. 弱判定 (`WDecAt`) 推出它; 加 `FEΩ` 推出 WLPO.

```agda
SepAt : (k : LH) → (HB (Lv k) → LH) → Set
SepAt k g = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (kα k g α ≡ lΩ k g)

WDecAt : (k : LH) → (HB (Lv k) → LH) → Set
WDecAt k g = ∀ (α : ℕ → Bool) → ¬ (kα k g α ≡ lΩ k g) ⊎ ¬ ¬ (kα k g α ≡ lΩ k g)

wdec→sep : ∀ k g → WDecAt k g → SepAt k g
wdec→sep k g D α with D α
... | inj₁ ne = inj₂ ne
... | inj₂ nn = inj₁ nnF
  where
  nnF : ∀ n → α n ≡ false
  nnF n with α n in eq
  ... | false = refl
  ... | true = ⊥-elim (nn (λ e → t≢f (trans (sym eq) (eq→F k g α e n))))
    where t≢f : ¬ (true ≡ false)
          t≢f ()

sep→WLPO : FEΩ → ∀ k g → SepAt k g → WLPO
sep→WLPO fe k g S α with S α
... | inj₁ h = inj₁ h
... | inj₂ ne = inj₂ (λ h → ne (F→eq fe k g α h))
```

## §2 在一个固定的 `lΩ`-层号上点更新 ⇒ 分离子

`PtUpdP s P`: 世界限制在满足 $P$ 的世界上 (带证据); `upd` 把 $\Omega_{s+1}$ (`νL s`) 的界升到 $1$ 以上 (`raise`); 对一切裸下标 $k'\ne s$, `νL k′` 在新世界里的界之下的, 在旧世界里也在界之下 (`keep`). 基世界 `wb = w₀ GL`: 每个分量的新界都是 $0$.

```agda
wb : Wd SL
wb = w₀ GL

record PtUpdP (s : LH) (P : Wd SL → Set) : Set where
  field
    upd   : (w : Wd SL) → P w → Wd SL
    raise : ∀ w p → Bd SL (νL s) (hs hz) (upd w p)
    keep  : ∀ w p k → ¬ (k ≡ s) → ∀ {c} → Bd SL (νL k) c (upd w p) → Bd SL (νL k) c w

-- 不带证据的版本
PtUpd : LH → Set
PtUpd s = PtUpdP s (λ _ → ⊤)

wdecP : ∀ k g {P} → P wb → PtUpdP (lΩ k g) P → WDecAt k g
wdecP k g {P} p₀ U α = go (proj₂ (W (kα k g α))) refl
  where
  open PtUpdP U
  s = lΩ k g
  W : Wd SL
  W = upd wb p₀
  r1 : Bd SL (νL s) (hs hz) W
  r1 = raise wb p₀
  go : ∀ v → proj₂ (W (kα k g α)) ≡ v → ¬ (kα k g α ≡ s) ⊎ ¬ ¬ (kα k g α ≡ s)
  go hz eq = inj₁ (λ e → one⊀z (subst (λ b → hs hz ⊲[ proj₁ (W (kα k g α)) ] b) eq (h e)))
    where
    h : kα k g α ≡ s → Bd SL (νL (kα k g α)) (hs hz) W
    h e = subst (λ x → Bd SL (νL x) (hs hz) W) (sym e) r1
  go (hs v) eq = inj₂ (λ ne → notz (λ ()) (keep wb p₀ (kα k g α) ne (subst (λ b → hs v ⊲[ proj₁ (W (kα k g α)) ] b) (sym eq) hself)))
  go (hl f) eq = inj₂ (λ ne → notz (λ ()) (keep wb p₀ (kα k g α) ne (subst (λ b → hl f ⊲[ proj₁ (W (kα k g α)) ] b) (sym eq) hself)))
  go (hΩ κ f) eq = inj₂ (λ ne → notz (λ ()) (keep wb p₀ (kα k g α) ne (subst (λ b → hΩ κ f ⊲[ proj₁ (W (kα k g α)) ] b) (sym eq) hself)))

updP-sep : ∀ k g {P} → P wb → PtUpdP (lΩ k g) P → SepAt k g
updP-sep k g p₀ U = wdec→sep k g (wdecP k g p₀ U)

upd-sep : ∀ k g → PtUpd (lΩ k g) → SepAt k g
upd-sep k g U = updP-sep k g tt U

updP→WLPO : FEΩ → ∀ k g {P} → P wb → PtUpdP (lΩ k g) P → WLPO
updP→WLPO fe k g p₀ U = sep→WLPO fe k g (updP-sep k g p₀ U)
```

**升到任意 $v$ 的版本是推论.** 按级回灌要的形状是把 `νL s` 的界置成任意 $v$ : `HB (Lv s)`; 取 $v=1$ 就是 `PtUpdP`.

```agda
record PtUpdVP (s : LH) (P : Wd SL → Set) : Set where
  field
    updV   : (w : Wd SL) → P w → HB (Lv s) → Wd SL
    raiseV : ∀ w p v → Bd SL (νL s) v (updV w p v)
    keepV  : ∀ w p v k → ¬ (k ≡ s) → ∀ {c} → Bd SL (νL k) c (updV w p v) → Bd SL (νL k) c w

v→1 : ∀ {s P} → PtUpdVP s P → PtUpdP s P
v→1 U = record
  { upd = λ w p → updV w p (hs hz)
  ; raise = λ w p → raiseV w p (hs hz)
  ; keep = λ w p k ne b → keepV w p (hs hz) k ne b }
  where open PtUpdVP U

updVP-sep : ∀ k g {P} → P wb → PtUpdVP (lΩ k g) P → SepAt k g
updVP-sep k g p₀ U = updP-sep k g p₀ (v→1 U)
```

## §3 每一站 $n\ge2$ 的层号都是 `lΩ lz g`

`tw 2 = Ω̂ 1` 的头是 $\Omega$-节点, 种类 `νL lz`; `Ω̂` 在 $\Omega$-节点上逐分支 (`Ω̂ (hΩ κ g) = hΩ κ (Ω̂ ∘ g)`), 所以以后各站的头种类不变. 读成层号, 头是 `lΩ lz`.

```agda
tw-hΩ : ∀ n → Σ (HB S⊥ → HB SL) (λ g → tw (suc (suc n)) ≡ hΩ (νL lz) g)
tw-hΩ zero = _ , refl
tw-hΩ (suc n) with tw-hΩ n
... | g , e = _ , cong Ω̂ e

stage-lΩ : ∀ n → Σ (HB S⊥ → LH) (λ g → ofHB (tw (suc (suc n))) ≡ lΩ lz g)
stage-lΩ n = (λ c → ofHB (proj₁ (tw-hΩ n) c)) , cong ofHB (proj₂ (tw-hΩ n))

-- 推论: 第 n+2 站的层号上的点更新 (世界可带任一含基世界的证据) ⇒ 分离子
stage-sep : ∀ n {P} → P wb → PtUpdP (ofHB (tw (suc (suc n)))) P → SepAt lz (proj₁ (stage-lΩ n))
stage-sep n p₀ U = updP-sep lz (proj₁ (stage-lΩ n)) p₀ (subst (λ s → PtUpdP s _) (proj₂ (stage-lΩ n)) U)

stage-sep→WLPO : FEΩ → ∀ n {P} → P wb → PtUpdP (ofHB (tw (suc (suc n)))) P → WLPO
stage-sep→WLPO fe n p₀ U = sep→WLPO fe lz (proj₁ (stage-lΩ n)) (stage-sep n p₀ U)

-- 第 0, 1 站的层号: lz, ls lz (不含函数)
stage0 : ofHB (tw 0) ≡ lz
stage0 = refl

stage1 : ofHB (tw 1) ≡ ls lz
stage1 = refl
```

## §4 前提可满足

**两半各自可满足.** 只升: 每个分量的新界换成 $1\boxplus$ 旧界 (`upAllL`, 不看下标). 只留: 世界不动 (`stayL`). 只升的那一半把每个 `νL k′` 都升了 (`upAllL-moves`).

```agda
upAllL : Wd SL → Wd SL
upAllL w k = proj₁ (w k) , hs hz ⊞ proj₂ (w k)

halfR : ∀ s w → Bd SL (νL s) (hs hz) (upAllL w)
halfR s w = ⊞-fst (hs hz) (proj₂ (w s))

upAllL-moves : ∀ w k → Bd SL (νL k) (hs hz) (upAllL w)
upAllL-moves w k = ⊞-fst (hs hz) (proj₂ (w k))

stayL : Wd SL → Wd SL
stayL w = w

halfK : ∀ s w k → ¬ (k ≡ s) → ∀ {c} → Bd SL (νL k) c (stayL w) → Bd SL (νL k) c w
halfK s w k ne b = b

-- 前提 P wb 的实例: 平凡证据
p₀⊤ : (λ (_ : Wd SL) → ⊤) wb
p₀⊤ = tt
```

**下标可判定时两半同时成立.** 第 0 站 (`lz`) 与第 1 站 (`ls lz`) 的层号可以按模式匹配, 点更新是构造.

```agda
updLz : Wd SL → Wd SL
updLz w lz = proj₁ (w lz) , hs hz ⊞ proj₂ (w lz)
updLz w (ls x) = w (ls x)
updLz w (ll f) = w (ll f)
updLz w (lΩ k g) = w (lΩ k g)

PtLz : PtUpd lz
PtLz = record { upd = λ w _ → updLz w ; raise = λ w _ → ⊞-fst (hs hz) (proj₂ (w lz)) ; keep = kp }
  where
  kp : ∀ w (p : ⊤) k → ¬ (k ≡ lz) → ∀ {c} → Bd SL (νL k) c (updLz w) → Bd SL (νL k) c w
  kp w p lz ne b = ⊥-elim (ne refl)
  kp w p (ls x) ne b = b
  kp w p (ll f) ne b = b
  kp w p (lΩ k g) ne b = b

updLs : Wd SL → Wd SL
updLs w lz = w lz
updLs w (ls lz) = proj₁ (w (ls lz)) , hs hz ⊞ proj₂ (w (ls lz))
updLs w (ls (ls x)) = w (ls (ls x))
updLs w (ls (ll f)) = w (ls (ll f))
updLs w (ls (lΩ k g)) = w (ls (lΩ k g))
updLs w (ll f) = w (ll f)
updLs w (lΩ k g) = w (lΩ k g)

PtLs : PtUpd (ls lz)
PtLs = record { upd = λ w _ → updLs w ; raise = λ w _ → ⊞-fst (hs hz) (proj₂ (w (ls lz))) ; keep = kp }
  where
  kp : ∀ w (p : ⊤) k → ¬ (k ≡ ls lz) → ∀ {c} → Bd SL (νL k) c (updLs w) → Bd SL (νL k) c w
  kp w p lz ne b = b
  kp w p (ls lz) ne b = ⊥-elim (ne refl)
  kp w p (ls (ls x)) ne b = b
  kp w p (ls (ll f)) ne b = b
  kp w p (ls (lΩ k g)) ne b = b
  kp w p (ll f) ne b = b
  kp w p (lΩ k g) ne b = b
```

## §5 结论 (按档)

- **[定理, 否定]** **`updP-sep`** (对一切 $k, g$, 一切含基世界的证据 $P$: `PtUpdP (lΩ k g) P` ⇒ `SepAt k g`), `upd-sep`, **`updVP-sep`** (升到任意 $v$), **`stage-sep`** (第 $n+2$ 站的层号). **[条件 `FEΩ`]** `updP→WLPO`, `stage-sep→WLPO`, `F→eq`, `sep→WLPO`.
- **[定理]** `eq→F` (不用外延: 补丁等于原层号 ⇒ $\alpha$ 全假), `wdec→sep`, **`tw-hΩ`**, **`stage-lΩ`** (每站 $n\ge2$ 的层号是 `lΩ lz g`), `stage0`, `stage1`.
- **[定理, 前提实例]** `halfR`, `halfK` (两半各自可满足), `upAllL-moves` (只升的那一半升了每个分量), `PtLz`, `PtLs` (第 0, 1 站上点更新是构造), `p₀⊤`.
- **[判断]** 与已有分离子 (`upd₁-sep`, `updH₁-sep`, `updHΛ⁺-sep`) 相比, 本篇的前提只涉及**一个**下标 $s$; 墙不来自 "一族下标", 来自 "对一个含函数的层号与任意裸下标判等". 分离子 `SepAt` 经典地成立 (判断), `FEΩ` 在 Agda 里证不出也否证不了 (判断, 与 `FE₀` 同档).
