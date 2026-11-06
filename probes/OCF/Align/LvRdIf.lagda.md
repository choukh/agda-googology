# 读回包 + 第 ω+1 级折叠: 接口

> **接口定稿 2026-11-05 14:28 (编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 作者选定原话: "A3: 读回包 + 第 ω+1 级折叠". 构造一路 `LvRd*`, 否定一路 `NegLvRd*`, 共用本篇. 本篇只放类型与记录, 不放证明. 依赖 [LvFbCode](LvFbCode.lagda.md) (路径码 `Code`, `tgt`, `code-≟`), [FamFoldRead](FamFoldRead.lagda.md) 的层 `ly`, [FamFoldIf](FamFoldIf.lagda.md) 的塔 `Sk`, 两种种类折叠的数据树 `D` ([HtTowerFTree](HtTowerFTree.lagda.md)). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **对象.**
>
> - **§1 坐标 ω, ω+1.** 第 $\omega$ 级的种类结构 `Gω = sup ℕ Sk` (种类 $(n,\kappa)$, $\kappa$ 是第 $n$ 级塔 `Sk n` 的种类); 第 $\omega+1$ 级 `Gω1 = step Gω` (新种类的坐标是 `HB Gω`). 它们的读回层: `lyω = hl (n ↦ ly (n+1))`, `lyω1 = hs lyω`. 有限级沿用 `Sk n` 与 `ly (n+1)` (层号 $c$ 的读回层是 $1+c$).
> - **§2 读回包对坐标推广.** `RdC T L`: 层 $L$ 的树读成 `HB T` (底是第一位置, 底合法则读出合法), 加反方向的翻译 `tr : HB T → D L`. 有限级 `RdC (Sk n) (ly (n+1))` 就是 `FamFoldRead.Pkg n` 在 `≤r` 处的两个分量; `PkgΩ` 是对角 (一切有限级) 加 $\omega$ 与 $\omega+1$ 两级.
> - **§3 下降.** `Dn T`: `HB T` 到两种种类的层 `Ht`, 合法输入给合法输出. 混合高度的下降是 `Dn Gω`.
> - **§4 世界.** 外层界固定为 $\omega+1$; 下标是**码** `Cd` (从界往下的路径: 停, 进后继, 进第 $n$ 支; 数据, 相等可判定), 码 $k$ 处的槽类型 `Pc k` 由码的结构给出 (ω 的码 `kω` 处是 `Gω`, 有限码 `kfin n` 处是 `Sk n`, 定义相等, 不经搬运). 世界只放槽. 更新记录 `Raise`.
> - **§5 第 ω+1 级折叠.** `FoldΩ1 R`: 层 `HB Gω1` ↦ 第 $\omega$ 层的树 `D lyω`; 新种类的结点处是一条世界链上的 ℕ-极限, 链的每一步在码 `kω` 上更新, 增量是折叠自己输出的函数 (`inc`), 分支读当前世界在 `kω` 的槽.
> - **§6 ω 层的槽由有限级回灌给出.** `ShapeΩ1`: 一条世界链, 第 $n+1$ 步把第 $n+1$ 级级顶的读回 (经 `ι (n+1)`) 接到 `kω` 的槽上; 极限世界 `V∞` 在 `kω` 的槽是链上各槽的 ℕ-极限.
> - **§7 W1 与 W2 合并 (码的弱化).** `WkLaw`: 外层界沿字面路径 $p : b\lhd_{[a]} b'$ 长高时, 旧码弱化成新码 (`wk p`); 目标不变, 单射, 与 `code-≟` 相容, 对路径复合函子. `Stages`: 外层界是增量的部分和 (W1), 第 $s+1$ 站的码在新界之下, 目标是旧界 (W2).
> - **§8 "层号由回灌给出" 的形状.** `LvShape`: `Stages` 的增量 $\sigma_s$ 是第 $s$ 站回灌输出 (降到 `Ht`) 经一个**与站号无关**的读法 `σ-of` 给出; 于是第 $s+1$ 站的层号 (码的目标) 是此前各站输出的读法的部分和.
>
> **律的定义域 (逐条).** 律里出现的每一对下标都带字面公共上界:
>
> - `Raise` 的 `at`, `off`, `mono`, `legal`: 下标是 `Cd` 的码, 都是同一个外层界 $\omega+1$ 之下的路径 (槽类型 `Pc` 对这个界写成); 码是数据, `off` 的 "不相等" 是数据的不相等, 可判定. 没有对坐标 (高度) 的律.
> - `FoldΩ1` 的 `ch-s`, `fold-Ω`: 只有一个码 `kω`.
> - `ShapeΩ1` 的 `V-s`, `slot∞`: 只有一个码 `kω`.
> - `WkLaw` 的 `wk-tgt`: 一个码 $k$ (界 $b$ 之下) 与证据 $p : b\lhd b'$; `wk-inj`, `wk-≟`: 两个码 $k, k'$ 在**同一个**界 $b$ 之下, 同一条 $p$; `wk-tr`: 一个码, 两条可复合的证据 $p : b\lhd b'$, $q : b'\lhd b''$. 弱化后的码都在 $b'$ (或 $b''$) 之下.
> - `Stages` 的 `κ-tgt`: 第 $s$ 站的码在界 `B (s+1)` 之下, 公共上界 `B (s+1)`; `B-s` 不含下标.
> - `LvShape` 的 `σ-is`: 不含下标.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvRdIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; D; nl)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.FamFoldRead using (ly)
open import OCF.Align.LvFbCode using (Code; tgt; code-≟; _⊲₀[_]_)
```

## §1 坐标 ω, ω+1

```agda
Gω : KS
Gω = sup ℕ Sk

Gω1 : KS
Gω1 = step Gω

lyω : Ht
lyω = hl (λ n → ly (suc n))

lyω1 : Ht
lyω1 = hs lyω
```

## §2 读回包对坐标推广

```agda
record RdC (T : KS) (L : Ht) : Set where
  field
    rdr : ∀ {W} → LgW₂ W → HB T → D L W → HB T
    fst : ∀ {W} (lW : LgW₂ W) b (x : D L W) {w} → b ⊲[ w ] rdr lW b x
    lgr : ∀ {W} (lW : LgW₂ W) b (x : D L W) → LgB b → LgB (rdr lW b x)
    tr  : ∀ {W} → HB T → D L W

-- 对角 (一切有限级) 加 ω 与 ω+1
PkgΩ : Set
PkgΩ = (∀ n → RdC (Sk n) (ly (suc n))) × RdC Gω lyω × RdC Gω1 lyω1
```

## §3 下降

```agda
Dn : KS → Set
Dn T = Σ (HB T → Ht) (λ d → ∀ x → LgB x → LgB (d x))
```

## §4 世界: 外层界 ω+1 之下的码, 只有槽

```agda
data Cd : Set where
  cH : Cd
  cP : Cd → Cd
  cL : ℕ → Cd → Cd

-- 有限界 fin n 之下的码 r 处的槽类型
Pf : Cd → ℕ → KS
Pf cH n = Sk n
Pf (cP r) (suc n) = Pf r n
Pf _ _ = S₀

-- 外层界 ω+1 之下的码处的槽类型
Pc : Cd → KS
Pc cH = Gω1
Pc (cP cH) = Gω
Pc (cP (cL n r)) = Pf r n
Pc _ = S₀

kω : Cd
kω = cP cH

kfin : ℕ → Cd
kfin n = cP (cL n cH)

Wld : Set
Wld = (k : Cd) → HB (Pc k)

LgV : Wld → Set
LgV v = ∀ k → LgB (v k)

record Raise : Set where
  field
    raise : Wld → (k₀ : Cd) → HB (Pc k₀) → Wld
    at    : ∀ v k₀ δ → raise v k₀ δ k₀ ≡ v k₀ ⊞ δ
    off   : ∀ v k₀ δ k → ¬ (k₀ ≡ k) → raise v k₀ δ k ≡ v k
    mono  : ∀ v k₀ δ k {w} → v k ⊲[ w ] raise v k₀ δ k
    legal : ∀ v k₀ δ → LgB δ → LgV v → LgV (raise v k₀ δ)
```

## §5 第 ω+1 级折叠

```agda
OutΩ : Set
OutΩ = (W : Wd₂) → D lyω W

record FoldΩ1 (R : Raise) : Set where
  field
    fold   : Wld → HB Gω1 → OutΩ
    inc    : OutΩ → HB Gω
    lg-inc : ∀ o → LgB (inc o)
    chain  : Wld → (HB Gω → HB Gω1) → ℕ → Wld
    ch-z   : ∀ v g → chain v g zero ≡ v
    ch-s   : ∀ v g k → chain v g (suc k) ≡
             Raise.raise R (chain v g k) kω (inc (fold (chain v g k) (g (chain v g k kω))))
    fold-Ω : ∀ v g W → fold v (hΩ (inj₂ tt) g) W ≡ nl (λ k → fold (chain v g k) (g (chain v g k kω)) W)
    ch-lg  : ∀ v g → LgV v → ∀ k → LgV (chain v g k)
```

## §6 ω 层的槽由有限级回灌给出

```agda
record ShapeΩ1 (R : Raise) : Set where
  field
    rt    : ∀ n → HB (Sk (suc n))          -- 第 n+1 级级顶折叠输出的读回
    V     : ℕ → Wld
    V-z   : ∀ k → LgB (V zero k)
    V-s   : ∀ n → V (suc n) ≡ Raise.raise R (V n) kω (ι {F = Sk} (suc n) (rt n))
    V∞    : Wld
    slot∞ : V∞ kω ≡ hz ⊞ hl (λ N → V (suc N) kω)
```

## §7 W1 与 W2 合并: 码的弱化

```agda
record WkLaw : Set where
  field
    wk     : ∀ {a b b′} → b ⊲₀[ a ] b′ → Code a b → Code a b′
    wk-tgt : ∀ {a b b′} (p : b ⊲₀[ a ] b′) k → tgt (wk p k) ≡ tgt k
    wk-inj : ∀ {a b b′} (p : b ⊲₀[ a ] b′) k k′ → wk p k ≡ wk p k′ → k ≡ k′
    wk-≟   : ∀ {a b b′} (p : b ⊲₀[ a ] b′) k k′ → isYes (code-≟ (wk p k) (wk p k′)) ≡ isYes (code-≟ k k′)
    wk-tr  : ∀ {a b b′ b″} (p : b ⊲₀[ a ] b′) (q : b′ ⊲₀[ a ] b″) k → wk q (wk p k) ≡ wk (⊲ᴮ-tr p q) k

record Stages (a : A) : Set where
  field
    B     : ℕ → HB S₀
    σ     : ℕ → HB S₀
    lgσ   : ∀ s → LgB (σ s)
    B-s   : ∀ s → B (suc s) ≡ B s ⊞ σ s
    κ     : ∀ s → Code a (B (suc s))       -- 第 s+1 站回灌所在的码
    κ-tgt : ∀ s → tgt (κ s) ≡ B s           -- 它的目标是旧界
```

## §8 "层号由回灌给出" 的形状

```agda
record LvShape (a : A) : Set where
  field
    St   : Stages a
    out  : ℕ → Ht                -- 第 s 站回灌的输出, 降到 Ht
    σ-of : Ht → HB S₀            -- 输出到外层界增量的读法, 与站号无关
    σ-is : ∀ s → Stages.σ St s ≡ σ-of (out s)
```
