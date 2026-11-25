# K3 封顶 (四): `RecB.Tω` 的层号是一对 (ℕ, 可数树)

> **第 4 层 (验收侧) 的判定文件.** 不改任何候选的定义, 不进成品与证书. 本篇不导入记号模块 (用不到).
>
> **判决: (乙) 封顶的编译事实, 签名一级** (定理是关于 `ℕ` 与 `Cd` 的, 它们与候选的联系靠读签名, 见下面 "它说了什么")**.** 候选的层号是一对 (底的下标 `n : ℕ`, 底内的层 `m : Cd`): `TN : ℕ → (m : Cd) → LgB m → Cd`, `inp n m : HB (Sb (suc n))`, 底 `Sb : ℕ → KS`. 入口自己已经写明 "底的下标是 ℕ, 一切层号在 Ω·ω 之下". 本篇把能写成定理的部分写出来:
>
> 1. `cd-Ωfree`: 底内的层号与回灌的下标都是可数树 `Cd`, 没有 Ω-结点. 所以这个候选里没有 "塔高度或回灌下标是 Ω-结点" 的情形 ([K3CapSan](K3CapSan.lagda.md) 里 Third 一族的那三处在这里不出现).
> 2. `dcI-suc` (`refl`): 跨底折叠里指标种类的决定对 `n` 结构递归: 更高的底上一律留. Ω-共尾的层号 (底的边界) 上的派发是 ℕ 上的分情况, 不是树上的比较.
> 3. `no-ω-bottom`: 底的下标里没有极限: `ℕ` 的一份严格保序拷贝在 `ℕ` 里没有上界. 同一形状换一个目标类型就可满足 (`K3CapRadical.nat-copy`: `ℕ` 的拷贝在可数树里有上界 ω), 所以否定针对的是下标类型取 `ℕ` 这件事.
> 4. `Tω-shape`, `zω-step`, `TD-shape`, `TN-shape` (`refl`): 闭项逐层分解到 `desc n (inp n m …)`, 每一项只用到一个有限的 `n`.
>
> **它说了什么, 没说什么.**
>
> - 编译事实: 上面各条. 第 3 条是关于 `ℕ` 的陈述; "候选的底只按 `ℕ` 编号" 是读签名 (`Sb`, `ΦX`, `desc` 都对 `n : ℕ` 递归), 不是一条关于 "不存在别的折叠" 的定理.
> - 读法 (判断): 层号 (n, m) 读 Ω·n+m; 装不下的第一站是需要第 ω 个底的站, 即层号 Ω·ω 本身作层号的站 (读法 ψ₀(Ω_{Ω·ω+1}) 一带). `Tω` 是对 `n` 的外部对角.
> - **不是值上界.** 没有证明 `Tω` 的序数值不超过任何具名序数; 入口的读法 ψ₀(Ω_{Ω·ω}) 没有定理, 上下界都没有.
>
> **第一个 Ω-共尾派发的站在哪 (读代码, 判断).** 层号 Ω 是第 1 个底的边界 (`fl 1`, 指标种类的结点). 目标层与结点层的比较在这里拆成两步: 底的下标按 `n` 的构造子分情况 (`dcI zero` 比较, `dcI (suc n)` 留), 底内的层用 `cmpB` 在可数的公共上界 `B` 之下比较. 这一站在候选的类型之内. 条件覆盖定理 (甲) 没有实填.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K3CapRecB where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; n<1+n; <-irrefl; ≤-<-trans)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.RecB using (J₁; Tω; zω; TD; yN; TN; desc; inp; gd-inp)
import OCF.Lean.CRwFold as CF₀
import OCF.Lean.RecBFold as RF₀
open import OCF.Align.K3CapSan using (ΩFree)

module CF = CF₀ I₁
module RF = RF₀ J₁
```

## §1 底内的层与回灌的下标没有 Ω-结点

```agda
cd-Ωfree : ∀ (c : Cd) → ΩFree c
cd-Ωfree hz = tt
cd-Ωfree (hs c) = cd-Ωfree c
cd-Ωfree (hl f) = λ n → cd-Ωfree (f n)
cd-Ωfree (hΩ () _)

-- 候选自己的签名: 回灌下标与底内的层都取 Cd
feed-index : ∀ n → Cd → HB (RF.Sb (suc n))
feed-index = RF.gtX

level-in-bottom : ℕ → (m : Cd) → LgB m → Cd
level-in-bottom = TN
```

## §2 Ω-共尾层号上的派发对 `n` 结构递归

```agda
dcI-suc : ∀ n {B t : Cd} (lB : LgB B) (pt : t ⊲ B) (o : hs hz ⊲ B) →
  RF.dcI (suc n) {B} {t} lB pt o ≡ CF.keep (CF.emb t RF.ιK) (CF.frE t RF.ιK)
dcI-suc n lB pt o = refl
```

## §3 底的下标里没有极限

```agda
infl : (F : ℕ → ℕ) → (∀ {a b} → a < b → F a < F b) → ∀ n → n ≤ F n
infl F mono zero = z≤n
infl F mono (suc n) = ≤-trans (s≤s (infl F mono n)) (mono (n<1+n n))

no-ω-bottom : (F : ℕ → ℕ) (top : ℕ) → (∀ {a b} → a < b → F a < F b) → (∀ n → F n < top) → ⊥
no-ω-bottom F top mono bd = <-irrefl refl (≤-<-trans (infl F mono top) (bd top))
```

## §4 闭项逐层分解 (只展开一步, 不计值)

```agda
Tω-shape : Tω ≡ hl zω
Tω-shape = refl

zω-step : ∀ k → zω (suc k) ≡ zω k ⊞ TD (suc k)
zω-step k = refl

TD-shape : ∀ n → TD n ≡ hl (yN n)
TD-shape n = refl

TN-shape : ∀ n m lm → TN n m lm ≡ desc n (inp n m lm) (gd-inp n m lm)
TN-shape n m lm = refl
```

## §5 结论 (按档)

- **[定理]** `cd-Ωfree`; `dcI-suc` (`refl`); `no-ω-bottom`; `Tω-shape`, `zω-step`, `TD-shape`, `TN-shape` (`refl`).
- **[判断]** 层号 (n, m) 读 Ω·n+m; 装不下的是需要第 ω 个底的站; 第一个 Ω-共尾派发的站 (第 1 个底的边界) 在类型之内, 派发是 ℕ 上的分情况加可数界下的 `cmpB`.
- **没有的.** 值上界与值下界; "不存在别的折叠" 一类的定理; 条件覆盖定理的实填.
