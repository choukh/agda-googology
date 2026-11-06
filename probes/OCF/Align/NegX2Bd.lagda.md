# X₂ 与往 `tw n`, 否定一路 (一): 坐标的合法与公共上界

> 不含记号. 入口 [NegX2](NegX2.lagda.md). 本篇**不依赖**构造一路的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** C 线到 $X_1$ 为止 ([PathOut](PathOut.lagda.md), [X1Up](X1Up.lagda.md)) 的决定都是 "两个下标在同一合法界之下, 用 `cmpB` 比较". `lΩ` 层号的种类 `(inj₂ y , κ)` 带证据 $y+1\lhd B$ ($B$ 合法), 进入分支的坐标先经 `leg` 合法化 (`PathOutX1.shift₁`). 而上层折叠的输出不满足 `LgB` ([NegX1UpInst](NegX1UpInst.lagda.md) `kept-not-LgB-U`; 可数层号上 [NegTySupMono](NegTySupMono.lagda.md) `kept-not-LgB`). 本篇问: 以折叠输出为坐标时, 还有没有合法的公共上界? 这对 $X_2=$ `lΩ lz (λ c → ls (ofU c))` 与更高的 `lΩ k` (坐标层 $k\neq$ `lz`) 各意味着什么?
>
> **结果.**
>
> 1. **`no-bd`, `no-lg-bound`, `ev→lgB` (定理, 对一切种类结构).** 合法世界里, 在界之下的坐标一定合法 (这就是 `KS` 的字段 `lgBd`); 合法界的第一位置一定合法 (`lgB⊲`). 所以**不合法的坐标在任何合法世界里都没有合法的公共上界**, `cmpK`/`cmpB` 用不上; PathOut 式的证据 $y+1\lhd B$ (界 $B$ 合法, 世界合法) 推出 $y$ 合法.
> 2. **`no-bd-o₁`, `no-ev-o₁` (定理).** 坐标层 $k=$ `ls lz` (第 1 层, 含 $\Omega_1$-结点) 的 `lΩ` 层号 `lΩ (ls lz) g` (对一切 $g$): 带类型折叠在第 1 层的输出 $o_1=$ `NegTySupMono.out hz` (留下的 $\Omega_1$-结点) 不合法, 所以它作 $\Omega_2$ 种类的坐标时在任何合法世界里都不在界之下, 作种类下标 `(inj₂ o₁ , κ)` 时没有 PathOut 式的证据.
> 3. **`cnt-ok` (定理).** 坐标层 $k=$ `lz` (就是 $X_1$ 与 $X_2$ 的情形): 第 0 层没有种类, 形状合法 `Sh` 就推出 `LgB` (`PathOut.sh→lgB₁`). 所以 $X_2$ 的 `lΩ` 坐标 (可数) 若来自折叠输出, 是合法的; 1, 2 的障碍**不在 $X_2$ 出现**.
> 4. **`leg₁`, `Lg-leg₁` (构造, 挑战 2 的读法).** 第 1 层的合法化: 对一切第 1 层的值 $x$, `leg₁ x` 合法. $\Omega_1$-结点的分支按坐标做 θ 式累加 ($G\,0=g'0$, $G(c+1)=G\,c\boxplus g'(c+1)$, $G(\lim f)=\lim G\circ f$), ℕ-极限取部分和. 所以 2 不是墙: 坐标层 $k=$ `ls lz` 时, PathOut 的机制要多一个 `leg₁` (与 `PathOutX1.leg` 同一种累加, 多一个 $\Omega$ 子句), `leg₁ o₁` 有证据 (`ev-leg₁`).
>
> **前提实例.** 1: 任一种类结构 (例如 2 的实例). 2: $o_1$ 不合法是 `kept-not-LgB hz` (定理); 合法世界的存在: `lgw₁` ($\Omega_2$ 种类的世界取 $(\mathrm{tt},0)$ 的常值族, 合法). 4: 无前提.
>
> **只否定什么.** 1, 2 只否定: 以**未合法化**的折叠输出为坐标, 在合法世界里用界比较 (`cmpB`, PathOut 的 `Ev`). **不否定**: 先合法化再比较 (4 是构造); 不经界的决定 (X1UpFold 的新种类按叠层层号决定, 可入是 Kripke 式, 不要坐标合法); $X_2$ (3). 本篇没有关闭任何路线.
>
> **对 "推到 `tw n` 是否每站一套机制" (判断, 依据 1-4).** 每升到一个新的坐标层 $k$, 进入 `lΩ k` 分支的坐标要先合法化, 合法化要对坐标层的每种结点写一个子句: 第 0 层 `leg` (ℕ-极限), 第 1 层 `leg₁` (再加 $\Omega_1$-结点的 θ 累加). 坐标层含 $\Omega_{m+1}$-结点 ($m\ge 1$, 坐标本身含 $\Omega$-结点) 时, θ 累加要把坐标的结点映成输出的同种类结点; 塔上有这样的嵌入 (`inj₁`), 所以**判断**能写成对层号递归的一条定义, 不必每站一套; 本篇没有写这条一般定义, 未证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX2Bd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv)
open import OCF.Align.NegTySupMono using (out; kept-not-LgB)
open import OCF.Align.PathOut using (sh→lgB₁)
import OCF.Align.TySupFold as F
open import OCF.Align.TySupSum using (ICdΣ)
open F ICdΣ using (Σ⁺; Sh)
```

## §1 不合法的坐标没有合法的公共上界

```agda
module _ {S : KS} where
  no-bd : ∀ {κ c w} → ¬ LgE S κ c → LgW S w → ¬ Bd S κ c w
  no-bd nl lw b = nl (lgBd S b lw)

  no-lg-bound : ∀ {a L : HB S} {w} → ¬ LgB a → LgW S w → a ⊲[ w ] L → ¬ LgB L
  no-lg-bound na lw p lL = na (lgB⊲ p lw lL)

  ev→lgB : ∀ {y B : HB S} {w} → LgW S w → LgB B → hs y ⊲[ w ] B → LgB y
  ev→lgB lw lB p = lgB⊲ (⊲ᴮ-tr (hsuc hself) p) lw lB
```

## §2 坐标层是第 1 层: 折叠输出没有界

第 1 层的种类结构 `Lv (ls lz)` 字面就是 `step S⊥` (= Fab3Typed 的 `T 1`). $o_1$: 带类型折叠 (塔的实例) 把第 2 层的 $\Omega_1$-结点折到第 1 层, 留下 $\Omega_1$-结点; 不合法 (`NegTySupMono.kept-not-LgB`).

```agda
L₁ : KS
L₁ = Lv (ls lz)

o₁ : HB L₁
o₁ = out hz

o₁-not-lg : ¬ LgB o₁
o₁-not-lg = kept-not-LgB hz
```

对一切 $g$, 层号 `lΩ (ls lz) g` (共尾度 $\Omega_2$) 的 $\Omega_2$ 种类 `κ₂` 的坐标是第 1 层的值. $o_1$ 在任何合法世界里都不在它的界之下; 以 $o_1$ 为下标的种类没有 PathOut 式的证据.

```agda
module Y₂ (g : HB L₁ → LH) where
  YS : KS
  YS = Lv (lΩ (ls lz) g)

  κ₂ : K YS
  κ₂ = inj₁ tt , inj₂ tt

  no-bd-o₁ : ∀ {w} → LgW YS w → ¬ Bd YS κ₂ o₁ w
  no-bd-o₁ lw = no-bd {YS} {κ₂} {o₁} o₁-not-lg lw

  no-ev-o₁ : ∀ {B : HB L₁} {w} → LgW L₁ w → LgB B → ¬ (hs o₁ ⊲[ w ] B)
  no-ev-o₁ lw lB p = o₁-not-lg (ev→lgB lw lB p)

  -- 前提实例: YS 的合法世界存在 (每个分量取最小的合法世界)
  w₀Lv : (k : LH) → Wd (Lv k)
  lw₀Lv : (k : LH) → LgW (Lv k) (w₀Lv k)
  w₀Lv lz = tt
  w₀Lv (ls x) = w₀Lv x , hz
  w₀Lv (ll f) = λ n → w₀Lv (f n)
  w₀Lv (lΩ k h) (inj₁ _) = w₀Lv k , hz
  w₀Lv (lΩ k h) (inj₂ c) = w₀Lv (h c)
  lw₀Lv lz = tt
  lw₀Lv (ls x) = lw₀Lv x , tt
  lw₀Lv (ll f) = λ n → lw₀Lv (f n)
  lw₀Lv (lΩ k h) (inj₁ _) = lw₀Lv k , tt
  lw₀Lv (lΩ k h) (inj₂ c) = lw₀Lv (h c)

  lgw₁ : LgW YS (w₀Lv (lΩ (ls lz) g))
  lgw₁ = lw₀Lv (lΩ (ls lz) g)

  -- 于是在这个合法世界里, o₁ 不在 Ω₂ 种类的界之下
  no-bd-o₁-w₀ : ¬ Bd YS κ₂ o₁ (w₀Lv (lΩ (ls lz) g))
  no-bd-o₁-w₀ = no-bd-o₁ lgw₁
```

## §3 坐标层是第 0 层 ($X_1$, $X_2$): 形状合法就是合法

```agda
cnt-ok : ∀ (h : HB S⊥) → Sh h → LgB h
cnt-ok = sh→lgB₁
```

## §4 第 1 层的合法化 `leg₁` (构造)

`acc h`: 对可数坐标的 θ 式累加, 对一切 `T`. 单调 (`acc-⊲`), 合法 (`Lg-acc`, 对合法坐标).

```agda
acc : ∀ {T : KS} → (HB S⊥ → HB T) → HB S⊥ → HB T
acc h hz = h hz
acc h (hs c) = acc h c ⊞ h (hs c)
acc h (hl f) = hl (λ n → acc h (f n))
acc h (hΩ () _)

acc-⊲ : ∀ {T : KS} (h : HB S⊥ → HB T) {a b : HB S⊥} {w : Wd T} → a ⊲[ tt ] b → acc h a ⊲[ w ] acc h b
acc-⊲ h hself = hself
acc-⊲ h (hsuc {b = b} p) = ⊲ᴮ-tr (acc-⊲ h p) (⊞-fst (acc h b) (h (hs b)))
acc-⊲ h (hlim n p) = hlim n (acc-⊲ h p)
acc-⊲ h (hLim {κ = ()} _ _)

Lg-acc : ∀ {T : KS} (h : HB S⊥ → HB T) → (∀ c → LgB (h c)) → ∀ c → LgB c → LgB (acc h c)
Lg-acc h lh hz l = lh hz
Lg-acc h lh (hs c) l = Lg-⊞ (acc h c) (h (hs c)) (Lg-acc h lh c l) (lh (hs c))
Lg-acc h lh (hl f) (st , l) = (λ {w} n → acc-⊲ h {w = w} (st n)) , (λ n → Lg-acc h lh (f n) (l n))
Lg-acc h lh (hΩ () _) l
```

`leg₁`: ℕ-极限取部分和, $\Omega_1$-结点的分支取累加. 对一切输入合法.

```agda
leg₁ : HB L₁ → HB L₁
leg₁ hz = hz
leg₁ (hs x) = hs (leg₁ x)
leg₁ (hl f) = hl (Σ⁺ (λ n → leg₁ (f n)))
leg₁ (hΩ (inj₁ ()) _)
leg₁ (hΩ (inj₂ _) g) = hΩ (inj₂ tt) (acc (λ c → leg₁ (g c)))

Lg-leg₁ : ∀ x → LgB (leg₁ x)
Lg-Σ₁ : ∀ (f : ℕ → HB L₁) n → LgB (Σ⁺ (λ m → leg₁ (f m)) n)
Lg-leg₁ hz = tt
Lg-leg₁ (hs x) = Lg-leg₁ x
Lg-leg₁ (hl f) = (λ n → ⊞-fst (Σ⁺ (λ m → leg₁ (f m)) n) (leg₁ (f (suc n)))) , Lg-Σ₁ f
Lg-leg₁ (hΩ (inj₁ ()) _)
Lg-leg₁ (hΩ (inj₂ _) g) =
  (λ {w} lw e e′ p → acc-⊲ (λ c → leg₁ (g c)) {w = w} p) ,
  (λ c lc → Lg-acc (λ c → leg₁ (g c)) (λ c → Lg-leg₁ (g c)) c lc)
Lg-Σ₁ f zero = Lg-leg₁ (f 0)
Lg-Σ₁ f (suc n) = Lg-⊞ _ (leg₁ (f (suc n))) (Lg-Σ₁ f n) (Lg-leg₁ (f (suc n)))

-- 合法化之后, o₁ 的像有 PathOut 式的证据 (界取它的后继的后继, 合法)
ev-leg₁ : ∀ {w : Wd L₁} → LgB (hs (hs (leg₁ o₁))) × (hs (leg₁ o₁) ⊲[ w ] hs (hs (leg₁ o₁)))
ev-leg₁ = Lg-leg₁ o₁ , hsuc hself
```

## 结论 (按档)

- **[定理]** `no-bd`, `no-lg-bound`, `ev→lgB` (对一切种类结构); `o₁-not-lg`, `Y₂.no-bd-o₁`, `Y₂.no-ev-o₁`, `Y₂.lgw₁` (前提实例), `Y₂.no-bd-o₁-w₀`; `cnt-ok`; `acc`, `acc-⊲`, `Lg-acc`, `leg₁`, **`Lg-leg₁`**, `ev-leg₁` (构造).
- **[判断]** 文件头 "推到 `tw n`" 一段: 合法化可写成对层号递归的一条定义 (未写, 未证); `leg₁` 改变值 (累加的毛刺, 同 `PathOutX1.leg`), 读法不变与否没有定理.
