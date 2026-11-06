# 带类型折叠到 sup 层, 否定一路 (五): 累加的折叠不单调, 留下的结点不满足 `LgB`

> 不含记号. 入口 [NegTySup](NegTySup.lagda.md). 对着接口 [TySupIf](TySupIf.lagda.md) 与构造一路的折叠 [TySupFold](TySupFold.lagda.md) (只读导入, 不改) 写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** `TySupFold` 把 ℕ-极限改为累加 (`Φ (hl f) = hl (Σ⁺ (Φ ∘ f))`), 合法性改为 `Sh` (ℕ-极限相邻项是第一位置, $\Omega$-结点**只要求分支遗传, 不要求单调**), 证书 `Sh-Φ` 对一切实例、一切输入成立. 它说: 单调 $a\lhd h\Rightarrow\Phi\,a\lhd\Phi\,h$ "未找到证明 (判断)". 本篇检查: 单调是否成立; `Sh` 与 `LgB` 在有种类的层上差多少; 留下的结点是否合法.
>
> **结果.**
>
> 1. **`Φ-not-mono` (定理, 对一切实例 `R`, 一切层号 $X$, 目标 $t$, 界 $b$).** 输入 $h=\lim(0,1,1,1,\dots)$ (合法, `Lg-hI`), $1\lhd h$, 但 $\Phi\,1\not\lhd\Phi\,h$ (任一世界). 原因: $\Phi\,1=\lim_k(k+1)$ (记作 $\hat\omega$), $\Phi\,h=\lim(1,\ 1\boxplus\hat\omega,\ 1\boxplus\hat\omega\boxplus\hat\omega,\dots)$; $\hat\omega$ 不是任何部分和的字面第一位置 (部分和的第 $k$ 项是 $\hat\omega$ 的第 $k$ 项接在非零的前缀后面). 输入不带结点, 所以不经 `dec`, 对一切实例成立. 对照: Fab3Typed 的 `Ψ (hl f) = hl (Ψ ∘ f)` 单调 (`Ψ-mono`). 所以 "未找到证明" 在字面第一位置的意义下是**否定**: 累加的 `Φ` 不单调.
> 2. **`kept-not-LgB` (定理, 塔的实例 `towerIf`).** 把 $\Omega_1$ 嵌在第 2 层 (`up (Ω 1)`, 合法) 折到目标层 1: `dec` 留下它 (种类 $\Omega_1$, 层号 0), 输出是一个 $\Omega_1$-结点, 分支是 $c\mapsto\Phi(c)$. 由 1, 分支在坐标 $1\lhd h$ 处不单调, 所以**输出不满足 `LgB`**; 它满足构造一路的 `Sh` (`kept-Sh`). 这就是 `sh⇏lgB`: 在有种类的层上 `Sh` 严格弱于 `LgB` (同一棵树).
>
> **前提实例.** 1 对一切 `R` 无前提 (只要有一个层号; `towerIf`, 构造一路的实例都有). 2 的输入合法 (`Lg-in`, 由 Fab3Typed 的 `LgB-Ω` 与 `Lg-up`), 世界 $(\mathrm{tt}, h)$ 合法 (`Lg-hI`).
>
> **只否定什么.** 只否定: (a) 累加的 `Φ` 保字面第一位置; (b) `Φ` 在留下结点的层上保 `LgB` (在 `towerIf` 上给出反例; 构造一路的 `HB S⊥` 层号实例未写出时, 本条对它是预测, 判断). **不否定**: `Sh-Φ` (对); 折到没有种类的层 `z` 时证书就是 `LgB` (构造一路的 `sh→lgB`, 那里 `Sh` 的结点条款是空的); 闭项的合法 (终点在 `z`). 也不否定 "不累加的写法有单调" (那是构造一路说的开放点, 本篇没有碰).
>
> **对纲领与目标.** 合法性的量词被替换了: 中间层的输出只满足 `Sh` (去掉 $\Omega$-单调), 不满足树自己的 `LgB`. 终点的证书不受影响 (没有种类的层上两者相同), 但 "中间层的值是合法的布劳威尔树" 不再由证书给出. 对 "让树自足" 而言, 这是一处要记账的地方: 合法性判据只在终点用到.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTySupMono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.Fab3Typed using (T; Ω; LgB-Ω)
open import OCF.Align.TySupIf
import OCF.Align.TySupFold as TF
open import OCF.Align.NegTySupIf using (towerIf; Below; here; LeB)
```

## §1 $\hat\omega$ 不在累加的部分和下面

对任一实例 `R` 与任一种类结构 `S`, 用折叠自己的 `mul` 与 `Σ⁺` (它们不读实例, 但名义上带着实例参数, 所以本模块也带).

```agda
module MS (R : TySupIf) {S : KS} where
  open TF R using (mul; Σ⁺)

  one : HB S
  one = hs hz

  ω̂ : HB S
  ω̂ = hl (mul one)

  at : HB S → ℕ → HB S
  at (hl f) n = f n
  at x n = x

  hs-inj : ∀ {x y : HB S} → hs x ≡ hs y → x ≡ y
  hs-inj refl = refl

  -- y ⊞ mul one k = hs^(k+1) y
  strip : ∀ {w} k {Y : HB S} → ω̂ ⊲[ w ] Y ⊞ mul one k → ω̂ ⊲[ w ] Y
  strip zero (hsuc p) = p
  strip (suc k) (hsuc p) = strip k p

  no-hz : ∀ {w} → ¬ (ω̂ ⊲[ w ] hz)
  no-hz ()

  key : ∀ {w a b} (Y : HB S) → a ⊲[ w ] b → a ≡ ω̂ → b ≡ Y ⊞ ω̂ → ¬ (Y ≡ hz) → ¬ (ω̂ ⊲[ w ] Y) → ⊥
  key Y hself ea eb nz nY = nz (sym (hs-inj (cong (λ h → at h 0) (trans (sym ea) eb))))
  key Y (hsuc p) ea ()
  key {w} {a} Y (hlim {f = F} n p) ea eb nz nY =
    nY (strip n (subst (λ z → z ⊲[ w ] Y ⊞ mul one n) ea (subst (λ z → a ⊲[ w ] z) (cong (λ h → at h n) eb) p)))
  key Y (hLim e p) ea ()

  module _ (g : ℕ → HB S) (g0 : g 0 ≡ one) (gs : ∀ m → g (suc m) ≡ ω̂) where
    s≢z : ∀ {x : HB S} → ¬ (hs x ≡ hz)
    s≢z ()

    l≢z : ∀ {f : ℕ → HB S} → ¬ (hl f ≡ hz)
    l≢z ()

    nzΣ : ∀ m → ¬ (Σ⁺ g m ≡ hz)
    nzΣ zero e = s≢z (trans (sym g0) e)
    nzΣ (suc m) e = l≢z (subst (λ z → Σ⁺ g m ⊞ z ≡ hz) (gs m) e)

    notΣ : ∀ {w} m → ¬ (ω̂ ⊲[ w ] Σ⁺ g m)
    notΣ {w} zero p = no-hz (strip 0 {hz} (subst (λ z → ω̂ ⊲[ w ] z) g0 p))
    notΣ {w} (suc m) p =
      key (Σ⁺ g m) (subst (λ z → ω̂ ⊲[ w ] Σ⁺ g m ⊞ z) (gs m) p) refl refl (nzΣ m) (notΣ m)

    notLim : ∀ {w} → ¬ (ω̂ ⊲[ w ] hl (Σ⁺ g))
    notLim {w} p = go p refl refl
      where
      go : ∀ {a b} → a ⊲[ w ] b → a ≡ ω̂ → b ≡ hl (Σ⁺ g) → ⊥
      go hself ea eb = s≢l (trans (trans (cong (λ h → at h 1) (trans (sym ea) eb))
                                         (cong (λ z → z ⊞ g 1) g0))
                                  (cong (λ z → one ⊞ z) (gs 0)))
        where
        s≢l : ∀ {x : HB S} {f : ℕ → HB S} → ¬ (hs x ≡ hl f)
        s≢l ()
      go (hsuc p) ea ()
      go {a} (hlim n p) ea eb = notΣ n (subst (λ z → z ⊲[ w ] Σ⁺ g n) ea (subst (λ z → a ⊲[ w ] z) (cong (λ h → at h n) eb) p))
      go (hLim e p) ea ()
```

## §2 对一切实例: `Φ` 不单调

```agda
module NotMono (R : TySupIf) where
  open TySupIf R
  open TF R using (Φ)

  fI : ∀ {S : KS} → ℕ → HB S
  fI zero = hz
  fI (suc n) = hs hz

  hI : ∀ {S : KS} → HB S
  hI = hl fI

  Lg-hI : ∀ {S : KS} → LgB {S} hI
  Lg-hI = st , lg
    where
    st : ∀ {w} n → fI n ⊲[ w ] fI (suc n)
    st zero = hsuc hself
    st (suc n) = hself
    lg : ∀ n → LgB (fI n)
    lg zero = tt
    lg (suc n) = tt

  one⊲hI : ∀ {S : KS} {w} → hs hz ⊲[ w ] hI {S}
  one⊲hI = hlim 1 hself

  -- 一般形: 输入是任一 ℕ-极限 lim (0, 1, 1, ...) (逐项命题相等即可)
  Φ-not-mono′ : ∀ X (a : AccR _⊏_ X) lX t pt b (F : ℕ → HB (L X)) → F 0 ≡ hz → (∀ m → F (suc m) ≡ hs hz) →
                {w : Wd (L t)} → ¬ (Φ X a lX t pt b (hs hz) ⊲[ w ] Φ X a lX t pt b (hl F))
  Φ-not-mono′ X (acc rs) lX t pt b F F0 Fs p =
    MS.notLim R {L t} (λ n → Φ X (acc rs) lX t pt b (F n))
      (cong (Φ X (acc rs) lX t pt b) F0) (λ m → cong (Φ X (acc rs) lX t pt b) (Fs m)) p

  Φ-not-mono : ∀ X (a : AccR _⊏_ X) lX t pt b {w : Wd (L t)} →
               ¬ (Φ X a lX t pt b (hs hz) ⊲[ w ] Φ X a lX t pt b hI)
  Φ-not-mono X a lX t pt b = Φ-not-mono′ X a lX t pt b fI refl (λ m → refl)
```

## §3 塔的实例: 留下的结点不满足 `LgB`

`up (Ω 1)`: 第 2 层里的 $\Omega_1$-结点 (种类 `inj₁ (inj₂ tt)`, 层号 0), 分支 $c\mapsto c$ (嵌入). 折到目标层 1: `dec` 留下它, 种类 `inj₂ tt` (`T 1` 的 $\Omega_1$), 读回恒等.

```agda
open TF towerIf using (Φ; Sh; Sh-Φ)

in₂ : HB (T 2)
in₂ = up (Ω 1)

Lg-in : LgB in₂
Lg-in = Lg-up (Ω 1) (LgB-Ω 1)

out : HB S⊥ → HB (T 1)
out b = Φ 2 (TySupIf.wf towerIf 2) tt 1 (inj₂ here) (up b) in₂

-- 输出是一个 Ω₁-结点, 分支是 c ↦ Φ (up (up c)) (定理, refl)
out-kept : ∀ b → out b ≡ hΩ (inj₂ tt) (λ c → Φ 2 (TySupIf.wf towerIf 2) tt 1 (inj₂ here) (up b) (up (up c)))
out-kept b = refl

kept-not-LgB : ∀ b → ¬ LgB (out b)
kept-not-LgB b (mo , _) =
  NotMono.Φ-not-mono′ towerIf 2 (TySupIf.wf towerIf 2) tt 1 (inj₂ here) (up b)
    (λ n → up (up (NotMono.fI towerIf n))) refl (λ m → refl)
    (mo {w = tt , NotMono.hI towerIf} (tt , NotMono.Lg-hI towerIf)
        (NotMono.one⊲hI towerIf) hself (NotMono.one⊲hI towerIf))

kept-Sh : ∀ b → Sh (out b)
kept-Sh b = Sh-Φ 2 (TySupIf.wf towerIf 2) tt 1 (inj₂ here) (up b) in₂

sh⇏lgB : Σ (HB (T 1)) (λ h → Sh h × ¬ LgB h)
sh⇏lgB = out hz , kept-Sh hz , kept-not-LgB hz
```

## 结论 (按档)

- **[定理]** `MS.strip`, `MS.key`, `MS.notΣ`, `MS.notLim`; `NotMono.Lg-hI`, `NotMono.one⊲hI`, **`NotMono.Φ-not-mono`**, `NotMono.Φ-not-mono′` (对一切实例); `Lg-in`, `out-kept`, **`kept-not-LgB`**, `kept-Sh`, **`sh⇏lgB`** (塔的实例).
- **[判断]** 构造一路的 `HB S⊥` 层号实例上 2 同样成立 (那里第 2 层也是 `step (step S⊥)`, 留下 $\Omega_1$ 的读回若是恒等, 证明逐字相同); 等实例写出后核对.
