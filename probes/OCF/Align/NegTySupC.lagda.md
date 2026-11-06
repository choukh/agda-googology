# 带类型折叠到 sup 层, 否定一路 (六): 对构造一路实例 `ICd` 的检查

> 不含记号. 入口 [NegTySup](NegTySup.lagda.md). 只读导入构造一路的 [TySupC](TySupC.lagda.md) (实例 `ICd`), [TySupFold](TySupFold.lagda.md), [TySup](TySup.lagda.md) (21:44 版), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **检查三件事: sup 层是否真的按层号留/坍缩, 回灌是否仍是恒等, 合法性量词是否被偷换.**
>
> 1. **`ok-ICd` (定理, 正面).** 实例的 `dec` 正确 (`NegTySupIf.Ok`): 留 ⇒ 种类的位置 `hs i` 是目标的第一位置; 同层 ⇒ 层号就是目标 (字面 `refl`); 在上 ⇒ $i$ 就是层号. 接口不保证这一点 (`NegTySupIf.¬ok-const`), 实例做到了. 回灌是恒等: 构造一路的 `feed-id` (refl), 读回 `toC` 逐种类是恒等.
> 2. **`kept-not-LgB-ICd`, `sh⇏lgB-ICd` (定理).** 实例里, $\Omega_1$ 嵌在第 2 层折到目标层 1 时被留下 (`out-kept-ICd`, refl), 输出的 $\Omega_1$-结点**不满足 `LgB`** (分支不单调, 由 `NegTySupMono.Φ-not-mono′`), 但满足构造一路的 `Sh`. 这一步就发生在闭项 `TC` 的计算里: "在上" 情形先折到种类自己的层 $i$ (目标 $i>0$), 那里留下低层种类. **合法性量词被换了**: 中间层的输出只有 `Sh` (去掉 $\Omega$-单调), 终点 (第 0 层, 没有种类) 上 `Sh` 就是 `LgB`, 闭项的证书不受影响.
> 3. **`¬LgB-topω` (定理).** 实例在 ℕ-极限层号上的地板 `topC (hl f) = hl (λ n → ι n (topC (f n)))` 正是 `HtTowerNeg.no-naive-diag` 的形状: 各分量各自的 $\Omega$, 互相不是字面第一位置. 在 $\omega$ 层 (`ωc`) 它不满足 `LgB` (由 `NegTySupDiag.indep-illegal`). 所以 `Tω = TC ωc` 是把折叠用在一个**不合法的输入**上; 证书 `Sh-Φ` 对一切输入成立, 不看输入是否合法, 所以 `Tω` 仍有 `LgB` 证书.
> 4. **`blind-TC` (定理, 盲).** 把实例的 `dec` 换成 "一律同层, 常值回灌" (`NegTySupIf.constOf ICd`), 同样的闭项公式 `TC′` 也有 `LgB` 证书 (`LgB-TC′`), 而 `TC′ 1 ≠ TC 1` (`TC-differ`, 第 1 个链点一个是极限一个是后继). 证书不区分正确与错误的决定.
>
> **前提实例.** 2 的输入 `up (topC 1)` 合法 (`Lg-in-ICd`); 世界 $(\mathrm{tt}, h)$ 合法. 3 的世界取 `NegTySupLg.coinLv` 的最小世界. 4 无前提.
>
> **只否定什么.** 只否定: (a) "实例的折叠在中间层保 `LgB`" (2); (b) "实例在极限层号上的地板合法" (3); (c) "`Sh-Φ` 证书反映 `dec` 或输入的正确" (4). **不否定**: 闭项 `Tn n`, `Tω`, `TΩΩ` 的 `LgB` 证书 (都对); `dec` 的正确 (1 是正面定理); 回灌恒等; 把极限层的地板改成接起来的 (`HtTowerU.θ` 的 `⊞` 形状) 之后的合法 (未写, 未否定); 不累加的折叠 (未写). 本篇没有关闭任何路线. 读法 (ψ₀(Ω_X)) 不受本篇影响也没被本篇支持: 值的定理两边都没有.
>
> **对纲领与目标.** 纲领 1 要求最终定义是布劳威尔树上的合法项: 闭项满足. "让树自足" 的进展判据之一是 "有树侧的合法性标准": 本路的中间层不满足树自己的 `LgB`, 极限层的地板也不满足; 合法性只在终点由形状给出. 这是翻译账里要记的一条 (由累加与 `Sh` 引入, 不来自记号).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTySupC where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupIf
open import OCF.Align.TySupC
import OCF.Align.TySupFold as TF
open import OCF.Align.TySup using (nat; ωc; lg-nat; lg-ω; TC; LgB-TC)
open import OCF.Align.NegTySupIf using (OkAt; Ok; Correct; constOf)
open import OCF.Align.NegTySupMono using (module NotMono)
open import OCF.Align.NegTySupDiag using (HasΩ; indep-illegal)
open import OCF.Align.NegTySupLg using (Coin; coinLv)
```

## §1 实例的决定正确

```agda
ok-pick : ∀ {X t i} {κ : K (LC X)} (to : HB (LC i) → E (LC X) κ) (pi : i ⊏ᶜ X)
          (r : (t ⊲[ tt ] hs i) ⊎ (hs i ⊲[ tt ] t)) → OkAt ICd i (pick {X} {t} {i} {κ} to pi r)
ok-pick to pi (inj₂ q) = q
ok-pick to pi (inj₁ hself) = hself
ok-pick to pi (inj₁ (hsuc hself)) = refl
ok-pick to pi (inj₁ (hsuc (hsuc q))) = refl
ok-pick to pi (inj₁ (hsuc (hlim n q))) = refl
ok-pick to pi (inj₁ (hsuc (hLim {κ = ()} _ _)))

ok-ICd : Correct ICd
ok-ICd X t pt lX κ = ok-pick (toC X κ) (posC X κ) (cmpB (posC X κ) pt tt lX)
```

## §2 留下的结点不满足 `LgB`

第 2 层 (`nat 2`, 种类结构字面是 `step (step S⊥)`) 里的 $\Omega_1$-结点 `up (topC 1)` 折到目标层 1.

```agda
open TF ICd using (Φ; Sh; Sh-Φ)

in₂ : HB (LC (nat 2))
in₂ = up (topC (nat 1))

Lg-in-ICd : LgB in₂
Lg-in-ICd = Lg-up (topC (nat 1)) ((λ lw e e′ p → up-⊲ p) , (λ c lc → Lg-up c lc))

outC : HB S⊥ → HB (LC (nat 1))
outC b = Φ (nat 2) (wfC (nat 2)) tt (nat 1) (hsuc hself) (up b) in₂

out-kept-ICd : ∀ b → outC b ≡ hΩ (inj₂ tt) (λ c → Φ (nat 2) (wfC (nat 2)) tt (nat 1) (hsuc hself) (up b) (up (up c)))
out-kept-ICd b = refl

kept-not-LgB-ICd : ∀ b → ¬ LgB (outC b)
kept-not-LgB-ICd b (mo , _) =
  NotMono.Φ-not-mono′ ICd (nat 2) (wfC (nat 2)) tt (nat 1) (hsuc hself) (up b)
    (λ n → up (up (NotMono.fI ICd n))) refl (λ m → refl)
    (mo {w = tt , NotMono.hI ICd} (tt , NotMono.Lg-hI ICd)
        (NotMono.one⊲hI ICd) hself (NotMono.one⊲hI ICd))

kept-Sh-ICd : ∀ b → Sh (outC b)
kept-Sh-ICd b = Sh-Φ (nat 2) (wfC (nat 2)) tt (nat 1) (hsuc hself) (up b) in₂

sh⇏lgB-ICd : Σ (HB (LC (nat 1))) (λ h → Sh h × ¬ LgB h)
sh⇏lgB-ICd = outC hz , kept-Sh-ICd hz , kept-not-LgB-ICd hz
```

## §3 $\omega$ 层的地板不合法

`LC ωc` 字面是 `sup ℕ (λ n → Lv (ofC (nat n)))`, 地板的第 $n$ 项是 `ι n (topC (nat n))`. 第 1 项带结点, 第 1, 2 项在不同分量.

```agda
wω : Wd (LC ωc)
wω = Coin.w₀ (coinLv (ofC ωc))

suc≢ : ∀ k → ¬ (k ≡ suc k)
suc≢ zero ()
suc≢ (suc k) e = suc≢ k (cong pr e)
  where
  pr : ℕ → ℕ
  pr zero = zero
  pr (suc n) = n

¬LgB-topω : ¬ LgB (topC ωc)
¬LgB-topω = indep-illegal {ℕ} {λ n → LC (nat n)} wω (λ n → n) (λ n → topC (nat n)) 1 (suc≢ 1) tt
```

## §4 盲: 常值决定的同一公式也有证书

`TC′`: 同一个闭项公式, 实例换成 `constOf ICd` (只换 `dec`). 第 0 层的 `Sh` 推出 `LgB` (与构造一路的 `sh→lgB` 同, 这里对 `constOf ICd` 的 `Sh` 重写一遍, 因为 `Sh` 名义上带实例参数).

```agda
R′ : TySupIf
R′ = constOf ICd

TC′ : (X : Cd) → LgB X → HB S⊥
TC′ X lX = TF.Φ R′ X (wfC X) lX hz (z⊲ᴮ X) hz (topC X)

sh→lgB′ : ∀ h → TF.Sh R′ {S⊥} h → LgB h
sh→lgB′ hz s = tt
sh→lgB′ (hs h) s = sh→lgB′ h s
sh→lgB′ (hl f) (st , s) = (λ {w} n → st {w} n) , (λ n → sh→lgB′ (f n) (s n))
sh→lgB′ (hΩ () _) s

LgB-TC′ : ∀ X lX → LgB (TC′ X lX)
LgB-TC′ X lX = sh→lgB′ (TC′ X lX) (TF.Sh-Φ R′ X (wfC X) lX hz (z⊲ᴮ X) hz (topC X))

at : HB S⊥ → ℕ → HB S⊥
at (hl f) n = f n
at x n = x

l≢s : ∀ {f : ℕ → HB S⊥} {x : HB S⊥} → ¬ (hl f ≡ hs x)
l≢s ()

-- 第 1 个链点: TC 的是 1 ⊞ ω̂ (极限), TC′ 的是 1 ⊞ 1 (后继)
TC-differ : ¬ (TC (nat 1) tt ≡ TC′ (nat 1) tt)
TC-differ e = l≢s (cong (λ h → at h 1) e)

blind-TC : LgB (TC (nat 1) tt) × LgB (TC′ (nat 1) tt) × ¬ (TC (nat 1) tt ≡ TC′ (nat 1) tt)
blind-TC = LgB-TC (nat 1) tt , LgB-TC′ (nat 1) tt , TC-differ
```

## 结论 (按档)

- **[定理]** `ok-pick`, **`ok-ICd`** (正面: 实例的决定正确); `Lg-in-ICd`, `out-kept-ICd`, **`kept-not-LgB-ICd`**, `kept-Sh-ICd`, **`sh⇏lgB-ICd`**; `wω`, **`¬LgB-topω`**; `R′`, `TC′`, `LgB-TC′`, `TC-differ`, **`blind-TC`**.
- **[判断]** 极限层的地板改成 `⊞` 接起来的形状 (如 `HtTowerU.θ`) 可以合法, 读法是否不变未查. 中间层不满足 `LgB` 对值的读法有无影响, 没有值的定理, 不下结论.
