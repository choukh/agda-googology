# NegFab6: Fab6 的外部结点是原子 (否定与复核一路, 入口)

> 不含记号. 2026-11-06. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延. 不改任何已有文件. 对象: [Fab6](Fab6.lagda.md), [Fab6Lay](Fab6Lay.lagda.md).
>
> | 文件 | 内容 |
> |---|---|
> | [NegFab6Sim](NegFab6Sim.lagda.md) | `Cd` 上的序 `≼`, 度量 `er`, 对齐关系 `Sim`, **模拟定理 `sim`**, `sound`, 严格树 `St`, `St-Φ` |
> | 本篇 | **`inU≼`**, 反单调 `anti-in`, `anti-out`, `atoms-f₂`, `atoms-f₁`, $\theta$ 一步 `J-hE`, **条件定理 `TU≼`**, 前提实例 `maj₁`, `ex₁` |
> | [NegFab6Lay](NegFab6Lay.lagda.md) | 好的层 `Gd`, **`ext-mul`**, `Gd-ext`, `Gd-diag`, `Gd-sup`, `Gd-pow`, `Gd-Pc`, `TΩΩ₂-mul`, `TΩ^Ω-bd` |
> | [NegFab6Cmp](NegFab6Cmp.lagda.md) | 与 CRw 的差: **`TX≢`, `TU1≢`, `TU2≢`**, **`crw-many`**, `fab-atom`, `crw-br`, `crw-br₂` (验收文件, 导入 CRw) |
> | [NegFab6Idx](NegFab6Idx.lagda.md) | 玩具: 按世界编索引时前缀能进分支 (`branch`) |

## §0 判决

**疑点成立的部分 (定理).** 同底折叠对外部结点只折前缀. 所以 `inU m` 里沿前缀数到的外部结点与后继的长度 `er (inU m lm)` 不超过一棵**不含外部结点**的普通塔上同样的折叠 `PU m lm` (`inU≼`, 对一切合法层号 $m$). 塔的高层新种类的 keep 分支、回灌链都在这条定理的覆盖之内 (`sim` 对一切 `m`, `t`, 种子与输入), 它们没有把外部结点变成别的东西. 跨底折叠对每个外部结点恰好调用一次 $\theta$ (`J-hE`), 所以 `TU m` 是一个长度不超过 `PU m lm` 的、由 $\theta$ 与 $\cdot\omega$ 组成的字作用在 $1$ 上.

**与 CRw 不同 (定理).** Fab6 与 CRw 的 `TX`, `TU1`, `TU2` 是不同的闭树 (`TX≢`, `TU1≢`, `TU2≢`), `Fab6Cmp` 的相同只是深度 4 的结点数. 同一个输入 $f+f$: Fab6 折出 `hE tt (φ f) g₀` (`fab-atom`), 分支原样, `er` 值 $3$ (`atoms-f₂`); CRw 折出的 $\Omega_1$-结点的分支是 $\varphi(f+g_c)$ (`crw-br`), 分支 $(1,d)$ 里 $\Omega_1$-种类结点不少于 $d$, 对一切可数树 $d$ (`crw-many`).

**读法 (判断).** Fab6 §5 的读法要下调, 见 §5. 没有与 ψ₀(Ω_x) 参照树的 `≼`, 没有值的定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFab6 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.Fab6Base
open import OCF.Lean.Fab6Fold
open import OCF.Lean.Fab6
open import OCF.Lean.NegFab6Sim
```

## §1 外部结点的个数

`Mk g₀`: 只允许分支是 `g₀` 的外部结点. `PU m lm`: 普通塔 (`X⊥`, 空底) 上, 种子 $1$, 第 $m$ 层地板折到第 $0$ 层. 外部结点的种子 `topL` 对着 $1$ (`es`).

**定理 (`inU≼`).** `er (inU m lm) ≼ PU m lm`. 这里 `inU~` 比它更强: `inU m lm` 与 `PU m lm` 逐构造子对齐, 所有外部结点的分支都是 `g₀`.

```agda
Mk : ((y : Cd) → HB X⊥ (Tw X⊥ S⊥ y)) → (x : ⊤) → ((y : Cd) → HB X⊥ (Tw X⊥ S⊥ y)) → Set
Mk g₀ _ g = g ≡ g₀

g₀ : (y : Cd) → HB X⊥ (Tw X⊥ S⊥ y)
g₀ = topT X⊥ S⊥ hz

module M₀ = Thm {X₁} (Mk g₀)
open Ali₂ {X₁} (Mk g₀) using (Sim; zz; ss; ll; oo; es; el; rT; Sim-top)

topL~ : Sim (rT {S⊥} hz) topL (hs hz)
topL~ = es refl zz

PU : (m : Cd) → LgB m → Cd
PU m lm = Φ {X⊥} {S⊥} m (wf m) lm hz (z⊲ᴮ m) (hs hz) (topT X⊥ S⊥ (hs hz) m)

inU~ : ∀ m lm → Sim (rT {S⊥} hz) (inU m lm) (PU m lm)
inU~ m lm = M₀.sim m (wf m) lm hz (z⊲ᴮ m) topL~ (Sim-top topL~ m)

inU≼ : ∀ m lm → er (inU m lm) ≼ PU m lm
inU≼ m lm = M₀.sound (inU~ m lm)
```

## §2 反单调

`φ`: 第 1 层到第 0 层的同底折叠作用在 `up h` 上. `f₁` 是 $f+1$, `f₂` 是 $f+f$, $f$ 是 `topL`. `μ`: 外部结点计 $\omega$ 的度量. 输入 $\mu(f+1)<\mu(f+f)$ (`anti-in`), 输出反过来 $\mu(\varphi(f+f))<\mu(\varphi(f+1))$ (`anti-out`). 外部结点个数: $\varphi(f+f)$ 的 `er` 恰好是 $3$ (`atoms-f₂`), $\varphi(f+1)$ 的不小于 $\omega$ (`atoms-f₁`). 后继子句取 $\cdot\omega$ 会复制前缀里的原子, 第二个原子却只加一次.

```agda
φ : HB X₁ S⊥ → HB X₁ S⊥
φ h = Φ (hs hz) (wf (hs hz)) tt hz (hsuc hself) topL (up h)

nat : ℕ → Cd
nat zero = hz
nat (suc n) = hs (nat n)

ω : Cd
ω = hl nat

μ : HB X₁ S⊥ → Cd
μ hz = hz
μ (hs h) = hs (μ h)
μ (hl f) = hl (λ n → μ (f n))
μ (hΩ () _)
μ (hE _ p _) = μ p ⊞ ω

f₁ : HB X₁ S⊥
f₁ = topL ⊞ hs hz

f₂ : HB X₁ S⊥
f₂ = topL ⊞ topL

atoms-f₂ : er (φ f₂) ≡ hs (hs (hs hz))
atoms-f₂ = refl

atoms-f₁ : ω ≼ er (φ f₁)
atoms-f₁ = l≼ (λ n → ≼l n (go n))
  where
  go : ∀ n → nat n ≼ er (mul (φ topL) n)
  go zero = z≼
  go (suc n) = s≼s (≼s (go n))

anti-in : hs (μ f₁) ≼ μ f₂
anti-in = ≼l 2 (s≼s (s≼s (≼-refl _)))

anti-out : hs (μ (φ f₂)) ≼ μ (φ f₁)
anti-out = ≼l 2 (≼l 1 (s≼s (≼s (⊞-mono (≼s (≼-refl _)) (≼-refl ω)))))
```

## §3 跨底折叠只调一次 $\theta$

`J`: 闭项用的跨底折叠 ($B=1$, 目标 $0$). `θ g x`: 种子 $x$ 上的回灌链. `J-hE` 是 `refl`: 外部结点的值是 $\theta$ 作用在折好的前缀上, 不看别的. `J` 的输出都是严格树 (`St-J`).

**条件定理 (`TU≼`).** 设 `Maj g`: `D` 在严格树上单调, 保持严格树, 盖住 $\cdot\omega$ 与 `θ g`. 则 `J` 被沿普通树迭代 `D` 的 `Itr` 控制 (`J≼`). 所以 `TU m lm ≼ Itr (PU m lm)`. **条件是 `Maj g₀`, 本路没有构造它**: 要 $\theta$ 在严格树上的单调上界, 这是值的定理. 前提的形状可满足: `maj₁` 是 `Maj g₁` ($g_1$ 是全 $0$ 的分支), `ex₁` 用到它. 对 `g₀` 可满足是判断.

```agda
J : HB X₁ S⊥ → Cd
J = ΦX W₀ tt hself hz (z⊲ᴮ W₀) hz

θ : ((y : Cd) → HB X⊥ (Tw X⊥ S⊥ y)) → Cd → Cd
θ g x = hl (chain x (λ c → brX W₀ tt hz (z⊲ᴮ W₀) c g c))

J-hE : ∀ p g → J (hE tt p g) ≡ θ g (J p)
J-hE p g = refl

pos-J : ∀ h → hs hz ≼ J h
pos-J hz = ≼-refl (hs hz)
pos-J (hs h) = ≼l 0 (pos-J h)
pos-J (hl f) = ≼l 0 (pos-J (f 0))
pos-J (hΩ () _)
pos-J (hE tt p g) = ≼l 0 (pos-br (J p) g)
  where
  pos-br : ∀ c g → hs hz ≼ brX W₀ tt hz (z⊲ᴮ W₀) c g c
  pos-br c g = pos≼ (W₀ ⊞ leg c) (wf _) (Lg-⊞ W₀ (leg c) tt (Lg-leg c)) hz (⊲ᴮ-tr (z⊲ᴮ W₀) (⊞-fst W₀ (leg c))) c (g (W₀ ⊞ leg c))

St-J : ∀ h → St (J h)
St-J hz = tt
St-J (hs h) = St-mul (J h) (St-J h) (pos-J h)
St-J (hl f) = St-Σ (λ n → J (f n)) (λ n → St-J (f n)) (λ n → pos-J (f n))
St-J (hΩ () _)
St-J (hE tt p g) = St-chain (J p) (λ c → brX W₀ tt hz (z⊲ᴮ W₀) c g c)
  (λ c → St-Φ (W₀ ⊞ leg c) (wf _) (Lg-⊞ W₀ (leg c) tt (Lg-leg c)) hz (⊲ᴮ-tr (z⊲ᴮ W₀) (⊞-fst W₀ (leg c))) c (g (W₀ ⊞ leg c)))
  (λ c → pos≼ (W₀ ⊞ leg c) (wf _) (Lg-⊞ W₀ (leg c) tt (Lg-leg c)) hz (⊲ᴮ-tr (z⊲ᴮ W₀) (⊞-fst W₀ (leg c))) c (g (W₀ ⊞ leg c)))

record Maj (g : (y : Cd) → HB X⊥ (Tw X⊥ S⊥ y)) : Set where
  field
    D    : Cd → Cd
    D-st : ∀ x → St x → St (D x)
    D-mo : ∀ {x y : Cd} → St x → St y → x ≼ y → D x ≼ D y
    D-ω  : ∀ x → St x → hl (mul x) ≼ D x
    D-θ  : ∀ x → St x → θ g x ≼ D x
open Maj

Sm≼ : (a : ℕ → Cd) → ∀ n → a n ≼ Σ⁺ a n
Sm≼ a zero = ≼-refl (a 0)
Sm≼ a (suc n) = ≼⊞r (Σ⁺ a n) (a (suc n))

mul-mono : ∀ {x y : Cd} → x ≼ y → ∀ n → mul x n ≼ mul y n
mul-mono p zero = p
mul-mono p (suc n) = ⊞-mono (mul-mono p n) p

Sm-mono : ∀ {a b : ℕ → Cd} → (∀ n → a n ≼ b n) → ∀ n → Σ⁺ a n ≼ Σ⁺ b n
Sm-mono p zero = p 0
Sm-mono p (suc n) = ⊞-mono (Sm-mono p n) (p (suc n))

module It {g : (y : Cd) → HB X⊥ (Tw X⊥ S⊥ y)} (M : Maj g) where
  Itr : Cd → Cd
  Itr hz = hs hz
  Itr (hs a) = D M (Itr a)
  Itr (hl f) = hl (Σ⁺ (λ n → Itr (f n)))
  Itr (hΩ () _)
  Itr (hE () _ _)

  infl : ∀ (x : Cd) → St x → x ≼ D M x
  infl x s = ≼-tr (≼l 0 (≼-refl x)) (D-ω M x s)

  St-Itr : ∀ a → St (Itr a)
  pos-Itr : ∀ a → hs hz ≼ Itr a
  St-Itr hz = tt
  St-Itr (hs a) = D-st M (Itr a) (St-Itr a)
  St-Itr (hl f) = St-Σ (λ n → Itr (f n)) (λ n → St-Itr (f n)) (λ n → pos-Itr (f n))
  St-Itr (hΩ () _)
  St-Itr (hE () _ _)
  pos-Itr hz = ≼-refl (hs hz)
  pos-Itr (hs a) = ≼-tr (pos-Itr a) (infl (Itr a) (St-Itr a))
  pos-Itr (hl f) = ≼l 0 (pos-Itr (f 0))
  pos-Itr (hΩ () _)
  pos-Itr (hE () _ _)

  Itr-⊲ : ∀ {a b : Cd} → a ⊲ b → Itr a ≼ Itr b
  Itr-⊲ {a} hself = ≼-refl (Itr a)
  Itr-⊲ {b = hs b} (hsuc p) = ≼-tr (Itr-⊲ p) (infl (Itr b) (St-Itr b))
  Itr-⊲ {b = hl f} (hlim n p) = ≼l n (≼-tr (Itr-⊲ p) (Sm≼ (λ m → Itr (f m)) n))
  Itr-⊲ (hLim {κ = ()} _ _)
  Itr-⊲ (hEx {x = ()} _)

  open Ali₂ {X₁} (Mk g) using () renaming (Sim to Simg; zz to zzg; ss to ssg; ll to llg; oo to oog; es to esg; el to elg; rT to rTg)

  J≼ : ∀ {u : HB X₁ S⊥} {v : Cd} → Simg (rTg {S⊥} hz) u v → J u ≼ Itr v
  J≼ zzg = ≼-refl (hs hz)
  J≼ {hs u} {hs v} (ssg p) =
    ≼-tr (l≼ (λ n → ≼l n (mul-mono (J≼ p) n))) (D-ω M (Itr v) (St-Itr v))
  J≼ {hl f} {hl f′} (llg k) = l≼ (λ n → ≼l n (Sm-mono (λ m → J≼ (k m)) n))
  J≼ (oog () _)
  J≼ {hE tt p _} {hs v} (esg refl q) =
    ≼-tr (D-θ M (J p) (St-J p)) (D-mo M (St-J p) (St-Itr v) (J≼ q))
  J≼ {hE tt p _} {hl w} (elg refl q gp) =
    ≼l 1 (≼-tr (≼-tr (≼-tr (D-θ M (J p) (St-J p)) (D-mo M (St-J p) (St-Itr (w 0)) (J≼ q))) (Itr-⊲ (gp {tt})))
               (≼⊞r (Itr (w 0)) (Itr (w 1))))

TU≼ : (M : Maj g₀) → ∀ m lm → TU m lm ≼ It.Itr M (PU m lm)
TU≼ M m lm = It.J≼ M (inU~ m lm)
```

## §4 前提的实例

```agda
g₁ : (y : Cd) → HB X⊥ (Tw X⊥ S⊥ y)
g₁ y = hz

maj₁ : Maj g₁
maj₁ = record
  { D = λ x → hl (mul (hs x))
  ; D-st = λ x s → St-mul (hs x) s (s≼s z≼)
  ; D-mo = λ _ _ p → l≼ (λ n → ≼l n (mul-mono (s≼s p) n))
  ; D-ω = λ x _ → l≼ (λ n → ≼l n (mul-mono (≼s (≼-refl x)) n))
  ; D-θ = λ x _ → l≼ (λ n → ≼l n (go x n)) }
  where
  go : ∀ x n → chain x (λ c → brX W₀ tt hz (z⊲ᴮ W₀) c g₁ c) n ≼ mul (hs x) n
  go x zero = s≼s z≼
  go x (suc n) = s≼s (≼-tr (go x n) (≼⊞l (mul (hs x) n) x))

ex₁ : J (hE tt hz g₁) ≼ It.Itr maj₁ (hs hz)
ex₁ = It.J≼ maj₁ (Ali.es refl Ali.zz)
```

## §5 Fab6 的读法应如何改写 (全是判断)

以下由 §1, §3 的定理与 [NegFab6Lay](NegFab6Lay.lagda.md) 的定理加上对 ψ 的纸面推算得到, 没有序数值定理.

- `TX`: 读法不动, 读 ψ₀(Ω_Ω). $\theta$ 枚举 $c\mapsto$ ψ₀(Ω_c) 的不动点.
- `TU m`: 从 "ψ₀(Ω_{Ω+m})" 改为 "$c\mapsto$ ψ₀(Ω_c) 的约第 `PU m` 个不动点", 写成界: 在 ψ₀(Ω_Ω) 之上, 在 ψ₀(Ω_{Ω+1}) 之下, 对一切 $m$.
- `TU2`: 从 "ψ₀(Ω_{Ω·2})" 改为 "$a\mapsto$ 第 $a$ 个不动点的不动点", 界: 在 ψ₀(Ω_{Ω+1}) 之下.
- `TΩΩ`: 不动 (`ext L₀` 没有用到原子: `L₀` 的地板是真的 $\Omega_1$-结点). 从 `TΩΩ₂` 起全部下调: `ext-mul` 说 `ext L` 的新结点的第 $c$ 个分支不超过旧值的 $P(c)$ 倍, 所以 `ext` 给的是乘 $\Omega$ 的量级, 不是 $\Omega_{\alpha+\Omega}$. 设 $A$ 是 `ext L₀` 的值 (读 $\Omega_\Omega$): `pow L₀ (c+1)` 读 $A\cdot\Omega^{c}$, `diag`, `P`, `Pc` 只在这个 $A$ 的右乘因子上做 $\Omega_1$ 算术, `TΩ^Ω` 读 ψ₀ 作用在 $A\cdot\Omega^{\Omega^{\Omega}}$ 上, 界: 整个层的代数的闭项都在 ψ₀(Ω_{Ω+1}) 之下.

## §6 只否定什么

**否定的 (定理):** "`TU1`, `TU2` 与 CRw 的闭项相同" 这一可能性 (`Fab6Cmp` 的 "逐项相同" 只是计数); "外部结点的折叠与 CRw 的 $\Omega_\Omega$ 结点的折叠机制相同" (`fab-atom` 对 `crw-br`, `atoms-f₂` 对 `crw-many`).

**否定的 (判断):** "读法相同的 40% 压缩", 与 §5 列的读法.

**不否定:** 外部种类这个想法; 分支类型随坐标变; `Fab6` 的证书与闭项的合法性 (没有查出问题); `TX`, `TΩΩ` 的读法; 它们作为另一条 (更低读法的) 定义的价值. 也没有证明 `TU2` 严格低于 CRw 的任何闭项: 没有跨系统的 `≼`.

**怎样补回来 (判断, 只有玩具).** 效应要前缀进分支, 就要分支的类型放得下前缀里的外部结点. Fab6 的分支类型 `HB X⊥ (Tw X⊥ S⊥ y)` 放不下. 把外部结点投影成分支 $y$ 处的 $g\,y$ 能通过类型, 但前缀的值被截到 $\Omega_y$ 量级, 纸面上不给乘法. 另一种写法是树按世界编索引 ([NegFab6Idx](NegFab6Idx.lagda.md) 的 `W B`, `lift`, `branch`, 编译过的玩具, 没有塔): 不用 `PH`, 不沿折叠搬运证据, 但世界还在, 那是路径的内容. 所以 "把路径变成类型" 可行的形状是**索引**, 不是**只随坐标变的分支类型**. 它在塔上的行数没有测. 这里没有壁垒定理, 也没有穷尽.

## §7 结论 (按档)

- **[定理]** `sim`, `sound`, `inU~`, `inU≼`, `J-hE`, `St-Φ`, `St-J`, `anti-in`, `anti-out`, `atoms-f₂`, `atoms-f₁`, `Ψ≼`, `br≼`, `fl≼`, `ext-mul`, `Gd-ext`, `Gd-ext′`, `Gd-diag`, `Gd-sup`, `Gd-pow`, `Gd-Pc`, `TΩΩ₂-mul`, `TΩ^Ω-bd`, `TX≢`, `TU1≢`, `TU2≢`, `fab-atom`, `crw-br`, `crw-br₂`, `crw-many`, `branch`.
- **[条件定理]** `J≼`, `TU≼`: 条件 `Maj g`; `TU≼` 的 `Maj g₀` 未构造, `Maj g₁` 有实例 `maj₁`.
- **[有限测试]** 位置敏感指纹 `hC`: `TX` 深度 5 (11298 对 11446), `TU1` 深度 7 (6643311 对 6643319), `TU2` 深度 8 (232515889 对 232515905). 盲区: 只看前 $k$ 项, 不给大小方向. 慢增长路径长度在 60 秒内没有结果 (未完成).
- **[判断]** §5 全部; `Maj g₀` 可满足; §6 的 "怎样补回来".
