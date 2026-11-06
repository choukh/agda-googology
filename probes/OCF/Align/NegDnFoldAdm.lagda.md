# 有内容的下降, 否定一路 (三): 裸可入判定与 "留下可入分支" 的桥

> 不含记号. 入口 [NegDnFold](NegDnFold.lagda.md). 对着接口 [DnFoldIf](DnFoldIf.lagda.md) ("接口定稿 2026-11-05 16:13 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FEA` (只对 $\mathbb N\to A$, 来自 `NegLvRdLay`) 只在两条条件定理里作前提, 标 "条件".
>
> 接口 §6 写了两样: `RestrK K` (无世界的层 `HB (Lev c)` 到带世界的层 `HB (LvW a c)`, `ForgetK` 的反方向) 与 `ExactAdm K a` (对裸坐标判定在外层世界 $a$ 里可入), 并说后者 "写出来只为让否定一路对准".
>
> 1. **裸判定推出分离子 (定理), 有外延时推出 WLPO (条件).** `ExactAdm S₀ ωA`, `ExactAdm S₁ (ωA , h)` (层号在 `Ht` 的层 `LvH` 的外层世界), 以及塔上一切站 `ExactAdm (Kc s) (wω s)` (世界塔 `wω` 的底分量是 $\omega$, 与构造一路的 `KcFoldTower.wtω` 同形), 都推出分离子 (`exact-sep`, `exactS₁-sep`, `exactKc-sep`); 有 `FEA` 时推出 WLPO (`exactKc→WLPO`). 由 `NegLvRdLay.decAcc-sep` 得到, 经 `step` 的旧种类与 `sup` 的第 `inj₁ tt` 个分量传下去 (`exStep`, `exSup`, `exKc`).
> 2. **"留下可入分支, 种类下标不变" 的桥与裸判定等价 (定理).** 在层号 $c_\Omega=\mathrm{h\Omega}\,\kappa\,(x\mapsto0)$ 上, `RestrK` 的一个分量 $R$ 若满足 `KeepIdx`: 可入坐标 $x$ 上的结点 `nd x` 被送到以 $(x,e)$ 为种类下标的 $\Omega$-结点 (`keep-in`), 送出的种类下标的坐标就是 $x$ (`keep-idx`); 则对一切 $x$ 判定了 $x$ 在 $a$ 里可入 (`keep→dec`). 反过来, 有判定就有这样的 $R$ (`dec→keep`). 所以有内容的 `RestrK` (逐结点保留可入的分支) 在 $a=\omega$ 的世界里就撞第 1 条 (`keepS₁-sep`).
>
> **前提可满足.** `dec→keep` 在 $a=0$ 的世界上给出 `KeepIdx` 的实例 (`keep0`: $x\lhd0$ 可判定). 分离子的前提 `ExactAdm … ωA` 经典地成立 (判断: 经典地 $x\lhd\omega$ 可判定); `FEA` 在 Agda 里证不出也否证不了 (与 `NegLvRdLay`, `NegKcFoldTower` 同档). 世界 `wω s` 合法 (`lwω`), 是 `WTower` (`wtωN`).
>
> **只否定什么.** 只否定裸判定 (没有公共上界) 与 "保留可入分支且种类下标不变" 的桥 (在 $a$ 的底分量为 $\omega$ 的世界里). **不否定**: 带公共上界的判定 (`KcFoldIf.BDecK`, 已有实例 `KcFoldBdec.bdecLv`); 不判定可入、只走底支或常数的 `RestrK` (常数 `hz` 就是实例); 外层世界取 $0$ 的桥 (`keep0`, 代价是只剩底支, 同 `LvOmNeg.only0`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegDnFoldAdm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; κA)
open import OCF.Align.LvKtCode using (w0; lw0; cdLev)
open import OCF.Align.LvKtIf
open import OCF.Align.KcFoldIf
open import OCF.Align.DnFoldIf
open import OCF.Align.ColimWNeg using (WLPO)
open import OCF.Align.NegLvRdLay using (ωA; Lg-ωA; xα; FEA; decAcc-sep; decAcc→WLPO)
```

## §1 裸判定推出分离子

```agda
Sep : Set
Sep = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (xα α ≡ ωA)

exact-sep : ExactAdm S₀ ωA → Sep
exact-sep D = decAcc-sep (λ a _ → D tt a)

exact→WLPO : FEA → ExactAdm S₀ ωA → WLPO
exact→WLPO fe D = decAcc→WLPO fe (λ a _ → D tt a)

-- 经 step 的旧种类, sup 的分量传下去
exStep : ∀ {S : KS} {w : Wd S} {β : HB S} → ExactAdm (step S) (w , β) → ExactAdm S w
exStep D κ x = D (inj₁ κ) x

exSup : ∀ {I : Set} {F : I → KS} {w : Wd (sup I F)} → ExactAdm (sup I F) w → ∀ i → ExactAdm (F i) (w i)
exSup D i κ x = D (i , κ) x

-- 层号在 Ht 的层的外层世界 (Wd₂ = A × H₀)
exactS₁-sep : ∀ (h : H₀) → ExactAdm S₁ (ωA , h) → Sep
exactS₁-sep h D = exact-sep (exStep {S₀} {ωA} {h} D)
```

**塔上一切站.** `base s a`: 第 $s$ 站世界沿 `inj₁ tt` 分量走到底的 `A`-分量. 世界塔 `wω`: 底分量 $\omega$, 旧站分量取上一站, 读回分量取基世界 (与 `KcFoldTower.aWω` 同形, 只是 $\omega$ 取 `NegLvRdLay` 的那一个).

```agda
base : ∀ s → Wd (Kc s) → A
base zero a = a
base (suc s) a = base s (a (inj₁ tt))

exKc : ∀ s (a : Wd (Kc s)) → ExactAdm (Kc s) a → ExactAdm S₀ (base s a)
exKc zero a D = D
exKc (suc s) a D = exKc s (a (inj₁ tt)) (exSup {⊤ ⊎ HB (Kc s)} {FN (Kc s)} {a} D (inj₁ tt))

wω : ∀ s → Wd (Kc s)
wω zero = ωA
wω (suc s) (inj₁ tt) = wω s
wω (suc s) (inj₂ c) = w0 (cdLev c)

lwω : ∀ s → LgW (Kc s) (wω s)
lwω zero = Lg-ωA
lwω (suc s) (inj₁ tt) = lwω s
lwω (suc s) (inj₂ c) = lw0 (cdLev c)

wtωN : WTower
wtωN = record { aW = wω ; laW = lwω ; grow = λ s → ≤w-rf (Kc s) }

baseω : ∀ s → base s (wω s) ≡ ωA
baseω zero = refl
baseω (suc s) = baseω s

exactKc-sep : ∀ s → ExactAdm (Kc s) (wω s) → Sep
exactKc-sep s D = exact-sep (subst (ExactAdm S₀) (baseω s) (exKc s (wω s) D))

exactKc→WLPO : FEA → ∀ s → ExactAdm (Kc s) (wω s) → WLPO
exactKc→WLPO fe s D = exact→WLPO fe (subst (ExactAdm S₀) (baseω s) (exKc s (wω s) D))
```

## §2 "留下可入分支" 的桥与裸判定等价

层号 $c_\Omega=\mathrm{h\Omega}\,\kappa\,(x\mapsto0)$: `Lev cΩ` 的种类是 $(x,\mathrm{tt})$ (坐标 `A`), `LvW a cΩ` 的种类是 $((x,e),\cdot)$, $e$ 是 $x$ 在 $a$ 里可入的证据. `nd x` 是 `Lev cΩ` 里种类 $(x,\mathrm{tt})$ 的结点; `kix` 读出一个高度的头的种类下标.

```agda
module Keep {𝕂 : KS} (a : Wd 𝕂) (κ : K 𝕂) where
  cΩ : HB 𝕂
  cΩ = hΩ κ (λ _ → hz)

  nd : E 𝕂 κ → HB (Lev cΩ)
  nd x = hΩ (x , tt) (λ _ → hz)

  kix : HB (LvW a cΩ) → Maybe (Σ (E 𝕂 κ) (λ x → Bd 𝕂 κ x a))
  kix (hΩ (p , _) _) = just p
  kix _ = nothing

  KeepIdx : (HB (Lev cΩ) → HB (LvW a cΩ)) → Set
  KeepIdx R =
    (∀ x → Bd 𝕂 κ x a → Σ (Σ (E 𝕂 κ) (λ y → Bd 𝕂 κ y a)) (λ p → kix (R (nd x)) ≡ just p)) ×
    (∀ x p → kix (R (nd x)) ≡ just p → proj₁ p ≡ x)

  keep→dec : ∀ R → KeepIdx R → ∀ x → Dec (Bd 𝕂 κ x a)
  keep→dec R (k1 , k2) x with kix (R (nd x)) in eq
  ... | just p = yes (subst (λ y → Bd 𝕂 κ y a) (k2 x p eq) (proj₂ p))
  ... | nothing = no (λ b → nj (trans (sym eq) (proj₂ (k1 x b))))
    where
    nj : ∀ {p} → ¬ (nothing ≡ just p)
    nj ()

  -- 反方向: 有判定就有这样的桥
  Rd : (x : E 𝕂 κ) → Dec (Bd 𝕂 κ x a) → HB (LvW a cΩ)
  Rd x (yes e) = hΩ ((x , e) , inj₁ tt) (λ _ → hz)
  Rd x (no _) = hz

  RD : (∀ x → Dec (Bd 𝕂 κ x a)) → HB (Lev cΩ) → HB (LvW a cΩ)
  RD D (hΩ (x , tt) g) = Rd x (D x)
  RD D _ = hz

  dec→keep : (D : ∀ x → Dec (Bd 𝕂 κ x a)) → KeepIdx (RD D)
  dec→keep D = k1 , k2
    where
    k1 : ∀ x → Bd 𝕂 κ x a → Σ (Σ (E 𝕂 κ) (λ y → Bd 𝕂 κ y a)) (λ p → kix (RD D (nd x)) ≡ just p)
    k1 x b with D x
    ... | yes e = (x , e) , refl
    ... | no ¬b = ⊥-elim (¬b b)
    k2 : ∀ x p → kix (RD D (nd x)) ≡ just p → proj₁ p ≡ x
    k2 x p eq with D x
    k2 x .(x , e) refl | yes e = refl
    k2 x p () | no _
```

`RestrK` 的分量. 一个 `ρ : RestrK K` 在 $(a, c_\Omega)$ 上满足 `KeepIdx`, 就判定了种类 $\kappa$ 的坐标在 $a$ 里可入.

```agda
restr→dec : ∀ {𝕂 : KS} (ρ : RestrK 𝕂) (a : Wd 𝕂) (la : LgW 𝕂 a) (κ : K 𝕂) →
  Keep.KeepIdx a κ (ρ a la (Keep.cΩ a κ)) → ∀ x → Dec (Bd 𝕂 κ x a)
restr→dec ρ a la κ k = Keep.keep→dec a κ (ρ a la (Keep.cΩ a κ)) k

-- 层号在 Ht 的层 (K = S₁), 外层世界 (ω, h), 种类 κA: 撞分离子
keepS₁-sep : ∀ (h : H₀) (ρ : RestrK S₁) (la : LgW S₁ (ωA , h)) →
  Keep.KeepIdx {S₁} (ωA , h) κA (ρ (ωA , h) la (Keep.cΩ {S₁} (ωA , h) κA)) → Sep
keepS₁-sep h ρ la k = exact-sep (λ _ x → restr→dec ρ (ωA , h) la κA k x)

keepS₁→WLPO : FEA → ∀ (h : H₀) (ρ : RestrK S₁) (la : LgW S₁ (ωA , h)) →
  Keep.KeepIdx {S₁} (ωA , h) κA (ρ (ωA , h) la (Keep.cΩ {S₁} (ωA , h) κA)) → WLPO
keepS₁→WLPO fe h ρ la k = exact→WLPO fe (λ _ x → restr→dec ρ (ωA , h) la κA k x)

-- 前提实例: 外层世界 0 上可判定, 所以 KeepIdx 有实例
dec0 : ∀ x → Dec (x ⊲ azero)
dec0 azero = yes C.self
dec0 (asuc x) = no (λ ())
dec0 (alim f) = no (λ ())

keep0 : Keep.KeepIdx {S₀} azero tt (Keep.RD {S₀} azero tt dec0)
keep0 = Keep.dec→keep {S₀} azero tt dec0

lgω₁ : LgW S₁ (ωA , hz)
lgω₁ = Lg-ωA , tt
```

## §3 结论 (按档)

- **[定理]** `exact-sep`, `exactS₁-sep`, **`exactKc-sep`** (一切站 $s$, 世界塔 `wω`): 裸判定 ⇒ 分离子. **[定理, 条件 `FEA`]** `exact→WLPO`, **`exactKc→WLPO`**.
- **[定理]** `exStep`, `exSup`, `exKc`, `baseω`, `lwω`, `wtωN` (前提的世界合法, 是 `WTower`).
- **[定理]** **`Keep.keep→dec`**, **`Keep.dec→keep`**: 保留可入分支且种类下标不变的桥 ⇔ 裸判定. `restr→dec`: 对 `RestrK` 的分量. **`keepS₁-sep`** (定理), `keepS₁→WLPO` (条件 `FEA`): 层号在 `Ht` 的层上, 外层世界的 `A`-分量为 $\omega$ 时.
- **[定理]** `dec0`, `keep0`: 前提实例 (外层世界 $0$).
- 为什么构造一路需要: `KcFold` 接手清单第 1 条要把 `LvOm` 推广到层号在 `Ht` (接口的 `LvH`), 外层世界取 `A × H₀`; 读回要进带世界的层, 就要把无世界的层 (`Lev c`, 接口 `KcFoldTop.top` 所在的类型) 搬进 `LvW a c`, 即 `RestrK`; 有内容的搬法是逐结点保留在 $a$ 里可入的分支 (`LvOmRd` 的 "可入就读成种类, 否则读成底" 的形状). 本篇说: 无公共上界时这就是 `ExactAdm`, 撞分离子. 出路 (判断): 照 `LvOmRd.RW.rdW` 在**读的世界** $W\ge a$ 之下判定 (`BDecK`, 有实例), 或者不判定, 只走底支 (代价 `only0`).
