# 层号由回灌给出: 一个外层界含极限的世界里的逐级折叠

> 不含记号. 入口 [LvFb](LvFb.lagda.md). 作者选定原话: "A3 提前探路". 用 W2 ([LvFbCode](LvFbCode.lagda.md): 以码为下标的世界, 单个增量有精确的 `at` 律) 把 [FamFoldAll](FamFoldAll.lagda.md) 的逐级折叠搬进**一个**世界: 外层界 $\omega+1$ (`bω = hs ω₀`, 含极限坐标 $\omega$), 一切有限级都在这个世界里回灌 (第 $n+1$ 级在 $n+1$ 的码 `kfin (n+1)` 上), 极限坐标 $\omega$ 的码 `kω` 上的槽由各级级顶的输出读回逐级升高. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延; 本篇没有模块参数, 没有条件定理.
>
> **构造.**
>
> - **第 $n+1$ 级的折叠** `FKc.fold n d ld v Λ W`: 与 `FamFoldAll.FK` 同形 (旧种类交给 `FamFoldRead.trK`, 新种类回灌), 世界换成码世界 `Wω.Cmpᶜ`, 更新换成 `Wω.raiseC` 在码 `kfin (n+1)` 上的单个增量 `ofSk (n+1) (rdO o)`. **不要族读回** (`famK`, `mFin`, `Uniform` 都不出现): `at` 律在一切码上是定理 (`LvFbCode.CW.at`).
> - **下降** `dnc`, 级顶 `Hc n`, 对角 `Λc`, 闭项 `T∞c = T⁺ Λc`, `fghc` (同 `FamFoldAll` 的形状, 折叠换成码世界的).
> - **极限层被回灌升高** `Vω`: $V_0$ = 全零世界; $V_{n+1}$ = $V_n$ 在码 `kω` 上接上 $\iota_{n+1}(\mathrm{ofSk}\,(\mathrm{rt}\,n))$, 其中 `rt n` 是第 $n+1$ 级的折叠在**世界 $V_n$** 里对级顶 `Ωtop (Sk (n+1))` 的输出的读回 (输出读成 `HB (Sk (n+1))`), $\iota_{n+1}$ 是 `HtTowerTy.ι` (种类结构 `G₀ ω₀ = sup ℕ (G₀ ∘ fin)` 的第 $n+1$ 个分量). 增量是折叠输出的函数, 不读世界的任何界.
>
> **形状定理.** `ωslot-s` (极限层的槽 = 旧槽 ⊞ 这一级的读回, 定义相等之外由 `at` 给出), `fin-zero` (有限码的槽在 $V_n$ 里不动), `lgV` (合法), `monoV` (只增); `lv1`, `lv2`: $V_1$, $V_2$ 的极限层槽的第 2 格最外是第 1, 第 2 级新种类的节点 (对具体级数的计算), 即 "极限层的界里出现的级随回灌升高". 级的折叠: `FKc.fold-Ω` (`refl`), `FKc.slot-s` (由 `at`), `FKc.ch-lg`, `FKc.ch-≤`.
>
> **范围 (坦白).** 第一, **层号本身仍是 ℕ**: 第 $n+1$ 级的折叠在码 `kfin (n+1)` 上回灌, 级数 $n$ 由外部给出; 由回灌给出的是极限层 $\omega$ 的**界** (槽), 不是回灌所在的坐标. 第二, 极限层的槽**没有被任何折叠读**: 读它要一个第 $\omega+1$ 级的折叠, 那要把 `HB (G₀ ω₀)` (种类是 $(n,\kappa)$ 的混合高度) 降到两种种类的层, 而现有的下降 `dnR n` 是逐级折叠, 对混合高度没有定义 (第一个障碍). 第三, 级的折叠只读自己的码的槽, 所以把世界在级之间串起来 (`rt` 用 $V_n$) 不改变有限级的输出 (`fin-zero`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvFbFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; D; n0; n1; _⨾_; nl)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺; ord; W₁)
open import OCF.Align.AdmWIf using (G₀)
open import OCF.Align.AdmWCoh using (fin; ω₀)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.FamFoldLift using (≤r)
open import OCF.Align.FamFoldRead using (ly; rdr; lgr; pkg; Rd; trK)
open import OCF.Align.FamFoldAll using (toSk; ofSk; lg-subst; eqG; δK; lδK; Dn)
open import OCF.Align.LvFbCode using (Code; tgt; kω; kfin; Pω; module Wω; v₀; lv₀)
```

## §1 第 $n+1$ 级的折叠, 在码世界里

```agda
module FKc (n : ℕ) (d : HB (Sk (suc n)) → Ht) (ld : ∀ x → LgB x → LgB (d x)) where
  K₁ : ℕ
  K₁ = suc n

  k₀ : Code azero (hs ω₀)
  k₀ = kfin K₁

  Outₖ : Set
  Outₖ = (W : Wd₂) → D (ly (suc K₁)) W

  slot : Wω.Cmpᶜ → HB (Sk K₁)
  slot u = toSk K₁ (Wω.slot u k₀)

  lay : Outₖ → HB (Sk K₁)
  lay o = rdr (Rd K₁) (tt , tt) hz (o W₁)

  Lg-lay : ∀ o → LgB (lay o)
  Lg-lay o = lgr (Rd K₁) (tt , tt) hz (o W₁) tt

  rdO : Outₖ → HB (Sk K₁)
  rdO o = δK K₁ (d (lay o)) (ld (lay o) (Lg-lay o))

  lg-rdO : ∀ o → LgB (rdO o)
  lg-rdO o = lδK K₁ (d (lay o)) (ld (lay o) (Lg-lay o))

  -- 单个增量: 读回值本身 (搬到 G₀ (fin K₁)), 不是族
  inc : Outₖ → HB (G₀ (fin K₁))
  inc o = ofSk K₁ (rdO o)

  lg-inc : ∀ o → LgB (inc o)
  lg-inc o = lg-subst (sym (eqG K₁)) (rdO o) (lg-rdO o)

  ch : (Wω.Cmpᶜ → Outₖ) → Wω.Cmpᶜ → ℕ → Wω.Cmpᶜ
  ch Fo v zero = v
  ch Fo v (suc k) = Wω.raiseC (ch Fo v k) k₀ (inc (Fo (ch Fo v k)))

  fold : Wω.Cmpᶜ → HB (Sk (suc K₁)) → Outₖ
  fold v hz W = n0
  fold v (hs x) W = fold v x W ⨾ n1
  fold v (hl f) W = nl (λ k → fold v (f k) W)
  fold v (hΩ (inj₁ κ) g) W = trK (pkg n) ≤r κ hself (λ c W′ → fold v (g c) W′) W
  fold v (hΩ (inj₂ tt) g) W =
    nl (λ k → fold (ch (λ u → fold u (g (slot u))) v k) (g (slot (ch (λ u → fold u (g (slot u))) v k))) W)

  chain : Wω.Cmpᶜ → (HB (Sk K₁) → HB (Sk (suc K₁))) → ℕ → Wω.Cmpᶜ
  chain v g = ch (λ u → fold u (g (slot u))) v

  fold-Ω : ∀ v g W → fold v (hΩ (inj₂ tt) g) W ≡ nl (λ k → fold (chain v g k) (g (slot (chain v g k))) W)
  fold-Ω v g W = refl

  -- 槽的递推: 由码上的 at 律, 不要族
  slot-s : ∀ v g k → Wω.slot (chain v g (suc k)) k₀ ≡
           Wω.slot (chain v g k) k₀ ⊞ inc (fold (chain v g k) (g (slot (chain v g k))))
  slot-s v g k = Wω.slot-at (chain v g k) k₀ _

  ch-lg : ∀ v g → Wω.LgC v → ∀ k → Wω.LgC (chain v g k)
  ch-lg v g lv zero = lv
  ch-lg v g lv (suc k) =
    Wω.legal (chain v g k) k₀ _ (lg-inc (fold (chain v g k) (g (slot (chain v g k))))) (ch-lg v g lv k)

  ch-≤ : ∀ v g k → chain v g k Wω.≤C chain v g (suc k)
  ch-≤ v g k = Wω.mono (chain v g k) k₀ _
```

## §2 下降, 级顶, 对角闭项

```agda
idxc : ∀ n → Dn n → Wω.Cmpᶜ → HB (Sk (suc (suc n))) → HB (Sk (suc n))
idxc n (d , ld) v Λ = FKc.lay n d ld (FKc.fold n d ld v Λ)

Lg-idxc : ∀ n (D′ : Dn n) v Λ → LgB (idxc n D′ v Λ)
Lg-idxc n (d , ld) v Λ = FKc.Lg-lay n d ld (FKc.fold n d ld v Λ)

dnc : ∀ n → Dn n
dnc zero = (λ x → x) , (λ x l → l)
dnc (suc n) = (λ Λ → proj₁ (dnc n) (idxc n (dnc n) v₀ Λ)) , (λ Λ _ → proj₂ (dnc n) _ (Lg-idxc n (dnc n) v₀ Λ))

Hc : ℕ → Ht
Hc n = proj₁ (dnc n) (Ωtop (Sk n))

lgHc : ∀ n → LgB (Hc n)
lgHc n = proj₂ (dnc n) (Ωtop (Sk n)) (Lg-Ωtop (Sk n))

cumc : ℕ → Ht
cumc zero = Hc zero
cumc (suc k) = cumc k ⊞ Hc (suc k)

lcumc : ∀ k → LgB (cumc k)
lcumc zero = lgHc zero
lcumc (suc k) = Lg-⊞ (cumc k) (Hc (suc k)) (lcumc k) (lgHc (suc k))

Λc : Ht
Λc = hl cumc

lΛc : LgB Λc
lΛc = (λ k → ⊞-fst (cumc k) (Hc (suc k))) , lcumc

T∞c : A
T∞c = T⁺ Λc lΛc

Lg-T∞c : Lg T∞c
Lg-T∞c = Lg-T⁺ Λc lΛc

fghc : ℕ → ℕ
fghc = FL.FGH (ord T∞c)
```

## §3 极限层被回灌升高

```agda
Vω : ℕ → Wω.Cmpᶜ

-- 第 n+1 级的折叠在世界 V n 里对级顶的输出的读回
rt : ∀ n → HB (Sk (suc n))
rt n = idxc n (dnc n) (Vω n) (Ωtop (Sk (suc n)))

lrt : ∀ n → LgB (rt n)
lrt n = Lg-idxc n (dnc n) (Vω n) (Ωtop (Sk (suc n)))

-- 极限层的增量: 读回值放进 G₀ ω₀ = sup ℕ (G₀ ∘ fin) 的第 n+1 个分量
incω : ∀ n → HB (G₀ ω₀)
incω n = ι {F = λ m → G₀ (fin m)} (suc n) (ofSk (suc n) (rt n))

lincω : ∀ n → LgB (incω n)
lincω n = Lg-ι {F = λ m → G₀ (fin m)} (suc n) _ (lg-subst (sym (eqG (suc n))) (rt n) (lrt n))

Vω zero = v₀
Vω (suc n) = Wω.raiseC (Vω n) kω (incω n)

ωslot-s : ∀ n → Wω.slot (Vω (suc n)) kω ≡ Wω.slot (Vω n) kω ⊞ incω n
ωslot-s n = Wω.slot-at (Vω n) kω (incω n)

lgV : ∀ n → Wω.LgC (Vω n)
lgV zero = lv₀
lgV (suc n) = Wω.legal (Vω n) kω (incω n) (lincω n) (lgV n)

monoV : ∀ n → Vω n Wω.≤C Vω (suc n)
monoV n = Wω.mono (Vω n) kω (incω n)

-- 有限码不动
kω≢kfin : ∀ m → ¬ (kω ≡ kfin m)
kω≢kfin m ()

fin-zero : ∀ n m → Wω.slot (Vω n) (kfin m) ≡ hz
fin-zero zero m = refl
fin-zero (suc n) m = trans (cong proj₂ (Wω.off (Vω n) kω (incω n) (kfin m) (kω≢kfin m))) (fin-zero n m)
```

**极限层的界里出现的级.** `lvOf x` 读出 `HB (G₀ ω₀)` 的最外节点的种类的级号 (不是节点时为 0). $V_1$, $V_2$ 的极限层槽的第 2 格分别是第 1, 第 2 级**新种类** (`inj₂ tt`) 的节点.

```agda
cellsOf : ∀ {S} → HB S → ℕ → HB S
cellsOf (hl f) = f
cellsOf _ = λ _ → hz

NewAt : ℕ → HB (G₀ ω₀) → Set
NewAt k (hΩ (suc j , inj₂ tt) _) = suc j ≡ k
NewAt k (hΩ (suc j , inj₁ _) _) = ⊥
NewAt k (hΩ (zero , _) _) = ⊥
NewAt k hz = ⊥
NewAt k (hs _) = ⊥
NewAt k (hl _) = ⊥

lv1 : NewAt 1 (cellsOf (Wω.slot (Vω 1) kω) 2)
lv1 = refl

lv2 : NewAt 2 (cellsOf (Wω.slot (Vω 2) kω) 2)
lv2 = refl
```

## §4 结论 (按档)

- **[定理]** `FKc.fold-Ω`, **`FKc.slot-s`** (由码上的 `at`, 不要族), `FKc.ch-lg`, `FKc.ch-≤`.
- **[定义; 合法是定理]** `dnc`, `Hc`, `Λc`, **`T∞c`**, `Lg-T∞c`, `fghc`.
- **[定理]** **`ωslot-s`**, `lgV`, `monoV`, `fin-zero`.
- **[定理, 对具体级数的计算]** `lv1`, `lv2`.
- **[判断]** 读法: `T∞c` 与 `FamFoldAll.T∞` 的输入逐级同形 (有限码的槽在两边都从 0 起, 回灌同法), 读 $\psi_0(\Omega_{\Omega_\omega})$ (判断, 没有值定理). `Vω` 的极限层槽是第 $\omega$ 层的界, 不进任何闭项.
