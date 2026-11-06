# 层号换类型, 否定一路 (二): 拷贝的界, 基世界只见底支, 不封口

> 不含记号. 入口 [NegLvKt](NegLvKt.lagda.md). 对着接口 [LvKtIf](LvKtIf.lagda.md) ("接口定稿 2026-11-05 15:21 (首次编译通过)", 变更记录: 无) 写, 导入它与它依赖的 [LvKtCode](LvKtCode.lagda.md), 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> 1. **嵌入的拷贝与原件的界互不相干 (定理).** `emb = ι (inj₁ tt)` 把第 $s$ 站的种类 $\kappa$ 搬成第 $s+1$ 站的种类 $(\mathrm{inj_1\,tt},\kappa)$; 在极限 `KΛc` 里两者是 $(s,\kappa)$ 与 $(s+1,(\mathrm{inj_1\,tt},\kappa))$, 坐标类型相同 (底种类, 坐标 `A`), 界在世界的两个独立分量里. **`no-emb→`, `no-emb←`**: 在合法的 `KΛc` 世界里, 一个的界推不出另一个的界 (两个方向). 推论 **`no-routeΛ`**: 经任何种类结构的任何种类都不能同时 "读进原件的界" 与 "读出拷贝的界" (`HtTowerNStage.no-wmatch`, `CohWNeg.no-route` 的形状, 落在接口的 `KΛc` 与 `emb` 上). 站内同样: `Kc 1` 里嵌入的底种类 $(\mathrm{inj_1\,tt},\mathrm{tt})$ 与层号 $0$ 处的拷贝 $(\mathrm{inj_2}\,0,\mathrm{tt})$ (`Lev hz = S₀`) 互不相干 (**`no-copy→`, `no-copy←`**). 各半可满足 (`sat0`, `sat1`, `satE`, `satL`).
> 2. **基世界只见底支 (定理).** 接口的码 `CdK` 带基世界 `w0` (`cdS₀` 取 $0$, `cdStep` 取 $(w_0,0)$, `cdSup` 逐分量). **`only-botK`**, **`only-botΛ`**: 在 `w0 (ckc s)` (任一站) 与 `w0 ckΛ` (极限) 里, 任一种类的界之下只有最小坐标 `bot`. 推论 **`code-botK`**, **`code-botΛ`**: 外层世界取基世界时, 码进 $\Omega$-分支的坐标码的目标恒为 `bot`; 码只走每个 $\Omega$-结点的底支. 这是 `LvOmNeg.only0` 对一切站与极限的推广. 对照: 世界变大就看得见别的坐标 (`sees1`).
> 3. **不封口 (定理, `no-retract` 的实例).** 极限 `KΛc` 与每个后继站 `Kc (s+1)` 都没有以自身全部高度为坐标收缩的种类 (`no-closeΛ`, `no-closeNxt`); 回灌输出的读法 `HB (step S) → HB S` 都没有左逆 (`no-faithfulK`, `NegLvRdLay.no-faithful` 推广到一切 `S`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegLvKtCopy where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.LvKtCode using (CdK; cdLev; cdS₀; w0; lw0; vE; tE; pE)
open import OCF.Align.LvKtIf
```

## §1 拷贝

```agda
one : A
one = asuc azero

-- 第 1 站: 嵌入的底种类, 与层号 0 处的底种类
κE κL : K (Kc 1)
κE = inj₁ tt , tt
κL = inj₂ hz , tt

sameE : E (Kc 1) κE ≡ E (Kc 1) κL
sameE = refl

-- 极限: 第 0 站的底种类与它在第 1 站的嵌入拷贝
κ0 κ1 : K KΛc
κ0 = 0 , tt
κ1 = 1 , κE

emb-kind : κ1 ≡ (1 , (inj₁ tt , tt))
emb-kind = refl
```

**合法的世界.** 第 1 站的世界是对 `⊤ ⊎ HB S₀` 的函数; 一个分量取 $1$, 其余取基世界 (`lw0` 给合法). 极限的世界逐站取.

```agda
wE1 : Wd (Kc 1)
wE1 (inj₁ tt) = one
wE1 (inj₂ c) = w0 (cdLev c)

lgE1 : LgW (Kc 1) wE1
lgE1 (inj₁ tt) = tt
lgE1 (inj₂ c) = lw0 (cdLev c)

wL1 : Wd (Kc 1)
wL1 (inj₁ tt) = azero
wL1 (inj₂ hz) = one
wL1 (inj₂ (hs c)) = w0 (cdLev (hs c))
wL1 (inj₂ (hl f)) = w0 (cdLev (hl f))
wL1 (inj₂ (hΩ κ g)) = w0 (cdLev (hΩ κ g))

lgL1 : LgW (Kc 1) wL1
lgL1 (inj₁ tt) = tt
lgL1 (inj₂ hz) = tt
lgL1 (inj₂ (hs c)) = lw0 (cdLev (hs c))
lgL1 (inj₂ (hl f)) = lw0 (cdLev (hl f))
lgL1 (inj₂ (hΩ κ g)) = lw0 (cdLev (hΩ κ g))

wX wY : Wd KΛc
wX zero = one
wX (suc s) = w0 (ckc (suc s))
wY zero = azero
wY (suc zero) = wE1
wY (suc (suc s)) = w0 (ckc (suc (suc s)))

lgX : LgW KΛc wX
lgX zero = tt
lgX (suc s) = lw0 (ckc (suc s))

lgY : LgW KΛc wY
lgY zero = tt
lgY (suc zero) = lgE1
lgY (suc (suc s)) = lw0 (ckc (suc (suc s)))
```

**否定.**

```agda
no-emb→ : ¬ (∀ {c w} → LgW KΛc w → Bd KΛc κ0 c w → Bd KΛc κ1 c w)
no-emb→ h with h {one} {wX} lgX C.self
... | ()

no-emb← : ¬ (∀ {c w} → LgW KΛc w → Bd KΛc κ1 c w → Bd KΛc κ0 c w)
no-emb← h with h {one} {wY} lgY C.self
... | ()

no-copy→ : ¬ (∀ {c w} → LgW (Kc 1) w → Bd (Kc 1) κE c w → Bd (Kc 1) κL c w)
no-copy→ h with h {one} {wE1} lgE1 C.self
... | ()

no-copy← : ¬ (∀ {c w} → LgW (Kc 1) w → Bd (Kc 1) κL c w → Bd (Kc 1) κE c w)
no-copy← h with h {one} {wL1} lgL1 C.self
... | ()

no-routeΛ : ∀ (S′ : KS) (κ′ : K S′) (t : A → E S′ κ′) (wm : Wd KΛc → Wd S′) →
  (∀ {c w} → LgW KΛc w → Bd KΛc κ0 c w → Bd S′ κ′ (t c) (wm w)) →
  (∀ {c w} → LgW KΛc w → Bd S′ κ′ (t c) (wm w) → Bd KΛc κ1 c w) → ⊥
no-routeΛ S′ κ′ t wm h1 h0 = no-emb→ (λ lw e → h0 lw (h1 lw e))

no-routeΛ← : ∀ (S′ : KS) (κ′ : K S′) (t : A → E S′ κ′) (wm : Wd KΛc → Wd S′) →
  (∀ {c w} → LgW KΛc w → Bd KΛc κ1 c w → Bd S′ κ′ (t c) (wm w)) →
  (∀ {c w} → LgW KΛc w → Bd S′ κ′ (t c) (wm w) → Bd KΛc κ0 c w) → ⊥
no-routeΛ← S′ κ′ t wm h1 h0 = no-emb← (λ lw e → h0 lw (h1 lw e))
```

**各半可满足** (同一个坐标 $1$, 各在自己的世界里):

```agda
sat0 : Bd KΛc κ0 one wX
sat0 = C.self
sat1 : Bd KΛc κ1 one wY
sat1 = C.self
satE : Bd (Kc 1) κE one wE1
satE = C.self
satL : Bd (Kc 1) κL one wL1
satL = C.self
```

## §2 基世界只见底支

```agda
botA : ∀ {c} → c ⊲ azero → c ≡ azero
botA C.self = refl

botH : ∀ {S} {w : Wd S} {c : HB S} → c ⊲[ w ] hz → c ≡ hz
botH hself = refl

only-botLev : ∀ {S} (x : HB S) (κ : K (Lev x)) (c : E (Lev x) κ) →
  Bd (Lev x) κ c (w0 (cdLev x)) → c ≡ bot (Lev x) κ
only-botLev hz κ c e = botA e
only-botLev (hs x) (inj₁ κ) c e = only-botLev x κ c e
only-botLev (hs x) (inj₂ tt) c e = botH e
only-botLev (hl f) (n , κ) c e = only-botLev (f n) κ c e
only-botLev (hΩ κ₀ g) (i , κ) c e = only-botLev (g i) κ c e

only-botK : ∀ s (κ : K (Kc s)) (c : E (Kc s) κ) → Bd (Kc s) κ c (w0 (ckc s)) → c ≡ bot (Kc s) κ
only-botK zero κ c e = botA e
only-botK (suc s) (inj₁ tt , κ) c e = only-botK s κ c e
only-botK (suc s) (inj₂ x , κ) c e = only-botLev x κ c e

only-botΛ : ∀ (κ : K KΛc) (c : E KΛc κ) → Bd KΛc κ c (w0 ckΛ) → c ≡ bot KΛc κ
only-botΛ (s , κ) c e = only-botK s κ c e

code-botK : ∀ s (κ : K (Kc s)) re (v : vE (ckc s) κ (w0 (ckc s)) re) →
  tE (ckc s) κ (w0 (ckc s)) re v ≡ bot (Kc s) κ
code-botK s κ re v = only-botK s κ _ (pE (ckc s) κ (w0 (ckc s)) re v)

code-botΛ : ∀ (κ : K KΛc) re (v : vE ckΛ κ (w0 ckΛ) re) → tE ckΛ κ (w0 ckΛ) re v ≡ bot KΛc κ
code-botΛ κ re v = only-botΛ κ _ (pE ckΛ κ (w0 ckΛ) re v)

-- 世界变大就看得见坐标 1
sees1 : Bd (Kc 1) κE one wE1
sees1 = C.self
```

## §3 不封口, 读法不忠实

```agda
no-closeΛ : ∀ (κ : K KΛc) (e : HB KΛc → E KΛc κ) (d : E KΛc κ → HB KΛc) → ¬ (∀ x → d (e x) ≡ x)
no-closeΛ = no-retract {S = KΛc}

no-closeNxt : ∀ s (κ : K (Kc (suc s))) (e : HB (Kc (suc s)) → E (Kc (suc s)) κ)
  (d : E (Kc (suc s)) κ → HB (Kc (suc s))) → ¬ (∀ x → d (e x) ≡ x)
no-closeNxt s = no-retract {S = Kc (suc s)}

no-faithfulK : ∀ (S : KS) (σ : HB (step S) → HB S) (d : HB S → HB (step S)) → ¬ (∀ x → d (σ x) ≡ x)
no-faithfulK S σ d = no-retract {S = step S} (inj₂ tt) σ d
```

## §4 只否定什么

- **否定**: 合法的 `KΛc` 世界里, 第 $s$ 站的种类与它的嵌入拷贝的界互相推出 (任一方向); 经任一种类结构的任一种类同时读通两者; 第 1 站里嵌入的底种类与 `Lev hz` 里的底种类的界互相推出; 外层世界取基世界 `w0` 时码走到非底坐标; `KΛc` 或 `Kc (s+1)` 有收缩自身全部高度的种类; 读法 `HB (step S) → HB S` 有左逆.
- **不否定**: 接口 (它没有要求拷贝的界相干, 没有固定外层世界; `FoldAtK` 以外层世界 $a$ 为输入); 由塔自己构造的相干世界 (例如每站的外层世界把 `inj₁ tt` 分量取成上一站的外层世界: 那是对**特定**世界的构造, 不是对一切合法世界的律); 外层世界变大 (`sees1`).
- 第 1 条的形状在 `HtTowerNStage.no-wmatch` (`U′`), `NegLvRdLay.no-wmatch-ω` (`Gω`), `CohWNeg.no-cross→` (`U⋆` 的 `Lev` 部分) 里已出现; 这里是同一现象落在接口的 `KΛc`, `emb`, `nxt` 上, 不是新的现象.
