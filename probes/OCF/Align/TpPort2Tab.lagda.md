# 两种种类的 Ω-极限一步 (五): 律 (b) 的严格版扩到 Ω-极限的右边, 去条件的闭项定理

> 入口 [TpPort2](TpPort2.lagda.md). 不含记号. 手写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 不改树、折叠、合法性.
>
> - **`fst<⁺`**: 接口 [TpMonoIf](TpMonoIf.lagda.md) 的律 (b) 严格版 `FstMono<`, 右边 $b$ 满足 `FreeTop b` 时成立: $b=h+1$ 且 $h$ 不含 Ω-极限, 或 $b=\mathrm{hl}\,f$ 且各项不含, 或 **$b=\mathrm{h\Omega}\,\kappa\,g$ 且 $g(\mathrm{bot})$ 不含** (新). 依据: 最小世界 $w_0=(0,0)$ 里过 $\Omega$-分支的路径只能走最小坐标 (界的证据 `C.self` / `hself` 把坐标定成 `bot`), 于是一步是 `TpPort2Om.sΩ`, 其余是 `TpPortStep.fst₀F`. `TpPortStep.fst<F` (右边 `Free`) 是它的特例.
> - **`fstLim`**: 非严格版只在路径不是 `hself` 时 (`NotSelf`) 给出; `hself` 一支要 Ω-极限输入上的合法性证明无关, 本组没有.
> - 去了条件的闭项定理: `TpMonoTab` 里较小一边不含 Ω-极限、较大一边最外是 Ω-极限且最小坐标的分支不含的那几条 (见 §2). 其余仍是条件定理, 边界写成编译过的 `¬FT-*` (只说本组的 `FreeTop` 不覆盖它们).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPort2Tab where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤-refl; ≤-trans; ≤-suc; irr)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; hself; hsuc; hlim; hLim; _⊲[_]_; LgB; bot; botBd; _⊞_)
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂; κA; κH)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺; Ω₂ᴴ; lΩ₂; T-Ω₂; mul; Lg-mul; Ω₂ω; Lg-Ω₂ω; T-Ω₂ω)
open import OCF.Align.TpMonoIf using (_⊲⁺[_]_; psuc; plim; pLim; _⊏_; _⊑_)
open import OCF.Align.TpPortSim using (Free)
open import OCF.Align.TpPortStep using (w₀; fst₀F; module SucF; module LimF; upto-all)
open import OCF.Align.TpPort2Om using (sΩ)
open import OCF.Align.HtTowerNFb using (Λs₂; Λω₂; lΛω₂; T-fb₂; T-fb₂ω)
open import OCF.Align.FamFoldOne using (idx; Lg-idx; cells; cells-st; Ω₃; Tᵀ)
open import OCF.Align.UipFbClosed using (module C₁; Tᵁ)
open import OCF.Align.FamFoldAll using (H; cum; Λ∞; T∞)
open import OCF.Align.LvRdFold using (Hn; ΛF)
open import OCF.Align.NegTpMonoWorld using (ValMono; _≤ᴴ_; Ω0≤ᴴ0)
```

## §1 律 (b) 的严格版, 右边的最外一步可以是 Ω-极限

```agda
FreeTop : Ht → Set
FreeTop hz = ⊥
FreeTop (hs b) = Free b
FreeTop (hl f) = ∀ n → Free (f n)
FreeTop (hΩ κ g) = Free (g (bot S₁ κ))

≤s : ∀ {x y} → asuc x ≤ y → x ≤ y
≤s h = ≤-trans (≤-suc (≤-refl _)) h

-- 最小世界里的严格第一位置; 过 Ω-分支时坐标被界定成最小坐标
fst<⁺₀ : ∀ {a b} → a ⊲⁺[ w₀ ] b → FreeTop b → ∀ la lb → asuc (T⁺ a la) ≤ T⁺ b lb
fst<⁺₀ {b = hs b} (psuc p) fb la lb = ≤-trans (s≤ (fst₀F p fb la lb)) (SucF.grow b lb fb)
fst<⁺₀ {b = hl f} (plim n p) fb la lb = ≤-trans (s≤ (fst₀F p (fb n) la (proj₂ lb n))) (LimF.grow f lb n (upto-all f fb n))
fst<⁺₀ {b = hΩ (inj₁ tt) g} (pLim C.self p) fb la lb =
  ≤-trans (s≤ (fst₀F p fb la (proj₂ lb azero tt))) (sΩ (inj₁ tt) g lb fb (proj₂ lb azero tt))
fst<⁺₀ {b = hΩ (inj₂ tt) g} (pLim hself p) fb la lb =
  ≤-trans (s≤ (fst₀F p fb la (proj₂ lb hz tt))) (sΩ (inj₂ tt) g lb fb (proj₂ lb hz tt))

-- 接口 FstMono< 在 FreeTop 的右边上
fst<⁺ : ∀ a la b lb → FreeTop b → a ⊏ b → asuc (T⁺ a la) ≤ T⁺ b lb
fst<⁺ a la b lb fb p = fst<⁺₀ (p {w₀}) fb la lb

-- 非严格: 路径不是 hself 时化成严格
NotSelf : ∀ {a b : Ht} → a ⊲[ w₀ ] b → Set
NotSelf hself = ⊥
NotSelf _ = ⊤

toP : ∀ {a b : Ht} (p : a ⊲[ w₀ ] b) → NotSelf p → a ⊲⁺[ w₀ ] b
toP (hsuc p) _ = psuc p
toP (hlim n p) _ = plim n p
toP (hLim e p) _ = pLim e p

fstLim : ∀ a la b lb → FreeTop b → (p : a ⊲[ w₀ ] b) → NotSelf p → T⁺ a la ≤ T⁺ b lb
fstLim a la b lb fb p ns = ≤s (fst<⁺₀ (toP p ns) fb la lb)
```

## §2 `TpMonoTab` 里由此去了条件的

```agda
-- T⁺ 0 < T⁺ Ω₂ (TpPort2Om.T0<Ω₂ 的接口写法)
Ω₂-bot : FreeTop Ω₂ᴴ
Ω₂-bot = tt

T0<Ω₂′ : asuc (T⁺ hz tt) ≤ T-Ω₂
T0<Ω₂′ = fst<⁺ hz tt Ω₂ᴴ lΩ₂ tt (λ {w} → pLim (botBd S₁ κH w) hself)
```

```agda
-- cells 2 的最外是 Ω-极限, 最小坐标的分支不含 Ω-极限 (检查器计算)
ft-cells2 : FreeTop (cells 2)
ft-cells2 = tt

-- 一切世界里的第一位置 cells 1 ⊑ cells 2 在最小世界里不是 hself
ns1 : NotSelf (cells-st 1 {w₀})
ns1 = tt

-- TpMonoTab.Tab.cells≤ 1 去条件
cells≤₁ : T⁺ (cells 1) (proj₂ (Lg-idx Ω₃) 1) ≤ T⁺ (cells 2) (proj₂ (Lg-idx Ω₃) 2)
cells≤₁ = fstLim (cells 1) (proj₂ (Lg-idx Ω₃) 1) (cells 2) (proj₂ (Lg-idx Ω₃) 2) ft-cells2 (cells-st 1) ns1

-- 严格版 (TpMonoTab 里没有这一条)
cells<₁₂ : asuc (T⁺ (cells 1) (proj₂ (Lg-idx Ω₃) 1)) ≤ T⁺ (cells 2) (proj₂ (Lg-idx Ω₃) 2)
cells<₁₂ = fst<⁺₀ (toP (cells-st 1) ns1) ft-cells2 (proj₂ (Lg-idx Ω₃) 1) (proj₂ (Lg-idx Ω₃) 2)
```

## §3 按值单调的否定去了条件

`NegTpMonoWorld.no-valmono⁺` 以 `Steps T⁺` 为前提, 证明只用 `s-hΩ` 在 $Z=\mathrm{h\Omega}\,\kappa_A\,(\lambda\_.0)$ 上的一次; 那一次是 `sΩ` 的实例 ($Z$ 的最小坐标的分支是 $0$). 所以无条件: `T⁺` 对通常的值序 `_≤ᴴ_` 不单调 (它分得开值序下互相 $\le$ 的 $Z$ 与 $0$).

```agda
Z : Ht
Z = hΩ κA (λ _ → hz)

lZ : LgB Z
lZ = (λ lw e e′ p → hself) , (λ c lc → tt)

T0<Z : asuc (T⁺ hz tt) ≤ T⁺ Z lZ
T0<Z = sΩ κA (λ _ → hz) lZ tt tt

no-valmonoT⁺ : ¬ ValMono T⁺ Lg-T⁺ _≤ᴴ_
no-valmonoT⁺ m = irr (T⁺ hz tt) (≤-trans T0<Z (m Z lZ hz tt Ω0≤ᴴ0))
```

## §4 边界: 本组的 `FreeTop` 不覆盖的 (编译过的否定, 只说本组不覆盖)

`TpMonoTab` 其余条件定理的较大一边 (或 `LimF` 要的前几项) 都不满足 `FreeTop`/`Upto`. ℕ-极限的那几条已有 `TpPortTab.¬F-*`; 这里补后继与 Ω-极限的那几条.

```agda
-- Ω₂ < Ω₂ + 1: 后继的前一项是 Ω₂
¬FT-Ω₂+1 : FreeTop (hs Ω₂ᴴ) → ⊥
¬FT-Ω₂+1 ()

-- Ω₂ < Ω₂·2: mul 2 的最小坐标的分支是 mul 1 = 0 ⊞ Ω₂
¬FT-mul2 : FreeTop (mul 2) → ⊥
¬FT-mul2 ()

-- fb₂: Λs₂ 1 的最小坐标的分支是 ℕ-极限, 它的第 1 项含 Ω-极限
¬FT-fb₂1 : FreeTop (proj₁ (Λs₂ 1)) → ⊥
¬FT-fb₂1 f with f 1
... | ()

-- cells≤ 2: cells 3 不满足
¬FT-cells3 : FreeTop (cells 3) → ⊥
¬FT-cells3 ()

-- Tᵀ < Tᵀ+1: 后继的前一项 idx Ω₃ = hl cells, cells 2 含 Ω-极限
¬FT-Tᵀ+1 : FreeTop (idx (hs Ω₃)) → ⊥
¬FT-Tᵀ+1 f with f 2
... | ()
```

`LvRdVal.val-strict` 要 $T^+(\Lambda_F)<T^+(\Lambda_F\boxplus H_{\omega+1})$; 右边最外是 ℕ-极限 (`Hω1-hl`), 要 `LimF` 在第 0 项 $\Lambda_F\boxplus f(0)$ 上, 而 $\Lambda_F$ 的第 0 项 `Hn 0` 含 Ω-极限:

```agda
¬F-Hn0 : Free (Hn 0) → ⊥
¬F-Hn0 ()

free⊞ˡ : ∀ a b → Free (a ⊞ b) → Free a
free⊞ˡ a hz f = f
free⊞ˡ a (hs b) f = free⊞ˡ a b f
free⊞ˡ a (hl g) f = free⊞ˡ a (g 0) (f 0)
free⊞ˡ a (hΩ κ g) ()

¬F-ΛF : Free ΛF → ⊥
¬F-ΛF f = ¬F-Hn0 (f 0)

-- LimF 在 Λω1 的第 0 项上要的前提不成立
¬Up-Λω1 : ∀ (f : ℕ → Ht) → Free (ΛF ⊞ f 0) → ⊥
¬Up-Λω1 f fr = ¬F-ΛF (free⊞ˡ ΛF (f 0) fr)
```
