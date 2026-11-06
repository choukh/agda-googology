# Ω-极限高度 (六): 回灌的每一格换到一个世界里重做

> 入口 [MonoPort9](MonoPort9.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 实例 $\Lambda=\mathrm{h\Omega}\,g$, 分支都不含 Ω-极限 (`fg`). 闭项 $T_\Lambda$ 的回灌第 $n$ 格 $\Delta_n$ 在世界 $V_n$ 里沿 `Walk` 走, 起始状态 $S_n$; $S_{n+1}=\mathrm{cv}\,q_n\,(S_n\oplus\Delta_n)$ 把第 $n$ 格的输出搬进更大的世界 $V_{n+1}$. `MonoPort8` §3 的障碍是: 单世界关系 `Good` 只说 $\Delta_n$ 在世界 $V_n$ 的目标上的读数, 第 $n+1$ 格要的是它在 $V_{n+1}$ 的目标上的读数 (`GoodUp`).
>
> 本文不证 `GoodUp`, 而是绕开它: 把**全部**格放到**同一个**世界 $V_\omega=\lim_n V_n$ 里重做 (`Z`, `Δ′`: 同样的坐标路径, 同样的节点 $u$, 动作 `Act`, 世界 $V_\omega$, 格与格之间没有 `cv`), 再用 [MonoPort9Two](MonoPort9Two.lagda.md) 的两世界互模拟 (只比不含 Ω-极限的目标) 证明:
>
> - `ZE`: 实际第 $n$ 格的起始状态 $S_n$ (世界 $V_n$) 与重做的 $Z_n$ (世界 $V_\omega$) 在一切目标对上读数互模拟;
> - `cellE`: 实际第 $n$ 格的输出 $\Delta_n$ 与重做的 $\Delta'_n$ 在一切目标对上读数互模拟, 特别是在第 0 层上和相等 (`cell≈`).
>
> 重做的一边全在一个世界里, 自洽由单世界的 `nodeSelf` 给出 ([MonoPort9Cell](MonoPort9Cell.lagda.md)). 新的引理: `frkΩ` (节点层不含 Ω-极限), `CutE`, `Walk-E`/`WRp-E` (两个世界里同一条坐标路径上的 `Walk`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort9Walk where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (module At; one)
open import OCF.Align.HtCrossVSim using (Free; free⊲)
open import OCF.Align.MonoPort8Sim using (SimE; e0; e1; e⨾; el; ei; ew; Re; sumE; symE0)
open import OCF.Align.MonoPort8Om using (module Om)
open import OCF.Align.MonoPort9Two using (module TwoF)
```

## 1 节点层不含 Ω-极限

```agda
frkΩ : ∀ (g : A → H) → (∀ c → Free (g c)) → ∀ {W₀ W k ly} → StH W₀ k ly → ly ⊲[ W ] hΩ g → Free k
frkΩ g fg (sL e P) hself = free⊲ P (fg _)
frkΩ g fg r (hLim e p) = free⊲ (S→⊲ᴴ r) (free⊲ p (fg _))
```

## 2 两个世界里的同一次 `Walk`

```agda
module WE (g : A → H) (l : LgH (hΩ g)) (fg : ∀ c → Free (g c)) where
  open Om g l using (Λ; u; w₁; Y₁; κ)
  module P = At Λ l
  open TwoF Λ l Λ l (frkΩ g fg) public

  uE : ∀ {c} (x : azero ⊲ c) (lc : Lg c) → Re Λ (u x lc) (u x lc)
  uE x lc = ei (λ _ _ _ _ _ _ _ → e1)

  CutE : ∀ {V₁ V₂} b {a} (p : a ⊲ b) (ab : azero ⊲ a) (lb : Lg b) (bW₁ : b ⊲ V₁) (bW₂ : b ⊲ V₂) →
         Re Λ (Cut u b p ab lb bW₁) (Cut u b p ab lb bW₂)
  CutE b C.self ab lb bW₁ bW₂ = e0
  CutE (asuc c) (C.suc p) ab lb bW₁ bW₂ = e⨾ (CutE c p ab lb _ _) (ew (uE (⊲-tr ab p) lb))
  CutE (alim f) (C.lim n p) ab (st , w) bW₁ bW₂ =
    e⨾ (CutE (f n) p ab (w n) _ _) (el (λ m → CutE (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (w (suc (m + n))) _ _))

  ActE : ∀ {W₁ W₂ U₁ U₂} (p₁ : W₁ ⊲ U₁) (p₂ : W₂ ⊲ U₂) → IgE {Λ} (P.Ig↾ p₁ P.Act) (P.Ig↾ p₂ P.Act)
  ActE p₁ p₂ = ige (λ p p′ lV lV′ hw hY → StepE hY)

  Walk-E : ∀ {V₁ V₂} b {a} (p : a ⊲ b) (ap : azero ⊲ a) (lb : Lg b) (bV₁ : b ⊲ V₁) (bV₂ : b ⊲ V₂) (lV₁ : Lg V₁) (lV₂ : Lg V₂)
           (ll₁ : Λ ⊲[ V₁ ] Λ) (ll₂ : Λ ⊲[ V₂ ] Λ) {A₁ : F₁.Ig Λ V₁} {A₂ : F₂.Ig Λ V₂} → IgE A₁ A₂ →
           {co₁ : D Λ V₁} {co₂ : D Λ V₂} → Re Λ co₁ co₂ → {Y₁ : F₁.St V₁} {Y₂ : F₂.St V₂} → StE Y₁ Y₂ →
           DfE (F₁.Walk accᴸ u b p ap lb bV₁ lV₁ ll₁ A₁ co₁ Y₁) (F₂.Walk accᴸ u b p ap lb bV₂ lV₂ ll₂ A₂ co₂ Y₂)
  WRp-E  : ∀ {V₁ V₂} (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} (p : a ⊲ f n) (ap : azero ⊲ a)
           (fV₁ : ∀ m → f m ⊲ V₁) (fV₂ : ∀ m → f m ⊲ V₂) (lV₁ : Lg V₁) (lV₂ : Lg V₂)
           (ll₁ : Λ ⊲[ V₁ ] Λ) (ll₂ : Λ ⊲[ V₂ ] Λ) {A₁ : F₁.Ig Λ V₁} {A₂ : F₂.Ig Λ V₂} → IgE A₁ A₂ →
           {co₁ : D Λ V₁} {co₂ : D Λ V₂} → Re Λ co₁ co₂ → {Y₁ : F₁.St V₁} {Y₂ : F₂.St V₂} → StE Y₁ Y₂ → ∀ m →
           Re Λ (proj₁ (F₁.WRp accᴸ u f stp wl p ap fV₁ lV₁ ll₁ A₁ co₁ Y₁ m)) (proj₁ (F₂.WRp accᴸ u f stp wl p ap fV₂ lV₂ ll₂ A₂ co₂ Y₂ m)) ×
           StE (proj₂ (F₁.WRp accᴸ u f stp wl p ap fV₁ lV₁ ll₁ A₁ co₁ Y₁ m)) (proj₂ (F₂.WRp accᴸ u f stp wl p ap fV₂ lV₂ ll₂ A₂ co₂ Y₂ m))

  Walk-E b C.self ap lb bV₁ bV₂ lV₁ lV₂ ll₁ ll₂ hA hco hY = zeroE
  Walk-E (asuc c) (C.suc p) ap lb bV₁ bV₂ lV₁ lV₂ ll₁ ll₂ hA hco hY =
    ⨾E ih (Run-E accᴸ accᴸ (uE (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bV₁) (⊲-tr (C.suc C.self) bV₂) lV₁ lV₂ ll₁ ll₂ hA
             (e⨾ hco (CutE c p ap lb (⊲-tr (C.suc C.self) bV₁) (⊲-tr (C.suc C.self) bV₂))) (⊕E lV₁ lV₂ hY ih))
    where
    ih = Walk-E c p ap lb (⊲-tr (C.suc C.self) bV₁) (⊲-tr (C.suc C.self) bV₂) lV₁ lV₂ ll₁ ll₂ hA hco hY
  Walk-E (alim f) (C.lim n p) ap (stp , wl) bV₁ bV₂ lV₁ lV₂ ll₁ ll₂ hA hco hY =
    ⨾E ih (nlE (λ m → Walk-E (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n)))
                         (⊲-tr (C.lim (suc (m + n)) C.self) bV₁) (⊲-tr (C.lim (suc (m + n)) C.self) bV₂) lV₁ lV₂ ll₁ ll₂ hA
                         (proj₁ (rp m)) (proj₂ (rp m))))
    where
    ih = Walk-E (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV₁) (⊲-tr (C.lim n C.self) bV₂) lV₁ lV₂ ll₁ ll₂ hA hco hY
    rp = WRp-E f stp wl p ap (λ m₁ → ⊲-tr (C.lim m₁ C.self) bV₁) (λ m₁ → ⊲-tr (C.lim m₁ C.self) bV₂) lV₁ lV₂ ll₁ ll₂ hA
           (e⨾ hco (CutE (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV₁) (⊲-tr (C.lim n C.self) bV₂))) (⊕E lV₁ lV₂ hY ih)

  WRp-E f stp wl p ap fV₁ fV₂ lV₁ lV₂ ll₁ ll₂ hA hco hY zero = hco , hY
  WRp-E f stp wl {n = n} p ap fV₁ fV₂ lV₁ lV₂ ll₁ ll₂ hA hco hY (suc m) =
    e⨾ (proj₁ ih) (CutE (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV₁ (suc (m + n))) (fV₂ (suc (m + n)))) ,
    ⊕E lV₁ lV₂ (proj₂ ih)
      (Walk-E (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV₁ (suc (m + n))) (fV₂ (suc (m + n)))
              lV₁ lV₂ ll₁ ll₂ hA (proj₁ ih) (proj₂ ih))
    where
    ih = WRp-E f stp wl p ap fV₁ fV₂ lV₁ lV₂ ll₁ ll₂ hA hco hY m
```

## 3 全部格在世界 $V_\omega$ 里重做

$V_\omega=\lim_n V_n$ 是合法的世界: 相邻项 $V_n\lhd V_{n+1}$ 就是第 $n+1$ 格的 `av` (`κc` 的字面, `sum-fst`).

```agda
  Vn : ℕ → A
  Vn n = P.v (κ n)

  Vω : A
  Vω = alim Vn

  lω : Lg Vω
  lω = (λ n → P.av (κ (suc n))) , (λ n → P.lv (κ n))

  X : ∀ n → Vn n ⊲ Vω
  X n = C.lim n C.self

  X₁ : one ⊲ Vω
  X₁ = ⊲-tr (P.wv (κ 0)) (X 0)

  -- 重做的上下文: 与实际的上下文同形, 只换最外的 nw
  co′ : ℕ → D Λ Vω
  co′ zero = nw X₁ w₁
  co′ (suc n) = nw (X n) (P.co (κ n) ⨾ Cut u (Vn n) (P.av (κ n)) (P.ap (κ n)) (P.lv (κ n)) C.self)

  Z  : ℕ → P.St Vω
  Δ′ : ℕ → P.Df Vω
  Z zero = P.cv X₁ Y₁
  Z (suc n) = P._⊕⟨_⟩_ (Z n) lω (Δ′ n)
  Δ′ n = P.Walk accᴸ u (Vn n) (P.av (κ n)) (P.ap (κ n)) (P.lv (κ n)) (X n) lω hself P.Act (co′ n) (Z n)

  -- 实际的第 n 格
  Δ : ∀ n → P.Df (Vn n)
  Δ n = P.κΔ accᴸ u hself P.Act (κ n)
```

**互模拟.** 上下文: 实际与重做只差最外的 `nw` 的路径 (`ew`), 里面同一棵树与自己相关 (`coR`). 状态: 对 $n$ 归纳, `cv` 只是把读数的目标路径接长 (`cvL`).

```agda
  w₁R : Re Λ w₁ w₁
  w₁R = e⨾ e0 (ew e1)

  coR : ∀ n → Re Λ (P.co (κ n)) (P.co (κ n))
  coR zero = ew w₁R
  coR (suc n) = ew (e⨾ (coR n) (CutE (Vn n) (P.av (κ n)) (P.ap (κ n)) (P.lv (κ n)) C.self C.self))

  coE : ∀ n → Re Λ (P.co (κ n)) (co′ n)
  coE zero = ew w₁R
  coE (suc n) = ew (e⨾ (coR n) (CutE (Vn n) (P.av (κ n)) (P.ap (κ n)) (P.lv (κ n)) C.self C.self))

  cvL : ∀ {W W′ U} (q : W ⊲ U) {Y : F₁.St W} {Y′ : F₂.St W′} → StE Y Y′ → StE (F₁.cv q Y) Y′
  cvL q h = ste (dfe (λ ft wm wm′ tm₁ tm₂ lm lm′ → at (dE h) ft (⊲-tr q wm) wm′ tm₁ tm₂ lm lm′))

  Y₀E : ∀ {W W′} → StE (P.Y₀ {W}) (P.Y₀ {W′})
  Y₀E = ste zeroE

  Y₁E : StE Y₁ Y₁
  Y₁E = ⊕E tt tt Y₀E (StepE Y₀E)

  ZE    : ∀ n → StE (P.Sv (κ n)) (Z n)
  cellE : ∀ n → DfE (Δ n) (Δ′ n)
  ZE zero = cvE (P.wv (κ 0)) X₁ Y₁E
  ZE (suc n) = cvL (P.av (κ (suc n))) (⊕E (P.lv (κ n)) lω (ZE n) (cellE n))
  cellE n = Walk-E (Vn n) (P.av (κ n)) (P.ap (κ n)) (P.lv (κ n)) C.self (X n) (P.lv (κ n)) lω (⊲ᴴ↑ (P.wv (κ n)) hself) hself
              (ActE (P.wv (κ n)) C.self) (coE n) (ZE n)

  -- 第 0 层: 实际格与重做格的和相等
  cell≈ : ∀ n β → sum β (P.yc (Δ′ n) (P.τ₀ lω)) ≤ sum β (P.yc (Δ n) (P.τ₀ (P.lv (κ n))))
  cell≈ n β = sumE accᴸ (symE0 accᴸ (at (cellE n) tt C.self C.self (z⊲ᴴ Λ) (z⊲ᴴ Λ) (P.lv (κ n)) lω)) (≤-refl β)
```
