# 主线数据类型上的 View (四): 主线折叠的输出是否世界稳定

> 不含记号. 入口 [MainView](MainView.lagda.md). 主线第 1 层的 View `view₁ᴴ` ([MainViewOne](MainViewOne.lagda.md)) 以 `HWᴴ x = HW (π x)` 为合法性. 这里问: 主线折叠 `HtFeedFold` (闭项里 $S=\cdot\omega$, `HtFeedClosed.At Λ lΛ`, **一切合法的 $\Lambda$**) 在目标第 1 层 ($t=$ `hs hz`) 上的输出满足它吗? 方法照 [BrwHWFold](BrwHWFold.lagda.md): 跨世界的关系 `R2` (经 `π`), 坐标形状 `Shᴴ`, 不变量 `Good = RS Y Y × HWs Y`.
>
> **与 SumOne 版的差别 (都变简单了):**
>
> - 目标是一对 (高度 $t$, 字面世界 $m$) 加证据 (`Tg W t m`); 换世界 `cv` 只把目标的证据往回搬 (`tg↑`), **不再按 `cmpF` 分两种结果** (`cvR` 一行).
> - 读坐标的节点不只是 $\Omega_\Omega$ 回灌里的那一个 (`CvFoldInst.Kn`): 一般的定理 `HW-RKi` 对**一切**层为 `hz` 的输入节点 `ni r u` (输入层 `ly` 任意), 只要节点的分支动作 `Ai` 跨世界保持状态关系 (`HB`, `HBh`). 两种比较结果 (`keep`, `rise`) 都覆盖.
> - `Ωd` 型节点 (分支是常数 `n1`) 的 `HB` 由动作 `A₀` 的同一性质给出 (`HB-n1`); 闭项的动作 `Act` (= `Step`) 有这个性质.
>
> 闭项实例: $\Lambda=$ `hs hz` 时一步 `ΔΩ` 在目标第 1 层的整个输出 `HWᴴ` (`HW-ΔΩ₁`), 所以 `view₁ᴴ` 用在它上面 (`view-ΔΩ₁`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MainViewHW where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
import OCF.Align.HtFeedTree as F
import OCF.Align.SumOneTree as T
import OCF.Align.HtFeedClosed as HC
open import OCF.Align.BrwViewDef using (BrwView)
open import OCF.Align.BrwViewOne using (HW; Sig₁; V₁)
open import OCF.Align.BrwHWBase using (Sh; sh0; sh1; sh⨾; shl; shwL; shwR; R2; R2→WSq; R2-n0; R2-n1; R2-⨾; R2-nl; R2-ni)
open import OCF.Align.MainViewOne using (D₁; π; ι₀; HWᴴ; toBᴴ; view₁ᴴ; V)
```

## §1 主线第 0 层坐标的形状

```agda
data Shᴴ : ∀ {V V′} → F.D₀ V → F.D₀ V′ → Set where
  sh0 : ∀ {V V′} → Shᴴ (F.n0 {W = V}) (F.n0 {W = V′})
  sh1 : ∀ {V V′} → Shᴴ (F.n1 {W = V}) (F.n1 {W = V′})
  sh⨾ : ∀ {V V′} {x y : F.D₀ V} {x′ y′ : F.D₀ V′} → Shᴴ x x′ → Shᴴ y y′ → Shᴴ (x F.⨾ y) (x′ F.⨾ y′)
  shl : ∀ {V V′} {d : ℕ → F.D₀ V} {d′ : ℕ → F.D₀ V′} → (∀ n → Shᴴ (d n) (d′ n)) → Shᴴ (F.nl d) (F.nl d′)
  shwL : ∀ {V₀ V V′} {p : V₀ ⊲ V} {x : F.D₀ V₀} {x′ : F.D₀ V′} → Shᴴ x x′ → Shᴴ (F.nw p x) x′
  shwR : ∀ {V V₀′ V′} {p : V₀′ ⊲ V′} {x : F.D₀ V} {x′ : F.D₀ V₀′} → Shᴴ x x′ → Shᴴ x (F.nw p x′)

ι-Sh : ∀ {V V′} {w : T.D azero V} {w′ : T.D azero V′} → Sh w w′ → Shᴴ (ι₀ w) (ι₀ w′)
ι-Sh sh0 = sh0
ι-Sh sh1 = sh1
ι-Sh (sh⨾ a b) = sh⨾ (ι-Sh a) (ι-Sh b)
ι-Sh (shl h) = shl (λ n → ι-Sh (h n))
ι-Sh (shwL h) = shwL (ι-Sh h)
ι-Sh (shwR h) = shwR (ι-Sh h)
```

## §2 状态之间的关系, 对一切 $\Lambda$

```agda
module Main (Λ : F.H) (lΛ : F.LgH Λ) where
  open HC.At Λ lΛ public

  T1 : A → A → Set
  T1 W m = Tg W (F.hs F.hz) m

  record ΔR {W W′} (Δ : Df W) (Δ′ : Df W′) : Set where
    constructor δr
    field rr : ∀ {m m′} (τ : T1 W m) (τ′ : T1 W′ m′) → R2 (π (yc Δ τ)) (π (yc Δ′ τ′))
  open ΔR public

  record RS {W W′} (Z : St W) (Z′ : St W′) : Set where
    constructor sr
    field rs : ∀ {m m′} (τ : T1 W m) (τ′ : T1 W′ m′) → R2 (π (yc (d Z) τ)) (π (yc (d Z′) τ′))
  open RS public

  ΔR-0 : ∀ {W W′} → ΔR (zeroD {W}) (zeroD {W′})
  ΔR-0 = δr (λ τ τ′ → R2-n0)

  -- ⊕ 的世界合法性只进第 0 层的和, 所以显式传
  ⊕R : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) {Z : St W} {Z′ : St W′} {Δ : Df W} {Δ′ : Df W′} →
       RS Z Z′ → ΔR Δ Δ′ → RS (Z ⊕⟨ lW ⟩ Δ) (Z′ ⊕⟨ lW′ ⟩ Δ′)
  ⊕R lW lW′ h k = sr (λ τ τ′ → R2-⨾ (rs h τ τ′) (rr k τ τ′))

  StepR : ∀ {W W′} {Z : St W} {Z′ : St W′} → RS Z Z′ → ΔR (Step Z) (Step Z′)
  StepR h = δr (λ τ τ′ → R2-nl (λ _ → R2-⨾ (R2-⨾ R2-n1 (R2-ni (λ _ _ _ → T.n1) (λ _ _ _ → T.n1) (λ r r′ l l′ sh → R2-n1))) (rs h τ τ′)))

  -- 换世界: 目标的证据往回搬, 一行
  cvR : ∀ {W W′ V V′} (q : W ⊲ V) (q′ : W′ ⊲ V′) {Y : St W} {Y′ : St W′} → RS Y Y′ → RS (cv q Y) (cv q′ Y′)
  cvR q q′ h = sr (λ τ τ′ → rs h (tg↑ q τ) (tg↑ q′ τ′))
```

## §3 跨世界的模拟: 沿第 0 层坐标折叠

```agda
  module RunSim {W W′} (lW : Lg W) (lW′ : Lg W′) (ll : LW F.hz W) (ll′ : LW F.hz W′)
                (A₀ : Ig F.hz W) (A₀′ : Ig F.hz W′)
                (hA : ∀ w w′ (Z : St W) (Z′ : St W′) → RS Z Z′ → ΔR (A₀ C.self lW w Z) (A₀′ C.self lW′ w′ Z′)) where
    RunR : ∀ {W₀ W₀′} (ac ac′ : F.AccY F.hz) {z : F.D₀ W₀} {z′ : F.D₀ W₀′} → Shᴴ z z′ →
           (q : W₀ ⊲ W) (q′ : W₀′ ⊲ W′) → ∀ w w′ Z Z′ → RS Z Z′ →
           ΔR (Run ac z q lW ll A₀ w Z) (Run ac′ z′ q′ lW′ ll′ A₀′ w′ Z′)
    RptR : ∀ {W₀ W₀′} (ac ac′ : F.AccY F.hz) {d : ℕ → F.D₀ W₀} {d′ : ℕ → F.D₀ W₀′} → (∀ n → Shᴴ (d n) (d′ n)) →
           (q : W₀ ⊲ W) (q′ : W₀′ ⊲ W′) → ∀ w w′ Z Z′ → RS Z Z′ →
           ∀ n → RS (proj₂ (Rpt ac d q lW ll A₀ w Z n)) (proj₂ (Rpt ac′ d′ q′ lW′ ll′ A₀′ w′ Z′ n))
    RunR ac ac′ sh0 q q′ w w′ Z Z′ h = ΔR-0
    RunR ac ac′ sh1 q q′ w w′ Z Z′ h = hA w w′ Z Z′ h
    RunR ac ac′ (sh⨾ hx hy) q q′ w w′ Z Z′ h = δr (λ τ τ′ →
      R2-⨾ (rr (RunR ac ac′ hx q q′ w w′ Z Z′ h) τ τ′)
           (rr (RunR ac ac′ hy q q′ _ _ _ _ (⊕R lW lW′ h (RunR ac ac′ hx q q′ w w′ Z Z′ h))) τ τ′))
    RunR ac ac′ (shl hd) q q′ w w′ Z Z′ h = δr (λ τ τ′ →
      R2-nl (λ n → rr (RunR ac ac′ (hd n) q q′ _ _ _ _ (RptR ac ac′ hd q q′ w w′ Z Z′ h n)) τ τ′))
    RunR ac ac′ (shwL {p = p} hs) q q′ w w′ Z Z′ h = RunR ac ac′ hs (⊲-tr p q) q′ w w′ Z Z′ h
    RunR ac ac′ (shwR {p = p} hs) q q′ w w′ Z Z′ h = RunR ac ac′ hs q (⊲-tr p q′) w w′ Z Z′ h
    RptR ac ac′ hd q q′ w w′ Z Z′ h zero = h
    RptR ac ac′ hd q q′ w w′ Z Z′ h (suc n) =
      ⊕R lW lW′ (RptR ac ac′ hd q q′ w w′ Z Z′ h n) (RunR ac ac′ (hd n) q q′ _ _ _ _ (RptR ac ac′ hd q q′ w w′ Z Z′ h n))
  open RunSim public
```

## §4 `HW` 那一半

```agda
  record HWd {W} (Δ : Df W) : Set where
    constructor hd
    field hd′ : ∀ {m} (τ : T1 W m) → HWᴴ (yc Δ τ)
  open HWd public

  record HWs {W} (Y : St W) : Set where
    constructor hs
    field hs′ : ∀ {m} (τ : T1 W m) → HWᴴ (yc (d Y) τ)
  open HWs public

  HW-⊕ : ∀ {W} (lW : Lg W) {Y : St W} {Δ : Df W} → HWs Y → HWd Δ → HWs (Y ⊕⟨ lW ⟩ Δ)
  HW-⊕ lW g h = hs (λ τ → hs′ g τ , hd′ h τ)

  HW-Step : ∀ {W} {Y : St W} → HWs Y → HWd (Step Y)
  HW-Step g = hd (λ τ → λ _ → (tt , ((λ p l w → tt) , R2→WSq (R2-ni (λ _ _ _ → T.n1) (λ _ _ _ → T.n1) (λ r r′ l l′ sh → R2-n1)))) , hs′ g τ)

  HW-cv : ∀ {W V} (q : W ⊲ V) {Y : St W} → HWs Y → HWs (cv q Y)
  HW-cv q g = hs (λ τ → hs′ g (tg↑ q τ))

  module RunHW {W} (lW : Lg W) (ll : LW F.hz W) (A₀ : Ig F.hz W) (hA : ∀ w (Z : St W) → HWs Z → HWd (A₀ C.self lW w Z)) where
    HW-Run : ∀ {W₀} (ac : F.AccY F.hz) (z : F.D₀ W₀) (q : W₀ ⊲ W) → ∀ w Z → HWs Z → HWd (Run ac z q lW ll A₀ w Z)
    HW-Rpt : ∀ {W₀} (ac : F.AccY F.hz) (d : ℕ → F.D₀ W₀) (q : W₀ ⊲ W) → ∀ w Z → HWs Z →
             ∀ n → HWs (proj₂ (Rpt ac d q lW ll A₀ w Z n))
    HW-Run ac F.n0 q w Z g = hd (λ τ → tt)
    HW-Run ac F.n1 q w Z g = hA w Z g
    HW-Run ac (x F.⨾ y) q w Z g = hd (λ τ → hd′ (HW-Run ac x q w Z g) τ , hd′ (HW-Run ac y q _ _ (HW-⊕ lW g (HW-Run ac x q w Z g))) τ)
    HW-Run ac (F.nl dd) q w Z g = hd (λ τ → λ n → hd′ (HW-Run ac (dd n) q _ _ (HW-Rpt ac dd q w Z g n)) τ)
    HW-Run ac (F.ni () u) q w Z g
    HW-Run ac (F.nκ () u) q w Z g
    HW-Run ac (F.nw p x) q w Z g = HW-Run ac x (⊲-tr p q) w Z g
    HW-Rpt ac dd q w Z g zero = g
    HW-Rpt ac dd q w Z g (suc n) = HW-⊕ lW (HW-Rpt ac dd q w Z g n) (HW-Run ac (dd n) q _ _ (HW-Rpt ac dd q w Z g n))
  open RunHW public

  Good : ∀ {W} → St W → Set
  Good Y = RS Y Y × HWs Y
```

## §5 层为 `hz` 的输入节点在目标第 1 层的输出

输入节点 `ni r u` 在输入层 `ly` 里, 层是 `hz` (`r : StH W₀ hz ly`). 折叠在目标 $t=$ `hs hz` 上比较 (`rkT`), 结果 `keep` 时输出一个读坐标的 `ni` 节点 (分支 `BNi`: 在 $z$ 上沿第 0 层坐标跑 `Ai`, 再跑一次 `Ai`); `rise` 时输出沿第 0 层的链. 条件 `HB`: 分支动作 `A² = Ai …` 在一切世界之间保持状态关系 (坐标任意); `HBh`: 它保持 `HWs`.

```agda
  module Node {ly W₀ W} (ac : F.AccY ly) (ac′ : F.AccY F.hz) (r : F.StH W₀ F.hz ly)
              (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → F.Vs ly r W′ → F.D ly W′) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W)
              (A₀ : Ig ly W) (w : F.D ly W) where
    hk : LW F.hz W
    hk = kk r q₀ ll

    A² : Ig F.hz W
    A² = Ai ac ac′ r u q₀ hk ll A₀ w

    module _ (HB : ∀ {V V′} (p : W ⊲ V) (p′ : W ⊲ V′) (l : Lg V) (l′ : Lg V′) z z′ (Z : St V) (Z′ : St V′) → RS Z Z′ → ΔR (A² p l z Z) (A² p′ l′ z′ Z′))
             (HBh : ∀ {V} (p : W ⊲ V) (l : Lg V) z (Z : St V) → HWs Z → HWd (A² p l z Z))
             (Y : St W) (gY : Good Y) where
      module Br {m} (T : T1 W m) where
        br : ∀ {W′} → m ⊲ W′ → Lg W′ → F.D₀ W′ → D₁ W′
        br p l y = yc (BNi ac ac′ r u q₀ ll A₀ w Y hk (⊲-tr (wm T) p) l y) (tg C.self (F.⊲ᴴ↑ p (tm T)) l)

        UI-br : ∀ {V V′} (s : m ⊲ V) (s′ : m ⊲ V′) (l : Lg V) (l′ : Lg V′) {y : T.D azero V} {y′ : T.D azero V′} → Sh y y′ →
                R2 (π (br s l (ι₀ y))) (π (br s′ l′ (ι₀ y′)))
        UI-br s s′ l l′ {y} {y′} sh =
          rr (HB P P′ l l′ (ι₀ y) (ι₀ y′) _ _
                 (⊕R l l′ (cvR P P′ (proj₁ gY))
                     (RunR l l′ (F.⊲ᴴ↑ P hk) (F.⊲ᴴ↑ P′ hk) (Ig↾ P A²) (Ig↾ P′ A²) (λ v v′ Z Z′ h → HB P P′ l l′ v v′ Z Z′ h)
                           ac′ ac′ (ι-Sh sh) C.self C.self n0′ n0′ _ _ (cvR P P′ (proj₁ gY)))))
             (tg C.self (F.⊲ᴴ↑ s (tm T)) l) (tg C.self (F.⊲ᴴ↑ s′ (tm T)) l′)
          where
          P = ⊲-tr (wm T) s
          P′ = ⊲-tr (wm T) s′
          n0′ : ∀ {V} → F.D₀ V
          n0′ = F.n0

        HW-br : ∀ {W′} (s : m ⊲ W′) (l : Lg W′) y → HWᴴ (br s l (ι₀ y))
        HW-br s l y =
          hd′ (HBh P l (ι₀ y) _ (HW-⊕ l (HW-cv P (proj₂ gY))
                (HW-Run l (F.⊲ᴴ↑ P hk) (Ig↾ P A²) (λ v Z g → HBh P l v Z g) ac′ (ι₀ y) C.self F.n0 _ (HW-cv P (proj₂ gY)))))
              (tg C.self (F.⊲ᴴ↑ s (tm T)) l)
          where P = ⊲-tr (wm T) s

        keep-R2 : R2 (π (RKi ac ac′ r u q₀ lW ll A₀ w Y T (keep (F.ss F.hself)))) (π (RKi ac ac′ r u q₀ lW ll A₀ w Y T (keep (F.ss F.hself))))
        keep-R2 = R2-ni (λ p l y → π (br p l (ι₀ y))) (λ p l y → π (br p l (ι₀ y))) UI-br

        keep-HW : HWᴴ (RKi ac ac′ r u q₀ lW ll A₀ w Y T (keep (F.ss F.hself)))
        keep-HW = (λ p l y → HW-br p l y) , R2→WSq keep-R2

        chain-HW : ∀ n → HWs (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)))
        chain-HW zero = proj₂ gY
        chain-HW (suc n) =
          HW-⊕ lW (chain-HW n) (HW-Run lW hk A² (λ v Z g → HBh C.self lW v Z g) ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) C.self _ _ (chain-HW n))

        rise-HW : HWᴴ (RKi ac ac′ r u q₀ lW ll A₀ w Y T rise)
        rise-HW n = hd′ (HW-Run lW hk A² (λ v Z g → HBh C.self lW v Z g) ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) C.self _ _ (chain-HW n)) T

        HW-RKi : ∀ (ρ : Rk F.hz (F.hs F.hz) m) → HWᴴ (RKi ac ac′ r u q₀ lW ll A₀ w Y T ρ)
        HW-RKi (keep (F.ss F.hself)) = keep-HW
        HW-RKi rise = rise-HW

      HW-RunNi : HWd (RunNi ac ac′ r u q₀ lW ll A₀ w Y)
      HW-RunNi = hd (λ T → Br.HW-RKi T _)
```

## §6 `Ωd` 型节点

分支是常数 `n1` 时, `A² p l z Z` 就是 `A₀ p l (…) Z` (定义相等), `HB` 化成动作 `A₀` 在一切世界之间保持状态关系.

```agda
  module N1 {ly W₀ W} (ac : F.AccY ly) (ac′ : F.AccY F.hz) (r : F.StH W₀ F.hz ly) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W)
            (A₀ : Ig ly W) (w : F.D ly W)
            (hA : ∀ {V V′} (p : W ⊲ V) (p′ : W ⊲ V′) (l : Lg V) (l′ : Lg V′) v v′ (Z : St V) (Z′ : St V′) → RS Z Z′ → ΔR (A₀ p l v Z) (A₀ p′ l′ v′ Z′))
            (hAh : ∀ {V} (p : W ⊲ V) (l : Lg V) v (Z : St V) → HWs Z → HWd (A₀ p l v Z)) where
    u₁ : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → F.Vs ly r W′ → F.D ly W′
    u₁ _ _ _ = F.n1

    open Node ac ac′ r u₁ q₀ lW ll A₀ w

    HB-n1 : ∀ {V V′} (p : W ⊲ V) (p′ : W ⊲ V′) (l : Lg V) (l′ : Lg V′) z z′ (Z : St V) (Z′ : St V′) → RS Z Z′ → ΔR (A² p l z Z) (A² p′ l′ z′ Z′)
    HB-n1 p p′ l l′ z z′ Z Z′ h = hA p p′ l l′ _ _ Z Z′ h

    HBh-n1 : ∀ {V} (p : W ⊲ V) (l : Lg V) z (Z : St V) → HWs Z → HWd (A² p l z Z)
    HBh-n1 p l z Z g = hAh p l _ Z g

    HW-RunNi₁ : ∀ (Y : St W) → Good Y → HWd (RunNi ac ac′ r u₁ q₀ lW ll A₀ w Y)
    HW-RunNi₁ Y gY = HW-RunNi HB-n1 HBh-n1 Y gY

  -- 闭项的动作
  hA-Act : ∀ {ly W V V′} (p : W ⊲ V) (p′ : W ⊲ V′) (l : Lg V) (l′ : Lg V′) (v : F.D ly V) (v′ : F.D ly V′) (Z : St V) (Z′ : St V′) →
           RS Z Z′ → ΔR (Act {ly} p l v Z) (Act {ly} p′ l′ v′ Z′)
  hA-Act p p′ l l′ v v′ Z Z′ h = StepR h

  hAh-Act : ∀ {ly W V} (p : W ⊲ V) (l : Lg V) (v : F.D ly V) (Z : St V) → HWs Z → HWd (Act {ly} p l v Z)
  hAh-Act p l v Z g = HW-Step g

  Good-Y₀ : ∀ {W} → Good (Y₀ {W})
  Good-Y₀ = sr (λ τ τ′ → R2-n0) , hs (λ τ → tt)

  Good-⊕Step : ∀ {W} (lW : Lg W) {Y : St W} → Good Y → Good (Y ⊕⟨ lW ⟩ Step Y)
  Good-⊕Step lW (h , g) = ⊕R lW lW h (StepR h) , HW-⊕ lW g (HW-Step g)
```

## §7 闭项实例: $\Lambda=$ `hs hz`

$\Omega_\Lambda$ 的差树是 $1⨾\sum_z 1$, 唯一的节点层是 `hz`. 一步 `ΔΩ` 在目标第 1 层的输出是 `Step Y₀ ⨾ (这个节点的输出)`, 两段都 `HWᴴ`.

```agda
module One = Main (F.hs F.hz) tt

HW-ΔΩ₁ : ∀ {m} (τ : One.T1 (asuc azero) m) → HWᴴ (One.yc One.ΔΩ τ)
HW-ΔΩ₁ τ =
  One.hd′ (One.HW-Step (proj₂ (One.Good-Y₀ {asuc azero}))) τ ,
  One.hd′ (One.N1.HW-RunNi₁ F.accᴸ (F.accK (F.ss F.hself)) (F.ss F.hself) (z⊲ (asuc azero)) tt F.hself One.Act
             (F.n0 F.⨾ F.nw (z⊲ (asuc azero)) F.n1) One.hA-Act One.hAh-Act _ (One.Good-⊕Step tt One.Good-Y₀)) τ

view-ΔΩ₁ : ∀ {m} (τ : One.T1 (asuc azero) m) → V (m , One.lm τ) (toBᴴ (One.lm τ) (One.yc One.ΔΩ τ))
view-ΔΩ₁ {m} τ = BrwView.view view₁ᴴ {m , One.lm τ} (One.yc One.ΔΩ τ) (HW-ΔΩ₁ τ)
```
