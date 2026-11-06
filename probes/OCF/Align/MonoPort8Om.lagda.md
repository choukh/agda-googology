# Ω-极限高度 (二): 回灌第一格的第一个节点

> 入口 [MonoPort8](MonoPort8.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 实例 $\Lambda=\mathrm{h\Omega}\,g$ 任意 (合法). $\Omega_\Lambda = 1 ⨾ \mathrm{nκ}\,(c\mapsto \mathrm{ni}\,(\mathrm{sL}_c\,\mathrm{self}\,\mathrm{hself})\,(\lambda\_\to 1))$. 闭项 $T_\Lambda$ 的第 0 层读数是 `Step` 的一段加回灌 `RKy … hz` 的极限 $\lim_n \mathrm{drp}(\Delta_n)$ (`TΛ≡`, 定义性的). 第 $0$ 格 $\Delta_0$ 在世界 $V_0=\mathrm{sum}\,1\,(z\,Y_1)$ (`κ 0`) 里沿 `Walk` 走; 它的第一个节点在坐标 $0$, 层 $g(0)$ (`N0`); 第二个节点在坐标 $1$ (非零, 给出严格).
>
> 证明分四步, 只有第一步跨世界:
>
> 1. **换世界、换实例** (`MonoPort8Sim.changeW`): $T_{g(0)}$ (实例 $g(0)$, 世界 $1$) 与 $\Omega_{g(0)}$ 在实例 $\Lambda$ 的世界 $V_0$ 里、节点 `N0` 的位置 `kk₀` 上折叠的和相等. 要 $g(0)$ 不含 Ω-极限.
> 2. **同一世界 $V_0$ 里比两次 $\Omega_{g(0)}$ 的折叠** (`MonoPort7Node.ΩdObs`): 左边从 $Y_0$, 动作 `Act`; 右边是 `N0` 上升时链的第 $0$ 项里那一次 $\Omega_{g(0)}$ (动作 `A²`, 状态 `Y′`). 世界、嵌入、良基证明的写法两边不同, `ΩdObs` 本来就允许.
> 3. **读数的前缀** (`pfx`): 链的第 $0$ 项是状态在层 $g(0)$ 上的读数 $(0 ⨾ \omega\cdot(\Omega_{g(0)} ⨾ 0)) ⨾ 0$ 的折叠, 它的和不低于其中第一次 $\Omega_{g(0)}$ 的和; 节点上升的输出 $\lim_n$ 不低于第 $0$ 项.
> 4. **严格**: 第 $0$ 格里坐标 $1$ 的节点在第 0 层非零 (`HtFeedGrow.G.L2`), 所以 $T_\Lambda$ 严格高于第一个节点的和.
>
> 结论 `growΩ₀`: $g(0)$ 不含 Ω-极限 ⇒ $T_{g(0)} < T_{\mathrm{h\Omega}\,g}$. 特例 `growΩᴴ₀`: $T_0 < T_{\Omega}$ (无前提).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort8Om where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (module At; TΛ; one)
open import OCF.Align.HtFeedGrow using (nz≤; sum≥; nzR; module G)
open import OCF.Align.HtFeedHt using (emb; Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtCrossVSim using (Free)
open import OCF.Align.MonoPort8Sim using (changeW; TΛ-at)
import OCF.Align.MonoPort7Rel as Rl
import OCF.Align.MonoPort7Node as Nd
```

## 1 小件

```agda
-- drp 不降和
drp≤ : ∀ {W W′} {b b′} → b ≤ b′ → (x : D₀ W) → sum b x ≤ sum b′ (drp {W} {W′} x)
pdrp : ∀ {W W′} {b b′} → b ≤ b′ → (d : ℕ → D₀ W) → ∀ n → pt b d n ≤ pt b′ (λ m → drp {W} {W′} (d m)) n
drp≤ h n0 = h
drp≤ h n1 = s≤ h
drp≤ h (x ⨾ y) = drp≤ (drp≤ h x) y
drp≤ h (nl d) = l≤ (λ n → ≤l n (pdrp h d n))
drp≤ h (ni () u)
drp≤ h (nκ () u)
drp≤ h (nw p x) = drp≤ h x
pdrp h d zero = h
pdrp h d (suc n) = drp≤ (pdrp h d n) (d n)

```

## 2 实例与闭项的展开

`TΛ≡` 是定义性的: 闭项的第 0 层读数 $= 1 ⨾ (\mathrm{Step}\,Y_0 ⨾ \lim_n \mathrm{drp}\,\Delta_n)$.

```agda
module Om (g : A → H) (l : LgH (hΩ g)) where
  Λ : H
  Λ = hΩ g
  module P = At Λ l
  module GG = G Λ l

  rk0 : ∀ {k m} (x : P.Rk k hz m) → x ≡ P.rise
  rk0 (P.keep ())
  rk0 P.rise = refl

  u : ∀ {c} → azero ⊲ c → Lg c → D Λ c
  u {c} _ _ = ni (sL {c = c} C.self hself) (λ _ _ _ → n1)

  w₁ : D Λ one
  w₁ = n0 ⨾ nw (z⊲ one) n1

  Y₁ : P.St one
  Y₁ = P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀)

  κ : ℕ → P.Cl one azero Λ
  κ = P.κc accᴸ u (z⊲ one) tt hself P.Act w₁ Y₁

  Dn : ℕ → D₀ one
  Dn n = drp (P.yc (P.κΔ accᴸ u hself P.Act (κ n)) (P.τ₀ (P.lv (κ n))))

  b : A
  b = sum one (P.yc (P.Step (P.Y₀ {one})) (P.τ₀ {one} tt))

  TΛ≡ : TΛ Λ l ≡ alim (pt b Dn)
  TΛ≡ = refl
```

## 3 第 0 格

第 $0$ 格的世界 $V_0 = \mathrm{sum}\,1\,(z\,Y_1)$, 从坐标 $0$ 走起. 坐标 $0$ 的节点 `N0` (层 $g(0)$), 它的状态 `Y₂` 是第 0 格的起始状态 `Sv` 接一段 $0$.

```agda
  c₀ : P.Cl one azero Λ
  c₀ = κ 0

  V₀ : A
  V₀ = P.v c₀

  lV₀ : Lg V₀
  lV₀ = P.lv c₀

  r₀ : StH azero (g azero) Λ
  r₀ = sL C.self hself

  q₀ : azero ⊲ V₀
  q₀ = C.lim 0 (C.suc C.self)

  A₀ : P.Ig Λ V₀
  A₀ = P.Ig↾ (P.wv c₀) P.Act

  w₀ : D Λ V₀
  w₀ = P.co c₀ ⨾ n0

  Y₂ : P.St V₀
  Y₂ = P._⊕⟨_⟩_ (P.Sv c₀) lV₀ P.zeroD

  N0 : P.Df V₀
  N0 = P.Run accᴸ (ni r₀ (λ _ _ _ → n1)) q₀ lV₀ hself A₀ w₀ Y₂

  τ : P.Tg V₀ hz V₀
  τ = P.τ₀ lV₀

  module R7 = Rl Λ l {V₀} lV₀ (z⊲ᴴ Λ)
  module N7 = Nd Λ l {V₀} lV₀ (z⊲ᴴ Λ)

  Free→Fin : ∀ k → Free k → R7.Fin k
  Free→Fin hz _ = tt
  Free→Fin (hs b) x = Free→Fin b x
  Free→Fin (hl f) x = λ n → Free→Fin (f n) (x n)
  Free→Fin (hΩ _) ()

  -- 状态在一切目标上非零 (HtFeedGrow 的 Inv)
  iY₁ : GG.Inv Y₁
  iY₁ = GG.iv (λ T → nzR (GG.nz-Step P.Y₀ T))

  hA : GG.NZA A₀ lV₀ τ
  hA = GG.na (λ w Y → GG.nz-Step Y τ)

  -- 严格: 第 0 格里坐标 1 的节点非零
  strict : asuc (sum b (P.yc N0 τ)) ≤ sum b (Dn 0)
  strict =
    ≤-trans (≤l 1 (nz≤ (sum b (P.yc N0 τ))
               (nzR (GG.L2 accᴸ (sL {c = one} C.self hself) (C.lim 1 (C.suc C.self)) lV₀ hself A₀ _ _ τ hA
                       (GG.inv⊕ lV₀ _ (GG.inv⊕ lV₀ _ (GG.invcv (P.wv c₀) iY₁)))))))
            (drp≤ (≤-refl b) (P.yc (P.κΔ accᴸ u hself P.Act c₀) τ))
```

## 4 下界: $T_{g(0)}$ 不高于第一个节点

层 $k=g(0)$, 位置 `kk₀` 是节点 `N0` 在世界 $V_0$ 里的层的位置. `A²` 是 `N0` 上升时链的动作 (坐标动作 `Ai`); 它在作用点上定义性地是 `Step`, 所以 `hSt` 就是它的前提.

```agda
  k : H
  k = g azero

  lk : LgH k
  lk = proj₂ l azero tt

  kk₀ : k ⊲[ V₀ ] Λ
  kk₀ = P.kk r₀ q₀ hself

  A² : P.Ig k V₀
  A² = P.Ai accᴸ (accL k) r₀ (λ _ _ _ → n1) q₀ kk₀ hself A₀ w₀

  w′ : D k V₀
  w′ = n0 ⨾ nw C.self n0

  Y′ : P.St V₀
  Y′ = P._⊕⟨_⟩_ Y₂ lV₀ P.zeroD

  -- 左: Ω_k 从 Y₀ 在世界 V₀ 里折叠; 右: 链第 0 项里的那一次 Ω_k
  L R : P.Df V₀
  L = P.Run accᴸ (Ωd k {azero}) (z⊲ V₀) lV₀ kk₀ P.Act n0 P.Y₀
  R = P.Run (accL k) (Ωd k {V₀}) C.self lV₀ kk₀ A² w′ Y′

  -- 链的第 0 项: 状态在层 k 上的读数的折叠
  z₀ : D k V₀
  z₀ = P.yc (P.d Y₂) (P.tg C.self kk₀ lV₀)

  C0 : P.Df V₀
  C0 = P.Run (accL k) z₀ C.self lV₀ kk₀ A² n0 Y₂

  -- 状态自洽 (MonoPort7 的 Good)
  g0 : R7.Good (P.Y₀ {V₀})
  g0 {t} tm = R7.r0 t

  gSv : R7.Good (P.Sv c₀)
  gSv {t} tm = R7.r⨾ t (R7.r0 t) (R7.r0 t) (R7.r0 t) (R7.rnl t (λ _ → x) (λ _ → x) (λ _ → x))
    where
    x = R7.r⨾ t (R7.rΩ t) (R7.rΩ t) (R7.rΩ t) (R7.r0 t)

  z≼ : ∀ Δ → R7._≼_ P.zeroD Δ
  z≼ Δ {t} tm = R7.r0 t

  g⊕0 : ∀ {Y} → R7.Good Y → R7.Good (P._⊕⟨_⟩_ Y lV₀ P.zeroD)
  g⊕0 {Y} gy = R7.⨾≼ {P.d Y} {P.zeroD} {P.d Y} {P.zeroD} gy gy gy (z≼ P.zeroD)

  gY′ : R7.Good Y′
  gY′ = g⊕0 {Y₂} (g⊕0 {P.Sv c₀} gSv)

  one≤b : one ≤ b
  one≤b = sum≥ one (P.yc (P.Step (P.Y₀ {one})) (P.τ₀ {one} tt))

  module Low (fk : Free k) where
    step1 : TΛ k lk ≤ sum one (R7.o₀ L)
    step1 = proj₁ (changeW k lk fk Λ l lV₀ (z⊲ V₀) kk₀)

    step2 : sum one (R7.o₀ L) ≤ sum b (R7.o₀ R)
    step2 = proj₁ (N7.ΩdObs k (Free→Fin k fk) kk₀ N7.aᴸ N7.aᴷ (z⊲ V₀) C.self P.Act A² (N7.hSt k) (N7.hSt k) (N7.hSt k)
                     n0 w′ one b P.Y₀ Y′ g0 gY′ (z≤ , z≼ (P.d Y′)) one≤b)

    -- 前缀: z₀ = (0 ⨾ ω·(Ω_k ⨾ 0)) ⨾ 0, 和不低于其中第一次 Ω_k
    step3 : sum b (R7.o₀ R) ≤ sum b (R7.o₀ C0)
    step3 = ≤l 1 (≤-refl _)

    RK : P.Rk k hz V₀ → D₀ V₀
    RK x = P.RKi accᴸ (accL k) r₀ (λ _ _ _ → n1) q₀ lV₀ hself A₀ w₀ Y₂ τ x

    -- 节点在第 0 层上升: 链的极限不低于第 0 项
    step4 : sum b (R7.o₀ C0) ≤ sum b (P.yc N0 τ)
    step4 = subst (λ x → sum b (R7.o₀ C0) ≤ sum b (RK x))
              (sym (rk0 (P.rkT (⊲ᴴ↑ C.self kk₀) (z⊲ᴴ Λ) lV₀))) (≤l 1 (≤-refl _))

    low : TΛ k lk ≤ sum b (P.yc N0 τ)
    low = ≤-trans step1 (≤-trans step2 (≤-trans step3 step4))
```

## 5 结论

```agda
  growΩ₀ : Free k → asuc (TΛ k lk) ≤ TΛ Λ l
  growΩ₀ fk = ≤-trans (s≤ (Low.low fk)) (≤-trans strict (≤l 1 (≤-refl _)))

-- 第一个 Ω-极限高度: T_0 < T_Ω, 无前提
growΩᴴ₀ : asuc (TΛ hz tt) ≤ TΛ Ωᴴ Lg-Ωᴴ
growΩᴴ₀ = Om.growΩ₀ emb Lg-Ωᴴ tt
```
