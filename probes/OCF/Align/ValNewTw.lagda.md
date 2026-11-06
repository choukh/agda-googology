# 新闭项的值 (三): `TΛ`, `TΛ₂`, `TΛn` 之间的无条件比较

> 不含记号. 入口 [ValNew](ValNew.lagda.md). 第 4 层: 只新增定理, 不改树, 折叠, 合法性. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提.
>
> 记 $T(h) =$ `col collL h lh` ([FabLFReGen](FabLFReGen.lagda.md) 的最终坍缩, 层 $1\boxplus h$, `GL` 的一切 A-回灌有损). 闭项 `TΛ`, `TΛ₂`, `TΛn n` 都是 $T(\mathrm{up}\,x)$ 的形状. 三步:
>
> - **§1 后继一步 `Hs.hs-step`**: $T(h)\le T(h+1)$, 两边的合法性证明任意, 前提 `NI h`. 证明: $T(h+1)$ 的折叠里, 层 $1\boxplus h$ 的节点在第 0 层目标上上升, 链的第 0 项的数据是 $0⨾\omega\cdot(\Omega_{1\boxplus h}⨾0)$ (`hs-unfold`); 实例 $1\boxplus h$ 的折叠 (就是 $T(h)$ 的折叠) 与它相关 (`ValNewRun.Two.cross`, 换实例 + 状态与前缀多出一段).
> - **§2 极限一步 `Hl.hl-step`**: $T(f\,n)\le T(\mathrm{hl}\,f)$, 对一切 $n$, 前提 `NI (hl f)`. 同样的两段: 第 $n$ 个节点的链的第 0 项 (`hl-unfold`, 与 [TpMonoHl](TpMonoHl.lagda.md) 的 `hl-unfold` 同形, 那里链要再走一格), 再 `cross`.
> - **§3 闭项**: `TΛn≤ : TΛn n ≤ TΛn (n+1)` (先后继一步到 $\mathrm{up}(\Lambda_n)+1$, 它字面是 $\Lambda_{n+1}=\mathrm{fix}(\Lambda_n+1)$ 的第 0 项, 再极限一步), `TΛ≤TΛ₂`, 塔的每一站 `stage≤ : T(up (tw n)) ≤ TΛ`, 以及合法性证明无关 `lg-irr` (同一层, 两个合法性证明, 两向 $\le$).
>
> 一切比较是 `A` 上通常的 `≤` (`TLRuleSpec._≤_`); `FabLFReGen.ordL` 按构造子把 `A` 搬到 `Ordᶜ`, 所以这就是 `ord` 的比较. 都是**不严格**的 $\le$; 严格没有做.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValNewTw where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (≤l; ≤-refl; ≤-trans) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (tpK; w₀; lw₀; StH; ss; sl; n0; n1; _⨾_; nl; ni; nw)
open import OCF.Align.GenFoldTree using (module Tree; topStepG; accᴸ; accL)
open import OCF.Align.LFReTy using (SL)
open import OCF.Align.LFReTower using (tw; Lg-tw; Λ; Lg-Λ; Λ₂; Lg-Λ₂; Λn; Lg-Λn; it)
open import OCF.Align.NewTwrIf using (col)
open import OCF.Align.NewTwrColl using (module At; one⊞)
open import OCF.Align.FabLFReGen using (GL; LdL; flL; collL; TΛ; TΛ₂; TΛn)
open import OCF.Align.ValNewRel
import OCF.Align.ValNewRun as VR

open Tree SL using (D; D₀; ≤rf; sum; pt; module Om)
open Rel SL
open OmM (topStepG (tpK GL))
open Om (topStepG (tpK GL)) using (Ωd)

module R = VR SL GL LdL flL (λ κ → refl)

W₁ : Wd (step SL)
W₁ = w₀ GL , hz

lW₁ : LgW (step SL) W₁
lW₁ = lw₀ GL , tt
```

## §1 后继一步

```agda
module Hs (h : HB (step SL)) (lh lh′ : LgB h) (nh : NI h) where
  L : HB (step SL)
  L = one⊞ h

  lL : LgB L
  lL = Lg-⊞ (hs hz) h tt lh

  oL : ∀ {w} → hs hz ⊲[ w ] L
  oL = ⊞-fst (hs hz) h

  lL′ : LgB (hs L)
  lL′ = Lg-⊞ (hs hz) (hs h) tt lh′

  oL′ : ∀ {w} → hs hz ⊲[ w ] hs L
  oL′ = ⊞-fst (hs hz) (hs h)

  nL : NI L
  nL = NI-⊞ (hs hz) h tt nh

  module Q = At GL LdL flL L lL oL
  module P = At GL LdL flL (hs L) lL′ oL′
  module TW = R.Two L lL oL (hs L) lL′ oL′ nL
  module F₂ = TW.F₂

  Y₁ᴾ : TW.T₂.St W₁
  Y₁ᴾ = F₂._⊕⟨_⟩_ P.Y₀ lW₁ (F₂.Stp P.Y₀)

  r : StH W₁ L (hs L)
  r = ss hself

  hk : L ⊲[ W₁ ] hs L
  hk = hsuc hself

  wᴾ : D (hs L) W₁
  wᴾ = n0 ⨾ nw ≤rf n1

  A² : TW.T₂.Ig L W₁
  A² = F₂.Ai accᴸ (accL L) r (λ _ _ _ → n1) ≤rf hk hself P.Act wᴾ

  Tk : TW.T₂.Tg W₁ L W₁
  Tk = TW.T₂.tg ≤rf hk lW₁

  b₀ : A
  b₀ = sum (asuc azero) (F₂.yc (F₂.Stp P.Y₀) (F₂.τ₀ lW₁))

  -- 链的第 0 项, 第 0 层的读数
  X : D₀ W₁
  X = F₂.yc (F₂.Run (accL L) (F₂.yc (F₂.d Y₁ᴾ) Tk) ≤rf lW₁ hk A² n0 Y₁ᴾ) (F₂.τ₀ lW₁)

  RK : F₂.Rk L hz W₁ → D₀ W₁
  RK x = F₂.RKi accᴸ (accL L) r (λ _ _ _ → n1) ≤rf lW₁ hself P.Act wᴾ Y₁ᴾ (F₂.τ₀ lW₁) x

  rk0 : ∀ {k m} (x : F₂.Rk k hz m) → x ≡ F₂.rise
  rk0 (F₂.keep ())
  rk0 F₂.rise = refl

  dd : D₀ W₁
  dd = F₂.yc (F₂.Run accᴸ (ni r (λ _ _ _ → n1)) ≤rf lW₁ hself P.Act wᴾ Y₁ᴾ) (F₂.τ₀ lW₁)

  dd≡ : dd ≡ RK F₂.rise
  dd≡ = cong RK (rk0 _)

  hs-unfold : sum b₀ X ≤ᴬ col collL (hs h) lh′
  hs-unfold = subst (λ y → sum b₀ X ≤ᴬ sum b₀ y) (sym dd≡) (≤l 1 (≤-refl _))

  -- 换实例, 状态与前缀多出一段
  hx : Rl L (Ωd L {W₁}) (F₂.yc (F₂.d Y₁ᴾ) Tk)
  hx = me (ml0 (mr (Ωd-M L nL acc⁺)))

  hA : TW.IgR {L} {W₁} Q.Act A²
  hA = TW.igr (λ p lW′ hw hY → TW.Step-R hY)

  T≤X : col collL h lh ≤ᴬ sum b₀ X
  T≤X = TW.cross {L} {W₁} accᴸ (accL L) {Ωd L {W₁}} {F₂.yc (F₂.d Y₁ᴾ) Tk} hx lW₁ hself hk
          {Q.Act} {A²} hA {n0} {n0} mz {Q.Y₀} {Y₁ᴾ} (TW.str TW.zero-R) (sum≥ (asuc azero) (F₂.yc (F₂.Stp P.Y₀) (F₂.τ₀ lW₁)))

  hs-step : col collL h lh ≤ᴬ col collL (hs h) lh′
  hs-step = ≤-trans T≤X hs-unfold
```

## §2 极限一步

```agda
module Hl (f : ℕ → HB (step SL)) (lf : LgB (hl f)) (nf : NI (hl f)) (n : ℕ) (lfn : LgB (f n)) where
  Λb : HB (step SL)
  Λb = one⊞ (hl f)

  lb : LgB Λb
  lb = Lg-⊞ (hs hz) (hl f) tt lf

  ob : ∀ {w} → hs hz ⊲[ w ] Λb
  ob = ⊞-fst (hs hz) (hl f)

  L : HB (step SL)
  L = one⊞ (f n)

  lL : LgB L
  lL = Lg-⊞ (hs hz) (f n) tt lfn

  oL : ∀ {w} → hs hz ⊲[ w ] L
  oL = ⊞-fst (hs hz) (f n)

  nL : NI L
  nL = NI-⊞ (hs hz) (f n) tt (nf n)

  module Q = At GL LdL flL L lL oL
  module P = At GL LdL flL Λb lb ob
  module TW = R.Two L lL oL Λb lb ob nL
  module F₂ = TW.F₂

  Fi : ℕ → D Λb W₁
  Fi j = ni (sl j hself) (λ _ _ _ → n1)

  Rp : ℕ → D Λb W₁ × TW.T₂.St W₁
  Rp = F₂.Rpt accᴸ Fi ≤rf lW₁ hself P.Act (n0 ⨾ nw ≤rf n1) (F₂._⊕⟨_⟩_ P.Y₀ lW₁ (F₂.Stp P.Y₀))

  d : ℕ → D₀ W₁
  d j = F₂.yc (F₂.Run accᴸ (Fi j) ≤rf lW₁ hself P.Act (proj₁ (Rp j)) (proj₂ (Rp j))) (F₂.τ₀ lW₁)

  b₀ : A
  b₀ = sum (asuc azero) (F₂.yc (F₂.Stp P.Y₀) (F₂.τ₀ lW₁))

  T≡ : col collL (hl f) lf ≡ alim (pt b₀ d)
  T≡ = refl

  r : StH W₁ L Λb
  r = sl n hself

  hk : L ⊲[ W₁ ] Λb
  hk = hlim n hself

  A² : TW.T₂.Ig L W₁
  A² = F₂.Ai accᴸ (accL L) r (λ _ _ _ → n1) ≤rf hk hself P.Act (proj₁ (Rp n))

  β : A
  β = pt b₀ d n

  RK : F₂.Rk L hz W₁ → D₀ W₁
  RK x = F₂.RKi accᴸ (accL L) r (λ _ _ _ → n1) ≤rf lW₁ hself P.Act (proj₁ (Rp n)) (proj₂ (Rp n)) (F₂.τ₀ lW₁) x

  rk0 : ∀ {k m} (x : F₂.Rk k hz m) → x ≡ F₂.rise
  rk0 (F₂.keep ())
  rk0 F₂.rise = refl

  dn≡ : d n ≡ RK F₂.rise
  dn≡ = cong RK (rk0 _)

  Tk : TW.T₂.Tg W₁ L W₁
  Tk = TW.T₂.tg ≤rf hk lW₁

  X : D₀ W₁
  X = F₂.yc (F₂.Run (accL L) (F₂.yc (F₂.d (proj₂ (Rp n))) Tk) ≤rf lW₁ hk A² n0 (proj₂ (Rp n))) (F₂.τ₀ lW₁)

  hl-unfold : sum β X ≤ᴬ col collL (hl f) lf
  hl-unfold = ≤l (suc n) (subst (λ y → sum β X ≤ᴬ sum β y) (sym dn≡) (≤l 1 (≤-refl _)))

  -- 第 m 段的状态在层 L 上的读数: 0 ⨾ ω·(Ω_L ⨾ 0) 再接前 m 个节点的输出
  stR : ∀ m → Rl L (Ωd L {W₁}) (F₂.yc (F₂.d (proj₂ (Rp m))) Tk)
  stR zero = me (ml0 (mr (Ωd-M L nL acc⁺)))
  stR (suc m) = mr (stR m)

  hA : TW.IgR {L} {W₁} Q.Act A²
  hA = TW.igr (λ p lW′ hw hY → TW.Step-R hY)

  T≤X : col collL (f n) lfn ≤ᴬ sum β X
  T≤X = TW.cross {L} {W₁} accᴸ (accL L) {Ωd L {W₁}} {F₂.yc (F₂.d (proj₂ (Rp n))) Tk} (stR n) lW₁ hself hk
          {Q.Act} {A²} hA {n0} {n0} mz {Q.Y₀} {proj₂ (Rp n)} (TW.str TW.zero-R)
          (≤-trans (sum≥ (asuc azero) (F₂.yc (F₂.Stp P.Y₀) (F₂.τ₀ lW₁))) (pt≥ b₀ d n))

  hl-step : col collL (f n) lfn ≤ᴬ col collL (hl f) lf
  hl-step = ≤-trans T≤X hl-unfold
```

## §3 闭项

**合法性证明无关.** 同一层, 两个合法性证明 (实例的 `cmpB` 读合法性证明, 两个实例的位置可以不同): 两向 $\le$. `TpMono` 文件头说 `T⁺` 的这一条一般没有证; 对 `GL` 的坍缩它是 `cross` 在 "两个实例同层" 处的特例.

```agda
module Irr (h : HB (step SL)) (lh lh′ : LgB h) (nh : NI h) where
  L : HB (step SL)
  L = one⊞ h

  nL : NI L
  nL = NI-⊞ (hs hz) h tt nh

  module Q₁ = At GL LdL flL L (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h)
  module Q₂ = At GL LdL flL L (Lg-⊞ (hs hz) h tt lh′) (⊞-fst (hs hz) h)
  module TW = R.Two L (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h) L (Lg-⊞ (hs hz) h tt lh′) (⊞-fst (hs hz) h) nL

  lg-irr : col collL h lh ≤ᴬ col collL h lh′
  lg-irr = TW.cross {L} {W₁} accᴸ accᴸ {Ωd L {W₁}} {Ωd L {W₁}} (Ωd-M L nL acc⁺) lW₁ hself hself
             {Q₁.Act} {Q₂.Act} (TW.igr (λ p lW′ hw hY → TW.Step-R hY)) {n0} {n0} mz {Q₁.Y₀} {Q₂.Y₀} (TW.str TW.zero-R) (≤-refl (asuc azero))
```

**闭项之间.** 陈述逐字写.

```agda
TΛn≤ : ∀ n → TΛn n ≤ᴬ TΛn (suc n)
TΛn≤ n =
  ≤-trans (Hs.hs-step (up (Λn n)) (Lg-up (Λn n) (Lg-Λn n)) (Lg-up (Λn n) (Lg-Λn n)) (NI-up (Λn n)))
          (Hl.hl-step (λ m → up (it (hs (Λn n)) m)) (Lg-up (Λn (suc n)) (Lg-Λn (suc n))) (NI-up (Λn (suc n))) 0
                      (Lg-up (Λn n) (Lg-Λn n)))

TΛ≤TΛ₂ : TΛ ≤ᴬ TΛ₂
TΛ≤TΛ₂ = TΛn≤ 0

-- 塔的每一站都不高于对角
stage≤ : ∀ n → col collL (up (tw n)) (Lg-up (tw n) (Lg-tw n)) ≤ᴬ TΛ
stage≤ n = Hl.hl-step (λ m → up (tw m)) (Lg-up Λ Lg-Λ) (NI-up Λ) n (Lg-up (tw n) (Lg-tw n))

-- TΛn 沿 n 单调 (一切 n ≤ m)
TΛn-mono : ∀ n k → TΛn n ≤ᴬ TΛn (k + n)
TΛn-mono n zero = ≤-refl (TΛn n)
TΛn-mono n (suc k) = ≤-trans (TΛn-mono n k) (TΛn≤ (k + n))
```
