# 主线数据类型上的 View (三): `HtFeedTree` 的第 1 层, 条件于世界稳定

> 不含记号. 入口 [MainView](MainView.lagda.md). 主线第 1 层的树 `D₁ W = HtFeedTree.D (hs hz) W`. 它与 `SumOneTree` 的第 1 层 `D one W` 构造子相同, 只是节点的层是高度 (`StH W k (hs hz)` 只有 `ss hself`) 而不是 `A` (`Strict k one` 只有 `ss self`), `ni` 分支的坐标是 `HtFeedTree.D₀` 而不是 `SumOneTree.D azero`.
>
> - `π : D₁ W → SumOneTree.D one W`: 逐构造子的改名, 坐标用 `ι₀ : SumOneTree.D azero W → HtFeedTree.D₀ W` 喂回分支. **主线第 1 层的值定义为 `toBᴴ l x = LayerTrOne.toB l (π x)`**, 合法性 `HWᴴ x = HW (π x)` (同 `BrwViewOne.HW`, 世界稳定). 这是读法的定义, 不是对 `HtFeedTree` 的改动.
> - 骨架 ([MainViewGen](MainViewGen.lagda.md)) 实例化: 读法 `Sm q b y = S q l b (π y)`, 方程除 `e-nl` 外都是 `refl`. 两个段:
>   - `ni` 段: 坐标 $(W',p,l',y)$ 上的部分是 `nw p x ⨾ Jι (λ w → u (q·p) l′ (ι₀ w)) (dif y) self n0`. `Jι` 是 `BrwViewOne.J` 输出在主线类型里的版本 (坐标仍是 `SumOne` 的第 0 层树, 正是 `π` 喂给分支的那些). 值一致 `JIπ` 与 `BrwViewOne.JI` 同形; 前缀抬升用 `BrwViewOne.lift` (条件 `HW`).
>   - `nκ` 段: 层 $c$ 上的部分是 `nw p x ⨾ (HtFeedTree.Cut u c p q lc self ⨾ u (q·p) lc)`. 值一致: `πCut` (主线的 `Cut` 经 `π` 与 `SumOneTree.Cut` 的值相同) 接 `BrwViewKappa.CK`.
> - 良基: 秩的比较 (`BrwWfOneRank`), 段的下降 `Jleπ`, `CKsπ` 与 `BrwWfOne.Jle`, `CKs` 同形, 其余直接用 `Rv`, `Smono`, `base`.
>
> **两处路径不定义相等:** `HtFeedTree.tailP` 与 `SumOneTree.tailP` 是两个同样的定义 (`tailP≡`), `Cut` 与 `K` 在极限处各用各的; 引理对 `aW ≡ aW′` 一般化. 不用 `Funext`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MainViewOne where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
import OCF.Align.HtFeedTree as F
import OCF.Align.SumOneTree as T
open import OCF.Align.BrwMidZero using (dif)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; Sp; I; Ip; K; KR; toB; S-fst; ok-yes)
open import OCF.Align.LayerTrRound using (S-cong; ⊲-idˡ; ≈-sym; ≈-refl; bi-≈)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
open import OCF.Align.BrwViewOne using (Sig₁; Ix₁; Cd₁; tg₁; K1; ki; kκ; WSq; HW; hw→ws; lift; bl-≈; bw-≈; ≡→≈)
open import OCF.Align.BrwViewKappa using (CK; κ-≈)
open import OCF.Align.BrwWfDef using (Obj; Part; p-s; p-l; p-Ω; BrwViewᵂ)
open import OCF.Align.BrwWfRead using (module Read; Cong; module ReadOk)
open import OCF.Align.BrwWfOneRank using (T₁; Sub₁; s-s; s-l; s-i; s-κ; _⊑_; ⊑-refl; _<ₛ_; lt; <ₛ-wf; bl-⊑; ⊑w; Smono; Rv)
open import OCF.Align.BrwWfOne using (base; bΩ-m₁)
open import OCF.Align.BrwHWBase using (R2-ni; R2-n1; R2→WSq)
open import OCF.Align.MainViewGen using (ps; module Skel)
```

## §1 改名 `π`

```agda
D₁ : A → Set
D₁ = F.D (F.hs F.hz)

ι₀ : ∀ {W} → T.D azero W → F.D₀ W
ι₀ T.n0 = F.n0
ι₀ T.n1 = F.n1
ι₀ (x T.⨾ y) = ι₀ x F.⨾ ι₀ y
ι₀ (T.nl d) = F.nl (λ n → ι₀ (d n))
ι₀ (T.ni () u)
ι₀ (T.nκ () u)
ι₀ (T.nw p x) = F.nw p (ι₀ x)

π : ∀ {W} → D₁ W → T.D one W
π F.n0 = T.n0
π F.n1 = T.n1
π (x F.⨾ y) = π x T.⨾ π y
π (F.nl d) = T.nl (λ n → π (d n))
π (F.ni (F.ss F.hself) u) = T.ni (C.ss C.self) (λ p l w → π (u p l (ι₀ w)))
π (F.nκ zz u) = T.nκ tt (λ p l → π (u p l))
π (F.nw p x) = T.nw p (π x)

toBᴴ : ∀ {W} → Lg W → D₁ W → B₁ W
toBᴴ l x = toB l (π x)

HWᴴ : ∀ {W} → D₁ W → Set
HWᴴ x = HW (π x)

ps-Spπ : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (b : B₁ W) (d : ℕ → D₁ W₀) n → S q l b (π (ps d n)) ≡ Sp q l b (λ n → π (d n)) n
ps-Spπ q l b d zero = refl
ps-Spπ q l b d (suc n) = cong (λ t → S q l t (π (d n))) (ps-Spπ q l b d n)
```

## §2 `ni` 段要的件

```agda
Jι : ∀ {W₀ W} → (T.D azero W → D₁ W) → T.D azero W₀ → W₀ ⊲ W → T.D azero W → D₁ W
Jι e T.n0 q w = F.n0
Jι e T.n1 q w = e w
Jι e (x T.⨾ y) q w = Jι e x q w F.⨾ Jι e y q (w T.⨾ T.nw q x)
Jι e (T.nl d) q w = F.nl (λ n → Jι e (d n) q (w T.⨾ T.Pre q d n))
Jι e (T.ni () u) q w
Jι e (T.nκ () u) q w
Jι e (T.nw p x) q w = Jι e x (⊲-tr p q) w

module _ {W : A} (l : Lg W) (e : T.D azero W → D₁ W) where
  JIπ  : ∀ {W₀} (z : T.D azero W₀) (q : W₀ ⊲ W) (w : T.D azero W) {c c′ : B₁ W} → c ≈ c′ →
         S C.self l c (π (Jι e z q w)) ≈ I (λ w′ b → S C.self l b (π (e w′))) z q w c′
  JIπp : ∀ {W₀} (d : ℕ → T.D azero W₀) (q : W₀ ⊲ W) (w : T.D azero W) {c c′ : B₁ W} → c ≈ c′ →
         ∀ n → Sp C.self l c (λ n → π (Jι e (d n) q (w T.⨾ T.Pre q d n))) n ≈ Ip (λ w′ b → S C.self l b (π (e w′))) d q w c′ n
  JIπ T.n0 q w h = h
  JIπ T.n1 q w h = S-cong C.self l (π (e w)) h
  JIπ (x T.⨾ y) q w h = JIπ y q (w T.⨾ T.nw q x) (JIπ x q w h)
  JIπ (T.nl d) q w h = bl-≈ (JIπp d q w h)
  JIπ (T.ni () u) q w h
  JIπ (T.nκ () u) q w h
  JIπ (T.nw p x) q w h = JIπ x (⊲-tr p q) w h
  JIπp d q w h zero = h
  JIπp d q w h (suc n) = JIπ (d n) q (w T.⨾ T.Pre q d n) (JIπp d q w h n)

  Jleπ  : ∀ {W₀} (z : T.D azero W₀) (q : W₀ ⊲ W) (w : T.D azero W) {c c′ : B₁ W} → c ⊑ c′ →
          S C.self l c (π (Jι e z q w)) ⊑ I (λ w′ b → S C.self l b (π (e w′))) z q w c′
  Jleπp : ∀ {W₀} (d : ℕ → T.D azero W₀) (q : W₀ ⊲ W) (w : T.D azero W) {c c′ : B₁ W} → c ⊑ c′ →
          ∀ n → Sp C.self l c (λ n → π (Jι e (d n) q (w T.⨾ T.Pre q d n))) n ⊑ Ip (λ w′ b → S C.self l b (π (e w′))) d q w c′ n
  Jleπ T.n0 q w h = h
  Jleπ T.n1 q w h = Smono C.self l (π (e w)) h
  Jleπ (x T.⨾ y) q w h = Jleπ y q (w T.⨾ T.nw q x) (Jleπ x q w h)
  Jleπ (T.nl d) q w h = bl-⊑ (Jleπp d q w h)
  Jleπ (T.ni () u) q w h
  Jleπ (T.nκ () u) q w h
  Jleπ (T.nw p x) q w h = Jleπ x (⊲-tr p q) w h
  Jleπp d q w h zero = h
  Jleπp d q w h (suc n) = Jleπ (d n) q (w T.⨾ T.Pre q d n) (Jleπp d q w h n)

HW-Jι : ∀ {W₀ W} (e : T.D azero W → D₁ W) → (∀ w → HWᴴ (e w)) → (z : T.D azero W₀) (q : W₀ ⊲ W) (w : T.D azero W) → HWᴴ (Jι e z q w)
HW-Jι e h T.n0 q w = tt
HW-Jι e h T.n1 q w = h w
HW-Jι e h (x T.⨾ y) q w = HW-Jι e h x q w , HW-Jι e h y q (w T.⨾ T.nw q x)
HW-Jι e h (T.nl d) q w = λ n → HW-Jι e h (d n) q (w T.⨾ T.Pre q d n)
HW-Jι e h (T.ni () u) q w
HW-Jι e h (T.nκ () u) q w
HW-Jι e h (T.nw p x) q w = HW-Jι e h x (⊲-tr p q) w
```

## §3 `nκ` 段要的件

```agda
tailP≡ : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) {a n} (p : a ⊲ f n) m → F.tailP f st p m ≡ T.tailP f st p m
tailP≡ f st p zero = refl
tailP≡ f st {n = n} p (suc m) = cong (λ t → ⊲-tr t (st (m + n))) (tailP≡ f st p m)

module _ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D₁ c) where
  u′ : ∀ {c} → W₀ ⊲ c → Lg c → T.D one c
  u′ p l = π (u p l)

  πCut  : ∀ b {a} (p : a ⊲ b) {aW aW′ : W₀ ⊲ a} → aW ≡ aW′ → ∀ (lb : Lg b) {Wt} (bW : b ⊲ Wt) (lτ : Lg Wt) {c c′ : B₁ Wt} →
          c ≈ c′ → S C.self lτ c (π (F.Cut u b p aW lb bW)) ≈ S C.self lτ c′ (T.Cut u′ b p aW′ lb bW)
  πCutR : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} (p : a ⊲ f n) (aW : W₀ ⊲ a)
          {Wt} (bW : alim f ⊲ Wt) (lτ : Lg Wt) {c c′ : B₁ Wt} → c ≈ c′ → ∀ m →
          Sp C.self lτ c (λ m → π (F.Cut u (f (suc (m + n))) (st (m + n)) (⊲-tr aW (F.tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW))) m ≈
          Sp C.self lτ c′ (λ m → T.Cut u′ (f (suc (m + n))) (st (m + n)) (⊲-tr aW (T.tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW)) m
  πCut b C.self refl lb bW lτ h = h
  πCut (asuc c) (C.suc p) {aW} refl lb bW lτ h =
    S-cong (⊲-tr (C.suc C.self) bW) lτ (u′ (⊲-tr aW p) lb) (πCut c p refl lb (⊲-tr (C.suc C.self) bW) lτ h)
  πCut (alim f) (C.lim n p) {aW} refl (st , wl) bW lτ h =
    bl-≈ (πCutR f st wl p aW bW lτ (πCut (f n) p refl (wl n) (⊲-tr (C.lim n C.self) bW) lτ h))
  πCutR f st wl p aW bW lτ h zero = h
  πCutR f st wl {n = n} p aW bW lτ h (suc m) =
    πCut (f (suc (m + n))) (st (m + n)) (cong (⊲-tr aW) (tailP≡ f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) lτ
         (πCutR f st wl p aW bW lτ h m)

  CKsπ  : ∀ b {a} (p : a ⊲ b) {aW aW′ : W₀ ⊲ a} → aW ≡ aW′ → ∀ (lb : Lg b) {Wt} (bW : b ⊲ Wt) (lT : Lg Wt) {x₀ : B₁ a} {c₀ : B₁ Wt} →
          c₀ ⊑ x₀ → S C.self lT c₀ (π (F.Cut u b p aW lb bW)) ⊑ K u′ b p aW′ lb x₀
  CKRsπ : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} (p : a ⊲ f n) (aW : W₀ ⊲ a)
          {Wt} (bW : alim f ⊲ Wt) (lT : Lg Wt) {x₀ : B₁ a} {c₀ : B₁ Wt} → c₀ ⊑ x₀ → ∀ m →
          Sp C.self lT (S C.self lT c₀ (π (F.Cut u (f n) p aW (wl n) (⊲-tr (C.lim n C.self) bW))))
             (λ m → π (F.Cut u (f (suc (m + n))) (st (m + n)) (⊲-tr aW (F.tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW))) m
          ⊑ KR u′ f st wl p aW x₀ m
  CKsπ b C.self refl lb bW lT h = h
  CKsπ (asuc c) (C.suc p) {aW} refl lb bW lT {x₀} {c₀} h =
    ⊑w (subst (λ t → S t lT (S C.self lT c₀ (π (F.Cut u c p aW lb r))) (u′ (⊲-tr aW p) lb) ⊑ S C.self lb (K u′ c p aW lb x₀) (u′ (⊲-tr aW p) lb))
              (⊲-idˡ r)
              (Rv (u′ (⊲-tr aW p) lb) C.self r lb lT (CKsπ c p refl lb r lT h)))
    where r = ⊲-tr (C.suc C.self) bW
  CKsπ (alim f) (C.lim n p) {aW} refl (st , wl) bW lT h = bl-⊑ (λ m → ⊑w (CKRsπ f st wl p aW bW lT h m))
  CKRsπ f st wl p aW bW lT h zero = CKsπ (f _) p refl (wl _) (⊲-tr (C.lim _ C.self) bW) lT h
  CKRsπ f st wl {n = n} p aW bW lT h (suc m) =
    CKsπ (f (suc (m + n))) (st (m + n)) (cong (⊲-tr aW) (tailP≡ f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) lT
         (CKRsπ f st wl p aW bW lT h m)

module _ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D₁ c) (hu : ∀ {c} p l → HWᴴ (u {c} p l)) where
  HW-Cutπ : ∀ b {a} (p : a ⊲ b) (aW : W₀ ⊲ a) (lb : Lg b) {Wt} (bW : b ⊲ Wt) → HWᴴ (F.Cut u b p aW lb bW)
  HW-Cutπ b C.self aW lb bW = tt
  HW-Cutπ (asuc c) (C.suc p) aW lb bW = HW-Cutπ c p aW lb _ , hu (⊲-tr aW p) lb
  HW-Cutπ (alim f) (C.lim n p) aW (st , wl) bW =
    HW-Cutπ (f n) p aW (wl n) _ ,
    (λ m → HW-Cutπ (f (suc (m + n))) (st (m + n)) (⊲-tr aW (F.tailP f st p m)) (wl (suc (m + n))) _)
```

## §4 骨架的实例

```agda
open Skel {Nd = λ W k → F.StH W k (F.hs F.hz)} {Vv = λ R → F.Vs (F.hs F.hz) R} {Zz = F.NZ (F.hs F.hz)}
          Sig₁ proj₁ (λ {i} x → toBᴴ (proj₂ i) x) (λ x → HWᴴ x) (λ {i} q b y → S q (proj₂ i) b (π y)) ≈-refl
          (λ q b → refl) (λ q b → refl) (λ q b y z → refl) (λ r q b y → refl) (λ x q y → refl) (λ x → refl) (z≼ , z≼)
          (λ {i} x q d → bl-≈ (λ n → ≡→≈ (sym (ps-Spπ q (proj₂ i) (toBᴴ (proj₂ i) x) d n))))
          (λ {i} q b y → S-fst yes q (proj₂ i) b (π y) (ok-yes (π y)))
          tt _,_ proj₁ proj₂ (λ h → h) (λ h → h) (λ h → h)
  public

segI : SegI
segI {W , l} x hx vx q (F.ss F.hself) u (hu , _) =
  vΩ ki g (λ c _ → hg c) (bi-≈ (λ {W′} p l′ y ly → ≈-sym (JIπ l′ (λ w → u (⊲-tr q p) l′ (ι₀ w)) (dif {W′} y (z⊲ y) ly) C.self T.n0 (lift l l′ p (π x) hx))))
  where
  g : (c : Cd₁ {W , l} ki) → X (tg₁ {W , l} {ki} c)
  g (W′ , p , l′ , y , ly) = F.nw p x F.⨾ Jι (λ w → u (⊲-tr q p) l′ (ι₀ w)) (dif {W′} y (z⊲ y) ly) C.self T.n0
  hg : ∀ c → Lgx {tg₁ {W , l} {ki} c} (g c)
  hg (W′ , p , l′ , y , ly) = hx , HW-Jι _ (λ w → hu (⊲-tr q p) l′ w) (dif {W′} y (z⊲ y) ly) C.self T.n0

segK : SegK
segK {W , l} x hx vx q zz u (hu , _) = vΩ kκ g (λ c _ → hg c) (κ-≈ brκ)
  where
  g : (c : Cd₁ {W , l} kκ) → X (tg₁ {W , l} {kκ} c)
  g (c , p , lc) = F.nw p x F.⨾ (F.Cut u c p q lc C.self F.⨾ u (⊲-tr q p) lc)
  hg : ∀ c → Lgx {tg₁ {W , l} {kκ} c} (g c)
  hg (c , p , lc) = hx , (HW-Cutπ u hu c p q lc C.self , hu (⊲-tr q p) lc)
  brκ : ∀ {c} (p : W ⊲ c) (lc : Lg c) →
        S C.self lc (K (u′ u) c p q lc (toBᴴ l x)) (π (u (⊲-tr q p) lc)) ≈ toBᴴ lc (g (c , p , lc))
  brκ {c} p lc = S-cong C.self lc (π (u (⊲-tr q p) lc))
    (≈-trans (CK (u′ u) (λ p′ l′ → hw→ws (π (u p′ l′)) (hu p′ l′)) c p q lc C.self lc
                 (≈-sym (≈-trans (lift l lc p (π x) hx) (bw-≈ p (toBᴴ l x)))))
             (≈-sym (πCut u c p refl lc C.self lc (≈-refl _))))

open WithSeg segI segK public

view₁ᴴ : BrwView Sig₁ X (λ {i} x → toBᴴ (proj₂ i) x) (λ {i} x → Lgx {i} x)
view₁ᴴ = view
```

`view₁ᴴ`: 一切 `HWᴴ` 的主线第 1 层树都有 View, 值一致对 `toBᴴ`. **条件定理**, 条件与 SumOne 上的 `view₁` 是同一个 (`HW`, 经 `π`).

## §5 部分的良基: 在 View 上无条件

```agda
rk₁ : ∀ {i : Ix₁} → B₁ (proj₁ i) → T₁
rk₁ {i} b = proj₁ i , b

D-i₁ : ∀ {i} (x : X i) (hx : HWᴴ x) (vx : V i (toBᴴ (proj₂ i) x)) {W₀ k} (q : W₀ ⊲ proj₁ i) (r : F.StH W₀ k (F.hs F.hz))
       (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → F.Vs (F.hs F.hz) r W′ → D₁ W′) (hy : HWᴴ (F.ni r u)) →
       (∀ {o} → Pt vx o → rk₁ {proj₁ o} (toBᴴ (proj₂ (proj₁ o)) (proj₁ (proj₂ o))) <ₛ rk₁ {i} (toBᴴ (proj₂ i) x)) →
       ∀ {o} → Pt (segI x hx vx q r u hy) o → rk₁ {proj₁ o} (toBᴴ (proj₂ (proj₁ o)) (proj₁ (proj₂ o))) <ₛ rk₁ {i} (S q (proj₂ i) (toBᴴ (proj₂ i) x) (π (F.ni r u)))
D-i₁ {W , l} x hx vx q (F.ss F.hself) u hy H (p-Ω (W′ , p , l′ , y , ly) _) =
  lt (s-i p l′ y ly) (Jleπ l′ (λ w → u (⊲-tr q p) l′ (ι₀ w)) (dif {W′} y (z⊲ y) ly) C.self T.n0 (⊑w (base l l′ p (π x))))

D-κ₁ : ∀ {i} (x : X i) (hx : HWᴴ x) (vx : V i (toBᴴ (proj₂ i) x)) {W₀} (q : W₀ ⊲ proj₁ i) (zz : F.NZ (F.hs F.hz))
       (u : ∀ {c} → W₀ ⊲ c → Lg c → D₁ c) (hy : HWᴴ (F.nκ zz u)) →
       (∀ {o} → Pt vx o → rk₁ {proj₁ o} (toBᴴ (proj₂ (proj₁ o)) (proj₁ (proj₂ o))) <ₛ rk₁ {i} (toBᴴ (proj₂ i) x)) →
       ∀ {o} → Pt (segK x hx vx q zz u hy) o → rk₁ {proj₁ o} (toBᴴ (proj₂ (proj₁ o)) (proj₁ (proj₂ o))) <ₛ rk₁ {i} (S q (proj₂ i) (toBᴴ (proj₂ i) x) (π (F.nκ zz u)))
D-κ₁ {W , l} x hx vx q zz u hy H (p-Ω (c , p , lc) _) =
  lt (s-κ p lc) (Smono C.self lc (π (u (⊲-tr q p) lc)) (CKsπ u c p refl lc C.self lc (base l lc p (π x))))

open Dec T₁ _<ₛ_ <ₛ-wf (λ {i} b → rk₁ {i} b) (λ b → lt s-s (⊑-refl b))
         (λ {i} x q d n → lt (s-l n) (subst (λ t → t ⊑ Sp q (proj₂ i) (toBᴴ (proj₂ i) x) (λ n → π (d n)) n)
                                             (sym (ps-Spπ q (proj₂ i) (toBᴴ (proj₂ i) x) d n)) (⊑-refl _)))
         D-i₁ D-κ₁
  public

wf₁ᴴ : WellFounded _◁ᴳ_
wf₁ᴴ = wf

view₁ᴴᵂ : BrwViewᵂ Sig₁ X (λ {i} x → toBᴴ (proj₂ i) x) (λ {i} x → Lgx {i} x)
view₁ᴴᵂ = viewᵂ
```

## §6 读出 `B₁`, 与前提可满足

```agda
Cong₁ᴴ : Cong view₁ᴴᵂ
Cong₁ᴴ = record { tr = ≼-trans ; bs-m = s≼s ; bl-m = λ h → l≼ (λ n → ≼l n (h n)) ; bΩ-m = λ {i} k h → bΩ-m₁ {i} k h }

rd₁ᴴ : (o : Obj Sig₁ X (λ {i} x → toBᴴ (proj₂ i) x) (λ {i} x → Lgx {i} x)) → B₁ (proj₁ (proj₁ o))
rd₁ᴴ o = Read.rd view₁ᴴᵂ (λ c → tt) o

rd₁≈ᴴ : ∀ o → (rd₁ᴴ o ≼ toBᴴ (proj₂ (proj₁ o)) (proj₁ (proj₂ o))) × (toBᴴ (proj₂ (proj₁ o)) (proj₁ (proj₂ o)) ≼ rd₁ᴴ o)
rd₁≈ᴴ o = ReadOk.rd≈ view₁ᴴᵂ (λ c → tt) Cong₁ᴴ o

-- 主线的 Ω₁: Ωd (hs hz) 在一切世界上 HWᴴ
HW-Ωᴴ : ∀ {W} → HWᴴ (F.Ωd (F.hs F.hz) {W})
HW-Ωᴴ = tt , ((λ p l w → tt) , R2→WSq (R2-ni (λ _ _ _ → T.n1) (λ _ _ _ → T.n1) (λ r r′ l l′ sh → R2-n1)))
```
