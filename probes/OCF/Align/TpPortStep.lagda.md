# 两种种类的单调 (十三): 不含 Ω-极限的输入上, 后继与 ℕ-极限两种一步

> 入口 [TpPort](TpPort.lagda.md). 不含记号. 手写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 不改树、折叠、合法性.
>
> [TpMonoHs](TpMonoHs.lagda.md) 把 $T^+(h) < T^+(h+1)$ 归结为 `ChangeHs h` (跨实例, 同一世界) 与 `MonoStepHs h` (实例之内), [TpMonoHl](TpMonoHl.lagda.md) 把 $T^+(f\,n) < T^+(\mathrm{hl}\,f)$ 归结为 `MonoHl f lf n`. 本文在 $h$ (以及 $f(0),\dots,f(n)$) 不含 Ω-极限时把它们证出来, 用的是单种类主线 `MonoPort6`–`7` 的手法, 搬到两种种类的折叠上 (生成的克隆 `TpPortSim` … `TpPortNode`):
>
> - **`change′`** (照 `HtCrossVInst.change′`): 小实例的最高层 $\Lambda$ 不含 Ω-极限, 则 $T_\Lambda$ 与它在任意大实例 $\Lambda'$ 里、任意位置 $e$ 上的折叠 (`TΛ-in`) 在值上互相 $\le$. 工具是不含回灌的互模拟 (`TpPortRun.Two`).
> - **`SucF.change`**, **`SucF.mono`**: `ChangeHs h`, `MonoStepHs h` (`Free h`). 前者是 `change′` 的同一个互模拟 (照 `HtCrossVInst.XR`), 后者是 $\Omega_L$ 在两个世界里的两次折叠的观测 (`TpPortNode.ΩdObs`, 照 `MonoPort7Lim.Suc.monoS`).
> - **`LimF.mono`**: `MonoHl f lf n`, 只要 $f(0),\dots,f(n)$ 不含 Ω-极限 (`Upto`). 右边状态的自洽 (`gRp`) 由 `nodeSelf` 对前 $n$ 段归纳; 第 $n$ 段之后的项不出现.
> - **`SucF.grow`**, **`LimF.grow`**: 由 `TpMonoHs.Hs.hs-reduce`, `TpMonoHl.Hl.N.hl-reduce` 得到 $T^+(h) < T^+(h+1)$ 与 $T^+(f\,n) < T^+(\mathrm{hl}\,f)$.
> - **`irrF`, `fstF`, `fst<F`**: 接口 [TpMonoIf](TpMonoIf.lagda.md) 的律 (b) 在不含 Ω-极限的右边 $b$ 上成立 (左边 $a$ 自动不含, 因为是 $b$ 的第一位置), 合法性证明无关也在这一部分成立. 这是定理, 不是 `Laws⁺` (一般输入上仍未证).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPortStep where

open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (n≤1+n) renaming (≤-trans to ≤ℕ-trans; ≤-refl to ≤ℕ-refl)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤-refl; ≤-trans; ≤-suc)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; hself; hsuc; hlim; hLim; _⊲[_]_; LgB; _⊞_; Lg-⊞; ⊞-fst; z⊲ᴮ)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; D; accᴸ; accK; ss; sl; n0; n1; _⨾_; nl; nw; Ωd; sum; pt; ≤rf)
  renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerFClosed using (module At; TΛ; T⁺; top⁺; one; W₁)
open import OCF.Align.HtTowerFGrow using (sum≥)
open import OCF.Align.TpMonoHs using (b₀; lW₁; module Hs)
open import OCF.Align.TpMonoHl using (module Hl)
open import OCF.Align.TpMonoIf using (_⊑_; _⊏_; _⊲⁺[_]_; psuc; plim; pLim)
open import OCF.Align.TpPortSim using (Free; free⊲; Ωd-R; sum-R; sum-R′; s0; s⨾; sw) renaming (Rl to Sm)
open import OCF.Align.TpPortRun using (module Two)
import OCF.Align.TpPortRel as RelP
import OCF.Align.TpPortNode as NodeP
```

## §1 不含 Ω-极限, 世界 $(0,0)\to(1,0)$

```agda
free⊞ : ∀ a b → Free a → Free b → Free (a ⊞ b)
free⊞ a hz fa fb = fa
free⊞ a (hs b) fa fb = free⊞ a b fa fb
free⊞ a (hl f) fa fb = λ n → free⊞ a (f n) fa (fb n)
free⊞ a (hΩ κ g) fa ()

free-top : ∀ h → Free h → Free (top⁺ h)
free-top h fh = free⊞ (hs hz) h tt fh

q₀₁ : (azero , hz) ≤ʷ W₁
q₀₁ = z⊲ one , hself

-- 值上相等
infix 4 _≃_
_≃_ : A → A → Set
a ≃ b = (a ≤ b) × (b ≤ a)

Sm→≃ : ∀ {W} {x y : D hz W} → Sm hz x y → ∀ b → sum b x ≃ sum b y
Sm→≃ r b = sum-R accᴸ r (≤-refl b) , sum-R′ accᴸ r (≤-refl b)
```

## §2 换实例 (照 `HtCrossVInst` §1–§2)

```agda
module Cross (Λ₁ : Ht) (l₁ : LgB Λ₁) (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ₁) (Λ₂ : Ht) (l₂ : LgB Λ₂) (o₂ : ∀ {w} → hs hz ⊲[ w ] Λ₂)
  (fr : ∀ {t m} → t ⊲[ m ] Λ₁ → t ⊲[ m ] Λ₂ → Free t) where
  open Two Λ₁ l₁ o₁ Λ₂ l₂ o₂ fr
  module P₁ = At Λ₁ l₁ o₁
  module P₂ = At Λ₂ l₂ o₂

  Act-R : ∀ {ly W} → IgR (P₁.Act {ly} {W}) (P₂.Act {ly} {W})
  Act-R = igr (λ p lW′ hw hY → Step-R hY)

  Y₀-R : ∀ {W} → StR (P₁.Y₀ {W}) (P₂.Y₀ {W})
  Y₀-R = str zero-R

  inst0′ : ∀ {ly W₀ W} (x : D ly W₀) → Sm ly x x → (q₀ : W₀ ≤ʷ W) (lW : LgW₂ W) (ll₁ : ly ⊲[ W ] Λ₁) (ll₂ : ly ⊲[ W ] Λ₂) →
           Sm hz (P₁.yc (P₁.Run accᴸ x q₀ lW ll₁ P₁.Act n0 P₁.Y₀) (P₁.τ₀ lW)) (P₂.yc (P₂.Run accᴸ x q₀ lW ll₂ P₂.Act n0 P₂.Y₀) (P₂.τ₀ lW))
  inst0′ x hx q₀ lW ll₁ ll₂ = at (Run-R accᴸ accᴸ hx q₀ lW ll₁ ll₂ Act-R s0 Y₀-R) ≤rf (z⊲ᴮ Λ₁) (z⊲ᴮ Λ₂) lW

-- 层 Λ 的 Ω_Λ 在大实例 Λ′ 里、位置 e 上折叠的闭项
TΛ-in : ∀ Λ′ (l′ : LgB Λ′) (o′ : ∀ {w} → hs hz ⊲[ w ] Λ′) Λ → Λ ⊲[ W₁ ] Λ′ → A
TΛ-in Λ′ l′ o′ Λ e = sum azero (n1 ⨾ P.yc (P.Run accᴸ (Ωd Λ {azero , hz}) q₀₁ lW₁ e P.Act n0 P.Y₀) (P.τ₀ lW₁))
  where module P = At Λ′ l′ o′

change′ : ∀ Λ (l : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) → Free Λ →
          ∀ Λ′ (l′ : LgB Λ′) (o′ : ∀ {w} → hs hz ⊲[ w ] Λ′) (e : Λ ⊲[ W₁ ] Λ′) → TΛ Λ l o ≃ TΛ-in Λ′ l′ o′ Λ e
change′ Λ l o fΛ Λ′ l′ o′ e =
  Sm→≃ (Cross.inst0′ Λ l o Λ′ l′ o′ (λ p _ → free⊲ p fΛ) (Ωd Λ) (Ωd-R Λ fΛ accᴸ) q₀₁ lW₁ hself e) one

-- 闭项的值与合法性证明无关 (不含 Ω-极限)
irrF : ∀ a (la la′ : LgB a) → Free a → T⁺ a la ≤ T⁺ a la′
irrF a la la′ fa = proj₁ (change′ (top⁺ a) (Lg-⊞ (hs hz) a tt la) (⊞-fst (hs hz) a) (free-top a fa)
                                   (top⁺ a) (Lg-⊞ (hs hz) a tt la′) (⊞-fst (hs hz) a) hself)
```

## §3 后继一步

```agda
module SucF (h : Ht) (lh : LgB h) (fh : Free h) where
  module H = Hs h lh

  L : Ht
  L = top⁺ h
  lL : LgB L
  lL = Lg-⊞ (hs hz) h tt lh
  oL : ∀ {w} → hs hz ⊲[ w ] L
  oL = ⊞-fst (hs hz) h
  fL : Free L
  fL = free-top h fh

  t₀ : hz ⊲[ W₁ ] L
  t₀ = z⊲ᴮ L

  open RelP L lL oL {W₁} lW₁ t₀
  open NodeP L lL oL {W₁} lW₁ t₀

  fH : ∀ k → Free k → Fin k
  fH hz _ = tt
  fH (hs b) x = fH b x
  fH (hl g) x = λ n → fH (g n) (x n)
  fH (hΩ _ _) ()

  z≼ : ∀ Δ → P.zeroD ≼ Δ
  z≼ Δ {t} tm = r0 t

  g0 : Good P.Y₀
  g0 = z≼ P.zeroD

  gL : Good (P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀))
  gL = ⨾≼ {P.d P.Y₀} {P.Stp P.Y₀} {P.d P.Y₀} {P.Stp P.Y₀} g0 g0 g0
         (proj₂ (hSt L n0 n0 azero azero P.Y₀ P.Y₀ g0 g0 (≤-refl _ , g0) z≤))

  Yʳ₀ : P.St W₁
  Yʳ₀ = P._⊕⟨_⟩_ (P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀)) lW₁ P.zeroD

  gR₀ : Good Yʳ₀
  gR₀ = ⨾≼ {P.d (P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀))} {P.zeroD} {P.d (P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀))} {P.zeroD} gL gL gL (z≼ P.zeroD)

  -- 实例之内: Ω_L 在两个世界里的两次折叠
  mono : H.MonoStepHs
  mono = proj₁ (ΩdObs L (fH L fL) hself aᴸ aᴸ q₀₁ ≤rf P.Act P.Act (hSt L) (hSt L) (hSt L)
                   n0 (n0 ⨾ nw ≤rf n0) one b₀ P.Y₀ Yʳ₀ g0 gR₀ (z≤ , z≼ (P.d Yʳ₀)) (sum≥ one (nl (λ _ → n1 ⨾ n0))))

  -- 跨实例: 实例 L+1 与 L 里的同一次折叠互模拟
  module TW = Two (top⁺ (hs h)) (Lg-⊞ (hs hz) (hs h) tt lh) (⊞-fst (hs hz) (hs h)) L lL oL (λ _ q → free⊲ q fL)

  A²-R : TW.IgR H.A² H.Q.Act
  A²-R = TW.igr (λ p lW′ hw hY → TW.Step-R hY)

  y0 : TW.StR (H.P.Y₀ {W₁}) (H.Q.Y₀ {W₁})
  y0 = TW.str TW.zero-R

  XR : Sm hz H.X H.X′
  XR = TW.at (TW.Run-R (accK {(azero , hz)} (ss hself)) accᴸ (Ωd-R L fL accᴸ) ≤rf lW₁ (hsuc hself) hself A²-R (s⨾ s0 (sw s0))
                (TW.⊕-R lW₁ (TW.⊕-R lW₁ y0 (TW.Step-R y0)) TW.zero-R))
             ≤rf (z⊲ᴮ (top⁺ (hs h))) (z⊲ᴮ L) lW₁

  change : H.ChangeHs
  change = sum-R′ accᴸ XR (≤-refl b₀)

  grow : asuc (T⁺ h lh) ≤ T⁺ (hs h) lh
  grow = H.hs-reduce change mono
```

## §4 ℕ-极限一步

`Upto f n`: $f(0),\dots,f(n)$ 都不含 Ω-极限. 第 $n$ 段的比较只读到前 $n$ 段的节点 (状态 `Rp n`) 与第 $n$ 段本身.

```agda
Upto : (ℕ → Ht) → ℕ → Set
Upto f n = ∀ m → m ≤ℕ n → Free (f m)

module LimF (f : ℕ → Ht) (lf : LgB (hl f)) where
  module HL = Hl f lf

  Λ′ : Ht
  Λ′ = top⁺ (hl f)
  l′ : LgB Λ′
  l′ = Lg-⊞ (hs hz) (hl f) tt lf
  o′ : ∀ {w} → hs hz ⊲[ w ] Λ′
  o′ = ⊞-fst (hs hz) (hl f)

  t₀ : hz ⊲[ W₁ ] Λ′
  t₀ = z⊲ᴮ Λ′

  open RelP Λ′ l′ o′ {W₁} lW₁ t₀
  open NodeP Λ′ l′ o′ {W₁} lW₁ t₀

  fH : ∀ k → Free k → Fin k
  fH hz _ = tt
  fH (hs b) x = fH b x
  fH (hl g) x = λ n → fH (g n) (x n)
  fH (hΩ _ _) ()

  z≼ : ∀ Δ → P.zeroD ≼ Δ
  z≼ Δ {t} tm = r0 t

  g0 : Good P.Y₀
  g0 = z≼ P.zeroD

  gL : Good (P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀))
  gL = ⨾≼ {P.d P.Y₀} {P.Stp P.Y₀} {P.d P.Y₀} {P.Stp P.Y₀} g0 g0 g0
         (proj₂ (hSt Λ′ n0 n0 azero azero P.Y₀ P.Y₀ g0 g0 (≤-refl _ , g0) z≤))

  -- Rp 的前 m 段的状态自洽: 每一步是层 hl f 上一个常数分支的节点, 子层 f(j) 不含 Ω-极限
  gRp : ∀ m → (∀ j → suc j ≤ℕ m → Free (f j)) → Good (proj₂ (HL.Rp m))
  gRp zero fs = gL
  gRp (suc m) fs =
    ⨾≼ {P.d (proj₂ (HL.Rp m))} {P.Run accᴸ (HL.Fi m) q₀₁ lW₁ hself P.Act (proj₁ (HL.Rp m)) (proj₂ (HL.Rp m))}
       {P.d (proj₂ (HL.Rp m))} {P.Run accᴸ (HL.Fi m) q₀₁ lW₁ hself P.Act (proj₁ (HL.Rp m)) (proj₂ (HL.Rp m))}
       ih ih ih
       (nodeSelf (sl m hself) (fH (top⁺ (f m)) (free-top (f m) (fs m ≤ℕ-refl))) q₀₁ hself P.Act (hSt Λ′) (proj₁ (HL.Rp m)) (proj₂ (HL.Rp m)) ih)
    where
    ih : Good (proj₂ (HL.Rp m))
    ih = gRp m (λ j le → fs j (≤ℕ-trans le (n≤1+n m)))

  oneβ : ∀ n → one ≤ HL.N.β n
  oneβ zero = sum≥ one (nl (λ _ → n1 ⨾ n0))
  oneβ (suc n) = ≤-trans (oneβ n) (sum≥ (HL.N.β n) (HL.d n))

  module M (n : ℕ) (fs : Upto f n) where
    module N = HL.N n

    fn : Free (top⁺ (f n))
    fn = free-top (f n) (fs n ≤ℕ-refl)

    Yʳ : P.St W₁
    Yʳ = P._⊕⟨_⟩_ (proj₂ (HL.Rp n)) lW₁ P.zeroD

    gRn : Good (proj₂ (HL.Rp n))
    gRn = gRp n (λ j le → fs j (≤ℕ-trans (n≤1+n j) le))

    gR : Good Yʳ
    gR = ⨾≼ {P.d (proj₂ (HL.Rp n))} {P.zeroD} {P.d (proj₂ (HL.Rp n))} {P.zeroD} gRn gRn gRn (z≼ P.zeroD)

    -- 实例 Λ′ 之内: 层 f(n)+1 的 Ω 在两个世界里的两次折叠
    monoL : TΛ-in Λ′ l′ o′ N.L N.hk ≤ sum N.β N.X
    monoL = proj₁ (ΩdObs N.L (fH N.L fn) N.hk aᴸ aᴷ q₀₁ ≤rf P.Act N.A² (hSt N.L) (hSt N.L) (hSt N.L)
                     n0 (n0 ⨾ nw ≤rf n0) one N.β P.Y₀ Yʳ g0 gR (z≤ , z≼ (P.d Yʳ)) (oneβ n))

    -- 跨实例 (change′) 再实例之内
    mono : N.MonoHl
    mono = ≤-trans (proj₁ (change′ N.L (Lg-⊞ (hs hz) (f n) tt (proj₂ lf n)) (⊞-fst (hs hz) (f n)) fn Λ′ l′ o′ N.hk)) monoL

  grow : ∀ n → Upto f n → asuc (T⁺ (f n) (proj₂ lf n)) ≤ T⁺ (hl f) lf
  grow n fs = HL.N.hl-reduce n (M.mono n fs)

upto-all : ∀ (f : ℕ → Ht) → (∀ m → Free (f m)) → ∀ n → Upto f n
upto-all f ff n m _ = ff m
```

## §5 律 (b) 在不含 Ω-极限的右边上

最小世界 $w_0=(0,0)$ 里的路径 (照 `TpMonoStep.FromSteps`). 右边不含 Ω-极限时路径里没有 `hLim`, 每一步是 `SucF.grow` 或 `LimF.grow`.

```agda
w₀ : Wd₂
w₀ = azero , hz

≤s : ∀ {x y} → asuc x ≤ y → x ≤ y
≤s h = ≤-trans (≤-suc (≤-refl _)) h

fst₀F : ∀ {a b} → a ⊲[ w₀ ] b → Free b → ∀ la lb → T⁺ a la ≤ T⁺ b lb
fst₀F {a} hself fb la lb = irrF a la lb fb
fst₀F {b = hs b} (hsuc p) fb la lb = ≤-trans (fst₀F p fb la lb) (≤s (SucF.grow b lb fb))
fst₀F {b = hl f} (hlim n p) fb la lb = ≤-trans (fst₀F p (fb n) la (proj₂ lb n)) (≤s (LimF.grow f lb n (upto-all f fb n)))
fst₀F (hLim e p) () la lb

fst<₀F : ∀ {a b} → a ⊲⁺[ w₀ ] b → Free b → ∀ la lb → asuc (T⁺ a la) ≤ T⁺ b lb
fst<₀F {b = hs b} (psuc p) fb la lb = ≤-trans (s≤ (fst₀F p fb la lb)) (SucF.grow b lb fb)
fst<₀F {b = hl f} (plim n p) fb la lb = ≤-trans (s≤ (fst₀F p (fb n) la (proj₂ lb n))) (LimF.grow f lb n (upto-all f fb n))
fst<₀F (pLim e p) () la lb

-- 接口的 (b) 两条, 限于右边不含 Ω-极限
fstF : ∀ a la b lb → Free b → a ⊑ b → T⁺ a la ≤ T⁺ b lb
fstF a la b lb fb p = fst₀F (p {w₀}) fb la lb

fst<F : ∀ a la b lb → Free b → a ⊏ b → asuc (T⁺ a la) ≤ T⁺ b lb
fst<F a la b lb fb p = fst<₀F (p {w₀}) fb la lb
```
