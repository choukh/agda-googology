# 布劳威尔树的 View (六): `nκ` 段, 同一条件下给出

> 不含记号. 入口 [BrwView](BrwView.lagda.md). [BrwViewOne](BrwViewOne.lagda.md) 把 `nκ` 段写成参数 `KSeg`. 这里在**同一个**条件 `HW` 下给出它, 所以第 1 层的 View 整个条件于 `HW` (`view₁`).
>
> - 读法: `kκ` 种 $\Omega$-极限, 层 $c\ge W$ 上的分支是 $x$ 抬到 $c$, 接上 $W$ 到 $c$ 之间各层的段 (`SumOneTree.Cut`), 再接 $u(c)$.
> - 值一致要的引理是 `CK`: `toB` 的世界分支用 `LayerTrOne.K` 走 $W\lhd c$, 每一段在**它自己的世界** $c'$ 里求值再用 `bw` 抬上来; `Cut` 把每一段用 `nw` 抬到 $c$, 在 $c$ 里求值. 两者之差逐段就是 `WSq` (世界稳定): 段在大世界里求值, 值不变. 所以 `CK` 的前提只有 "各层的分支 `HW`". 前缀的抬升同 `ni` 段, 用 `lift`.
> - 路径: `K` 与 `Cut` 在每一段用同一条路径 (`⊲-tr aW p`, 极限处 `tailP`), 不用搬运; 后继处一次 `⊲-idˡ`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwViewKappa where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; Cut; tailP)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; Sp; K; KR; toB)
open import OCF.Align.LayerTrRound using (S-cong; ⊲-idˡ; ≈-sym)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
open import OCF.Align.BrwViewOne
```

## §1 `K` 与 `Cut` 的值相同

```agda
κ-≈ : ∀ {W} {f g : ∀ {c} → W ⊲ c → Lg c → B₁ c} → (∀ {c} p lc → f {c} p lc ≈ g p lc) → bκ f ≈ bκ g
κ-≈ h = κ≼ (λ p lc → ≼κ p lc (proj₁ (h p lc))) , κ≼ (λ p lc → ≼κ p lc (proj₂ (h p lc)))

-- CK 只要分支世界稳定 (WSq), 不要它们遗传地 HW
module _ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) (wu : ∀ {c} p l → WSq (u {c} p l)) where
  CK  : ∀ b {a} (p : a ⊲ b) (aW : W₀ ⊲ a) (lb : Lg b) {Wt} (bW : b ⊲ Wt) (lt : Lg Wt) {x₀ : B₁ a} {c₀ : B₁ Wt} →
        x₀ ≈ c₀ → K u b p aW lb x₀ ≈ S C.self lt c₀ (Cut u b p aW lb bW)
  CKR : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} (p : a ⊲ f n) (aW : W₀ ⊲ a)
        {Wt} (bW : alim f ⊲ Wt) (lt : Lg Wt) {x₀ : B₁ a} {c₀ : B₁ Wt} → x₀ ≈ c₀ → ∀ m →
        KR u f st wl p aW x₀ m ≈
        Sp C.self lt (S C.self lt c₀ (Cut u (f n) p aW (wl n) (⊲-tr (C.lim n C.self) bW)))
           (λ m → Cut u (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW)) m
  CK b C.self aW lb bW lt e = e
  CK (asuc c) (C.suc p) aW lb bW lt {x₀} {c₀} e =
    ≈-trans (bw-≈ (C.suc C.self) _)
      (subst (λ t → S C.self lb (K u c p aW lb x₀) (u (⊲-tr aW p) lb) ≈ S t lt (S C.self lt c₀ (Cut u c p aW lb r)) (u (⊲-tr aW p) lb))
             (⊲-idˡ r)
             (wu (⊲-tr aW p) lb C.self r lb lt (CK c p aW lb r lt e)))
    where r = ⊲-tr (C.suc C.self) bW
  CK (alim f) (C.lim n p) aW (st , wl) bW lt e =
    bl-≈ (λ m → ≈-trans (bw-≈ (C.lim (m + n) C.self) _) (CKR f st wl p aW bW lt e m))
  CKR f st wl p aW bW lt e zero = CK (f _) p aW (wl _) (⊲-tr (C.lim _ C.self) bW) lt e
  CKR f st wl {n = n} p aW bW lt e (suc m) =
    CK (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) lt
       (CKR f st wl p aW bW lt e m)

module _ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) (hu : ∀ {c} p l → HW (u {c} p l)) where
  HW-Cut : ∀ b {a} (p : a ⊲ b) (aW : W₀ ⊲ a) (lb : Lg b) {Wt} (bW : b ⊲ Wt) → HW (Cut u b p aW lb bW)
  HW-Cut b C.self aW lb bW = tt
  HW-Cut (asuc c) (C.suc p) aW lb bW = HW-Cut c p aW lb _ , hu (⊲-tr aW p) lb
  HW-Cut (alim f) (C.lim n p) aW (st , wl) bW =
    HW-Cut (f n) p aW (wl n) _ ,
    (λ m → HW-Cut (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) _)
```

## §2 `nκ` 段

```agda
κseg : KSeg
κseg {W₀} {W} l x hx q zz u (hu , _) = vΩ kκ g (λ c _ → hg c) (κ-≈ brκ)
  where
  g : (c : Cd₁ {W , l} kκ) → X₁ (tg₁ {W , l} {kκ} c)
  g (c , p , lc) = nw p x ⨾ (Cut u c p q lc C.self ⨾ u (⊲-tr q p) lc)
  hg : ∀ c → Lgl₁ {tg₁ {W , l} {kκ} c} (g c)
  hg (c , p , lc) = hx , (HW-Cut u hu c p q lc C.self , hu (⊲-tr q p) lc)
  brκ : ∀ {c} (p : W ⊲ c) (lc : Lg c) →
       S C.self lc (K u c p q lc (toB l x)) (u (⊲-tr q p) lc) ≈ val₁ {c , lc} (g (c , p , lc))
  brκ {c} p lc = S-cong C.self lc (u (⊲-tr q p) lc)
    (CK u (λ p′ l′ → hw→ws (u p′ l′) (hu p′ l′)) c p q lc C.self lc (≈-sym (≈-trans (lift l lc p x hx) (bw-≈ p (toB l x)))))

open WithKappa κseg public using (vw; view₁)
```

`view₁ : BrwView Sig₁ X₁ val₁ Lgl₁`: 一切 `HW` 的第 1 层差树都有 View, 值一致对 `toB`. 条件定理 (前提 `HW`, 由 `HW-Ωx` 知可满足).
