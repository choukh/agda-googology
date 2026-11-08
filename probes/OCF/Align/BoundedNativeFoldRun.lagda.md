# 原生 P 上动态跨底直接回灌

在原 Source 树上结构递归。指标保留到 Native t 的零层种类，分支先回灌
并更新路径界；分量的新种类按同一合法 B 比较，same/above 用原生坐标直接回灌。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeFoldRun where
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.BoundedFoldRun using (diagonal)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldIf

data Decision (B t : Cd) (A : Set) : Set where
  keep : (κ : K (Native t)) → (E (Native t) κ → A) → Decision B t A
  same : (HB (Native t) → A) → Decision B t A
  above : (i : Cd) → hs i ⊲ B → t ⊲ i → (HB (Native i) → A) → Decision B t A

pick : ∀ {B t i A} → (HB (Native i) → A) → hs i ⊲ B →
  (t ⊲ hs i) ⊎ (hs i ⊲ t) → Decision B t A
pick to p (inj₂ q) = keep (along q) (λ c → to (fr-along q c))
pick to p (inj₁ hself) = keep (inj₂ tt) to
pick to p (inj₁ (hsuc hself)) = same to
pick to p (inj₁ (hsuc q@(hsuc _))) = above _ p q to
pick to p (inj₁ (hsuc q@(hlim _ _))) = above _ p q to
pick to p (inj₁ (hsuc (hLim {κ = ()} _ _)))

decide : ∀ {B t A} → t ⊲ B → LgB B → Class B A → Decision B t A
decide {t = t} pt lB (base κ to fr a b) = keep (base-kind t κ) (λ e → to (base-fr t κ e))
decide pt lB (rank i pi to fr a b) = pick to pi (cmpB pi pt tt lB)

fold : ∀ B → LgB B → ∀ t → t ⊲ B → (h : HB Source) → Path B h → HB (Native t)
fold B lB t pt hz p = hs hz
fold B lB t pt (hs h) p = Ops.repeat (Native t) (fold B lB t pt h p)
fold B lB t pt (hl f) p = hl (λ n → fold B lB t pt (f n) (p n))
fold B lB t pt (hΩ (inj₁ _ , inj₁ ()) g) p
fold B lB t pt (hΩ (inj₁ _ , inj₂ _) g) (ev , pg) =
  hΩ (base-kind t (inj₂ tt)) (λ c →
    let e = base-fr t (inj₂ tt) c
        ad = adm-sh e lB
    in fold (nxt₀ B (sh₀ B e) ad) (lg-nx ad lB) t (⊲ᴮ-tr pt (nx-up ad))
      (g (sh₀ B e)) (pg (sh₀ B e) ad))
fold B lB t pt (hΩ (inj₂ c , κ) g) (ev , pg)
  with decide pt lB (raise ev (classify c κ))
... | keep κ′ fr = hΩ κ′ (λ e → fold B lB t pt (g (fr e)) (pg (fr e) tt))
... | same to = diagonal
  (λ e → fold B lB t pt (g (to e)) (pg (to e) tt))
  (λ e → fold B lB t pt (g (to e)) (pg (to e) tt))
... | above i pi ti to = diagonal
  (λ e → fold B lB i (⊲ᴮ-tr (hsuc hself) pi) (g (to e)) (pg (to e) tt))
  (λ e → fold B lB t pt (g (to e)) (pg (to e) tt))

instance-native : NativeFold
instance-native = record { fold = fold }
```

运行器实际定义完成，不以接口假设代替。它仍未声称一般输入保合法；
也未把高层 ≤ᵛ 当作下降后的值序。可数末段接 BridgeTerminal 时还须给
原生零层输出的 Lg* 证书。
