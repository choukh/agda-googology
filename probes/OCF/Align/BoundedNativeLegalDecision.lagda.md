# 实际跨底决定的合法取枝

实际 decide 的三种输出均保持“原分量分支可以取出”的证书。保留种类的
坐标先由合法目标世界向上下文投影；这里没有把任意原始坐标当作合法。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeLegalDecision where
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLeg using (lgpw; bdFr)
open import OCF.Lean.BoundedContextRun using (path-context)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun using (Decision; keep; same; above; pick; decide)
open import OCF.Align.BoundedNativeLegalWorld
open import OCF.Align.BoundedNativeLegalClass

base-fr-legal : ∀ t κ e → LegalCoordinate t (base-kind t κ) e →
  LegalCoordinate hz κ (base-fr t κ e)
base-fr-legal hz κ e l = l
base-fr-legal (hs t) κ e l = base-fr-legal t κ e l
base-fr-legal (hl f) κ e l = base-fr-legal (f 0) κ e l

along-fr-legal : ∀ {i t} (p : hs i ⊲ t) e → LegalCoordinate t (along p) e →
  LgB (fr-along p e)
along-fr-legal {i} {t} p e le = lgB⊲
  (bdFr ctx (inj₂ tt) (coordinate-admitted t (along p) e))
  (proj₁ projected) (proj₂ projected)
  where
  ctx = path-context (ls lz) lz p
  projected = lgpw ctx (coordinate-world-legal t (along p) e le)

Allowed : ∀ {B t A} → (A → Set) → Decision B t A → Set
Allowed {t = t} Q (keep κ fr) = ∀ e → LegalCoordinate t κ e → Q (fr e)
Allowed Q (same to) = ∀ e → LgB e → Q (to e)
Allowed Q (above i pi ti to) = ∀ e → LgB e → Q (to e)

pick-allowed : ∀ {B t i A} (Q : A → Set) (to : HB (Native i) → A)
  (p : hs i ⊲ B) (q : (t ⊲ hs i) ⊎ (hs i ⊲ t)) →
  (∀ e → LgB e → Q (to e)) → Allowed Q (pick to p q)
pick-allowed Q to p (inj₂ q) h e le = h (fr-along q e) (along-fr-legal q e le)
pick-allowed Q to p (inj₁ hself) h e le = h e le
pick-allowed Q to p (inj₁ (hsuc hself)) h = h
pick-allowed Q to p (inj₁ (hsuc q@(hsuc _))) h = h
pick-allowed Q to p (inj₁ (hsuc q@(hlim _ _))) h = h
pick-allowed Q to p (inj₁ (hsuc (hLim {κ = ()} _ _))) h

decide-allowed : ∀ {B t A} (Q : A → Set) (pt : t ⊲ B) lB cl →
  Supported Q cl → Allowed Q (decide pt lB cl)
decide-allowed {t = t} Q pt lB (base κ to fr a b) h e le =
  h (base-fr t κ e) (base-fr-legal t κ e le)
decide-allowed Q pt lB (rank i pi to fr a b) h =
  pick-allowed Q to pi (cmpB pi pt tt lB) h

component-allowed : ∀ {B t} c κ (pc : c ⊲ B) (pt : t ⊲ B) lB →
  Allowed (LegalCoordinate c κ) (decide pt lB (raise pc (classify c κ)))
component-allowed c κ pc pt lB = decide-allowed (LegalCoordinate c κ) pt lB _
  (raise-supported (LegalCoordinate c κ) pc _ (classify-supported c κ))
```

这覆盖任意 c、B、t 及实际分类器的全部决定，并未替换运行器。
其前提由真实分量路径 c⊲B、目标路径 t⊲B 与公共界合法性提供。
尚未证明输出第一位置步进；尤其 ℕ 极限仍须把原分量步进送过原 fold。

将结论直接用于原分量 Ω 的真实分支；反馈坐标证书来自实际合法输出
时，此定理可供递归调用使用，而不需要为整个 Source 构造世界。

```agda
allowed-map : ∀ {B t A} (Q R : A → Set) (d : Decision B t A) →
  (∀ e → Q e → R e) → Allowed Q d → Allowed R d
allowed-map Q R (keep κ fr) h p e le = h (fr e) (p e le)
allowed-map Q R (same to) h p e le = h (to e) (p e le)
allowed-map Q R (above i pi ti to) h p e le = h (to e) (p e le)

component-branches : ∀ {B t} c κ (g : E (Native c) κ → HB (Native c)) →
  LgB (hΩ κ g) → (pc : c ⊲ B) → (pt : t ⊲ B) → (lB : LgB B) →
  Allowed (λ e → LgB (g e)) (decide pt lB (raise pc (classify c κ)))
component-branches c κ g lg pc pt lB =
  allowed-map (LegalCoordinate c κ) (λ e → LgB (g e)) _
    (branch-legal c κ g lg) (component-allowed c κ pc pt lB)
```

component-branches 的 LgB 前提可取现有 Lg-flL 所给的每个真实分量地板；
递归下降时也由本定理取出的分支证书继续满足。这不是输出 LgB 的证明：
后者还需要保留 Ω 的位置单调和所有 ℕ 极限的相邻项位置关系。
