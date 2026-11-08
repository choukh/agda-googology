# 任意原生可数高度内的回灌世界

固定一个真实 Native c 分量，在其内部沿 rank 路径放入任意合法原始坐标。
只更新自然数 sup 的槽；不在整个 Source 的不可判定 Cd 分量上作单槽更新。
本篇覆盖任意 Cd 高度，不限于有限自然数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeLegalWorld where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLay using (_⊕L_; upL)
open import OCF.Lean.LHRecLeg using (w₀L; lw₀L; Ctx; here; viaS; viaL; pw; bdTo)
open import OCF.Lean.BoundedContextRun using (compose; path-context)
open import Data.Sum using (inj₂)
open import OCF.Align.BoundedDescentValueBridge using (Native; along; to-along)

canonical : ∀ c → Wd (Native c)
canonical c = w₀L (ls lz ⊕L upL lz c)
canonical-legal : ∀ c → LgW (Native c) (canonical c)
canonical-legal c = lw₀L (ls lz ⊕L upL lz c)

plug : (f : ℕ → Cd) → ∀ n → Wd (Native (f n)) → ∀ j → Wd (Native (f j))
plug f zero v zero = v
plug f zero v (suc j) = canonical (f (suc j))
plug f (suc n) v zero = canonical (f zero)
plug f (suc n) v (suc j) = plug (λ j → f (suc j)) n v j
plug-own : ∀ f n v → plug f n v n ≡ v
plug-own f zero v = refl
plug-own f (suc n) v = plug-own (λ j → f (suc j)) n v
plug-legal : ∀ f n v → LgW (Native (f n)) v → ∀ j → LgW (Native (f j)) (plug f n v j)
plug-legal f zero v lv zero = lv
plug-legal f zero v lv (suc j) = canonical-legal (f (suc j))
plug-legal f (suc n) v lv zero = canonical-legal (f zero)
plug-legal f (suc n) v lv (suc j) = plug-legal (λ j → f (suc j)) n v lv j

world : ∀ {i c : Cd} → hs i ⊲ c → HB (Native i) → Wd (Native c)
world {i} hself x = canonical i , x
world (hsuc p) x = world p x , hz
world {c = hl f} (hlim n p) x = plug f n (world p x)

world-legal : ∀ {i c : Cd} (p : hs i ⊲ c) x → LgB x → LgW (Native c) (world p x)
world-legal {i} hself x lx = canonical-legal i , lx
world-legal (hsuc p) x lx = world-legal p x lx , tt
world-legal {c = hl f} (hlim n p) x lx = plug-legal f n (world p x) (world-legal p x lx)

pw-compose : ∀ {T S R} (a : Ctx T S) (b : Ctx S R) W →
  pw (compose a b) W ≡ pw b (pw a W)
pw-compose a here W = refl
pw-compose a (viaS b) W = cong proj₁ (pw-compose a b W)
pw-compose a (viaL b n) W = cong (λ v → v n) (pw-compose a b W)

world-project : ∀ {i c : Cd} (p : hs i ⊲ c) x →
  pw (path-context (ls lz) lz p) (world p x) ≡ (canonical i , x)
world-project hself x = refl
world-project (hsuc p) x = trans
  (pw-compose (viaS here) (path-context (ls lz) lz p) (world p x , hz))
  (world-project p x)
world-project {c = hl f} (hlim n p) x = trans
  (pw-compose (viaL here n) (path-context (ls lz) lz p) (plug f n (world p x)))
  (trans (cong (pw (path-context (ls lz) lz p)) (plug-own f n (world p x)))
    (world-project p x))

admitted : ∀ {i c : Cd} (p : hs i ⊲ c) x →
  Bd (Native c) (along p) (to-along p x) (world p x)
admitted {i} p x = bdTo (path-context (ls lz) lz p) (inj₂ tt) selected
  where
  selected : Bd (Native (hs i)) (inj₂ tt) x
    (pw (path-context (ls lz) lz p) (world p x))
  selected rewrite world-project p x = hself
```

world-legal 和 admitted 给出实际合法反馈坐标的可入实例；没有另加全局
世界相干前提。它们还不证明运行器保第一位置或输出合法；后续应在固定
分量的局部 LgB 下使用此世界取出分支合法性。

下面直接按原生种类递归给出所有合法坐标的世界，包含零层旧 Ω；
它可用于固定分量的 LgB 分支取出，不要求 Source 的全积世界截面。

```agda
open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Data.Sum using (inj₁)

LegalCoordinate : ∀ c κ → E (Native c) κ → Set
LegalCoordinate hz (inj₁ ()) e
LegalCoordinate hz (inj₂ _) e = LgB e
LegalCoordinate (hs c) (inj₁ κ) e = LegalCoordinate c κ e
LegalCoordinate (hs c) (inj₂ _) e = LgB e
LegalCoordinate (hl f) (n , κ) e = LegalCoordinate (f n) κ e

coordinate-world : ∀ c κ → E (Native c) κ → Wd (Native c)
coordinate-world hz (inj₁ ()) e
coordinate-world hz (inj₂ _) e = tt , e
coordinate-world (hs c) (inj₁ κ) e = coordinate-world c κ e , hz
coordinate-world (hs c) (inj₂ _) e = canonical c , e
coordinate-world (hl f) (n , κ) e = plug f n (coordinate-world (f n) κ e)

coordinate-world-legal : ∀ c κ e → LegalCoordinate c κ e →
  LgW (Native c) (coordinate-world c κ e)
coordinate-world-legal hz (inj₁ ()) e l
coordinate-world-legal hz (inj₂ _) e l = tt , l
coordinate-world-legal (hs c) (inj₁ κ) e l = coordinate-world-legal c κ e l , tt
coordinate-world-legal (hs c) (inj₂ _) e l = canonical-legal c , l
coordinate-world-legal (hl f) (n , κ) e l = plug-legal f n _ (coordinate-world-legal (f n) κ e l)

coordinate-admitted : ∀ c κ e → Bd (Native c) κ e (coordinate-world c κ e)
coordinate-admitted hz (inj₁ ()) e
coordinate-admitted hz (inj₂ _) e = hself
coordinate-admitted (hs c) (inj₁ κ) e = coordinate-admitted c κ e
coordinate-admitted (hs c) (inj₂ _) e = hself
coordinate-admitted (hl f) (n , κ) e rewrite plug-own f n (coordinate-world (f n) κ e) =
  coordinate-admitted (f n) κ e

branch-legal : ∀ c κ (g : E (Native c) κ → HB (Native c)) →
  LgB (hΩ κ g) → ∀ e → LegalCoordinate c κ e → LgB (g e)
branch-legal c κ g lg e le = proj₂ lg (coordinate-world-legal c κ e le) (coordinate-admitted c κ e)
```
