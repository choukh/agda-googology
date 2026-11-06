# SameV (二): 同底折叠沿配对单调

> 不含记号. 入口 [SameV](SameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 模块参数: `uipC` (`Cd` 上的 UIP, 只经 ValC 的 `monoΦ` 用到, 本篇自己的比较不用它), 配对 `Mt`, 地板律 `tp` (配对的层的地板相关). 只导入 stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValC*` (只用, 不改), [SameVRel](SameVRel.lagda.md).
>
> **定理 `crossΦ`.** 左边第 $m$ 层, 右边第 $m'$ 层; 目标 $t\lhd m$, $t'\lhd m'$, $t\sim t'$; 界 $b\preceq b'$ (`Bx`: 右边值合法, 在地板之上); 输入 $x\preceq y$, 右边值合法 ⟹ $\Phi_{m\to t,b}\,x\preceq\Phi_{m'\to t',b'}\,y$.
>
> **决定不变.** 结点对 $(k,k')$ 配对, 目标对 $(t,t')$ 配对. 由 `~s`, `~pp`, `~fun`, 左边的决定 (留 / 同层 / 在上) 决定右边的决定, 不一致的组合由没有真回路排除. 这里**不用** UIP: 两边的视图 `DV` 的层与目标是四个不同的变量, 对 `ds` 的模式匹配不用消去自反方程.
>
> **`≼Ω` 一侧不用路线引理的跨层版本.** 归纳假设接到右边的一支, 再用**同层**的 `monoΦ` 接到整个结点. 路线引理只在同层出现.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Lean.SameVRel as SR
module OCF.Lean.SameVMono (I : CRwIf) (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) (Mt : SR.Match I) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
open import OCF.Lean.ValCBase I
open import OCF.Lean.ValCMono I uipC
open SR.X I Mt public
```

## §1 地板律, 定理

```agda
module Thm (tp : ∀ {k k′} → k ~ k′ → LE k k′ (top b⊥ k) (top b⊥ k′)) where

  mutual
    crossΦ : ∀ {m m′} (w : AP m) (a : Acc b⊥ m) (a′ : Acc b⊥ m′) (lm : LgB m) (lm′ : LgB m′)
             {t t′} (pt : t ⊲ m) (pt′ : t′ ⊲ m′) → t ~ t′ → {b : H t} {b′ : H t′} → Ch.Bx t t′ b b′ →
             ∀ {x} y → MoAt m′ y → LE m m′ x y → LE t t′ (G a lm t pt b x) (G a′ lm′ t′ pt′ b′ y)
    crossΦ w a a′ lm lm′ {t} {t′} pt pt′ ev B y my R2.z≼ = Lm.one≼ t t′ (one≤ a′ lm′ t′ pt′ _ y)
    crossΦ w a a′ lm lm′ {t} {t′} pt pt′ ev B {hs x} (hs y) my (R2.s≼s p) =
      R2.l≼l (λ n → n) (L.idInc t) (Lm.mul≼ t t′ (crossΦ w a a′ lm lm′ pt pt′ ev B y my p))
    crossΦ w a a′ lm lm′ pt pt′ ev B (hs y) my (R2.≼s p) =
      R2.≼l 0 (crossΦ w a a′ lm lm′ pt pt′ ev B y my p)
    crossΦ w a a′ lm lm′ {t} {t′} pt pt′ ev B {hl f} (hl g) my (R2.l≼l σ i h) =
      R2.l≼l σ i (Lm.Σ≼ t t′ _ _ σ i (λ n → crossΦ w a a′ lm lm′ pt pt′ ev B (g (σ n)) (my (σ n)) (h n)))
    crossΦ w a a′ lm lm′ {t} {t′} pt pt′ ev B (hl g) my (R2.≼l n p) =
      R2.≼l n (Lm.tr≼ t t′ (crossΦ w a a′ lm lm′ pt pt′ ev B (g n) (my n) p) (Ac0.Σ-ge t′ _ n))
    crossΦ {m} {m′} w a a′ lm lm′ {t} {t′} pt pt′ ev {b} {b′} B@(mb′ , tb , bb) (hΩ κ g′) my (R2.≼Ω c bd mc p) =
      Lm.tr≼ t t′ (crossΦ w a a′ lm lm′ pt pt′ ev B (g′ (toK m′ κ c)) (proj₂ (moConv g′ my) c mc) p)
        (monoΦ (apWf m′) a′ a′ lm′ lm′ pt′ pt′ (Ac0.bnd-refl t′ mb′ tb) (hΩ κ g′) (proj₂ (moConv g′ my) c mc) my
           (Rel.≤Ω c (→lle m′ κ c _ bd) (→lmo m′ κ c mc) (L.≤-refl m′ _)))
    crossΦ {m} {m′} w (acc rs) (acc rs′) lm lm′ {t} {t′} pt pt′ ev {b} {b′} B {hΩ κ g} (hΩ κ′ g′) my (R2.Ω≼Ω e h) =
      ΦΩ rs lm pt b κ g (λ z → LE t t′ z (G (acc rs′) lm′ t′ pt′ b′ (hΩ κ′ g′)))
        (ΦΩ rs′ lm′ pt′ b′ κ′ g′
          (λ z → LE t t′ (caseDc (pick S⊥ (toK m κ) (pK m κ) (cmpB (pK m κ) pt tt lm)) (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b)) z)
          (mΩ w rs rs′ lm lm′ pt pt′ ev B g g′ (pK m κ) (pK m′ κ′) (toK m κ) (toK m′ κ′) e
             (dvK κ pt lm) (dvK κ′ pt′ lm′) (moConv g′ my)
             (λ d d′ md r → h d d′ md (→ll m κ _ r))))

    mΩ : ∀ {m m′} (w : AP m) rs rs′ (lm : LgB m) (lm′ : LgB m′) {t t′} (pt : t ⊲ m) (pt′ : t′ ⊲ m′) → t ~ t′ →
         {b : H t} {b′ : H t′} → Ch.Bx t t′ b b′ →
         ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m′) κ′ → H m′) {k k′} (pk : hs k ⊲ m) (pk′ : hs k′ ⊲ m′)
         (to : H k → E (T m) κ) (to′ : H k′ → E (T m′) κ′) → k ~ k′ → ∀ {d d′} →
         DV k t to pk d → DV k′ t′ to′ pk′ d′ → MoN m′ k′ to′ g′ →
         (∀ c c′ → MoAt k′ c′ → LE k k′ c c′ → LE m m′ (g (to c)) (g′ (to′ c′))) →
         LE t t′ (caseDc d (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b))
                 (caseDc d′ (Kc rs′ lm′ g′ pt′ b′) (Sc rs′ lm′ g′ pt′ b′) (Ac rs′ lm′ g′ pt′ b′))
    mΩ w rs rs′ lm lm′ {t} {t′} pt pt′ ev {b} {b′} B g g′ pk pk′ to to′ ev₂ (dk κ₁ e₁ fr₁ ft₁ u₁) (dk κ₂ e₂ fr₂ ft₂ u₂) My H′ =
      keepX κ₁ κ₂ e₁ e₂ fr₁ fr₂ ft₁ ft₂ ev₂ (λ c → G (acc rs) lm t pt b (g (to c))) (λ c → G (acc rs′) lm′ t′ pt′ b′ (g′ (to′ c)))
        (λ c c′ mc r → crossΦ w (acc rs) (acc rs′) lm lm′ pt pt′ ev B (g′ (to′ c′)) (proj₂ My c′ mc) (H′ c c′ mc r))
    mΩ w rs rs′ lm lm′ pt pt′ ev B g g′ pk pk′ to to′ ev₂ (dk κ₁ e₁ fr₁ ft₁ u₁) ds My H′ = ⊥-elim (nos (~s ev₂ ev u₁))
    mΩ w rs rs′ lm lm′ pt pt′ ev B g g′ pk pk′ to to′ ev₂ (dk κ₁ e₁ fr₁ ft₁ u₁) (da q′ pp′) My H′ = ⊥-elim (nos′ (~s ev₂ ev u₁) q′)
    mΩ w rs rs′ lm lm′ pt pt′ ev B g g′ pk pk′ to to′ ev₂ ds (dk κ₂ e₂ fr₂ ft₂ u₂) My H′ =
      ⊥-elim (nos (subst (λ z → hs z ⊲ _) (~fun ev₂ ev) u₂))
    mΩ {m} {m′} w rs rs′ lm lm′ {t} {t′} pt pt′ ev {b} {b′} B g g′ pk pk′ to to′ ev₂ ds ds My H′ =
      Ch.chX-hl t t′ (ch (acc rs) lm pt g to) (ch (acc rs′) lm′ pt′ g′ to′) B
        (kpG (apWf m′) (acc rs′) lm′ pt′ g′ to′ My)
        (λ {b₁} {b₂} (m2 , t2 , le) → crossΦ w (acc rs) (acc rs′) lm lm′ pt pt′ ev (m2 , t2 , le) (g′ (to′ b₂)) (proj₂ My b₂ m2) (H′ b₁ b₂ m2 le))
    mΩ w rs rs′ lm lm′ pt pt′ ev B g g′ pk pk′ to to′ ev₂ ds (da q′ pp′) My H′ =
      ⊥-elim (noPP (subst (λ z → Pp _ z) (~fun ev₂ ev) pp′) hself)
    mΩ w rs rs′ lm lm′ pt pt′ ev B g g′ pk pk′ to to′ ev₂ (da q pp) (dk κ₂ e₂ fr₂ ft₂ u₂) My H′ =
      ⊥-elim (noPP (~pp ev ev₂ pp) (⊏⊑ u₂))
    mΩ w rs rs′ lm lm′ pt pt′ ev B g g′ pk pk′ to to′ ev₂ (da q pp) ds My H′ =
      ⊥-elim (noPP (~pp ev ev₂ pp) hself)
    mΩ {m} {m′} (ap hw) rs rs′ lm lm′ {t} {t′} pt pt′ ev {b} {b′} B g g′ {k} {k′} pk pk′ to to′ ev₂ (da q pp) (da q′ pp′) My H′ =
      crossΦ (hw (s⊲→Pp pk)) (rs b⊥ k (lt pk)) (rs′ b⊥ k′ (lt pk′)) (lg↓ pk lm) (lg↓ pk′ lm′) q q′ ev B
        (hl (chain (top b⊥ k′) (ch (acc rs′) lm′ (⊏⊑ pk′) g′ to′)))
        (moCh (apWf m′) (acc rs′) lm′ (⊏⊑ pk′) g′ to′ My)
        (Ch.chX-hl k k′ (ch (acc rs) lm (⊏⊑ pk) g to) (ch (acc rs′) lm′ (⊏⊑ pk′) g′ to′)
           (Mo-top k′ , L.≤-refl k′ _ , tp ev₂)
           (kpG (apWf m′) (acc rs′) lm′ (⊏⊑ pk′) g′ to′ My)
           (λ {b₁} {b₂} (m2 , t2 , le) → crossΦ (ap hw) (acc rs) (acc rs′) lm lm′ (⊏⊑ pk) (⊏⊑ pk′) ev₂ (m2 , t2 , le) (g′ (to′ b₂)) (proj₂ My b₂ m2) (H′ b₁ b₂ m2 le)))
```

## 结论 (按档)

- **[条件定理, 条件: `Cd` 上的 UIP (经 ValC 的 `monoΦ`), 地板律 `tp`]** **`Thm.crossΦ`**, `Thm.mΩ`: 同底折叠沿配对单调, 对一切配对 `Mt`.
