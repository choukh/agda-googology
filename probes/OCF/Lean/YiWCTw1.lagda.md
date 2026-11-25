# 塔第 1 项那一格: 较弱链形状在 EBO 参照上

> 验收文件 (读记号). 判决: 编译定理, 无前提, 不改树、折叠、合法性; 分级实例取 `YiBAEbo.gradedᴱ` (上下文带坍缩下标 ν, 这一格要 ν = 1, 主系统的 `Below` 才成立). `YiBAEbo.Tw1Keep` 的点 (辅助系统, 替身顶结点, 精确参照 Ω₂, 上下文 ψ_1(P + ·)): P 空时较弱形状成立 (`weak-tw1`, 下标取 m = k+1), 原形状对一切 P 不成立 (`¬strong-tw1`, 即 `¬above` 的那一处).
> 不坍缩的参照 Ω₁ (κ = 0) 使全量化的 `AboveLʳ` 对一切 P 不成立 (`¬aboveʳ-tw1`, 与 `YiBAEbo.¬nodeout` 同一机制, 与链形状无关). 不给出什么: P 非空没有证也没有否定; 不涉及值. 第 1 层的自身折叠保持 `Self₁` 照 `YiGTSelf.Self.LF`, 折叠换成 `YiRBSib.ψ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWCTw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
import OCF.Lean.YiRBSib as RB
open import OCF.Lean.YiBSBase using (Rb)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiGTGen
open import OCF.Lean.YiGTUp using (up-zero)
open import OCF.Lean.YiANFam using (Pen)
open import OCF.Lean.YiNLCtx using (prefix)
open import OCF.Lean.YiGLDom using (dC; dz; dom-top)
open import OCF.Lean.YiBLFold using (Sₙ; rcₙ; route-tw1; module Aux)
import OCF.Lean.YiBLFold as BLF
open import OCF.Lean.YiVALeaf using (nzs)
open import OCF.Lean.YiTBRow using (h₁)
open import OCF.Lean.YiBALemma
open import OCF.Lean.YiBAEbo
open import OCF.Lean.YiXTIface
open import OCF.Lean.YiBAWeak
open import OCF.Lean.YiWCIface
```

## 第 1 层上 ψ_1 的自身折叠保持

第 1 层 (`j₁`) 唯一的槽位在第 0 层, 那里只读出 0, 而 0+1 ≤ 1, 所以结点一行保留 (`pen₁`).

```agda
𝟙 : E.T
𝟙 = E.𝟏 ∷ []

pen₁ : (p : Pos j₁) (κ : E.T) → GR.Nu j₁ p κ → Pen (E.cmpᵀ (E.sucT κ) 𝟙)
pen₁ (inj₂ (tt , inj₁ tt)) κ nu with rd0 nu
... | refl = inj₂ refl
pen₁ (inj₂ (tt , inj₂ ())) κ nu

module Self₁ (o : Ok j₁) (r : Rb j₁) (B : Base j₁) (t : E.T) (β : Tr⁺ j₁)
    (mb : GR.R j₁ (E.ψ 𝟙 t ∷ []) (proj₁ β)) where
  F : Tr j₁ → Tr⁺ j₁
  F x = RB.ψ j₁ o r B j₁ self β x

  LF : ∀ {a x} → GR.R j₁ a x → GR.R j₁ (E.ψ 𝟙 (t ++ a) ∷ []) (proj₁ (F x))
  LF (H.mz {x = x}) = ++[] (λ z → GR.R j₁ (E.ψ 𝟙 z ∷ []) (proj₁ (F x))) t
    (zlᴿ j₁ (λ y → proj₁ (F y)) (RB.mono j₁ o r B j₁ self β) mb x)
  LF (H.m1 {t = a} {x = x} e m) = nextψ j₁ 𝟙 t a e (F x) (LF m)
  LF (H.mL {t = a} {x = x} e m) = limψ j₁ 𝟙 t a e (proj₁ (F x)) (λ n → LF (m n))
  LF (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
    nodeψ j₁ 𝟙 t a p e (pen₁ p κ nu) nu (λ η c lc → LF (m η c lc))
  LF (H.mU {t = a} {s = b} {x = x} {c = tt} {y = y} m ch) =
    subst (λ z → GR.R j₁ (E.ψ 𝟙 z ∷ []) (proj₁ (Up zero (down {s = sS} {h = λ _ → zero} stop tt) (F x) y))) (++-assoc t a b)
      (up-zero 𝟙 (down {s = sS} {h = λ _ → zero} stop tt) (t ++ a) (F x) (LF m) ch)
  LF (H.mw m d) = weakᴿ j₁ (LF m) (RB.mono j₁ o r B j₁ self β d)
  LF (H.mc le m) = closeᴿ j₁ (app≤ν 𝟙 t le) (LF m)

top₁ : GR.R j₁ (E.ψ 𝟙 [] ∷ []) (proj₁ (Ωt j₁))
top₁ = dom-top (dC (prefix zero) zero (dz zero) (H.m1 refl H.mz))
```

## 那一格

系统与 `YiBAEbo.Tw1Keep` 相同 (两个系统的条件都取 `KeepAt`). 替身顶结点上树的链 `zᴬ` 从零树起, 第 m+1 个链点是 g(z m) 朝第 1 层、以 Ω 树为底的折叠, 与 P 无关.

```agda
module Tw1W (B : Base (tw 1)) (β : Tr⁺ j₁) (x : Tr (tw 1)) where
  KA : ∀ {a} → Aux.Stᴬ j₁ a → E.T × E.T → Set
  KA _ K = KeepAt j₁ (proj₁ K)

  KB : ∀ {a} → BLF.Main.Stᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B j₁ (suc zero) self
                 (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero)) a → E.T × E.T → Set
  KB _ K = KeepAt j₁ (proj₁ K)

  open Tw1Neg B (E.T × E.T) apE KA (E.T × E.T) apE KB
  open AuxNode β x
  open WithR _≤ᵀ_ weakᴱ limᴱ nodeᴱ zeroᴱ succᴱ embᴱ (leRᴱ {j = j₁}) genᴱ using (xtᴬ; chᴬ)
  open W gradedᴱ domsᴱ using (RefChainʳ)
  open XW gradedᴱ domsᴱ using (AboveLʳ)

  zᴬ : ℕ → Tr j₁
  zᴬ = proj₁ (chᴬ sA pᴬ gᴬ tt neᴬ)
```

P 空: 参照链第 k 项不高于树的链第 k+1 项. 第 0 项用 Ω₁ ≤ 第 1 层的 Ω 树, 之后逐项用 `Self₁`.

```agda
  chain₁ : ∀ k → GR.R j₁ (E.γT Ω₂ 𝟙 k) (zᴬ (suc k))
  chain₁ zero    = weakᴿ j₁ top₁ (◃l zero)
  chain₁ (suc k) = weakᴿ j₁ (Self₁.LF _ _ _ [] (Ωt j₁) top₁ (chain₁ k)) (◃l zero)

  weak-tw1 : RefChainʳ sysᴬ sA (𝟙 , []) pᴬ gᴬ Ω₂ (chᴬ sA pᴬ gᴬ tt neᴬ)
  weak-tw1 = (λ k → E.γT Ω₂ 𝟙 k) , proj₁ cl , proj₂ cl , λ k → suc k , chain₁ k
    where cl = collψ 𝟙 [] Ω₂ {κ = 𝟙} refl refl
```

原形状在同一处: 参照链第 0 项被迫是 Ω₁ (`collψ` 与前缀消去), 树的链第 0 项是零树 (`R-zero`).

```agda
  ¬strong-tw1 : (P : E.T) → XT.RefChain gradedᴱ domsᴱ sysᴬ sA (𝟙 , P) pᴬ gᴬ Ω₂ (chᴬ sA pᴬ gᴬ tt neᴬ) → ⊥
  ¬strong-tw1 P (γ , cω , fs , ch) = Ω≢[] (trans γ0 (R-zero j₁ (ch 0)))
    where
    Ω≢[] : E.Ωt 𝟙 ≡ [] → ⊥
    Ω≢[] ()
    γ0 : E.Ωt 𝟙 ≡ γ 0
    γ0 = ψ∷-canc P (trans (sym (proj₂ (collψ 𝟙 P Ω₂ {κ = 𝟙} refl refl) 0)) (fs 0))
```

全量化的 `AboveLʳ` 也对不坍缩的参照要余尾 ω; Ω₁ 在 ψ_1 下保持余尾 Ω₁ (`keepψ`).

```agda
  ¬aboveʳ-tw1 : (P : E.T) → AboveLʳ sysᴬ keepᴬ Dᴬ xtᴬ → ⊥
  ¬aboveʳ-tw1 P ab = cω≢cΩ (trans (sym (proj₁ (proj₂ r))) (proj₁ (keepψ 𝟙 P t₁ {κ = []} refl tt)))
    where r = ab sA (𝟙 , P) keep-tw1 pᴬ {t = t₁} {κ = []} gᴬ tt refl (GR.c0 refl) (hRᴬ t₁ (λ _ → refl)) neᴬ self
```

树的链与主系统的底、底值、左项都无关 (辅助状态的底是 `B₀`, 链只用它): 上下文前缀 P 只能靠链点往后挪来吸收.

```agda
zᴬ-free : ∀ (B : Base (tw 1)) (β : Tr⁺ j₁) (x : Tr (tw 1)) (B′ : Base (tw 1)) (β′ : Tr⁺ j₁) (x′ : Tr (tw 1)) (k : ℕ)
  → Tw1W.zᴬ B β x k ≡ Tw1W.zᴬ B′ β′ x′ k
zᴬ-free B β x B′ β′ x′ k = refl
```
