# 接线变体: 较弱链形状接到换基折叠的 EBO 终点

> 验收文件 (读记号). 判决: 编译定理, 不改 `YiWREnd`, 不改树、折叠、合法性. `Wireʳ`: `YiWREnd.Wire` 的 `aboveᴱ` 换成较弱形状 (`ChainRelʳ`: 参照链第 k 项不高于树的链的某一项), 终点 `ebo-endʳ`; 原 `ChainRel` 与 `LowSlot` 都推出它 (`chain→ʳ`, `slot→ʳ`). 树的链从第 0 个链点起 (node⁺ 自己的链, `xt⁰`) 与从第 1 个起 (`ptᶻ`) 两种写法的较弱形状等价 (`to⁰`, `from⁰`, 用 `R-zero`), 所以 `YiWRZero` 里 "链从第 1 项起" 那一步不再需要 (`ebo-endʳ⁰`).
> 较弱形状拆成第 0 项 `BaseW` 与步 `StepW` (`bs→ʳ⁰`); `LowSlot` 推出两者 (`slot→base`, `slot→step`); 在 `Inv₁` 之下第 0 项只要槽位层上的 Leaf, 逐点, 不经 `LowSlot` (`base₁`). 不给出什么: `StepW` 仍要槽位层对上下文的支配, 本文没有证也没有否定; 出口条件对新推导另陈述 (`ExitOn`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWCWire where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; sym; trans; cong)

open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiRWOps using (iter; Tr⁺)
open import OCF.Lean.YiRWPath using (Ok; z≤; posW)
open import OCF.Lean.YiRWFold using (Base; Keep; kp; node⁺)
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiBSBase using (Rb)
open import OCF.Lean.YiBLFold using (wfL)
open import OCF.Lean.YiGIBlock using (slTᵍ)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
open import OCF.Lean.YiKVRel using (_⊴_)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.Value using (_≼_; l≼; ≼-trans)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiMENote using (cofψΩ; fsnψΩ)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiGTGen using (weakenᴿ; closeᴿ; Ω≤ψ)
open import OCF.Lean.YiBALemma using (R-zero)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiQDIface using (module QD)
open import OCF.Lean.YiQDFold using (module AddR)
open import OCF.Lean.YiXTIface using (module XT; module Rest)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiGIInst using (exitᵍ; gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiGIEnd using (hs; reference)
open import OCF.Lean.YiGLDom using (dom-top; dom-keel)
open import OCF.Lean.YiWRZero
open import OCF.Lean.YiWREnd
open import OCF.Lean.YiWCIface
open import OCF.Lean.YiWCTw1 using (top₁)
open import OCF.Lean.YiBAEbo using (j₁)
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiRWPath using (Ok-tw)
open import OCF.Lean.YiBSBase using (rb-tw)
open ExSuff gradedᵍ domsᵍ using (Exit₀; Keel⁻)

γ≢[] : ∀ b μ k → E.γT b μ k ≡ [] → ⊥
γ≢[] b μ zero    ()
γ≢[] b μ (suc k) ()

pt⁰ : ∀ {a} (s : Stᶻ a) (p : Pos a) (g : Br a p → Tr a) → ℕ → Br a p
pt⁰ {a} s p g k = iter (stepPt s p g) (fromBr a p zero) k
```

## 较弱形状与两种链

参数同 `YiWREnd.Wire`; 非结点的五条出口直接用 `Wire.restᴱ`.

```agda
module Wireʳ (Inv : ∀ {a} → Stᶻ a → E.T → Set)
    (inv-zero : ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) (β : Tr⁺ zero) {K} → Inv (o , r , B , β) K → GR.R zero (E.ψ [] K ∷ []) (proj₁ β))
    (inv-step : ∀ {a} (s : Stᶻ a) K → Inv s K → (c : CH a) → ∀ {t x} → GR.R a t x
              → GR.R zero (apᴱ K t) (proj₁ (Φᶻ s x)) → Inv (stepᶻ s c x) (K ++ t))
    (inv-root : ∀ n → Inv (rootᴮ n) []) where
  module Wi = Wire Inv inv-zero inv-step inv-root
  open Zero gradedᴮ domsᴮ E.T apᴱ Inv
  open WithRules _≤ᵀ_ weakᴮ limᴮ nodeᴮ zeroᴮ succᴮ embᴮ leRᴮ genᴮ using (xtᶻ)
  open QD gradedᴮ domsᴮ using (Chain; module SuffD)
  open XT gradedᴮ domsᴮ
  open Rest gradedᴮ domsᴮ
  open XW gradedᴮ domsᴮ
  open AddR gradedᴮ domsᴮ _≤ᵀ_ zeroᴮ succᴮ limᴮ nodeᴮ embᴮ weakᴮ zero leRᴮ (genᴮ zero)

  ChainRelOn : (∀ {a} → Stᶻ a → (p : Pos a) → (Br a p → Tr a) → ℕ → Br a p) → Set
  ChainRelOn pt = ∀ {a} (s : Stᶻ a) K → Inv s K → (p : Pos a) → ∀ {t κ} (g : Br a p → Tr a)
    → E.cof t ≡ E.cΩ κ → GR.Nu a p κ → (∀ η c → GR.R (at a p) η (slTᵍ a p c) → GR.R a (E.fsT t η) (g c))
    → ∀ k → Σ ℕ λ m → GR.R (at a p) (E.γT (K ++ t) κ k) (slTᵍ a p (pt s p g m))

  ChainRelʳ ChainRelʳ⁰ : Set
  ChainRelʳ  = ChainRelOn ptᶻ
  ChainRelʳ⁰ = ChainRelOn pt⁰

  chain→ʳ : Wi.ChainRel → ChainRelʳ
  chain→ʳ cr s K bd p g e nu hR k = k , cr s K bd p g e nu hR k

  slot→ʳ : Wi.LowSlot → ChainRelʳ
  slot→ʳ ls = chain→ʳ (Wi.chain←slot ls)

  to⁰ : ChainRelʳ → ChainRelʳ⁰
  to⁰ cr s K bd p g e nu hR k = suc (proj₁ (cr s K bd p g e nu hR k)) , proj₂ (cr s K bd p g e nu hR k)
```

第 0 个链点是零树, 参照链每一项都非空, 所以较弱形状里下标 0 从不被用到.

```agda
  from⁰ : ChainRelʳ⁰ → ChainRelʳ
  from⁰ cr {a} s K bd p {t} {κ} g e nu hR k = go (cr s K bd p g e nu hR k)
    where
    go : Σ ℕ (λ m → GR.R (at a p) (E.γT (K ++ t) κ k) (slTᵍ a p (pt⁰ s p g m)))
       → Σ ℕ (λ m → GR.R (at a p) (E.γT (K ++ t) κ k) (slTᵍ a p (ptᶻ s p g m)))
    go (zero , r)  = ⊥-elim (γ≢[] (K ++ t) κ k (R-zero (at a p) (subst (GR.R (at a p) _) (slT-fb a p zero) r)))
    go (suc m , r) = m , r
```

## 树一侧取 node⁺ 自己的链

`xt⁰` 与 `YiWRZero.xtᶻ` 只差链: 链点从第 0 个起, 支配直接是 `AddR.chain-dom`.

```agda
  domPt⁰ : ∀ {X x₀} (m : Keep zero X x₀) (G′ : X → Tr⁺ zero) (S′ : X → X)
    → ∀ k {τ} → GR.R zero τ (proj₁ (G′ (iter S′ x₀ k))) → GR.R zero τ (proj₁ (node⁺ m G′ S′))
  domPt⁰ (just (() , _)) G′ S′
  domPt⁰ nothing G′ S′ k = chain-dom G′ S′ k

  ch⁰ : ∀ {a} (s : Stᶻ a) (p : Pos a) (g : Br a p → Tr a) → Dᶻ s (Ω p g) → (⊥ → ⊥) → Chain sysᶻ s p g
  ch⁰ {a} (o , r , B , β) p g _ _ = pt⁰ (o , r , B , β) p g
    , domPt⁰ (kp a o p (z≤ a)) (λ z → BS.ψ a o r B zero (z≤ a) β (g z)) (stepPt (o , r , B , β) p g)

  xt⁰ : XTree sysᶻ keepᶻ Dᶻ
  xt⁰ = record { xp = λ {a} s p → high (λ ()) (z≤ (at a p)) ; ch = ch⁰ ; lvl = λ _ _ () ; mvR = λ _ _ () }
```

## 接线

参照一侧的余尾与基本列逐字同 `Wire.aboveᴱ`. `lowOn`, `ExitOn`, `ebo-endOn` 对树一侧 (`xtᶻ` 或 `xt⁰`) 参数化.

```agda
  refparts : ∀ (K t : E.T) {κ} → E.cof t ≡ E.cΩ κ
    → E.cof (apᴱ K t) ≡ E.cω × (∀ k → E.fsn (apᴱ K t) k ≡ apᴱ K (E.fsT t (E.γT (K ++ t) κ k)))
  refparts K t {κ} e = trans (cofψΩ [] (K ++ t) (cof++Ω K t e)) (cong (E.cofψ₊ [] κ) (sucgt κ))
    , (λ k → trans (fsnψΩ [] (K ++ t) k (cof++Ω K t e))
        (trans (cong (λ c → E.fsnc [] (K ++ t) κ c k) (sucgt κ))
          (cong (λ z → E.ψ [] z ∷ []) (fsT++ K t (E.γT (K ++ t) κ k) e))))

  aboveᴱʳ : ChainRelʳ → AboveLʳ sysᶻ keepᶻ Dᶻ xtᶻ
  aboveᴱʳ cr s K bd p {t} {κ} g d e nu hR _ _ =
    (λ k → E.γT (K ++ t) κ k) , proj₁ (refparts K t e) , proj₂ (refparts K t e) , cr s K bd p g e nu hR

  aboveᴱʳ⁰ : ChainRelʳ⁰ → AboveLʳ sysᶻ keepᶻ Dᶻ xt⁰
  aboveᴱʳ⁰ cr s K bd p {t} {κ} g d e nu hR _ _ =
    (λ k → E.γT (K ++ t) κ k) , proj₁ (refparts K t e) , proj₂ (refparts K t e) , cr s K bd p g e nu hR

  module _ (xt : XTree sysᶻ keepᶻ Dᶻ) (cx : At sysᶻ keepᶻ Dᶻ xt (PartXʳ sysᶻ keepᶻ Dᶻ xt))
           (ab : AboveLʳ sysᶻ keepᶻ Dᶻ xt) where
    lowOn : ∀ {ℓ} (s : Stᶻ ℓ) K → Inv s K → ∀ {a x} → GR.R ℓ a x → GR.R zero (apᴱ K a) (proj₁ (Φᶻ s x))
    lowOn {ℓ} s K bd r =
      SuffD.keepAllᴰ sysᶻ _≤ᵀ_ weakᴮ limᴮ nodeᴮ monoᶻ keepᶻ fallᶻ domᶻ (λ _ _ _ _ _ → tt)
        (withN sysᶻ Wi.restᴱ (outʳ sysᶻ keepᶻ Dᶻ xt belowᶻ ab cx)) genᴮ (wfL gradedᴮ domsᴮ ℓ) s K bd r tt

    foldedOn : ∀ n → GR.R zero (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ n)) ∷ []) (twcᴮ n)
    foldedOn n = lowOn (rootᴮ n) [] (inv-root n) (dom-top (dom-keel n))

    ExitOn : Set
    ExitOn = ∀ n → H.Exᴴ (foldedOn n)

    ebo-endOn : ExitOn → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
    ebo-endOn ex = ≼-trans reference (l≼ (λ n → ≼-trans (Exit₀.exit exitᵍ (foldedOn n) (ex n) (hs n)) (upperᴮ n)))

  ebo-endʳ : (cr : ChainRelʳ) → ExitOn xtᶻ (λ _ _ _ _ _ _ _ _ _ → tt) (aboveᴱʳ cr) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
  ebo-endʳ cr = ebo-endOn xtᶻ (λ _ _ _ _ _ _ _ _ _ → tt) (aboveᴱʳ cr)

  ebo-endʳ⁰ : (cr : ChainRelʳ⁰) → ExitOn xt⁰ (λ _ _ _ _ _ _ _ _ _ → tt) (aboveᴱʳ⁰ cr) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
  ebo-endʳ⁰ cr = ebo-endOn xt⁰ (λ _ _ _ _ _ _ _ _ _ → tt) (aboveᴱʳ⁰ cr)
```

## 第 0 项与步

`BaseW`: 某个链点不低于 Ω_κ. `StepW`: 参照链第 k 项不高于某个链点, 则第 k+1 项也不高于某个链点 (下标可以往后挪任意多). `LowSlot` 给出两者, 下标分别是 1 与 m+1.

```agda
  BaseW StepW : Set
  BaseW = ∀ {a} (s : Stᶻ a) K → Inv s K → (p : Pos a) → ∀ {κ} (g : Br a p → Tr a) → GR.Nu a p κ
    → Σ ℕ λ m → GR.R (at a p) (E.Ωt κ) (slTᵍ a p (pt⁰ s p g m))
  StepW = ∀ {a} (s : Stᶻ a) K → Inv s K → (p : Pos a) → ∀ {t κ} (g : Br a p → Tr a)
    → E.cof t ≡ E.cΩ κ → GR.Nu a p κ → (∀ η c → GR.R (at a p) η (slTᵍ a p c) → GR.R a (E.fsT t η) (g c))
    → ∀ k m → GR.R (at a p) (E.γT (K ++ t) κ k) (slTᵍ a p (pt⁰ s p g m))
    → Σ ℕ λ m′ → GR.R (at a p) (E.γT (K ++ t) κ (suc k)) (slTᵍ a p (pt⁰ s p g m′))

  bs→ʳ⁰ : BaseW → StepW → ChainRelʳ⁰
  bs→ʳ⁰ bw sw s K bd p g e nu hR zero    = bw s K bd p g nu
  bs→ʳ⁰ bw sw s K bd p g e nu hR (suc k) =
    sw s K bd p g e nu hR k (proj₁ (bs→ʳ⁰ bw sw s K bd p g e nu hR k)) (proj₂ (bs→ʳ⁰ bw sw s K bd p g e nu hR k))

  slot→base : Wi.LowSlot → BaseW
  slot→base ls {a} s K bd p {κ} g nu = 1 , subst (GR.R (at a p) (E.Ωt κ)) (sym (slT-fb a p _))
    (closeᴿ (at a p) (Ω≤ψ κ (K ++ [])) (ls s K bd p nu (mz′ a)))

  slot→step : Wi.LowSlot → StepW
  slot→step ls {a} s K bd p {t} {κ} g e nu hR k m r = suc m ,
    subst₂ (GR.R (at a p)) (cong (λ z → E.ψ κ z ∷ []) (sym (fsT++ K t (E.γT (K ++ t) κ k) e))) (sym (slT-fb a p _))
      (ls s K bd p nu (hR (E.γT (K ++ t) κ k) (pt⁰ s p g m) r))
```

`Inv₁` 的第二项 (各层底不低于该层的 Ω 树) 之下, 第 1 个链点不低于槽位层的 Ω 树; 槽位层上有 Leaf 的点, 第 0 项成立. 这里的 Leaf 是逐点的前提 (全域 Leaf 有编译的否定, `YiLLLeafNeg.noLeaf`).

```agda
base₁ : ∀ {a} (o : Ok a) r (B : Base a) (β : Tr⁺ zero) → (∀ i u → proj₁ (O.Ωt i) ⊴ proj₁ (B i u))
  → (p : Pos a) (g : Br a p → Tr a) {κ : E.T} → GR.R (at a p) (E.Ωt κ) (proj₁ (O.Ωt (at a p)))
  → GR.R (at a p) (E.Ωt κ) (slTᵍ a p (pt⁰ (o , r , B , β) p g 1))
base₁ {a} o r B β bs p g lf = subst (GR.R (at a p) _) (sym (slT-fb a p _))
  (weakenᴿ (at a p) (weakenᴿ (at a p) lf (bs (at a p) (posW a p)))
    (ψ-⊵ᴮ a o r B (at a p) (posW a p) (B (at a p) (posW a p)) (g (fromBr a p zero))))
```

## 前提可满足

`Wireʳ` 的参数取 `YiWREnd` 的 `Inv₀` (同 `W₀`); `base₁` 的前提在塔第 1 项、第 1 层槽位、底 `B₀` 上成立.

```agda
module Wʳ₀ = Wireʳ Inv₀ (λ o r B β bd → bd) inv₀-step (λ n → H.pos⁰ (proj₁ (betaᴮ n)) (proj₂ (betaᴮ n)))

base₁-tw1 : (g : Br (tw 1) (inj₂ (suc zero , inj₁ tt)) → Tr (tw 1)) (β : Tr⁺ zero)
  → GR.R j₁ (E.Ωt (E.𝟏 ∷ [])) (slTᵍ (tw 1) (inj₂ (suc zero , inj₁ tt)) (pt⁰ (Ok-tw 1 , rb-tw 1 , B₀ (tw 1) , β) (inj₂ (suc zero , inj₁ tt)) g 1))
base₁-tw1 g β = base₁ (Ok-tw 1) (rb-tw 1) (B₀ (tw 1)) β (λ i u → K.⊴r) (inj₂ (suc zero , inj₁ tt)) g top₁
```
