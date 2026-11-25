# 换基折叠朝第 0 层的系统: 树一侧全部实填

> 判决: 编译定理, 不读记号, 不改树、折叠、合法性. 目标为第 0 层、路径 `z≤` 的 `YiBSFold.ψ` 的全部状态 (底, 底值任意) 组成一个回退系统: 嵌入一行逐字是孩子的回退 (`fallᶻ`), 第 0 层没有槽位, 所以保留律空真, 每个结点都走折叠自己的链 (`xtᶻ`, 链从第 1 个链点起), `Below` 空真.
> 于是 `lowᶻ`: 朝第 0 层的保持只要出口里非结点的五条 (`OutDN`) 与这个系统的 `AboveL`, 加关系的生成规则. 换基一行 (`route` 落在地板之上) 不在这条递归里: 它只出现在链点与孩子的底里 (见 [YiWREnd](YiWREnd.lagda.md) 文首).
> 不给出什么: 参照一侧的各条在这里是前提 (记号上的实填在 [YiWREnd](YiWREnd.lagda.md)); 没有值的定理. 写法照 [YiQDFold](YiQDFold.lagda.md) 的 `QDPack`, 链的支配用 `YiQDFold.AddR.chain-dom`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWRZero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; node⁺)
open import OCF.Lean.YiBSBase using (Rb)
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiGIBlock using (blkᵍ; chLᵍ; ChTᵍ; chTᵍ; upᵍ)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiXTIface
open import OCF.Lean.YiBLFold using (foldᴮ; rowsᴮ; _⊴ᵗ_; wfL)
open import OCF.Lean.YiQDFold using (module AddR)
```

## 状态, 像, 回退

状态是 (合法证据, 换基证据, 底, 底值); 像是朝第 0 层沿 `z≤` 的折叠. 第 0 层之外的层号上 `z≤` 处处是 `inu`, 所以嵌入一行逐字落进孩子.

```agda
Stᶻ : L → Set
Stᶻ a = Ok a × Rb a × Base a × Tr⁺ zero

Φᶻ : ∀ {a} → Stᶻ a → Tr a → Tr⁺ zero
Φᶻ {a} (o , r , B , β) x = BS.ψ a o r B zero (z≤ a) β x

stepᶻ : ∀ {a} → Stᶻ a → (c : CH a) → Tr a → Stᶻ (chLᵍ a c)
stepᶻ {nd s h} (o , r , B , β) c x =
  proj₂ o c , proj₂ r c , (λ i u → BS.ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) , BS.ψ (nd s h) o r B zero (z≤ (nd s h)) β x

fallᶻ′ : ∀ {a} (s : Stᶻ a) (c : CH a) (x : Tr a) (y : ChTᵍ a c)
  → proj₁ (Φᶻ (stepᶻ s c x) (chTᵍ a c y)) ⊴ᵗ proj₁ (Φᶻ s (upᵍ x c y))
fallᶻ′ {nd s h} (o , r , B , β) c x (y , e) = inj₁ refl

monoᶻ′ : ∀ {a} (s : Stᶻ a) {x y : Tr a} → a ⊢ x ◃ y → zero ⊢ proj₁ (Φᶻ s x) ◃ proj₁ (Φᶻ s y)
monoᶻ′ {a} (o , r , B , β) d = BS.mono a o r B zero (z≤ a) β d

```

结点 `Ω p g` 上折叠自己的链: 链步是第 g z 个分支朝槽位层的折叠 (底值取底在槽位层上的值), 链点从第 1 个起 (`ptᶻ`). 第 0 个链点是第 0 个分支 (零树), 参照一侧的链从 Ω_κ 起, 在零树上对不上 (判断, 见 [YiWREnd](YiWREnd.lagda.md)).

```agda
slotFold : ∀ {a} (s : Stᶻ a) (p : Pos a) → Tr a → Tr (at a p)
slotFold {a} (o , r , B , β) p y = proj₁ (BS.ψ a o r B (at a p) (posW a p) (B (at a p) (posW a p)) y)

stepPt : ∀ {a} (s : Stᶻ a) (p : Pos a) (g : Br a p → Tr a) → Br a p → Br a p
stepPt {a} s p g z = fromBr a p (slotFold s p (g z))

ptᶻ : ∀ {a} (s : Stᶻ a) (p : Pos a) (g : Br a p → Tr a) → ℕ → Br a p
ptᶻ {a} s p g k = iter (stepPt s p g) (fromBr a p zero) (suc k)
```

## 接上整体接口

参照一侧 (上下文, 作用, 状态对上下文的条件) 作模块参数, 同 `YiBLFold.Pack`. 第 0 层没有槽位 (`Pos zero` 是空类型), 证据取空.

```agda
module Zero {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (Cxtᶻ : Set) (apᶻ : Cxtᶻ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᶻ : ∀ {a} → Stᶻ a → Cxtᶻ → Set) where
  open FI 𝔾 𝔻 using (Sys; Gen⁺)
  open QD 𝔾 𝔻
  open XT 𝔾 𝔻
  open Rest 𝔾 𝔻
  open Laws 𝔾 𝔻 using (Weak; Lim; Node; Zero; Succ; Emb) renaming (R to Rᵍ)

  sysᶻ : Sys zero
  sysᶻ = record { St = Stᶻ ; Φ = λ s x → proj₁ (Φᶻ s x) ; Ev = λ _ _ → ⊥ ; Cxt = Cxtᶻ ; ap = apᶻ ; Bdˢ = Bdᶻ }

  keepᶻ : Sys.KeepLaw sysᶻ
  keepᶻ = record { slot = λ _ _ () ; mvc = λ _ _ () ; keep = λ _ _ () }

  fallᶻ : Sys.FallLaw sysᶻ
  fallᶻ = record { step = stepᶻ ; fall = fallᶻ′ }

  monoᶻ : Sys.Monoˢ sysᶻ
  monoᶻ = monoᶻ′

  Dᶻ : ∀ {a} → Stᶻ a → Tr a → Set
  Dᶻ _ _ = ⊤

  domᶻ : Dom sysᶻ
  domᶻ = record { D = Dᶻ ; dw = λ _ _ _ → tt ; dsc = λ _ _ → tt ; dnd = λ _ _ _ _ _ → tt ; dup = λ _ _ _ _ _ → tt }

  belowᶻ : Below sysᶻ
  belowᶻ s K bd p e nu ()
```

结点: 第 0 层的保留判定只能给 `nothing` (`just` 要第 0 层的槽位), 链取 `ptᶻ`.

```agda
  module WithRules (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) (lm : Lim) (nod : Node) (zr : Zero) (sr : Succ) (em : Emb)
      (leR : ∀ {s t o} → Le s t → Rᵍ zero t o → Rᵍ zero s o) (gen : ∀ a → Gen⁺ Le a) where
    open AddR 𝔾 𝔻 Le zr sr lm nod em wk zero leR (gen zero)

    domPt : ∀ {X x₀} (m : Keep zero X x₀) (G′ : X → Tr⁺ zero) (S′ : X → X)
      → ∀ k {τ} → Rᵍ zero τ (proj₁ (G′ (iter S′ x₀ (suc k)))) → Rᵍ zero τ (proj₁ (node⁺ m G′ S′))
    domPt (just (() , _)) G′ S′
    domPt nothing G′ S′ k = chain-dom G′ S′ (suc k)

    chᶻ : ∀ {a} (s : Stᶻ a) (p : Pos a) (g : Br a p → Tr a) → Dᶻ s (Ω p g) → (⊥ → ⊥) → Chain sysᶻ s p g
    chᶻ {a} (o , r , B , β) p g _ _ = ptᶻ (o , r , B , β) p g
      , domPt (kp a o p (z≤ a)) (λ z → BS.ψ a o r B zero (z≤ a) β (g z)) (stepPt (o , r , B , β) p g)

    xtᶻ : XTree sysᶻ keepᶻ Dᶻ
    xtᶻ = record { xp = λ {a} s p → high (λ ()) (z≤ (at a p)) ; ch = chᶻ ; lvl = λ _ _ () ; mvR = λ _ _ () }

    crossᶻ : At sysᶻ keepᶻ Dᶻ xtᶻ (PartX sysᶻ keepᶻ Dᶻ xtᶻ)
    crossᶻ s K bd p g d e nu hR = tt

    nodeᶻ : AboveL sysᶻ keepᶻ Dᶻ xtᶻ → NodeOut sysᶻ keepᶻ Dᶻ
    nodeᶻ ab = out sysᶻ keepᶻ Dᶻ xtᶻ belowᶻ ab crossᶻ
```

`lowᶻ`: 非结点的五条出口与 `AboveL` 成立, 则任何状态上朝第 0 层的保持对一切树成立.

```agda
    lowᶻ : OutDN sysᶻ Le fallᶻ → AboveL sysᶻ keepᶻ Dᶻ xtᶻ
      → ∀ {ℓ} (s : Stᶻ ℓ) (K : Cxtᶻ) → Bdᶻ s K → ∀ {a x} → Rᵍ ℓ a x → Rᵍ zero (apᶻ K a) (proj₁ (Φᶻ s x))
    lowᶻ rest ab {ℓ} s K bd r =
      SuffD.keepAllᴰ sysᶻ Le wk lm nod monoᶻ keepᶻ fallᶻ domᶻ (λ _ _ _ _ _ → tt) (withN sysᶻ rest (nodeᶻ ab)) gen
        (wfL 𝔾 𝔻 ℓ) s K bd r tt
```

## 前提可满足

平凡模型 (`YiXTReb.ModelAᴮ`: 关系处处为真): `lowᶻ` 的全部前提成立.

```agda
module ModelZ (𝕍 : Val) where
  open import OCF.Lean.YiXTReb using (module ModelAᴮ)
  open ModelAᴮ 𝕍 using (gradedAᴮ; domsAᴮ; genAᴮ)
  open Zero gradedAᴮ domsAᴮ ⊤ (λ _ t → t) (λ _ _ → ⊤)
  open XT gradedAᴮ domsAᴮ
  open Rest gradedAᴮ domsAᴮ
  open WithRules (λ _ _ → ⊤) (λ _ _ → tt) (λ _ _ → tt) (λ _ _ _ _ _ → tt) (λ _ → tt) (λ _ _ → tt) (λ _ _ _ _ → tt)
    (λ _ _ → tt) genAᴮ

  restZ : OutDN sysᶻ (λ _ _ → ⊤) fallᶻ
  restZ = record { zeroE = λ _ _ _ _ → tt ; succE = λ _ _ _ _ _ _ → tt ; limE = λ _ _ _ _ → tt , λ _ → refl
                 ; upE = λ _ _ _ _ _ _ → tt , tt , λ _ → refl ; leE = λ _ _ _ _ _ → tt }

  aboveZ : AboveL sysᶻ keepᶻ Dᶻ xtᶻ
  aboveZ s K bd p g d e nu hR ne u = (λ _ → tt) , tt , (λ _ → refl) , (λ _ → tt)

  modelZ-low : ∀ {ℓ} (s : Stᶻ ℓ) {a : ⊤} {x : Tr ℓ} → ⊤ → ⊤
  modelZ-low s {a} {x} r = lowᶻ restZ aboveZ s tt tt {a} {x} r
```
