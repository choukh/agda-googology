# 换基折叠上的出口分解: 读回域里没有分叉一份

> 判决: 编译定理, 不读记号, 不改树、折叠、合法性; 系统复用 `YiBLFold.Pack` 与 `YiQDFold.QDPack`. 主系统 (`YiBSFold.ψ` 的根状态, 域 `KD`): 域内结点都在保留出口, 结点出口只要 `Below` (`nodeᴮ`; 对现有树一侧 `ntᴮ` 同样, `nodeRᴮ`). 辅助系统 (`lift` 路径与上折): 路径一致, 出口没有分叉, 结点出口只要 `Below` 与 `AboveL` (`nodeᴬ`).
> 于是 `lowˣ`: `QDPack.WithRules.lowᴰ` 的结论只要两组出口里非结点的各条 (`OutRDN`, `OutDN`) 加两个系统的 `Below` 与辅助系统的 `AboveL`; 分叉一份不出现. R94 在换基折叠上: 嵌入在孩子 0 而目标在地板之下时经 `back` 在孩子 0 上折 (`r94-backᴮ`), 在孩子层号自身时材料只进尾项 (`r94-seenᴮ`).
> 前提可满足: 平凡模型里 `lowˣ` 的全部前提成立 (`modelA-low`). 不给出什么: 参照一侧的各条没有对记号实填; 没有值的定理; `route` 落在地板之下的根状态不在本文的系统里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXTReb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; node⁺)
import OCF.Lean.YiRBSib as RB
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiGIBlock using (blkᵍ; chLᵍ; ChTᵍ; chTᵍ; upᵍ; slTᵍ)
open import OCF.Lean.YiAbsFrame using (Block; Fold)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiBLFold
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiQDFold
open import OCF.Lean.YiXTIface
open import OCF.Lean.YiXTKp
open import OCF.Lean.YiXTCur using (module ModelA)
open import OCF.Lean.YiVALeaf using (nzs)
open import OCF.Lean.YiTBRow using (h₁)
open import OCF.Lean.YiAbsGRow using (module Row)
```

## 两个系统的出口

参数同 `YiQDFold.QDPack`. 主系统: 出口由 `kexit` 给出; 域 `KD` 要求本层结点的槽位保留, 所以无证据的一支在域里是空的 (`chᴮ`).

```agda
module XReb {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴮ : ∀ {a} → Main.Stᴮ k h o S rc B j c′ v u eq a → Cxtᴮ → Set) where
  open FI 𝔾 𝔻 using (Gen⁺)
  open QD 𝔾 𝔻
  open XT 𝔾 𝔻
  open Rest 𝔾 𝔻
  open Laws 𝔾 𝔻 using (Weak; Lim; Node; Zero; Succ; Emb; app; Cx) renaming (R to Rᵍ)
  open Aux j
  open Main k h o S rc B j c′ v u eq
  open QDPack 𝔾 𝔻 k h o S rc B j c′ v u eq Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ public

  toXᴮ : ∀ β (p : Pos ℓ) → KExit j ℓ o p w → XPick sysᴮ (rt β) p
  toXᴮ β p (kept e)              = kept e
  toXᴮ β p (high ne u′)          = high ne u′
  toXᴮ β p (cross ne c c″ u′ v′) = cross ne c c″ u′ v′

  xpᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) → XPick sysᴮ s p
  xpᴮ (rt β) p = toXᴮ β p (kexit ℓ o p w)

  chᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) (g : Br a p → Tr a) → Dᴮ s (Ω p g) → (Evᴮ s p → ⊥) → Chain sysᴮ s p g
  chᴮ (rt β) p g (kd , _) ne = ⊥-elim (ne kd)

  lvlᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) (e : Evᴮ s p) → at j (slotᴮ s p e) ≡ at a p
  lvlᴮ (rt β) p (q , cv , e , eq′) = kp-lvl ℓ o p w q cv e eq′

  xtᴮ : XTree sysᴮ keepᴮ Dᴮ
  xtᴮ = record { xp = xpᴮ ; ch = chᴮ ; lvl = lvlᴮ ; mvR = mvRᴮ }

  aboveᴮ : AboveL sysᴮ keepᴮ Dᴮ xtᴮ
  aboveᴮ (rt β) K bd p g (kd , _) e nu hR ne u′ = ⊥-elim (ne kd)

  crossᴮ : At sysᴮ keepᴮ Dᴮ xtᴮ (PartX sysᴮ keepᴮ Dᴮ xtᴮ)
  crossᴮ (rt β) K bd p {t} {κ} g d e nu hR = px (xpᴮ (rt β) p)
    where
    px : (x : XPick sysᴮ (rt β) p) → PartX sysᴮ keepᴮ Dᴮ xtᴮ (rt β) K p g d t κ x
    px (kept _)           = tt
    px (high _ _)         = tt
    px (cross ne _ _ _ _) = ⊥-elim (ne (proj₁ d))

  nodeᴮ : Below sysᴮ → NodeOut sysᴮ keepᴮ Dᴮ
  nodeᴮ bl = out sysᴮ keepᴮ Dᴮ xtᴮ bl aboveᴮ crossᴮ

  nodeRᴮ : Below sysᴮ → NodeRef sysᴮ keepᴮ Dᴮ ntᴮ
  nodeRᴮ bl (rt β) K bd p g (kd , _) e nu hR = bl (rt β) K bd p e nu (proj₁ kd) (lvlᴮ (rt β) p kd)
```

辅助系统: `rbs` 状态的目标路径是 `lift j b`, 一致, 出口由 `kexit-uni` 给出, 没有分叉 (`uni-notX`); 上折状态处处保留.

```agda
  toXᴬ : ∀ b o′ B′ β (p : Pos (j ⊕ b)) → KExit j (j ⊕ b) o′ p (lift j b) → XPick sysᴬ (rbs b o′ B′ β) p
  toXᴬ b o′ B′ β p (kept e)              = kept e
  toXᴬ b o′ B′ β p (high ne u′)          = high ne u′
  toXᴬ b o′ B′ β p (cross ne c c″ u′ v′) = cross ne c c″ u′ v′

  xpᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) → XPick sysᴬ s p
  xpᴬ (rbs b o′ B′ β) p = toXᴬ b o′ B′ β p (kexit-uni (j ⊕ b) o′ p (lift j b) (uni-lift j b))
  xpᴬ (us d β)        p = kept tt

  lvlᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) (e : Evᴬ s p) → at j (slotᴬ s p e) ≡ at a p
  lvlᴬ (rbs b o′ B′ β) p (q , cv , e , eq′) = kp-lvl (j ⊕ b) o′ p (lift j b) q cv e eq′
  lvlᴬ (us d β)        p _                  = proj₁ (mv-good d p)

  module WithR (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) (lm : Lim) (nod : Node) (zr : Zero) (sr : Succ) (em : Emb)
      (leR : ∀ {s t o} → Le s t → Rᵍ j t o → Rᵍ j s o) (gen : ∀ a → Gen⁺ Le a) where
    open AddR 𝔾 𝔻 Le zr sr lm nod em wk j leR (gen j)

    chᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) (g : Br a p → Tr a) → Dᴬ s (Ω p g) → (Evᴬ s p → ⊥) → Chain sysᴬ s p g
    chᴬ (rbs b o′ B′ β) p g _ ne = chainK (Rᵍ j) (kp (j ⊕ b) o′ p (lift j b)) G′ S′ (chain-dom G′ S′) ne
      where
      G′ : Br (j ⊕ b) p → Tr⁺ j
      G′ z = RB.ψ (j ⊕ b) o′ (RB.rb-no (j ⊕ b)) B′ j (lift j b) β (g z)
      S′ : Br (j ⊕ b) p → Br (j ⊕ b) p
      S′ z = fromBr (j ⊕ b) p (proj₁ (RB.ψ (j ⊕ b) o′ (RB.rb-no (j ⊕ b)) B′ (at (j ⊕ b) p) (posW (j ⊕ b) p)
               (B′ (at (j ⊕ b) p) (posW (j ⊕ b) p)) (g z)))
    chᴬ (us d β) p g _ ne = ⊥-elim (ne tt)

    xtᴬ : XTree sysᴬ keepᴬ Dᴬ
    xtᴬ = record { xp = xpᴬ ; ch = chᴬ ; lvl = lvlᴬ ; mvR = mvRᴬ }

    crossᴬ : At sysᴬ keepᴬ Dᴬ xtᴬ (PartX sysᴬ keepᴬ Dᴬ xtᴬ)
    crossᴬ (rbs b o′ B′ β) K bd p {t} {κ} g d e nu hR =
      px (kexit-uni (j ⊕ b) o′ p (lift j b) (uni-lift j b)) (uni-notX (j ⊕ b) o′ p (lift j b) (uni-lift j b))
      where
      px : (x : KExit j (j ⊕ b) o′ p (lift j b)) → NotX x → PartX sysᴬ keepᴬ Dᴬ xtᴬ (rbs b o′ B′ β) K p g d t κ (toXᴬ b o′ B′ β p x)
      px (kept _)          _ = tt
      px (high _ _)        _ = tt
      px (cross _ _ _ _ _) ()
    crossᴬ (us d′ β) K bd p g d e nu hR = tt

    nodeᴬ : Below sysᴬ → AboveL sysᴬ keepᴬ Dᴬ xtᴬ → NodeOut sysᴬ keepᴬ Dᴬ
    nodeᴬ bl ab = out sysᴬ keepᴬ Dᴬ xtᴬ bl ab crossᴬ
```

`lowˣ`: 同 `QDPack.WithRules.lowᴰ`, 结点一条换成上面的两个结点出口.

```agda
    lowˣ : OutRDN sysᴮ sysᴬ keepᴬ embᴮ Le Dᴮ → OutDN sysᴬ Le fallᴬ
      → Below sysᴮ → Below sysᴬ → AboveL sysᴬ keepᴬ Dᴬ xtᴬ
      → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ app Kc t)
      → ∀ {a x} → KD x → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (BS.ψ ℓ o r B j w β x))
    lowˣ rᴮ rᴬ blᴮ blᴬ ab β K₀ bd Kc ec =
      SuffRAD.sys→lowᴰ sysᴮ sysᴬ keepᴬ embᴮ Le wk lm nod monoᴮ keepᴮ domᴮ domᴬ rowDᴮ
        (withRN sysᴮ sysᴬ keepᴬ embᴮ rᴮ (nodeᴮ blᴮ)) monoᴬ fallᴬ (λ _ _ _ _ _ → tt) (withN sysᴬ rᴬ (nodeᴬ blᴬ ab))
        (wfL 𝔾 𝔻) gen (wfL 𝔾 𝔻 ℓ) (rt β) K₀ bd (o , r , B) w β Kc (λ x → refl) ec
```

## 前提可满足

平凡模型 (同 `YiXTCur.ModelA`, 块上的折叠换成 `foldᴮ`), 塔第 1 项, 目标 `h₁ 1` 经孩子 1 (`QDTw1` 的实例): `lowˣ` 的全部前提成立.

```agda
module ModelAᴮ (𝕍 : Val) where
  open ModelA 𝕍 using (refA)

  gradedAᴮ : Graded blkᵍ foldᴮ rowsᴮ refA 𝕍
  gradedAᴮ = record { ℓ₀ = zero ; v = λ _ → Val.vz 𝕍 ; R = λ _ _ _ → ⊤ ; Rd = λ _ _ → ⊤ ; Nu = λ _ _ _ → ⊤
                    ; bt = proj₁ ; cl = λ _ t → t ; Cx = λ _ _ → ⊤ ; app = λ _ t → t ; Bd = λ _ _ _ _ → ⊤ }

  domsAᴮ : Doms blkᵍ foldᴮ
  domsAᴮ = record { Gx = λ _ _ → ⊤ ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ _ _ → ⊤ }

  open FI gradedAᴮ domsAᴮ using (Gen⁺)
  open Row gradedAᴮ domsAᴮ using (Rules)
  open XT gradedAᴮ domsAᴮ
  open Rest gradedAᴮ domsAᴮ

  genAᴮ : ∀ a → Gen⁺ (λ _ _ → ⊤) a
  genAᴮ a Q rs _ _ = go _
    where
    open Rules rs
    go : (x : Tr a) → Q tt x
    go zero         = qz tt
    go (suc x)      = q1 tt tt (go x)
    go (lim f r)    = qw tt (go (f zero)) (◃l zero)
    go (Ω p g)      = qΩ p g tt tt (λ _ _ _ → tt) (λ η c _ → go (g c))
    go (up x c y e) = qU c (y , e) tt (go x) tt

  open XReb gradedAᴮ domsAᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) (B₀ (tw 1)) (h₁ (suc zero)) (suc zero) self
    (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero)) ⊤ (λ _ t → t) (λ _ _ → ⊤) ⊤ (λ _ t → t) (λ _ _ → ⊤)
  open WithR (λ _ _ → ⊤) (λ _ _ → tt) (λ _ _ → tt) (λ _ _ _ _ _ → tt) (λ _ → tt) (λ _ _ → tt) (λ _ _ _ _ → tt)
    (λ _ _ → tt) genAᴮ

  restᴮ : OutRDN sysᴮ sysᴬ keepᴬ embᴮ (λ _ _ → ⊤) Dᴮ
  restᴮ = record { zeroE = λ _ _ _ _ → tt ; succE = λ _ _ _ _ _ _ → tt ; limE = λ _ _ _ _ → tt , λ _ → refl
                 ; leE = λ _ _ _ _ _ → tt
                 ; embE = λ { (Main.rt β) K bd → (λ c r q → tt , tt , λ _ → refl) , (λ c y d r ry → tt , tt , tt) } }

  restᴬ : OutDN sysᴬ (λ _ _ → ⊤) fallᴬ
  restᴬ = record { zeroE = λ _ _ _ _ → tt ; succE = λ _ _ _ _ _ _ → tt ; limE = λ _ _ _ _ → tt , λ _ → refl
                 ; upE = λ _ _ _ _ _ _ → tt , tt , λ _ → refl ; leE = λ _ _ _ _ _ → tt }

  belowᴮ : Below sysᴮ
  belowᴮ s K bd p e nu q lv = tt , (λ _ → refl) , tt

  belowᴬ : Below sysᴬ
  belowᴬ s K bd p e nu q lv = tt , (λ _ → refl) , tt

  aboveᴬ : AboveL sysᴬ keepᴬ Dᴬ xtᴬ
  aboveᴬ s K bd p g d e nu hR ne u = (λ _ → tt) , tt , (λ _ → refl) , (λ _ → tt)

  modelA-low : (β : Tr⁺ (h₁ (suc zero))) → ∀ {a x} → KD x → ⊤ → ⊤
  modelA-low β {a} {x} d r = lowˣ restᴮ restᴬ belowᴮ belowᴬ aboveᴬ β tt tt tt (λ _ → refl) {a} {x} d r
```

## R94 在换基折叠上

同 `YiXTCur.r94-fallᶻ` 的上下文 (Λ, 嵌入在孩子 1, 目标经孩子 2), 目标再经 `tw 2` 的孩子 `Ω p g`. 目标进偏移的下标层 (`ink`, 地板之下): `route` 给 `inj₁`, 材料 y 在孩子 0 (层号 `tw 1`) 上朝原目标折. 目标就是孩子层号自身 (`self`, 地板之上): 材料只进第 0 层尾项.

```agda
rbΛ : Rb Λ
rbΛ = tt , rb-tw

r94-backᴮ : (B : Base Λ) (i : L) (p : Pos (tw 1)) (g : Br (tw 1) p → Tr (tw 1)) (v′ : i ≤ at (tw 1) p) (β : Tr⁺ i)
  (x : Tr Λ) (y : Tr (tw 1)) (e : tw 1 ⊢ zero ◃ y)
  → Σ (Base (tw 1)) λ B″ → Σ (Tr⁺ i) λ β″
  → BS.ψ Λ Ok-Λ rbΛ B i (inc 2 (inc (Ω p g) (ink v′))) β (up x 1 y e) ≡ BS.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B″ i (v′ ∙ posW (tw 1) p) β″ y
r94-backᴮ B i p g v′ β x y e = _ , _ , refl

r94-seenᴮ : (B : Base Λ) (p : Pos (tw 1)) (g : Br (tw 1) p → Tr (tw 1)) (β : Tr⁺ (tw 1 ⊕ ↑ (tw 1) (Ω p g)))
  (x : Tr Λ) (y : Tr (tw 1)) (e : tw 1 ⊢ zero ◃ y)
  → Σ (Tr⁺ (tw 1 ⊕ ↑ (tw 1) (Ω p g))) λ β″
  → BS.ψ Λ Ok-Λ rbΛ B (tw 1 ⊕ ↑ (tw 1) (Ω p g)) (inc 2 (inc (Ω p g) self)) β (up x 1 y e)
  ≡ β″ ⊞ BS.ψ (tw 1) (Ok-tw 1) (rb-tw 1) (B₀ (tw 1)) zero (z≤ (tw 1)) (Ωt zero) y
r94-seenᴮ B p g β x y e = _ , refl
```
