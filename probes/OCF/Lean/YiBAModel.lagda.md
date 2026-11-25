# 余尾不相交的模型里 `Below` 与 `AboveL` 同时成立

> 判决: 编译定理, 无前提; 不读记号, 不改树、折叠、合法性. 模型 `refM`: 余尾 Ω 与余尾 ω 是关系 (`CΩᴹ`, `Cωᴹ`), 两者不相交 (`dωᴹ`, 由 `YiXTKp.no-cyc`); 上下文把参照项包成 "朝目标 j 折叠" (`col j`), 其余尾按字面层号定: 槽位下标是目标某个真槽位的层号时保持 Ω, 目标到它有字面路径时降成 ω.
> 对 `YiXTReb.XReb` 的一切实例, 主系统与辅助系统的 `Below`、辅助系统的 `AboveL` 成立 (`belowᴮᴹ`, `belowᴬᴹ`, `aboveᴬᴹ`), 两个结点出口成立 (`nodeᴮᴹ`, `nodeᴬᴹ`). 塔第 1 项上两条的前提都有实例, 且一处给 Ω、一处给 ω (`tw1-below`, `tw1-above`).
> 不给出什么: 模型的关系取 ⊤, 不涉及值; 不说明 EBO 参照满足这两条 (见 [YiBAEbo](YiBAEbo.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBAModel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiBSBase
open import OCF.Lean.YiGIBlock using (blkᵍ)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLFold using (foldᴮ; rowsᴮ; Sₙ; rcₙ; route-tw1; module Aux)
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiQDFold using (kept-tw1)
open import OCF.Lean.YiXTIface
open import OCF.Lean.YiXTKp using (no-cyc)
open import OCF.Lean.YiXTReb using (module XReb)
open import OCF.Lean.YiVALeaf using (nzs)
open import OCF.Lean.YiTBRow using (h₁)
```

## 参照项与余尾

`lv b`: 层号 b 作余尾下标; `om κ`: 余尾 Ω_{κ+1} 的项; `col j t`: 朝 j 折叠. 余尾是关系, 不是判定.

```agda
data MT : Set where
  nil : MT
  lv  : L → MT
  om  : MT → MT
  col : L → MT → MT

unlv : MT → L
unlv (lv b) = b
unlv _      = zero

Same Abv : L → MT → Set
Same j κ = Σ L λ b → (κ ≡ lv b) × Σ (Pos j) λ q → at j q ≡ b
Abv  j κ = Σ L λ b → (κ ≡ lv b) × (j ≤ b)

CΩᴹ : MT → MT → Set
CΩᴹ (om κ′)   κ = κ′ ≡ κ
CΩᴹ (col j t) κ = CΩᴹ t κ × Same j κ
CΩᴹ _         _ = ⊥

Cωᴹ : MT → Set
Cωᴹ (col j t) = Σ MT λ κ → CΩᴹ t κ × Abv j κ
Cωᴹ _         = ⊥

fsTᴹ : MT → MT → MT
fsTᴹ (col j t) η = col j (fsTᴹ t η)
fsTᴹ _         η = η

fsnᴹ : MT → ℕ → MT
fsnᴹ (col j t) n = col j (fsTᴹ t nil)
fsnᴹ t         n = t

refM : Ref
refM = record { T = MT ; C0 = λ t → t ≡ nil ; C1 = λ _ → ⊥ ; Cω = Cωᴹ ; CΩ = CΩᴹ
              ; pred = λ t → t ; fsn = fsnᴹ ; fsT = fsTᴹ ; _⊕_ = λ t _ → t ; Ωr = om }
```

余尾 Ω 的下标唯一, 所以余尾 ω 与余尾 Ω 不相交: 两者给出同一层号 b 既是目标真槽位的层号, 又有目标到它的字面路径.

```agda
cof-fun : ∀ t {κ κ′} → CΩᴹ t κ → CΩᴹ t κ′ → κ ≡ κ′
cof-fun nil       () _
cof-fun (lv _)    () _
cof-fun (om κ″)   e        e′        = trans (sym e) e′
cof-fun (col j t) (e , _)  (e′ , _)  = cof-fun t e e′

dωᴹ : ∀ {u κ} → Cωᴹ u → CΩᴹ u κ → ⊥
dωᴹ {u = nil}     () _
dωᴹ {u = lv _}    () _
dωᴹ {u = om _}    () _
dωᴹ {u = col j t} (κ′ , e′ , b′ , l′ , w) (e , b , l , q , aq) =
  no-cyc j q (subst (j ≤_) (sym aq) (subst (j ≤_) (cong unlv (trans (sym l′) (trans (cof-fun t e′ e) l))) w))
```

## 分级结构与两个系统

关系取 ⊤; 槽位允许的余尾下标恰是槽位层号 (`Nu`). 生成原理经向下封闭 (`Le` 取 ⊤) 从零行得到.

```agda
module Mod (𝕍 : Val) where
  gradedM : Graded blkᵍ foldᴮ rowsᴮ refM 𝕍
  gradedM = record { ℓ₀ = zero ; v = λ _ → Val.vz 𝕍 ; R = λ _ _ _ → ⊤ ; Rd = λ _ _ → ⊤
                   ; Nu = λ ℓ p κ → κ ≡ lv (at ℓ p) ; bt = proj₁ ; cl = λ _ t → t ; Cx = λ _ _ → ⊤
                   ; app = λ _ t → t ; Bd = λ _ _ _ _ → ⊤ }

  domsM : Doms blkᵍ foldᴮ
  domsM = record { Gx = λ _ _ → ⊤ ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ _ _ → ⊤ }

  open FI gradedM domsM using (Gen⁺)
  open Row gradedM domsM using (Rules)

  genM : ∀ a → Gen⁺ (λ _ _ → ⊤) a
  genM a Q rs qc {t} {x} _ = qc {s = t} {t = nil} tt tt (Rules.qz rs refl)

  module M (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
           (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j)
           (eq : route S j c′ v ≡ inj₂ u) where
    open XReb gradedM domsM k h o S rc B j c′ v u eq ⊤ (λ _ t → col j t) (λ _ _ → ⊤) ⊤ (λ _ t → col j t) (λ _ _ → ⊤) public
    open WithR (λ _ _ → ⊤) (λ _ _ → tt) (λ _ _ → tt) (λ _ _ _ _ _ → tt) (λ _ → tt) (λ _ _ → tt) (λ _ _ _ _ → tt)
      (λ _ _ → tt) genM public
    open XT gradedM domsM
    open QD gradedM domsM using (NodeOut)

    belowᴮᴹ : Below sysᴮ
    belowᴮᴹ s K bd p e nu q lq = (e , _ , nu , q , lq) , (λ _ → refl) , trans nu (cong lv (sym lq))

    belowᴬᴹ : Below sysᴬ
    belowᴬᴹ s K bd p e nu q lq = (e , _ , nu , q , lq) , (λ _ → refl) , trans nu (cong lv (sym lq))

    aboveᴬᴹ : AboveL sysᴬ keepᴬ Dᴬ xtᴬ
    aboveᴬᴹ s K bd p {κ = κ} g d e nu hR ne w = (λ _ → nil) , (κ , e , _ , nu , w) , (λ _ → refl) , (λ _ → tt)

    nodeᴮᴹ : NodeOut sysᴮ keepᴮ Dᴮ
    nodeᴮᴹ = nodeᴮ belowᴮᴹ

    nodeᴬᴹ : NodeOut sysᴬ keepᴬ Dᴬ
    nodeᴬᴹ = nodeᴬ belowᴬᴹ aboveᴬᴹ
```

## 前提可满足: 塔第 1 项

目标 `h₁ 1`. 主系统: Ω 树的顶槽位保留 (`kept-tw1`), 目标有同层的真槽位, `Below` 给余尾 Ω. 辅助系统: 换基层号 `h₁ 1 ⊕ ↑ 0 1` (孩子 1 的偏移) 的 Ω 树的顶结点在孩子 tt 的顶槽位上, 无证据 (`top-noEv`), 层号就是目标, `AboveL` 给余尾 ω.

```agda
  module Tw1 (β : Tr⁺ (h₁ (suc zero))) (x : Tr (tw 1)) where
    open M zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) (B₀ (tw 1)) (h₁ (suc zero)) (suc zero) self
      (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero))
    module Mn = OCF.Lean.YiBLFold.Main zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) (B₀ (tw 1)) (h₁ (suc zero)) (suc zero) self
                  (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero))
    open Aux (h₁ (suc zero)) using (top-noEv)

    pᴮ : Pos (tw 1)
    pᴮ = inj₁ (inj₁ tt)

    qᴮ : Pos (h₁ (suc zero))
    qᴮ = inj₂ (tt , inj₁ tt)

    tw1-below : CΩᴹ (col (h₁ (suc zero)) (om (lv zero))) (lv zero)
    tw1-below = proj₁ (belowᴮᴹ (Mn.rt β) tt tt pᴮ {t = om (lv zero)} refl refl qᴮ refl)

    pᴬ : Pos (h₁ (suc zero) ⊕ ↑ zero (suc zero))
    pᴬ = inj₂ (tt , inj₁ tt)

    tw1-above : Cωᴹ (col (h₁ (suc zero)) (om (lv (h₁ (suc zero)))))
    tw1-above = proj₁ (proj₂ (aboveᴬᴹ (Mn.Srᴮ β (suc zero) x) tt tt pᴬ {t = om (lv (h₁ (suc zero)))} (λ _ → zero) tt refl refl
      (λ _ _ _ → tt) (top-noEv sS (λ _ → zero) (Mn.oᴮ (suc zero)) (B₀ _) (Mn.Φᴮ (Mn.rt β) x) tt) self))
```
