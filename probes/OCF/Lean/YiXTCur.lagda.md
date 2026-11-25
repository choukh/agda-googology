# 现行折叠上的出口分解: 只剩分叉一份, 对角分叉上与 `Below` 冲突

> 判决: 编译定理, 不读记号, 不改树、折叠、合法性. 系统 `sysᵀ`: `YiTBRow.ψ` 的一切状态 (证据, 比较表, 底, 目标路径, 底值), 域取全体; 出口由 `kexit` 给出 (`xpᵀ`), 链由 "关系对左加封闭" 给出 (`chᵀ`). `exactᵀ`: 在 `Below`, `AboveL` 之下 `NodeRef` 当且仅当分叉一份.
> 对一切 Ω 形状层号, 孩子 c 里的槽位字面是目标 `h c` 的槽位时出口是分叉 (`diag-cross`), 在 `Below` 与余尾不相交之下结点出口不成立 (`diag-stuck`, `diag-¬out`); R80 的分叉同样 (`r80-stuck`). 前提可满足: 平凡模型里全部前提成立, 得到结点出口 (`modelA-out`); 二值模型里 `Below` 与不相交成立, 结点出口不成立 (`modelB-¬out`).
> R94 (ℕ 极限层号, 嵌入在前面的孩子): 塔第 2 项上材料经孩子 0 进入, 目标在非零孩子里时落到回退行 (`r94-fallᶻ`). 不否定什么: 没有值的定理; `AddR`, `Move` 两段搬自 `YiQDFold`, 只换成 `foldᵍ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXTCur where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; node⁺)
import OCF.Lean.YiTBRow as TB
open import OCF.Lean.YiMTTab using (rbᶻ; ψ₀ᶻ)
open import OCF.Lean.YiCMExit using (NZ; nzs; nzl; nzΩ; nzu)
open import OCF.Lean.YiGIBlock using (blkᵍ; foldᵍ; rowsᵍ; slTᵍ)
open import OCF.Lean.YiAbsFrame using (Fold)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiFIFold using (node-eq)
open import OCF.Lean.YiQDFold using (GoodK; kp-good)
open import OCF.Lean.YiXTIface
open import OCF.Lean.YiXTKp
```

## 搬来的两段

`AddRᵍ` 同 `YiQDFold.AddR` (`add`, `cum-dom`, `chain-dom`); `MoveG.byGood` 同 `YiQDFold.Move.byGood`, 对任何折叠.

```agda
module AddRᵍ {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᵍ rowsᵍ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᵍ) (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set)
    (zr : Laws.Zero 𝔾 𝔻) (sr : Laws.Succ 𝔾 𝔻) (lm : Laws.Lim 𝔾 𝔻) (nod : Laws.Node 𝔾 𝔻) (em : Laws.Emb 𝔾 𝔻)
    (wk : Laws.Weak 𝔾 𝔻) (j : L) (leR : ∀ {s t o} → Le s t → Graded.R 𝔾 j t o → Graded.R 𝔾 j s o)
    (G : FI.Gen⁺ 𝔾 𝔻 Le j) where
  open Graded 𝔾 using () renaming (R to Rᵍ)

  add : (A : Tr j) → ∀ {τ y} → Rᵍ j τ y → Rᵍ j τ (A + y)
  add A = G (λ τ y → Rᵍ j τ (A + y)) (record
    { qz = λ e → zr e
    ; q1 = λ e _ q → sr e q
    ; qL = λ e _ h → lm e h
    ; qΩ = λ p g e nu _ h → nod p (λ z → A + g z) e nu h
    ; qU = λ { c (y , e) _ q ry → em c (y , e) q ry }
    ; qw = λ _ q d → wk q (+-mono A d) })
    (λ le _ q → leR le q)

  cum-dom : (F : ℕ → Tr j) → ∀ k {τ} → Rᵍ j τ (F k) → Rᵍ j τ (cum F k)
  cum-dom F zero    r = r
  cum-dom F (suc k) r = add (cum F k) r

  chain-dom : ∀ {X x₀} (G′ : X → Tr⁺ j) (S′ : X → X) → ∀ k {τ}
    → Rᵍ j τ (proj₁ (G′ (iter S′ x₀ k))) → Rᵍ j τ (proj₁ (node⁺ {x₀ = x₀} nothing G′ S′))
  chain-dom {x₀ = x₀} G′ S′ k r = wk (cum-dom (λ n → proj₁ (G′ (iter S′ x₀ n))) k r) (◃l k)

module MoveG {𝔽 : Fold blkᵍ} {ℜ : Rows blkᵍ 𝔽} {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ 𝔽 ℜ 𝕋 𝕍) where
  open Graded 𝔾 using () renaming (R to Rᵍ)

  trSl : ∀ {A B : L} (e : A ≡ B) {η : Ref.T 𝕋} {x : Tr A} → Rᵍ A η x → Rᵍ B η (subst Tr e x)
  trSl refl r = r

  byGood : ∀ {j a} {p : Pos a} (q : Pos j) (cv : Br j q → Br a p)
    → (Σ (at j q ≡ at a p) λ e → ∀ z → slTᵍ a p (cv z) ≡ subst Tr e (slTᵍ j q z))
    → ∀ η c → Rᵍ (at j q) η (slTᵍ j q c) → Rᵍ (at a p) η (slTᵍ a p (cv c))
  byGood {a = a} {p} q cv (e , cm) η c r = subst (Rᵍ (at a p) η) (sym (cm c)) (trSl e r)
```

## 系统

状态是 `YiTBRow.ψ` 的全部参数 (目标 j 固定). 证据是 `EvK`.

```agda
record Stᵀ (j a : L) : Set where
  constructor st
  field
    o : Ok a
    r : TB.Rb a
    B : Base a
    w : j ≤ a
    β : Tr⁺ j

Φᵀ : ∀ {j a} → Stᵀ j a → Tr a → Tr⁺ j
Φᵀ {j} {a} (st o r B w β) x = TB.ψ a o r B j w β x

Evᵀ : ∀ {j a} → Stᵀ j a → Pos a → Set
Evᵀ {j} {a} (st o r B w β) p = EvK j a o p w

module Cur {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᵍ rowsᵍ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᵍ) (j : L)
    (Cxt : Set) (ap : Cxt → Ref.T 𝕋 → Ref.T 𝕋) (Bd : ∀ {a} → Stᵀ j a → Cxt → Set) where
  open FI 𝔾 𝔻 using (Sys; Gen⁺)
  open QD 𝔾 𝔻
  open XT 𝔾 𝔻
  open Laws 𝔾 𝔻 using (_⊴_; Weak; Lim; Node; Zero; Succ; Emb) renaming (R to Rᵍ)
  open MoveG 𝔾

  sysᵀ : Sys j
  sysᵀ = record { St = Stᵀ j ; Φ = λ s x → proj₁ (Φᵀ s x) ; Ev = Evᵀ ; Cxt = Cxt ; ap = ap ; Bdˢ = Bd }

  keepᵀ′ : ∀ {a} (s : Stᵀ j a) (p : Pos a) (e : Evᵀ s p) (g : Br a p → Tr a)
    → Ω (proj₁ e) (λ c → proj₁ (Φᵀ s (g (proj₁ (proj₂ e) c)))) ⊴ proj₁ (Φᵀ s (Ω p g))
  keepᵀ′ {a} (st o r B w β) p (q , cv , e , eq) g = inj₁ (node-eq (kp a o p w) q cv e _ _ eq)

  keepᵀ : Sys.KeepLaw sysᵀ
  keepᵀ = record { slot = λ s p e → proj₁ e ; mvc = λ s p e c → proj₁ (proj₂ e) c ; keep = keepᵀ′ }

  D⊤ : ∀ {a} → Stᵀ j a → Tr a → Set
  D⊤ _ _ = ⊤

  toXᵀ : ∀ {a} o r B w β (p : Pos a) → KExit j a o p w → XPick sysᵀ (st o r B w β) p
  toXᵀ o r B w β p (kept e)            = kept e
  toXᵀ o r B w β p (high ne u)         = high ne u
  toXᵀ o r B w β p (cross ne c c′ u v) = cross ne c c′ u v

  xpᵀ : ∀ {a} (s : Stᵀ j a) (p : Pos a) → XPick sysᵀ s p
  xpᵀ {a} (st o r B w β) p = toXᵀ o r B w β p (kexit a o p w)

  lvlᵀ : ∀ {a} (s : Stᵀ j a) (p : Pos a) (e : Evᵀ s p) → at j (proj₁ e) ≡ at a p
  lvlᵀ {a} (st o r B w β) p (q , cv , e , eq) = kp-lvl a o p w q cv e eq

  mvRᵀ : ∀ {a} (s : Stᵀ j a) (p : Pos a) (e : Evᵀ s p) → ∀ η c
    → Rᵍ (at j (proj₁ e)) η (slTᵍ j (proj₁ e) c) → Rᵍ (at a p) η (slTᵍ a p (proj₁ (proj₂ e) c))
  mvRᵀ {a} (st o r B w β) p (q , cv , e , eq) = byGood q cv (subst (GoodK (at a p) (slTᵍ a p)) eq (kp-good a o p w))
```

链与分解: 链要第 j 层的关系对六条规则与向下封闭生成 (同 `YiQDFold.WithRules`).

```agda
  module WithR (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (zr : Zero) (sr : Succ) (lm : Lim) (nod : Node) (em : Emb) (wk : Weak)
      (leR : ∀ {s t o} → Le s t → Rᵍ j t o → Rᵍ j s o) (gen : Gen⁺ Le j) where
    open AddRᵍ 𝔾 𝔻 Le zr sr lm nod em wk j leR gen

    chᵀ : ∀ {a} (s : Stᵀ j a) (p : Pos a) (g : Br a p → Tr a) → D⊤ s (Ω p g) → (Evᵀ s p → ⊥) → Chain sysᵀ s p g
    chᵀ {a} (st o r B w β) p g _ ne = chainK (Rᵍ j) (kp a o p w) G′ S′ (chain-dom G′ S′) ne
      where
      G′ : Br a p → Tr⁺ j
      G′ z = TB.ψ a o r B j w β (g z)
      S′ : Br a p → Br a p
      S′ z = fromBr a p (proj₁ (TB.ψ a o r B (at a p) (posW a p) (B (at a p) (posW a p)) (g z)))

    xtᵀ : XTree sysᵀ keepᵀ D⊤
    xtᵀ = record { xp = xpᵀ ; ch = chᵀ ; lvl = lvlᵀ ; mvR = mvRᵀ }

    exactᵀ : Below sysᵀ → AboveL sysᵀ keepᵀ D⊤ xtᵀ
      → (NodeRef sysᵀ keepᵀ D⊤ (XTree.nt xtᵀ) → At sysᵀ keepᵀ D⊤ xtᵀ (PartX sysᵀ keepᵀ D⊤ xtᵀ))
      × (At sysᵀ keepᵀ D⊤ xtᵀ (PartX sysᵀ keepᵀ D⊤ xtᵀ) → NodeRef sysᵀ keepᵀ D⊤ (XTree.nt xtᵀ))
    exactᵀ = exact sysᵀ keepᵀ D⊤ xtᵀ

    outᵀ : Below sysᵀ → AboveL sysᵀ keepᵀ D⊤ xtᵀ → At sysᵀ keepᵀ D⊤ xtᵀ (PartX sysᵀ keepᵀ D⊤ xtᵀ)
      → NodeOut sysᵀ keepᵀ D⊤
    outᵀ = out sysᵀ keepᵀ D⊤ xtᵀ
```

## 对角分叉

Ω 形状层号 `nd (sΩ k) h`, 目标是孩子层号 `h c` 自己 (路径 `inc c self`), 槽位是孩子 c 里的 p′, 即目标的槽位. 出口是分叉, 而目标有同层的真槽位 p′.

```agda
module Diag {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᵍ rowsᵍ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᵍ) (k : L) (h : Tr k → L) (c : Tr k)
    (Cxt : Set) (ap : Cxt → Ref.T 𝕋 → Ref.T 𝕋) (Bd : ∀ {a} → Stᵀ (h c) a → Cxt → Set) where
  open Cur 𝔾 𝔻 (h c) Cxt ap Bd public
  open QD 𝔾 𝔻
  open XT 𝔾 𝔻
  open Laws 𝔾 𝔻 using (Cω; CΩ; Nu; fsT; slL; slT) renaming (R to Rᵍ)

  sᵈ : Ok (nd (sΩ k) h) → TB.Rb (nd (sΩ k) h) → Base (nd (sΩ k) h) → Tr⁺ (h c) → Stᵀ (h c) (nd (sΩ k) h)
  sᵈ o r B β = st o r B (inc c self) β

  pᵈ : Pos (h c) → Pos (nd (sΩ k) h)
  pᵈ p′ = inj₂ (c , inj₂ p′)

  IsX : ∀ {a} {s : Stᵀ (h c) a} {p : Pos a} → XPick sysᵀ s p → Set
  IsX (cross _ _ _ _ _) = ⊤
  IsX (kept _)          = ⊥
  IsX (high _ _)        = ⊥

  diag-cross : ∀ o r B β (p′ : Pos (h c)) → IsX (xpᵀ (sᵈ o r B β) (pᵈ p′))
  diag-cross o r B β p′ = tt

  noevᵈ : ∀ o r B β (p′ : Pos (h c)) → Evᵀ (sᵈ o r B β) (pᵈ p′) → ⊥
  noevᵈ o r B β p′ (_ , _ , _ , ())

  diag-stuck : Below sysᵀ → ∀ {κ} → (∀ {u} → Cω u → CΩ u κ → ⊥) → ∀ o r B β (p′ : Pos (h c)) K → Bd (sᵈ o r B β) K
    → {t : Ref.T 𝕋} (g : Br (h c) p′ → Tr (nd (sΩ k) h)) → CΩ t κ → Nu (nd (sΩ k) h) (pᵈ p′) κ
    → NodeRes sysᵀ keepᵀ (sᵈ o r B β) K (pᵈ p′) g t κ → ⊥
  diag-stuck bl dω o r B β p′ K bd g e nu =
    stuck sysᵀ bl dω {𝓀 = keepᵀ} (sᵈ o r B β) K bd (pᵈ p′) g e nu (noevᵈ o r B β p′) p′ refl

  diag-¬out : Below sysᵀ → ∀ {κ} → (∀ {u} → Cω u → CΩ u κ → ⊥) → NodeOut sysᵀ keepᵀ D⊤
    → ∀ o r B β (p′ : Pos (h c)) K → Bd (sᵈ o r B β) K → {t : Ref.T 𝕋} (g : Br (h c) p′ → Tr (nd (sΩ k) h))
    → CΩ t κ → Nu (nd (sΩ k) h) (pᵈ p′) κ
    → (∀ η c′ → Rᵍ (slL (nd (sΩ k) h) (pᵈ p′)) η (slT (nd (sΩ k) h) (pᵈ p′) c′) → Rᵍ (nd (sΩ k) h) (fsT t η) (g c′)) → ⊥
  diag-¬out bl dω no o r B β p′ K bd g e nu hR = diag-stuck bl dω o r B β p′ K bd g e nu (no (sᵈ o r B β) K bd (pᵈ p′) g tt e nu hR)
```

R80 的分叉 (`YiXTKp.r80-cross`): 塔第 3 项的孩子层号 `L′` 上, 下标侧槽位 (层号 `tw 1`) 朝目标 `tw 2`; 同样与 `Below` 冲突.

```agda
module R80Cur {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᵍ rowsᵍ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᵍ)
    (Cxt : Set) (ap : Cxt → Ref.T 𝕋 → Ref.T 𝕋) (Bd : ∀ {a} → Stᵀ (tw 2) a → Cxt → Set) where
  open Cur 𝔾 𝔻 (tw 2) Cxt ap Bd
  open QD 𝔾 𝔻
  open XT 𝔾 𝔻
  open Laws 𝔾 𝔻 using (Cω; CΩ; Nu)

  r80-stuck : Below sysᵀ → ∀ {κ} → (∀ {u} → Cω u → CΩ u κ → ⊥) → ∀ r B β K → Bd (st o′ r B (inu vs′) β) K
    → {t : Ref.T 𝕋} (g : Br L′ (inj₁ (inj₁ tt)) → Tr L′) → CΩ t κ → Nu L′ (inj₁ (inj₁ tt)) κ
    → NodeRes sysᵀ keepᵀ (st o′ r B (inu vs′) β) K (inj₁ (inj₁ tt)) g t κ → ⊥
  r80-stuck bl dω r B β K bd g e nu =
    stuck sysᵀ bl dω {𝓀 = keepᵀ} (st o′ r B (inu vs′) β) K bd (inj₁ (inj₁ tt)) g e nu ne (inj₁ (inj₁ tt)) r80-lit
    where
    ne : Evᵀ (st o′ r B (inu vs′) β) (inj₁ (inj₁ tt)) → ⊥
    ne (_ , _ , _ , eq) = jn (trans (sym eq) r80-drop)
```

## 前提可满足

平凡模型 (参照项只有一个, 关系处处成立): 生成原理按树的构造递归 (`genA`), 全部前提成立, 得到结点出口.

```agda
module ModelA (𝕍 : Val) where
  refA : Ref
  refA = record { T = ⊤ ; C0 = λ _ → ⊤ ; C1 = λ _ → ⊤ ; Cω = λ _ → ⊤ ; CΩ = λ _ _ → ⊤
                ; pred = λ _ → tt ; fsn = λ _ _ → tt ; fsT = λ _ _ → tt ; _⊕_ = λ _ _ → tt ; Ωr = λ _ → tt }

  gradedA : Graded blkᵍ foldᵍ rowsᵍ refA 𝕍
  gradedA = record { ℓ₀ = zero ; v = λ _ → Val.vz 𝕍 ; R = λ _ _ _ → ⊤ ; Rd = λ _ _ → ⊤ ; Nu = λ _ _ _ → ⊤
                   ; bt = proj₁ ; cl = λ _ t → t ; Cx = λ _ _ → ⊤ ; app = λ _ t → t ; Bd = λ _ _ _ _ → ⊤ }

  domsA : Doms blkᵍ foldᵍ
  domsA = record { Gx = λ _ _ → ⊤ ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ _ _ → ⊤ }

  open FI gradedA domsA using (Gen⁺)
  open Row gradedA domsA using (Rules)
  open XT gradedA domsA
  open QD gradedA domsA using (NodeOut)

  genA : ∀ a → Gen⁺ (λ _ _ → ⊤) a
  genA a Q rs _ _ = go _
    where
    open Rules rs
    go : (x : Tr a) → Q tt x
    go zero         = qz tt
    go (suc x)      = q1 tt tt (go x)
    go (lim f r)    = qw tt (go (f zero)) (◃l zero)
    go (Ω p g)      = qΩ p g tt tt (λ _ _ _ → tt) (λ η c _ → go (g c))
    go (up x c y e) = qU c (y , e) tt (go x) tt

  module _ (j : L) where
    open Cur gradedA domsA j ⊤ (λ _ t → t) (λ _ _ → ⊤)
    open WithR (λ _ _ → ⊤) (λ _ → tt) (λ _ _ → tt) (λ _ _ → tt) (λ _ _ _ _ _ → tt) (λ _ _ _ _ → tt) (λ _ _ → tt)
      (λ _ _ → tt) (genA j)

    belowA : Below sysᵀ
    belowA s K bd p e nu q lv = tt , (λ _ → refl) , tt

    aboveA : AboveL sysᵀ keepᵀ D⊤ xtᵀ
    aboveA s K bd p g d e nu hR ne u = (λ _ → tt) , tt , (λ _ → refl) , (λ _ → tt)

    crossA : At sysᵀ keepᵀ D⊤ xtᵀ (PartX sysᵀ keepᵀ D⊤ xtᵀ)
    crossA s K bd p g d e nu hR = px (xpᵀ s p)
      where
      px : (x : XPick sysᵀ s p) → PartX sysᵀ keepᵀ D⊤ xtᵀ s K p g d _ _ x
      px (kept _)          = tt
      px (high _ _)        = tt
      px (cross _ _ _ _ _) = (λ _ → tt) , tt , (λ _ → refl) , (λ _ → tt)

    modelA-out : NodeOut sysᵀ keepᵀ D⊤
    modelA-out = outᵀ belowA aboveA crossA
```

二值模型 (余尾 Ω 与余尾 ω 是两个不同的值, 上下文不改参照项): `Below` 与不相交成立; 塔第 1 项的对角分叉 (孩子 1, 槽位层号第 0 层) 上结点出口不成立.

```agda
module ModelB (𝕍 : Val) where
  refB : Ref
  refB = record { T = Bool ; C0 = λ _ → ⊥ ; C1 = λ _ → ⊥ ; Cω = λ t → t ≡ false ; CΩ = λ t _ → t ≡ true
                ; pred = λ t → t ; fsn = λ t _ → t ; fsT = λ t _ → t ; _⊕_ = λ t _ → t ; Ωr = λ t → t }

  gradedB : Graded blkᵍ foldᵍ rowsᵍ refB 𝕍
  gradedB = record { ℓ₀ = zero ; v = λ _ → Val.vz 𝕍 ; R = λ _ _ _ → ⊤ ; Rd = λ _ _ → ⊤ ; Nu = λ _ _ _ → ⊤
                   ; bt = proj₁ ; cl = λ _ t → t ; Cx = λ _ _ → ⊤ ; app = λ _ t → t ; Bd = λ _ _ _ _ → ⊤ }

  domsB : Doms blkᵍ foldᵍ
  domsB = record { Gx = λ _ _ → ⊤ ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ _ _ → ⊤ }

  open XT gradedB domsB
  open QD gradedB domsB using (NodeOut)
  open Diag gradedB domsB zero TB.h₁ (suc zero) ⊤ (λ _ t → t) (λ _ _ → ⊤)

  belowB : Below sysᵀ
  belowB s K bd p e nu q lv = e , (λ _ → refl) , tt

  dωB : ∀ {u : Bool} → u ≡ false → u ≡ true → ⊥
  dωB refl ()

  modelB-¬out : NodeOut sysᵀ keepᵀ D⊤ → ⊥
  modelB-¬out no = diag-¬out belowB {κ = true} dωB no (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) (Ωt (TB.h₁ (suc zero)))
    (inj₂ (tt , inj₁ tt)) tt tt {t = true} (λ _ → zero) refl tt (λ _ _ _ → tt)
```

## R94: 嵌入在前面的孩子

ℕ 极限层号 Λ, 嵌入在孩子 1, 目标经孩子 2 (`way` 给 `tw 1 ≤ tw 2` 是 `ink self`): 材料经 `emb` 进 `tw 2` 的孩子 0 (层号 `tw 1`, 即地板). 目标再经 `tw 2` 的非零孩子 c 时, 表 `rbᶻ` 在 (0, c) 上的条目要求孩子 0 的层号字面是零层, 这里不是, 所以是回退行: 前缀的折叠加 y 折到第 0 层.

```agda
r94-fallᶻ : (B : Base Λ) (i : L) {c : Tr (tw 1)} (v : i ≤ tw 1 ⊕ ↑ (tw 1) c) (β : Tr⁺ i) (x : Tr Λ)
  (y : Tr (tw 1)) (e : tw 1 ⊢ zero ◃ y) → NZ c
  → TB.ψ Λ Ok-Λ (rbᶻ Λ) B i (inc 2 (inc c v)) β (up x 1 y e)
  ≡ TB.ψ Λ Ok-Λ (rbᶻ Λ) B i (inc 2 (inc c v)) β x ⊞ ψ₀ᶻ (tw 1) (Ok-tw 1) y
r94-fallᶻ B i v β x y e (nzs _)       = refl
r94-fallᶻ B i v β x y e (nzl _ _)     = refl
r94-fallᶻ B i v β x y e (nzΩ _ _)     = refl
r94-fallᶻ B i v β x y e (nzu _ _ _ _) = refl
```
