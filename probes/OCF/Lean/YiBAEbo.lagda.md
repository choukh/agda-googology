# EBO 参照上的 `Below` 与 `AboveL`: 换基折叠的两个系统

> 验收文件 (读记号). 判决: 编译定理, 不改树、折叠、合法性. 主线关系 `YiGIRel.R` 连同换基折叠填进 `Graded` (`gradedᴱ`; 上下文是坍缩下标 ν 与前缀 P, 参照 ψ_ν(P + a), ν 空即主线的 ψ₀).
> `Below` 条件成立: 在 `KeepAt j ν` (目标每个真槽位层读出的 μ 都有 μ+1 ≤ ν, 只看层号与记号的字面比较) 之下对 `XReb` 的一切实例两个系统都成立, 主系统结点出口随之成立 (`BelowE`); 塔第 1 项 (目标 `h₁ 1`, ν = 1) 条件成立 (`keep-tw1`, `Tw1Keep`). ψ₀ (更一般地 1 > ν) 的根上下文下 `Below` 与主系统 `NodeRef` 不成立, 反例在 `KD` 里 Ω 树的保留顶槽位 (`¬below`, `¬noderef`, `Tw1Main`).
> `AboveL` 否定: 对一切 ψ_ν(P + ·) 形状的上下文, 塔第 1 项换基行孩子 1 的替身 (该换基层号的 Ω 树) 的顶结点上, 精确参照 Ω_2 使 `AboveL` 不成立 (`¬above`, `¬above-tw1`): ν ≤ 1 时坍缩, 链第 0 项被迫是 Ω_1, 而树的链从零树起 (`R-zero`); ν ≥ 2 时不坍缩. 较小的 Ω_1 在 ν ≥ 1 下使辅助系统结点出口本身不成立 (`¬nodeout`), 参照不精确, 读作谓词太宽. 不给出值的定理; 去掉逐项对齐的较弱形式在 [YiBAWeak](YiBAWeak.lagda.md). 来源: 生成规则与生成原理照 `YiFIGen` (`weakᴷ` 等), `hRᴮ` 照 `YiGLDom.dom-top` 的 `dN` 行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBAEbo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiBSBase
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiKVRel as KV
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiFIGen using (module Ind; →low; low→)
open import OCF.Lean.YiGIBlock using (blkᵍ)
open import OCF.Lean.YiBLFold using (Bsᴮ; foldᴮ; rowsᴮ; Sₙ; rcₙ; route-tw1; module Aux)
import OCF.Lean.YiBLFold as BLF
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiQDFold using (kept-tw1)
open import OCF.Lean.YiXTIface
open import OCF.Lean.YiXTReb using (module XReb)
open import OCF.Lean.YiVALeaf using (nzs)
open import OCF.Lean.YiTBRow using (h₁)
open import OCF.Lean.YiGLDom using (dC; dz; dom-top)
open import OCF.Lean.YiNLCtx using (prefix)
open import OCF.Lean.YiBALemma
```

## 分级结构

关系、读法、槽位允许的余尾与 `YiGIInst.gradedᵍ` 相同; 上下文多一个坍缩下标 ν (`apE`), 底的条件照 `Bdᵍ`. 量化域不用 (本文不陈述 LowKeep).

```agda
apE : E.T × E.T → E.T → E.T
apE K a = E.ψ (proj₁ K) (proj₂ K ++ a) ∷ []

Bdᴱ : ∀ {ℓ j} → Bsᴮ ℓ → j ≤ ℓ → Tr⁺ j → E.T × E.T → Set
Bdᴱ {ℓ} {j} (o , r , b) w β K = GR.R j (apE K []) (proj₁ β) × (∀ i u → proj₁ (Ωt i) KV.⊴ proj₁ (b i u))

gradedᴱ : Graded blkᵍ foldᴮ rowsᴮ refᴱ 𝕍
gradedᴱ = record { ℓ₀ = zero ; v = KV.readRW ; R = GR.R ; Rd = GR.Rd ; Nu = GR.Nu ; bt = proj₁
                 ; cl = λ _ t → E.ψ [] t ∷ [] ; Cx = λ _ _ → E.T × E.T ; app = apE ; Bd = Bdᴱ }

domsᴱ : Doms blkᵍ foldᴮ
domsᴱ = record { Gx = λ _ _ → ⊤ ; Gb = λ _ _ → ⊤ ; Wl = λ _ → ⊤ ; Gl = λ _ _ → ⊤ }

open Laws gradedᴱ domsᴱ using (Weak; Lim; Node; Zero; Succ; Emb)
open FI gradedᴱ domsᴱ using (Gen⁺)
open Row gradedᴱ domsᴱ using (Rules)
```

生成规则与生成原理 (照 `YiFIGen` 的 `weakᴷ`, `limᴷ`, `nodeᴷ`, `genᴷ`, 换成 `gradedᴱ`); 只用于实例化 `XReb.WithR`.

```agda
weakᴱ : Weak
weakᴱ {ℓ = zero}   = H.mw
weakᴱ {ℓ = nd s h} = H.mw

limᴱ : Lim
limᴱ {ℓ = zero}   = H.mL
limᴱ {ℓ = nd s h} = H.mL

nodeᴱ : Node
nodeᴱ {ℓ = zero}   () g e nu hyp
nodeᴱ {ℓ = nd s h} p  g e nu hyp = H.mΩ e nu (λ η c l → hyp η c (low→ (nd s h) p l))

zeroᴱ : Zero
zeroᴱ {ℓ = zero}   {t} {x} e = subst (λ τ → GR.R zero τ x) (sym (c0→[] t e)) H.mz
zeroᴱ {ℓ = nd s h} {t} {x} e = subst (λ τ → GR.R (nd s h) τ x) (sym (c0→[] t e)) H.mz

succᴱ : Succ
succᴱ {ℓ = zero}   e r = H.m1 e r
succᴱ {ℓ = nd s h} e r = H.m1 e r

embᴱ : Emb
embᴱ {ℓ = zero}   () y r ry
embᴱ {ℓ = nd s h} c (y , e) r ry = H.mU r ry

leRᴱ : ∀ {j s t o} → s ≤ᵀ t → GR.R j t o → GR.R j s o
leRᴱ {j = zero}   = H.mc
leRᴱ {j = nd s h} = H.mc

genᴱ : ∀ ℓ → Gen⁺ _≤ᵀ_ ℓ
genᴱ zero Q rs qc = Ind.ind Q (qz refl) q1 qL (λ ()) (λ ()) qw qc
  where open Rules rs
genᴱ (nd s h) Q rs qc = Ind.ind Q (qz refl) q1 qL
  (λ p g e nu hR hQ → qΩ p g e nu (λ η c l → hR η c (→low (nd s h) p l)) (λ η c l → hQ η c (→low (nd s h) p l)))
  (λ c y e m q ch → qU c (y , e) m q ch) qw qc
  where open Rules rs
```

## `Below` 在条件 `KeepAt` 之下

`KeepAt j ν`: 目标 j 的每个真槽位层能读出的每个 μ, 都有 μ+1 ≤ ν (记号的字面比较). 条件只看层号与 ν, 不看树, 不看状态. `rk`: 槽位与目标真槽位同层时, 保持余尾与代入交换来自 `keepψ`, 余尾下标经同层搬到目标槽位.

```agda
KeepAt : L → E.T → Set
KeepAt j ν = ∀ (q : Pos j) {μ} → GR.Rd (at j q) μ → NotGt (E.cmpᵀ (E.sucT μ) ν)

rk : ∀ j {a} (K : E.T × E.T) → KeepAt j (proj₁ K) → (p : Pos a) → ∀ {t κ} → E.cof t ≡ E.cΩ κ → GR.Nu a p κ
  → (q : Pos j) → at j q ≡ at a p
  → (E.cof (apE K t) ≡ E.cΩ κ) × (∀ η → E.fsT (apE K t) η ≡ apE K (E.fsT t η)) × GR.Nu j q κ
rk j {a} K kt p {t} {κ} e nu q lq = proj₁ ψk , proj₂ ψk , rd→nu j q rd
  where
  rd : GR.Rd (at j q) κ
  rd = subst (λ b → GR.Rd b κ) (sym lq) (nu→rd a p nu)
  ψk = keepψ (proj₁ K) (proj₂ K) t e (kt q rd)

module BelowE (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u) where
  open XReb gradedᴱ domsᴱ k h o S rc B j c′ v u eq (E.T × E.T) apE (λ _ K → KeepAt j (proj₁ K))
    (E.T × E.T) apE (λ _ K → KeepAt j (proj₁ K)) public
  open XT gradedᴱ domsᴱ
  open QD gradedᴱ domsᴱ using (NodeOut)

  belowᴱᴮ : Below sysᴮ
  belowᴱᴮ s K bd p e nu q lq = rk j K bd p e nu q lq

  belowᴱᴬ : Below sysᴬ
  belowᴱᴬ s K bd p e nu q lq = rk j K bd p e nu q lq

  nodeᴱᴮ : NodeOut sysᴮ keepᴮ Dᴮ
  nodeᴱᴮ = nodeᴮ belowᴱᴮ
```

塔第 1 项: 目标 `h₁ 1` 的真槽位只有一个, 在第 0 层; 第 0 层只读出 0 (`rd0`), 而 1 ≤ 1.

```agda
keep-tw1 : KeepAt (h₁ (suc zero)) (E.𝟏 ∷ [])
keep-tw1 (inj₁ ())
keep-tw1 (inj₂ (tt , inj₂ ()))
keep-tw1 (inj₂ (tt , inj₁ tt)) r with rd0 r
... | refl = tt
```

## 塔第 1 项上的否定

目标 `h₁ 1`, 主系统是 `YiBLFold.Tw1` 的根状态; 参照一侧的上下文、作用、条件任取. 两个参照项: Ω_1 (`t₁`, 正规叶, 代入是恒等) 与 Ω_{Ω_1} (`t₂`, 代入 η 得 Ω_η). 余尾都是 Ω_1 (κ = 0).

```agda
t₁ t₂ : E.T
t₁ = E.ψ (E.𝟏 ∷ []) [] ∷ []
t₂ = E.ψ t₁ [] ∷ []

Ω₂ : E.T
Ω₂ = E.ψ (E.𝟏 ∷ E.𝟏 ∷ []) [] ∷ []

cω≢cΩ : ∀ {μ} → E.cω ≡ E.cΩ μ → ⊥
cω≢cΩ ()

refute : {X Y : Set} → (X → ⊥) → (Y → ⊥) → X ⊎ Y → ⊥
refute f g (inj₁ x) = f x
refute f g (inj₂ y) = g y

j₁ : L
j₁ = h₁ (suc zero)

module Tw1Neg (B : Base (tw 1))
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → E.T → E.T) (Bdᴬ : ∀ {a} → Aux.Stᴬ j₁ a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → E.T → E.T)
    (Bdᴮ : ∀ {a} → BLF.Main.Stᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B j₁ (suc zero) self
                     (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero)) a → Cxtᴮ → Set) where
  module Mn = BLF.Main zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B j₁ (suc zero) self (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero))
  open XReb gradedᴱ domsᴱ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B j₁ (suc zero) self
    (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero)) Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ public
  open XT gradedᴱ domsᴱ
  open QD gradedᴱ domsᴱ using (NodeOut; NodeRef)
```

主系统: Ω 树 `Ωt (tw 1)` 的顶槽位 (第 0 层, 保留, 所以这棵树在 `KD` 里), 目标的真槽位 `qᴮ` 同层. 只要根上的上下文是 ψ_ν(P + ·) 且 1 > ν (ν 空即主线), 参照把余尾 Ω_1 坍缩成 ω, 与 `Below` 及保留一支的 `NodeRef` 矛盾. 分支关系 `hRᴮ` 照 `YiGLDom.dom-top` 的 `dN` 一行.

```agda
  pᴮ : Pos (tw 1)
  pᴮ = inj₁ (inj₁ tt)

  qᴮ : Pos j₁
  qᴮ = inj₂ (tt , inj₁ tt)

  ¬below : (β : Tr⁺ j₁) (K : Cxtᴮ) → Bdᴮ (Mn.rt β) K → (ν P : E.T) → (∀ a → apᴮ K a ≡ E.ψ ν (P ++ a) ∷ [])
    → E.cmpᵀ (E.𝟏 ∷ []) ν ≡ E.gt → Below sysᴮ → ⊥
  ¬below β K bd ν P eK g bl =
    cω≢cΩ (trans (sym (proj₁ (collψ ν P t₁ {κ = []} refl g))) (trans (cong E.cof (sym (eK t₁)))
      (proj₁ (bl (Mn.rt β) K bd pᴮ {t = t₁} {κ = []} refl (GR.c0 refl) qᴮ refl))))

  gᴮ : Tr zero → Tr (tw 1)
  gᴮ c = proj₁ (upz c (Ωt (h₁ c)))

  dᴮ : KD (Ω pᴮ gᴮ)
  dᴮ = Ωt-in (kept-tw1 (nzs zero))

  hRᴮ : ∀ η c → GR.R zero η c → GR.R (tw 1) (E.fsT t₂ η) (gᴮ c)
  hRᴮ η c r = H.mU H.mz (dom-top (dC (prefix zero) zero (dz zero) r))

  ¬noderef : (β : Tr⁺ j₁) (K : Cxtᴮ) → Bdᴮ (Mn.rt β) K → (ν P : E.T) → (∀ a → apᴮ K a ≡ E.ψ ν (P ++ a) ∷ [])
    → E.cmpᵀ (E.𝟏 ∷ []) ν ≡ E.gt → NodeRef sysᴮ keepᴮ Dᴮ ntᴮ → ⊥
  ¬noderef β K bd ν P eK g nr =
    cω≢cΩ (trans (sym (proj₁ (collψ ν P t₂ {κ = []} refl g))) (trans (cong E.cof (sym (eK t₂)))
      (proj₁ (nr (Mn.rt β) K bd pᴮ {t = t₂} {κ = []} gᴮ dᴮ refl (GR.c0 refl) hRᴮ))))
```

辅助系统: 换基行在孩子 1 上的状态 `Srᴮ β 1 x` (层号 `h₁ 1 ⊕ ↑ 0 1`, 即 `h₁ 1` 的后继形状), 树是它的替身 `subᴮ 1 x` (该层的 Ω 树, `sub-is`). 顶结点在孩子 tt 的顶槽位上: 无证据 (`top-noEv`), 层号就是目标. 参照项取正规叶 t (代入是恒等), 余尾下标 κ 是槽位层能读出的.

```agda
  module AuxNode (β : Tr⁺ j₁) (x : Tr (tw 1)) where
    open Aux j₁ using (top-noEv)

    sA : Aux.Stᴬ j₁ (j₁ ⊕ ↑ zero (suc zero))
    sA = Mn.Srᴮ β (suc zero) x

    pᴬ : Pos (j₁ ⊕ ↑ zero (suc zero))
    pᴬ = inj₂ (tt , inj₁ tt)

    gᴬ : Tr j₁ → Tr (j₁ ⊕ ↑ zero (suc zero))
    gᴬ c = up zero tt (suc c) (z◃ c ◃s)

    sub-is : Ω pᴬ gᴬ ≡ Mn.subᴮ (suc zero) x
    sub-is = refl

    neᴬ : Aux.Evᴬ j₁ sA pᴬ → ⊥
    neᴬ = top-noEv sS (λ _ → zero) (Mn.oᴮ (suc zero)) (B₀ _) (Mn.Φᴮ (Mn.rt β) x) tt

    hRᴬ : ∀ t → (∀ η → E.fsT t η ≡ η) → ∀ η c → GR.R j₁ η c → GR.R (j₁ ⊕ ↑ zero (suc zero)) (E.fsT t η) (gᴬ c)
    hRᴬ t ft η c r = subst (λ τ → GR.R (j₁ ⊕ ↑ zero (suc zero)) τ (gᴬ c)) (sym (ft η)) (H.mU H.mz (H.mw r ◃s))
```

`AboveL` 给出的链 γ 必须对着树自己的链 (从零树起) 逐项; ψ_ν 不坍缩时余尾不是 ω, 坍缩时第 0 项是 Ω_κ ≠ 0. 对 `WithR` 的一切参数成立.

```agda
    module _ (Le : E.T → E.T → Set) (wk : Weak) (lm : Lim) (nod : Node) (zr : Zero) (sr : Succ) (em : Emb)
        (leR : ∀ {s t o} → Le s t → GR.R j₁ t o → GR.R j₁ s o) (gen : ∀ a → Gen⁺ Le a) where
      open WithR Le wk lm nod zr sr em leR gen

      ¬above : (K : Cxtᴬ) → Bdᴬ sA K → (ν P : E.T) → (∀ a → apᴬ K a ≡ E.ψ ν (P ++ a) ∷ [])
        → (t κ : E.T) → E.cof t ≡ E.cΩ κ → (∀ η → E.fsT t η ≡ η) → GR.Rd j₁ κ
        → AboveL sysᴬ keepᴬ Dᴬ xtᴬ → ⊥
      ¬above K bd ν P eK t κ et ft nu ab = go (E.cmpᵀ (E.sucT κ) ν) refl
        where
        r = ab sA K bd pᴬ {t = t} {κ = κ} gᴬ tt et nu (hRᴬ t ft) neᴬ self
        go : (m : E.Cmp) → E.cmpᵀ (E.sucT κ) ν ≡ m → ⊥
        go E.gt g = Ω≢[] (trans γ (R-zero j₁ (proj₂ (proj₂ (proj₂ r)) 0)))
          where
          Ω≢[] : E.Ωt κ ≡ [] → ⊥
          Ω≢[] ()
          γ : E.Ωt κ ≡ proj₁ r 0
          γ = trans (sym (ft (E.Ωt κ))) (trans (ψ∷-canc P
                (trans (sym (proj₂ (collψ ν P t et g) 0))
                (trans (cong (λ τ → E.fsn τ 0) (sym (eK t)))
                (trans (proj₁ (proj₂ (proj₂ r)) 0) (eK (E.fsT t (proj₁ r 0)))))))
                (ft (proj₁ r 0)))
        go E.lt g = cω≢cΩ (trans (sym (proj₁ (proj₂ r))) (trans (cong E.cof (eK t))
                      (proj₁ (keepψ ν P t et (subst NotGt (sym g) tt)))))
        go E.eq g = cω≢cΩ (trans (sym (proj₁ (proj₂ r))) (trans (cong E.cof (eK t))
                      (proj₁ (keepψ ν P t et (subst NotGt (sym g) tt)))))
```

参照不坍缩时 (κ+1 ≤ ν), 辅助系统的结点出口本身不成立: 无证据, 余尾又不是 ω.

```agda
    ¬nodeout : (K : Cxtᴬ) → Bdᴬ sA K → (ν P : E.T) → (∀ a → apᴬ K a ≡ E.ψ ν (P ++ a) ∷ [])
      → (t κ : E.T) → E.cof t ≡ E.cΩ κ → (∀ η → E.fsT t η ≡ η) → GR.Rd j₁ κ
      → NotGt (E.cmpᵀ (E.sucT κ) ν) → NodeOut sysᴬ keepᴬ Dᴬ → ⊥
    ¬nodeout K bd ν P eK t κ et ft nu ng no =
      refute (λ r → neᴬ (proj₁ r))
             (λ r → cω≢cΩ (trans (sym (proj₁ (proj₂ (proj₂ r)))) (trans (cong E.cof (eK t)) (proj₁ (keepψ ν P t et ng)))))
             (no sA K bd pᴬ {t = t} {κ = κ} gᴬ tt et nu (hRᴬ t ft))
```

## 实例: 前提可满足

主线 (ν 空): 根上下文 `([] , P)`, 根条件取 `Bdᵍ` 的第一项 (底值不低于 ψ₀(P)); 标准根 (β 是第 1 层的 Ω 树, P 空) 满足它 (`root-ok`). 这时 `Below` 与主系统的 `NodeRef` 都不成立.

```agda
module Tw1Main (B : Base (tw 1)) where
  BdM : ∀ {a} → BLF.Main.Stᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B j₁ (suc zero) self
                  (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero)) a → E.T × E.T → Set
  BdM (BLF.Main.rt β) K = GR.R j₁ (apE K []) (proj₁ β)

  open Tw1Neg B (E.T × E.T) apE (λ _ _ → ⊤) (E.T × E.T) apE BdM
  open XT gradedᴱ domsᴱ
  open QD gradedᴱ domsᴱ using (NodeRef)

  root-ok : BdM (Mn.rt (Ωt j₁)) ([] , [])
  root-ok = H.mw (H.mU H.mz (H.m1 refl H.mz)) ◃w

  main-¬below : ∀ β P → BdM (Mn.rt β) ([] , P) → Below sysᴮ → ⊥
  main-¬below β P bd = ¬below β ([] , P) bd [] P (λ _ → refl) refl

  main-¬noderef : ∀ β P → BdM (Mn.rt β) ([] , P) → NodeRef sysᴮ keepᴮ Dᴮ ntᴮ → ⊥
  main-¬noderef β P bd = ¬noderef β ([] , P) bd [] P (λ _ → refl) refl

  main-¬below₀ : Below sysᴮ → ⊥
  main-¬below₀ = main-¬below (Ωt j₁) [] root-ok

  main-¬noderef₀ : NodeRef sysᴮ keepᴮ Dᴮ ntᴮ → ⊥
  main-¬noderef₀ = main-¬noderef (Ωt j₁) [] root-ok
```

按层号的参照 (ν = 1), 两个系统的条件都取 `KeepAt`: `Below` 两条与主系统结点出口成立; 辅助系统在替身顶结点上, 精确参照 Ω_2 (槽位层第 1 层的读法) 使 `AboveL` 不成立; 不精确的 Ω_1 使结点出口本身不成立.

```agda
module Tw1Keep (B : Base (tw 1)) (β : Tr⁺ j₁) (x : Tr (tw 1)) where
  KA : ∀ {a} → Aux.Stᴬ j₁ a → E.T × E.T → Set
  KA _ K = KeepAt j₁ (proj₁ K)

  KB : ∀ {a} → BLF.Main.Stᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B j₁ (suc zero) self
                 (lift zero (↑ zero (suc zero))) (route-tw1 (nzs zero)) a → E.T × E.T → Set
  KB _ K = KeepAt j₁ (proj₁ K)

  open Tw1Neg B (E.T × E.T) apE KA (E.T × E.T) apE KB
  open AuxNode β x
  open XT gradedᴱ domsᴱ
  open QD gradedᴱ domsᴱ using (NodeOut)
  open WithR _≤ᵀ_ weakᴱ limᴱ nodeᴱ zeroᴱ succᴱ embᴱ (leRᴱ {j = j₁}) genᴱ using (xtᴬ)

  below-tw1ᴮ : Below sysᴮ
  below-tw1ᴮ s K bd p e nu q lq = rk j₁ K bd p e nu q lq

  below-tw1ᴬ : Below sysᴬ
  below-tw1ᴬ s K bd p e nu q lq = rk j₁ K bd p e nu q lq

  node-tw1ᴮ : NodeOut sysᴮ keepᴮ Dᴮ
  node-tw1ᴮ = nodeᴮ below-tw1ᴮ

  ¬above-tw1 : (P : E.T) → AboveL sysᴬ keepᴬ Dᴬ xtᴬ → ⊥
  ¬above-tw1 P = ¬above _≤ᵀ_ weakᴱ limᴱ nodeᴱ zeroᴱ succᴱ embᴱ (leRᴱ {j = j₁}) genᴱ ((E.𝟏 ∷ []) , P) keep-tw1 (E.𝟏 ∷ []) P
    (λ _ → refl) Ω₂ (E.𝟏 ∷ []) refl (λ _ → refl) (GR.ca (inj₂ (refl , GR.c0 refl)))

  ¬node-tw1ᴬ : (P : E.T) → NodeOut sysᴬ keepᴬ Dᴬ → ⊥
  ¬node-tw1ᴬ P = ¬nodeout ((E.𝟏 ∷ []) , P) keep-tw1 (E.𝟏 ∷ []) P (λ _ → refl) t₁ [] refl (λ _ → refl) (GR.c0 refl) tt
```

`Hand₁` (换基行嵌入出口的上下文交接) 把根上下文的 ν 原样交给辅助系统, 前缀接上 t; 所以上面两种上下文是同一个 ν.

```agda
hand-form : ∀ {Cxtᴬ Cxtᴮ : Set} (apᴬ : Cxtᴬ → E.T → E.T) (apᴮ : Cxtᴮ → E.T → E.T) {K : Cxtᴮ} {K″ : Cxtᴬ} {t : E.T} (ν P : E.T)
  → (∀ a → apᴮ K a ≡ E.ψ ν (P ++ a) ∷ []) → (∀ a → apᴬ K″ a ≡ apᴮ K (t ++ a))
  → ∀ a → apᴬ K″ a ≡ E.ψ ν ((P ++ t) ++ a) ∷ []
hand-form apᴬ apᴮ {t = t} ν P eK eh a = trans (eh a) (trans (eK (t ++ a)) (cong (λ b → E.ψ ν b ∷ []) (sym (++-assoc P t a))))
```
