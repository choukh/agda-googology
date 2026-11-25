# 换基律的树一侧实例: `YiBSFold` 的换基行

> 判决: 编译定理, 不读记号. 辅助系统是换基层号 `j ⊕ b` 上沿 `lift j b` 的 `YiRBSib.ψ` (无证据) 连同到达 j 之后的上折 `Up`: 保留律 (`keepᴬ`), 回退律 (`fallᴬ`), 单调 (`monoᴬ`) 都成立. 主系统是 `YiBSFold.ψ` 在 Ω 形状层号上, 目标经孩子 c′ 且 `route` 落在地板之上 (`inj₂ u`) 的根状态: 保留律 (`keepᴮ`), 换基律 (`rebᴮ`; `lw` 是 `lift`, 副本证据 `ev-cp` 由 `lift` 给出), 接上 `YiBLIface` 得 `lowᴮ`; 塔各项是实例 (`lowᵗ`, 第 1 项的 `route` 由 `route-tw1` 给出).
> `Out.nodeE` 在换基下: 副本槽位上证据, 槽位与分支换型都由 `lift` 实填 (`nodeE-cp`), 只剩参照一侧的三项; 替身自己的孩子层槽位不保留 (`top-noEv`), 只能走链; 主系统孩子槽位的结点照旧不保留 (`main-noEv`, 即 `YiFINeg.kp-drop`).
> 不给出什么: 出口 `OutR` 与辅助系统的 `Out` 是前提, 没有实填; 不处理 `route` 落在地板之下与无证据的行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBLFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp; kp⁼; node⁺)
import OCF.Lean.YiRBSib as R
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiGIBlock using (blkᵍ; chLᵍ; ChTᵍ; chTᵍ; upᵍ; slTᵍ)
open import OCF.Lean.YiAbsFrame using (Block; Fold)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiFIFold using (node-eq)
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiVALeaf using (NZ; nzs; nzl)
open import OCF.Lean.YiTBRow using (h₁)
```

## 填进 `Fold`, `Rows`

块用 `YiGIBlock.blkᵍ`; 底是 (合法证据, 换基证据 `YiBSBase.Rb`, 原底). `Rows` 与 `YiGIBlock.rowsᵍ` 逐项相同.

```agda
Bsᴮ : L → Set
Bsᴮ ℓ = Ok ℓ × Rb ℓ × Base ℓ

dnᴮ : (ℓ : L) → Bsᴮ ℓ → (c : CH ℓ) → Tr ℓ → Bsᴮ (chLᵍ ℓ c)
dnᴮ (nd s h) (o , r , b) c x = proj₂ o c , proj₂ r c , λ j w → BS.ψ (nd s h) o r b j (inc c w) (b j (inc c w)) x

foldᴮ : Fold blkᵍ
foldᴮ = record
  { Bs = Bsᴮ ; LegB = λ _ _ → ⊤ ; Bt = Tr⁺ ; LegT = λ _ _ → ⊤
  ; ψ  = λ ℓ b j w β x → proj₁ (BS.ψ ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w β x)
  ; ψβ = λ ℓ b j w β x → BS.ψ ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w β x
  ; dn = dnᴮ }

rowsᴮ : Rows blkᵍ foldᴮ
rowsᴮ = record
  { sc = suc ; Sl = Pos ; slL = at ; SlT = Br ; slT = slTᵍ ; nd = Ω
  ; Ωt = λ ℓ → proj₁ (Ωt ℓ) ; Dn = Dn ; upf = λ {ℓ} {j} d β y → proj₁ (Up j d β y)
  ; sucL = λ ℓ → nd sS (λ _ → ℓ) ; ΩL = λ k h → nd (sΩ k) h ; lift = ↑ }

infix 4 _⊴ᵗ_
_⊴ᵗ_ : ∀ {ℓ} → Tr ℓ → Tr ℓ → Set
x ⊴ᵗ y = (x ≡ y) ⊎ (Lt (Sig _) x y)

dn₁ : (a : L) (c : CH a) → Dn a (chLᵍ a c)
dn₁ zero     ()
dn₁ (nd s h) c = down stop c

fall-self : (j : L) (o : Ok j) (B : Base j) (β : Tr⁺ j) (x : Tr j) (c : CH j) (y : ChTᵍ j c)
  → Up (chLᵍ j c) (dn₁ j c) (R.ψ j o (R.rb-no j) B j self β x) (chTᵍ j c y) ≡ R.ψ j o (R.rb-no j) B j self β (upᵍ x c y)
fall-self (nd s h) o B β x c (y , e) = refl

cW-eq : ∀ {A B X : Set} (W : A ⊎ B) {F : A → X} {G : B → X} {b : B} → W ≡ inj₂ b → cW W F G ≡ G b
cW-eq .(inj₂ _) refl = refl
```

## 辅助系统: 换基层号上沿 `lift` 的折叠

状态: 换基层号 `j ⊕ b` 上 (路径 `lift j b`, 全是 `inu`), 或到达 j 以后沿下行链的上折. 前者在 b 的孩子上回退进 `j ⊕ h c`, b 取尽时进上折; 都不比较孩子.

```agda
module Aux (j : L) where
  data Stᴬ : L → Set where
    rbs : (b : L) → Ok (j ⊕ b) → Base (j ⊕ b) → Tr⁺ j → Stᴬ (j ⊕ b)
    us  : ∀ {a} → Dn j a → Tr⁺ j → Stᴬ a

  Φᴬ : ∀ {a} → Stᴬ a → Tr a → Tr⁺ j
  Φᴬ (rbs b o B β) x = R.ψ (j ⊕ b) o (R.rb-no (j ⊕ b)) B j (lift j b) β x
  Φᴬ (us {a} d β) x  = Up a d β x

  Evᴬ : ∀ {a} → Stᴬ a → Pos a → Set
  Evᴬ (rbs b o B β) p = Σ (Pos j) λ q → Σ (Br j q → Br (j ⊕ b) p) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr (j ⊕ b) p zero) λ e
    → kp (j ⊕ b) o p (lift j b) ≡ just (q , cv , e)
  Evᴬ (us d β) p = ⊤

  slotᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) → Evᴬ s p → Pos j
  slotᴬ (rbs b o B β) p e = proj₁ e
  slotᴬ (us d β) p e = mv d p

  mvcᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) (e : Evᴬ s p) → Br j (slotᴬ s p e) → Br a p
  mvcᴬ (rbs b o B β) p e z = proj₁ (proj₂ e) z
  mvcᴬ (us d β) p e z = mvBr d p z

  keepᴬ′ : ∀ {a} (s : Stᴬ a) (p : Pos a) (e : Evᴬ s p) (g : Br a p → Tr a)
    → Ω (slotᴬ s p e) (λ c → proj₁ (Φᴬ s (g (mvcᴬ s p e c)))) ⊴ᵗ proj₁ (Φᴬ s (Ω p g))
  keepᴬ′ (rbs b o B β) p (q , cv , e , eq) g = inj₁ (node-eq (kp (j ⊕ b) o p (lift j b)) q cv e _ _ eq)
  keepᴬ′ (us d β) p e g = inj₁ refl

  dnD : ∀ {a} → Dn j a → (c : CH a) → Dn j (chLᵍ a c)
  dnD {a = zero} d ()
  dnD {nd s h} d c = down d c

  stepᴬ : ∀ {a} → Stᴬ a → (c : CH a) → Tr a → Stᴬ (chLᵍ a c)
  stepᴬ (rbs zero o B β) c x = us (dn₁ j c) (Φᴬ (rbs zero o B β) x)
  stepᴬ (rbs (nd s h) o B β) c x =
    rbs (h c) (proj₂ o c) (λ i u → R.ψ (j ⊕ nd s h) o (R.rb-no _) B i (inc c u) (B i (inc c u)) x) (Φᴬ (rbs (nd s h) o B β) x)
  stepᴬ (us {a} d β) c x = us (dnD d c) (Up a d β x)

  fallᴬ′ : ∀ {a} (s : Stᴬ a) (c : CH a) (x : Tr a) (y : ChTᵍ a c)
    → proj₁ (Φᴬ (stepᴬ s c x) (chTᵍ a c y)) ⊴ᵗ proj₁ (Φᴬ s (upᵍ x c y))
  fallᴬ′ (rbs zero o B β) c x y = inj₁ (cong proj₁ (fall-self j o B β x c y))
  fallᴬ′ (rbs (nd s h) o B β) c x (y , e) = inj₁ refl
  fallᴬ′ (us {a = zero} d β) () x y
  fallᴬ′ (us {nd s h} d β) c x (y , e) = inj₁ refl

  monoᴬ′ : ∀ {a} (s : Stᴬ a) {x y : Tr a} → a ⊢ x ◃ y → j ⊢ proj₁ (Φᴬ s x) ◃ proj₁ (Φᴬ s y)
  monoᴬ′ (rbs b o B β) d = R.mono (j ⊕ b) o (R.rb-no (j ⊕ b)) B j (lift j b) β d
  monoᴬ′ (us {a} d β) d′ = Upm a d β d′
```

目标层的槽位 q 沿 b 的任一条到叶子的孩子路径 (`Lf b`) 复制进 `j ⊕ b` (`cp`); 副本在 `lift j b` 下保留, 落回 q, 换型逐层是恒等 (`ev-cp`). `YiRKCell.keep-lift` 是第一孩子路径 (`lf`) 的情形. 替身层号 b = `nd s h` 时孩子层号自身的槽位 (`j ⊕ h c`, 不低于 j) 不保留 (`top-noEv`; `YiRKCell.seen-s` 是 b 为后继形状时替身的顶结点).

```agda
  data Lf : L → Set where
    here  : Lf zero
    there : ∀ {s h} (c : Ch s) → Lf (h c) → Lf (nd s h)

  lf : (b : L) → Lf b
  lf zero     = here
  lf (nd s h) = there (c₀ s) (lf (h (c₀ s)))

  cp : (b : L) → Lf b → Pos j → Pos (j ⊕ b)
  cp .zero     here                q = q
  cp .(nd _ _) (there {h = h} c l) q = inj₂ (c , inj₂ (cp (h c) l q))

  ev-cp : (b : L) (l : Lf b) (o : Ok (j ⊕ b)) (q : Pos j)
    → Σ (Br j q → Br (j ⊕ b) (cp b l q)) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr (j ⊕ b) (cp b l q) zero) λ e
      → kp (j ⊕ b) o (cp b l q) (lift j b) ≡ just (q , cv , e)
  ev-cp .zero     here                o q = (λ z → z) , refl , refl
  ev-cp .(nd _ _) (there {h = h} c l) o q = ev-cp (h c) l (proj₂ o c) q

  evᴬ-cp : (b : L) (l : Lf b) (o : Ok (j ⊕ b)) (B : Base (j ⊕ b)) (β : Tr⁺ j) (q : Pos j) → Evᴬ (rbs b o B β) (cp b l q)
  evᴬ-cp b l o B β q = q , ev-cp b l o q

  top-noEv : ∀ s h (o : Ok (j ⊕ nd s h)) B β (c : Ch s) → Evᴬ (rbs (nd s h) o B β) (inj₂ (c , inj₁ tt)) → ⊥
  top-noEv s h o B β c (q , cv , e , ())
```

## 主系统: 换基行的根状态

Ω 形状层号 ℓ = `nd (sΩ k) h`, 换基证据 `(just S , rc)`, 目标 j 经孩子 c′ (路径 `inc c′ v`), `route` 给出地板之上 (`eq`). 行的形状 `row-reb` 由 `eq` 得到, 不对孩子 c 分情形.

```agda
module Main (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
            (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j)
            (eq : route S j c′ v ≡ inj₂ u) where
  open Aux j

  ℓ : L
  ℓ = nd (sΩ k) h
  r : Rb ℓ
  r = just S , rc
  w : j ≤ ℓ
  w = inc c′ v
  oj : Ok j
  oj = downOk (h c′) (proj₂ o c′) j v

  data Stᴮ : L → Set where
    rt : Tr⁺ j → Stᴮ (nd (sΩ k) h)

  Φᴮ : ∀ {a} → Stᴮ a → Tr a → Tr⁺ j
  Φᴮ (rt β) x = BS.ψ ℓ o r B j w β x

  Evᴮ : ∀ {a} → Stᴮ a → Pos a → Set
  Evᴮ (rt β) p = Σ (Pos j) λ q → Σ (Br j q → Br ℓ p) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr ℓ p zero) λ e
    → kp ℓ o p w ≡ just (q , cv , e)

  slotᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) → Evᴮ s p → Pos j
  slotᴮ (rt β) p e = proj₁ e

  mvcᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) (e : Evᴮ s p) → Br j (slotᴮ s p e) → Br a p
  mvcᴮ (rt β) p e z = proj₁ (proj₂ e) z

  keepᴮ′ : ∀ {a} (s : Stᴮ a) (p : Pos a) (e : Evᴮ s p) (g : Br a p → Tr a)
    → Ω (slotᴮ s p e) (λ c → proj₁ (Φᴮ s (g (mvcᴮ s p e c)))) ⊴ᵗ proj₁ (Φᴮ s (Ω p g))
  keepᴮ′ (rt β) p (q , cv , e , eq′) g = inj₁ (node-eq (kp ℓ o p w) q cv e _ _ eq′)

  main-noEv : ∀ β (c : Tr k) (t : Pos⁼ (h c)) → Evᴮ (rt β) (inj₂ (c , t)) → ⊥
  main-noEv β c t (q , cv , e , ())

  monoᴮ′ : ∀ {a} (s : Stᴮ a) {x y : Tr a} → a ⊢ x ◃ y → j ⊢ proj₁ (Φᴮ s x) ◃ proj₁ (Φᴮ s y)
  monoᴮ′ (rt β) d = BS.mono ℓ o r B j w β d

  row-reb : ∀ β x c y e → BS.ψ ℓ o r B j w β (up x c y e)
    ≡ seen S j oj u (BS.ψ ℓ o r B j w β x) c ⊞ BS.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y
  row-reb β x c y e = cW-eq (route S j c′ v) eq
```

换基行的各项: 换基层号 `j ⊕ offsets S c`, 辅助状态 `rbs` (底值是 x 的像), 替身是该层的 Ω 树; 它的像就是 `seen`, 而行的输出是 `seen ⊞ 尾项`, 所以替身的像严格低于行的输出.

```agda
  oᴮ : (c : Tr k) → Ok (j ⊕ offsets S c)
  oᴮ c = Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c))

  Srᴮ : Tr⁺ j → (c : Tr k) → Tr ℓ → Stᴬ (j ⊕ offsets S c)
  Srᴮ β c x = rbs (offsets S c) (oᴮ c) (B₀ _) (BS.ψ ℓ o r B j w β x)

  subᴮ : (c : Tr k) → Tr ℓ → Tr (j ⊕ offsets S c)
  subᴮ c x = proj₁ (Ωt (j ⊕ offsets S c))

  rebᴮ′ : ∀ β c x (y : ChTᵍ ℓ c) → proj₁ (Φᴬ (Srᴮ β c x) (subᴮ c x)) ⊴ᵗ proj₁ (Φᴮ (rt β) (upᵍ x c y))
  rebᴮ′ β c x (y , e) = inj₂ (subst (λ Z → j ⊢ proj₁ (seen S j oj u (BS.ψ ℓ o r B j w β x) c) ◃ proj₁ Z)
    (sym (row-reb β x c y e))
    (+-mono _ (ι-mono j (proj₂ (BS.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))))
```

## 接上整体接口

参照一侧 (上下文, 作用, 状态对上下文的条件) 两个系统各一组, 作模块参数.

```agda
wfL : {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ) (a : L) → FI.WfL 𝔾 𝔻 a
wfL 𝔾 𝔻 zero      = FI.wf (λ ())
wfL 𝔾 𝔻 (nd s h′) = FI.wf (λ c → wfL 𝔾 𝔻 (h′ c))

module Pack {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴮ : ∀ {a} → Main.Stᴮ k h o S rc B j c′ v u eq a → Cxtᴮ → Set) where
  open FI 𝔾 𝔻
  open BL 𝔾 𝔻
  open Laws 𝔾 𝔻 using (Weak; Lim; Node; app; Cx) renaming (R to Rᵍ)
  open Aux j
  open Main k h o S rc B j c′ v u eq

  sysᴬ : Sys j
  sysᴬ = record { St = Stᴬ ; Φ = λ s x → proj₁ (Φᴬ s x) ; Ev = Evᴬ ; Cxt = Cxtᴬ ; ap = apᴬ ; Bdˢ = Bdᴬ }

  keepᴬ : Sys.KeepLaw sysᴬ
  keepᴬ = record { slot = slotᴬ ; mvc = mvcᴬ ; keep = keepᴬ′ }

  fallᴬ : Sys.FallLaw sysᴬ
  fallᴬ = record { step = stepᴬ ; fall = fallᴬ′ }

  monoᴬ : Sys.Monoˢ sysᴬ
  monoᴬ = monoᴬ′

  sysᴮ : Sys j
  sysᴮ = record { St = Stᴮ ; Φ = λ s x → proj₁ (Φᴮ s x) ; Ev = Evᴮ ; Cxt = Cxtᴮ ; ap = apᴮ ; Bdˢ = Bdᴮ }

  keepᴮ : Sys.KeepLaw sysᴮ
  keepᴮ = record { slot = slotᴮ ; mvc = mvcᴮ ; keep = keepᴮ′ }

  monoᴮ : Sys.Monoˢ sysᴮ
  monoᴮ = monoᴮ′

  rebᴮ : ∀ {a} (s : Stᴮ a) → RebAt sysᴮ sysᴬ keepᴬ s
  rebᴮ (rt β) = record
    { Lr  = λ c x → j ⊕ offsets S c
    ; Sr  = Srᴮ β
    ; sub = subᴮ
    ; reb = rebᴮ′ β
    ; lw  = λ c x → lift j (offsets S c)
    ; cp  = λ c x q → cp (offsets S c) (lf (offsets S c)) q
    ; cpE = λ c x q → evᴬ-cp (offsets S c) (lf (offsets S c)) (oᴮ c) (B₀ _) (BS.ψ ℓ o r B j w β x) q
    ; cpS = λ c x q → refl }

  embᴮ : EmbLaw sysᴮ sysᴬ keepᴬ
  embᴮ = record { row = λ s → inj₂ (rebᴮ s) }
```

`lowᴮ`: 主系统的出口 `OutR` 与辅助系统的出口 `Out` 成立, 各层的关系是生成的, 则根状态上 `YiBSFold.ψ` 的保持对 ℓ 层的一切树成立.

```agda
  lowᴮ : (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) (lm : Lim) (nod : Node)
    → OutR sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ → Sys.Out sysᴬ Le keepᴬ fallᴬ → (∀ a → Gen⁺ Le a)
    → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ app Kc t)
    → ∀ {a x} → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (BS.ψ ℓ o r B j w β x))
  lowᴮ Le wk lm nod ex exᴬ gen β K₀ bd Kc ec =
    SuffRA.sys→low sysᴮ sysᴬ keepᴬ embᴮ Le wk lm nod monoᴮ keepᴮ ex monoᴬ fallᴬ exᴬ (wfL 𝔾 𝔻) gen
      (wfL 𝔾 𝔻 ℓ) (rt β) K₀ bd (o , r , B) w β Kc (λ x → refl) ec
```

`Out.nodeE` 在副本槽位上的保留一支: 证据, 目标层的槽位与分支换型都由 `lift` 给出, 换型是恒等, 所以只剩参照一侧的三项 (上下文保持余尾 Ω, 代入交换, 目标槽位允许 κ).

```agda
  trR : (b : L) (l : Lf b) (o′ : Ok (j ⊕ b)) (q : Pos j)
    → ∀ η c → Rᵍ (at j q) η (slTᵍ j q c) → Rᵍ (at (j ⊕ b) (cp b l q)) η (slTᵍ (j ⊕ b) (cp b l q) (proj₁ (ev-cp b l o′ q) c))
  trR .zero     here                o′ q η c x = x
  trR .(nd _ _) (there {h = h′} c′′ l) o′ q η c x = trR (h′ c′′) l (proj₂ o′ c′′) q η c x

  nodeE-cp : (b : L) (l : Lf b) (o′ : Ok (j ⊕ b)) (B′ : Base (j ⊕ b)) (β : Tr⁺ j) (K : Cxtᴬ) (q : Pos j) {t κ : Ref.T 𝕋}
    → Ref.CΩ 𝕋 (apᴬ K t) κ → (∀ η → Ref.fsT 𝕋 (apᴬ K t) η ≡ apᴬ K (Ref.fsT 𝕋 t η)) → Graded.Nu 𝔾 j q κ
    → Σ (Evᴬ (rbs b o′ B′ β) (cp b l q)) λ e → Ref.CΩ 𝕋 (apᴬ K t) κ × (∀ η → Ref.fsT 𝕋 (apᴬ K t) η ≡ apᴬ K (Ref.fsT 𝕋 t η))
        × Graded.Nu 𝔾 j (slotᴬ (rbs b o′ B′ β) (cp b l q) e) κ
        × (∀ η c → Rᵍ (at j (slotᴬ (rbs b o′ B′ β) (cp b l q) e)) η (slTᵍ j (slotᴬ (rbs b o′ B′ β) (cp b l q) e) c)
             → Rᵍ (at (j ⊕ b) (cp b l q)) η (slTᵍ (j ⊕ b) (cp b l q) (mvcᴬ (rbs b o′ B′ β) (cp b l q) e c)))
  nodeE-cp b l o′ B′ β K q cΩ fs nu = evᴬ-cp b l o′ B′ β q , cΩ , fs , nu , trR b l o′ q
```

## 塔各项

`rb-tw (suc n)` 的第一分量就是 `just` 一个地板为 `tw n` 的 `Schema`, 所以塔的每一项在 `route` 落在地板之上时是 `Main` 的实例; 第 1 项上目标取 `h₁ d` (d 非零, 经孩子 d 自身) 时 `route` 就是 `inj₂`.

```agda
Sₙ : (n : ℕ) → Schema (tw n) (λ c → tw n ⊕ ↑ (tw n) c)
Sₙ n = schema (tw n) (↑ (tw n)) (Ok-tw n) self (OkO↑ (tw n) (tw n) (Ok-tw n) self) (λ c → refl)

rcₙ : (n : ℕ) (c : Tr (tw n)) → Rb (tw n ⊕ ↑ (tw n) c)
rcₙ n c = rbO (tw n) (↑ (tw n) c) (rb-tw n) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c)

rb-tw≡ : (n : ℕ) → rb-tw (suc n) ≡ (just (Sₙ n) , rcₙ n)
rb-tw≡ n = refl

route-tw1 : ∀ {d} → NZ d → route (Sₙ 0) (h₁ d) d self ≡ inj₂ (lift zero (↑ zero d))
route-tw1 (nzs _)   = refl
route-tw1 (nzl _ _) = refl

module Tower {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ) (n : ℕ)
    (B : Base (tw (suc n))) (j : L) (c′ : Tr (tw n)) (v : j ≤ tw n ⊕ ↑ (tw n) c′) (u : tw n ≤ j)
    (eq : route (Sₙ n) j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋)
    (Bdᴮ : ∀ {a} → Main.Stᴮ (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ok-tw (suc n)) (Sₙ n) (rcₙ n) B j c′ v u eq a → Cxtᴮ → Set) where
  open FI 𝔾 𝔻 using (Sys)
  open Pack 𝔾 𝔻 (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ok-tw (suc n)) (Sₙ n) (rcₙ n) B j c′ v u eq Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ public

  lowᵗ : (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Laws.Weak 𝔾 𝔻) (lm : Laws.Lim 𝔾 𝔻) (nod : Laws.Node 𝔾 𝔻)
    → BL.OutR 𝔾 𝔻 sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ → Sys.Out sysᴬ Le keepᴬ fallᴬ → (∀ a → FI.Gen⁺ 𝔾 𝔻 Le a)
    → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (Main.rt β) K₀ → (Kc : Laws.Cx 𝔾 𝔻 (tw (suc n)) j) → (∀ t → apᴮ K₀ t ≡ Laws.app 𝔾 𝔻 Kc t)
    → ∀ {a x} → Graded.R 𝔾 (tw (suc n)) a x
    → Graded.R 𝔾 j (Laws.app 𝔾 𝔻 Kc a) (proj₁ (BS.ψ (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) B j (inc c′ v) β x))
  lowᵗ = lowᴮ
```

第 1 项, 目标 `h₁ d` (d 非零, 路径 `inc d self`): `route` 的前提由 `route-tw1` 填上, 只剩参照一侧.

```agda
module Tw1 {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (B : Base (tw 1)) {d : Tr zero} (nz : NZ d)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ (h₁ d) a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋)
    (Bdᴮ : ∀ {a} → Main.Stᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B (h₁ d) d self (lift zero (↑ zero d)) (route-tw1 nz) a → Cxtᴮ → Set) =
  Tower 𝔾 𝔻 0 B (h₁ d) d self (lift zero (↑ zero d)) (route-tw1 nz) Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ
```
