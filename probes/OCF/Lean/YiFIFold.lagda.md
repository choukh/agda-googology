# 整体接口的树一侧实例: `YiDXFold.Fold K lifted`

> 判决: 编译定理与定义候选 (未经作者采纳, 不进主线); 不读记号. 主线块与 `Fold K lifted` 填进 `Block`/`Fold`/`Rows` (`foldᴷ`, `rowsᴷ`); 上折回退 (`lifted = true`) 时, Ω 形状层号上经指定孩子的路径, 表整行缺项, 对任何保留判定 K 与任何分级关系, 系统 `sysᴷ` 满足 `FallLaw` 与 `Monoˢ`, `KeepLaw` 的证据是 "K 在搬到本层的槽位上返回保留" (`keepᴷ`, `fallᴷ`, `monoᴷ`); 接上 `YiFIIface` 得 `lowᴷ`.
> 保留判定的候选 `kpˢ src`: 来源给出槽位层号到目标的字面路径 `at ℓ p ≤ j` 时, 在路径推出的目标槽位上保留 (`keepOf`; `YiDXFold.flr` 是路径取 `z≤` 的情形, `flr-keepOf`).
> 不给出什么: 出口 `Out` (参照一侧) 是 `lowᴷ` 的前提, 没有实填; 不处理表有条目的行与其余路径形状. 违反与满足的对照在 [YiFINeg](YiFINeg.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFIFold where
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; node⁺)
open import OCF.Lean.YiTBRow using (Rb)
import OCF.Lean.YiDXFold as DX
open DX using (KeepFn; alt; flr)
open import OCF.Lean.YiGIBlock using (blkᵍ; Bsᵍ; chLᵍ; ChTᵍ; chTᵍ; upᵍ; slTᵍ)
open import OCF.Lean.YiAbsFrame using (Block; Fold)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
```

## 填进 `Block`, `Fold`, `Rows`

块用 `YiGIBlock.blkᵍ` (与折叠无关). 底是 (合法证据, 比较表, 原底), 孩子的底照 `dnᵍ`. `Rows` 各项与 `rowsᵍ` 相同.
填不进的: `Fold.dn` 与 `Hand`/`HandU` 只描述 "进孩子层用孩子自己的折叠" 的行; Ω 形状层号上经指定孩子的回退行的输出是 `ψˡ` (前缀的折叠作状态), 不是孩子层的 `ψ`, 所以这一行写成 `YiFIIface.Sys` 的状态. 路径的 `ink` 在 `Block` 里没有对应字段. `Graded` 与 `Doms` 是参照一侧, 这里作模块参数.

```agda
module _ (K : KeepFn) (lifted : Bool) where
  private module F = DX.Fold K lifted

  dnᴷ : (ℓ : L) → Bsᵍ ℓ → (c : CH ℓ) → Tr ℓ → Bsᵍ (chLᵍ ℓ c)
  dnᴷ (nd s h) (o , r , b) c x =
    proj₂ o c , proj₂ r c , λ j w → F.ψ (nd s h) o r b j (inc c w) (b j (inc c w)) x

  foldᴷ : Fold blkᵍ
  foldᴷ = record
    { Bs = Bsᵍ ; LegB = λ _ _ → ⊤ ; Bt = Tr⁺ ; LegT = λ _ _ → ⊤
    ; ψ  = λ ℓ b j w β x → proj₁ (F.ψ ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w β x)
    ; ψβ = λ ℓ b j w β x → F.ψ ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w β x
    ; dn = dnᴷ }

  rowsᴷ : Rows blkᵍ foldᴷ
  rowsᴷ = record
    { sc = suc ; Sl = Pos ; slL = at ; SlT = Br ; slT = slTᵍ ; nd = Ω
    ; Ωt = λ ℓ → proj₁ (Ωt ℓ) ; Dn = Dn ; upf = λ {ℓ} {j} d β y → proj₁ (Up j d β y)
    ; sucL = λ ℓ → nd sS (λ _ → ℓ) ; ΩL = λ k h → nd (sΩ k) h ; lift = ↑ }
```

## 字面路径给出保留

`keepOf ℓ p u`: u 是槽位层号到目标 j 的字面路径. 路径把 "槽位层号自己" 这个位置推到 j 里 (`psh`); 落在 j 的真槽位上就保留, 换型是 `pshBr`; 落在 j 自己上 (u 是 `self`, 即槽位层号等于目标) 不保留, 那是对角的情形. 结果不看目标经过哪个孩子.

```agda
keep⁼ : ∀ {j X} (b : L) (f : Tr b → X) (t : Pos⁼ j) (cv : Br⁼ j t → Tr b) → cv (bz⁼ j t) ≡ zero → Keep j X (f zero)
keep⁼ b f (inj₁ _) cv e = nothing
keep⁼ b f (inj₂ q) cv e = just (q , (λ z → f (cv z)) , cong f e)

keepOf : (ℓ : L) (p : Pos ℓ) {j : L} → at ℓ p ≤ j → Keep j (Br ℓ p) (fromBr ℓ p zero)
keepOf ℓ p {j} u = keep⁼ (at ℓ p) (fromBr ℓ p) (psh u (inj₁ tt)) (pshBr u (inj₁ tt)) (pshFirst u (inj₁ tt))

Src : Set
Src = (ℓ : L) → Ok ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Maybe (at ℓ p ≤ j)

fromSrc : (ℓ : L) (p : Pos ℓ) {j : L} → Maybe (at ℓ p ≤ j) → Keep j (Br ℓ p) (fromBr ℓ p zero)
fromSrc ℓ p (just u) = keepOf ℓ p u
fromSrc ℓ p nothing  = nothing

kpˢ : Src → KeepFn
kpˢ src ℓ o p w = alt (kp ℓ o p w) (fromSrc ℓ p (src ℓ o p w))

flr-keepOf : ∀ s h {X : Set} (f : Tr zero → X) → flr zero f (nd s h) ≡ keep⁼ zero f (psh (z≤ (nd s h)) (inj₁ tt)) (pshBr (z≤ (nd s h)) (inj₁ tt)) (pshFirst (z≤ (nd s h)) (inj₁ tt))
flr-keepOf s h f = refl
```

## 行的形状

结点一行: K 返回保留时输出是目标层槽位上逐分支折叠的结点. 回退一行: 表在 (c, c′) 缺项时输出由开关选出.

```agda
node-eq : ∀ {j X x₀} (m : Keep j X x₀) q cv e (G : X → Tr⁺ j) (S : X → X)
  → m ≡ just (q , cv , e) → Ω q (λ z → proj₁ (G (cv z))) ≡ proj₁ (node⁺ m G S)
node-eq _ q cv e G S refl = refl
```

## 系统: 上折回退

固定 Ω 形状层号 ℓ = `nd (sΩ k) h`, 目标 j 在孩子 c′ 下 (路径 `inc c′ v`), 表整行缺项. 状态: 根 (`rt β`, 像是 `ψ`), 或沿下行链 d 回退之后 (`lf d X β`, 像是 `ψˡ`, X 是前缀朝各低层的折叠). 证据: K 在搬到 ℓ 的槽位上返回保留.

```agda
module Tree (K : KeepFn) {𝕋 : Ref} {𝕍 : Val}
    (𝔾 : Graded blkᵍ (foldᴷ K true) (rowsᴷ K true) 𝕋 𝕍) (𝔻 : Doms blkᵍ (foldᴷ K true))
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h))
    (j : L) (c′ : Tr k) (v : j ≤ h c′) where
  open FI 𝔾 𝔻
  open Laws 𝔾 𝔻 using (_⊴_; Weak; Lim; Node; app) renaming (R to Rᵍ)
  private
    module F = DX.Fold K true
    ℓ : L
    ℓ = nd (sΩ k) h
    w : j ≤ ℓ
    w = inc c′ v
    r : Rb ℓ
    r = (λ _ _ → nothing) , rc

  wfL : (a : L) → WfL a
  wfL zero      = wf (λ ())
  wfL (nd s h′) = wf (λ c → wfL (h′ c))

  data Stᴷ : L → Set where
    rt : Tr⁺ j → Stᴷ (nd (sΩ k) h)
    lf : ∀ {a} → Dn (nd (sΩ k) h) a → Base (nd (sΩ k) h) → Tr⁺ j → Stᴷ a

  Φ⁺ : ∀ {a} → Stᴷ a → Tr a → Tr⁺ j
  Φ⁺ (rt β)         x = F.ψ ℓ o r B j w β x
  Φ⁺ (lf {a} d X β) x = F.ψˡ ℓ o X j w β a d x

  pos : ∀ {a} → Stᴷ a → Pos a → Pos ℓ
  pos (rt β)     p = p
  pos (lf d X β) p = mv d p

  back : ∀ {a} (s : Stᴷ a) (p : Pos a) → Br ℓ (pos s p) → Br a p
  back (rt β)     p z = z
  back (lf d X β) p z = mvBr d p z

  Evᴷ : ∀ {a} → Stᴷ a → Pos a → Set
  Evᴷ s p = Σ (Pos j) λ q → Σ (Br j q → Br ℓ (pos s p)) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr ℓ (pos s p) zero) λ e
    → K ℓ o (pos s p) w ≡ just (q , cv , e)

  module _ (Cxtᴷ : Set) (apᴷ : Cxtᴷ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴷ : ∀ {a} → Stᴷ a → Cxtᴷ → Set) where
    sysᴷ : Sys j
    sysᴷ = record { St = Stᴷ ; Φ = λ s x → proj₁ (Φ⁺ s x) ; Ev = Evᴷ ; Cxt = Cxtᴷ ; ap = apᴷ ; Bdˢ = Bdᴷ }
    open Sys sysᴷ

    keepᴷ : KeepLaw
    keepᴷ = record
      { slot = λ s p e → proj₁ e
      ; mvc  = λ s p e c → back s p (proj₁ (proj₂ e) c)
      ; keep = kp′ }
      where
      kp′ : ∀ {a} (s : Stᴷ a) (p : Pos a) (e : Evᴷ s p) (g : Br a p → Tr a)
          → Ω (proj₁ e) (λ c → proj₁ (Φ⁺ s (g (back s p (proj₁ (proj₂ e) c))))) ⊴ proj₁ (Φ⁺ s (Ω p g))
      kp′ (rt β)     p (q , cv , e , eq) g = inj₁ (node-eq (K ℓ o p w) q cv e _ _ eq)
      kp′ (lf d X β) p (q , cv , e , eq) g = inj₁ (node-eq (K ℓ o (mv d p) w) q cv e _ _ eq)

    stepᴷ : ∀ {a} → Stᴷ a → (c : CH a) → Tr a → Stᴷ (chLᵍ a c)
    stepᴷ (rt β) c x = lf (down stop c) (λ i u → F.ψ ℓ o r B i u (B i u) x) (F.ψ ℓ o r B j w β x)
    stepᴷ {a = nd s h′} (lf d X β) c x =
      lf (down d c) (λ i u → F.ψˡ ℓ o X i u (X i u) (nd s h′) d x) (F.ψˡ ℓ o X j w β (nd s h′) d x)

    fallᴷ : FallLaw
    fallᴷ = record { step = stepᴷ ; fall = fl }
      where
      fl : ∀ {a} (s : Stᴷ a) (c : CH a) (x : Tr a) (y : ChTᵍ a c)
         → proj₁ (Φ⁺ (stepᴷ s c x) (chTᵍ a c y)) ⊴ proj₁ (Φ⁺ s (upᵍ x c y))
      fl (rt β) c x (y , e) = inj₁ refl
      fl {a = nd s h′} (lf d X β) c x (y , e) = inj₁ refl

    monoᴷ : Monoˢ
    monoᴷ (rt β)     d′ = F.mono ℓ o r B j w β d′
    monoᴷ (lf d X β) d′ = F.monoˡ ℓ o X j w β _ d d′
```

接上充分性: 出口 `Out` 成立, 各层的关系是生成的 (可带参照一侧的向下封闭), 则根状态上 `ψ` 的保持对 ℓ 层的一切树成立. `K₀` 是根状态的上下文, `Kc` 是它在 `Graded.Cx` 里的代表.

```agda
    lowᴷ : (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) → Weak → Lim → Node → Out Le keepᴷ fallᴷ → (∀ a → Gen⁺ Le a)
      → (β : Tr⁺ j) (K₀ : Cxtᴷ) → Bdᴷ (rt β) K₀ → (Kc : Graded.Cx 𝔾 ℓ j) → (∀ t → apᴷ K₀ t ≡ app Kc t)
      → ∀ {a x} → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (F.ψ ℓ o r B j w β x))
    lowᴷ Le wk lm nod ex gen β K₀ bd Kc ec =
      Suff.sys→low Le wk lm nod monoᴷ keepᴷ fallᴷ ex gen (wfL ℓ) (rt β) K₀ bd (o , r , B) w β Kc (λ x → refl) ec
```
