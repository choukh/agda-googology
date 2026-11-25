# 换基折叠上按读回域的 LowKeep: 树一侧的出口全部实填

> 判决: 编译定理, 不读记号. 主系统的域 `KD`: 本层结点都在有保留证据的槽位上 (`kp` 的字面结果), 嵌入的原材料 `⊴` 孩子层号的 Ω 树; 对放宽, 后继, 分支, 嵌入左项封闭; Ω 树在域里当且仅当顶槽位保留 (`Ωt-in`, `Ωt-out`), 塔第 1 项上保留 (`kept-tw1`). 辅助系统的域取全体. 替身支配原材料归到两棵 Ω 树之间 (`SubDom`, `embEᴮ`).
> 结点出口的树一侧两个系统都实填 (`ntᴮ`, `ntᴬ`): 槽位换型下关系照搬 (`kp-good`, `mv-good`), 辅助系统无证据的结点走折叠自己的链, 支配由 "关系对左加封闭" 给出 (`add`, `chain-dom`, 只用六条规则, 向下封闭与生成). 于是 `lowᴰ`: 换基行上的 LowKeep 对域里的树成立, 前提只剩参照一侧的 `OutRDT` (嵌入一条可由 `Hand₁`, `SubDom` 给出), `OutDT` 与关系的生成规则; `low-tw1` 是塔第 1 项 Ω 树上的实例.
> 不给出什么: 参照一侧的出口没有实填; 不处理 `route` 落在地板之下的行; 域外的树 (主系统孩子槽位上的结点, 高于孩子层号 Ω 树的原材料) 不陈述.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQDFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; mapK; kp; kp⁼; node⁺)
import OCF.Lean.YiRBSib as R
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiGIBlock using (blkᵍ; chLᵍ; ChTᵍ; chTᵍ; upᵍ; slTᵍ; slT⁼ᵍ)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiBLFold
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiVALeaf using (NZ; nzs; nzl)
open import OCF.Lean.YiTBRow using (h₁)
```

## 槽位换型下关系照搬

`GoodK`: 保留时目标槽位的层号就是原槽位的层号, 换型与 `slTᵍ` 交换. `kp` 的每一行都满足 (`kp-good`, 逐行照 `kp` 的分情形); 上折的槽位搬运同样 (`mv-good`).

```agda
GoodK : ∀ {j X x₀} (A : L) → (X → Tr A) → Keep j X x₀ → Set
GoodK {j} A σ (just (q , cv , _)) = Σ (at j q ≡ A) λ e → ∀ z → σ (cv z) ≡ subst Tr e (slTᵍ j q z)
GoodK A σ nothing = ⊤

mapK-good : ∀ {j X Y x₀ y₀} {A B : L} {σ : X → Tr A} {σ′ : Y → Tr B} (f : X → Y) (e : f x₀ ≡ y₀) (eAB : A ≡ B)
  → (∀ x → σ′ (f x) ≡ subst Tr eAB (σ x)) → (m : Keep j X x₀) → GoodK A σ m → GoodK B σ′ (mapK f e m)
mapK-good f e eAB hf (just (q , cv , _)) (eq , cm) =
  trans eq eAB , λ z → trans (hf (cv z)) (trans (cong (subst Tr eAB) (cm z)) (subst-subst eq))
mapK-good f e eAB hf nothing _ = tt

psh-good : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k)
  → Σ (proj₁ (sl⁼ a (psh v t)) ≡ proj₁ (sl⁼ k t)) λ e → ∀ x → slT⁼ᵍ k t (pshBr v t x) ≡ subst Tr e (slT⁼ᵍ a (psh v t) x)
psh-good self t = refl , λ x → refl
psh-good (inc c v) t = psh-good v t
psh-good {a = nd s h} (inu vs) t = psh-good (vs (c₀ s)) t
psh-good (ink v) t = psh-good v t

mutual
  kp-good : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → GoodK (at ℓ p) (slTᵍ ℓ p) (kp ℓ o p w)
  kp-good ℓ o p self = refl , λ z → refl
  kp-good (nd s h) (_ , oc) (inj₂ (c , t)) (inu vs) = kp⁼-good (h c) (oc c) t (vs c)
  kp-good (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v) = kp⁼-good (h c) (oc c) t (v ∙ kh c)
  kp-good (nd sS h) (_ , oc) (inj₂ (c , t)) (inc _ v) = kp⁼-good (h c) (oc c) t v
  kp-good (nd sL g) (r , oc) (inj₂ (m , t)) (inc n v) =
    cW-ind (GoodK (at (nd sL g) (inj₂ (m , t))) (slTᵍ (nd sL g) (inj₂ (m , t)))) (way g r m n)
      (λ u → mapK-good (pshBr u t) (pshFirst u t) (proj₁ (psh-good u t)) (proj₂ (psh-good u t))
               (kp⁼ (g n) (oc n) (psh u t) v) (kp⁼-good (g n) (oc n) (psh u t) v))
      (λ u → kp⁼-good (g m) (oc m) t (v ∙ u))
  kp-good (nd (sΩ k) h) _ (inj₂ _) (inc _ _) = tt
  kp-good (nd (sΩ k) h) ((ok , _) , _) (inj₁ t) (ink v) = kp⁼-good k ok t v
  kp-good (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t) (inc c v) =
    mapK-good (pshBr (kh c) t) (pshFirst (kh c) t) (proj₁ (psh-good (kh c) t)) (proj₂ (psh-good (kh c) t))
      (kp⁼ (h c) (oc c) (psh (kh c) t) v) (kp⁼-good (h c) (oc c) (psh (kh c) t) v)
  kp-good (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t) (inu vs) =
    mapK-good (pshBr (kh zero) t) (pshFirst (kh zero) t) (proj₁ (psh-good (kh zero) t)) (proj₂ (psh-good (kh zero) t))
      (kp⁼ (h zero) (oc zero) (psh (kh zero) t) (vs zero)) (kp⁼-good (h zero) (oc zero) (psh (kh zero) t) (vs zero))

  kp⁼-good : (a : L) (o : Ok a) (t : Pos⁼ a) {j : L} (w : j ≤ a) → GoodK (proj₁ (sl⁼ a t)) (slT⁼ᵍ a t) (kp⁼ a o t w)
  kp⁼-good a o (inj₁ _) w = tt
  kp⁼-good a o (inj₂ p) w = kp-good a o p w

mv-good : ∀ {ℓ a} (d : Dn ℓ a) (p : Pos a)
  → Σ (at ℓ (mv d p) ≡ at a p) λ e → ∀ z → slTᵍ a p (mvBr d p z) ≡ subst Tr e (slTᵍ ℓ (mv d p) z)
mv-good stop       p = refl , λ z → refl
mv-good (down d c) p = mv-good d (inj₂ (c , inj₂ p))
```

对任何关系: 层号相等, 树沿换型相等, 关系就照搬.

```agda
module Move {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) where
  open Graded 𝔾 using () renaming (R to Rᵍ)

  trSl : ∀ {A B : L} (e : A ≡ B) {η : Ref.T 𝕋} {x : Tr A} → Rᵍ A η x → Rᵍ B η (subst Tr e x)
  trSl refl r = r

  byGood : ∀ {j a} {p : Pos a} (q : Pos j) (cv : Br j q → Br a p)
    → (Σ (at j q ≡ at a p) λ e → ∀ z → slTᵍ a p (cv z) ≡ subst Tr e (slTᵍ j q z))
    → ∀ η c → Rᵍ (at j q) η (slTᵍ j q c) → Rᵍ (at a p) η (slTᵍ a p (cv c))
  byGood {a = a} {p} q cv (e , cm) η c r = subst (Rᵍ (at a p) η) (sym (cm c)) (trSl e r)
```

## 关系对左加封闭, 部分和极限的链支配

第 j 层的关系由六条规则与沿 Le 向下封闭生成, 且对这些规则封闭: 则 `R τ y` 推出 `R τ (A + y)`. 无证据的结点折成链的部分和极限, 第 k 个链点的像满足的关系, 第 k 个部分和满足, 极限也满足.

```agda
module AddR {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ) (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set)
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

  node-pick : ∀ {X x₀} (m : Keep j X x₀) (G′ : X → Tr⁺ j) (S′ : X → X)
    → (Σ (Pos j) λ q → Σ (Br j q → X) λ cv → Σ (cv (fromBr j q zero) ≡ x₀) λ e → m ≡ just (q , cv , e))
      ⊎ (Σ (ℕ → X) λ z → ∀ k {τ} → Rᵍ j τ (proj₁ (G′ (z k))) → Rᵍ j τ (proj₁ (node⁺ m G′ S′)))
  node-pick (just (q , cv , e)) G′ S′ = inj₁ (q , cv , e , refl)
  node-pick {x₀ = x₀} nothing G′ S′ = inj₂ ((λ k → iter S′ x₀ k) , chain-dom G′ S′)
```

## 两个系统的域与树一侧的结点出口

参数同 `YiBLFold.Pack`. 主系统的域看本层结点的槽位是否保留, 嵌入的孩子树只要求不高于孩子层号的 Ω 树 (换基行不递归进孩子树).

```agda
module QDPack {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴮ : ∀ {a} → Main.Stᴮ k h o S rc B j c′ v u eq a → Cxtᴮ → Set) where
  open FI 𝔾 𝔻 using (Gen⁺)
  open QD 𝔾 𝔻
  open Laws 𝔾 𝔻 using (Weak; Lim; Node; Zero; Succ; Emb; app; Cx) renaming (R to Rᵍ)
  open Aux j
  open Main k h o S rc B j c′ v u eq
  open Pack 𝔾 𝔻 k h o S rc B j c′ v u eq Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ public
  open Move 𝔾

  Kept : Pos ℓ → Set
  Kept p = Σ (Pos j) λ q → Σ (Br j q → Br ℓ p) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr ℓ p zero) λ e
    → kp ℓ o p w ≡ just (q , cv , e)

  KD : Tr ℓ → Set
  KD zero         = ⊤
  KD (suc x)      = KD x
  KD (lim f _)    = ∀ n → KD (f n)
  KD (Ω p g)      = Kept p × (∀ z → KD (g z))
  KD (up x c y _) = KD x × (y ⊴ᵗ proj₁ (Ωt (h c)))

  kd-dw : ∀ {x x′ : Tr ℓ} → ℓ ⊢ x ◃ x′ → KD x′ → KD x
  kd-dw ◃s           d       = d
  kd-dw (◃l n)       d       = d n
  kd-dw ◃w           (_ , d) = d _
  kd-dw (◃u x c y e) d       = proj₁ d
  kd-dw (◃c x c r)   (d , inj₁ refl) = d , inj₂ r
  kd-dw (◃c x c r)   (d , inj₂ r′)   = d , inj₂ (◃t r r′)
  kd-dw (◃t d₁ d₂)   d       = kd-dw d₁ (kd-dw d₂ d)

  Dᴮ : ∀ {a} → Stᴮ a → Tr a → Set
  Dᴮ (rt β) x = KD x

  dwᴮ : ∀ {a} (s : Stᴮ a) {x x′ : Tr a} → a ⊢ x ◃ x′ → Dᴮ s x′ → Dᴮ s x
  dwᴮ (rt β) d k′ = kd-dw d k′

  dscᴮ : ∀ {a} (s : Stᴮ a) {x : Tr a} → Dᴮ s (suc x) → Dᴮ s x
  dscᴮ (rt β) k′ = k′

  dndᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) (g : Br a p → Tr a) → Dᴮ s (Ω p g) → ∀ c → Dᴮ s (g c)
  dndᴮ (rt β) p g (_ , k′) c = k′ c

  dupᴮ : ∀ {a} (s : Stᴮ a) (x : Tr a) (c : CH a) (y : ChTᵍ a c) → Dᴮ s (upᵍ x c y) → Dᴮ s x
  dupᴮ (rt β) x c y k′ = proj₁ k′

  domᴮ : Dom sysᴮ
  domᴮ = record { D = Dᴮ ; dw = dwᴮ ; dsc = dscᴮ ; dnd = dndᴮ ; dup = dupᴮ }

  Ωt-in : Kept (inj₁ (inj₁ tt)) → KD (proj₁ (Ωt ℓ))
  Ωt-in e = e , λ _ → tt , inj₁ refl

  Ωt-out : KD (proj₁ (Ωt ℓ)) → Kept (inj₁ (inj₁ tt))
  Ωt-out = proj₁

  pickᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) (g : Br a p → Tr a) → Dᴮ s (Ω p g) → Evᴮ s p ⊎ Chain sysᴮ s p g
  pickᴮ (rt β) p g (e , _) = inj₁ e

  mvRᴮ : ∀ {a} (s : Stᴮ a) (p : Pos a) (e : Evᴮ s p) → ∀ η c
    → Rᵍ (at j (slotᴮ s p e)) η (slTᵍ j (slotᴮ s p e) c) → Rᵍ (at a p) η (slTᵍ a p (mvcᴮ s p e c))
  mvRᴮ (rt β) p (q , cv , e , eqk) = byGood q cv (subst (GoodK (at ℓ p) (slTᵍ ℓ p)) eqk (kp-good ℓ o p w))

  ntᴮ : NodeTree sysᴮ keepᴮ Dᴮ
  ntᴮ = record { pick = pickᴮ ; mvR = mvRᴮ }
```

换基行的嵌入出口: 域里的原材料不高于孩子层号的 Ω 树, 所以 "替身支配原材料" 归到两棵 Ω 树之间 (`SubDom`: 孩子层号 `h c` 与换基层号 `j ⊕ offsets S c` 的 Ω 树, 地板 ≤ j, 偏移相同); Le 自反时, 它由 "Ω 树上的关系沿层号抬高保持" 给出 (`raise→SubDom`).

```agda
  module SubstDom (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) where
    SubDom : Set
    SubDom = ∀ (c : Tr k) {t u : Ref.T 𝕋} {x : Tr ℓ} → Rᵍ ℓ t x → Rᵍ (h c) u (proj₁ (Ωt (h c)))
      → Σ (Ref.T 𝕋) λ u″ → Rᵍ (j ⊕ offsets S c) u″ (proj₁ (Ωt (j ⊕ offsets S c))) × Le (Ref._⊕_ 𝕋 t u) (Ref._⊕_ 𝕋 t u″)

    Hand₁ : Set
    Hand₁ = ∀ (β : Tr⁺ j) (K : Cxtᴮ) → Bdᴮ (rt β) K → (c : Tr k) → ∀ {t x} → Rᵍ ℓ t x → Rᵍ j (apᴮ K t) (proj₁ (Φᴮ (rt β) x))
      → Σ Cxtᴬ λ K″ → Bdᴬ (Srᴮ β c x) K″ × (∀ u → apᴬ K″ u ≡ apᴮ K (Ref._⊕_ 𝕋 t u))

    embEᴮ : Hand₁ → SubDom → ∀ {a} (s : Stᴮ a) K → Bdᴮ s K → EmbOutD sysᴮ sysᴬ keepᴬ embᴮ Le Dᴮ s K (inj₂ (rebᴮ s))
    embEᴮ e₁ sd (rt β) K bd = e₁ β K bd , λ c y d r ry → sd c r (Row.wk⊴ 𝔾 𝔻 wk ry (proj₂ d))

    raise→SubDom : (∀ {t} → Le t t)
      → (∀ (c : Tr k) {u} → Rᵍ (h c) u (proj₁ (Ωt (h c))) → Rᵍ (j ⊕ offsets S c) u (proj₁ (Ωt (j ⊕ offsets S c)))) → SubDom
    raise→SubDom rf rs c {u = u} _ r = u , rs c r , rf

  rowDᴮ : ∀ {a} (s : Stᴮ a) → RowD sysᴮ sysᴬ keepᴬ embᴮ Dᴮ (λ _ _ → ⊤) s (inj₂ (rebᴮ s))
  rowDᴮ (rt β) c x = tt

  Dᴬ : ∀ {a} → Stᴬ a → Tr a → Set
  Dᴬ _ _ = ⊤

  domᴬ : Dom sysᴬ
  domᴬ = record { D = Dᴬ ; dw = λ _ _ _ → tt ; dsc = λ _ _ → tt ; dnd = λ _ _ _ _ _ → tt ; dup = λ _ _ _ _ _ → tt }

  mvRᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) (e : Evᴬ s p) → ∀ η c
    → Rᵍ (at j (slotᴬ s p e)) η (slTᵍ j (slotᴬ s p e) c) → Rᵍ (at a p) η (slTᵍ a p (mvcᴬ s p e c))
  mvRᴬ (rbs b o′ B′ β) p (q , cv , e , eqk) =
    byGood q cv (subst (GoodK (at (j ⊕ b) p) (slTᵍ (j ⊕ b) p)) eqk (kp-good (j ⊕ b) o′ p (lift j b)))
  mvRᴬ (us d β) p e = byGood (mv d p) (mvBr d p) (mv-good d p)
```

辅助系统: 换基层号上的状态按 `kp` 的字面结果二选一 (保留, 或折叠自己的链 `iter S x₀`); 上折状态处处保留.

```agda
  module WithRules (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) (lm : Lim) (nod : Node) (zr : Zero) (sr : Succ) (em : Emb)
      (leR : ∀ {s t o} → Le s t → Rᵍ j t o → Rᵍ j s o) (gen : ∀ a → Gen⁺ Le a) where
    open AddR 𝔾 𝔻 Le zr sr lm nod em wk j leR (gen j)

    pickᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) (g : Br a p → Tr a) → Dᴬ s (Ω p g) → Evᴬ s p ⊎ Chain sysᴬ s p g
    pickᴬ (rbs b o′ B′ β) p g _ = node-pick (kp (j ⊕ b) o′ p (lift j b))
      (λ z → R.ψ (j ⊕ b) o′ (R.rb-no (j ⊕ b)) B′ j (lift j b) β (g z))
      (λ z → fromBr (j ⊕ b) p (proj₁ (R.ψ (j ⊕ b) o′ (R.rb-no (j ⊕ b)) B′ (at (j ⊕ b) p) (posW (j ⊕ b) p)
               (B′ (at (j ⊕ b) p) (posW (j ⊕ b) p)) (g z))))
    pickᴬ (us d β) p g _ = inj₁ tt

    ntᴬ : NodeTree sysᴬ keepᴬ Dᴬ
    ntᴬ = record { pick = pickᴬ ; mvR = mvRᴬ }
```

`lowᴰ`: 参照一侧两组出口 (`OutRDT`, `OutDT`, 结点一条只剩 `NodeRef`) 成立, 则根状态上 `YiBSFold.ψ` 的保持对域里的一切树成立.

```agda
    lowᴰ : OutRDT sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ Dᴮ ntᴮ → OutDT sysᴬ Le keepᴬ fallᴬ Dᴬ ntᴬ
      → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ app Kc t)
      → ∀ {a x} → KD x → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (BS.ψ ℓ o r B j w β x))
    lowᴰ exᴮ exᴬ β K₀ bd Kc ec =
      SuffRAD.sys→lowᴰ sysᴮ sysᴬ keepᴬ embᴮ Le wk lm nod monoᴮ keepᴮ domᴮ domᴬ rowDᴮ
        (outRDT→outRD sysᴮ sysᴬ keepᴬ embᴮ exᴮ) monoᴬ fallᴬ (λ _ _ _ _ _ → tt) (outDT→outD sysᴬ exᴬ)
        (wfL 𝔾 𝔻) gen (wfL 𝔾 𝔻 ℓ) (rt β) K₀ bd (o , r , B) w β Kc (λ x → refl) ec
```

## 塔第 1 项

目标 `h₁ d` (d 非零, 路径 `inc d self`): 顶槽位经 `lift` 推进孩子层号, 落在 `self` 路径上, 保留; 所以 Ω 树在域里.

```agda
kept-tw1 : ∀ {d} → NZ d → Σ (Pos (h₁ d)) λ q → Σ (Br (h₁ d) q → Br (tw 1) (inj₁ (inj₁ tt))) λ cv
  → Σ (cv (fromBr (h₁ d) q zero) ≡ fromBr (tw 1) (inj₁ (inj₁ tt)) zero) λ e
  → kp (tw 1) (Ok-tw 1) (inj₁ (inj₁ tt)) (inc d self) ≡ just (q , cv , e)
kept-tw1 (nzs _)   = _ , _ , _ , refl
kept-tw1 (nzl _ _) = _ , _ , _ , refl

module QDTw1 {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᴮ rowsᴮ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᴮ)
    (B : Base (tw 1)) {d : Tr zero} (nz : NZ d)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ (h₁ d) a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋)
    (Bdᴮ : ∀ {a} → Main.Stᴮ zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B (h₁ d) d self (lift zero (↑ zero d)) (route-tw1 nz) a → Cxtᴮ → Set) where
  open QDPack 𝔾 𝔻 zero h₁ (Ok-tw 1) (Sₙ 0) (rcₙ 0) B (h₁ d) d self (lift zero (↑ zero d)) (route-tw1 nz)
    Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ public
  open QD 𝔾 𝔻 using (OutRDT; OutDT)

  Ωt-tw1 : KD (proj₁ (Ωt (tw 1)))
  Ωt-tw1 = Ωt-in (kept-tw1 nz)

  module _ (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Laws.Weak 𝔾 𝔻) (lm : Laws.Lim 𝔾 𝔻) (nod : Laws.Node 𝔾 𝔻)
      (zr : Laws.Zero 𝔾 𝔻) (sr : Laws.Succ 𝔾 𝔻) (em : Laws.Emb 𝔾 𝔻)
      (leR : ∀ {s t o} → Le s t → Graded.R 𝔾 (h₁ d) t o → Graded.R 𝔾 (h₁ d) s o) (gen : ∀ a → FI.Gen⁺ 𝔾 𝔻 Le a) where
    open WithRules Le wk lm nod zr sr em leR gen

    low-tw1 : OutRDT sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ Dᴮ ntᴮ → OutDT sysᴬ Le keepᴬ fallᴬ Dᴬ ntᴬ
      → (β : Tr⁺ (h₁ d)) (K₀ : Cxtᴮ) → Bdᴮ (Main.rt β) K₀ → (Kc : Laws.Cx 𝔾 𝔻 (tw 1) (h₁ d))
      → (∀ t → apᴮ K₀ t ≡ Laws.app 𝔾 𝔻 Kc t)
      → ∀ {a} → Graded.R 𝔾 (tw 1) a (proj₁ (Ωt (tw 1)))
      → Graded.R 𝔾 (h₁ d) (Laws.app 𝔾 𝔻 Kc a) (proj₁ (BS.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B (h₁ d) (inc d self) β (proj₁ (Ωt (tw 1)))))
    low-tw1 exᴮ exᴬ β K₀ bd Kc ec = lowᴰ exᴮ exᴬ β K₀ bd Kc ec Ωt-tw1
```
