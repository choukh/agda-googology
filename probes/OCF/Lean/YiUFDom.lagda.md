# 完整候选折叠上按读回域的 LowKeep, 塔各项的 Ω 树在域里

> 判决: 编译定理, 不读记号. 候选的保留判定每一行 (含接 `keepS` 的一行) 在槽位换型下照搬关系 (`kp-good`); 域 `KD` (本层结点都在有保留证据的槽位上, 嵌入的原材料 `⊴` 孩子层号的 Ω 树) 与两个系统的结点出口树一侧实填; `lowᴰ`: 候选换基行上的 LowKeep 对域里的树成立, 前提只在参照一侧 (`OutRDT`, `OutDT`, 关系的生成规则).
> 新的一条: 塔第 n+1 项的 Ω 树对一切 n, 一切孩子 c′, 一切落在地板之上的目标在域里, 除非目标字面就是 `tw n` (`Ωt-tw`); `YiQDFold` 里只有第 1 项 (`kept-tw1`), 第 2 项起那里顶槽位不保留 (`YiCMCross.drop-tw`).
> 不给出什么: 参照一侧的出口没有实填, 没有值; 域外的树 (孩子侧槽位上的结点, 高于孩子层号 Ω 树的原材料) 不陈述. 来源: `Move`, `AddR`, `QDPack` 逐段搬自 `YiQDFold` (换成候选的折叠与证据), `GoodK`, `mapK-good`, `psh-good`, `mv-good` 原样导入.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUFDom where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; mapK; node⁺)
open import OCF.Lean.YiRBSib using (rb-ind)
open import OCF.Lean.YiBSBase using (Schema; schema; floor; offsets; ok-floor; index-floor; ok-offsets; shape; route; back; raiseO; downOk)
open import OCF.Lean.YiCMCross using (toKeep; keepS; IsJust; isJ)
open import OCF.Lean.YiGIBlock using (blkᵍ; chLᵍ; ChTᵍ; chTᵍ; upᵍ; slTᵍ; slT⁼ᵍ)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiBLFold using (_⊴ᵗ_; cW-eq)
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiQDFold using (GoodK; mapK-good; psh-good; mv-good)
open import OCF.Lean.YiUFBase
import OCF.Lean.YiUFFold as C
open C using (kp; kp⁼)
open import OCF.Lean.YiUFLaw
open import OCF.Lean.YiUFExit using (c′₂; j₂; v₂)
```

## 槽位换型下关系照搬 (候选的保留判定)

接 `keepS` 的一行: 槽位沿 `index-floor ∙ u` 推进目标, 层号与换型由 `psh-good` 给出.

```agda
toKeep-good : ∀ {j X} {x₀ : X} {A : L} {σ : X → Tr A} (r : Pos⁼ j) (cv : Br⁼ j r → X) (e : cv (bz⁼ j r) ≡ x₀)
  → (Σ (proj₁ (sl⁼ j r) ≡ A) λ eq → ∀ x → σ (cv x) ≡ subst Tr eq (slT⁼ᵍ j r x)) → GoodK A σ (toKeep r cv e)
toKeep-good (inj₁ _) cv e g = tt
toKeep-good (inj₂ q) cv e g = g

keepS-good : ∀ {k h} (S : Schema k h) (t : Pos⁼ k) {j} (u : floor S ≤ j)
  → GoodK (proj₁ (sl⁼ k t)) (slT⁼ᵍ k t) (keepS S t u)
keepS-good S t u = toKeep-good (psh (index-floor S ∙ u) t) _ _ (psh-good (index-floor S ∙ u) t)

mutual
  kp-good : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → GoodK (at ℓ p) (slTᵍ ℓ p) (kp ℓ o r p w)
  kp-good ℓ o r p self = refl , λ z → refl
  kp-good (nd s h) (_ , oc) (_ , rc) (inj₂ (c , t)) (inu vs) = kp⁼-good (h c) (oc c) (rc c) t (vs c)
  kp-good (nd (sΩ k) h) ((_ , kh) , oc) (_ , rc) (inj₂ (c , t)) (ink v) = kp⁼-good (h c) (oc c) (rc c) t (v ∙ kh c)
  kp-good (nd sS h) (_ , oc) (_ , rc) (inj₂ (c , t)) (inc _ v) = kp⁼-good (h c) (oc c) (rc c) t v
  kp-good (nd sL g) (r , oc) (_ , rc) (inj₂ (m , t)) (inc n v) =
    cW-ind (GoodK (at (nd sL g) (inj₂ (m , t))) (slTᵍ (nd sL g) (inj₂ (m , t)))) (way g r m n)
      (λ u → mapK-good (pshBr u t) (pshFirst u t) (proj₁ (psh-good u t)) (proj₂ (psh-good u t))
               (kp⁼ (g n) (oc n) (rc n) (psh u t) v) (kp⁼-good (g n) (oc n) (rc n) (psh u t) v))
      (λ u → kp⁼-good (g m) (oc m) (rc m) t (v ∙ u))
  kp-good (nd (sΩ k) h) _ _ (inj₂ _) (inc _ _) = tt
  kp-good (nd (sΩ k) h) ((ok , _) , _) ((rk , _) , _) (inj₁ t) (ink v) = kp⁼-good k ok rk t v
  kp-good (nd (sΩ k) h) ((_ , kh) , oc) ((_ , m) , rc) (inj₁ t) (inc c v) =
    rb-ind (GoodK (proj₁ (sl⁼ k t)) (slT⁼ᵍ k t)) m
      (λ S → cW-ind (GoodK (proj₁ (sl⁼ k t)) (slT⁼ᵍ k t)) (route S _ c v)
        (λ _ → mapK-good (pshBr (kh c) t) (pshFirst (kh c) t) (proj₁ (psh-good (kh c) t)) (proj₂ (psh-good (kh c) t))
                 (kp⁼ (h c) (oc c) (rc c) (psh (kh c) t) v) (kp⁼-good (h c) (oc c) (rc c) (psh (kh c) t) v))
        (λ u → keepS-good S t u))
      (mapK-good (pshBr (kh c) t) (pshFirst (kh c) t) (proj₁ (psh-good (kh c) t)) (proj₂ (psh-good (kh c) t))
        (kp⁼ (h c) (oc c) (rc c) (psh (kh c) t) v) (kp⁼-good (h c) (oc c) (rc c) (psh (kh c) t) v))
  kp-good (nd (sΩ k) h) ((_ , kh) , oc) (_ , rc) (inj₁ t) (inu vs) =
    mapK-good (pshBr (kh zero) t) (pshFirst (kh zero) t) (proj₁ (psh-good (kh zero) t)) (proj₂ (psh-good (kh zero) t))
      (kp⁼ (h zero) (oc zero) (rc zero) (psh (kh zero) t) (vs zero)) (kp⁼-good (h zero) (oc zero) (rc zero) (psh (kh zero) t) (vs zero))

  kp⁼-good : (a : L) (o : Ok a) (r : Rb a) (t : Pos⁼ a) {j : L} (w : j ≤ a) → GoodK (proj₁ (sl⁼ a t)) (slT⁼ᵍ a t) (kp⁼ a o r t w)
  kp⁼-good a o r (inj₁ _) w = tt
  kp⁼-good a o r (inj₂ p) w = kp-good a o r p w
```

## 关系的搬运, 左加封闭, 链支配 (同 `YiQDFold`, 换成候选的折叠)

```agda
module Move (d : ℕ) {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ (foldᶜ (suc d)) (rowsᶜ (suc d)) 𝕋 𝕍) where
  open Graded 𝔾 using () renaming (R to Rᵍ)

  trSl : ∀ {A B : L} (e : A ≡ B) {η : Ref.T 𝕋} {x : Tr A} → Rᵍ A η x → Rᵍ B η (subst Tr e x)
  trSl refl r = r

  byGood : ∀ {j a} {p : Pos a} (q : Pos j) (cv : Br j q → Br a p)
    → (Σ (at j q ≡ at a p) λ e → ∀ z → slTᵍ a p (cv z) ≡ subst Tr e (slTᵍ j q z))
    → ∀ η c → Rᵍ (at j q) η (slTᵍ j q c) → Rᵍ (at a p) η (slTᵍ a p (cv c))
  byGood {a = a} {p} q cv (e , cm) η c r = subst (Rᵍ (at a p) η) (sym (cm c)) (trSl e r)
```

```agda
module AddR (d : ℕ) {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ (foldᶜ (suc d)) (rowsᶜ (suc d)) 𝕋 𝕍) (𝔻 : Doms blkᵍ (foldᶜ (suc d))) (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set)
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

参数同 `YiUFLaw.Pack`.

```agda
module QDPack (d : ℕ) {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ (foldᶜ (suc d)) (rowsᶜ (suc d)) 𝕋 𝕍) (𝔻 : Doms blkᵍ (foldᶜ (suc d)))
    (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (rk : Rb k) (S : Schema k h) (rc : (c : Tr k) → Rb (h c))
    (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (u : floor S ≤ j) (eq : route S j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ d j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴮ : ∀ {a} → Main.Stᴮ d k h o rk S rc B j c′ v u eq a → Cxtᴮ → Set) where
  open FI 𝔾 𝔻 using (Gen⁺)
  open QD 𝔾 𝔻
  open Laws 𝔾 𝔻 using (Weak; Lim; Node; Zero; Succ; Emb; app; Cx) renaming (R to Rᵍ)
  open Aux d j
  open Main d k h o rk S rc B j c′ v u eq
  open Pack d 𝔾 𝔻 k h o rk S rc B j c′ v u eq Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ public
  open Move d 𝔾

  Kept : Pos ℓ → Set
  Kept p = Σ (Pos j) λ q → Σ (Br j q → Br ℓ p) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr ℓ p zero) λ e
    → kp ℓ o r p w ≡ just (q , cv , e)

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
  mvRᴮ (rt β) p (q , cv , e , eqk) = byGood q cv (subst (GoodK (at ℓ p) (slTᵍ ℓ p)) eqk (kp-good ℓ o r p w))

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
  mvRᴬ (rbs b o′ r′ B′ β) p (q , cv , e , eqk) =
    byGood q cv (subst (GoodK (at (j ⊕ b) p) (slTᵍ (j ⊕ b) p)) eqk (kp-good (j ⊕ b) o′ r′ p (lift j b)))
  mvRᴬ (us d β) p e = byGood (mv d p) (mvBr d p) (mv-good d p)
```

辅助系统: 换基层号上的状态按 `kp` 的字面结果二选一 (保留, 或折叠自己的链 `iter S x₀`); 上折状态处处保留.

```agda
  module WithRules (Le : Ref.T 𝕋 → Ref.T 𝕋 → Set) (wk : Weak) (lm : Lim) (nod : Node) (zr : Zero) (sr : Succ) (em : Emb)
      (leR : ∀ {s t o} → Le s t → Rᵍ j t o → Rᵍ j s o) (gen : ∀ a → Gen⁺ Le a) where
    open AddR d 𝔾 𝔻 Le zr sr lm nod em wk j leR (gen j)

    pickᴬ : ∀ {a} (s : Stᴬ a) (p : Pos a) (g : Br a p → Tr a) → Dᴬ s (Ω p g) → Evᴬ s p ⊎ Chain sysᴬ s p g
    pickᴬ (rbs b o′ r′ B′ β) p g _ = node-pick (kp (j ⊕ b) o′ r′ p (lift j b))
      (λ z → C.ψ d (j ⊕ b) o′ r′ B′ j (lift j b) β (g z))
      (λ z → fromBr (j ⊕ b) p (proj₁ (C.ψ d (j ⊕ b) o′ r′ B′ (at (j ⊕ b) p) (posW (j ⊕ b) p)
               (B′ (at (j ⊕ b) p) (posW (j ⊕ b) p)) (g z))))
    pickᴬ (us d β) p g _ = inj₁ tt

    ntᴬ : NodeTree sysᴬ keepᴬ Dᴬ
    ntᴬ = record { pick = pickᴬ ; mvR = mvRᴬ }
```

`lowᴰ`: 参照一侧两组出口 (`OutRDT`, `OutDT`, 结点一条只剩 `NodeRef`) 成立, 则根状态上候选 `ψ (suc d)` 的保持对域里的一切树成立.

```agda
    lowᴰ : OutRDT sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ Dᴮ ntᴮ → OutDT sysᴬ Le keepᴬ fallᴬ Dᴬ ntᴬ
      → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ app Kc t)
      → ∀ {a x} → KD x → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (C.ψ (suc d) ℓ o r B j w β x))
    lowᴰ exᴮ exᴬ β K₀ bd Kc ec =
      SuffRAD.sys→lowᴰ sysᴮ sysᴬ keepᴬ embᴮ Le wk lm nod monoᴮ keepᴮ domᴮ domᴬ rowDᴮ
        (outRDT→outRD sysᴮ sysᴬ keepᴬ embᴮ exᴮ) monoᴬ fallᴬ (λ _ _ _ _ _ → tt) (outDT→outD sysᴬ exᴬ)
        (wfL 𝔾 𝔻) gen (wfL 𝔾 𝔻 ℓ) (rt β) K₀ bd (o , r , B) w β Kc (λ x → refl) ec
```

## 塔各项的 Ω 树在域里

塔第 n+1 项, 目标 j 经任一孩子 c′, `route` 给地板之上 (`eq`): 顶槽位保留, 除非目标字面就是 `tw n` (那时是同层, 按规则走对角). 所以 `lowᴰ` 对 `Ωt (tw (suc n))` 可用, 对一切 n.

```agda
top-w : ∀ {k j} (w : k ≤ j)
  → (Σ (Pos j) λ q → Σ (Br j q → Tr k) λ cv → Σ (cv (fromBr j q zero) ≡ zero) λ e′
       → toKeep (psh w (inj₁ tt)) (pshBr w (inj₁ tt)) (pshFirst w (inj₁ tt)) ≡ just (q , cv , e′))
    ⊎ (k ≡ j)
top-w self                  = inj₂ refl
top-w (inc c v)             = inj₁ (_ , _ , _ , refl)
top-w {j = nd s h} (inu vs) = inj₁ (_ , _ , _ , refl)
top-w (ink v)               = inj₁ (_ , _ , _ , refl)

module QDTw (d n : ℕ) {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ (foldᶜ (suc d)) (rowsᶜ (suc d)) 𝕋 𝕍) (𝔻 : Doms blkᵍ (foldᶜ (suc d)))
    (B : Base (tw (suc n))) (j : L) (c′ : Tr (tw n)) (v : j ≤ tw n ⊕ ↑ (tw n) c′) (u : tw n ≤ j)
    (eq : route (Sₙ n) j c′ v ≡ inj₂ u)
    (Cxtᴬ : Set) (apᴬ : Cxtᴬ → Ref.T 𝕋 → Ref.T 𝕋) (Bdᴬ : ∀ {a} → Aux.Stᴬ d j a → Cxtᴬ → Set)
    (Cxtᴮ : Set) (apᴮ : Cxtᴮ → Ref.T 𝕋 → Ref.T 𝕋)
    (Bdᴮ : ∀ {a} → Main.Stᴮ d (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ok-tw (suc n)) (rb-tw n) (Sₙ n) (rcₙ n) B j c′ v u eq a → Cxtᴮ → Set) where
  open QDPack d 𝔾 𝔻 (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ok-tw (suc n)) (rb-tw n) (Sₙ n) (rcₙ n) B j c′ v u eq
    Cxtᴬ apᴬ Bdᴬ Cxtᴮ apᴮ Bdᴮ public

  kept-top : Kept (inj₁ (inj₁ tt)) ⊎ (tw n ≡ j)
  kept-top with top-w (self ∙ u)
  ... | inj₁ (q , cv , e′ , eqk) = inj₁ (q , cv , e′ , trans (cW-eq (route (Sₙ n) j c′ v) eq) eqk)
  ... | inj₂ e = inj₂ e

  Ωt-tw : KD (proj₁ (Ωt (tw (suc n)))) ⊎ (tw n ≡ j)
  Ωt-tw with kept-top
  ... | inj₁ e = inj₁ (Ωt-in e)
  ... | inj₂ e = inj₂ e
```

前提可满足: 塔第 2 项, 审查 E 路 `drop₂` 的那个目标 (`YiUFExit.j₂`), `route` 给地板之上.

```agda
route₂ : route (Sₙ 1) j₂ c′₂ v₂ ≡ inj₂ (lift (tw 1) (nd sS (λ _ → zero)))
route₂ = refl
```
