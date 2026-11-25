# 层号上的保持接口, 与后继层号的一步

> 验收文件 (读记号), 不进成品; 树、折叠、合法性不改. 判决: 编译定理, 无前提 (一步定理 `Step₊.W₊` 的前提是六条记号一侧的比较与共尾式). 接口 `Laws` 把一个层号 j 上要的保持写成一条记录: 折到自身 (`selfP`), 上折进任意高层 (`upP`), 朝每个登记的目标下折 (`df`), 每个槽位在每个目标处是保留还是走链 (`kc`).
> 一步: j 满足接口, 则 `nd sS (λ _ → j)` 满足接口, 目标多出 j 自身 (指定孩子路径与一致路径各一个). 证明里新用到的字段: `selfP₊` 用 `upP`, `df₊` 的嵌入行用 `selfP` 与 `df`, 链行用 `leafᵗ`.
> 不给出什么: ℕ 极限层号的一步没有做; 接口的实例与塔见 [YiZSTower](YiZSTower.lagda.md).
> 来源: `LF`, `chain`, `gbS` 各行照 `YiBSFam.LF` 与 `YiSVStep.Step.Fold₊.LFw` (有限层号 `fn n` 换成带接口的 j, `kcaseT` 换成字段 `kc`); `selfP₊` 照 `YiHCOmega.Tω.Self.PFω`; `upP₊` 照 `YiHCOmega.UpT.PuTˢ`; `leaf₊` 即 `YiSVStep.Step.Mβ₊`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZSLev where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; node⁺)
open import OCF.Lean.YiRBSib using (Rb; ψ; mono)
import OCF.Lean.YiKVRel as K
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc; module Gen)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; γT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (Pen; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiHCOmega using (ψᵘ; appᵘ)
open import OCF.Lean.YiSVMono using (ψ-⊵)
open import OCF.Lean.YiSVStep using (to)

⊴t : ∀ {ℓ} {a b c : Tr ℓ} → a K.⊴ b → b K.⊴ c → a K.⊴ c
⊴t p K.⊴r     = p
⊴t p (K.⊴◃ e) = K.⊴◃ (K.⊴-◃ p e)
```

## 数据与律

`Tg b`: 登记的目标 (j 之下, 不含 j 自身); b = `true` 是指定孩子的路径 (链经过的那些), `false` 是一致路径. `Hi μ`: j 的每个槽位的读法都低于 μ; `Lo μ`: 每个目标的读法都不高于 μ.

```agda
record Data (j : L) : Set₁ where
  field
    Low  : (p : Pos j) → E.T → Br j p → Set
    Chd  : (c : CH j) → E.T → ChT j c → Set
    Nu   : Pos j → E.T → Set
    Tg   : Bool → Set
    lv   : ∀ {b} → Tg b → L
    pth  : ∀ {b} (τ : Tg b) → lv τ ≤ j
    Lowᵗ : ∀ {b} (τ : Tg b) (p : Pos (lv τ)) → E.T → Br (lv τ) p → Set
    Chdᵗ : ∀ {b} (τ : Tg b) (c : CH (lv τ)) → E.T → ChT (lv τ) c → Set
    Nuᵗ  : ∀ {b} (τ : Tg b) → Pos (lv τ) → E.T → Set
    νᵗ   : ∀ {b} → Tg b → E.T
    Hi   : E.T → Set
    Lo   : E.T → Set

  Mj : E.T → Tr j → Set
  Mj = Mᴴ (Sig j) Low Chd Nu

  Mᵗ : ∀ {b} (τ : Tg b) → E.T → Tr (lv τ) → Set
  Mᵗ τ = Mᴴ (Sig (lv τ)) (Lowᵗ τ) (Chdᵗ τ) (Nuᵗ τ)

  GB : Base j → E.T → Set
  GB B t₀ = (σ : Tg true) → (proj₁ (Ωt (lv σ)) K.⊴ proj₁ (B (lv σ) (pth σ))) × Mᵗ σ (ψᵘ (νᵗ σ) t₀) (proj₁ (B (lv σ) (pth σ)))

  KcT : Ok j → Set₁
  KcT oj = ∀ {b} (τ : Tg b) (p : Pos j) (Q : Keep (lv τ) (Br j p) (fromBr j p zero) → Set)
    → ((σ : Tg true) (toBr : Tr (lv σ) → Br j p)
         → ((F : (k : L) → k ≤ j → Tr k) → fromBr j p (F (at j p) (posW j p)) ≡ toBr (F (lv σ) (pth σ)))
         → (∀ {η y} → Mᵗ σ η y → Low p η (toBr y))
         → (∀ {ν′} → Nu p ν′ → ν′ ≡ νᵗ σ)
         → cmpᵀ (sucT (νᵗ σ)) (νᵗ τ) ≡ gt
         → Q nothing)
    → ((q : Pos (lv τ)) (cv : Br (lv τ) q → Br j p) (eq : cv (fromBr (lv τ) q zero) ≡ fromBr j p zero)
         → (∀ {ν′} → Nu p ν′ → Nuᵗ τ q ν′)
         → (∀ η c → Lowᵗ τ q η c → Low p η (cv c))
         → Q (just (q , cv , eq)))
    → Q (kp j oj p (pth τ))

record Laws {j : L} (D : Data j) (oj : Ok j) (ν : E.T) : Set₁ where
  open Data D
  field
    hi-pen : (μ : E.T) → Hi μ → (p : Pos j) {ν′ : E.T} → Nu p ν′ → Pen (cmpᵀ (sucT ν′) μ)
    hi-own : Hi ν
    lo-gt  : (μ : E.T) → Lo μ → ∀ {b} (τ : Tg b) → cmpᵀ (sucT μ) (νᵗ τ) ≡ gt
    penᵗ   : ∀ {b} (τ : Tg b) (q : Pos (lv τ)) {ν′ : E.T} → Nuᵗ τ q ν′ → Pen (cmpᵀ (sucT ν′) (νᵗ τ))
    leaf   : Mj (E.Ωt ν) (proj₁ (Ωt j))
    leafᵗ  : (σ : Tg true) → Mᵗ σ (E.Ωt (νᵗ σ)) (proj₁ (Ωt (lv σ)))
    selfP  : (r : Rb j) (B : Base j) (β : Tr⁺ j) (P₀ : E.T) → Mj (ψᵘ ν P₀) (proj₁ β)
           → ∀ {a x} → Mj a x → Mj (ψᵘ ν (P₀ ++ a)) (proj₁ (ψ j oj r B j self β x))
    upP    : (ℓ′ : L) (Low′ : (p : Pos ℓ′) → E.T → Br ℓ′ p → Set) (Chd′ : (c : CH ℓ′) → E.T → ChT ℓ′ c → Set)
             (Nu′ : Pos ℓ′ → E.T → Set) (ν′ : E.T) (d : Dn ℓ′ j) → Hi ν′
           → ((p : Pos j) {η : E.T} → Nu p η → Nu′ (mv d p) η)
           → ((p : Pos j) {η : E.T} (c : Br ℓ′ (mv d p)) → Low′ (mv d p) η c → Low p η (mvBr d p c))
           → (b : Tr⁺ ℓ′) (t : E.T) → Mᴴ (Sig ℓ′) Low′ Chd′ Nu′ (ψᵘ ν′ t) (proj₁ b)
           → ∀ {s y} → Mj s y → Mᴴ (Sig ℓ′) Low′ Chd′ Nu′ (ψᵘ ν′ (t ++ s)) (proj₁ (Up j d b y))
    kc     : KcT oj
    df     : ∀ {b} (τ : Tg b) (r : Rb j) (B : Base j) (t₀ : E.T) → GB B t₀
           → (β : Tr⁺ (lv τ)) → Mᵗ τ (ψᵘ (νᵗ τ) t₀) (proj₁ β)
           → ∀ {a x} → Mj a x → Mᵗ τ (ψᵘ (νᵗ τ) (t₀ ++ a)) (proj₁ (ψ j oj r B (lv τ) (pth τ) β x))
```

## 一步: 后继层号

前提都在记号一侧: ν₊ 的 Ω 项以 ν 为共尾下标 (`cofS`, `fsS`), ν 不低于自己与各目标 (`gtν`, `loν`), j 的槽位与 ν 都低于 ν₊ (`hiν`, `penT`).

```agda
module Step₊ {j : L} {oj : Ok j} {ν : E.T} (D : Data j) (W : Laws D oj ν) (ν₊ : E.T)
  (cofS : cof (E.Ωt ν₊) ≡ cΩ ν)
  (fsS : ∀ η → fsT (E.Ωt ν₊) η ≡ η)
  (gtν : cmpᵀ (sucT ν) ν ≡ gt)
  (loν : Data.Lo D ν)
  (hiν : Data.Hi D ν₊)
  (penT : Pen (cmpᵀ (sucT ν) ν₊)) where
  open Data D
  open Laws W

  ℓ₊ : L
  ℓ₊ = nd sS (λ _ → j)

  o₊ : Ok ℓ₊
  o₊ = tt , λ _ → oj

  Low₊ : (p : Pos ℓ₊) → E.T → Br ℓ₊ p → Set
  Low₊ (inj₁ ())
  Low₊ (inj₂ (tt , inj₁ tt)) = Mj
  Low₊ (inj₂ (tt , inj₂ p))  = Low p

  Nu₊ : Pos ℓ₊ → E.T → Set
  Nu₊ (inj₁ ())
  Nu₊ (inj₂ (tt , inj₁ tt)) ν′ = ν′ ≡ ν
  Nu₊ (inj₂ (tt , inj₂ p))     = Nu p

  Tg₊ : Bool → Set
  Tg₊ b = Maybe (Tg b)

  lv₊ : ∀ {b} → Tg₊ b → L
  lv₊ nothing  = j
  lv₊ (just τ) = lv τ

  pth₊ : ∀ {b} (τ : Tg₊ b) → lv₊ τ ≤ ℓ₊
  pth₊ {b = true}  nothing  = inc tt self
  pth₊ {b = false} nothing  = inu (λ _ → self)
  pth₊ {b = true}  (just τ) = inc tt (pth τ)
  pth₊ {b = false} (just τ) = inu (λ _ → pth τ)

  Lowᵗ₊ : ∀ {b} (τ : Tg₊ b) (p : Pos (lv₊ τ)) → E.T → Br (lv₊ τ) p → Set
  Lowᵗ₊ nothing  = Low
  Lowᵗ₊ (just τ) = Lowᵗ τ

  Chdᵗ₊ : ∀ {b} (τ : Tg₊ b) (c : CH (lv₊ τ)) → E.T → ChT (lv₊ τ) c → Set
  Chdᵗ₊ nothing  = Chd
  Chdᵗ₊ (just τ) = Chdᵗ τ

  Nuᵗ₊ : ∀ {b} (τ : Tg₊ b) → Pos (lv₊ τ) → E.T → Set
  Nuᵗ₊ nothing  = Nu
  Nuᵗ₊ (just τ) = Nuᵗ τ

  νᵗ₊ : ∀ {b} → Tg₊ b → E.T
  νᵗ₊ nothing  = ν
  νᵗ₊ (just τ) = νᵗ τ

  Hi₊ Lo₊ : E.T → Set
  Hi₊ μ = Hi μ × Pen (cmpᵀ (sucT ν) μ)
  Lo₊ μ = Lo μ × (cmpᵀ (sucT μ) ν ≡ gt)

  D₊ : Data ℓ₊
  D₊ = record { Low = Low₊ ; Chd = λ _ → Mj ; Nu = Nu₊ ; Tg = Tg₊ ; lv = lv₊ ; pth = pth₊
              ; Lowᵗ = Lowᵗ₊ ; Chdᵗ = Chdᵗ₊ ; Nuᵗ = Nuᵗ₊ ; νᵗ = νᵗ₊ ; Hi = Hi₊ ; Lo = Lo₊ }

  module D′ = Data D₊

  M₊ : E.T → Tr ℓ₊ → Set
  M₊ = D′.Mj

  Mᵗ₊ : ∀ {b} (τ : Tg₊ b) → E.T → Tr (lv₊ τ) → Set
  Mᵗ₊ = D′.Mᵗ

  module G₊ = Gen {Sig ℓ₊} {Low₊} {λ _ → Mj} {Nu₊}
  module Gt {b : Bool} (τ : Tg₊ b) = Gen {Sig (lv₊ τ)} {Lowᵗ₊ τ} {Chdᵗ₊ τ} {Nuᵗ₊ τ}
```

小律.

```agda
  hi-pen₊ : (μ : E.T) → Hi₊ μ → (p : Pos ℓ₊) {ν′ : E.T} → Nu₊ p ν′ → Pen (cmpᵀ (sucT ν′) μ)
  hi-pen₊ μ hi (inj₁ ())
  hi-pen₊ μ hi (inj₂ (tt , inj₁ tt)) refl = proj₂ hi
  hi-pen₊ μ hi (inj₂ (tt , inj₂ p))  nu   = hi-pen μ (proj₁ hi) p nu

  hi-own₊ : Hi₊ ν₊
  hi-own₊ = hiν , penT

  lo-gt₊ : (μ : E.T) → Lo₊ μ → ∀ {b} (τ : Tg₊ b) → cmpᵀ (sucT μ) (νᵗ₊ τ) ≡ gt
  lo-gt₊ μ lo nothing  = proj₂ lo
  lo-gt₊ μ lo (just τ) = lo-gt μ (proj₁ lo) τ

  penᵗ₊ : ∀ {b} (τ : Tg₊ b) (q : Pos (lv₊ τ)) {ν′ : E.T} → Nuᵗ₊ τ q ν′ → Pen (cmpᵀ (sucT ν′) (νᵗ₊ τ))
  penᵗ₊ nothing  q nu = hi-pen ν hi-own q nu
  penᵗ₊ (just τ) q nu = penᵗ τ q nu

  leaf₊ : M₊ (E.Ωt ν₊) (proj₁ (Ωt ℓ₊))
  leaf₊ = mΩ cofS refl (λ η c l → subst (λ s → M₊ s (up zero tt (suc c) (z◃ c ◃s))) (sym (fsS η)) (mU mz (mw l ◃s)))

  leafᵗ₊ : (σ : Tg₊ true) → Mᵗ₊ σ (E.Ωt (νᵗ₊ σ)) (proj₁ (Ωt (lv₊ σ)))
  leafᵗ₊ nothing  = leaf
  leafᵗ₊ (just σ) = leafᵗ σ
```

槽位的判定: 顶槽位 (分支在 j 的树上) 在每个目标处走链, 链经过目标 `nothing` (j 自身, 指定孩子的路径); 其余槽位在目标 j 处保留, 在更低的目标处照 j 的判定.

```agda
  kc₊ : D′.KcT o₊
  kc₊ τ (inj₁ ()) Q ch kq
  kc₊ {b = true}  nothing  (inj₂ (tt , inj₁ tt)) Q ch kq = ch nothing (λ y → y) (λ F → refl) (λ m → m) (λ nu → nu) gtν
  kc₊ {b = false} nothing  (inj₂ (tt , inj₁ tt)) Q ch kq = ch nothing (λ y → y) (λ F → refl) (λ m → m) (λ nu → nu) gtν
  kc₊ {b = true}  (just τ) (inj₂ (tt , inj₁ tt)) Q ch kq = ch nothing (λ y → y) (λ F → refl) (λ m → m) (λ nu → nu) (lo-gt ν loν τ)
  kc₊ {b = false} (just τ) (inj₂ (tt , inj₁ tt)) Q ch kq = ch nothing (λ y → y) (λ F → refl) (λ m → m) (λ nu → nu) (lo-gt ν loν τ)
  kc₊ {b = true}  nothing  (inj₂ (tt , inj₂ p))  Q ch kq = kq p (λ z → z) refl (λ nu → nu) (λ η c l → l)
  kc₊ {b = false} nothing  (inj₂ (tt , inj₂ p))  Q ch kq = kq p (λ z → z) refl (λ nu → nu) (λ η c l → l)
  kc₊ {b = true}  (just τ) (inj₂ (tt , inj₂ p))  Q ch kq =
    kc τ p Q (λ σ toBr gen toLw nuσ gtσ → ch (just σ) toBr (λ F → gen (λ k w → F k (inc tt w))) toLw nuσ gtσ) kq
  kc₊ {b = false} (just τ) (inj₂ (tt , inj₂ p))  Q ch kq =
    kc τ p Q (λ σ toBr gen toLw nuσ gtσ → ch (just σ) toBr (λ F → gen (λ k w → F k (inc tt w))) toLw nuσ gtσ) kq
```

## 折到自身, 上折进高层

```agda
  selfP₊ : (r : Rb ℓ₊) (B : Base ℓ₊) (β : Tr⁺ ℓ₊) (P₀ : E.T) → M₊ (ψᵘ ν₊ P₀) (proj₁ β)
         → ∀ {a x} → M₊ a x → M₊ (ψᵘ ν₊ (P₀ ++ a)) (proj₁ (ψ ℓ₊ o₊ r B ℓ₊ self β x))
  selfP₊ r B β P₀ hP (mz {x = x}) =
    ++[] (λ z → M₊ (ψᵘ ν₊ z) (proj₁ (ψ ℓ₊ o₊ r B ℓ₊ self β x))) P₀
      (G₊.m-zl (λ y → proj₁ (ψ ℓ₊ o₊ r B ℓ₊ self β y)) (mono ℓ₊ o₊ r B ℓ₊ self β) hP x)
  selfP₊ r B β P₀ hP (m1 {t = a} {x = x} e h) =
    G₊.m-next (ψ ℓ₊ o₊ r B ℓ₊ self β x) (cofψ1 ν₊ (P₀ ++ a) (cof++1 P₀ a e))
      (λ k → trans (fsnψ1 ν₊ (P₀ ++ a) k (cof++1 P₀ a e)) (cong (λ z → replicate k (E.ψ ν₊ z)) (pred++ P₀ a e)))
      (selfP₊ r B β P₀ hP h)
  selfP₊ r B β P₀ hP (mL {t = a} {x = x} e h) =
    mL (cofψω ν₊ (P₀ ++ a) (cof++ω P₀ a e))
      (λ k → subst (λ z → M₊ z (proj₁ (ψ ℓ₊ o₊ r B ℓ₊ self β x)))
        (sym (trans (fsnψω ν₊ (P₀ ++ a) k (cof++ω P₀ a e)) (cong (ψᵘ ν₊) (fsn++ P₀ a k e))))
        (selfP₊ r B β P₀ hP (h k)))
  selfP₊ r B β P₀ hP (mΩ {t = a} {p = p} {g = g} e nu h) =
    mΩ (cofK ν₊ (P₀ ++ a) (hi-pen₊ ν₊ hi-own₊ p nu) (cof++Ω P₀ a e)) nu
      (λ η c l → subst (λ z → M₊ z (proj₁ (ψ ℓ₊ o₊ r B ℓ₊ self β (g c))))
        (sym (trans (fsTK ν₊ (P₀ ++ a) η (hi-pen₊ ν₊ hi-own₊ p nu) (cof++Ω P₀ a e)) (cong (ψᵘ ν₊) (fsT++ P₀ a η e))))
        (selfP₊ r B β P₀ hP (h η c l)))
  selfP₊ r B β P₀ hP (mU {t = s₀} {s = s₁} {x = x} {y = y} h ch) =
    subst (λ z → M₊ (ψᵘ ν₊ z) (proj₁ (Up j (down stop tt) (ψ ℓ₊ o₊ r B ℓ₊ self β x) y))) (++-assoc P₀ s₀ s₁)
      (upP ℓ₊ Low₊ (λ _ → Mj) Nu₊ ν₊ (down stop tt) hiν (λ p nu → nu) (λ p c l → l)
           (ψ ℓ₊ o₊ r B ℓ₊ self β x) (P₀ ++ s₀) (selfP₊ r B β P₀ hP h) ch)
  selfP₊ r B β P₀ hP (mw h dd) = mw (selfP₊ r B β P₀ hP h) (mono ℓ₊ o₊ r B ℓ₊ self β dd)
  selfP₊ r B β P₀ hP (mc le h) = mc (appᵘ ν₊ P₀ le) (selfP₊ r B β P₀ hP h)

  module UpH (ℓ′ : L) (Low′ : (p : Pos ℓ′) → E.T → Br ℓ′ p → Set) (Chd′ : (c : CH ℓ′) → E.T → ChT ℓ′ c → Set)
             (Nu′ : Pos ℓ′ → E.T → Set) (ν′ : E.T) (hi : Hi₊ ν′) where
    M′ : E.T → Tr ℓ′ → Set
    M′ = Mᴴ (Sig ℓ′) Low′ Chd′ Nu′

    module G′ = Gen {Sig ℓ′} {Low′} {Chd′} {Nu′}

    upP₊ : (d : Dn ℓ′ ℓ₊)
         → ((p : Pos ℓ₊) {η : E.T} → Nu₊ p η → Nu′ (mv d p) η)
         → ((p : Pos ℓ₊) {η : E.T} (c : Br ℓ′ (mv d p)) → Low′ (mv d p) η c → Low₊ p η (mvBr d p c))
         → (b : Tr⁺ ℓ′) (t : E.T) → M′ (ψᵘ ν′ t) (proj₁ b)
         → ∀ {s y} → M₊ s y → M′ (ψᵘ ν′ (t ++ s)) (proj₁ (Up ℓ₊ d b y))
    upP₊ d cN cL b t mb (mz {x = y}) =
      ++[] (λ z → M′ (ψᵘ ν′ z) (proj₁ (Up ℓ₊ d b y))) t
        (G′.m-zl (λ y → proj₁ (Up ℓ₊ d b y)) (Upm ℓ₊ d b) mb y)
    upP₊ d cN cL b t mb (m1 {t = s} {x = y} e h) =
      G′.m-next (Up ℓ₊ d b y) (cofψ1 ν′ (t ++ s) (cof++1 t s e))
        (λ k → trans (fsnψ1 ν′ (t ++ s) k (cof++1 t s e)) (cong (λ z → replicate k (E.ψ ν′ z)) (pred++ t s e)))
        (upP₊ d cN cL b t mb h)
    upP₊ d cN cL b t mb (mL {t = s} {x = y} e h) =
      mL (cofψω ν′ (t ++ s) (cof++ω t s e))
        (λ k → subst (λ z → M′ z (proj₁ (Up ℓ₊ d b y)))
          (sym (trans (fsnψω ν′ (t ++ s) k (cof++ω t s e)) (cong (ψᵘ ν′) (fsn++ t s k e))))
          (upP₊ d cN cL b t mb (h k)))
    upP₊ d cN cL b t mb (mΩ {t = s} {p = p} {g = g} e nu h) =
      mΩ (cofK ν′ (t ++ s) (hi-pen₊ ν′ hi p nu) (cof++Ω t s e)) (cN p nu)
        (λ η c l → subst (λ z → M′ z (proj₁ (Up ℓ₊ d b (g (mvBr d p c)))))
          (sym (trans (fsTK ν′ (t ++ s) η (hi-pen₊ ν′ hi p nu) (cof++Ω t s e)) (cong (ψᵘ ν′) (fsT++ t s η e))))
          (upP₊ d cN cL b t mb (h η (mvBr d p c) (cL p c l))))
    upP₊ d cN cL b t mb (mU {t = s₀} {s = s₁} {x = y₀} {y = y₁} h ch) =
      subst (λ z → M′ (ψᵘ ν′ z) (proj₁ (Up j (down d tt) (Up ℓ₊ d b y₀) y₁))) (++-assoc t s₀ s₁)
        (upP ℓ′ Low′ Chd′ Nu′ ν′ (down d tt) (proj₁ hi)
             (λ p nu → cN (inj₂ (tt , inj₂ p)) nu) (λ p c l → cL (inj₂ (tt , inj₂ p)) c l)
             (Up ℓ₊ d b y₀) (t ++ s₀) (upP₊ d cN cL b t mb h) ch)
    upP₊ d cN cL b t mb (mw h dd) = mw (upP₊ d cN cL b t mb h) (Upm ℓ₊ d b dd)
    upP₊ d cN cL b t mb (mc le h) = mc (appᵘ ν′ t le) (upP₊ d cN cL b t mb h)
```

## 朝登记的目标下折

底在每个指定孩子路径的目标处不低于该层的 Ω 树并承载 ψ(t₀) (`GB`). 嵌入行: 目标是 j 时用 `selfP`, 更低时用 j 的 `df`, 孩子层的底合格由对左项的归纳假设给出 (`gbS`). 结点行由 `kc₊` 分成链与保留.

```agda
  module Fold (r : Rb ℓ₊) (B : Base ℓ₊) (t₀ : E.T) (gb : D′.GB B t₀) where

    F : ∀ {b} (τ : Tg₊ b) → Tr⁺ (lv₊ τ) → Tr ℓ₊ → Tr⁺ (lv₊ τ)
    F τ β x = ψ ℓ₊ o₊ r B (lv₊ τ) (pth₊ τ) β x

    cb : Tr ℓ₊ → Base j
    cb x i u = ψ ℓ₊ o₊ r B i (inc tt u) (B i (inc tt u)) x

    feed : (p : Pos ℓ₊) → (Br ℓ₊ p → Tr ℓ₊) → Br ℓ₊ p → Br ℓ₊ p
    feed p g z = fromBr ℓ₊ p (proj₁ (ψ ℓ₊ o₊ r B (at ℓ₊ p) (posW ℓ₊ p) (B (at ℓ₊ p) (posW ℓ₊ p)) (g z)))

    mutual
      LF : ∀ {b} (τ : Tg₊ b) (β : Tr⁺ (lv₊ τ)) → Mᵗ₊ τ (ψᵘ (νᵗ₊ τ) t₀) (proj₁ β)
         → ∀ {a x} → M₊ a x → Mᵗ₊ τ (ψᵘ (νᵗ₊ τ) (t₀ ++ a)) (proj₁ (F τ β x))
      LF τ β hβ (mz {x = x}) =
        ++[] (λ z → Mᵗ₊ τ (ψᵘ (νᵗ₊ τ) z) (proj₁ (F τ β x))) t₀
          (Gt.m-zl τ (λ y → proj₁ (F τ β y)) (mono ℓ₊ o₊ r B (lv₊ τ) (pth₊ τ) β) hβ x)
      LF τ β hβ (m1 {t = a} {x = x} e h) =
        Gt.m-next τ (F τ β x) (cofψ1 (νᵗ₊ τ) (t₀ ++ a) (cof++1 t₀ a e))
          (λ k → trans (fsnψ1 (νᵗ₊ τ) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ (νᵗ₊ τ) z)) (pred++ t₀ a e)))
          (LF τ β hβ h)
      LF τ β hβ (mL {t = a} {x = x} e h) =
        mL (cofψω (νᵗ₊ τ) (t₀ ++ a) (cof++ω t₀ a e))
          (λ k → subst (λ z → Mᵗ₊ τ z (proj₁ (F τ β x)))
            (sym (trans (fsnψω (νᵗ₊ τ) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᵘ (νᵗ₊ τ)) (fsn++ t₀ a k e))))
            (LF τ β hβ (h k)))
      LF τ β hβ (mΩ {t = a} {ν = ν′} {p = p} {g = g} e nu h) =
        kc₊ τ p (λ K → Mᵗ₊ τ (ψᵘ (νᵗ₊ τ) (t₀ ++ a)) (proj₁ (node⁺ K (λ z → F τ β (g z)) (feed p g))))
          (λ σ toBr gen toLw nuσ gtσ →
            mL (cofG (νᵗ₊ τ) (t₀ ++ a) (subst (λ z → cmpᵀ (sucT z) (νᵗ₊ τ) ≡ gt) (sym (nuσ nu)) gtσ) (cof++Ω t₀ a e))
              (λ k → subst (λ z → Mᵗ₊ τ z (proj₁ (limc⁺ (λ k′ → F τ β (g (iter (feed p g) (fromBr ℓ₊ p zero) k′))))))
                (sym (trans (fsnG (νᵗ₊ τ) (t₀ ++ a) k (subst (λ z → cmpᵀ (sucT z) (νᵗ₊ τ) ≡ gt) (sym (nuσ nu)) gtσ) (cof++Ω t₀ a e))
                            (cong (ψᵘ (νᵗ₊ τ)) (fsT++ t₀ a (γT (t₀ ++ a) ν′ k) e))))
                (Gt.m-cum τ (λ k′ → F τ β (g (iter (feed p g) (fromBr ℓ₊ p zero) k′))) (suc k)
                  (LF τ β hβ (h (γT (t₀ ++ a) ν′ k) (iter (feed p g) (fromBr ℓ₊ p zero) (suc k))
                                (chain σ p toBr gen toLw e (nuσ nu) h k))))))
          (λ q cv eq nuq lw →
            mΩ (cofK (νᵗ₊ τ) (t₀ ++ a) (penᵗ₊ τ q (nuq nu)) (cof++Ω t₀ a e)) (nuq nu)
              (λ η c l → subst (λ z → Mᵗ₊ τ z (proj₁ (F τ β (g (cv c)))))
                (sym (trans (fsTK (νᵗ₊ τ) (t₀ ++ a) η (penᵗ₊ τ q (nuq nu)) (cof++Ω t₀ a e)) (cong (ψᵘ (νᵗ₊ τ)) (fsT++ t₀ a η e))))
                (LF τ β hβ (h η (cv c) (lw η c l)))))
      LF {b = true} nothing β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
        subst (λ z → Mj (ψᵘ ν z) (proj₁ (ψ j oj (proj₂ r tt) (cb x) j self (F {b = true} nothing β x) y))) (++-assoc t₀ a s₁)
          (selfP (proj₂ r tt) (cb x) (F {b = true} nothing β x) (t₀ ++ a) (LF {b = true} nothing β hβ h) ch)
      LF {b = false} nothing β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
        subst (λ z → Mj (ψᵘ ν z) (proj₁ (ψ j oj (proj₂ r tt) (cb x) j self (F {b = false} nothing β x) y))) (++-assoc t₀ a s₁)
          (selfP (proj₂ r tt) (cb x) (F {b = false} nothing β x) (t₀ ++ a) (LF {b = false} nothing β hβ h) ch)
      LF {b = true} (just τ) β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
        subst (λ z → Mᵗ τ (ψᵘ (νᵗ τ) z) (proj₁ (ψ j oj (proj₂ r tt) (cb x) (lv τ) (pth τ) (F {b = true} (just τ) β x) y))) (++-assoc t₀ a s₁)
          (df τ (proj₂ r tt) (cb x) (t₀ ++ a) (gbS h) (F {b = true} (just τ) β x) (LF {b = true} (just τ) β hβ h) ch)
      LF {b = false} (just τ) β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
        subst (λ z → Mᵗ τ (ψᵘ (νᵗ τ) z) (proj₁ (ψ j oj (proj₂ r tt) (cb x) (lv τ) (pth τ) (F {b = false} (just τ) β x) y))) (++-assoc t₀ a s₁)
          (df τ (proj₂ r tt) (cb x) (t₀ ++ a) (gbS h) (F {b = false} (just τ) β x) (LF {b = false} (just τ) β hβ h) ch)
      LF τ β hβ (mw h dd) = mw (LF τ β hβ h) (mono ℓ₊ o₊ r B (lv₊ τ) (pth₊ τ) β dd)
      LF τ β hβ (mc le h) = mc (appᵘ (νᵗ₊ τ) t₀ le) (LF τ β hβ h)

      gbS : ∀ {a x} → M₊ a x → GB (cb x) (t₀ ++ a)
      gbS {x = x} h σ =
        ⊴t (proj₁ (gb (just σ))) (to (ψ-⊵ ℓ₊ o₊ r B (lv σ) (inc tt (pth σ)) (B (lv σ) (inc tt (pth σ))) x))
        , LF {b = true} (just σ) (B (lv σ) (inc tt (pth σ))) (proj₂ (gb (just σ))) h

      chain : (σ : Tg₊ true) (p : Pos ℓ₊) (toBr : Tr (lv₊ σ) → Br ℓ₊ p)
            → ((F′ : (k : L) → k ≤ ℓ₊ → Tr k) → fromBr ℓ₊ p (F′ (at ℓ₊ p) (posW ℓ₊ p)) ≡ toBr (F′ (lv₊ σ) (pth₊ σ)))
            → (∀ {η y} → Mᵗ₊ σ η y → Low₊ p η (toBr y))
            → ∀ {a ν′} {g : Br ℓ₊ p → Tr ℓ₊} → cof a ≡ cΩ ν′ → ν′ ≡ νᵗ₊ σ
            → (∀ η c → Low₊ p η c → M₊ (fsT a η) (g c))
            → ∀ k → Low₊ p (γT (t₀ ++ a) ν′ k) (iter (feed p g) (fromBr ℓ₊ p zero) (suc k))
      chain σ p toBr gen toLw {a} {g = g} e refl h zero =
        subst (Low₊ p (γT (t₀ ++ a) (νᵗ₊ σ) zero))
          (sym (gen (λ k w → proj₁ (ψ ℓ₊ o₊ r B k w (B k w) (g (fromBr ℓ₊ p zero))))))
          (toLw (Gt.m⊴ σ (leafᵗ₊ σ)
            (⊴t (proj₁ (gb σ)) (to (ψ-⊵ ℓ₊ o₊ r B (lv₊ σ) (pth₊ σ) (B (lv₊ σ) (pth₊ σ)) (g (fromBr ℓ₊ p zero)))))))
      chain σ p toBr gen toLw {a} {g = g} e refl h (suc k) =
        subst (Low₊ p (γT (t₀ ++ a) (νᵗ₊ σ) (suc k)))
          (sym (gen (λ k′ w → proj₁ (ψ ℓ₊ o₊ r B k′ w (B k′ w) (g (iter (feed p g) (fromBr ℓ₊ p zero) (suc k)))))))
          (toLw (subst (λ z → Mᵗ₊ σ (ψᵘ (νᵗ₊ σ) z)
                          (proj₁ (F σ (B (lv₊ σ) (pth₊ σ)) (g (iter (feed p g) (fromBr ℓ₊ p zero) (suc k))))))
                  (sym (fsT++ t₀ a (γT (t₀ ++ a) (νᵗ₊ σ) k) e))
                  (LF σ (B (lv₊ σ) (pth₊ σ)) (proj₂ (gb σ))
                    (h (γT (t₀ ++ a) (νᵗ₊ σ) k) (iter (feed p g) (fromBr ℓ₊ p zero) (suc k))
                       (chain σ p toBr gen toLw e refl h k)))))
```

## 一步定理

```agda
  W₊ : Laws D₊ o₊ ν₊
  W₊ = record
    { hi-pen = hi-pen₊
    ; hi-own = hi-own₊
    ; lo-gt  = lo-gt₊
    ; penᵗ   = penᵗ₊
    ; leaf   = leaf₊
    ; leafᵗ  = leafᵗ₊
    ; selfP  = selfP₊
    ; upP    = λ ℓ′ Low′ Chd′ Nu′ ν′ d hi → UpH.upP₊ ℓ′ Low′ Chd′ Nu′ ν′ hi d
    ; kc     = kc₊
    ; df     = λ τ r B t₀ gb → Fold.LF r B t₀ gb τ
    }
```

## 任意目标处 Ω 树的值

```agda
module Top {j : L} {oj : Ok j} {ν : E.T} (D : Data j) (W : Laws D oj ν) where
  open Data D
  open Laws W

  gb₀ : (B : Base j) → ((i : L) (u : i ≤ j) → proj₁ (Ωt i) K.⊴ proj₁ (B i u)) → GB B []
  gb₀ B ok σ = ok (lv σ) (pth σ) , Gen.m⊴ (leafᵗ σ) (ok (lv σ) (pth σ))

  Ω-fold : ∀ {b} (τ : Tg b) (r : Rb j) (B : Base j) → ((i : L) (u : i ≤ j) → proj₁ (Ωt i) K.⊴ proj₁ (B i u))
         → (β : Tr⁺ (lv τ)) → Mᵗ τ (ψᵘ (νᵗ τ) []) (proj₁ β)
         → Mᵗ τ (ψᵘ (νᵗ τ) (E.Ωt ν)) (proj₁ (ψ j oj r B (lv τ) (pth τ) β (proj₁ (Ωt j))))
  Ω-fold τ r B ok β hβ = df τ r B [] (gb₀ B ok) β hβ leaf
```
