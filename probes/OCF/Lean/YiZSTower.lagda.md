# ω 层之上的有限段: 偏移 n 的 Ω 树朝 ω 层折, 承载 ψ_ω(Ω_{ω+n})

> 验收文件 (读记号), 不进成品; 树、折叠、合法性不改. 判决: 编译定理, 无前提. ω 层满足 [YiZSLev](YiZSLev.lagda.md) 的接口 (`W₀`), 一步定理迭代 n 次得 `ω 层 ⊕ ↑ n` 的接口 (`pk`, 对 n 递归, 各阶段同一条一步定理); 所以 `carN`: 偏移 n+1 的 Ω 树承载 ψ_ω(Ω_{ω+n+1}).
> `seg`: `YiSVRed.Red.StepS` 的结论在 η ≤ ω+n+1 且孩子字面含 n+1 时成立; `ext-ω2`, `branch-ω2`: 字面延伸 ω 的孩子处承载 ψ_ω(Ω_{ω·2}).
> 不给出什么: `StepS` 本身没有证出 (它的前提是 `M 0 (pred η) x`, 这里用的是字面前提 `nat (suc n) ⊴ c`); ω+ω 以上的层号没有做.
> 来源: `upω` 照 `YiHCOmega.UpT.PuTˢ` 与 `Tω.upJ`, `upB` (目标从 ω 层换成任意层); `penB′` 照 `YiHCOmega.penB`; `cofSᵀ`, `fsSᵀ` 照 `YiANFam.cofΩ`, `fsTΩ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZSTower where
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep)
open import OCF.Lean.YiRBSib using (Rb; ψ)
import OCF.Lean.YiKVRel as K
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc; module Gen)
import OCF.Align.EboLeanDef as E
open E using (cof; cω; cΩ; fsn; fsT; natT; sucT; cmpᵀ; gt)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (Pen; cofK; fsTK; cof-nat; pred-nat; cmp-gt; cmp-pen)
open import OCF.Lean.YiDCRel using (suc-nat)
open import OCF.Lean.YiCLFam using (fn; lev; fd0)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiLRBridge using (NwB)
open import OCF.Lean.YiHCBridge using (MB; LwB)
open import OCF.Lean.YiHCOmega using (ψᵘ; appᵘ; penω; module UpT)
open import OCF.Lean.YiLTLift using (Ωt≤)
open import OCF.Lean.YiTBRow using (h₁; nat)
open import OCF.Lean.YiTBTab using (ωᶜ)
open import OCF.Lean.YiBSBase using (seen)
open import OCF.Lean.YiSVMono
open import OCF.Lean.YiSVStep using (to)
open import OCF.Lean.YiSVCell using (cell)
open import OCF.Lean.YiSVOmega
open import OCF.Lean.YiSVRed using (Qη; module Red)
open import OCF.Lean.YiZSLev
open Wω using (Lω; Mω; Lowω; Nuω)
```

## 记号一侧: ω+n

```agda
νᵀ : ℕ → E.T
νᵀ n = E.ψ [] (E.𝟏 ∷ []) ∷ natT n

ν0 : νᵀ 0 ≡ ωᵀ
ν0 = refl

ν1 : νᵀ 1 ≡ sucT ωᵀ
ν1 = refl

cofSᵀ : ∀ n → cof (E.Ωt (νᵀ (suc n))) ≡ cΩ (νᵀ n)
cofSᵀ n = trans (cong (E.cofψ0 (νᵀ (suc n))) (cof-nat n)) (cong (λ z → cΩ (E.ψ [] (E.𝟏 ∷ []) ∷ z)) (pred-nat n))

fsSᵀ : ∀ n η → fsT (E.Ωt (νᵀ (suc n))) η ≡ η
fsSᵀ n η = cong (λ c → E.fsT0 (νᵀ (suc n)) c η) (cof-nat n)

gtᵀ : ∀ {m k} → m ≤ⁿ k → cmpᵀ (sucT (νᵀ k)) (νᵀ m) ≡ gt
gtᵀ {m} {k} le = cmp-gt {b = m} {a = k} le

penᵀ : ∀ {m k} → suc m ≤ⁿ k → Pen (cmpᵀ (sucT (νᵀ m)) (νᵀ k))
penᵀ {m} {k} le = cmp-pen {a = m} {b = k} le

HiN : E.T → Set
HiN μ = ∀ k → Pen (cmpᵀ (sucT (natT k)) μ)

hiNᵀ : ∀ k → HiN (νᵀ k)
hiNᵀ k i = inj₁ (cong (λ z → cmpᵀ z (νᵀ k)) (suc-nat i))

ω2ᵀ : E.T
ω2ᵀ = E.ψ [] (E.𝟏 ∷ []) ∷ E.ψ [] (E.𝟏 ∷ []) ∷ []

hiN2 : HiN ω2ᵀ
hiN2 i = inj₁ (cong (λ z → cmpᵀ z ω2ᵀ) (suc-nat i))

pen2 : ∀ n → Pen (cmpᵀ (sucT (νᵀ n)) ω2ᵀ)
pen2 zero    = inj₁ refl
pen2 (suc n) = inj₁ refl

penB′ : (μ : E.T) → HiN μ → ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) (t : Pos⁼ ℓ) {ν : E.T} → NwB ℓ e t ν → Pen (cmpᵀ (sucT ν) μ)
penB′ μ hi {N} _ refl t refl = hi (lev N t)
```

## ω 层满足接口

没有登记的目标. 新证的只有 `upω`: ω 层的树上折进任意高层 (高层的关系与读法是参数).

```agda
module Base (oc : (k : ℕ) → Ok (G k)) where

  ⊥L : ∀ {b : Bool} → ⊥ → L
  ⊥L ()

  D₀ : Data Lω
  D₀ = record { Low = Lowω ; Chd = λ m → MB (G m) (eG m) ; Nu = Nuω ; Tg = λ _ → ⊥ ; lv = λ {b} → ⊥L {b} ; pth = λ { () }
              ; Lowᵗ = λ { () } ; Chdᵗ = λ { () } ; Nuᵗ = λ { () } ; νᵗ = λ { () } ; Hi = HiN ; Lo = λ _ → ⊤ }

  module UpΩ (ℓ′ : L) (Low′ : (p : Pos ℓ′) → E.T → Br ℓ′ p → Set) (Chd′ : (c : CH ℓ′) → E.T → ChT ℓ′ c → Set)
             (Nu′ : Pos ℓ′ → E.T → Set) (ν′ : E.T) (hi : HiN ν′) where
    M′ : E.T → Tr ℓ′ → Set
    M′ = Mᴴ (Sig ℓ′) Low′ Chd′ Nu′

    module G′ = Gen {Sig ℓ′} {Low′} {Chd′} {Nu′}

    upJ′ : ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) (D : Dn ℓ′ ℓ)
         → ((p : Pos ℓ) {η : E.T} → NwB ℓ e (inj₂ p) η → Nu′ (mv D p) η)
         → ((p : Pos ℓ) {η : E.T} (c : Br ℓ′ (mv D p)) → Low′ (mv D p) η c → LwB ℓ e (inj₂ p) η (mvBr D p c))
         → (b : Tr⁺ ℓ′) {t : E.T} → M′ (ψᵘ ν′ t) (proj₁ b)
         → ∀ {s y} → MB ℓ e s y → M′ (ψᵘ ν′ (t ++ s)) (proj₁ (Up ℓ D b y))
    upJ′ {N} _ refl D hN hL b mb m = UpT.PuT ν′ D hN hL hi N fd0 b mb m

    upω : (d : Dn ℓ′ Lω)
        → ((p : Pos Lω) {η : E.T} → Nuω p η → Nu′ (mv d p) η)
        → ((p : Pos Lω) {η : E.T} (c : Br ℓ′ (mv d p)) → Low′ (mv d p) η c → Lowω p η (mvBr d p c))
        → (b : Tr⁺ ℓ′) (t : E.T) → M′ (ψᵘ ν′ t) (proj₁ b)
        → ∀ {s y} → Mω s y → M′ (ψᵘ ν′ (t ++ s)) (proj₁ (Up Lω d b y))
    upω d cN cL b t mb (mz {x = y}) =
      ++[] (λ z → M′ (ψᵘ ν′ z) (proj₁ (Up Lω d b y))) t
        (G′.m-zl (λ y → proj₁ (Up Lω d b y)) (Upm Lω d b) mb y)
    upω d cN cL b t mb (m1 {t = s} {x = y} e h) =
      G′.m-next (Up Lω d b y) (cofψ1 ν′ (t ++ s) (cof++1 t s e))
        (λ k → trans (fsnψ1 ν′ (t ++ s) k (cof++1 t s e)) (cong (λ z → replicate k (E.ψ ν′ z)) (pred++ t s e)))
        (upω d cN cL b t mb h)
    upω d cN cL b t mb (mL {t = s} {x = y} e h) =
      mL (cofψω ν′ (t ++ s) (cof++ω t s e))
        (λ k → subst (λ z → M′ z (proj₁ (Up Lω d b y)))
          (sym (trans (fsnψω ν′ (t ++ s) k (cof++ω t s e)) (cong (ψᵘ ν′) (fsn++ t s k e))))
          (upω d cN cL b t mb (h k)))
    upω d cN cL b t mb (mΩ {p = inj₁ ()} _ _ _)
    upω d cN cL b t mb (mΩ {t = s} {p = inj₂ (m , q)} {g = g} e nu h) =
      mΩ (cofK ν′ (t ++ s) (penB′ ν′ hi (G m) (eG m) q nu) (cof++Ω t s e)) (cN (inj₂ (m , q)) nu)
        (λ η c l → subst (λ z → M′ z (proj₁ (Up Lω d b (g (mvBr d (inj₂ (m , q)) c)))))
          (sym (trans (fsTK ν′ (t ++ s) η (penB′ ν′ hi (G m) (eG m) q nu) (cof++Ω t s e)) (cong (ψᵘ ν′) (fsT++ t s η e))))
          (upω d cN cL b t mb (h η (mvBr d (inj₂ (m , q)) c) (cL (inj₂ (m , q)) c l))))
    upω d cN cL b t mb (mU {t = s₀} {s = s₁} {x = y₀} {c = m} {y = y₁} h ch) =
      subst (λ z → M′ (ψᵘ ν′ z) (proj₁ (Up (G m) (down d m) (Up Lω d b y₀) y₁))) (++-assoc t s₀ s₁)
        (upJ′ (G m) (eG m) (down d m) (λ p nu → cN (inj₂ (m , inj₂ p)) nu) (λ p c l → cL (inj₂ (m , inj₂ p)) c l)
              (Up Lω d b y₀) (upω d cN cL b t mb h) ch)
    upω d cN cL b t mb (mw h dd) = mw (upω d cN cL b t mb h) (Upm Lω d b dd)
    upω d cN cL b t mb (mc le h) = mc (appᵘ ν′ t le) (upω d cN cL b t mb h)

  hi-pen₀ : (μ : E.T) → HiN μ → (p : Pos Lω) {ν′ : E.T} → Nuω p ν′ → Pen (cmpᵀ (sucT ν′) μ)
  hi-pen₀ μ hi (inj₁ ())
  hi-pen₀ μ hi (inj₂ (m , q)) nu = penB′ μ hi (G m) (eG m) q nu

  W₀ : Laws D₀ (Rr , oc) ωᵀ
  W₀ = record
    { hi-pen = hi-pen₀
    ; hi-own = penω
    ; lo-gt  = λ { μ _ () }
    ; penᵗ   = λ { () }
    ; leaf   = Hω.leafω (λ _ → ≤-refl)
    ; leafᵗ  = λ { () }
    ; selfP  = λ r B β P₀ hP m → Hω.Self.PFω oc r B β hP m
    ; upP    = λ ℓ′ Low′ Chd′ Nu′ ν′ d hi → UpΩ.upω ℓ′ Low′ Chd′ Nu′ ν′ hi d
    ; kc     = λ { () }
    ; df     = λ { () }
    }
```

## 塔: 一步定理迭代

`J n` 是 ω 层加偏移 n. `pk` 对 n 递归, 每一步是同一条 `Step₊.W₊`; 随带的 `hiA`, `loA` 是下一步要的两条记号比较 (`hi2` 是对 ω·2 的, 用在 [YiZSLim](YiZSLim.lagda.md)). `bot` 取出最低的目标 (ω 层, 一致路径), `isb` 把该目标的层号、路径、关系、读法一并换成字面的.

```agda
  J : ℕ → L
  J n = Lω ⊕ ↑ zero (nat n)

  oJ : ∀ n → OkO Lω (↑ zero (nat n)) → Ok (J n)
  oJ n ob = Ok⊕ Lω (↑ zero (nat n)) (Rr , oc) ob

  record Pk (n : ℕ) (ob : OkO Lω (↑ zero (nat n))) : Set₁ where
    field
      D   : Data (J n)
      W   : Laws D (oJ n ob) (νᵀ n)
      hiA : ∀ k → n ≤ⁿ k → Data.Hi D (νᵀ k)
      loA : ∀ k → n ≤ⁿ k → Data.Lo D (νᵀ k)
      hi2 : Data.Hi D ω2ᵀ

  pk : ∀ n ob → Pk n ob
  pk zero    ob = record { D = D₀ ; W = W₀ ; hiA = λ k _ → hiNᵀ k ; loA = λ _ _ → tt ; hi2 = hiN2 }
  pk (suc n) ob = record
    { D   = S.D₊
    ; W   = S.W₊
    ; hiA = λ k le → Pk.hiA Pn k (≤-trans (n≤1+n n) le) , penᵀ le
    ; loA = λ k le → Pk.loA Pn k (≤-trans (n≤1+n n) le) , gtᵀ (≤-trans (n≤1+n n) le)
    ; hi2 = Pk.hi2 Pn , pen2 n
    }
    where
    Pn : Pk n (proj₂ ob tt)
    Pn = pk n (proj₂ ob tt)
    module S = Step₊ (Pk.D Pn) (Pk.W Pn) (νᵀ (suc n)) (cofSᵀ n) (fsSᵀ n) (gtᵀ {n} {n} ≤-refl)
                     (Pk.loA Pn n ≤-refl) (Pk.hiA Pn (suc n) (n≤1+n n)) (penᵀ {n} {suc n} ≤-refl)

  record Bot (n : ℕ) (ob : OkO Lω (↑ zero (nat (suc n)))) : Set₁ where
    private module DD = Data (Pk.D (pk (suc n) ob))
    field
      τ   : DD.Tg false
      isb : (X : (i : L) → i ≤ J (suc n) → (E.T → Tr i → Set) → E.T → Set)
          → X (DD.lv τ) (DD.pth τ) (DD.Mᵗ τ) (DD.νᵗ τ) → X Lω (lift Lω (↑ zero (nat (suc n)))) Mω ωᵀ

  bot : ∀ n ob → Bot n ob
  bot zero    ob = record { τ = nothing ; isb = λ X x → x }
  bot (suc n) ob = record
    { τ   = just (Bot.τ (bot n (proj₂ ob tt)))
    ; isb = λ X x → Bot.isb (bot n (proj₂ ob tt)) (λ i w Mi μ → X i (inu (λ _ → w)) Mi μ) x
    }
```

## 偏移 n+1 的 Ω 树

```agda
  module R = Red oc

  carN : ∀ n → R.Car (Qη (νᵀ (suc n))) (↑ zero (nat (suc n)))
  carN n ob r B β ok hβ =
    Bot.isb (bot n ob)
      (λ i w Mi μ → (β′ : Tr⁺ i) → Mi (ψᵘ μ []) (proj₁ β′)
                  → Mi (ψᵘ μ (E.Ωt (νᵀ (suc n)))) (proj₁ (ψ (J (suc n)) (oJ (suc n) ob) r B i w β′ (proj₁ (Ωt (J (suc n)))))))
      (λ β′ hβ′ → Top.Ω-fold (Pk.D (pk (suc n) ob)) (Pk.W (pk (suc n) ob)) (Bot.τ (bot n ob)) r B (λ i u → to (ok i u)) β′ hβ′)
      β hβ

  lit⊑ : ∀ {a c : Tr zero} → a ⊴ c → ↑ zero a ⊑ ↑ zero c
  lit⊑ ⊴r     = self
  lit⊑ (⊴◃ d) = ◃→⊑ zero d

  seg : ∀ n {η c} → η ≤ᵀ νᵀ (suc n) → nat (suc n) ⊴ c → R.Car (Qη η) (↑ zero c)
  seg n {c = c} le v = R.Cc (appᵘ ωᵀ [] (Ωt≤ le)) (R.C.mono-path (Qη (νᵀ (suc n))) (lit⊑ v) (noΩ-↑ c) (carN n))

  StepS-seg : ∀ n {η x} → η ≤ᵀ νᵀ (suc n) → nat (suc n) ⊴ suc x → R.Car (Qη η) (↑ zero (suc x))
  StepS-seg n = seg n
```

字面延伸 ω 的孩子: 每个 n+1 都字面在它之下, 所以承载 ψ_ω(Ω_{ω·2}) (`ω2ᵀ` 的基本列第 k 项是 ω+k).

```agda
  car-ω : ∀ c → R.Car (Qη ωᵀ) (↑ zero c)
  car-ω c = R.C.mono-path (Qη ωᵀ) (z⊑ (↑ zero c) (noΩ-↑ c)) (noΩ-↑ c) R.S.car₀

  car-k : ∀ k {c} → ωᶜ ⊴ c → R.Car (Qη (νᵀ k)) (↑ zero c)
  car-k zero    {c} v = car-ω c
  car-k (suc k) {c} v = seg k (inj₂ refl) (⊴-trans (⊴◃ (◃l (suc k))) v)

  ext-ω2 : ∀ {c} → ωᶜ ⊴ c → R.Car (Qη ω2ᵀ) (↑ zero c)
  ext-ω2 {c} v = R.CL refl (λ k → subst (λ z → R.Car (Qη (E.ψ [] (E.𝟏 ∷ []) ∷ z)) (↑ zero c)) (sym (rep1 k)) (car-k k v))
```

## 实际证据下塔第 1 项 Ω 树的各支

```agda
module Bᴬ = Base ocᴬ

branch-car : ∀ {t} (B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → ∀ c → Bᴬ.R.Car t (↑ zero c)
           → Mω t (proj₁ (Fᴬ B β (blk c)))
branch-car {t} B β hβ c car =
  cell nzω (Ok-tw 1) (Mω t) mw c B β zero (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))
    (Bᴬ.R.C.seen-car t Sᶻ (lift zero (↑ zero ωᶜ)) β c car hβ)

branch-seg : ∀ n (B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → ∀ c → nat (suc n) ⊴ c
           → Mω (Qη (νᵀ (suc n))) (proj₁ (Fᴬ B β (blk c)))
branch-seg n B β hβ c v = branch-car B β hβ c (Bᴬ.seg n (inj₂ refl) v)

branch-ω2 : (B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → ∀ c → ωᶜ ⊴ c
          → Mω (Qη ω2ᵀ) (proj₁ (Fᴬ B β (blk c)))
branch-ω2 B β hβ c v = branch-car B β hβ c (Bᴬ.ext-ω2 v)
```
