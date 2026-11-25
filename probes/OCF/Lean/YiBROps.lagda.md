# 新旧块的逐层关系: 运算保持关系

> 编译定理 (验收用, 对一切相关的输入, 无前提): 加法与它的单调 (`+-R`), `next`, 部分和极限, 零的比较与 "非零" (`zl-R`, `zs-R`), 各层的 Ω 树 (`Ωt-R`), 第 0 层的嵌入 (`ι-R`), 孩子树沿路径搬进高层 (`emb-R`), 上折 (`Up-R`); 每条同时给值与推导的关系.
> 不否定什么. 关系的定义在 `YiBRRel`, 槽位与路径的引理在 `YiBRLem`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBROps where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem
```

## 一层之内

```agda
module _ {ℓ : L} {ℓ′ : F.L} where
  mutual
    +-R : {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′ → RelT ℓ ℓ′ y y′ → RelT ℓ ℓ′ (x + y) (x′ F.+ y′)
    +-R {y = zero}       rx iz              = rx
    +-R {y = suc y}      rx (is r)          = is (+-R rx r)
    +-R {y = lim f a}    rx (il (rf , ra))  = il ((λ n → +-R rx (rf n)) , (λ n → +m-R rx (ra n)))
    +-R {y = Ω p g}      rx (iw (rp , rg))  = iw (rp , λ z z′ rz → +-R rx (rg z z′ rz))
    +-R {y = up y c w e} rx (iu (ry , ru))  = iu (+-R rx ry , ru)

    +m-R : {c : Tr ℓ} {c′ : F.Tr ℓ′} {a b : Tr ℓ} {a′ b′ : F.Tr ℓ′} {d : ℓ ⊢ a ◃ b} {d′ : F._⊢_◃_ ℓ′ a′ b′}
         → RelT ℓ ℓ′ c c′ → RelD ℓ ℓ′ d d′ → RelD ℓ ℓ′ (+-mono c d) (F.+-mono c′ d′)
    +m-R {d = ◃s}         rc ds               = ds
    +m-R {d = ◃l n}       rc dl               = dl
    +m-R {d = ◃w}         rc (dw (rp , rg))   = dw (rp , λ z z′ rz → +-R rc (rg z z′ rz))
    +m-R {d = ◃u x k y e} rc (du (rx , ru))   = du (+-R rc rx , ru)
    +m-R {d = ◃c x k r}   rc (dc (rx , rr))   = dc (+-R rc rx , rr)
    +m-R {d = ◃t d e}     rc (dt (r₁ , r₂))   = dt (+m-R rc r₁ , +m-R rc r₂)

  iter-R : {b : Tr ℓ} {b′ : F.Tr ℓ′} → RelT ℓ ℓ′ b b′ → (n : ℕ) → RelT ℓ ℓ′ (iter (b +_) b n) (F.iter (b′ F.+_) b′ n)
  iter-R rb zero    = rb
  iter-R rb (suc n) = +-R rb (iter-R rb n)

  nextA-R : {b : Tr ℓ} {b′ : F.Tr ℓ′} {nb : ℓ ⊢ zero ◃ b} {nb′ : F._⊢_◃_ ℓ′ F.zero b′}
          → RelT ℓ ℓ′ b b′ → RelD ℓ ℓ′ nb nb′ → (n : ℕ) → RelD ℓ ℓ′ (nextA b nb n) (F.nextA b′ nb′ n)
  nextA-R rb rn zero    = +m-R rb rn
  nextA-R rb rn (suc n) = +m-R rb (nextA-R rb rn n)

  -- next⁺ 的值与非零
  next-R : (b : Tr⁺ ℓ) {b′ : F.Tr ℓ′} {nb′ : F._⊢_◃_ ℓ′ F.zero b′}
         → RelT ℓ ℓ′ (proj₁ b) b′ → RelD ℓ ℓ′ (proj₂ b) nb′
         → RelT ℓ ℓ′ (proj₁ (next⁺ b)) (F.next b′ nb′) × RelD ℓ ℓ′ (proj₂ (next⁺ b)) (F.◃t nb′ (F.◃l {f = F.iter (b′ F.+_) b′} {a = F.nextA b′ nb′} zero))
  next-R b rb rn = il (iter-R rb , nextA-R rb rn) , dt (rn , dl)

  cum-R : {G : ℕ → Tr ℓ} {G′ : ℕ → F.Tr ℓ′} → ((n : ℕ) → RelT ℓ ℓ′ (G n) (G′ n)) → (n : ℕ) → RelT ℓ ℓ′ (cum G n) (F.cum G′ n)
  cum-R rG zero    = rG zero
  cum-R rG (suc n) = +-R (cum-R rG n) (rG (suc n))

  limc-R : (G : ℕ → Tr⁺ ℓ) {G′ : ℕ → F.Tr ℓ′} {nz : (n : ℕ) → F._⊢_◃_ ℓ′ F.zero (G′ n)}
         → ((n : ℕ) → RelT ℓ ℓ′ (proj₁ (G n)) (G′ n)) → ((n : ℕ) → RelD ℓ ℓ′ (proj₂ (G n)) (nz n))
         → RelT ℓ ℓ′ (proj₁ (limc⁺ G)) (F.limc G′ nz)
  limc-R G rG rN = il (cum-R rG , λ n → +m-R (cum-R rG n) (rN (suc n)))
```

## 零的比较

F2 的 `zl` 在 ℕ 极限与 Ω 结点处对非变量的第一项作 `with`; 这里用同形的辅助 `Zf` 对变量陈述, 再由 `with` 化到 F2 的子句.

```agda
module _ {S : F.Sg} where
  Zf : (x′ : F.T S) {y′ : F.T S} → F.Lt S x′ y′ → F.Lt S F.zero y′
  Zf x′ {y′} d′ with F.zl x′
  ... | inj₁ e   = subst (λ v → F.Lt S v y′) (sym e) d′
  ... | inj₂ d″  = F.◃t d″ d′

module _ {ℓ : L} {ℓ′ : F.L} where
  data RZl {x : Tr ℓ} {x′ : F.Tr ℓ′} : (zero ≡ x) ⊎ (ℓ ⊢ zero ◃ x) → (F.zero ≡ x′) ⊎ F._⊢_◃_ ℓ′ F.zero x′ → Set where
    z₁ : ∀ {e e′} → RZl (inj₁ e) (inj₁ e′)
    z₂ : ∀ {d d′} → RelD ℓ ℓ′ d d′ → RZl (inj₂ d) (inj₂ d′)

module _ {S : F.Sg} where
  zl-lim≡ : (f′ : ℕ → F.T S) (a′ : (n : ℕ) → F.Lt S (f′ n) (f′ (suc n)))
          → F.zl (F.lim f′ a′) ≡ inj₂ (Zf (f′ zero) (F.◃l zero))
  zl-lim≡ f′ a′ with F.zl (f′ zero)
  ... | inj₁ e = refl
  ... | inj₂ d = refl

  zl-Ω≡ : (p′ : F.P S) (g′ : F.B S p′ → F.T S) → F.zl (F.Ω p′ g′) ≡ inj₂ (Zf (g′ (F.b₀ S p′)) F.◃w)
  zl-Ω≡ p′ g′ with F.zl (g′ (F.b₀ S p′))
  ... | inj₁ e = refl
  ... | inj₂ d = refl

mutual
  zl-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′ → RZl (zl x) (F.zl x′)
  zl-R rl {x = zero} iz = z₁
  zl-R rl {suc x} {F.suc x′} (is r) with zl x | F.zl x′ | zl-R rl r
  ... | inj₁ refl | inj₁ refl | z₁    = z₂ ds
  ... | inj₂ d    | inj₂ d′   | z₂ rd = z₂ (dt (rd , ds))
  zl-R rl {lim f a} {F.lim f′ a′} (il (rf , ra)) =
    subst (RZl (inj₂ (z◃ (f zero) (◃l zero)))) (sym (zl-lim≡ f′ a′)) (z₂ (Zg rl (rf zero) dl))
  zl-R {ℓ} {ℓ′} rl {Ω p g} {F.Ω p′ g′} (iw (rp , rg)) =
    subst (RZl (inj₂ (z◃ (g (fromBr ℓ p zero)) ◃w))) (sym (zl-Ω≡ p′ g′))
      (z₂ (Zg rl (rg _ _ (br0-R rl p p′ rp)) (dw (rp , rg))))
  zl-R rl {up x c y e} {F.up x′ c′ y′ e′} (iu (rx , ru)) with zl x | F.zl x′ | zl-R rl rx
  ... | inj₁ refl | inj₁ refl | z₁    = z₂ (du (iz , ru))
  ... | inj₂ d    | inj₂ d′   | z₂ rd = z₂ (dt (rd , du (rx , ru)))

  Zg : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
     → {y : Tr ℓ} {y′ : F.Tr ℓ′} {d : ℓ ⊢ x ◃ y} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′ → RelD ℓ ℓ′ (z◃ x d) (Zf x′ d′)
  Zg rl {x} {x′} rx {y′ = y′} rd with zl x | F.zl x′ | zl-R rl rx
  ... | inj₁ refl | inj₁ e′  | z₁    = RelD-substʳ (λ v → v) (λ _ → y′) (sym e′) rd
  ... | inj₂ d₀   | inj₂ d₀′ | z₂ r₀ = dt (r₀ , rd)

zs-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′ → RelD ℓ ℓ′ (z◃ x ◃s) (F.z◃s x′)
zs-R rl {x} {x′} rx with zl x | F.zl x′ | zl-R rl rx
... | inj₁ refl | inj₁ refl | z₁    = ds
... | inj₂ d    | inj₂ d′   | z₂ rd = dt (rd , ds)
```

## 各层的 Ω 树, 第 0 层的嵌入

```agda
mutual
  Ωt-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → RelT ℓ ℓ′ (proj₁ (Ωt ℓ)) (F.Ωt ℓ′)
  Ωt-R lz          = is iz
  Ωt-R (lS r)      = iw (i₁ tt , λ z z′ rz → iu (iz , (is rz , zs-R r rz)))
  Ωt-R (lL r)      = il (cumΩ-R (lL r) , λ n → du (cumΩ-R (lL r) n , (refl , Ωt-R (r (suc n)) , Ωn-R (r (suc n)))))
  Ωt-R (lΩ rk rh)  = iw (i₁ (i₁ tt) , λ z z′ rz → iu (iz , (rz , Ωt-R (rh z z′ rz) , Ωn-R (rh z z′ rz))))

  Ωn-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → RelD ℓ ℓ′ (proj₂ (Ωt ℓ)) (F.Ωt-nz ℓ′)
  Ωn-R lz          = ds
  Ωn-R (lS r)      = dt (du (iz , (is iz , zs-R r iz)) , dw (i₁ tt , λ z z′ rz → iu (iz , (is rz , zs-R r rz))))
  Ωn-R (lL r)      = dt (du (iz , (refl , Ωt-R (r zero) , Ωn-R (r zero))) , dl)
  Ωn-R (lΩ rk rh)  = dt (du (iz , (iz , Ωt-R (rh zero F.zero iz) , Ωn-R (rh zero F.zero iz)))
                       , dw (i₁ (i₁ tt) , λ z z′ rz → iu (iz , (rz , Ωt-R (rh z z′ rz) , Ωn-R (rh z z′ rz)))))

  cumΩ-R : ∀ {g g′} → RelL (nd sL g) (F.lim g′) → (n : ℕ)
         → RelT (nd sL g) (F.lim g′) (cum (λ n → proj₁ (upz {s = sL} {h = g} n (Ωt (g n)))) n) (F.cumΩ g′ n)
  cumΩ-R (lL r) zero    = iu (iz , (refl , Ωt-R (r zero) , Ωn-R (r zero)))
  cumΩ-R (lL r) (suc n) = iu (cumΩ-R (lL r) n , (refl , Ωt-R (r (suc n)) , Ωn-R (r (suc n))))

module _ {j : L} {j′ : F.L} where
  mutual
    ι-R : {y : Tr zero} {y′ : F.Tr F.zero} → RelT zero F.zero y y′ → RelT j j′ (ι j y) (F.ι j′ y′)
    ι-R {y = zero} iz             = iz
    ι-R {suc y}   (is r)         = is (ι-R r)
    ι-R {lim f a} (il (rf , ra)) = il ((λ n → ι-R (rf n)) , (λ n → ιm-R (ra n)))

    ιm-R : {a b : Tr zero} {a′ b′ : F.Tr F.zero} {d : zero ⊢ a ◃ b} {d′ : F._⊢_◃_ F.zero a′ b′}
         → RelD zero F.zero d d′ → RelD j j′ (ι-mono j d) (F.ι-mono j′ d′)
    ιm-R {d = ◃s}     ds             = ds
    ιm-R {d = ◃l n}   dl             = dl
    ιm-R {d = ◃t d e} (dt (r₁ , r₂)) = dt (ιm-R r₁ , ιm-R r₂)
```

## 孩子树沿路径搬进高层

```agda
emb-R : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → ∀ {k k′} {v : k ≤ ℓ} {v′ : F._≤_ k′ ℓ′} → RelW v v′
      → (y : Tr⁺ k) {y′ : F.Tr k′} {nz : F._⊢_◃_ k′ F.zero y′} → RelT k k′ (proj₁ y) y′ → RelD k k′ (proj₂ y) nz
      → RelT ℓ ℓ′ (proj₁ (emb ℓ o v y)) (F.emb ℓ′ ε v′ y′ nz) × RelD ℓ ℓ′ (proj₂ (emb ℓ o v y)) (F.emb-nz ℓ′ ε v′ y′ nz)
emb-R re wself y ry rn = ry , rn
emb-R (eS re) (wincS rv) y ry rn = let r = emb-R re rv y ry rn in iu (iz , r) , du (iz , r)
emb-R (eS re) (winuS rv) y ry rn = let r = emb-R re rv y ry rn in iu (iz , r) , du (iz , r)
emb-R (eL rr re) (wincL n rv) y ry rn = let r = emb-R (re n) rv y ry rn in iu (iz , (refl , r)) , du (iz , (refl , r))
emb-R (eL rr re) (winuL rvs) y ry rn =
  let r = emb-R (re zero) (rvs zero) y ry rn in iu (iz , (refl , r)) , du (iz , (refl , r))
emb-R (eΩ rk rwc rc) (wincΩ {c = c} {c′ = c′} rcc rv) y ry rn =
  let r = emb-R ((rc c c′ rcc)) rv y ry rn in iu (iz , (rcc , r)) , du (iz , (rcc , r))
emb-R (eΩ rk rwc rc) (winuΩ rvs) y ry rn =
  let r = emb-R ((rc zero F.zero iz)) (rvs zero F.zero iz) y ry rn in iu (iz , (iz , r)) , du (iz , (iz , r))
emb-R (eΩ rk rwc rc) (wink rv) y ry rn =
  let r = emb-R ((rc zero F.zero iz)) (∙-R rv ((rwc zero F.zero iz))) y ry rn in iu (iz , (iz , r)) , du (iz , (iz , r))

emb-mono-R : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → ∀ {k k′} {v : k ≤ ℓ} {v′ : F._≤_ k′ ℓ′} → RelW v v′
  → {y₁ y₂ : Tr⁺ k} {y₁′ y₂′ : F.Tr k′} {n₁ : F._⊢_◃_ k′ F.zero y₁′} {n₂ : F._⊢_◃_ k′ F.zero y₂′}
  → {d : k ⊢ proj₁ y₁ ◃ proj₁ y₂} {d′ : F._⊢_◃_ k′ y₁′ y₂′} → RelD k k′ d d′
  → RelD ℓ ℓ′ (emb-mono ℓ o v {y₁} {y₂} d) (F.emb-mono ℓ′ ε v′ {n′ = n₁} {n = n₂} d′)
emb-mono-R re wself rd = rd
emb-mono-R (eS re) (wincS rv) rd = dc (iz , emb-mono-R re rv rd)
emb-mono-R (eS re) (winuS rv) rd = dc (iz , emb-mono-R re rv rd)
emb-mono-R (eL rr re) (wincL n rv) rd = dc (iz , (refl , emb-mono-R (re n) rv rd))
emb-mono-R (eL rr re) (winuL rvs) rd = dc (iz , (refl , emb-mono-R (re zero) (rvs zero) rd))
emb-mono-R (eΩ rk rwc rc) (wincΩ {c = c} {c′ = c′} rcc rv) rd = dc (iz , (rcc , emb-mono-R ((rc c c′ rcc)) rv rd))
emb-mono-R (eΩ rk rwc rc) (winuΩ rvs) rd = dc (iz , (iz , emb-mono-R ((rc zero F.zero iz)) (rvs zero F.zero iz) rd))
emb-mono-R (eΩ rk rwc rc) (wink rv) rd =
  dc (iz , (iz , emb-mono-R ((rc zero F.zero iz)) (∙-R rv ((rwc zero F.zero iz))) rd))
```

## 上折

```agda
mutual
  Up-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → ∀ {j j′} → RelL j j′ → {d : Dn ℓ j} {d′ : F.Dn ℓ′ j′} → RelDn d d′
       → (b : Tr⁺ ℓ) {b′ : F.Tr ℓ′} {nb : F._⊢_◃_ ℓ′ F.zero b′} → RelT ℓ ℓ′ (proj₁ b) b′ → RelD ℓ ℓ′ (proj₂ b) nb
       → {y : Tr j} {y′ : F.Tr j′} → RelT j j′ y y′
       → RelT ℓ ℓ′ (proj₁ (Up j d b y)) (F.Up j′ d′ b′ nb y′) × RelD ℓ ℓ′ (proj₂ (Up j d b y)) (F.Up-nz j′ d′ b′ nb y′)
  Up-R rl rj rd b rb rn {y = zero} iz = rb , rn
  Up-R rl rj {d} rd b rb rn {suc y} (is r) =
    let u = Up-R rl rj rd b rb rn r in next-R (Up _ d b y) (proj₁ u) (proj₂ u)
  Up-R rl rj rd b rb rn {lim f a} (il (rf , ra)) =
    il ((λ n → proj₁ (Up-R rl rj rd b rb rn (rf n))) , (λ n → Upm-R rl rj rd b rb rn (ra n)))
    , dt (proj₂ (Up-R rl rj rd b rb rn (rf zero)) , dl)
  Up-R {ℓ} rl rj {d} {d′} rd b rb rn {Ω p g} {F.Ω p′ g′} (iw (rp , rg)) =
    let rm = mv-R rd p p′ rp
        rG = λ z z′ rz → proj₁ (Up-R rl rj rd b rb rn (rg _ _ (mvBr-R rd p p′ rz)))
    in iw (rm , rG)
       , dt (proj₂ (Up-R rl rj rd b rb rn (rg _ _ (mvBr-R rd p p′ (br0-R rl (mv d p) (F.mv d′ p′) rm)))) , dw (rm , rG))
  Up-R rl (lS r) {d} rd b rb rn {up y c y₀ e} (iu (ry , (ry₀ , _))) =
    let u = Up-R rl (lS r) rd b rb rn ry in Up-R rl r (ddown (lS r) rd tt) (Up _ d b y) (proj₁ u) (proj₂ u) ry₀
  Up-R rl (lL r) {d} rd b rb rn {up y n y₀ e} (iu (ry , (refl , ry₀ , _))) =
    let u = Up-R rl (lL r) rd b rb rn ry in Up-R rl (r n) (ddown (lL r) rd refl) (Up _ d b y) (proj₁ u) (proj₂ u) ry₀
  Up-R rl (lΩ rk rh) {d} rd b rb rn {up y c y₀ e} {F.up _ c′ _ _} (iu (ry , (rc , ry₀ , _))) =
    let u = Up-R rl (lΩ rk rh) rd b rb rn ry
    in Up-R rl (rh c c′ rc) (ddown (lΩ rk rh) rd rc) (Up _ d b y) (proj₁ u) (proj₂ u) ry₀

  Upm-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → ∀ {j j′} → RelL j j′ → {d : Dn ℓ j} {d′ : F.Dn ℓ′ j′} → RelDn d d′
        → (b : Tr⁺ ℓ) {b′ : F.Tr ℓ′} {nb : F._⊢_◃_ ℓ′ F.zero b′} → RelT ℓ ℓ′ (proj₁ b) b′ → RelD ℓ ℓ′ (proj₂ b) nb
        → {x y : Tr j} {x′ y′ : F.Tr j′} {e : j ⊢ x ◃ y} {e′ : F._⊢_◃_ j′ x′ y′} → RelD j j′ e e′
        → RelD ℓ ℓ′ (Upm j d b e) (F.Up-mono j′ d′ b′ nb e′)
  Upm-R rl rj rd b rb rn {e = ◃s} ds = dl
  Upm-R rl rj rd b rb rn {e = ◃l n} dl = dl
  Upm-R {ℓ} {ℓ′} rl {j} {j′} rj {d} {d′} rd b {b′} {nb} rb rn {e = ◃w {p = p} {g = g}} {e′ = F.◃w {p = p′} {g = g′}} (dw (rp , rg)) =
    RelD-substˡ (λ t → proj₁ (Up j d b (g t))) (λ _ → proj₁ (Up j d b (Ω p g))) (mvFirst d p)
      (RelD-substʳ (λ t → F.Up j′ d′ b′ nb (g′ t)) (λ _ → F.Up j′ d′ b′ nb (F.Ω p′ g′)) (F.mvFirst d′ p′)
        (dw (mv-R rd p p′ rp , λ z z′ rz → proj₁ (Up-R rl rj rd b rb rn (rg _ _ (mvBr-R rd p p′ rz))))))
  Upm-R rl (lS r) {d} rd b rb rn {e = ◃u x c y e} (du (rx , (ry , re))) =
    let u = Up-R rl (lS r) rd b rb rn rx in Upm-R rl r (ddown (lS r) rd tt) (Up _ d b x) (proj₁ u) (proj₂ u) re
  Upm-R rl (lL r) {d} rd b rb rn {e = ◃u x n y e} (du (rx , (refl , ry , re))) =
    let u = Up-R rl (lL r) rd b rb rn rx in Upm-R rl (r n) (ddown (lL r) rd refl) (Up _ d b x) (proj₁ u) (proj₂ u) re
  Upm-R rl (lΩ rk rh) {d} rd b rb rn {e = ◃u x c y e} {e′ = F.◃u _ c′ _ _} (du (rx , (rc , ry , re))) =
    let u = Up-R rl (lΩ rk rh) rd b rb rn rx
    in Upm-R rl (rh c c′ rc) (ddown (lΩ rk rh) rd rc) (Up _ d b x) (proj₁ u) (proj₂ u) re
  Upm-R rl (lS r) {d} rd b rb rn {e = ◃c x c r₀} (dc (rx , rr)) =
    let u = Up-R rl (lS r) rd b rb rn rx in Upm-R rl r (ddown (lS r) rd tt) (Up _ d b x) (proj₁ u) (proj₂ u) rr
  Upm-R rl (lL r) {d} rd b rb rn {e = ◃c x n r₀} (dc (rx , (refl , rr))) =
    let u = Up-R rl (lL r) rd b rb rn rx in Upm-R rl (r n) (ddown (lL r) rd refl) (Up _ d b x) (proj₁ u) (proj₂ u) rr
  Upm-R rl (lΩ rk rh) {d} rd b rb rn {e = ◃c x c r₀} {e′ = F.◃c _ c′ _} (dc (rx , (rc , rr))) =
    let u = Up-R rl (lΩ rk rh) rd b rb rn rx
    in Upm-R rl (rh c c′ rc) (ddown (lΩ rk rh) rd rc) (Up _ d b x) (proj₁ u) (proj₂ u) rr
  Upm-R rl rj rd b rb rn {e = ◃t e₁ e₂} (dt (r₁ , r₂)) = dt (Upm-R rl rj rd b rb rn r₁ , Upm-R rl rj rd b rb rn r₂)

```
