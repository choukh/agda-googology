# 不单射的孩子编码: 一般层号对, 到 `Tp` 与 `Ωt` 的值单调

> 判决: 条件定理 (排中律, 函数外延作参数). 对一切合法 a 与值不低于它的 b (b 不要求合法), `Tr a` 单射地嵌进 `Tr b` (`IS`); 于是 `PS` 对一切合法值有序层号对成立 (`psAll`), `YiRVOmega.Tp` 成立 (`tpAll`), `Ωt` 对右侧正规的合法层号按值单调 (`ΩtMono`, `ΩtSame`).
> 构造: 对左侧层号按值良基递归 (`Gen`); 孩子与槽位用递归得到的嵌入 (槽位再经排中律取逆成满射), 槽位路径编码进目标层 (`pz`: 孩子路径 ↦ `up (lab c) (χ c) …`, 下标层路径 ↦ `Ω p₀ (常值)`), 一步由 `YiQNEncStep.step` 完成. 第 0 层用 `ι` (`ZeroE`).
> 不否定什么; 不用记号. 条件只在验收层.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQNEncGen where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Induction.WellFounded using (Acc; acc)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (Tr⁺; c₀; z◃; ι; ι-mono; Ωt)
open import OCF.Lean.YiRWPath using (Ok; Ok-at)
import OCF.Lean.YiVWVal as W
open W using (val; _≼_; _≈_)
open import OCF.Lean.YiRVLevel using (LEM; _≼ᴸ_; _≺ᴸ_; _≈ᴸ_; n≼; ≺≼; ≺→≼; ≼ᴸ-refl; Nm)
open import OCF.Lean.YiRVOmega using (Tp; module Mono)
open import OCF.Lean.YiNMSharp using (wfL; path→≼; posLt)
open import OCF.Lean.YiQNReg using (Surj; PS; tpPS; toBr; ft; ok₂; ok₂′; le₂; le₂′; w₁)
open import OCF.Lean.YiRVLevel using (sc)
open import OCF.Lean.YiQNEncBase
open import OCF.Lean.YiQNEncStep
```

## 第 0 层的嵌入 `ι`

```agda
module ZeroE (lem : LEM) (fe : Funext) (b : L) where
  uZ : UIP (Tr zero)
  uZ = lem→uip lem (Tr zero)

  TZ TB : Set
  TZ = TL (Sig zero)
  TB = TL (Sig b)

  ι̂ : ∀ {x y} → zero ⊢ x ◃ y → TB
  ι̂ {x} {y} d = ι b x , ι b y , ι-mono b d

  pS : Tr b → Tr b
  pS (suc x) = x
  pS _       = zero

  pL : ℕ → Tr b → TB
  pL n (lim f a) = f n , f (suc n) , a n
  pL n _         = zero , suc zero , ◃s

  kl : ℕ → Tr zero → TZ
  kl n (lim f a) = f n , lim f a , ◃l n
  kl n _         = zero , suc zero , ◃s

  lN : TB → ℕ
  lN (_ , _ , ◃l n) = n
  lN _              = zero

  tL tR : TB → TB
  tL (x , z , ◃t {y = y} d e) = x , y , d
  tL t                        = t
  tR (x , z , ◃t {y = y} d e) = y , z , e
  tR t                        = t

  tg : TB → ℕ
  tg (_ , _ , ◃s)     = 0
  tg (_ , _ , ◃l _)   = 1
  tg (_ , _ , ◃t _ _) = 2
  tg _                = 3

  mutual
    jT : (x x′ : Tr zero) → ι b x ≡ ι b x′ → x ≡ x′
    jT zero      zero        E = refl
    jT (suc x)   (suc x′)    E = cong suc (jT x x′ (cong pS E))
    jT (lim f a) (lim f′ a′) E =
      let fn = λ n → jT (f n) (f′ n) (cong (λ t → proj₁ (pL n t)) E) in
      limEq uZ fe (fe fn) (λ n → jL (a n) (a′ n) (fn n) (fn (suc n)) (cong (pL n) E))
    jT zero      (suc _)     ()
    jT zero      (lim _ _)   ()
    jT (suc _)   zero        ()
    jT (suc _)   (lim _ _)   ()
    jT (lim _ _) zero        ()
    jT (lim _ _) (suc _)     ()

    jL : ∀ {x y x′ y′} (d : zero ⊢ x ◃ y) (d′ : zero ⊢ x′ ◃ y′) → x ≡ x′ → y ≡ y′ → ι̂ d ≡ ι̂ d′
       → _≡_ {A = TZ} (x , y , d) (x′ , y′ , d′)
    jL d d′ ex ey E = jL′ d d′ ex ey E (cong tg E)

    jL′ : ∀ {x y x′ y′} (d : zero ⊢ x ◃ y) (d′ : zero ⊢ x′ ◃ y′) → x ≡ x′ → y ≡ y′ → ι̂ d ≡ ι̂ d′
        → tg (ι̂ d) ≡ tg (ι̂ d′) → _≡_ {A = TZ} (x , y , d) (x′ , y′ , d′)
    jL′ ◃s             ◃s       ex ey E _ = cong (λ t → t , suc t , ◃s) ex
    jL′ (◃l {f} {a} n) (◃l n′)  ex ey E _ = trans (cong (λ m → kl m (lim f a)) (cong lN E)) (cong (kl n′) ey)
    jL′ (◃t {y = y₁} d₁ e₁) (◃t {y = y₂} d₂ e₂) ex ez E _ =
      let ey = jT y₁ y₂ (cong (λ t → proj₁ (proj₂ (tL t))) E) in
      tEq uZ (jL d₁ d₂ ex ey (cong tL E)) (jL e₁ e₂ ey ez (cong tR E))
    jL′ ◃s       (◃l _)   _ _ _ ()
    jL′ ◃s       (◃t _ _) _ _ _ ()
    jL′ (◃l _)   ◃s       _ _ _ ()
    jL′ (◃l _)   (◃t _ _) _ _ _ ()
    jL′ (◃t _ _) ◃s       _ _ _ ()
    jL′ (◃t _ _) (◃l _)   _ _ _ ()

  ιE : Emb zero b
  ιE = record { σ = ι b ; σm = ι-mono b ; σz = refl ; inj = λ {x} {x′} → jT x x′ ; injL = jL }
```

## 递归的产物与形状相关的部分

`Pack a b`: 嵌入, 连同 a 的路径 (`Pos⁼ a`) 到 `Tr⁺ b` 的单射编码. `Aux`: 孩子标签 (`lab`) 与下标层路径的编码 (`pk`), 只有这两样依赖形状.

```agda
PZ : L → L → Set
PZ a b = Σ (Pos⁼ a → Tr⁺ b) λ f → ∀ {t t′} → proj₁ (f t) ≡ proj₁ (f t′) → t ≡ t′

Pack : L → L → Set
Pack a b = Emb a b × PZ a b

Rec : L → Set
Rec a = ∀ {j} → j ≺ᴸ a → Ok j → ∀ {m} → j ≼ᴸ m → Pack j m

record Aux (s : Sh) (b : L) : Set where
  field
    lab  : Ch s → Tr b
    labi : ∀ {c d} → lab c ≡ lab d → c ≡ d
    pk   : PK s → Tr b
    pki  : ∀ {t t′} → pk t ≡ pk t′ → t ≡ t′

kLt : ∀ {k h} → Ok (nd (sΩ k) h) → k ≺ᴸ nd (sΩ k) h
kLt {k} {h} oa = zero , path→≼ (h zero) (proj₂ oa zero) (proj₂ (proj₁ oa) zero)

aux : (s : Sh) (h : Ch s → L) {b : L} → Ok (nd s h) → nd s h ≼ᴸ b → Rec (nd s h) → Aux s b
aux sS     h oa le rc = record { lab = λ _ → zero ; labi = λ _ → refl ; pk = λ () ; pki = λ { {()} } }
aux sL     h oa le rc = record { lab = natT ; labi = natT-inj ; pk = λ () ; pki = λ { {()} } }
aux (sΩ k) h {b} oa le rc =
  let P = rc (kLt oa) (proj₁ (proj₁ oa)) (≺→≼ b (≺≼ (nd (sΩ k) h) b (kLt oa) le)) in
  record { lab = σ (proj₁ P) ; labi = inj (proj₁ P)
         ; pk = λ t → proj₁ (proj₁ (proj₂ P) t) ; pki = proj₂ (proj₂ P) }
```

## 路径编码

```agda
module PathEnc (lem : LEM) {s : Sh} {h : Ch s → L} {s′ : Sh} {h′ : Ch s′ → L}
               (χ : Ch s → Ch s′) (A : Aux s (nd s′ h′)) (pc : (c : Ch s) → PZ (h c) (h′ (χ c))) where
  open Aux A
  Ꞵ′ : L
  Ꞵ′ = nd s′ h′

  p₀ : Pos Ꞵ′
  p₀ = inj₂ (c₀ s′ , inj₁ tt)

  pzf : Pos⁼ (nd s h) → Tr⁺ Ꞵ′
  pzf (inj₁ tt)              = suc zero , ◃s
  pzf (inj₂ (inj₂ (c , t)))  = let Y = proj₁ (pc c) t in
    up (lab c) (χ c) (proj₁ Y) (proj₂ Y) , z◃ (lab c) (◃u (lab c) (χ c) (proj₁ Y) (proj₂ Y))
  pzf (inj₂ (inj₁ t))        = Ω p₀ (λ _ → pk t) , z◃ (pk t) ◃w

  upA : Tr Ꞵ′ → Tr Ꞵ′
  upA (up x _ _ _) = x
  upA _            = zero

  upT : Tr Ꞵ′ → Σ (Ch s′) λ c → Tr⁺ (h′ c)
  upT (up _ c y e) = c , y , e
  upT _            = c₀ s′ , suc zero , ◃s

  ΩG : Tr Ꞵ′ → Σ (Pos Ꞵ′) λ q → Br Ꞵ′ q → Tr Ꞵ′
  ΩG (Ω q G) = q , G
  ΩG _       = p₀ , λ _ → zero

  upJ : ∀ {c c′ t t′} → c ≡ c′ → up (lab c) (χ c) (proj₁ (proj₁ (pc c) t)) (proj₂ (proj₁ (pc c) t))
                                 ≡ up (lab c′) (χ c′) (proj₁ (proj₁ (pc c′) t′)) (proj₂ (proj₁ (pc c′) t′))
      → _≡_ {A = Pos⁼ (nd s h)} (inj₂ (inj₂ (c , t))) (inj₂ (inj₂ (c′ , t′)))
  upJ {c} {t = t} {t′} refl E =
    cong (λ u → inj₂ (inj₂ (c , u)))
      (proj₂ (pc c) (cong proj₁ (fib (λ k → Tr⁺ (h′ k)) (lem→uip lem (Ch s′)) (cong upT E))))

  pzi : ∀ {t t′} → proj₁ (pzf t) ≡ proj₁ (pzf t′) → t ≡ t′
  pzi {inj₁ tt}             {inj₁ tt}               E = refl
  pzi {inj₂ (inj₂ (c , t))} {inj₂ (inj₂ (c′ , t′))} E = upJ (labi (cong upA E)) E
  pzi {inj₂ (inj₁ t)}       {inj₂ (inj₁ t′)}        E =
    cong (λ u → inj₂ (inj₁ u))
      (pki (cong (λ k → k zero) (fib (λ q → Br Ꞵ′ q → Tr Ꞵ′) (lem→uip lem (Pos Ꞵ′)) {p₀} {λ _ → pk t} {λ _ → pk t′} (cong ΩG E))))
  pzi {inj₁ tt}             {inj₂ (inj₂ _)}         ()
  pzi {inj₁ tt}             {inj₂ (inj₁ _)}         ()
  pzi {inj₂ (inj₂ _)}       {inj₁ tt}               ()
  pzi {inj₂ (inj₂ _)}       {inj₂ (inj₁ _)}         ()
  pzi {inj₂ (inj₁ _)}       {inj₁ tt}               ()
  pzi {inj₂ (inj₁ _)}       {inj₂ (inj₂ _)}         ()
```

## 按值良基的递归

```agda
module G (lem : LEM) (fe : Funext) where
  unPos : ∀ {a} {p q : Pos a} → _≡_ {A = Pos⁼ a} (inj₂ p) (inj₂ q) → p ≡ q
  unPos {p = p} e = cong (λ { (inj₂ x) → x ; (inj₁ _) → p }) e

  Gen : (a : L) → Acc _≺ᴸ_ a → ∀ {b} → Ok a → a ≼ᴸ b → Pack a b
  Gen zero     _       {b}         oa le     = ZeroE.ιE lem fe b , (λ { (inj₁ tt) → suc zero , ◃s }) , λ { {inj₁ tt} {inj₁ tt} _ → refl }
  Gen (nd s h) _       {b = zero} oa (n≼ f) = ⊥-elim (f (c₀ s))
  Gen (nd s h) (acc r) {b = nd s′ h′} oa (n≼ f) = Step.step lem fe Dt , PathEnc.pzf lem χ A pc , PathEnc.pzi lem χ A pc
    where
    a b : L
    a = nd s h
    b = nd s′ h′
    rc : Rec a
    rc lt oj le = Gen _ (r lt) oj le
    χ : Ch s → Ch s′
    χ c = proj₁ (f c)
    PC : (c : Ch s) → Pack (h c) (h′ (χ c))
    PC c = rc (c , ≼ᴸ-refl (h c)) (proj₂ oa c) (proj₂ (f c))
    pc : (c : Ch s) → PZ (h c) (h′ (χ c))
    pc c = proj₂ (PC c)
    A : Aux s b
    A = aux s h oa (n≼ f) rc
    sl′ : (p : Pos a) → Σ (Ch s′) λ c′ → at a p ≼ᴸ h′ c′
    sl′ p = ≺≼ a b (posLt a oa p) (n≼ f)
    Ep : (p : Pos a) → Emb (at a p) (h′ (proj₁ (sl′ p)))
    Ep p = proj₁ (rc (posLt a oa p) (Ok-at a oa p) (proj₂ (sl′ p)))
    SJ : (p : Pos a) → Surj (Tr (h′ (proj₁ (sl′ p)))) (Tr (at a p))
    SJ p = inj→surj lem zero (σ (Ep p) , inj (Ep p))
    π′ : Pos a → Pos b
    π′ p = inj₂ (proj₁ (sl′ p) , inj₁ tt)
    ρ′ : (p : Pos a) → Br b (π′ p) → Br a p
    ρ′ p w = fromBr a p (proj₁ (SJ p) w)
    ρs′ : (p : Pos a) (z : Br a p) → Σ (Br b (π′ p)) λ w → ρ′ p w ≡ z
    ρs′ p z = let u = proj₂ (SJ p) (toBr a p z) in
      proj₁ u , trans (cong (fromBr a p) (proj₂ u)) (ft a p z)
    ρb′ : (p : Pos a) → ρ′ p zero ≡ fromBr a p zero
    ρb′ p = cong (fromBr a p)
      (trans (cong (proj₁ (SJ p)) (sym (σz (Ep p)))) (proj₂ (proj₂ (SJ p) zero)))
    Dt : StepData s h s′ h′
    Dt = record
      { χ = χ ; emb = λ c → proj₁ (PC c)
      ; π = π′ ; ρ = ρ′ ; ρs = ρs′ ; ρb = ρb′
      ; tagP = λ p → proj₁ (PathEnc.pzf lem χ A pc (inj₂ p))
      ; tagPi = λ e → unPos (PathEnc.pzi lem χ A pc e)
      ; tagC = Aux.lab A ; tagCi = Aux.labi A }

  IS : ∀ {a b} → Ok a → a ≼ᴸ b → Emb a b
  IS {a} oa le = proj₁ (Gen a (wfL a) oa le)
```

## 接口: `PS`, `Tp`, `Ωt` 的值单调

```agda
  psAll : ∀ {a a′} → Ok a → Ok a′ → a ≼ᴸ a′ → PS a a′
  psAll {a = zero}   oa oa′ le ()
  psAll {a = nd s h} {a′ = zero}     oa oa′ (n≼ f) p = ⊥-elim (f (c₀ s))
  psAll {a = nd s h} {a′ = nd s′ h′} oa oa′ le     p =
    let c′ = ≺≼ (nd s h) (nd s′ h′) (posLt (nd s h) oa p) le
        E  = IS (Ok-at (nd s h) oa p) (proj₂ c′) in
    inj₂ (proj₁ c′ , inj₁ tt) , inj→surj lem zero (σ E , inj E)

  tpAll : Tp
  tpAll = tpPS psAll

  ΩtMono : (ℓ ℓ′ : L) → Ok ℓ → Ok ℓ′ → Nm ℓ′ → ℓ ≼ᴸ ℓ′ → val ℓ (proj₁ (Ωt ℓ)) ≼ val ℓ′ (proj₁ (Ωt ℓ′))
  ΩtMono = Mono.M lem tpAll

  ΩtSame : (ℓ ℓ′ : L) → Ok ℓ → Ok ℓ′ → Nm ℓ → Nm ℓ′ → ℓ ≈ᴸ ℓ′ → val ℓ (proj₁ (Ωt ℓ)) ≈ val ℓ′ (proj₁ (Ωt ℓ′))
  ΩtSame = Mono.M≈ lem tpAll
```

例: `YiQNReg` 里的合法同值对 `sc (sc zero)`, `sc w₁` (没有同层号槽位) 的 `Ωt` 同值.

```agda
  ex₂ : val (sc (sc zero)) (proj₁ (Ωt (sc (sc zero)))) ≈ val (sc w₁) (proj₁ (Ωt (sc w₁)))
  ex₂ = ΩtSame (sc (sc zero)) (sc w₁) ok₂ ok₂′ tt tt (le₂ , le₂′)
```
