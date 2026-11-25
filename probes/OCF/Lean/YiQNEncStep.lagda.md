# 不单射的孩子编码: 一步嵌入

> 判决: 条件定理 (排中律, 函数外延作参数). 给定一步数据 `StepData` (孩子映射 χ 与孩子嵌入, 槽位映射 π 与分支的满射 ρ, 槽位与孩子在目标层的单射标签), 造出嵌入 `Emb (nd s h) (nd s′ h′)` (`step`).
> 编码: 标签与原像用目标层的 Ω 对 `⟪X , Y⟫ = Ω p₀ (0 ↦ X, 其余 ↦ Y)` 拼在一起: Ω 结点 ↦ `⟪Ω (π p) (σ ∘ g ∘ ρ) , tagP p⟫`, 嵌入 ↦ `up ⟪σ x , tagC c⟫ (χ c) (σ_c y)`. 单射性逐构造子证, 相邻证明在全空间 `TL` 上比较.
> 不否定什么. 实例在 `YiQNEncPair`, 一般层号对在 `YiQNEncGen`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQNEncStep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (Tr⁺; c₀)
open import OCF.Lean.YiRVLevel using (LEM)
open import OCF.Lean.YiQNEncBase
```

## 一步数据

```agda
record StepData (s : Sh) (h : Ch s → L) (s′ : Sh) (h′ : Ch s′ → L) : Set where
  field
    χ     : Ch s → Ch s′
    emb   : (c : Ch s) → Emb (h c) (h′ (χ c))
    π     : Pos (nd s h) → Pos (nd s′ h′)
    ρ     : (p : Pos (nd s h)) → Br (nd s′ h′) (π p) → Br (nd s h) p
    ρs    : (p : Pos (nd s h)) (z : Br (nd s h) p) → Σ (Br (nd s′ h′) (π p)) λ w → ρ p w ≡ z
    ρb    : (p : Pos (nd s h)) → ρ p (b₀ (Sig (nd s′ h′)) (π p)) ≡ b₀ (Sig (nd s h)) p
    tagP  : Pos (nd s h) → Tr (nd s′ h′)
    tagPi : ∀ {p q} → tagP p ≡ tagP q → p ≡ q
    tagC  : Ch s → Tr (nd s′ h′)
    tagCi : ∀ {c d} → tagC c ≡ tagC d → c ≡ d
```

## 映射

```agda
module Step (lem : LEM) (fe : Funext) {s : Sh} {h : Ch s → L} {s′ : Sh} {h′ : Ch s′ → L}
            (D : StepData s h s′ h′) where
  open StepData D

  Ꞵ Ꞵ′ : L
  Ꞵ  = nd s h
  Ꞵ′ = nd s′ h′

  p₀ : Pos Ꞵ′
  p₀ = inj₂ (c₀ s′ , inj₁ tt)

  pr : Tr Ꞵ′ → Tr Ꞵ′ → Br Ꞵ′ p₀ → Tr Ꞵ′
  pr X Y zero = X
  pr X Y _    = Y

  ⟪_,_⟫ : Tr Ꞵ′ → Tr Ꞵ′ → Tr Ꞵ′
  ⟪ X , Y ⟫ = Ω p₀ (pr X Y)

  ez : (c : Ch s) {y : Tr (h c)} → h c ⊢ zero ◃ y → h′ (χ c) ⊢ zero ◃ σ (emb c) y
  ez c {y} e = proj₂ (σ⁺ (emb c) (y , e))

  mutual
    σB : Tr Ꞵ → Tr Ꞵ′
    σB zero         = zero
    σB (suc x)      = suc (σB x)
    σB (lim f a)    = lim (λ n → σB (f n)) (λ n → σmB (a n))
    σB (Ω p g)      = ⟪ Ω (π p) (λ w → σB (g (ρ p w))) , tagP p ⟫
    σB (up x c y e) = up ⟪ σB x , tagC c ⟫ (χ c) (σ (emb c) y) (ez c e)

    σmB : ∀ {x y} → Ꞵ ⊢ x ◃ y → Ꞵ′ ⊢ σB x ◃ σB y
    σmB ◃s           = ◃s
    σmB (◃l n)       = ◃l n
    σmB (◃w {p} {g}) = ◃t (subst (λ t → Ꞵ′ ⊢ σB (g t) ◃ Ω (π p) (λ w → σB (g (ρ p w)))) (ρb p) ◃w) ◃w
    σmB (◃u x c y e) = ◃t ◃w (◃u _ (χ c) _ (ez c e))
    σmB (◃c x c d)   = ◃c _ (χ c) (σm (emb c) d)
    σmB (◃t d e)     = ◃t (σmB d) (σmB e)
```

## 投影与标签

```agda
  uB : UIP (Tr Ꞵ)
  uB = lem→uip lem (Tr Ꞵ)
  uCh : UIP (Ch s)
  uCh = lem→uip lem (Ch s)
  uCh′ : UIP (Ch s′)
  uCh′ = lem→uip lem (Ch s′)
  uP′ : UIP (Pos Ꞵ′)
  uP′ = lem→uip lem (Pos Ꞵ′)

  TB TB′ : Set
  TB  = TL (Sig Ꞵ)
  TB′ = TL (Sig Ꞵ′)

  σ̂ : ∀ {x y} → Ꞵ ⊢ x ◃ y → TB′
  σ̂ {x} {y} d = σB x , σB y , σmB d

  pS : Tr Ꞵ′ → Tr Ꞵ′
  pS (suc x) = x
  pS _       = zero

  pL : ℕ → Tr Ꞵ′ → TB′
  pL n (lim f a) = f n , f (suc n) , a n
  pL n _         = zero , suc zero , ◃s

  upA : Tr Ꞵ′ → Tr Ꞵ′
  upA (up x _ _ _) = x
  upA _            = zero

  upT : Tr Ꞵ′ → Σ (Ch s′) λ c → Tr⁺ (h′ c)
  upT (up _ c y e) = c , y , e
  upT _            = c₀ s′ , suc zero , ◃s

  ΩG : Tr Ꞵ′ → Σ (Pos Ꞵ′) λ q → Br Ꞵ′ q → Tr Ꞵ′
  ΩG (Ω q G) = q , G
  ΩG _       = p₀ , λ _ → zero

  upXC : Tr Ꞵ → Tr Ꞵ × Ch s
  upXC (up x c _ _) = x , c
  upXC _            = zero , c₀ s

  upYE : Tr Ꞵ → Σ (Ch s) λ c → Tr⁺ (h c)
  upYE (up _ c y e) = c , y , e
  upYE _            = c₀ s , suc zero , ◃s

  kl : ℕ → Tr Ꞵ → TB
  kl n (lim f a) = f n , lim f a , ◃l n
  kl n _         = zero , suc zero , ◃s

  kw : Tr Ꞵ → TB
  kw (Ω p g) = g (b₀ (Sig Ꞵ) p) , Ω p g , ◃w
  kw _       = zero , suc zero , ◃s

  ku : Tr Ꞵ → TB
  ku (up x c y e) = x , up x c y e , ◃u x c y e
  ku _            = zero , suc zero , ◃s

  tL tR : TB′ → TB′
  tL (x , z , ◃t {y = y} d e) = x , y , d
  tL t                        = t
  tR (x , z , ◃t {y = y} d e) = y , z , e
  tR t                        = t

  lN : TB′ → ℕ
  lN (_ , _ , ◃l n) = n
  lN _              = zero

  cP : TB′ → Σ (Ch s′) λ k → TL (Sig (h′ k))
  cP (_ , _ , ◃c _ k {y′} {y} r) = k , y′ , y , r
  cP _                           = c₀ s′ , zero , suc zero , ◃s

  tag : TB′ → ℕ
  tag (_ , _ , ◃s)                = 0
  tag (_ , _ , ◃l _)              = 1
  tag (_ , _ , ◃c _ _ _)          = 4
  tag (_ , _ , ◃t _ ◃w)           = 2
  tag (_ , _ , ◃t _ (◃u _ _ _ _)) = 3
  tag (_ , _ , ◃t _ _)            = 5
  tag (_ , _ , ◃w)                = 6
  tag (_ , _ , ◃u _ _ _ _)        = 7

  code : ∀ {x y} → Ꞵ ⊢ x ◃ y → ℕ
  code ◃s           = 0
  code (◃l _)       = 1
  code ◃w           = 2
  code (◃u _ _ _ _) = 3
  code (◃c _ _ _)   = 4
  code (◃t _ _)     = 5

  tag5 : ∀ {x y z} (d : Ꞵ ⊢ x ◃ y) (e : Ꞵ ⊢ y ◃ z) → tag (σB x , σB z , ◃t (σmB d) (σmB e)) ≡ 5
  tag5 d ◃s           = refl
  tag5 d (◃l _)       = refl
  tag5 d ◃w           = refl
  tag5 d (◃u _ _ _ _) = refl
  tag5 d (◃c _ _ _)   = refl
  tag5 d (◃t _ _)     = refl

  tagσ : ∀ {x y} (d : Ꞵ ⊢ x ◃ y) → tag (σ̂ d) ≡ code d
  tagσ ◃s           = refl
  tagσ (◃l _)       = refl
  tagσ ◃w           = refl
  tagσ (◃u _ _ _ _) = refl
  tagσ (◃c _ _ _)   = refl
  tagσ (◃t d e)     = tag5 d e
```

## 单射性: Ω 对与各构造子的 J 引理

```agda
  prEq : ∀ {X Y X′ Y′} → ⟪ X , Y ⟫ ≡ ⟪ X′ , Y′ ⟫ → (X ≡ X′) × (Y ≡ Y′)
  prEq {X} {Y} {X′} {Y′} E = let P = fib (λ q → Br Ꞵ′ q → Tr Ꞵ′) uP′ {p₀} {pr X Y} {pr X′ Y′} (cong ΩG E) in
    cong (λ k → k zero) P , cong (λ k → k (suc zero)) P

  ΩJ : {p p₂ : Pos Ꞵ} {g : Br Ꞵ p → Tr Ꞵ} {g₂ : Br Ꞵ p₂ → Tr Ꞵ} → p ≡ p₂
     → Ω (π p) (λ w → σB (g (ρ p w))) ≡ Ω (π p₂) (λ w → σB (g₂ (ρ p₂ w)))
     → ((z : Br Ꞵ p) (x′ : Tr Ꞵ) → σB (g z) ≡ σB x′ → g z ≡ x′) → Ω p g ≡ Ω p₂ g₂
  ΩJ {p} {g = g} {g₂} refl E rec = cong (Ω p) (fe (λ z → pt z (ρs p z)))
    where
    GG : (λ w → σB (g (ρ p w))) ≡ (λ w → σB (g₂ (ρ p w)))
    GG = fib (λ q → Br Ꞵ′ q → Tr Ꞵ′) uP′ (cong ΩG E)
    pt : (z : Br Ꞵ p) → Σ (Br Ꞵ′ (π p)) (λ w → ρ p w ≡ z) → g z ≡ g₂ z
    pt z (w , r) = subst (λ t → g t ≡ g₂ t) r (rec (ρ p w) (g₂ (ρ p w)) (cong (λ k → k w) GG))

  upJ : {x x₂ : Tr Ꞵ} {c c₂ : Ch s} {y : Tr (h c)} {e : h c ⊢ zero ◃ y} {y₂ : Tr (h c₂)} {e₂ : h c₂ ⊢ zero ◃ y₂}
      → x ≡ x₂ → c ≡ c₂ → σB (up x c y e) ≡ σB (up x₂ c₂ y₂ e₂) → up x c y e ≡ up x₂ c₂ y₂ e₂
  upJ {x} {c = c} refl refl E =
    cong (λ t → up x c (proj₁ t) (proj₂ t))
      (inj⁺ (lem→uip lem (Tr (h c))) (emb c) (fib (λ k → Tr⁺ (h′ k)) uCh′ (cong upT E)))

  cJ2 : ∀ {x c y₁ y₂ e₁ e₂ y₁′ y₂′ e₁′ e₂′} {r : h c ⊢ y₁ ◃ y₂} {r′ : h c ⊢ y₁′ ◃ y₂′}
      → _≡_ {A = Tr⁺ (h c)} (y₁ , e₁) (y₁′ , e₁′) → _≡_ {A = Tr⁺ (h c)} (y₂ , e₂) (y₂′ , e₂′)
      → σ̂ (◃c x c {e′ = e₁} {e = e₂} r) ≡ σ̂ (◃c x c {e′ = e₁′} {e = e₂′} r′)
      → _≡_ {A = TB} (up x c y₁ e₁ , up x c y₂ e₂ , ◃c x c r) (up x c y₁′ e₁′ , up x c y₂′ e₂′ , ◃c x c r′)
  cJ2 {x} {c} {y₁} {y₂} {e₁} {e₂} {r = r} {r′} refl refl E =
    cong (λ t → up x c y₁ e₁ , up x c y₂ e₂ , ◃c x c t)
      (fix2 (lem→uip lem (Tr (h c))) (injL (emb c) r r′ refl refl (fib (λ k → TL (Sig (h′ k))) uCh′ (cong cP E))))

  cJ1 : ∀ {x c y₁ y₂ e₁ e₂ x′ c′ y₁′ y₂′ e₁′ e₂′} {r : h c ⊢ y₁ ◃ y₂} {r′ : h c′ ⊢ y₁′ ◃ y₂′}
      → _≡_ {A = Tr Ꞵ × Ch s} (x , c) (x′ , c′)
      → up x c y₁ e₁ ≡ up x′ c′ y₁′ e₁′ → up x c y₂ e₂ ≡ up x′ c′ y₂′ e₂′
      → σ̂ (◃c x c {e′ = e₁} {e = e₂} r) ≡ σ̂ (◃c x′ c′ {e′ = e₁′} {e = e₂′} r′)
      → _≡_ {A = TB} (up x c y₁ e₁ , up x c y₂ e₂ , ◃c x c r) (up x′ c′ y₁′ e₁′ , up x′ c′ y₂′ e₂′ , ◃c x′ c′ r′)
  cJ1 refl ex ey E = cJ2 (fib (λ k → Tr⁺ (h k)) uCh (cong upYE ex)) (fib (λ k → Tr⁺ (h k)) uCh (cong upYE ey)) E
```

## 单射性

ℕ 极限只对序列项递归 (`f n` 是结构子项), 相邻证明的比较用调用者给出的两端相等; 合成 `◃t` 的中间端是非强制的构造子参数, 可以递归.

```agda
  mutual
    jT : (x x′ : Tr Ꞵ) → σB x ≡ σB x′ → x ≡ x′
    jT zero          zero             E = refl
    jT (suc x)       (suc x′)         E = cong suc (jT x x′ (cong pS E))
    jT (lim f a)     (lim f′ a′)      E =
      let fn = λ n → jT (f n) (f′ n) (cong (λ t → proj₁ (pL n t)) E) in
      limEq uB fe (fe fn) (λ n → jL (a n) (a′ n) (fn n) (fn (suc n)) (cong (pL n) E))
    jT (Ω p g)       (Ω p₂ g₂)        E =
      let PQ = prEq E in ΩJ (tagPi (proj₂ PQ)) (proj₁ PQ) (λ z x′ → jT (g z) x′)
    jT (up x c y e)  (up x₂ c₂ y₂ e₂) E =
      let PQ = prEq (cong upA E) in upJ (jT x x₂ (proj₁ PQ)) (tagCi (proj₂ PQ)) E
    jT zero          (suc _)       ()
    jT zero          (lim _ _)     ()
    jT zero          (Ω _ _)       ()
    jT zero          (up _ _ _ _)  ()
    jT (suc _)       zero          ()
    jT (suc _)       (lim _ _)     ()
    jT (suc _)       (Ω _ _)       ()
    jT (suc _)       (up _ _ _ _)  ()
    jT (lim _ _)     zero          ()
    jT (lim _ _)     (suc _)       ()
    jT (lim _ _)     (Ω _ _)       ()
    jT (lim _ _)     (up _ _ _ _)  ()
    jT (Ω _ _)       zero          ()
    jT (Ω _ _)       (suc _)       ()
    jT (Ω _ _)       (lim _ _)     ()
    jT (Ω _ _)       (up _ _ _ _)  ()
    jT (up _ _ _ _)  zero          ()
    jT (up _ _ _ _)  (suc _)       ()
    jT (up _ _ _ _)  (lim _ _)     ()
    jT (up _ _ _ _)  (Ω _ _)       ()

    jL : ∀ {x y x′ y′} (d : Ꞵ ⊢ x ◃ y) (d′ : Ꞵ ⊢ x′ ◃ y′) → x ≡ x′ → y ≡ y′ → σ̂ d ≡ σ̂ d′
         → _≡_ {A = TB} (x , y , d) (x′ , y′ , d′)
    jL d d′ ex ey E = jL′ d d′ ex ey E (trans (sym (tagσ d)) (trans (cong tag E) (tagσ d′)))

    jL′ : ∀ {x y x′ y′} (d : Ꞵ ⊢ x ◃ y) (d′ : Ꞵ ⊢ x′ ◃ y′) → x ≡ x′ → y ≡ y′ → σ̂ d ≡ σ̂ d′ → code d ≡ code d′
          → _≡_ {A = TB} (x , y , d) (x′ , y′ , d′)
    jL′ ◃s                  ◃s                  ex ey E _ = cong (λ t → t , suc t , ◃s) ex
    jL′ (◃l {f} {a} n)      (◃l n′)             ex ey E _ = trans (cong (λ m → kl m (lim f a)) (cong lN E)) (cong (kl n′) ey)
    jL′ ◃w                  ◃w                  ex ey E _ = cong kw ey
    jL′ (◃u _ _ _ _)        (◃u _ _ _ _)        ex ey E _ = cong ku ey
    jL′ (◃c x c r)          (◃c x′ c′ r′)       ex ey E _ = cJ1 (cong upXC ex) ex ey E
    jL′ (◃t {y = y₁} d₁ e₁) (◃t {y = y₂} d₂ e₂) ex ez E _ =
      let ey = jT y₁ y₂ (cong (λ t → proj₁ (proj₂ (tL t))) E) in
      tEq uB (jL d₁ d₂ ex ey (cong tL E)) (jL e₁ e₂ ey ez (cong tR E))
    jL′ ◃s            (◃l _)        _ _ _ ()
    jL′ ◃s            ◃w            _ _ _ ()
    jL′ ◃s            (◃u _ _ _ _)  _ _ _ ()
    jL′ ◃s            (◃c _ _ _)    _ _ _ ()
    jL′ ◃s            (◃t _ _)      _ _ _ ()
    jL′ (◃l _)        ◃s            _ _ _ ()
    jL′ (◃l _)        ◃w            _ _ _ ()
    jL′ (◃l _)        (◃u _ _ _ _)  _ _ _ ()
    jL′ (◃l _)        (◃c _ _ _)    _ _ _ ()
    jL′ (◃l _)        (◃t _ _)      _ _ _ ()
    jL′ ◃w            ◃s            _ _ _ ()
    jL′ ◃w            (◃l _)        _ _ _ ()
    jL′ ◃w            (◃u _ _ _ _)  _ _ _ ()
    jL′ ◃w            (◃c _ _ _)    _ _ _ ()
    jL′ ◃w            (◃t _ _)      _ _ _ ()
    jL′ (◃u _ _ _ _)  ◃s            _ _ _ ()
    jL′ (◃u _ _ _ _)  (◃l _)        _ _ _ ()
    jL′ (◃u _ _ _ _)  ◃w            _ _ _ ()
    jL′ (◃u _ _ _ _)  (◃c _ _ _)    _ _ _ ()
    jL′ (◃u _ _ _ _)  (◃t _ _)      _ _ _ ()
    jL′ (◃c _ _ _)    ◃s            _ _ _ ()
    jL′ (◃c _ _ _)    (◃l _)        _ _ _ ()
    jL′ (◃c _ _ _)    ◃w            _ _ _ ()
    jL′ (◃c _ _ _)    (◃u _ _ _ _)  _ _ _ ()
    jL′ (◃c _ _ _)    (◃t _ _)      _ _ _ ()
    jL′ (◃t _ _)      ◃s            _ _ _ ()
    jL′ (◃t _ _)      (◃l _)        _ _ _ ()
    jL′ (◃t _ _)      ◃w            _ _ _ ()
    jL′ (◃t _ _)      (◃u _ _ _ _)  _ _ _ ()
    jL′ (◃t _ _)      (◃c _ _ _)    _ _ _ ()

  step : Emb Ꞵ Ꞵ′
  step = record { σ = σB ; σm = σmB ; σz = refl ; inj = λ {x} {x′} → jT x x′ ; injL = jL }
```
