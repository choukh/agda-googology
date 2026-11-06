# EboLeanTrian

> **记号侧验收工作**, 读记号, 不进成品. 逐字取自 [WfFsnTrian](WfFsnTrian.lagda.md) (Buchholz 3.4 `Gtri`, 3.5, 3.6 的 Ω 部分 `TΩ`, γ-链的界, 规则 6 的 `T-case4`), 只把导入换成 EboLean 各段; 结论与证明见原文. `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLeanTrian where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.EboLeanDef
open import OCF.Align.EBO using (pred-suc; <-sucT)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanView

Cov : T → T → T → Set              -- x ≼ G_u(c)
Cov u c x = Σ T λ y → InG u y c × (x ≤ᵀ y)

Dom : T → T → T → T → Set          -- x ≼ G_u(c) ∪ {0} ∪ G_u(z)
Dom u z c x = Cov u c x ⊎ (x ≡ []) ⊎ Cov u z x

record Trian (z b a : T) : Set where
  constructor mkT
  field
    t< : b <ᵀ a
    tb : ∀ u c → b <ᵀ c → c ≤ᵀ a → ∀ {x} → InG u x b → Dom u z c x
open Trian public

cov-lift : ∀ {u c₀ c x} → (∀ {y} → InG u y c₀ → InG u y c) → Cov u c₀ x → Cov u c x
cov-lift f (y , i , l) = y , f i , l

dom-lift : ∀ {u z c₀ c x} → (∀ {y} → InG u y c₀ → InG u y c) → Dom u z c₀ x → Dom u z c x
dom-lift f (inj₁ cv) = inj₁ (cov-lift f cv)
dom-lift f (inj₂ d)  = inj₂ d

pos : ∀ {b a} → b <ᵀ a → [] <ᵀ a
pos {a = _ ∷ _} _ = []<

posG : ∀ {u x b} → InG u x b → [] <ᵀ b
posG {b = _ ∷ _} _ = []<

irrᵀ : ∀ {u u′} → u ≡ u′ → u <ᵀ u′ → ⊥
irrᵀ refl p = <ᵀ-irrefl p

irrᴾ : ∀ {x x′} → x ≡ x′ → x <ᴾ x′ → ⊥
irrᴾ refl p = <ᴾ-irrefl p

-- 头部写成两个变量加一个等式: 否则 --without-K 下 tl< 的匹配要消去自反等式
cons-btw′ : ∀ {x x′ b₀ b c} → x ≡ x′ → (x ∷ b₀) <ᵀ c → c ≤ᵀ (x′ ∷ b) →
            Σ T λ c₀ → (c ≡ x ∷ c₀) × (b₀ <ᵀ c₀) × (c₀ ≤ᵀ b)
cons-btw′ e (hd< p) (inj₁ (hd< q)) = ⊥-elim (irrᴾ e (<ᴾ-trans p q))
cons-btw′ e (hd< p) (inj₁ (tl< q)) = ⊥-elim (irrᴾ e p)
cons-btw′ e (hd< p) (inj₂ refl)    = ⊥-elim (irrᴾ e p)
cons-btw′ e (tl< p) (inj₁ (hd< q)) = ⊥-elim (irrᴾ e q)
cons-btw′ e (tl< p) (inj₁ (tl< q)) = _ , refl , p , inj₁ q
cons-btw′ e (tl< p) (inj₂ refl)    = _ , refl , p , inj₂ refl

cons-btw : ∀ {x b₀ b c} → (x ∷ b₀) <ᵀ c → c ≤ᵀ (x ∷ b) →
           Σ T λ c₀ → (c ≡ x ∷ c₀) × (b₀ <ᵀ c₀) × (c₀ ≤ᵀ b)
cons-btw = cons-btw′ refl

psi-btw′ : ∀ {u u′ b₀ b c} → u ≡ u′ → (ψ u b₀ ∷ []) ≤ᵀ c → c ≤ᵀ (ψ u′ b ∷ []) →
           Σ T λ c₀ → Σ T λ c₁ → (c ≡ ψ u c₀ ∷ c₁) × (b₀ ≤ᵀ c₀) × (c₀ ≤ᵀ b)
psi-btw′ e l (inj₁ (tl< ()))
psi-btw′ e (inj₂ refl) (inj₂ refl)            = _ , [] , refl , inj₂ refl , inj₂ refl
psi-btw′ e (inj₂ refl) (inj₁ (hd< (lv< p)))   = ⊥-elim (irrᵀ e p)
psi-btw′ e (inj₂ refl) (inj₁ (hd< (ar< p)))   = _ , [] , refl , inj₂ refl , inj₁ p
psi-btw′ e (inj₁ (hd< (lv< p))) (inj₂ refl)   = ⊥-elim (irrᵀ e p)
psi-btw′ e (inj₁ (hd< (ar< p))) (inj₂ refl)   = _ , [] , refl , inj₁ p , inj₂ refl
psi-btw′ e (inj₁ (tl< ())) (inj₂ refl)
psi-btw′ e (inj₁ (hd< (lv< p))) (inj₁ (hd< (lv< q))) = ⊥-elim (irrᵀ e (<ᵀ-trans p q))
psi-btw′ e (inj₁ (hd< (lv< p))) (inj₁ (hd< (ar< q))) = ⊥-elim (irrᵀ e p)
psi-btw′ e (inj₁ (hd< (ar< p))) (inj₁ (hd< (lv< q))) = ⊥-elim (irrᵀ e q)
psi-btw′ e (inj₁ (hd< (ar< p))) (inj₁ (hd< (ar< q))) = _ , _ , refl , inj₁ p , inj₁ q
psi-btw′ e (inj₁ (tl< p)) (inj₁ (hd< (lv< q)))       = ⊥-elim (irrᵀ e q)
psi-btw′ e (inj₁ (tl< p)) (inj₁ (hd< (ar< q)))       = _ , _ , refl , inj₂ refl , inj₁ q

psi-btw : ∀ {u b₀ b c} → (ψ u b₀ ∷ []) ≤ᵀ c → c ≤ᵀ (ψ u b ∷ []) →
          Σ T λ c₀ → Σ T λ c₁ → (c ≡ ψ u c₀ ∷ c₁) × (b₀ ≤ᵀ c₀) × (c₀ ≤ᵀ b)
psi-btw = psi-btw′ refl

psi-sub-btw : ∀ {u₀ u c} → (ψ u₀ [] ∷ []) <ᵀ c → c ≤ᵀ (ψ u [] ∷ []) →
              Σ T λ r → Σ T λ s → Σ T λ c₁ → (c ≡ ψ r s ∷ c₁) × (u₀ ≤ᵀ r) × (r ≤ᵀ u)
psi-sub-btw l (inj₁ (hd< (ar< ())))
psi-sub-btw l (inj₁ (tl< ()))
psi-sub-btw (hd< (lv< p)) (inj₁ (hd< (lv< q))) = _ , _ , _ , refl , inj₁ p , inj₁ q
psi-sub-btw (hd< (ar< p)) (inj₁ (hd< (lv< q))) = _ , _ , _ , refl , inj₂ refl , inj₁ q
psi-sub-btw (tl< p) (inj₁ (hd< (lv< q)))       = _ , _ , _ , refl , inj₂ refl , inj₁ q
psi-sub-btw (hd< (lv< p)) (inj₂ refl)          = _ , _ , _ , refl , inj₁ p , inj₂ refl
psi-sub-btw (hd< (ar< ())) (inj₂ refl)
psi-sub-btw (tl< ()) (inj₂ refl)

T-nil : ∀ {z a} → [] <ᵀ a → Trian z [] a
T-nil p = mkT p (λ _ _ _ _ ())

T-self : ∀ {z a} → z <ᵀ a → Trian z z a
T-self p = mkT p (λ u c _ _ i → inj₂ (inj₂ (_ , i , inj₂ refl)))


T-cons : ∀ {z b₀ b} x → Trian z b₀ b → Trian z (x ∷ b₀) (x ∷ b)
T-cons {z} {b₀} {b} x t = mkT (tl< (t< t)) go where
  go : ∀ u c → (x ∷ b₀) <ᵀ c → c ≤ᵀ (x ∷ b) → ∀ {y} → InG u y (x ∷ b₀) → Dom u z c y
  go u c q r (gp i) with cons-btw q r
  ... | c₀ , refl , q₀ , r₀ = inj₁ (_ , gp i , inj₂ refl)
  go u c q r (gtl i) with cons-btw q r
  ... | c₀ , refl , q₀ , r₀ = dom-lift gtl (tb t u c₀ q₀ r₀ i)

psi-core : ∀ {z b₀ b u c₀ c₁ v x} → (∀ v c → b₀ <ᵀ c → c ≤ᵀ b → ∀ {x} → InG v x b₀ → Dom v z c x) →
           b₀ ≤ᵀ c₀ → c₀ ≤ᵀ b → InG v x (ψ u b₀ ∷ []) → Dom v z (ψ u c₀ ∷ c₁) x
psi-core h l₀ r₀ (gp (gh l))              = inj₁ (_ , gp (gh l) , l₀)
psi-core h l₀ r₀ (gp (gw l i))            = inj₁ (_ , gp (gw l i) , inj₂ refl)
psi-core h (inj₁ p) r₀ (gp (gc l i))      = dom-lift (λ j → gp (gc l j)) (h _ _ p r₀ i)
psi-core h (inj₂ refl) r₀ (gp (gc l i))   = inj₁ (_ , gp (gc l i) , inj₂ refl)
psi-core h l₀ r₀ (gtl ())

T-psi : ∀ {z b₀ b} u → Trian z b₀ b → Trian z (ψ u b₀ ∷ []) (ψ u b ∷ [])
T-psi {z} {b₀} {b} u t = mkT (hd< (ar< (t< t))) go where
  go : ∀ v c → (ψ u b₀ ∷ []) <ᵀ c → c ≤ᵀ (ψ u b ∷ []) → ∀ {x} → InG v x (ψ u b₀ ∷ []) → Dom v z c x
  go v c q r m with psi-btw (inj₁ q) r
  ... | c₀ , c₁ , refl , l₀ , r₀ = psi-core (tb t) l₀ r₀ m

sub-core : ∀ {z u₀ u r s c₁ v x} → (∀ v c → u₀ <ᵀ c → c ≤ᵀ u → ∀ {x} → InG v x u₀ → Dom v z c x) →
           u₀ ≤ᵀ r → r ≤ᵀ u → InG v x (ψ u₀ [] ∷ []) → Dom v z (ψ r s ∷ c₁) x
sub-core h l₀ r₀ (gp (gh l))            = inj₂ (inj₁ refl)
sub-core h (inj₁ p) r₀ (gp (gw l i))    = dom-lift (λ j → gp (gw (≤-trans′ l (inj₁ p)) j)) (h _ _ p r₀ i)
sub-core h (inj₂ refl) r₀ (gp (gw l i)) = inj₁ (_ , gp (gw l i) , inj₂ refl)
sub-core h l₀ r₀ (gp (gc l ()))
sub-core h l₀ r₀ (gtl ())

T-sub : ∀ {z u₀ u} → Trian z u₀ u → Trian z (ψ u₀ [] ∷ []) (ψ u [] ∷ [])
T-sub {z} {u₀} {u} t = mkT (hd< (lv< (t< t))) go where
  go : ∀ v c → (ψ u₀ [] ∷ []) <ᵀ c → c ≤ᵀ (ψ u [] ∷ []) → ∀ {x} → InG v x (ψ u₀ [] ∷ []) → Dom v z c x
  go v c q r m with psi-sub-btw q r
  ... | r′ , s , c₁ , refl , l₀ , r₀ = sub-core (tb t) l₀ r₀ m

rep-ge : ∀ {x} k → (x ∷ []) ≤ᵀ replicate (suc k) x
rep-ge zero    = inj₂ refl
rep-ge (suc k) = inj₁ (tl< []<)

T-rep : ∀ {z x a} → Trian z (x ∷ []) a → ∀ k → replicate k x <ᵀ a → Trian z (replicate k x) a
T-rep {z} {x} {a} t k p = mkT p (go k) where
  go : ∀ k → ∀ u c → replicate k x <ᵀ c → c ≤ᵀ a → ∀ {y} → InG u y (replicate k x) → Dom u z c y
  go (suc k) u c q r i = tb t u c (≤-< (rep-ge k) q) r (G-rep (suc k) i)

rep< : ∀ {u b′ b} → b′ <ᵀ b → ∀ k → replicate k (ψ u b′) <ᵀ (ψ u b ∷ [])
rep< p zero    = []<
rep< p (suc k) = hd< (ar< p)

step1 : ∀ {u z b a} → Trian z b a → GB u a a → GB u z b → GB u b a
step1 t ga gz i with tb t _ _ (t< t) (inj₂ refl) i
... | inj₁ (y , j , l)        = ≤-< l (ga j)
... | inj₂ (inj₁ refl)        = pos (t< t)
... | inj₂ (inj₂ (y , j , l)) = ≤-< l (<ᵀ-trans (gz j) (t< t))

key : ∀ {u z b a} → Trian z b a → GB u z b → ∀ d → GB u d a → GB u b b ⊎ GB u d b
key t gz [] _ = inj₂ GB[]
key {u} {z} {b} {a} t gz (ψ v c ∷ ts) gd with key t gz ts (λ i → gd (gtl i))
... | inj₁ h = inj₁ h
... | inj₂ gts with dec≤ u v
...   | inj₂ v<u = inj₂ λ { (gp (gh l)) → ⊥-elim (≤¬> l v<u) ; (gp (gw l _)) → ⊥-elim (≤¬> l v<u)
                         ; (gp (gc l _)) → ⊥-elim (≤¬> l v<u) ; (gtl i) → gts i }
...   | inj₁ l with key t gz v (λ i → gd (gp (gw l i))) | key t gz c (λ i → gd (gp (gc l i)))
...     | inj₁ h  | _       = inj₁ h
...     | inj₂ _  | inj₁ h  = inj₁ h
...     | inj₂ gv | inj₂ gc′ with tri c b
...       | inj₁ c<b = inj₂ λ { (gp (gh _)) → c<b ; (gp (gw _ i)) → gv i ; (gp (gc _ i)) → gc′ i ; (gtl i) → gts i }
...       | inj₂ (inj₁ refl) = inj₁ gc′
...       | inj₂ (inj₂ b<c) = inj₁ go where
  go : GB u b b
  go i with tb t u c b<c (inj₁ (gd (gp (gh l)))) i
  ... | inj₁ (y , j , l′)        = ≤-< l′ (gc′ j)
  ... | inj₂ (inj₁ refl)         = posG i
  ... | inj₂ (inj₂ (y , j , l′)) = ≤-< l′ (gz j)

Gtri : ∀ {u z b a} → Trian z b a → GB u a a → GB u z b → GB u b b
Gtri {b = b} t ga gz with key t gz b (step1 t ga gz)
... | inj₁ h = h
... | inj₂ h = h

ψ0≢c1 : ∀ {u} c → cofψ0 u c ≡ c1 → ⊥
ψ0≢c1 c0 ()
ψ0≢c1 c1 ()
ψ0≢c1 cω ()
ψ0≢c1 (cΩ _) ()

T-pred : ∀ t → cof t ≡ c1 → Trian [] (pred t) t
T-pred [] ()
T-pred (x ∷ xs@(_ ∷ _)) e = T-cons x (T-pred xs e)
T-pred (𝟏 ∷ []) e = T-nil []<
T-pred (ψ u b@(_ ∷ _) ∷ []) e = ⊥-elim (cofA≢c1 u (cof b) e)
T-pred (ψ u@(_ ∷ _) [] ∷ []) e = ⊥-elim (ψ0≢c1 (cof u) e)

TΩ : ∀ {a μ} (v : VΩ a μ) {η} → η <ᵀ Ωs μ → Trian η (fΩ v η) a
TΩ (ωs {x = x} v) p    = T-cons x (TΩ v p)
TΩ (ωr e) {η} p        = T-self (subst (η <ᵀ_) (reg-eq e) p)
TΩ (ωl e v) p          = T-sub (TΩ v p)
TΩ (ωp {u = u} _ _ v) p = T-psi u (TΩ v p)

Dom′ : T → T → T → Set            -- x ≤ c, 或 x ≼ G_v(c), 或 x = 0
Dom′ v c x = (x ≤ᵀ c) ⊎ Cov v c x ⊎ (x ≡ [])

dom′-le : ∀ {v c x y} → x ≤ᵀ y → Dom′ v c y → Dom′ v c x
dom′-le l (inj₁ m)                    = inj₁ (≤-trans′ l m)
dom′-le l (inj₂ (inj₁ (y′ , j , m)))  = inj₂ (inj₁ (y′ , j , ≤-trans′ l m))
dom′-le l (inj₂ (inj₂ refl))          = inj₂ (inj₂ (≤[] l))

HS : ∀ {b ν} → VΩ b ν → Set
HS {b} {ν} w = ∀ v c → fΩ w (γ w zero) ≤ᵀ c → c ≤ᵀ b → ∀ {x} → InG v x ν → Cov v c x ⊎ (x ≡ [])

HB : ∀ {b ν} → VΩ b ν → Set
HB {b} {ν} w = ∀ k v c → fΩ w (γ w k) ≤ᵀ c → c ≤ᵀ b → ∀ {x} → InG v x (γ w k) → Dom′ v c x

tower-bd : ∀ {b ν} (w : VΩ b ν) → HS w → HB w
tower-bd w hS zero v c l r (gp (gh _)) = inj₂ (inj₂ refl)
tower-bd w hS zero v c l r (gp (gw _ i)) with hS v c l r i
... | inj₁ cv = inj₂ (inj₁ cv)
... | inj₂ e  = inj₂ (inj₂ e)
tower-bd w hS zero v c l r (gp (gc _ ()))
tower-bd w hS zero v c l r (gtl ())
tower-bd w hS (suc k) v c l r (gp (gh _)) = inj₁ (inj₁ (<-≤ (val-mono w k) l))
tower-bd w hS (suc k) v c l r (gp (gw _ i)) with hS v c (≤-trans′ (val-le0 w (suc k)) l) r i
... | inj₁ cv = inj₂ (inj₁ cv)
... | inj₂ e  = inj₂ (inj₂ e)
tower-bd w hS (suc k) v c l r (gp (gc _ i)) with ≤-trans′ (inj₁ (val-mono w k)) l
... | inj₂ refl = inj₂ (inj₁ (_ , i , inj₂ refl))
... | inj₁ q with tb (TΩ w (γ< w k)) v c q r i
...   | inj₁ cv = inj₂ (inj₁ cv)
...   | inj₂ (inj₁ e) = inj₂ (inj₂ e)
...   | inj₂ (inj₂ (y , j , xy)) = dom′-le xy (tower-bd w hS k v c (inj₁ q) r j)
tower-bd w hS (suc k) v c l r (gtl ())

c4-core : ∀ {u b ν c₀ c₁ v x} (w : VΩ b ν) → HB w → ∀ n →
          fΩ w (γ w n) ≤ᵀ c₀ → c₀ ≤ᵀ b → InG v x (ψ u (fΩ w (γ w n)) ∷ []) → Dom v [] (ψ u c₀ ∷ c₁) x
c4-core w hB n l₀ r₀ (gp (gh l))   = inj₁ (_ , gp (gh l) , l₀)
c4-core w hB n l₀ r₀ (gp (gw l i)) = inj₁ (_ , gp (gw l i) , inj₂ refl)
c4-core w hB n (inj₂ refl) r₀ (gp (gc l i)) = inj₁ (_ , gp (gc l i) , inj₂ refl)
c4-core {v = v} w hB n (inj₁ p) r₀ (gp (gc l i)) with tb (TΩ w (γ< w n)) v _ p r₀ i
... | inj₁ cv = inj₁ (cov-lift (λ j → gp (gc l j)) cv)
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ (y , j , xy)) with hB n v _ (inj₁ p) r₀ j
...   | inj₁ m = inj₁ (_ , gp (gh l) , ≤-trans′ xy m)
...   | inj₂ (inj₁ (y′ , j′ , m)) = inj₁ (y′ , gp (gc l j′) , ≤-trans′ xy m)
...   | inj₂ (inj₂ refl) = inj₂ (inj₁ (≤[] xy))
c4-core w hB n l₀ r₀ (gtl ())

T-case4 : ∀ {u b ν} (w : VΩ b ν) → HB w → ∀ n → Trian [] (ψ u (fΩ w (γ w n)) ∷ []) (ψ u b ∷ [])
T-case4 {u} {b} w hB n = mkT (hd< (ar< (t< (TΩ w (γ< w n))))) go where
  go : ∀ v c → (ψ u (fΩ w (γ w n)) ∷ []) <ᵀ c → c ≤ᵀ (ψ u b ∷ []) → ∀ {x} →
       InG v x (ψ u (fΩ w (γ w n)) ∷ []) → Dom v [] c x
  go v c q r m with psi-btw (inj₁ q) r
  ... | c₀ , c₁ , refl , l₀ , r₀ = c4-core w hB n l₀ r₀ m
```
