# 新旧块的逐层关系: 定义

> 定义 (验收用). 精简块 (`YiRWBlock`) 与 F2 (`YiLegBlock`) 之间的关系, 不是映射: 树 `RelT`, 孩子 `RelU`, 推导 `RelD`, 槽位 `RelP`, 分支 `RelB` (一个互递归的函数块); 层号 `RelL`, 路径 `RelW`, `RelV`, 证据 `RelE` 是数据; 底 `RelBase`.
> Ω 结点与 Ω 形状的孩子处: 对相关的分支 (下标) 给相关的树, 不要求往返恒等, 不用函数外延. F2 一侧用 "形状见证" 数据 (`IsS` 等) 读出构造子, 免去不相配的情形.
> 偏离简报: ℕ 极限的步进推导与嵌入的非零推导进了关系 (`RelD`), 因为证据里的相邻路径由推导经 `◃→⊑` 读出, 折叠沿这些路径比较孩子. 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBRRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
```

## F2 一侧的形状见证

```agda
module _ {S : F.Sg} where
  data IsZ : F.T S → Set where
    iz : IsZ F.zero
  data IsS (P : F.T S → Set) : F.T S → Set where
    is : ∀ {x} → P x → IsS P (F.suc x)
  data IsL (P : (f : ℕ → F.T S) → ((n : ℕ) → F.Lt S (f n) (f (suc n))) → Set) : F.T S → Set where
    il : ∀ {f a} → P f a → IsL P (F.lim f a)
  data IsΩ (P : (p : F.P S) → (F.B S p → F.T S) → Set) : F.T S → Set where
    iw : ∀ {p g} → P p g → IsΩ P (F.Ω p g)
  data IsU (P : F.T S → (c : F.C S) (y : F.D S c) → F.R S c (F.z₀ S c) y → Set) : F.T S → Set where
    iu : ∀ {x c y e} → P x c y e → IsU P (F.up x c y e)

  data DS : {x y : F.T S} → F.Lt S x y → Set where
    ds : ∀ {x} → DS (F.◃s {x = x})
  data DL (n : ℕ) : {x y : F.T S} → F.Lt S x y → Set where
    dl : ∀ {f a} → DL n (F.◃l {f = f} {a = a} n)
  data DW (P : (p : F.P S) → (F.B S p → F.T S) → Set) : {x y : F.T S} → F.Lt S x y → Set where
    dw : ∀ {p g} → P p g → DW P (F.◃w {p = p} {g = g})
  data DU (P : (x : F.T S) (c : F.C S) (y : F.D S c) → F.R S c (F.z₀ S c) y → Set) : {x y : F.T S} → F.Lt S x y → Set where
    du : ∀ {x c y e} → P x c y e → DU P (F.◃u x c y e)
  data DC (P : (x : F.T S) (c : F.C S) {y′ y : F.D S c} → F.R S c y′ y → Set) : {x y : F.T S} → F.Lt S x y → Set where
    dc : ∀ {x c y′ y e′ e} {r : F.R S c y′ y} → P x c r → DC P (F.◃c x c {e′ = e′} {e = e} r)
  data DT {x y : F.T S} (P : ∀ {m} → F.Lt S x m → F.Lt S m y → Set) : F.Lt S x y → Set where
    dt : ∀ {m} {d : F.Lt S x m} {e : F.Lt S m y} → P d e → DT P (F.◃t d e)

data I₁ {A B : Set} (P : A → Set) : A ⊎ B → Set where
  i₁ : ∀ {a} → P a → I₁ P (inj₁ a)
data I₂ {A B : Set} (P : B → Set) : A ⊎ B → Set where
  i₂ : ∀ {b} → P b → I₂ P (inj₂ b)
data IΣ {A : Set} {B : A → Set} (P : (a : A) → B a → Set) : Σ A B → Set where
  iσ : ∀ {a b} → P a b → IΣ P (a , b)
data IΣₙ {B : ℕ → Set} (n : ℕ) (P : B n → Set) : Σ ℕ B → Set where
  iσₙ : ∀ {b} → P b → IΣₙ n P (n , b)
```

## 树, 孩子, 推导, 槽位, 分支

树的关系按精简块一侧的构造子递归; Ω 结点: 槽位相关, 且对相关的分支给相关的树. 嵌入: 孩子编号相关 (Ω 形状的孩子是低层的树, 也用 `RelT`).

```agda
mutual
  RelT : (ℓ : L) (ℓ′ : F.L) → Tr ℓ → F.Tr ℓ′ → Set
  RelT ℓ ℓ′ zero         x′ = IsZ x′
  RelT ℓ ℓ′ (suc x)      x′ = IsS (RelT ℓ ℓ′ x) x′
  RelT ℓ ℓ′ (lim f a)    x′ = IsL (λ f′ a′ → ((n : ℕ) → RelT ℓ ℓ′ (f n) (f′ n)) × ((n : ℕ) → RelD ℓ ℓ′ (a n) (a′ n))) x′
  RelT ℓ ℓ′ (Ω p g)      x′ = IsΩ (λ p′ g′ → RelP ℓ ℓ′ p p′
    × ((z : Br ℓ p) (z′ : F.Br ℓ′ p′) → RelB ℓ ℓ′ p p′ z z′ → RelT ℓ ℓ′ (g z) (g′ z′))) x′
  RelT ℓ ℓ′ (up x c y e) x′ = IsU (λ x₀ c′ y′ e′ → RelT ℓ ℓ′ x x₀ × RelU ℓ ℓ′ c y e c′ y′ e′) x′

  RelU : (ℓ : L) (ℓ′ : F.L) (c : CH ℓ) (y : ChT ℓ c) (e : RCh ℓ c (chZ ℓ c) y)
         (c′ : F.Ch ℓ′) (y′ : F.ChT ℓ′ c′) (e′ : F.RCh ℓ′ c′ (F.chZ ℓ′ c′) y′) → Set
  RelU (nd sS h)     (F.suc a)    c y e c′ y′ e′ = RelT (h c) a y y′ × RelD (h c) a e e′
  RelU (nd sL g)     (F.lim g′)   n y e n′ y′ e′ = (n ≡ n′) × RelT (g n) (g′ n′) y y′ × RelD (g n) (g′ n′) e e′
  RelU (nd (sΩ k) h) (F.Ωₗ k′ h′) c y e c′ y′ e′ = RelT k k′ c c′ × RelT (h c) (h′ c′) y y′ × RelD (h c) (h′ c′) e e′
  RelU _             _            _ _ _ _  _  _  = ⊥

  RelD : (ℓ : L) (ℓ′ : F.L) {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} → ℓ ⊢ x ◃ y → F._⊢_◃_ ℓ′ x′ y′ → Set
  RelD ℓ ℓ′ ◃s                     d′ = DS d′
  RelD ℓ ℓ′ (◃l n)                 d′ = DL n d′
  RelD ℓ ℓ′ (◃w {p = p} {g = g})   d′ = DW (λ p′ g′ → RelP ℓ ℓ′ p p′
    × ((z : Br ℓ p) (z′ : F.Br ℓ′ p′) → RelB ℓ ℓ′ p p′ z z′ → RelT ℓ ℓ′ (g z) (g′ z′))) d′
  RelD ℓ ℓ′ (◃u x c y e)           d′ = DU (λ x′ c′ y′ e′ → RelT ℓ ℓ′ x x′ × RelU ℓ ℓ′ c y e c′ y′ e′) d′
  RelD ℓ ℓ′ (◃c x c r)             d′ = DC (λ x′ c′ r′ → RelT ℓ ℓ′ x x′ × RelDc ℓ ℓ′ c r c′ r′) d′
  RelD ℓ ℓ′ (◃t d e)               d′ = DT (λ d₁ e₁ → RelD ℓ ℓ′ d d₁ × RelD ℓ ℓ′ e e₁) d′

  RelDc : (ℓ : L) (ℓ′ : F.L) (c : CH ℓ) {y₁ y₂ : ChT ℓ c} → RCh ℓ c y₁ y₂
          → (c′ : F.Ch ℓ′) {y₁′ y₂′ : F.ChT ℓ′ c′} → F.RCh ℓ′ c′ y₁′ y₂′ → Set
  RelDc (nd sS h)     (F.suc a)    c r c′ r′ = RelD (h c) a r r′
  RelDc (nd sL g)     (F.lim g′)   n r n′ r′ = (n ≡ n′) × RelD (g n) (g′ n′) r r′
  RelDc (nd (sΩ k) h) (F.Ωₗ k′ h′) c r c′ r′ = RelT k k′ c c′ × RelD (h c) (h′ c′) r r′
  RelDc _             _            _ _ _  _  = ⊥

  RelP : (ℓ : L) (ℓ′ : F.L) → Pos ℓ → F.Pos ℓ′ → Set
  RelP (nd sS h)     (F.suc a)    (inj₂ (c , t)) t′ = RelP⁼ (h c) a t t′
  RelP (nd sL g)     (F.lim g′)   (inj₂ (n , t)) p′ = IΣₙ n (RelP⁼ (g n) (g′ n) t) p′
  RelP (nd (sΩ k) h) (F.Ωₗ k′ h′) (inj₁ t)       p′ = I₁ (RelP⁼ k k′ t) p′
  RelP (nd (sΩ k) h) (F.Ωₗ k′ h′) (inj₂ (c , t)) p′ = I₂ (IΣ (λ c′ t′ → RelT k k′ c c′ × RelP⁼ (h c) (h′ c′) t t′)) p′
  RelP _             _            _              _  = ⊥

  RelP⁼ : (a : L) (a′ : F.L) → Pos⁼ a → F.Pos⁼ a′ → Set
  RelP⁼ a a′ (inj₁ _) t′ = I₁ (λ _ → ⊤) t′
  RelP⁼ a a′ (inj₂ p) t′ = I₂ (RelP a a′ p) t′

  RelB : (ℓ : L) (ℓ′ : F.L) (p : Pos ℓ) (p′ : F.Pos ℓ′) → Br ℓ p → F.Br ℓ′ p′ → Set
  RelB (nd sS h)     (F.suc a)    (inj₂ (c , t)) t′               z z′ = RelB⁼ (h c) a t t′ z z′
  RelB (nd sL g)     (F.lim g′)   (inj₂ (n , t)) (n′ , t′)        z z′ = RelB⁼ (g n) (g′ n′) t t′ z z′
  RelB (nd (sΩ k) h) (F.Ωₗ k′ h′) (inj₁ t)       (inj₁ t′)        z z′ = RelB⁼ k k′ t t′ z z′
  RelB (nd (sΩ k) h) (F.Ωₗ k′ h′) (inj₂ (c , t)) (inj₂ (c′ , t′)) z z′ = RelB⁼ (h c) (h′ c′) t t′ z z′
  RelB _             _            _              _                _ _  = ⊥

  RelB⁼ : (a : L) (a′ : F.L) (t : Pos⁼ a) (t′ : F.Pos⁼ a′) → Br⁼ a t → F.Br⁼ a′ t′ → Set
  RelB⁼ a a′ (inj₁ _) (inj₁ _)  z z′ = RelT a a′ z z′
  RelB⁼ a a′ (inj₂ p) (inj₂ p′) z z′ = RelB a a′ p p′ z z′
  RelB⁼ _ _  _        _         _ _  = ⊥
```

## 层号, 孩子编号

```agda
data RelL : L → F.L → Set where
  lz : RelL zero F.zero
  lS : ∀ {h a} → RelL (h tt) a → RelL (nd sS h) (F.suc a)
  lL : ∀ {g g′} → ((n : ℕ) → RelL (g n) (g′ n)) → RelL (nd sL g) (F.lim g′)
  lΩ : ∀ {k h k′ h′} → RelL k k′ → ((c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelL (h c) (h′ c′))
     → RelL (nd (sΩ k) h) (F.Ωₗ k′ h′)

RelC : (ℓ : L) (ℓ′ : F.L) → CH ℓ → F.Ch ℓ′ → Set
RelC (nd sS h)     (F.suc a)    c c′ = ⊤
RelC (nd sL g)     (F.lim g′)   n n′ = n ≡ n′
RelC (nd (sΩ k) h) (F.Ωₗ k′ h′) c c′ = RelT k k′ c c′
RelC _             _            _ _  = ⊥
```

## 路径 (目标路径 `≤` 与不经下标层侧的 `⊑`)

```agda
data RelW : {j ℓ : L} {j′ ℓ′ : F.L} → j ≤ ℓ → F._≤_ j′ ℓ′ → Set where
  wself : ∀ {ℓ ℓ′} → RelW (self {ℓ = ℓ}) (F.self {ℓ = ℓ′})
  wincS : ∀ {j h j′ a} {c : ⊤} {v : j ≤ h c} {v′ : F._≤_ j′ a}
        → RelW v v′ → RelW (inc {s = sS} {h = h} c v) (F.ins v′)
  winuS : ∀ {j h j′ a} {vs : (c : ⊤) → j ≤ h c} {v′ : F._≤_ j′ a}
        → RelW (vs tt) v′ → RelW (inu {s = sS} {h = h} vs) (F.ins v′)
  wincL : ∀ {j g j′ g′} (n : ℕ) {v : j ≤ g n} {v′ : F._≤_ j′ (g′ n)}
        → RelW v v′ → RelW (inc {s = sL} {h = g} n v) (F.inl {g = g′} n v′)
  winuL : ∀ {j g j′ g′} {vs : (n : ℕ) → j ≤ g n} {vs′ : (n : ℕ) → F._≤_ j′ (g′ n)}
        → ((n : ℕ) → RelW (vs n) (vs′ n)) → RelW (inu {s = sL} {h = g} vs) (F.inlu {g = g′} vs′)
  wincΩ : ∀ {j k h j′ k′ h′} {c : Tr k} {c′ : F.Tr k′} {v : j ≤ h c} {v′ : F._≤_ j′ (h′ c′)}
        → RelT k k′ c c′ → RelW v v′ → RelW (inc {s = sΩ k} {h = h} c v) (F.inb {h = h′} c′ v′)
  winuΩ : ∀ {j k h j′ k′ h′} {vs : (c : Tr k) → j ≤ h c} {vs′ : (c : F.Tr k′) → F._≤_ j′ (h′ c)}
        → ((c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelW (vs c) (vs′ c′)) → RelW (inu {s = sΩ k} {h = h} vs) (F.inu {h = h′} vs′)
  wink  : ∀ {j k h j′ k′ h′} {v : j ≤ k} {v′ : F._≤_ j′ k′}
        → RelW v v′ → RelW (ink {h = h} v) (F.ink {h = h′} v′)

data RelV : {j ℓ : L} {j′ ℓ′ : F.L} → j ⊑ ℓ → F._⊑_ j′ ℓ′ → Set where
  vself : ∀ {ℓ ℓ′} → RelV (self {ℓ = ℓ}) (F.self {ℓ = ℓ′})
  vincS : ∀ {j h j′ a} {c : ⊤} {v : j ⊑ h c} {v′ : F._⊑_ j′ a}
        → RelV v v′ → RelV (inc {s = sS} {h = h} c v) (F.ins v′)
  vinuS : ∀ {j h j′ a} {vs : (c : ⊤) → j ⊑ h c} {v′ : F._⊑_ j′ a}
        → RelV (vs tt) v′ → RelV (inu {s = sS} {h = h} vs) (F.ins v′)
  vincL : ∀ {j g j′ g′} (n : ℕ) {v : j ⊑ g n} {v′ : F._⊑_ j′ (g′ n)}
        → RelV v v′ → RelV (inc {s = sL} {h = g} n v) (F.inl {g = g′} n v′)
  vinuL : ∀ {j g j′ g′} {vs : (n : ℕ) → j ⊑ g n} {vs′ : (n : ℕ) → F._⊑_ j′ (g′ n)}
        → ((n : ℕ) → RelV (vs n) (vs′ n)) → RelV (inu {s = sL} {h = g} vs) (F.inlu {g = g′} vs′)
  vincΩ : ∀ {j k h j′ k′ h′} {c : Tr k} {c′ : F.Tr k′} {v : j ⊑ h c} {v′ : F._⊑_ j′ (h′ c′)}
        → RelT k k′ c c′ → RelV v v′ → RelV (inc {s = sΩ k} {h = h} c v) (F.inb {h = h′} c′ v′)
  vinuΩ : ∀ {j k h j′ k′ h′} {vs : (c : Tr k) → j ⊑ h c} {vs′ : (c : F.Tr k′) → F._⊑_ j′ (h′ c)}
        → ((c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelV (vs c) (vs′ c′)) → RelV (inu {s = sΩ k} {h = h} vs) (F.inu {h = h′} vs′)
```

## 证据与底

精简块的 `Ok` 对 F2 的 `Ev` 与 `Rt`: ℕ 极限形状的相邻路径相关, Ω 形状的下标层到孩子的路径对相关的孩子相关.

```agda
data RelE : (ℓ : L) (ℓ′ : F.L) → Ok ℓ → F.Ev ℓ′ → F.Rt ℓ′ → Set where
  ez : ∀ {o ε ρ} → RelE zero F.zero o ε ρ
  eS : ∀ {h a} {o : Ok (nd sS h)} {ε : F.Ev a} {ρ : F.Rt a}
     → RelE (h tt) a (proj₂ o tt) ε ρ → RelE (nd sS h) (F.suc a) o ε ρ
  eL : ∀ {g g′} {o : Ok (nd sL g)} {ε : F.Ev (F.lim g′)} {ρ : F.Rt (F.lim g′)}
     → ((n : ℕ) → RelW (proj₁ o n) (proj₂ ρ n)) → ((n : ℕ) → RelE (g n) (g′ n) (proj₂ o n) (ε n) (proj₁ ρ n))
     → RelE (nd sL g) (F.lim g′) o ε ρ
  eΩ : ∀ {k h k′ h′} {o : Ok (nd (sΩ k) h)} {ε : F.Ev (F.Ωₗ k′ h′)} {ρ : F.Rt (F.Ωₗ k′ h′)}
     → RelE k k′ (proj₁ (proj₁ o)) (proj₁ ε) (proj₁ ρ)
     → ((c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelW (proj₂ (proj₁ o) c) (proj₁ (proj₂ ε c′)))
     → ((c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelE (h c) (h′ c′) (proj₂ o c) (proj₂ (proj₂ ε c′)) (proj₂ ρ c′))
     → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ

RelBase : (ℓ : L) (ℓ′ : F.L) → Base ℓ → F.Base ℓ′ → Set
RelBase ℓ ℓ′ B B′ = (j : L) (j′ : F.L) (w : j ≤ ℓ) (w′ : F._≤_ j′ ℓ′) → RelW w w′
  → RelT j j′ (proj₁ (B j w)) (F.bs B′ j′ w′) × RelD j j′ (proj₂ (B j w)) (F.ns B′ j′ w′)
```
