# 实际会移动的指标路径实例

路径世界是可数布劳威尔树。进入指标坐标 c 要当前界位于 c，且 c
合法，进入后的世界就是 c。前缀的其他分量用 psStep/psSup 的 Kripke
可入，故并非把整个路径结构取 triv。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedPathMoving where
open import Data.Nat using (zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.BoundedFoldIf using (U; P; T)
open import OCF.Lean.ThirdPS
open import OCF.Lean.BoundedPathRun

order : Po
order = record { W = HB S⊥ ; _≤_ = λ a b → a ⊲[ tt ] b ; rf = hself ; tr = ⊲ᴮ-tr }

empty : PS order S⊥
empty = triv

moving : PS order U
moving = record
  { Ev = λ V _ → hs hz ⊲[ tt ] V
  ; Ad = λ V κ c → admit V κ c
  ; nx = λ V κ c a → enter V κ c a
  ; ev↑ = λ q p → ⊲ᴮ-tr p q
  ; ad↓ = λ q {κ} {c} a → down q κ c a
  ; nx↑ = λ {V} {κ} {c} a → ascend V κ c a }
  where
  admit : ∀ V κ → E U κ → Set
  admit V (inj₁ ()) c
  admit V (inj₂ _) c = (V ⊲[ tt ] c) × LgB c
  enter : ∀ V κ c → admit V κ c → HB S⊥
  enter V (inj₁ ()) c a
  enter V (inj₂ _) c a = c
  down : ∀ {V W} → V ⊲[ tt ] W → ∀ κ c (a : admit W κ c) →
    Data.Product.Σ (admit V κ c) (λ b → enter V κ c b ⊲[ tt ] enter W κ c a)
  down q (inj₁ ()) c a
  down q (inj₂ _) c (p , l) = (⊲ᴮ-tr q p , l) , hself
  ascend : ∀ V κ c (a : admit V κ c) → V ⊲[ tt ] enter V κ c a
  ascend V (inj₁ ()) c a
  ascend V (inj₂ _) c (p , l) = p

tower : ∀ c → PS order (Lv (ls lz ⊕L upL lz c))
tower hz = psStep empty
tower (hs c) = psStep (tower c)
tower (hl f) = psSup (λ n → tower (f n))
tower (hΩ () f)

parts : (i : ⊤ ⊎ HB S⊥) → PS order (FXL lz (λ c → ls lz ⊕L upL lz c) i)
parts (inj₁ _) = moving
parts (inj₂ c) = tower c

Q : PS order (T hz)
Q = psSup parts
module R = Relative Q

one two : HB S⊥
one = hs hz
two = hs one

enter-one : PS.Ad Q one (inj₁ tt , inj₂ tt) one
enter-one = hself , tt
enter-two : PS.Ad Q one (inj₁ tt , inj₂ tt) two
enter-two = hsuc hself , tt

next-one : PS.nx Q one (inj₁ tt , inj₂ tt) one enter-one ≡ one
next-one = refl
next-two : PS.nx Q one (inj₁ tt , inj₂ tt) two enter-two ≡ two
next-two = refl

-- 真正Ω高度，指标分量进入two后保留这一动态世界。
B : HB U
B = hΩ (inj₂ tt) up
source-next : PS.nx (R.paths B) one (inj₁ tt , inj₂ tt) two
  (R.index-ad up one (inj₂ tt) two enter-two) ≡ two
source-next = refl
```

同一当前界 one 对不同坐标有两个不同后继世界；并非常值 next。
每个坐标可入证据直接给出当前界到该坐标的字面路径，没有判等或三歧。
此实例验收的是 keep 所需路径字段，不是新序数闭项或强度结论。
