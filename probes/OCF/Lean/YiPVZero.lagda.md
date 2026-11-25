# 第 0 层关系与前驱的搬运
验收文件；编译定理：复制保留步进，相关终点的 F2 前驱可读回，M⁰ 双向搬运。
为第 1 层的分支量化与嵌入提供桥；来源 YiBRRel 的对应、YiMEBase/YiKVRel 的关系构造子。
没有改变树、折叠或合法性；入口 YiPVOne。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPVZero where
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as FO
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiMEBase as ME
open import OCF.Lean.YiBRRel

mutual
  copy : B.Tr B.zero → F.Tr F.zero
  copy B.zero = F.zero
  copy (B.suc x) = F.suc (copy x)
  copy (B.lim f a) = F.lim (λ n → copy (f n)) (λ n → copyD (a n))
  copyD : ∀ {x y} → B._⊢_◃_ B.zero x y → F._⊢_◃_ F.zero (copy x) (copy y)
  copyD B.◃s = F.◃s
  copyD (B.◃l n) = F.◃l n
  copyD (B.◃t d e) = F.◃t (copyD d) (copyD e)
mutual
  copy-R : ∀ x → RelT B.zero F.zero x (copy x)
  copy-R B.zero = iz
  copy-R (B.suc x) = is (copy-R x)
  copy-R (B.lim f a) = il ((λ n → copy-R (f n)) , (λ n → copyD-R (a n)))
  copyD-R : ∀ {x y} (d : B._⊢_◃_ B.zero x y) → RelD B.zero F.zero d (copyD d)
  copyD-R B.◃s = ds
  copyD-R (B.◃l n) = dl
  copyD-R (B.◃t d e) = dt (copyD-R d , copyD-R e)

forth : ∀ {t x} → K.M⁰ t x → ME.M⁰ t (copy x)
forth K.mz = ME.mz
forth (K.m1 e m) = ME.m1 e (forth m)
forth (K.mL e h) = ME.mL e (λ n → forth (h n))
forth (K.mw m d) = ME.mw (forth m) (copyD d)

pull : ∀ {x x′ y′} → RelT B.zero F.zero x x′ → (d′ : F._⊢_◃_ F.zero y′ x′)
  → Σ (B.Tr B.zero) λ y → RelT B.zero F.zero y y′ × Σ (B._⊢_◃_ B.zero y x) λ d → RelD B.zero F.zero d d′
pull {x = B.zero} iz d = ⊥-elim (FO.¬◃z d)
pull {x = B.suc x} (is r) F.◃s = x , r , B.◃s , ds
pull {x = B.lim f a} (il (rf , ra)) (F.◃l n) = f n , rf n , B.◃l n , dl
pull r (F.◃t d e) with pull r e
... | y , ry , de , re with pull ry d
... | z , rz , dd , rd = z , rz , B.◃t dd de , dt (rd , re)

zero-back : ∀ {x} → RelT B.zero F.zero x F.zero → x ≡ B.zero
zero-back {B.zero} iz = refl
zero-back {B.suc x} ()
zero-back {B.lim f a} ()

nonzeroR : ∀ {x x′} → RelT B.zero F.zero x x′ → (d′ : F._⊢_◃_ F.zero F.zero x′)
  → Σ (B._⊢_◃_ B.zero B.zero x) λ d → RelD B.zero F.zero d d′
nonzeroR {x} r d′ with pull r d′
... | z , rz , dz , rdz = subst (λ w → Σ (B._⊢_◃_ B.zero w x) λ d → RelD B.zero F.zero d d′) (zero-back rz) (dz , rdz)

back : ∀ {t x x′} → RelT B.zero F.zero x x′ → ME.M⁰ t x′ → K.M⁰ t x
back r ME.mz = K.mz
back r (ME.mL e h) = K.mL e (λ n → back r (h n))
back {x = B.zero} () (ME.m1 e m)
back {x = B.suc x} (is r) (ME.m1 e m) = K.m1 e (back r m)
back {x = B.lim f a} () (ME.m1 e m)
back r (ME.mw m d) with pull r d
... | y , ry , dy , rdy = K.mw (back ry m) dy
```
