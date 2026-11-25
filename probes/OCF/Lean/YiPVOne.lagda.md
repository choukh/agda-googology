# 第 1 层 F2 关系搬到精简块
验收文件；编译定理：RelT one (suc zero) 将 YiANFam.M 1 搬到 YiCLFam.M 1。
来源 YiBRRel；零层分支与孩子用 YiPVZero，mw 沿相关终点读回前驱。
本桥不限定源折叠的层号；不提供可数层号上的 Leaf，实例见 YiPVSmall。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPVOne where
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as FO
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiANFam as AF
import OCF.Lean.YiMEBase as ME
open import OCF.Lean.YiBRRel
import OCF.Lean.YiPVZero as Z
one′ : F.L
one′ = F.suc F.zero

pull : ∀ {x x′ y′} → RelT K.one one′ x x′ → F._⊢_◃_ one′ y′ x′
  → Σ (B.Tr K.one) λ y → RelT K.one one′ y y′ × B._⊢_◃_ K.one y x
pull {x = B.zero} iz d = ⊥-elim (FO.¬◃z d)
pull {x = B.suc x} (is r) F.◃s = x , r , B.◃s
pull {x = B.lim f a} (il (rf , ra)) (F.◃l n) = f n , rf n , B.◃l n
pull {x = B.Ω (inj₂ (tt , inj₁ tt)) g} (iw (i₁ _ , rg)) F.◃w = g B.zero , rg B.zero F.zero iz , B.◃w
pull {x = B.Ω (inj₁ ()) g} _ _
pull {x = B.Ω (inj₂ (tt , inj₂ ())) g} _ _
pull {x = B.up x tt y e} (iu (rx , (ry , re))) (F.◃u _ _ _ _) = x , rx , B.◃u x tt y e
pull {x = B.up x tt y e} (iu (rx , (ry , re))) (F.◃c _ _ {e′ = nz′} d) with Z.pull ry d
... | z , rz , dz , rdz = B.up x tt z (proj₁ nz) , iu (rx , (rz , proj₂ nz)) , B.◃c x tt dz
  where
  nz = Z.nonzeroR rz nz′
pull r (F.◃t d e) with pull r e
... | y , ry , de with pull ry d
... | z , rz , dd = z , rz , B.◃t dd de

back : ∀ {t x x′} → RelT K.one one′ x x′ → AF.M 1 t x′ → H.M 1 t x
back r ME.mz = K.mz
back r (ME.mL e h) = K.mL e (λ n → back r (h n))
back {x = B.zero} () (ME.m1 e m)
back {x = B.suc x} (is r) (ME.m1 e m) = K.m1 e (back r m)
back {x = B.lim f a} () (ME.m1 e m)
back {x = B.Ω p g} () (ME.m1 e m)
back {x = B.up x c y e} () (ME.m1 e′ m)
back {x = B.zero} () (ME.mΩ e nu h)
back {x = B.suc x} () (ME.mΩ e nu h)
back {x = B.lim f a} () (ME.mΩ e nu h)
back {x = B.up x c y e} () (ME.mΩ e′ nu h)
back {x = B.Ω (inj₁ ()) g} r m
back {x = B.Ω (inj₂ (tt , inj₂ ())) g} r m
back {x = B.Ω (inj₂ (tt , inj₁ tt)) g} (iw (i₁ _ , rg)) (ME.mΩ e nu h) =
  K.mΩ e nu (λ η c l → back (rg c (Z.copy c) (Z.copy-R c)) (h η (Z.copy c) (Z.forth l)))
back {x = B.zero} () (ME.mU m ch)
back {x = B.suc x} () (ME.mU m ch)
back {x = B.lim f a} () (ME.mU m ch)
back {x = B.Ω p g} () (ME.mU m ch)
back {x = B.up x tt y e} (iu (rx , (ry , re))) (ME.mU m ch) = K.mU (back rx m) (Z.back ry ch)
back r (ME.mw m d) with pull r d
... | y , ry , dy = K.mw (back ry m) dy
```
