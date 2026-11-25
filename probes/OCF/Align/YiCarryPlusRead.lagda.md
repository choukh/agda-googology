# Carry⁺：有限次 Ω 与带证据读回

沿用 YiK1b 的次数归纳及 Raw 结构递归。新增使用的字段只有根下界
Nested：Raw lc 行从输入 Nested 的 NestedLow 投影，Ω 后继行用
cO-nested。原 Reg 的全部守卫量词直接复用 YiK1bBase.read-regs。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryPlusRead where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (Below)
import OCF.Align.YiK1 as K
import OCF.Align.YiCarry as Y
open import OCF.Align.YiCarryBounds using (LglLow; NestedLow; cO-nested)
open import OCF.Align.YiCarryPlus using (Carry⁺; forget⁺; LglB; cp-carry⁺)
open import OCF.Align.YiK1bBase

read0-carry⁺ : ∀ (η : F.Raw F.zero) → Carry⁺ (V.up F.zero η)
read0-carry⁺ G.zero = tt
read0-carry⁺ (G.suc a) = read0-carry⁺ a
read0-carry⁺ (G.lim f) = λ n → read0-carry⁺ (f n)
read0-carry⁺ (G.lc () c t g)
read0-carry⁺ (G.em () a)
read0-carry⁺ G.top = tt

pow-node-carry⁺ : ∀ n k c t g → Reg (pow n (F.lc k c t g)) →
  LglB k c → Carry⁺ (pow n t) →
  (∀ η e → LglB k η → Carry⁺ (pow n (g η e))) →
  Carry⁺ (pow n (F.lc k c t g))
pow-node-carry⁺ zero k c t g reg (lc , bc) ct cg = reg , lc , bc , ct , cg
pow-node-carry⁺ (suc n) k c t g reg b ct cg =
  pow-node-carry⁺ n k c (V.Ω̂ t) (λ η e → V.Ω̂ (g η e)) reg b ct cg

pow-lim-carry⁺ : ∀ n (f : ℕ → F.LF) →
  (∀ j → Carry⁺ (pow n (f j))) → Carry⁺ (pow n (F.lim f))
pow-lim-carry⁺ zero f r = r
pow-lim-carry⁺ (suc n) f r = pow-lim-carry⁺ n (λ j → V.Ω̂ (f j)) r

pow-upN-carry⁺ : ∀ n y (r : F.Pre y) (c : F.Low y r)
  (t : F.LF) (g : (η : F.Low y r) → F.GdL y r c η → F.LF) →
  LglLow y r c → NestedLow y r c → Reg (pow n (V.upN y r c t g)) →
  Carry⁺ (pow n t) → (∀ η e → Carry⁺ (pow n (g η e))) →
  Carry⁺ (pow n (V.upN y r c t g))
pow-upN-carry⁺ n F.zero ()
pow-upN-carry⁺ n (F.suc y) (inj₁ _) c t g lc bc reg ct cg =
  pow-node-carry⁺ n y c t g reg (lc , bc) ct (λ η e b → cg η e)
pow-upN-carry⁺ n (F.suc y) (inj₂ r) c t g lc bc reg ct cg =
  pow-upN-carry⁺ n y r c t g lc bc reg ct cg
pow-upN-carry⁺ n (F.lim f) (m , r) c t g lc bc reg ct cg =
  pow-upN-carry⁺ n (f m) r c t g lc bc reg ct cg
pow-upN-carry⁺ n (F.lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g lc bc reg ct cg =
  pow-node-carry⁺ n k c t g reg (lc , bc) ct (λ η e b → cg η e)
pow-upN-carry⁺ n (F.lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g lc bc reg ct cg =
  pow-upN-carry⁺ n k r c t g lc bc reg ct cg
pow-upN-carry⁺ n (F.lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g lc bc reg ct cg =
  pow-upN-carry⁺ n t₀ r c t g lc bc reg ct cg
pow-upN-carry⁺ n (F.lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g lc bc reg ct cg =
  pow-upN-carry⁺ n (g₀ η e) r c t g lc bc reg ct cg

top-read-carry⁺ : ∀ y → Reg y → Below y (V.Ω̂ y) → Carry⁺ (V.Ω̂ y) →
  ∀ η → LglB y η → F.Cp y G.top η → Carry⁺ (V.up y η)
top-read-carry⁺ y ry root co G.zero b (inj₁ ())
top-read-carry⁺ y ry root co G.zero b (inj₂ ())
top-read-carry⁺ y ry root co (G.suc a) b (inj₁ ())
top-read-carry⁺ y ry root co (G.suc a) b (inj₂ p) =
  top-read-carry⁺ y ry root co a b p
top-read-carry⁺ y ry root co (G.lim f) ((st , lf) , bf) (inj₁ ())
top-read-carry⁺ y ry root co (G.lim f) ((st , lf) , bf) (inj₂ (n , p)) = term
  where
  term : ∀ m → Carry⁺ (V.up y (f m))
  term m with F.cmpC y (f (m + n))
    (subst (λ z → F.Cp y (f m) (f z)) (+-comm n m) (K.up-to y f st n m))
    (F.Cp-tr y p (K.up-to y f st m n)) (lf (m + n))
  ... | inj₁ below-top = cp-carry⁺ (V.cp→CP y below-top) co
  ... | inj₂ above-top = top-read-carry⁺ y ry root co (f m) (lf m , bf m) above-top
top-read-carry⁺ y ry root co (G.lc r c t g)
  ((tg , mono , irr , lt , lg) , lc , bc , bt , bg) (inj₁ ())
top-read-carry⁺ y ry root co (G.lc r c t g)
  ((tg , mono , irr , lt , lg) , lc , bc , bt , bg) (inj₂ p) =
  pow-upN-carry⁺ zero y r c (V.up y t) (λ η e → V.up y (g η e)) lc bc
    (K.top-read-reg y ry root (Y.forget (forget⁺ co)) (G.lc r c t g)
      (tg , mono , irr , lt , lg) (inj₂ p))
    (top-read-carry⁺ y ry root co t (lt , bt) p)
    (λ η e → top-read-carry⁺ y ry root co (g η e) (lg η e , bg η e)
      (F.Cp-tr y p (tg η e)))
top-read-carry⁺ y ry root co (G.em i a) b (inj₁ ())
top-read-carry⁺ y ry root co (G.em i a) b (inj₂ ())
top-read-carry⁺ y ry root co G.top b p = co

guard-read-carry⁺ : ∀ y → Reg y → Below y (V.Ω̂ y) → Carry⁺ (V.Ω̂ y) →
  ∀ η → F.Gd y (V.cO y) η → LglB y η → Carry⁺ (V.up y η)
guard-read-carry⁺ F.zero ry root co η e b = read0-carry⁺ η
guard-read-carry⁺ (F.suc y) ry root co η e b =
  top-read-carry⁺ (F.suc y) ry root co η b (proj₁ e)
guard-read-carry⁺ (F.lim f) ry root co η e b =
  top-read-carry⁺ (F.lim f) ry root co η b (proj₁ e)
guard-read-carry⁺ (F.lc k c t g) ry root co η e b =
  top-read-carry⁺ (F.lc k c t g) ry root co η b (proj₁ e)

Carrys⁺ : ℕ → F.LF → Set
Carrys⁺ zero y = Carry⁺ y
Carrys⁺ (suc n) y = Carrys⁺ n y × Carry⁺ (pow (suc n) y)

carrys-base⁺ : ∀ n y → Carrys⁺ n y → Carry⁺ y
carrys-base⁺ zero y r = r
carrys-base⁺ (suc n) y r = carrys-base⁺ n y (proj₁ r)

carrys-last⁺ : ∀ n y → Carrys⁺ n y → Carry⁺ (pow n y)
carrys-last⁺ zero y r = r
carrys-last⁺ (suc n) y r = proj₂ r

carrys-omega⁺ : ∀ n y → Carrys⁺ (suc n) y → Carry⁺ (V.Ω̂ y)
carrys-omega⁺ zero y r = proj₂ r
carrys-omega⁺ (suc n) y r = carrys-omega⁺ n y (proj₁ r)

carrys-regs⁺ : ∀ n y → Carrys⁺ n y → Regs n y
carrys-regs⁺ zero y r = Y.forget (forget⁺ r)
carrys-regs⁺ (suc n) y r =
  carrys-regs⁺ n y (proj₁ r) , Y.forget (forget⁺ (proj₂ r))
```

read-carrys⁺ 的环境保留 0..n+1 次 Ω 的证书与
Below (suc y) (Ω̂ y)。后继 Raw 坐标使用真子坐标提供下一次环境；
不从单份 Carry⁺ y 假定 Ω 封闭。前提实例在 Instances 的 stages⁺
与 coordinate-suc-root 的实际调用中逐项构造。

```agda
mutual
  read-carrys⁺ : ∀ n y → Below (F.suc y) (V.Ω̂ y) → Carrys⁺ (suc n) y →
    ∀ η → F.Gd y (V.cO y) η → LglB y η → Carrys⁺ n (V.up y η)
  read-carrys⁺ zero y p r = guard-read-carry⁺ y
    (Y.forget (forget⁺ (carrys-base⁺ 1 y r))) (root p) (carrys-omega⁺ zero y r)
  read-carrys⁺ (suc n) F.zero p r η e b = ⊥-elim (no-one-one p)
  read-carrys⁺ (suc n) (F.suc y) p r η e b =
    carry-step⁺ n (F.suc y) refl p r η e b
  read-carrys⁺ (suc n) (F.lim f) p r η e b =
    carry-step⁺ n (F.lim f) refl p r η e b
  read-carrys⁺ (suc n) (F.lc k c t g) p r η e b =
    carry-step⁺ n (F.lc k c t g) refl p r η e b

  carry-step⁺ : ∀ n y → V.cO y ≡ G.top →
    Below (F.suc y) (V.Ω̂ y) → Carrys⁺ (suc (suc n)) y →
    ∀ η → F.Gd y (V.cO y) η → LglB y η → Carrys⁺ (suc n) (V.up y η)
  carry-step⁺ n y eq p r η e b =
    read-carrys⁺ n y p (proj₁ r) η e b ,
    go η b (subst (λ z → F.Cp y z η) eq (proj₁ e))
    where
    as-guard : ∀ η → F.Cp y G.top η → F.Lgl y η → F.Gd y (V.cO y) η
    as-guard η q l = subst (λ z → F.Cp y z η) (sym eq) q , l

    reg : ∀ η → F.Gd y (V.cO y) η → Reg (pow (suc n) (V.up y η))
    reg η e = regs-last (suc n) (V.up y η)
      (read-regs (suc n) y p (carrys-regs⁺ (suc (suc n)) y r) η e)

    go : ∀ η → LglB y η → F.Cp y G.top η → Carry⁺ (pow (suc n) (V.up y η))
    go G.zero b (inj₁ ())
    go G.zero b (inj₂ ())
    go (G.suc a) b (inj₁ ())
    go (G.suc a) b (inj₂ q) =
      pow-node-carry⁺ n (V.up y a) (V.cO (V.up y a)) (V.Ω̂ (V.up y a))
        (λ ζ d → V.up (V.up y a) ζ)
        (reg (G.suc a) (as-guard (G.suc a) (inj₂ q) (proj₁ b)))
        (V.Lgl-cO (V.up y a) , cO-nested (V.up y a)) (go a b q)
        (λ ζ d bz → carrys-last⁺ n (V.up (V.up y a) ζ)
          (read-carrys⁺ n (V.up y a) pa ra ζ d bz))
      where
      ea : F.Gd y (V.cO y) a
      ea = as-guard a q (proj₁ b)
      pa : Below (F.suc (V.up y a)) (V.Ω̂ (V.up y a))
      pa = read-root y p a ea
      ra : Carrys⁺ (suc n) (V.up y a)
      ra = read-carrys⁺ n y p (proj₁ r) a ea b , go a b q
    go (G.lim f) ((st , lf) , bf) (inj₁ ())
    go (G.lim f) ((st , lf) , bf) (inj₂ (m , q)) =
      pow-lim-carry⁺ (suc n) (λ j → V.up y (f j)) term
      where
      term : ∀ j → Carry⁺ (pow (suc n) (V.up y (f j)))
      term j with F.cmpC y (f (j + m))
        (subst (λ z → F.Cp y (f j) (f z)) (+-comm m j) (K.up-to y f st m j))
        (F.Cp-tr y q (K.up-to y f st j m)) (lf (j + m))
      ... | inj₁ below-top = cp-carry⁺ (pow-cp (suc n) (V.cp→CP y below-top)) (proj₂ r)
      ... | inj₂ above-top = go (f j) (lf j , bf j) above-top
    go (G.lc r₀ c t g) b (inj₁ ())
    go (G.lc r₀ c t g) b@((tg , mono , irr , lt , lg) , lc , bc , bt , bg) (inj₂ q) =
      pow-upN-carry⁺ (suc n) y r₀ c (V.up y t) (λ η e → V.up y (g η e))
        lc bc (reg (G.lc r₀ c t g) (as-guard (G.lc r₀ c t g) (inj₂ q) (proj₁ b)))
        (go t (lt , bt) q)
        (λ η e → go (g η e) (lg η e , bg η e) (F.Cp-tr y q (tg η e)))
    go (G.em i a) b (inj₁ ())
    go (G.em i a) b (inj₂ ())
    go G.top b q = proj₂ r
```

全部 cmpC 调用的字面公共界仍是 f(j+m)（零次读回为 f(m+n)）：
两条 Cp 在调用处给出，该项 Lgl 来自输入极限的 lf。
Below 只作结构路径，不送入比较器。这里没有全局比较或新阶段前提。
