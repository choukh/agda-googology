# 降维打击的检验: 翻译与基本列交换 (验收)

> **验收节.** 记号只出现在本文件、[InaccStrikeNat](InaccStrikeNat.lagda.md) 与 [InaccStrikeAccept](InaccStrikeAccept.lagda.md); 折叠 `FoldS` 不依赖记号. 结论汇总在 [InaccStrike](InaccStrike.lagda.md).
>
> **`Lab.Commute` (§4): 判决在下标类 `N` 上正确 ⟹ 翻译对封闭类 `P` 内每个项逐项带标签.** 证明先对项结构递归 (单步 `stepT`), 再对树递归 (`lab`). 不用项的良基性, 不读 `isOTᵉ`, 没有地板, 没有深度, 不按阶段分情形. 非平凡的两种情形: `pen` (`penΩ`) 与 `rise` (`chain-lem`) 都只用单步的 Ω 分支条款.
>
> **前提与 InaccTreeAccept 的 `Agree` 不同.** `Funext` 是模块参数. `GV` 比 `Agree` 强两点: 搬运 `b` 必须作用为恒等 (否则为假, 见 `b-bad`), 路径必须字面命中 (`at i r ≡ j`, 不是 `≅`; 这是证明的便利, 是否必需未判定). 同时它只需要在下标对 (`ν`, `u`) 上成立, 比全部项对弱. 项 `P` 的封闭性 (`P-fs`, `P-pr`) 是假设; 对标准形这就是 `OTFS_thm`, 本仓库没有.
>
> **前提可满足.** [InaccStrikeNat](InaccStrikeNat.lagda.md): 判决 `ver`, 下标为自然数, 无条件.
>
> 对象是同形的 `S`, 不是 `Tr.⟦_⟧`: 后者把 `low` 写在匿名 `where` 里, 无法对开放的树陈述引理. 两者的等同只有有限检验 (`u-*` 与本文件的比较都走 `diff`), 没有定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccStrikeCommute where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong-app; subst)

open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccStrikeBase
open import OCF.Align.InaccTreeAccept using (LabN; l0; l1; lω)
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; cof; cofP; cofA; cofψ0; cofψ₊; pred; pred-<; fsn; fsn↓; fsn↓₊; fsn↓c; fsn↓0; rep↓; fsT; fsT0; fsT₊; fsTc; fsT↓; fsT↓-trm; γT; γ↓; γ↓-trm; Ωt; 𝟏; sucT; cmpᵀ; cmpᴾ; Cmp; lt; eq; gt; trm; dec) renaming (ψ to ψᵗ)
```

## §1 项的纯语法事实

`sc`: `a < b` 时 `a+1 ≤ b`, 否则 `a+1 > b`. 不要求标准形: `𝟏` 是最小的主项.

```agda
SC : Cmp → Cmp → Set
SC lt gt = ⊥
SC lt _  = ⊤
SC _  gt = ⊤
SC _  _  = ⊥

sc : ∀ a b → SC (cmpᵀ a b) (cmpᵀ (sucT a) b)
sc [] [] = tt
sc [] (ψᵗ [] [] ∷ [])          = tt
sc [] (ψᵗ [] [] ∷ _ ∷ _)       = tt
sc [] (ψᵗ [] (_ ∷ _) ∷ ys)     = tt
sc [] (ψᵗ (_ ∷ _) _ ∷ ys)      = tt
sc (x ∷ xs) [] = tt
sc (x ∷ xs) (y ∷ ys) with cmpᴾ x y
... | lt = tt
... | gt = tt
... | eq = sc xs ys

cofA-nz : ∀ u c → cofA u c ≡ c0 → ⊥
cofA-nz u c0 ()
cofA-nz u c1 ()
cofA-nz u cω ()
cofA-nz u (cΩ μ) e with cmpᵀ (sucT μ) u
cofA-nz u (cΩ μ) () | lt
cofA-nz u (cΩ μ) () | eq
cofA-nz u (cΩ μ) () | gt

cof-nz  : ∀ x xs → cof (x ∷ xs) ≡ c0 → ⊥
cof-nz (ψᵗ u (y ∷ ys)) [] e = cofA-nz u (cof (y ∷ ys)) e
cof-nz (ψᵗ [] []) [] ()
cof-nz (ψᵗ (w ∷ ws) []) [] e = go (cof (w ∷ ws)) refl e where
  go : ∀ c → cof (w ∷ ws) ≡ c → cofψ0 (w ∷ ws) c ≡ c0 → ⊥
  go c0 p _ = cof-nz w ws p
  go c1 p ()
  go cω p ()
  go (cΩ μ) p ()
cof-nz x (y ∷ ys) e = cof-nz y ys e
```

## §2 翻译与判决的规格

`S` 是 InaccTreeAccept 的 `⟦_⟧` 去掉 `up` 后的形式: 和用 `addS`, `ψ_u(w)` 是目标 `L u` 的折叠. (`Tr.⟦_⟧` 的 `addU` 把 `low` 写在匿名 `where` 里, 无法对开放的树陈述关于它的引理, 所以这里用同形的 `S`.) `GV` 是判决的规格: `lt` 要 `pen`, 路径字面命中, 搬运 `b` 作用为恒等; 其余要 `rise`.

```agda
module Tr (D : Oracle) where
  open FoldS D

  S  : T → St
  Sᴾ : PT → St
  L  : T → Lv
  S []       = zero
  S (x ∷ xs) = addS (Sᴾ x) (S xs)
  Sᴾ (ψᵗ u w) = strip (ψS {L u} (S w))
  L u = toLvS (S u)

GV : ∀ {j i} → Cmp → Verdict j i → Set
GV {j} {i} lt (pen r b) = (at i r ≡ j) × (∀ y → strip (b y) ≡ strip y)
GV lt rise      = ⊥
GV eq (pen r b) = ⊥
GV eq rise      = ⊤
GV gt (pen r b) = ⊥
GV gt rise      = ⊤

rise-of : ∀ {j i} v (V : Verdict j i) → GV v V → SC v gt → V ≡ rise
rise-of lt V g ()
rise-of eq rise g s = refl
rise-of gt rise g s = refl

record PenOf {j i} (V : Verdict j i) : Set where
  field
    rr : Pre i
    bb : Ordᴸ (at i rr) → Ordᴸ j
    vq : V ≡ pen rr bb
    lb : at i rr ≡ j
    sb : ∀ y → strip (bb y) ≡ strip y

pen-of : ∀ {j i} (V : Verdict j i) → GV lt V → PenOf V
pen-of (pen r b) (l , s) = record { rr = r ; bb = b ; vq = refl ; lb = l ; sb = s }

lt-of : ∀ v → SC v lt → v ≡ lt
lt-of lt s = refl
lt-of eq ()
lt-of gt ()

lt-of′ : ∀ v → SC v eq → v ≡ lt
lt-of′ lt s = refl
lt-of′ eq ()
lt-of′ gt ()

-- 单步的形状: F 是 ω-基本列, H 是 Ω-基本列
module Step (D : Oracle) where
  open Tr D public
  open FoldS D public

  StepF : T → Cof → (ℕ → T) → (T → T) → Set
  StepF t c0     F H = S t ≡ zero
  StepF t c1     F H = S t ≡ suc (S (pred t))
  StepF t cω     F H = S t ≡ lim (λ n → S (F n))
  StepF t (cΩ ν) F H = Σ Lv λ ℓ → (ℓ ≡ L ν) × Σ (Ordᴸ ℓ → St) λ f →
                       (S t ≡ limᵢ ℓ f) × (∀ y η → strip y ≡ S η → f y ≡ S (H η))

-- Q: 跑单步的项; N: 下标类, 判决只需在 N 上正确 (N 可以远小于 Q)
record ClQ (Q N : T → Set) : Set where
  field
    cl-tl  : ∀ {x xs} → Q (x ∷ xs) → Q xs
    cl-sub : ∀ {u w xs} → Q (ψᵗ u w ∷ xs) → Q u
    cl-arg : ∀ {u w xs} → Q (ψᵗ u w ∷ xs) → Q w
    cl-idx : ∀ {u w xs} → Q (ψᵗ u w ∷ xs) → N u
    cl-nu  : ∀ {w ν} → Q w → cof w ≡ cΩ ν → N ν
```

## §3 单步: 和、Ω 叶、后继与极限参数

```agda
module Main (fe : Funext) (D : Oracle) (Q N : T → Set) (cl : ClQ Q N)
            (agr : ∀ u v → N u → N v → GV (cmpᵀ u v) (D (Tr.L D u) (Tr.L D v))) where
  open Step D
  open Ext fe
  open ClQ cl

  sumS : ∀ x y ys c → cof (y ∷ ys) ≡ c → StepF (y ∷ ys) c (fsn (y ∷ ys)) (fsT (y ∷ ys)) →
         StepF (x ∷ y ∷ ys) c (fsn (x ∷ y ∷ ys)) (fsT (x ∷ y ∷ ys))
  sumS x y ys c0     be ih = ⊥-elim (cof-nz y ys be)
  sumS x y ys c1     be ih = cong (addS (Sᴾ x)) ih
  sumS x y ys cω     be ih = cong (addS (Sᴾ x)) ih
  sumS x y ys (cΩ ν) be (ℓ , e , f , q , h) =
    ℓ , e , (λ y′ → addS (Sᴾ x) (f y′)) , cong (addS (Sᴾ x)) q , λ y′ η p → cong (addS (Sᴾ x)) (h y′ η p)

  leaf : ∀ w ws c (be : cof (w ∷ ws) ≡ c) → StepF (w ∷ ws) c (fsn (w ∷ ws)) (fsT (w ∷ ws)) →
         StepF (ψᵗ (w ∷ ws) [] ∷ []) (cofψ0 (w ∷ ws) c) (λ n → trm (fsn↓0 w ws c be n)) (fsT0 (w ∷ ws) c)
  leaf w ws c0     be ih = ⊥-elim (cof-nz w ws be)
  leaf w ws c1     be ih =
    L (pred (w ∷ ws)) , refl , strip , cong (λ z → strip (Ω (toLvS z))) ih , λ y η p → p
  leaf w ws cω     be ih = cong (λ z → strip (Ω (toLvS z))) ih
  leaf w ws (cΩ ν) be (ℓ , e , f , q , h) =
    ℓ , e , (λ y → strip (Ω (toLvS (f y)))) , cong (λ z → strip (Ω (toLvS z))) q ,
    λ y η p → cong (λ z → strip (Ω (toLvS z))) (h y η p)

  rep-lem : ∀ u p {a} (a′< : p E.<ᵀ a) n →
            strip (iter (ψS {L u} (S p) +_) zero n) ≡ S (trm (rep↓ u a′< n))
  rep-lem u p a′< zero    = refl
  rep-lem u p a′< (suc n) =
    trans (strip-add (ψS {L u} (S p)) (σ-id (L u)) (iter (ψS {L u} (S p) +_) zero n))
          (cong (addS (strip (ψS {L u} (S p)))) (rep-lem u p a′< n))
```

## §4 单步: 规则 6 (γ 与 iter)、规则 5 (fsT 与分支), 以及 `Commute`

链的交换 `chain-lem` 只用 `h` (分支 = Ω-基本列) 一条; 穿透只多用判决的 `sb`.

```agda
  suc-inj : ∀ {a b : St} → sucS a ≡ sucS b → a ≡ b
  suc-inj refl = refl
  lim-inj : ∀ {a b : ℕ → St} → limS a ≡ limS b → a ≡ b
  lim-inj refl = refl

  module Chain (u b ν : T) (f : Ordᴸ (L ν) → St)
               (h : ∀ y η → strip y ≡ S η → f y ≡ S (fsT b η)) where
    chain : ℕ → Ordᴸ (L ν)
    chain n = iter (λ x → ψS {L ν} (f x)) (Ω (L ν)) n

    chain-lem : ∀ n → strip (chain n) ≡ S (γT b ν n)
    chain-lem zero    = refl
    chain-lem (suc n) = cong (λ z → strip (ψS {L ν} z)) (h (chain n) (γT b ν n) (chain-lem n))

  penΩ : ∀ u y ys ν (qu : N u) (qν : N ν) → cmpᵀ ν u ≡ lt →
         StepF (y ∷ ys) (cΩ ν) (fsn (y ∷ ys)) (fsT (y ∷ ys)) →
         StepF (ψᵗ u (y ∷ ys) ∷ []) (cΩ ν) (λ _ → []) (λ η → ψᵗ u (fsT (y ∷ ys) η) ∷ [])
  penΩ u y ys ν qu qν lv (_ , refl , f , q , h) =
    at (L u) (PenOf.rr P) , PenOf.lb P ,
    (λ y′ → strip (ψS {L u} (f (PenOf.bb P (outL (L u) (PenOf.rr P) (intoL (L u) (PenOf.rr P) y′)))))) ,
    trans (cong (λ z → strip (ψS {L u} z)) q) (cong (λ V → strip (dispS f V)) (PenOf.vq P)) ,
    λ y′ η p → trans
      (cong (λ z → strip (ψS {L u} (f (PenOf.bb P z)))) (out-into (L u) (PenOf.rr P) y′))
      (cong (λ z → strip (ψS {L u} z)) (h (PenOf.bb P y′) η (trans (PenOf.sb P y′) p)))
    where
      V₀ = D (L ν) (L u)
      gv : GV lt V₀
      gv = subst (λ v → GV v V₀) lv (agr ν u qν qu)
      P : PenOf V₀
      P = pen-of V₀ gv

  argΩ : ∀ u y ys ν (be : cof (y ∷ ys) ≡ cΩ ν) (qu : N u) (qν : N ν) m → cmpᵀ (sucT ν) u ≡ m →
         StepF (y ∷ ys) (cΩ ν) (fsn (y ∷ ys)) (fsT (y ∷ ys)) →
         StepF (ψᵗ u (y ∷ ys) ∷ []) (cofψ₊ u ν m) (λ n → trm (fsn↓c u y ys ν be m n)) (fsTc u (y ∷ ys) ν m)
  argΩ u y ys ν be qu qν gt em (_ , refl , f , q , h) =
    trans (cong (λ z → strip (ψS {L u} z)) q)
    (trans (cong (λ V → strip (dispS f V))
                 (rise-of (cmpᵀ ν u) (D (L ν) (L u)) (agr ν u qν qu)
                          (subst (SC (cmpᵀ ν u)) em (sc ν u))))
           (cong limS (fe λ n →
             trans (cong (λ z → strip (ψS {L u} z)) (h (chain n) (γT b ν n) (chain-lem n)))
                   (cong (λ z → strip (ψS {L u} (S (fsT b z)))) (sym (γ↓-trm b ν be n))
                    ▸ cong (λ z → strip (ψS {L u} (S z))) (sym (fsT↓-trm b be (dec (γ↓ b ν be n))))))))
    where
      b = y ∷ ys
      open Chain u b ν f h
      _▸_ : ∀ {A : Set} {p q r : A} → p ≡ q → q ≡ r → p ≡ r
      _▸_ = trans
  argΩ u y ys ν be qu qν lt em ih = penΩ u y ys ν qu qν (lt-of _ (subst (SC (cmpᵀ ν u)) em (sc ν u))) ih
  argΩ u y ys ν be qu qν eq em ih = penΩ u y ys ν qu qν (lt-of′ _ (subst (SC (cmpᵀ ν u)) em (sc ν u))) ih
```

```agda
  arg : ∀ u y ys c (be : cof (y ∷ ys) ≡ c) → N u → Q (y ∷ ys) →
        StepF (y ∷ ys) c (fsn (y ∷ ys)) (fsT (y ∷ ys)) →
        StepF (ψᵗ u (y ∷ ys) ∷ []) (cofA u c) (λ n → trm (fsn↓₊ u y ys c be n)) (fsT₊ u (y ∷ ys) c)
  arg u y ys c0     be qu qb ih = ⊥-elim (cof-nz y ys be)
  arg u y ys c1     be qu qb ih =
    trans (cong (λ z → strip (ψS {L u} z)) ih)
          (cong limS (fe (rep-lem u (pred (y ∷ ys)) (pred-< (y ∷ ys) be))))
  arg u y ys cω     be qu qb ih = cong (λ z → strip (ψS {L u} z)) ih
  arg u y ys (cΩ ν) be qu qb ih = argΩ u y ys ν be qu (cl-nu qb be) (cmpᵀ (sucT ν) u) refl ih

  stepT : ∀ t → Q t → StepF t (cof t) (fsn t) (fsT t)
  stepP : ∀ x → Q (x ∷ []) → StepF (x ∷ []) (cofP x) (fsn (x ∷ [])) (fsT (x ∷ []))

  stepT []          q = refl
  stepT (x ∷ [])    q = stepP x q
  stepT (x ∷ y ∷ ys) q = sumS x y ys (cof (y ∷ ys)) refl (stepT (y ∷ ys) (cl-tl q))

  stepP (ψᵗ [] [])       q = refl
  stepP (ψᵗ (w ∷ ws) []) q = leaf w ws (cof (w ∷ ws)) refl (stepT (w ∷ ws) (cl-sub q))
  stepP (ψᵗ u (y ∷ ys))  q = arg u y ys (cof (y ∷ ys)) refl (cl-idx q) (cl-arg q) (stepT (y ∷ ys) (cl-arg q))

  -- 单步之后对树递归: 项的良基性完全不需要
  module Lab (P : T → Set) (P⊂Q : ∀ {t} → P t → Q t)
             (P-fs : ∀ {t} → P t → cof t ≡ cω → ∀ n → P (fsn t n))
             (P-pr : ∀ {t} → P t → cof t ≡ c1 → P (pred t))
             (P-nc : ∀ {t ν} → P t → cof t ≡ cΩ ν → ⊥) where

    lab : ∀ x t → x ≡ S t → P t → LabN (dz x) t
    lab zero t e p with cof t in ce | stepT t (P⊂Q p)
    ... | c0   | s = l0 ce
    ... | c1   | s with () ← trans e s
    ... | cω   | s with () ← trans e s
    ... | cΩ ν | s = ⊥-elim (P-nc p ce)
    lab (suc a) t e p with cof t in ce | stepT t (P⊂Q p)
    ... | c0   | s with () ← trans e s
    ... | c1   | s = l1 ce (lab a (pred t) (suc-inj (trans e s)) (P-pr p ce))
    ... | cω   | s with () ← trans e s
    ... | cΩ ν | s = ⊥-elim (P-nc p ce)
    lab (lim f) t e p with cof t in ce | stepT t (P⊂Q p)
    ... | c0   | s with () ← trans e s
    ... | c1   | s with () ← trans e s
    ... | cω   | s = lω ce (λ n → lab (f n) (fsn t n) (cong-app (lim-inj (trans e s)) n) (P-fs p ce n))
    ... | cΩ ν | s = ⊥-elim (P-nc p ce)
    lab (limᵢ ℓ f) t e p with cof t in ce | stepT t (P⊂Q p)
    ... | c0   | s with () ← trans e s
    ... | c1   | s with () ← trans e s
    ... | cω   | s with () ← trans e s
    ... | cΩ ν | s = ⊥-elim (P-nc p ce)

    Commute : ∀ t → P t → LabN (dz (S t)) t
    Commute t p = lab (S t) t refl p
```
