# 原有限分量下降的分层结构关系接口

反馈不能把任意raw坐标的点态Same当作函数外延。本接口按实际坐标层
递归定义逻辑关系：Ω的两个分支只须对已经相关的低层坐标给出相关树。
高层关系不预设全raw分支Same；到Native0时坐标全为Cd，才可取出Same。
所有层比较仍由各自字面公共界中的路径给出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteRunIf where
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same)
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
import OCF.Align.BoundedNativeFloor as N
import OCF.Align.BoundedNativeFoldRun as R

-- Q只是一对同类型坐标的结构证书，不提供三歧、判等或值比较。
data TreeRel (S : KS) (Q : ∀ κ → E S κ → E S κ → Set) :
  HB S → HB S → Set where
  rz : TreeRel S Q hz hz
  rs : ∀ {a b} → TreeRel S Q a b → TreeRel S Q (hs a) (hs b)
  rl : ∀ {f g} → (∀ n → TreeRel S Q (f n) (g n)) → TreeRel S Q (hl f) (hl g)
  ro : ∀ {κ f g} → (∀ x y → Q κ x y → TreeRel S Q (f x) (g y)) →
    TreeRel S Q (hΩ κ f) (hΩ κ g)

Rel : ∀ c → HB (Native c) → HB (Native c) → Set
Coord : ∀ c κ → E (Native c) κ → E (Native c) κ → Set
Rel c = TreeRel (Native c) (Coord c)
Coord hz (inj₁ ())
Coord hz (inj₂ _) = Same
Coord (hs c) (inj₁ κ) = Coord c κ
Coord (hs c) (inj₂ _) = Rel c
Coord (hl f) (n , κ) = Coord (f n) κ

-- 原source里固定一个分量；不是另造输入树。
placed : ∀ c → HB (Native c) → HB Source
placed c a = ι (inj₂ c) a

at : ∀ n m {B} → LgB B → num n ⊲ B → num m ⊲ B →
  HB (Native (num n)) → HB (Native (num m))
at n m {B} lB pc pt a = R.fold B lB (num m) pt (placed (num n) a)
  (N.component-path (num n) B pc a)

record ComponentBridge : Set₁ where
  field
    coherent : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
      (pc : num n ⊲ B) (pc′ : num n ⊲ B′)
      (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
      {a b} → Rel (num n) a b →
      Rel (num m) (at n m lB pc pt a) (at n m lB′ pc′ pt′ b)
```

接口中的coherent是待实现目标，不是本篇的假设定理或已有实例。
原floor全有限n的Rel自相关将在独立文件构造；不能以仅记录存在收工。
Rel不是合法性证书，也不暗示原输出LgB。它只处理结构同余及回灌可替换性。
