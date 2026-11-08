# 跨签名保留节点的数据尚不足以给分支

对定稿的 `TowerWorldIf.Keep` 做两个最小实例检查。
它们不否定该记录可满足，也不否定扩大后的折叠接口；恰好说明仅凭
坐标反变和合法坐标搬运不能得到可入搬运或分支世界对应。
所有世界关系都是字面相等，不比较无公共上界的下标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerObstructionKeep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import OCF.Lean.TowerWorldIf

-- 世界没有隐含的全序；只可沿给定相等证据移动。
sig : (Admission : Set) → (ℕ → ℕ) → Signature
sig Admission step = record
  { World = ℕ
  ; _≤w_ = _≡_
  ; reflw = λ _ → refl
  ; transw = trans
  ; Kind = ⊤
  ; Coord = λ _ → ⊤
  ; LegalCoord = λ _ _ → ⊤
  ; Admit = λ _ _ _ → Admission
  ; admitted-legal = λ _ → tt
  ; next = λ w _ _ _ → step w }

source target : Signature
source = sig ⊥ (λ w → w)
target = sig ⊤ (λ w → w)

empty-keep : Keep source target
empty-keep = record
  { world = λ w → w
  ; kind = λ k → k
  ; coordinate = λ _ c → c
  ; legal-coordinate = λ _ _ l → l }

-- 目标世界就是源世界本身，公共世界证据为 refl。
no-admission-pull :
  (∀ w k c → Signature.Admit target (Keep.world empty-keep w) (Keep.kind empty-keep k) c →
    Signature.Admit source w k (Keep.coordinate empty-keep k c)) → ⊥
no-admission-pull pull = pull zero tt tt tt

stay move : Signature
stay = sig ⊤ (λ _ → zero)
move = sig ⊤ (λ _ → suc zero)

next-keep : Keep stay move
next-keep = record
  { world = λ w → w
  ; kind = λ k → k
  ; coordinate = λ _ c → c
  ; legal-coordinate = λ _ _ l → l }

-- 此次反向可入已具备，仍不能推出两边 next 的关系。
admission-pull : ∀ w k c → Signature.Admit move w k c → Signature.Admit stay w k c
admission-pull w k c a = a

no-next-alignment :
  Signature._≤w_ move
    (Keep.world next-keep (Signature.next stay zero tt tt tt))
    (Signature.next move (Keep.world next-keep zero) tt tt tt) → ⊥
no-next-alignment ()
```

前提可满足：两个 `Keep` 都给出完整实例；第二例连可入搬运都有。
第一例没有可入的源分支，不影响签名与树本身可满足，`Trees.zero`
在每个世界都有。第二例的两个源/目标出发世界字面相同。

翻译账：无新树构造子；只检测保留节点所需的数据方向。下一步若要
定义跨签名递归转换，至少须说明在目标未来世界与坐标处怎样选源未来
世界、源可入证据，并把递归结果送入目标的 next 世界。
这个“至少”是依赖类型检查所显露的义务，不是所有可能折叠的穷尽定理。

## 两边都有 NextUp，仍缺跨签名的 next 对齐

上一例只检测原始 Signature。这里进一步满足前缀运算实际使用的
`NextUp`：源 next = 后继，目标 next = 恒等，世界序为自然数通常的 ≤。
每边自己的进入均增长，但跨签名所需的方向仍不成立。

```agda
import Data.Nat as N
import Data.Nat.Properties as NP

up-sig : (step : ℕ → ℕ) → Signature
up-sig step = record
  { World = ℕ
  ; _≤w_ = N._≤_
  ; reflw = λ _ → NP.≤-refl
  ; transw = NP.≤-trans
  ; Kind = ⊤ ; Coord = λ _ → ⊤ ; LegalCoord = λ _ _ → ⊤
  ; Admit = λ _ _ _ → ⊤ ; admitted-legal = λ _ → tt
  ; next = λ w _ _ _ → step w }

rising stationary : Signature
rising = up-sig suc
stationary = up-sig (λ w → w)

rising-up : NextUp rising
rising-up = record { up = λ w k c a → NP.n≤1+n w }

stationary-up : NextUp stationary
stationary-up = record { up = λ w k c a → NP.≤-refl }

up-keep : Keep rising stationary
up-keep = record
  { world = λ w → w ; kind = λ k → k
  ; coordinate = λ _ c → c ; legal-coordinate = λ _ _ l → l }

up-admission-pull : ∀ w k c → Signature.Admit stationary w k c → Signature.Admit rising w k c
up-admission-pull w k c a = a

no-next-alignment-up :
  Signature._≤w_ stationary
    (Keep.world up-keep (Signature.next rising zero tt tt tt))
    (Signature.next stationary (Keep.world up-keep zero) tt tt tt) → ⊥
no-next-alignment-up ()
```

此例的出发世界、目标未来世界均为 0，公共界为 0，有两条自反证据；
相矛盾的是进入之后源世界 1 到目标世界 0 的方向。
没有要求比较任意裸下标。两个 NextUp 与 Keep、可入搬运已同时给出，
因此该缺口即使在本轮前缀运算的条件下仍存在。
