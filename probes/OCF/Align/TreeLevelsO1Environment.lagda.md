# O1 / O3：为初始源 Λ 填一个真实表项

**结构性补口；不是完整记号解释。** `TreeLevelsO1Native` 证明空表下没有
极限形目标的 `Tg`。本篇在同一个原始源 Λ 中，使用差树产生合法分支值，
填入一个实际表项，然后构造对应极限形目标的 `tp`。
表项的上界、分支守卫、目标路径和可入性全部实填，不用额外公理。
因此上篇的否定不能被读作“该候选永远不能处理极限形目标”。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO1Environment where

open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Free.Level as F
import OCF.Align.LevelFixCore as L
open import OCF.Align.LevelFixVal using (cO; up; tw; Λ; Legal-tw)
open import OCF.Align.LevelNoKU
  using (Elt; el; gd; _⊑̂_; toU; toUg; module U; self-U)
open import OCF.Align.NoKCertEval using (Ord₀; rdR)
open import OCF.Align.LevelNoKFold using (O)
open import OCF.Align.TreeLevelsO3Shape
open import OCF.Align.TreeLevelsO1Native using (module Initial)

base : Ord₀
base = F.suc F.zero

increment : Difference
increment = tick idle

growing : Ord₀
growing = act (limit (λ _ → increment)) base

r : L.Raw L.zero
r = rdR L.zero growing

guard-r : L.Gd L.zero (cO L.zero) r
guard-r = guard-from-shape L.zero (cO L.zero) base growing
  (inj₁ refl) tt (appended (limit (λ _ → increment)) refl)

c≤r : L.Cp L.zero (cO L.zero) r
c≤r = proj₁ guard-r

legal-r : L.Lgl L.zero r
legal-r = proj₂ guard-r

η : L.Raw L.zero
η = L.G.suc r

Y : L.Raw L.zero
Y = L.G.suc η

e : el L.zero (cO L.zero) ⊑̂ el L.zero η
e = gd (inj₂ c≤r , legal-r)

bound-proof : el L.zero (cO L.zero) ⊑̂ el L.zero Y
bound-proof = gd (inj₂ (inj₂ c≤r) , legal-r)

branches : (x : Elt) → el L.zero (cO L.zero) ⊑̂ x → U.LG
branches = toUg L.zero (cO L.zero) (λ a _ → up L.zero a)

entry : U.Up
entry = U.mkU (el L.zero (cO L.zero)) (U.suc U.zero) branches
  (el L.zero Y) bound-proof

environment : U.Ents
environment = U.∅ U.▸ entry

key-self : U.key entry U.≈ U.key entry
key-self = self-U (tw 2) (Legal-tw 2)

branch-admissible : U.Bel (U.tab environment)
  (el L.zero (cO L.zero)) (U.suc U.zero) branches e
branch-admissible = entry , inj₁ (key-self , refl) , key-self ,
  (inj₁ refl , legal-r)

target : U.LG
target = toU (up L.zero r)

target-path : target U.< toU Λ
target-path = U.lim 2 (U.bra (el L.zero η) e U.zero)

target-admissible : U.Adm (U.tab environment) target-path
target-admissible = branch-admissible , tt

target-in-environment : Initial.Tg environment target
target-in-environment = Initial.tp target-path target-admissible

collapse-at-limit : O (toU Λ) U.tz → O target U.tz
collapse-at-limit body = Initial.ψ environment target-in-environment (λ ()) body
```

`r` 是差树列读回得到的极限，`target` 因而也是极限形。表项的界为
Y = r + 2，所取分支值为 η = r + 1；严格守卫由实际第一位置给出。
本篇没有证明候选运行会自动生产这个表，也没有证明环境对全部子项、
ψ 输出及回灌封闭。后一项仍是完整 ι 缺失的结构，不能由这一个实填
实例外推到所有记号项。
`collapse-at-limit` 已实际调用原折叠，输入仍是原源 Λ 的对象；尚没有
它与某个记号项的序数值比较定理。
