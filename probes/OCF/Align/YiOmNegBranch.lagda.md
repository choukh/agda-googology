# YiOmNeg 第 4 项：目标在某一支里，树是 `top`

**判决：编译定理。** 最小记录 `TopBranch` (目标在 `tw 2` 的位置 `q` 上时，`top` 的保留像的各支满足保留律，且只对与目标有路径相连的支要求) 推出 LPO；不用折叠律。
目标取第 `coordᴸ α` 支的根，守卫是闭的相关证明；用到的分支只有坐标 2 的那一支。在排中律的实例 `Locate` 下记录有模型。
否定的是 "保留律对 `tw 2` 的一切位置上的目标成立"，律的定义域取 `Link` 也一样；不否定目标是第 0 层、`tw 2` 自己或主干位置的折叠。接口 [YiOmIf](YiOmIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmNegBranch where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiOmIf
open import OCF.Align.YiIrrNegWide using (Found; seen; seen-found; seen-hit; flag; dense)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiLvNegKeep
  using (LPO; Locate; coordᴸ; levelᴸ; found→one; kept-node; kept-at; below-one; plus-one)
open import OCF.Align.YiRawNegOmega using (K₂ω; br; qα; Link; placeᵒ; placeᵒ-kept)
open import OCF.Align.YiLvFoldAdd using (plus)
open import OCF.Align.YiOmNegTop using (e₂)
```

## 1 最小记录

目标在位置 `q` 上，层号 `lev K₂ω q`。`top` 读回是 `tw 3`；目标层里有层号 0 的位置时，根在目标之下，输出是保留结点，
它的分支函数定义在 `tw 3` 根上的整个分支域上：`branch q η e` 是第 `η` 支折到目标层的像。第 `suc s` 支是层号 `read0 s` 的结点，
保留律 (`YiRawIf.RawFold.keep-law` 的同形) 要求：这个层号在目标层的某个位置上时，像是保留结点，槽位上的层号是它。
律只对与目标有路径相连的支要求 (`YiRawNegOmega.Link`，上一轮给律定的定义域)：前提越强，律越容易满足。
记录不写保留结点怎样装进输出 (那要沿层号相等搬运下界的类型)，只写分支与它的保留律。

```agda
record TopBranch : Set where
  field
    branch : (q : Pre K₂ω) (η : R) → .(Gd zero raw1 η) → Raw (lev K₂ω q)
    branch-keep : ∀ q s (e : Gd zero raw1 (G.suc s)) →
      Link (br (G.suc s) e (inj₁ tt)) q → At (lev K₂ω q) (read0 s) →
      Kept (lev K₂ω q) (read0 s) (branch q (G.suc s) e)
```

目标 `qα α` 的层号 `levelᴸ α` 里总有层号 0 的位置，所以 "根在目标之下" 对一切 `α` 成立，不要见证。

```agda
root-below : ∀ α → At (lev K₂ω (qα α)) zero
root-below α = below-one (one +ʳ dense α) (plus-one (dense α))
```

## 2 记录推出 LPO

坐标 2 的那一支是层号 1 的结点。它在 `levelᴸ α` 的位置上当且仅当 `α` 有真值；有真值时坐标 2 还是 `coordᴸ α` 的字面第一位置，所以这一对有路径相连 (`found→link`)。
像是数据：不是结点，就没有真值；是结点，槽位 `(n , r)` 是数据，"`seen α n` 为真" 可判定，为假时这个槽位上的层号不是 1，与保留律矛盾。

```agda
slot-test : ∀ x .(nb : Nested zero (one +ʳ flag x)) (r : Pre (up zero (one +ʳ flag x) nb)) →
  (x ≡ true) ⊎ (lev (up zero (one +ʳ flag x) nb) r ≡ suc zero → ⊥)
slot-test true nb r = inj₁ refl
slot-test false nb (inj₁ _) = inj₂ (λ ())
slot-test false nb (inj₂ ())

decide : ∀ α (y : Raw (levelᴸ α)) →
  (Found α → Kept (levelᴸ α) (suc zero) y) → Found α ⊎ (Found α → ⊥)
decide α (G.lc (n , r) c t g) kl with slot-test (seen α n) _ r
... | inj₁ p = inj₁ (seen-found α n p)
... | inj₂ no = inj₂ (λ s → no (kept-at (levelᴸ α) (suc zero) (n , r) c t g (kl s)))
decide α G.zero kl = inj₂ (λ s → kept-node _ _ G.zero (kl s))
decide α (G.suc y) kl = inj₂ (λ s → kept-node _ _ (G.suc y) (kl s))
decide α (G.lim f) kl = inj₂ (λ s → kept-node _ _ (G.lim f) (kl s))
decide α (G.em i T) kl = inj₂ (λ s → kept-node _ _ (G.em i T) (kl s))
decide α G.top kl = inj₂ (λ s → kept-node _ _ G.top (kl s))

two-flag : ∀ x → x ≡ true → Cp zero (G.suc one) (one +ʳ flag x)
two-flag .true refl = inj₁ refl

found→link : ∀ α → Found α → Cp zero (G.suc one) (coordᴸ α)
found→link α (n , p) = inj₂ (inj₂ (n , two-flag (seen α n) (seen-hit α n p)))

top-branch→lpo : TopBranch → LPO
top-branch→lpo F α = decide α (branch (qα α) (G.suc one) e₂)
  (λ s → branch-keep (qα α) one e₂ (inj₁ (found→link α s)) (found→one α s))
  where open TopBranch F
```

## 3 记录不可反驳

判定 "`k` 是不是 `m` 的某个位置上的层号" 的神谕 (排中律的实例，`YiLvNegKeep.Locate`) 给出模型。

```agda
branchᵒ : Locate → (q : Pre K₂ω) → R → Raw (lev K₂ω q)
branchᵒ orc q (G.suc s) = placeᵒ (lev K₂ω q) (read0 s) (orc (lev K₂ω q) (read0 s))
branchᵒ orc q G.zero = G.zero
branchᵒ orc q (G.lim f) = G.zero
branchᵒ orc q (G.lc () c t g)
branchᵒ orc q (G.em () T)
branchᵒ orc q G.top = G.zero

oracle-branch : Locate → TopBranch
oracle-branch orc = record
  { branch = λ q η e → branchᵒ orc q η
  ; branch-keep = λ q s e l a →
      placeᵒ-kept (lev K₂ω q) (read0 s) (orc (lev K₂ω q) (read0 s)) a }
```

## 4 边界与走查

目标层是 1 时不碰这堵墙：层号 1 的位置上只有层号 0，"结点层是不是 0" 看头就能判定 (`at-one-dec`)。墙是否只在目标层含极限层号的位置时出现，没有证。

```agda
at-one-dec : ∀ k → At (suc zero) k ⊎ (At (suc zero) k → ⊥)
at-one-dec zero = inj₁ (inj₁ tt , refl)
at-one-dec (suc k) = inj₂ λ { (inj₁ _ , ()) ; (inj₂ () , e) }
at-one-dec (lim f) = inj₂ λ { (inj₁ _ , ()) ; (inj₂ () , e) }
at-one-dec (lc k c w b t g) = inj₂ λ { (inj₁ _ , ()) ; (inj₂ () , e) }
```

规范的链何时问到这种目标 (走查，判断；折叠在 `tw 2` 上还没有，下面两条只是走查用到的编译事实)。链 `ξ₀ = top`，`ξ₁ = top + Φ(top)`。
若 `Φ(top)` 取保留的写法 ([YiOmNegTop](YiOmNegTop.lagda.md))，它在坐标 `suc s` (`s` 不是零) 的那一支是层号非零的保留结点，槽位只能在某一支里 (`own-in-branch`)；
加法把 `top` 放到这个结点之下的每个零叶上 (`plus-node`, `plus-leaf`)。把 `ξ₁` 折到第 0 层时这个结点在目标之上，它的链由 "各支折到结点自己那一层" 推进
(`YiRawFold.own` 的规则)，目标就在那一支里，被折的树里有叶 `top`。所以按这个走查，这一行在第二个链点就会被问到，目标是闭的链点；这是判断，不是定理。

```agda
own-in-branch : ∀ q → (lev K₂ω q ≡ zero → ⊥) →
  Σ R λ η → Σ (Gd zero raw1 η) λ e → Σ (Pre (read0 η)) λ r → q ≡ br η e r
own-in-branch (inj₁ (inj₁ _)) nz = ⊥-elim (nz refl)
own-in-branch (inj₂ (inj₁ (inj₁ _))) nz = ⊥-elim (nz refl)
own-in-branch (inj₂ (inj₂ (η , e , r))) nz = η , e , r , refl

plus-node : ∀ x q c t g → plus K₂ω x (G.lc q c t g) ≡
  G.lc q c (plus K₂ω x t) (λ η e → plus K₂ω x (g η e))
plus-node x q c t g = refl

plus-leaf : ∀ x → plus K₂ω x G.zero ≡ x
plus-leaf x = refl
```

## 范围与归类

陈述里有折叠的一行 (分支的像与保留律)，没有值；失败的字段是保留律交出的槽位 (`Kept` 里的位置与层号方程)。
机制与 `YiRawNegOmega.dec-at→lpo`、`YiLvNegKeep.bare-way→lpo` 相同：判定固定层号 1 是否出现在另一支的极限层号 `levelᴸ α` 的位置上；
这里的判定由保留结点的头与槽位读出，前提比 `keep-fold→wlpo` 少 (不要折叠律)，结论强 (LPO)，探针树从人造结点换成 `top` 自己的一支。
与 `no-compare-tw2` 不是同一机制：那里没有折叠，失败的是 `Tri` 的三个构造子都无居留，位置对没有路径相连；这里层号在目标层的位置上时位置对总有路径相连，
比较本身成立 (`compare-link`)，拿不到的是 "相连与否" 这一位：分支的像由坐标与目标算出，律的前提里的路径它读不到。
它不是 `Barrier.barrier` 的字面实例：那里的前提是一个带精确嵌入、顶元与有界三歧的下标类型，本篇的前提是保留律，没有由它构造这样的下标类型。
与守卫相关还是无关没有关系：目标位置与坐标 2 的守卫都是闭的相关证明，证明里没有无关参数的消去。
目标族 `qα α` 是不是规范的链走到的坐标，没有判定；对单个闭的目标，见 [YiOmNegBranchFixed](YiOmNegBranchFixed.lagda.md) (条件定理)。
