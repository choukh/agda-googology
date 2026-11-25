# YiWall 条件验收：只读树的 gt 行与 WLPO

**条件。** 本篇不向成品或证书加入函数外延。已证明的结论是：
只读树的两个恒分支 gt 检验，加上“空守卫域上的两个根读数相等”，
推出 WLPO；Funext 足以提供后一前提。**没有证明去掉此前提的蕴涵。**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiWallConditional where

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; false; true)
open import Data.Bool.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import OCF.Align.LevelFixCore as F
import OCF.Align.YiK2Base as A
import OCF.Align.YiK2bBase as B
import OCF.Align.YiCarry as C
import OCF.Align.YiK2cIrr as I
import OCF.Align.YiWallTree as T
open F using (module G)

Funext : Set₁
Funext = Extensionality 0ℓ 0ℓ

-- 只要求空守卫域上的这两个恒分支根，远小于任意函数外延的声明。
EmptyAgreement : (F.LF → A.R) → Set
EmptyAgreement run = ∀ c → (F.Lgl F.zero c → ⊥) →
  run (T.node c false) ≡ run (T.node c true)

funext→empty-agreement : Funext → ∀ run → EmptyAgreement run
funext→empty-agreement fe run c nc = cong run
  (cong (λ g → F.lc F.zero c T.unitLF g)
    (fe (λ η → fe (λ e → ⊥-elim
      (nc (F.lgl-cp F.zero (proj₁ e) (Data.Product.Base.proj₂ e)))))))

head-suc : A.R → Bool
head-suc (G.suc a) = true
head-suc _ = false

observe : A.R → Bool
observe x = head-suc (I.lim-body (I.lim-body x zero) (suc zero))

probe-tag : Bool → Bool
probe-tag false = true
probe-tag true = false

probe-observe : ∀ run → T.ProbeRows run → ∀ c b → F.Lgl F.zero c →
  observe (run (T.node c b)) ≡ probe-tag b
probe-observe run rows c false lc =
  trans (cong observe (T.ProbeRows.constant-gt rows c false lc))
    (cong (λ x → head-suc (I.lim-body x (suc zero)))
      (T.ProbeRows.unit-row rows))
probe-observe run rows c true lc =
  trans (cong observe (T.ProbeRows.constant-gt rows c true lc))
    (cong (λ x → head-suc (I.lim-body x (suc zero)))
      (T.ProbeRows.double-row rows))

true-not-false : true ≡ false → ⊥
true-not-false ()

WeakLgl : Set
WeakLgl = ∀ c → (F.Lgl F.zero c → ⊥) ⊎
  ((F.Lgl F.zero c → ⊥) → ⊥)

probes→weak-lgl : ∀ run → T.ProbeRows run → EmptyAgreement run → WeakLgl
probes→weak-lgl run rows empty c with
  observe (run (T.node c false)) ≟ observe (run (T.node c true))
... | yes eq = inj₁ (λ lc → true-not-false
  (trans (sym (probe-observe run rows c false lc))
    (trans eq (probe-observe run rows c true lc))))
... | no ne = inj₂ (λ nc → ne (cong observe (empty c nc)))
```

两个观测相等时，下界不合法；不相等时，只得下界非非合法，
没有把后者说成任意 Lgl 可判定。以下限定下界族的合法性恰是
“给定布尔列全为 false”；该性质稳定，故这一个族已经足够推出 WLPO。

```agda
AllFalse : (ℕ → Bool) → Set
AllFalse α = ∀ n → α n ≡ false

WLPO : Set
WLPO = ∀ α → AllFalse α ⊎ (AllFalse α → ⊥)

flag : Bool → A.R
flag false = A.one
flag true = G.zero

-- 列为 1, flag(α 0), 1, flag(α 1), ...；每个坏位都有前面的字面 1。
columns : (ℕ → Bool) → ℕ → A.R
columns α zero = A.one
columns α (suc zero) = flag (α zero)
columns α (suc (suc n)) = columns (λ j → α (suc j)) n

encoded : (ℕ → Bool) → A.R
encoded α = G.lim (columns α)

columns-legal : ∀ α n → F.Lgl F.zero (columns α n)
columns-legal α zero = tt
columns-legal α (suc zero) with α zero
... | false = tt
... | true = tt
columns-legal α (suc (suc n)) = columns-legal (λ j → α (suc j)) n

all→steps : ∀ α → AllFalse α → ∀ n →
  F.Cp F.zero (columns α n) (columns α (suc n))
all→steps α az zero = inj₁ (sym (cong flag (az zero)))
all→steps α az (suc zero) = inj₁ (cong flag (az zero))
all→steps α az (suc (suc n)) =
  all→steps (λ j → α (suc j)) (λ j → az (suc j)) n

flag-valid : ∀ b → F.Cp F.zero A.one (flag b) → b ≡ false
flag-valid false p = refl
flag-valid true (inj₁ ())
flag-valid true (inj₂ ())

steps→all : ∀ α →
  (∀ n → F.Cp F.zero (columns α n) (columns α (suc n))) → AllFalse α
steps→all α st zero = flag-valid (α zero) (st zero)
steps→all α st (suc n) = steps→all (λ j → α (suc j))
  (λ j → st (suc (suc j))) n

all→legal : ∀ α → AllFalse α → F.Lgl F.zero (encoded α)
all→legal α az = all→steps α az , columns-legal α

legal→all : ∀ α → F.Lgl F.zero (encoded α) → AllFalse α
legal→all α l = steps→all α (proj₁ l)

false-stable : ∀ b → ((b ≡ false → ⊥) → ⊥) → b ≡ false
false-stable false nn = refl
false-stable true nn = ⊥-elim (nn true-not-false)

all-stable : ∀ α → ((AllFalse α → ⊥) → ⊥) → AllFalse α
all-stable α nn n = false-stable (α n) (λ ne → nn (λ az → ne (az n)))

weak-lgl→wlpo : WeakLgl → WLPO
weak-lgl→wlpo weak α with weak (encoded α)
... | inj₁ nc = inj₂ (λ az → nc (all→legal α az))
... | inj₂ nn = inj₁ (all-stable α (λ na → nn (λ lc → na (legal→all α lc))))

probes-empty→wlpo : ∀ run → T.ProbeRows run → EmptyAgreement run → WLPO
probes-empty→wlpo run rows empty = weak-lgl→wlpo (probes→weak-lgl run rows empty)

-- 条件验收定理。fe 只是前提，没有产出外延公理或将它存入证书。
funext-probes→wlpo : Funext → ∀ run → T.ProbeRows run → WLPO
funext-probes→wlpo fe run rows =
  probes-empty→wlpo run rows (funext→empty-agreement fe run)

funext-fold-tree→wlpo : Funext → ∀ run (d : B.FoldRows0) →
  B.FoldRows0.ψ d ≡ (λ s → run (C.term (B.original s))) → WLPO
funext-fold-tree→wlpo fe run d tree = funext-probes→wlpo fe run
  (T.from-fold run d tree)

-- 限定下界族两端都有闭实例，非法端也不是不明的外部命题。
encoded-good : F.Lgl F.zero (encoded (λ n → false))
encoded-good = all→legal (λ n → false) (λ n → refl)

encoded-bad : F.Lgl F.zero (encoded (λ n → true)) → ⊥
encoded-bad l = true-not-false (legal→all (λ n → true) l zero)
```

## 前提可满足性与尚缺的蕴涵

- 编译实例：`encoded-good`、`encoded-bad` 分别给合法与非法的闭下界；
  Tree.node-source 在所有带 Lgl 证明的下界实填原三个证书。
  这里没有空假的“下界既合法又非法”前提。
- **纸面可满足性说明，非编译构造：** 在经典外延集合解释中，Funext 成立，
  并能按 Lgl c 是否成立给 LF 作良基递归解释：零和后继取指定行；
  lc 0 的合法下界用 c 自身及其守卫读分支、返回该子读数的常极限；
  非法下界及其余 lc 可取第一支读数。两个恒分支根随即满足 ProbeRows。
  同一解释满足 EmptyAgreement，因为非法下界的守卫域空，两根相等。
  这说明本篇的最小前提在经典外延解释中可同时满足；没有证明完整
  FoldRows0 可满足，也没有给出其生成器、位置保持或实现修补。
- **判断／未证：** 只读树加原 gt 行，在不加 EmptyAgreement 或 Funext
  时推出 WLPO，尚未证得。证明恰卡在非法下界：两分支函数逐点相等
  （守卫会导出矛盾），但要把两个 lc 根送给任意 run 后判为相等，
  仍缺整分支函数的等式。原 Legal.irr 只比较一个已存在守卫下的读数，
  不提供这条空域外延等式。也没有无条件证明这样的 run 不存在。

这条障碍仅用两个常分支、两个有限子项；不用 gt 的加法更新、输出保持、
高层比较或一般有界位置律。所有用于比较的布尔观测均可判定；
没有比较裸不可数下标，没有新增记号或阶段字段。
