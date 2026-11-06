# 事件世界上的真折叠 (八): 有限测试

> 不含记号. 入口 [EvFold](EvFold.lagda.md). **这些是有限测试, 不是证明.** `same d w a b`: 两棵 `A` 树到深度 $d$, 每个极限取前 $w$ 支, 构造子相同 (同 `HtTowerFTest.same`, 这里另写一份, 免得导入 `HtOut*`). `diff d w a b`: 同样的遍历, 给出第一个不同处的路径 (各层所取的支). `diffL`: 同 `diff`, 但只有极限算深度 (后继不算).
>
> 结果见入口 §4. 正面的测试 (找得到不同) 写成 `refl`; **找不到不同的测试也写成 `refl`** (`diff … ≡ none`), 它们说的只是 "在这个范围里没有不同", 是盲点的记录, 不是相等的证明.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvFoldTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy using (hz; hs; hl; hΩ; LgB; _⊲[_]_; hself; hsuc; hlim)
open import OCF.Align.EvFoldTree using (Ht; κa)
open import OCF.Align.EvFoldClosed using (T⁺; T-Ω₂; T-Ω₃; T-Ω₃+1)
import OCF.Align.HtTowerFClosed as F

all< : ℕ → (ℕ → Bool) → Bool
all< zero p = true
all< (suc n) p = all< n p ∧ p n

same : ℕ → ℕ → A → A → Bool
same zero w a b = true
same (suc d) w azero azero = true
same (suc d) w (asuc a) (asuc b) = same d w a b
same (suc d) w (alim f) (alim g) = all< w (λ n → same d w (f n) (g n))
same (suc d) w _ _ = false

data Res : Set where
  none : Res
  at   : List ℕ → Res

orR : Res → Res → Res
orR none r = r
orR (at p) r = at p

cons : ℕ → Res → Res
cons k none = none
cons k (at p) = at (k ∷ p)

diffs : ℕ → ℕ → ℕ → (ℕ → A) → (ℕ → A) → Res
diff  : ℕ → ℕ → A → A → Res
diff zero w a b = none
diff (suc d) w azero azero = none
diff (suc d) w (asuc a) (asuc b) = diff d w a b
diff (suc d) w (alim f) (alim g) = diffs d w w f g
diff (suc d) w _ _ = at []
diffs d w zero f g = none
diffs d w (suc k) f g = orR (diffs d w k f g) (cons k (diff d w (f k) (g k)))

diffsL : ℕ → ℕ → ℕ → (ℕ → A) → (ℕ → A) → Res
diffL  : ℕ → ℕ → A → A → Res
diffL d w azero azero = none
diffL d w (asuc a) (asuc b) = diffL d w a b
diffL zero w (alim f) (alim g) = none
diffL (suc d) w (alim f) (alim g) = diffsL d w w f g
diffL d w _ _ = at []
diffsL d w zero f g = none
diffsL d w (suc k) f g = orR (diffsL d w k f g) (cons k (diffL d w (f k) (g k)))

-- A 坐标上的嵌入: Ω₁ 的层 (本折叠里的对照)
nbA₁ : A → Ht
nbA₁ azero = hz
nbA₁ (asuc c) = hs (nbA₁ c)
nbA₁ (alim f) = hl (λ n → nbA₁ (f n))

nbA₁-mono : ∀ {a b} {W} → a ⊲ b → nbA₁ a ⊲[ W ] nbA₁ b
nbA₁-mono C.self = hself
nbA₁-mono (C.suc p) = hsuc (nbA₁-mono p)
nbA₁-mono (C.lim n p) = hlim n (nbA₁-mono p)

Lg-nbA₁ : ∀ c → Lg c → LgB (nbA₁ c)
Lg-nbA₁ azero _ = tt
Lg-nbA₁ (asuc c) l = Lg-nbA₁ c l
Lg-nbA₁ (alim f) (st , l) = (λ n → nbA₁-mono (st n)) , (λ n → Lg-nbA₁ (f n) (l n))

T-Ω₁ : A
T-Ω₁ = T⁺ (hΩ κa nbA₁) ((λ lW e e′ p → nbA₁-mono p) , Lg-nbA₁)
```

**找得到不同的.**

```agda
a4 : same 4 2 T-Ω₃ T-Ω₃+1 ≡ true
a4 = refl

a5 : same 5 2 T-Ω₃ T-Ω₃+1 ≡ false
a5 = refl

b4 : same 4 2 T-Ω₂ F.T-Ω₂ ≡ true
b4 = refl

b5 : same 5 2 T-Ω₂ F.T-Ω₂ ≡ false
b5 = refl

c10 : diff 10 3 T-Ω₁ T-Ω₂ ≡ at (1 ∷ 0 ∷ 0 ∷ [])
c10 = refl
```

**找不到不同的 (盲点的记录).** 更大的范围 (`same 26 2`, `diff 14 3`, `diffL 12 3`, `diffL 9 4`) 在复核时跑过, 结果见入口 §4; 这里只留编译快的两条.

```agda
d20 : same 20 2 T-Ω₂ T-Ω₃ ≡ true
d20 = refl

d9 : diffL 9 3 T-Ω₂ T-Ω₃ ≡ none
d9 = refl
```
