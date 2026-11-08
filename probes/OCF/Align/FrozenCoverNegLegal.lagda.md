# 坐标前缀变换在实际首生成元上不保合法

检验同一 FrozenCoverIf.D，不改其接口。合法输入就是 Generated.initial。
反例坐标为 1 与常值极限 lim(const 1)，二者有字面的合法公共界。
D 后的分支将坐标相加两次，第一位置步进失败；这是路径反例，不是值不等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenCoverNegLegal where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (top)
open import OCF.Align.FrozenOutputIf using (Generated; initial)
open import OCF.Align.FrozenCoverIf using (D)

U = step S⊥
I : HB U
I = top (hs hz)

up-path : ∀ {a b : Cd} {w : Wd U} → a ⊲ b → up a ⊲[ w ] up b
up-path hself = hself
up-path (hsuc p) = hsuc (up-path p)
up-path (hlim n p) = hlim n (up-path p)

up-legal : ∀ a → LgB a → LgB (up {S⊥} a)
up-legal hz l = tt
up-legal (hs a) l = up-legal a l
up-legal (hl f) (s , l) = (λ n → up-path (s n)) , (λ n → up-legal (f n) (l n))

legal-initial : LgB I
legal-initial = (λ lw e e′ p → up-path p) ,
  (λ {w = w} {c} lw e → up-legal c (lgB⊲ e (proj₁ lw) (Data.Product.proj₂ lw)))

generated-initial : Generated I
generated-initial = initial

B : Cd
B = hl (λ _ → hs hz)
legal-B : LgB B
legal-B = (λ n → hself) , (λ n → tt)
first-coordinate : hs hz ⊲ B
first-coordinate = hlim 0 hself
second-coordinate : B ⊲ B
second-coordinate = hself

no-two-zero : ∀ {w : Wd U} → hs {S = U} (hs hz) ⊲[ w ] hz → ⊥
no-two-zero ()
no-two-one : ∀ {w : Wd U} → hs {S = U} (hs hz) ⊲[ w ] hs hz → ⊥
no-two-one (hsuc p) = no-two-zero p
no-two-limit : ∀ {w : Wd U} → hs {S = U} (hs hz) ⊲[ w ] hl (λ _ → hs hz) → ⊥
no-two-limit (hlim n p) = no-two-one p
no-two-slimit : ∀ {w : Wd U} → hs {S = U} (hs hz) ⊲[ w ] hs (hl (λ _ → hs hz)) → ⊥
no-two-slimit (hsuc p) = no-two-limit p
no-two-double : ∀ {w : Wd U} →
  hs {S = U} (hs hz) ⊲[ w ] hl (λ _ → hs (hl (λ _ → hs hz))) → ⊥
no-two-double (hlim n p) = no-two-slimit p

no-legal-D-initial : LgB (D I) → ⊥
no-legal-D-initial l = no-two-double
  (proj₁ l {w = tt , B} (tt , legal-B) first-coordinate second-coordinate first-coordinate)

no-preserves-generated-legal :
  (∀ c → Generated c → LgB c → LgB (D c)) → ⊥
no-preserves-generated-legal preserves = no-legal-D-initial
  (preserves I generated-initial legal-initial)
```

该否定不涉及 Candidate.Covers 的值覆盖结论，也不否定通过其他合法树代表
D 的值、或实际冻结输出族的错位覆盖。它只排除把原样 D 用作保合法变换。
翻译账：新增值验收路线的合法性否定，未改已有树、折叠或证书。
