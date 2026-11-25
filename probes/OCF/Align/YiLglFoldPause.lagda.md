# 严格源的 gt 输出仍可被迫成为常列

本篇只检验已固定的零、后继及 gt 输出规则，不实现完整 ψ 或 γ。
源是 lc 0 raw1 1 (λ η e → 1)：它满足平行 Legalˢ 与既有 R₂，
没有不合法的 ℕ 常列。但零种子为1、后继行给 go 1=W 后，
每条分支的 out 都是同一个 W，gt 的逐点输出因此不能满足 Legalˢ。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglFoldPause where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; subst; subst₂)
open import OCF.Align.YiLglCore using (LF; Raw; Gd; Dn)
import OCF.Align.YiLglCore as F
open F using (module G)
open import OCF.Align.YiLglVal using (CP)
import OCF.Align.YiLglVal as V
open import OCF.Align.YiLglStrict using (Legalˢ; Properˢ; R₂; under-suc; under-lim)
import OCF.Align.YiLglStrict as S
import OCF.Align.YiLglCompare as C
open import OCF.Align.YiLglFoldIf using (copies; successor; successor-legal; iter)

One W : LF
One = F.suc F.zero
W = successor One

one-legal : Legalˢ One
one-legal = tt

W-legal : Legalˢ W
W-legal = successor-legal One one-legal tt

source-body : (η : Raw F.zero) → Gd F.zero (V.cO F.zero) η → LF
source-body η e = One

source : LF
source = F.lc F.zero (V.cO F.zero) One source-body

source-legal : Legalˢ source
source-legal = tt , (λ η e → V.self) , (λ η e η′ e′ p → V.self) ,
  (λ η e e′ → refl) , tt , (λ η e → tt)

source-R₂ : R₂ source
source-R₂ = S.one S.e-first , tt , tt , (λ η e → tt)

bound : C.Level
bound = C.level One one-legal

field-position : C.Position bound
field-position = C.located bound V.self

target-position : C.Position bound
target-position = C.located (C.level F.zero tt) (V.suc V.self)

root-order : C.Order One F.zero
root-order = C.bounded-compare bound field-position target-position

root-gt : root-order ≡ C.above (under-suc V.self)
root-gt = refl
```

比较以合法界1为公共界，确实选择 gt。W 本身严格合法；
下面用有限性排除 W 到自己的一条 Properˢ 路径，而不比较两个极限函数。

```agda
data Finite : LF → Set where
  finite-zero : Finite F.zero
  finite-suc : ∀ {x} → Finite x → Finite (F.suc x)

one-add-finite : ∀ {x} → Finite x → Finite (V._+ᴸ_ One x)
one-add-finite finite-zero = finite-suc finite-zero
one-add-finite (finite-suc p) = finite-suc (one-add-finite p)

copies-finite : ∀ n → Finite (copies One n)
copies-finite zero = finite-zero
copies-finite (suc n) = one-add-finite (copies-finite n)

finite-position : ∀ {x y} → CP x y → Finite y → Finite x
finite-position V.self p = p
finite-position (V.suc q) (finite-suc p) = finite-position q p
finite-position (V.lim n q) ()
finite-position (V.fst q) ()

W-not-finite : Finite W → ⊥
W-not-finite ()

no-proper-W : Properˢ W W → ⊥
no-proper-W (under-lim n p) = W-not-finite (finite-position p (copies-finite n))

no-pause : ∀ {f : ℕ → LF} → f zero ≡ W → f (suc zero) ≡ W →
  Legalˢ (F.lim f) → ⊥
no-pause first second (step , lawful) =
  no-proper-W (subst₂ Properˢ first second (step zero))

no-constant-columns : ∀ {f : ℕ → LF} → (∀ n → f n ≡ W) →
  Legalˢ (F.lim f) → ⊥
no-constant-columns same = no-pause (same zero) (same (suc zero))

no-constant-out : ∀ {A : Set} (out : A → LF) (points : ℕ → A) →
  (∀ a → out a ≡ W) → Legalˢ (F.lim (λ n → out (points n))) → ⊥
no-constant-out out points same = no-constant-columns (λ n → same (points n))

no-iter-output : ∀ {A : Set} (step : A → A) start (out : A → LF) →
  (∀ a → out a ≡ W) →
  Legalˢ (F.lim (λ n → out (iter step start n))) → ⊥
no-iter-output step start out same = no-constant-out out (iter step start) same

no-selected-iter : ∀ {A : Set} (step : A → A) start (out : A → LF)
  (select : ℕ → ℕ) → (∀ a → out a ≡ W) →
  Legalˢ (F.lim (λ n → out (iter step start (select n)))) → ⊥
no-selected-iter step start out select same =
  no-constant-out out (λ n → iter step start (select n)) same
```

select 可以是首步移位，也可以任取子列；没有判定停顿或另写严格化程序。
这些否定不限于某种 step。再把 out 接回这个合法源的实际分支函数。

```agda
Coordinate : Set
Coordinate = Σ (Raw F.zero) (λ η → Gd F.zero (V.cO F.zero) η)

raw1 raw2 : Raw F.zero
raw1 = G.suc G.zero
raw2 = G.suc raw1

coordinate1 coordinate2 : Coordinate
coordinate1 = raw1 , (inj₁ refl , tt)
coordinate2 = raw2 , (inj₂ (inj₁ refl) , tt)

raw-strict : Dn F.zero raw1 raw2
raw-strict = inj₁ refl

coordinate-strict : Properˢ (V.up F.zero raw1) (V.up F.zero raw2)
coordinate-strict = under-suc V.self

out : (LF → LF) → Coordinate → LF
out go p = go (source-body (proj₁ p) (proj₂ p))

out-constant : ∀ go → go One ≡ W → ∀ p → out go p ≡ W
out-constant go one-rule p = one-rule

no-source-output : ∀ go → go One ≡ W → (points : ℕ → Coordinate) →
  Legalˢ (F.lim (λ n → out go (points n))) → ⊥
no-source-output go one-rule points =
  no-constant-out (out go) points (out-constant go one-rule)

no-out-strict : ∀ go → go One ≡ W →
  Properˢ (out go coordinate1) (out go coordinate2) → ⊥
no-out-strict go one-rule p =
  no-proper-W (subst₂ Properˢ one-rule one-rule p)

no-out-dn-map : ∀ go → go One ≡ W →
  (∀ (a b : Coordinate) → Dn F.zero (proj₁ a) (proj₁ b) →
    Properˢ (out go a) (out go b)) → ⊥
no-out-dn-map go one-rule strict =
  no-out-strict go one-rule (strict coordinate1 coordinate2 raw-strict)
```

raw1、raw2 均过原守卫，且二者已有 Dn 以及读回后的 Properˢ。
源的 Ω 分支单调性却只是弱 CP；常分支把这两个坐标送到同一个 One。
所以不能只凭递归 go 对严格路径的保持，推断 out 也保持坐标严格性。

最后固定最小规则合同。它只记录零行、输入1的后继行及这个源的 gt 行，
不要求或冒称完整 ψ。gt 行只对给定坐标序列量化，不强加所有序列必须是同一条 γ。

```agda
one-from-rules : (go : LF → LF) → go F.zero ≡ One → go One ≡ successor (go F.zero) → go One ≡ W
one-from-rules go zero-rule successor-rule =
  trans successor-rule (cong successor zero-rule)

record SourceRules (go : LF → LF) (points : ℕ → Coordinate) : Set where
  field
    zero-rule : go F.zero ≡ One
    successor-one : go One ≡ successor (go F.zero)
    gt-rule : go source ≡ F.lim (λ n → out go (points n))
open SourceRules public

no-rule-preservation : ∀ go points → SourceRules go points → Legalˢ (go source) → ⊥
no-rule-preservation go points rules lawful =
  no-source-output go
    (one-from-rules go (zero-rule rules) (successor-one rules)) points
    (subst Legalˢ (gt-rule rules) lawful)

observer : LF → LF
observer F.zero = One
observer (F.suc x) = W
observer (F.lim f) = One
observer (F.lc k c t g) = F.lim (λ _ → W)

observer-rules : ∀ points → SourceRules observer points
zero-rule (observer-rules points) = refl
successor-one (observer-rules points) = refl
gt-rule (observer-rules points) = refl

nonempty-sequence : ℕ → Coordinate
nonempty-sequence n = coordinate1

contract-instance : SourceRules observer nonempty-sequence
contract-instance = observer-rules nonempty-sequence
```

observer 只证明上述局部规则同时可满足；它不满足、也不自称满足完整 ψ 规则。
源、W、坐标及局部规则合同均有实例，反例不是靠矛盾前提得到。

这里否定的是当前全 Legalˢ／R₂ 源域上按所给 gt 规则产生严格输出的通用合同。
没有给这个常 Ω 分支源的 EBO Rep 或 Reach 证书，不称其为实际 EBO 输入、
实际 ψ 列停顿或实际 γ 输出反例。未改原定义或添加正则性形状；没有使用 Funext、
UIP、裸下标比较或为任意原始树补码。
