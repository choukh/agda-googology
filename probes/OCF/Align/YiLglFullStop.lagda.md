# 四处严格仍不能保证局部 gt 输出严格

规范闭包已由 FullVal 给出。本篇只检验一个完全合法的 Ω 源和闭种子，
不实现完整 ψ／γ。源的分支在 Dn 坐标步下严格，但保留的守卫下界等号
允许种子 raw1；保留的第一支弱 CP 又允许该分支值为0。
零行在此返回1。对明确固定这个 canonical Raw 种子的局部 gt 合同，
输出于是成为常1列，不能满足 Legal。这是硬止损2的条件否定，不研究修补。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglFullStop where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; subst; subst₂)
import OCF.Align.YiLglFullCore as F
open F using (module G)
import OCF.Align.YiLglFullVal as V

Raw0 : Set
Raw0 = F.Raw F.zero

-- 每条 lim 列丢首支；否则简单的逐点减一不一定保持严格性。
lower : Raw0 → F.LF
lower G.zero = F.zero
lower (G.suc G.zero) = F.zero
lower (G.suc (G.suc a)) = F.suc (lower (G.suc a))
lower (G.suc (G.lim f)) = F.suc (lower (G.lim f))
lower (G.suc (G.lc () c t g))
lower (G.suc (G.em () T))
lower (G.suc G.top) = F.suc F.zero
lower (G.lim f) = F.lim (λ n → lower (f (suc n)))
lower (G.lc () c t g)
lower (G.em () T)
lower G.top = F.zero

lower-cp : (b : Raw0) → F.Lgl F.zero b → ∀ {a} →
  F.Cp F.zero a b → V.CP (lower a) (lower b)
lower-cp b lawful (inj₁ refl) = V.self
lower-cp G.zero lawful (inj₂ ())
lower-cp (G.suc G.zero) lawful (inj₂ (inj₁ refl)) = V.self
lower-cp (G.suc G.zero) lawful (inj₂ (inj₂ ()))
lower-cp (G.suc (G.suc b)) lawful (inj₂ p) =
  V.suc (lower-cp (G.suc b) lawful p)
lower-cp (G.suc (G.lim f)) lawful (inj₂ p) =
  V.suc (lower-cp (G.lim f) lawful p)
lower-cp (G.suc (G.lc () c t g)) lawful (inj₂ p)
lower-cp (G.suc (G.em () T)) lawful (inj₂ p)
lower-cp (G.suc G.top) lawful (inj₂ p) = V.suc (lower-cp G.top tt p)
lower-cp (G.lim f) (step , lawful) (inj₂ (n , p)) =
  V.lim n (lower-cp (f (suc n)) (lawful (suc n))
    (F.Cp-tr F.zero p (inj₂ (step n))))
lower-cp (G.lc () c t g) lawful (inj₂ p)
lower-cp (G.em () T) lawful (inj₂ p)
lower-cp G.top lawful (inj₂ ())

lower-dn : (b : Raw0) → F.Lgl F.zero b → ∀ {a} →
  (a ≡ G.zero → ⊥) → F.Dn F.zero a b → V.Properˢ (lower a) (lower b)
lower-dn G.zero lawful nonzero ()
lower-dn (G.suc G.zero) lawful nonzero (inj₁ refl) = ⊥-elim (nonzero refl)
lower-dn (G.suc G.zero) lawful nonzero (inj₂ ())
lower-dn (G.suc (G.suc b)) lawful nonzero p =
  V.under-suc (lower-cp (G.suc b) lawful p)
lower-dn (G.suc (G.lim f)) lawful nonzero p =
  V.under-suc (lower-cp (G.lim f) lawful p)
lower-dn (G.suc (G.lc () c t g)) lawful nonzero p
lower-dn (G.suc (G.em () T)) lawful nonzero p
lower-dn (G.suc G.top) lawful nonzero p = V.under-suc (lower-cp G.top tt p)
lower-dn (G.lim f) (step , lawful) nonzero (n , p) =
  V.under-lim n (lower-cp (f (suc n)) (lawful (suc n))
    (F.Cp-tr F.zero p (inj₂ (step n))))
lower-dn (G.lc () c t g) lawful nonzero p
lower-dn (G.em () T) lawful nonzero p
lower-dn G.top lawful nonzero ()

dn-target-nonzero : ∀ {a b : Raw0} → F.Dn F.zero a b → b ≡ G.zero → ⊥
dn-target-nonzero () refl

lower-legal : (a : Raw0) → F.Lgl F.zero a → V.Legal (lower a)
lower-legal G.zero lawful = tt
lower-legal (G.suc G.zero) lawful = tt
lower-legal (G.suc (G.suc a)) lawful = lower-legal (G.suc a) lawful
lower-legal (G.suc (G.lim f)) lawful = lower-legal (G.lim f) lawful
lower-legal (G.suc (G.lc () c t g)) lawful
lower-legal (G.suc (G.em () T)) lawful
lower-legal (G.suc G.top) lawful = tt
lower-legal (G.lim f) (step , lawful) =
  (λ n → lower-dn (f (suc (suc n))) (lawful (suc (suc n)))
    (dn-target-nonzero (step n)) (step (suc n))) ,
  (λ n → lower-legal (f (suc n)) (lawful (suc n)))
lower-legal (G.lc () c t g) lawful
lower-legal (G.em () T) lawful
lower-legal G.top lawful = tt
```

lower-cp 与 lower-dn 的 lim 行把原见证 n 沿严格相邻步推进到 suc n，
再递归到原输入的直接孩子。这里不用比较任意坐标，也不把旧 Raw 搬到新 Raw。
lower-dn 的源非零条件不可省；源的守卫会提供它。

```agda
One : F.LF
One = F.suc F.zero

seed : Raw0
seed = G.suc G.zero

seed-guard : F.Gd F.zero seed seed
seed-guard = inj₁ refl , tt

guard-nonzero : ∀ {η} → F.Gd F.zero seed η → η ≡ G.zero → ⊥
guard-nonzero (inj₁ () , lawful) refl
guard-nonzero (inj₂ () , lawful) refl

zero-CP : ∀ x → V.CP F.zero x
zero-CP F.zero = V.self
zero-CP (F.suc x) = V.suc (zero-CP x)
zero-CP (F.lim f) = V.lim zero (zero-CP (f zero))
zero-CP (F.lc k c t g) = V.fst (zero-CP t)

body : (η : Raw0) → F.Gd F.zero seed η → F.LF
body η e = lower η

source : F.LF
source = F.lc F.zero seed F.zero body

source-legal : V.Legal source
source-legal = tt , (λ η e → zero-CP (lower η)) ,
  (λ η e η′ e′ d → lower-dn η′ (proj₂ e′) (guard-nonzero e) d) ,
  (λ η e e′ → refl) , tt , (λ η e → lower-legal η (proj₂ e))

body-at-seed : ∀ e → body seed e ≡ F.zero
body-at-seed e = refl

first-at-seed : V.CP F.zero (body seed seed-guard)
first-at-seed = V.self

no-proper-zero : V.Properˢ F.zero F.zero → ⊥
no-proper-zero ()

no-first-strict : (∀ η e → V.Properˢ F.zero (body η e)) → ⊥
no-first-strict strict = no-proper-zero (strict seed seed-guard)

-- 根派发的1与目标0有字面合法公共界1，且目标在派发下方。
root-bound-legal : V.Legal One
root-bound-legal = tt

root-field-position : V.CP One One
root-field-position = V.self

root-target-position : V.CP F.zero One
root-target-position = V.suc V.self

root-above : V.Properˢ F.zero One
root-above = V.under-suc V.self
```

source 的全部 Ω 分支严格合法，分支严格单调也已经实填。
它在 seed 上恰用保留的下界等号和第一支 CP.self；并非仍有遗漏的常 Ω 分支。
以下合同不从 up 的值相等推回 Raw 相等。canonical seed 明确就是上述 raw1，
step 的固定性逐个守卫证据给 raw 分量方程，不识别 Σ 证书或证明。

```agda
Step : Set
Step = (η : Raw0) → F.Gd F.zero seed η → Raw0

record SeedChain (step : Step) (points : ℕ → Raw0)
  (guards : ∀ n → F.Gd F.zero seed (points n)) : Set where
  field
    seed-fixed : ∀ e → step seed e ≡ seed
    initial : points zero ≡ seed
    next : ∀ n → points (suc n) ≡ step (points n) (guards n)
open SeedChain public

step-at-seed : (step : Step) → (∀ e → step seed e ≡ seed) →
  ∀ η e → η ≡ seed → step η e ≡ seed
step-at-seed step fixed .seed e refl = fixed e

points-fixed : ∀ step points guards → SeedChain step points guards →
  ∀ n → points n ≡ seed
points-fixed step points guards chain zero = initial chain
points-fixed step points guards chain (suc n) =
  trans (next chain n)
    (step-at-seed step (seed-fixed chain) (points n) (guards n)
      (points-fixed step points guards chain n))

out : (F.LF → F.LF) → ∀ η → F.Gd F.zero seed η → F.LF
out go η e = go (body η e)

out-at-seed : ∀ go → go F.zero ≡ One → ∀ η e →
  η ≡ seed → out go η e ≡ One
out-at-seed go zero-row .seed e refl = zero-row

no-proper-one : V.Properˢ One One → ⊥
no-proper-one (V.under-suc ())

no-constant-one : ∀ {f : ℕ → F.LF} → (∀ n → f n ≡ One) →
  V.Legal (F.lim f) → ⊥
no-constant-one same (strict , lawful) =
  no-proper-one (subst₂ V.Properˢ (same zero) (same (suc zero)) (strict zero))

no-fixed-output : ∀ go step points guards → go F.zero ≡ One →
  SeedChain step points guards →
  V.Legal (F.lim (λ n → out go (points n) (guards n))) → ⊥
no-fixed-output go step points guards zero-row chain =
  no-constant-one (λ n → out-at-seed go zero-row (points n) (guards n)
    (points-fixed step points guards chain n))

record LocalRules (go : F.LF → F.LF) (step : Step) (points : ℕ → Raw0)
  (guards : ∀ n → F.Gd F.zero seed (points n)) : Set where
  field
    zero-row : go F.zero ≡ One
    fixed-chain : SeedChain step points guards
    gt-row : go source ≡ F.lim (λ n → out go (points n) (guards n))
open LocalRules public

no-rule-preservation : ∀ go step points guards →
  LocalRules go step points guards → V.Legal (go source) → ⊥
no-rule-preservation go step points guards rules lawful =
  no-fixed-output go step points guards (zero-row rules) (fixed-chain rules)
    (subst V.Legal (gt-row rules) lawful)

canonical-step : Step
canonical-step η e = seed

canonical-points : ℕ → Raw0
canonical-points n = seed

canonical-guards : ∀ n → F.Gd F.zero seed (canonical-points n)
canonical-guards n = seed-guard

canonical-chain : SeedChain canonical-step canonical-points canonical-guards
seed-fixed canonical-chain e = refl
initial canonical-chain = refl
next canonical-chain n = refl

observer : F.LF → F.LF
observer F.zero = One
observer (F.suc x) = One
observer (F.lim f) = One
observer (F.lc k c t g) = F.lim (λ _ → One)

contract-instance :
  LocalRules observer canonical-step canonical-points canonical-guards
zero-row contract-instance = refl
fixed-chain contract-instance = canonical-chain
gt-row contract-instance = refl
```

source-legal、canonical-chain、contract-instance 都是闭实例，
所以否定不靠空前提。observer 只证明这几条局部方程可同时满足，
不称完整 ψ；canonical-step 也只是所选闭种子的观察步，不是任意 LF 的回收器。
固定坐标是合同的显式前提，不由读回值推出，不宣称完整 γ 已构造。
本篇未给 source 的 EBO Rep／Reach 证书，不称实际 EBO 输入或实际轨道反例。
结论仅否定：在当前全 Legal 源域上同时满足这个固定种子与 gt 局部合同的
折叠，能够对所有这些源保持 Legal。硬止损到此，不增加合法性形状或研究修补。
