# 闭零步的固定性来自执行方程

本篇只核验反例的闭种子，不新增合法性形状或修补折叠。
固定 raw1 不能从任意读回相等单独推出；本篇同时使用输出的原守卫。
这不是全局 up 单射或从任意 LF 回收 Raw，只反演一个带守卫的闭值1。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglFullZeroStep where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
import OCF.Align.YiLglFullCore as F
open F using (module G)
import OCF.Align.YiLglFullVal as V
import OCF.Align.YiLglFullStop as S
open S using (Raw0; Step; One; seed; body; source; out; SeedChain)
open S.SeedChain

suc-injective : ∀ {a b} → F.suc a ≡ F.suc b → a ≡ b
suc-injective refl = refl

read-zero-only : ∀ a → V.up F.zero a ≡ F.zero → a ≡ G.zero
read-zero-only G.zero e = refl
read-zero-only (G.suc a) ()
read-zero-only (G.lim f) ()
read-zero-only (G.lc () c t g) e
read-zero-only (G.em () T) e
read-zero-only G.top ()

guarded-one-unique : ∀ a → F.Gd F.zero seed a → V.up F.zero a ≡ One → a ≡ seed
guarded-one-unique G.zero lawful ()
guarded-one-unique (G.suc a) lawful e = cong G.suc (read-zero-only a (suc-injective e))
guarded-one-unique (G.lim f) lawful ()
guarded-one-unique (G.lc () c t g) lawful e
guarded-one-unique (G.em () T) lawful e
guarded-one-unique G.top (inj₁ () , lawful) e
guarded-one-unique G.top (inj₂ () , lawful) e

record ZeroStep (go : F.LF → F.LF) (step : Step) : Set where
  field
    output-guard : ∀ e → F.Gd F.zero seed (step seed e)
    read-step : ∀ e → V.up F.zero (step seed e) ≡ go (body seed e)
open ZeroStep public

fixed-from-zero : ∀ go step → go F.zero ≡ One → ZeroStep go step →
  ∀ e → step seed e ≡ seed
fixed-from-zero go step zero-row execution e =
  guarded-one-unique (step seed e) (output-guard execution e)
    (trans (read-step execution e) zero-row)

chain-from-zero : ∀ go step points guards → go F.zero ≡ One → ZeroStep go step →
  points zero ≡ seed →
  (∀ n → points (suc n) ≡ step (points n) (guards n)) →
  SeedChain step points guards
seed-fixed (chain-from-zero go step points guards zero-row execution initial-row next-row) =
  fixed-from-zero go step zero-row execution
initial (chain-from-zero go step points guards zero-row execution initial-row next-row) = initial-row
next (chain-from-zero go step points guards zero-row execution initial-row next-row) = next-row

no-faithful-output : ∀ go step points guards → go F.zero ≡ One → ZeroStep go step →
  points zero ≡ seed →
  (∀ n → points (suc n) ≡ step (points n) (guards n)) →
  V.Legal (F.lim (λ n → out go (points n) (guards n))) → ⊥
no-faithful-output go step points guards zero-row execution initial-row next-row =
  S.no-fixed-output go step points guards zero-row
    (chain-from-zero go step points guards zero-row execution initial-row next-row)

no-faithful-preservation : ∀ go step points guards → go F.zero ≡ One → ZeroStep go step →
  points zero ≡ seed →
  (∀ n → points (suc n) ≡ step (points n) (guards n)) →
  go source ≡ F.lim (λ n → out go (points n) (guards n)) →
  V.Legal (go source) → ⊥
no-faithful-preservation go step points guards zero-row execution initial-row next-row gt-row lawful =
  no-faithful-output go step points guards zero-row execution initial-row next-row
    (subst V.Legal gt-row lawful)

canonical-zero-step : ZeroStep S.observer S.canonical-step
output-guard canonical-zero-step e = S.seed-guard
read-step canonical-zero-step e = refl
```

output-guard 是链点继续可入的义务，read-step 是该闭步忠实于递归输出的义务；
两者加零行，就把固定性推出来，而不是额外假定一个任意固定点。
初项／步进来自给定的模板迭代，canonical-chain 与 canonical-zero-step 给非空实例。
没有识别 Σ 或守卫证据，没有判定坐标，也没有实现完整 γ。
硬止损2由这个忠实闭步合同下的停顿触发，不是“增长需要判定”。
