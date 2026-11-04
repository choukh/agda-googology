# 桥: 验收 (有限测试)

> **验收节.** 记号只在本文件 (经 [GuardTightAccept](GuardTightAccept.lagda.md)). 结论写在 [GuardBridge](GuardBridge.lagda.md). **全部是有限测试, 不是证明.** $t_{11}$ = `T₀ (suc c₁)` ($\psi_0(\Omega_{\Omega+1})$), $u_{11}$ = `T₀′ (suc c₁)`, $q_{11}$ = 塔 ([LadderNFTree](LadderNFTree.lagda.md)), $f_{11}$ = [OCF.Free.Tree](../Free/Tree.lagda.md) 的 `ψ̄ (Ω̇ 1)`.
>
> `mis d w`: 深度 $d$, 宽度 $w$ ($\lim$ 的下标与分支的下标都 $<w$), 逐闭包比界. 上一轮的 `agree` 宽度 2, 看不到第 2 项 $n=2$, 所以 `T₀` 的差别没有出现. 这里宽度 3.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardBridgeAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z)
import OCF.Free.Prefix as ZP
import OCF.Align.LadderNFTree as Q
open import OCF.Align.GuardTightAccept using (dfZ; tΩ11; toN)
open import OCF.Align.GuardBridgeNeg using (tgt₁; tgt₁′; freeTree; iterᴵ; up⊑)

q11 : Z
q11 = ZP.toZ (Q.Tᵠ 0 (suc zero) {zero} {suc zero} (tt , (λ q → q)) zero)

data Dir : Set where
  L : ℕ → Dir
  B : ℕ → Dir
  F : Dir
  S : Dir

data Mis : Set where
  bnd : List Dir → ℕ → ℕ → Mis
  knd : List Dir → Mis

orM : Maybe Mis → Maybe Mis → Maybe Mis
orM (just x) _ = just x
orM nothing y = y

eqn : ℕ → ℕ → Maybe Mis → Maybe Mis → Maybe Mis
eqn zero zero a b = b
eqn (suc m) (suc n) a b = eqn m n a b
eqn m n a b = a

mis : ℕ → ℕ → List Dir → Z → Z → Maybe Mis
misL : ℕ → ℕ → ℕ → List Dir → (ℕ → Z) → (ℕ → Z) → Maybe Mis
misB : ℕ → ℕ → ℕ → List Dir → ∀ {c c′ : Ordᴵ} → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → ((η : Ordᴵ) → c′ ⊑ᴵ η → Z) → Maybe Mis
mis zero w p _ _ = nothing
mis (suc d) w p Z.zero Z.zero = nothing
mis (suc d) w p (Z.suc x) (Z.suc y) = mis d w (p ++ (S ∷ [])) x y
mis (suc d) w p (Z.lim f) (Z.lim g) = misL w d w p f g
mis (suc d) w p (Z.ĉᴸ c z zg o₀ o) (Z.ĉᴸ c′ z′ zg′ o₀′ o′) =
  eqn (toN c) (toN c′) (just (bnd p (toN c) (toN c′))) (orM (mis d w (p ++ (F ∷ [])) o₀ o₀′) (misB w d w p o o′))
mis (suc d) w p _ _ = just (knd p)
misL zero d w p f g = nothing
misL (suc n) d w p f g = orM (mis d w (p ++ (L n ∷ [])) (f n) (g n)) (misL n d w p f g)
misB zero d w p o o′ = nothing
misB (suc k) d w p {c} {c′} o o′ = orM (mis d w (p ++ (B k ∷ [])) (o (iterᴵ c k) (up⊑ k)) (o′ (iterᴵ c′ k) (up⊑ k))) (misB k d w p o o′)
```

## §1 `T₀` 对塔, 对对面: 第一个差别

```agda
pth₀ : List Dir
pth₀ = L 2 ∷ B 2 ∷ L 1 ∷ L 0 ∷ L 2 ∷ L 0 ∷ F ∷ L 2 ∷ L 0 ∷ []

t-q : mis 10 3 [] tgt₁ q11 ≡ just (bnd pth₀ 2 1)
t-q = refl

t-f : mis 10 3 [] tgt₁ freeTree ≡ just (bnd pth₀ 2 1)
t-f = refl

-- 对照: 窄的宽度看不到
t-q₂ : mis 10 2 [] tgt₁ q11 ≡ nothing
t-q₂ = refl
```

## §2 改一行之后

```agda
u-q : mis 10 3 [] tgt₁′ q11 ≡ nothing
u-q = refl

u-kind : dfZ 12 2 tΩ11 tgt₁′ ≡ nothing
u-kind = refl
```

## §3 极限的帧: 对对面, 对塔

`toE`: 把字面的小序数读成 $1000x+y$ ($\omega x+y$), 只用来显示. 路径 `p₁` 在 [GuardBridgeNeg](GuardBridgeNeg.lagda.md). **这里界 $\omega+1$, 对面与塔都是 $\omega$.**

```agda
open import OCF.Free.Level using (lim)
open import OCF.Align.GuardBridgeNeg using (p₁; walkP; bdOf)

_+ₙ_ : ℕ → ℕ → ℕ
zero +ₙ k = k
suc m +ₙ k = suc (m +ₙ k)

sub : ℕ → ℕ → ℕ
sub m zero = m
sub zero (suc n) = zero
sub (suc m) (suc n) = sub m n

nEq : ℕ → ℕ → Maybe ℕ
nEq zero zero = nothing
nEq (suc a) (suc b) = nEq a b
nEq a b = just a

toE : Ordᴵ → ℕ
toE zero = 0
toE (suc a) = suc (toE a)
toE (lim f s) with nEq (toE (f 5)) (toE (f 6))
... | nothing = toE (f 5)
... | just _ = 1000 +ₙ sub (toE (f 5)) 5

lim-u : toE (bdOf (proj₁ (walkP p₁ tgt₁′ freeTree))) ≡ 1001
lim-u = refl

lim-f : toE (bdOf (proj₂ (walkP p₁ tgt₁′ freeTree))) ≡ 1000
lim-f = refl

lim-q : toE (bdOf (proj₂ (walkP p₁ tgt₁′ q11))) ≡ 1000
lim-q = refl
```
