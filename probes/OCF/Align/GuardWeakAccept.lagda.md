# 弱证据的树: 验收 (有限测试)

> **验收节.** 记号与塔只在本文件. 结论写在 [GuardWeak](GuardWeak.lagda.md). **全部是有限测试, 不是证明, 不是证书.**
>
> `mis d w v`: 对塔 ([LadderNFTree](LadderNFTree.lagda.md)), 逐闭包比界 (`vE`: 值的读数, 对 $<\omega^2$ 与字面形状无关), 深度 $, 宽度 $ ($\lim$ 下标与分支 +k$ 都 $<w$), 另加分支 $\omega+j$, <v$ (`W`, 当界是字面有限). 读数不一样的给 `bnd`, 种类不一样的给 `knd`.
> `chk`: 沿给定路径比, 步子 `L`, `F`, `B`, `W`, `V` ($\omega^2+j$, 极限的极限). 路径是随机的, 步子不适用就停.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardWeakAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z)
import OCF.Free.Prefix as ZP
open import OCF.Align.GuardTightAccept using (dfZ; tΩ11; tq; tqω)
open import OCF.Align.GuardBridgeNeg using (iterᴵ; up⊑; p₁; walkP; bdOf; tgt₁′)
open import OCF.Align.GuardTightLv using (module Lv; Dom₀)
open Lv Dom₀ using (s≈) renaming (suc to sucL)
open import OCF.Align.GuardReadAccept using (rΩ₁; gΩ₁; r2; rψ₁₁)
open import OCF.Align.GuardWeakRd using (Tc-of; Tc-F)
open import OCF.Align.GuardReadRs using (Rs-add)
open import OCF.Align.GuardTightBase using (Tc)
open import OCF.Align.GuardTightAccept using (xΩ₁; x2; x3; xf0; xf0s; Cf-xΩ₁; Cf-x2; Cf-x3; Cf-f0; g2; e1; e2; Ω₁ᶜ)
import OCF.Align.GuardTightUni as Uni
open Uni Dom₀ using (Good-add)
open import OCF.Align.GuardWeakTree using (T₀ʷ)

-- 值的读数: ω·a + b 记成 1000a+b, 对 < ω² 与字面形状无关 (极限看 f 6, f 7)
open import Data.Nat using (_+_; _∸_; _/_; _*_)

eqB : ℕ → ℕ → ℕ → ℕ → ℕ
eqB zero zero a b = a
eqB (suc m) (suc n) a b = eqB m n a b
eqB m n a b = b

vEₖ : ℕ → Ordᴵ → ℕ
vEₖ k zero = 0
vEₖ k (suc a) = suc (vEₖ k a)
vEₖ k (lim f s) = eqB (vEₖ (3 + k) (f k)) (vEₖ (3 + k) (f (suc k))) (vEₖ (3 + k) (f k)) (1000 * suc (vEₖ (3 + k) (f k) / 1000))

vE : Ordᴵ → ℕ
vE = vEₖ 3

data Dir : Set where
  L : ℕ → Dir
  B : ℕ → Dir
  W : ℕ → Dir
  V : ℕ → Dir
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

fnat : (a : Ordᴵ) → Maybe (Σ ℕ λ n → a ≅ᴵ natᴵ n)
fnat zero = just (0 , z≅)
fnat (suc a) with fnat a
... | just (n , e) = just (suc n , s≅ e)
... | nothing = nothing
fnat (lim _ _) = nothing

leω : (c : Ordᴵ) → Maybe (c ⊑ᴵ ωᴵ)
leω zero = just z⊑
leω (suc a) with fnat a
... | just (n , e) = just (s⊑ e (lim (suc n) zero))
... | nothing = nothing
leω (lim _ _) = nothing

-- ω²: 极限的极限
ωm : ℕ → Ordᴵ
ωm zero = ωᴵ
ωm (suc n) = lim (iterᴵ (ωm n)) (λ k → Sim→⊑ᴵ suc)

ωsq : Ordᴵ
ωsq = lim ωm (λ n → Sim→⊑ᴵ (λ q → lim 0 q))

ω⊑sq : ωᴵ ⊑ᴵ ωsq
ω⊑sq = Sim→⊑ᴵ (λ q → lim 0 q)

-- 宽度 w: lim 的下标 < w, 分支 c+k (k < w); ω 探针: 分支 ω+j (j < v), 当 c 是字面有限
mis : ℕ → ℕ → ℕ → List Dir → Z → Z → Maybe Mis
misL : ℕ → ℕ → ℕ → ℕ → List Dir → (ℕ → Z) → (ℕ → Z) → Maybe Mis
misB : ℕ → ℕ → ℕ → ℕ → List Dir → ∀ {c c′ : Ordᴵ} → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → ((η : Ordᴵ) → c′ ⊑ᴵ η → Z) → Maybe Mis
misW : ℕ → ℕ → ℕ → ℕ → List Dir → ∀ {c c′ : Ordᴵ} → c ⊑ᴵ ωᴵ → c′ ⊑ᴵ ωᴵ → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → ((η : Ordᴵ) → c′ ⊑ᴵ η → Z) → Maybe Mis
misΩ : ℕ → ℕ → ℕ → List Dir → (c c′ : Ordᴵ) → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → ((η : Ordᴵ) → c′ ⊑ᴵ η → Z) → Maybe Mis
mis zero w v p _ _ = nothing
mis (suc d) w v p Z.zero Z.zero = nothing
mis (suc d) w v p (Z.suc x) (Z.suc y) = mis d w v (p ++ (S ∷ [])) x y
mis (suc d) w v p (Z.lim f) (Z.lim g) = misL w d w v p f g
mis (suc d) w v p (Z.ĉᴸ c z zg o₀ o) (Z.ĉᴸ c′ z′ zg′ o₀′ o′) =
  eqn (vE c) (vE c′) (just (bnd p (vE c) (vE c′))) (orM (mis d w v (p ++ (F ∷ [])) o₀ o₀′) (orM (misB w d w v p o o′) (misΩ d w v p c c′ o o′)))
mis (suc d) w v p _ _ = just (knd p)
misL zero d w v p f g = nothing
misL (suc n) d w v p f g = orM (mis d w v (p ++ (L n ∷ [])) (f n) (g n)) (misL n d w v p f g)
misB zero d w v p o o′ = nothing
misB (suc k) d w v p {c} {c′} o o′ = orM (mis d w v (p ++ (B k ∷ [])) (o (iterᴵ c k) (up⊑ k)) (o′ (iterᴵ c′ k) (up⊑ k))) (misB k d w v p o o′)
misΩ d w zero p c c′ o o′ = nothing
misΩ d w (suc v) p c c′ o o′ with leω c | leω c′
... | just e | just e′ = misW (suc v) d w (suc v) p e e′ o o′
... | _ | _ = nothing
misW zero d w v p e e′ o o′ = nothing
misW (suc j) d w v p {c} {c′} e e′ o o′ =
  orM (mis d w v (p ++ (W j ∷ [])) (o (iterᴵ ωᴵ j) (⊑ᴵ-trans e (up⊑ j))) (o′ (iterᴵ ωᴵ j) (⊑ᴵ-trans e′ (up⊑ j)))) (misW j d w v p e e′ o o′)

U-x1 : Tc xΩ₁
U-x1 = Tc-of rΩ₁ gΩ₁
U-x2 : Tc x2
U-x2 = Tc-of r2 g2
U-x3 : Tc x3
U-x3 = Tc-of (Rs-add r2 e2 rΩ₁ e1) (Good-add {σ = λ q → q} g2 e2 gΩ₁)
U-f0 : Tc xf0
U-f0 = Tc-F zero

u1 u11 u12 u2 u21 u3 uf0 : Z
u1 = T₀ʷ xΩ₁ Cf-xΩ₁ U-x1
u11 = T₀ʷ (sucL xΩ₁) (proj₁ Cf-xΩ₁ , s≈ (proj₂ Cf-xΩ₁)) U-x1
u12 = T₀ʷ (sucL (sucL xΩ₁)) (proj₁ Cf-xΩ₁ , s≈ (s≈ (proj₂ Cf-xΩ₁))) U-x1
u2 = T₀ʷ x2 Cf-x2 U-x2
u21 = T₀ʷ (sucL x2) (proj₁ Cf-x2 , s≈ (proj₂ Cf-x2)) U-x2
u3 = T₀ʷ x3 Cf-x3 U-x3
uf0 = T₀ʷ xf0 Cf-f0 U-f0

pc : List Dir → ℕ
pc [] = 1
pc (L n ∷ p) = (10 + n) + 100 * pc p
pc (B n ∷ p) = (30 + n) + 100 * pc p
pc (W n ∷ p) = (50 + n) + 100 * pc p
pc (V n ∷ p) = (60 + n) + 100 * pc p
pc (F ∷ p) = 70 + 100 * pc p
pc (S ∷ p) = 71 + 100 * pc p

code : Maybe Mis → ℕ
code nothing = 0
code (just (bnd p a b)) = a + 10000 * (b + 10000 * pc p)
code (just (knd p)) = 9999 + 10000 * (9999 + 10000 * pc p)

-- 沿给定路径比: 每一步比种类与界. 步子不适用就停 (算一致).
chk : List Dir → List Dir → Z → Z → Maybe Mis
chk p [] _ _ = nothing
chk p (d ∷ ds) Z.zero Z.zero = nothing
chk p (S ∷ ds) (Z.suc x) (Z.suc y) = chk (p ++ (S ∷ [])) ds x y
chk p (d ∷ ds) (Z.suc x) (Z.suc y) = chk (p ++ (S ∷ [])) (d ∷ ds) x y
chk p (L n ∷ ds) (Z.lim f) (Z.lim g) = chk (p ++ (L n ∷ [])) ds (f n) (g n)
chk p (d ∷ ds) (Z.lim f) (Z.lim g) = chk (p ++ (L 1 ∷ [])) ds (f 1) (g 1)
chk p (d ∷ ds) (Z.ĉᴸ c z zg o₀ o) (Z.ĉᴸ c′ z′ zg′ o₀′ o′) =
  eqn (vE c) (vE c′) (just (bnd p (vE c) (vE c′))) (step d)
  where
  step : Dir → Maybe Mis
  step F = chk (p ++ (F ∷ [])) ds o₀ o₀′
  step (B k) = chk (p ++ (B k ∷ [])) ds (o (iterᴵ c k) (up⊑ k)) (o′ (iterᴵ c′ k) (up⊑ k))
  step (W j) with leω c | leω c′
  ... | just e | just e′ = chk (p ++ (W j ∷ [])) ds (o (iterᴵ ωᴵ j) (⊑ᴵ-trans e (up⊑ j))) (o′ (iterᴵ ωᴵ j) (⊑ᴵ-trans e′ (up⊑ j)))
  ... | _ | _ = chk (p ++ (B j ∷ [])) ds (o (iterᴵ c j) (up⊑ j)) (o′ (iterᴵ c′ j) (up⊑ j))
  step (V j) with leω c | leω c′
  ... | just e | just e′ = chk (p ++ (V j ∷ [])) ds (o (iterᴵ ωsq j) (⊑ᴵ-trans (⊑ᴵ-trans e ω⊑sq) (up⊑ j))) (o′ (iterᴵ ωsq j) (⊑ᴵ-trans (⊑ᴵ-trans e′ ω⊑sq) (up⊑ j)))
  ... | _ | _ = chk (p ++ (B j ∷ [])) ds (o (iterᴵ c j) (up⊑ j)) (o′ (iterᴵ c′ j) (up⊑ j))
  step (L n) = chk (p ++ (B n ∷ [])) ds (o (iterᴵ c n) (up⊑ n)) (o′ (iterᴵ c′ n) (up⊑ n))
  step S = chk (p ++ (F ∷ [])) ds o₀ o₀′
chk p _ (Z.lim _) Z.zero = just (knd p)
chk p _ x y = just (knd p)

chkAll : List (List Dir) → Z → Z → Maybe Mis
chkAll [] x y = nothing
chkAll (p ∷ ps) x y = orM (chk [] p x y) (chkAll ps x y)

```

## §1 路径 `p₁`: 极限的帧

**上一轮的差别在这里没有了.** $\psi_0(\Omega_{\Omega+1})$, 路径 `p₁`: 这棵树的界 $\omega$, 塔 $\omega$; `T₀′` 是 $\omega+1$ (对照).

```agda
lim-w : vE (bdOf (proj₁ (walkP p₁ u11 (tq 0 (suc zero))))) ≡ 1000
lim-w = refl

lim-q : vE (bdOf (proj₂ (walkP p₁ u11 (tq 0 (suc zero))))) ≡ 1000
lim-q = refl

lim-old : vE (bdOf (proj₁ (walkP p₁ tgt₁′ (tq 0 (suc zero))))) ≡ 1001
lim-old = refl
```

## §2 对塔: 穷尽, 看界

```agda
m-1 : code (mis 9 3 2 [] u1 (tq 0 zero)) ≡ 0
m-1 = refl

m-11 : code (mis 8 3 2 [] u11 (tq 0 (suc zero))) ≡ 0
m-11 = refl

m-12 : code (mis 7 3 2 [] u12 (tq 0 (suc (suc zero)))) ≡ 0
m-12 = refl

m-2 : code (mis 4 3 2 [] u2 (tq 1 zero)) ≡ 0
m-2 = refl

m-21 : code (mis 4 3 2 [] u21 (tq 1 (suc zero))) ≡ 0
m-21 = refl

m-3 : code (mis 4 3 2 [] u3 (tq 2 zero)) ≡ 0
m-3 = refl

m-f0 : code (mis 5 3 2 [] uf0 tqω) ≡ 0
m-f0 = refl
```

## §3 对照: 比较器看得见差别

```agda
nz? : ℕ → Bool
nz? zero = false
nz? (suc _) = true

ctl₁ : nz? (code (mis 7 3 0 [] u21 (tq 1 zero))) ≡ true
ctl₁ = refl

ctl₂ : nz? (code (chk [] (L 1 ∷ F ∷ L 2 ∷ []) u11 (tq 0 (suc (suc zero))))) ≡ true
ctl₂ = refl
```

## §4 对塔: 随机路径, 长度 10

```agda
ps-u11 : List (List Dir)
ps-u11 =
  (L 2 ∷ W 1 ∷ L 2 ∷ L 2 ∷ L 2 ∷ B 0 ∷ L 1 ∷ L 0 ∷ F ∷ L 2 ∷ []) ∷
  (B 2 ∷ B 2 ∷ L 2 ∷ L 0 ∷ L 1 ∷ F ∷ B 1 ∷ L 1 ∷ F ∷ F ∷ []) ∷
  (L 0 ∷ L 1 ∷ L 2 ∷ V 0 ∷ B 1 ∷ B 2 ∷ L 0 ∷ F ∷ L 0 ∷ W 1 ∷ []) ∷
  (L 0 ∷ W 0 ∷ L 0 ∷ L 2 ∷ L 2 ∷ F ∷ B 1 ∷ L 1 ∷ L 2 ∷ B 0 ∷ []) ∷
  (L 0 ∷ L 2 ∷ B 0 ∷ B 0 ∷ L 1 ∷ V 0 ∷ L 2 ∷ L 2 ∷ V 0 ∷ L 2 ∷ []) ∷
  (L 0 ∷ L 2 ∷ V 0 ∷ L 1 ∷ L 1 ∷ L 2 ∷ L 1 ∷ L 0 ∷ L 2 ∷ F ∷ []) ∷
  (L 1 ∷ L 2 ∷ L 2 ∷ L 2 ∷ L 2 ∷ L 1 ∷ L 1 ∷ W 0 ∷ B 0 ∷ B 2 ∷ []) ∷
  (L 2 ∷ W 2 ∷ L 0 ∷ L 0 ∷ F ∷ L 2 ∷ L 2 ∷ L 2 ∷ L 0 ∷ L 2 ∷ []) ∷
  []

p-u11 : code (chkAll ps-u11 u11 (tq 0 (suc zero))) ≡ 0
p-u11 = refl

ps-u2 : List (List Dir)
ps-u2 =
  (F ∷ W 2 ∷ L 1 ∷ W 0 ∷ B 0 ∷ L 2 ∷ L 0 ∷ L 1 ∷ F ∷ V 0 ∷ []) ∷
  (L 2 ∷ V 0 ∷ F ∷ V 1 ∷ W 2 ∷ L 0 ∷ L 0 ∷ L 1 ∷ L 0 ∷ L 2 ∷ []) ∷
  (L 0 ∷ W 2 ∷ B 0 ∷ B 1 ∷ L 2 ∷ W 1 ∷ V 0 ∷ W 2 ∷ L 2 ∷ L 0 ∷ []) ∷
  (F ∷ L 0 ∷ V 1 ∷ B 1 ∷ V 1 ∷ L 2 ∷ L 2 ∷ L 2 ∷ L 0 ∷ L 0 ∷ []) ∷
  (L 2 ∷ B 1 ∷ L 0 ∷ L 1 ∷ B 0 ∷ F ∷ B 1 ∷ B 1 ∷ L 1 ∷ L 1 ∷ []) ∷
  (L 2 ∷ W 0 ∷ W 1 ∷ L 1 ∷ L 1 ∷ L 0 ∷ B 1 ∷ W 0 ∷ L 1 ∷ V 1 ∷ []) ∷
  (L 2 ∷ L 1 ∷ B 2 ∷ L 0 ∷ W 1 ∷ W 0 ∷ B 1 ∷ F ∷ L 2 ∷ L 1 ∷ []) ∷
  (L 1 ∷ L 1 ∷ L 1 ∷ B 2 ∷ L 0 ∷ F ∷ B 1 ∷ V 0 ∷ L 2 ∷ L 0 ∷ []) ∷
  []

p-u2 : code (chkAll ps-u2 u2 (tq 1 zero)) ≡ 0
p-u2 = refl

ps-u21 : List (List Dir)
ps-u21 =
  (B 2 ∷ B 0 ∷ L 1 ∷ F ∷ V 0 ∷ L 1 ∷ L 2 ∷ L 2 ∷ L 0 ∷ L 2 ∷ []) ∷
  (B 2 ∷ B 1 ∷ L 1 ∷ L 0 ∷ L 2 ∷ V 1 ∷ F ∷ B 1 ∷ L 0 ∷ L 0 ∷ []) ∷
  (L 1 ∷ F ∷ B 1 ∷ W 0 ∷ W 0 ∷ L 0 ∷ L 1 ∷ B 0 ∷ L 2 ∷ W 2 ∷ []) ∷
  (W 2 ∷ L 2 ∷ F ∷ B 0 ∷ L 2 ∷ L 2 ∷ F ∷ F ∷ W 2 ∷ L 2 ∷ []) ∷
  (V 0 ∷ L 1 ∷ V 1 ∷ F ∷ L 2 ∷ L 0 ∷ F ∷ L 0 ∷ F ∷ L 2 ∷ []) ∷
  (L 0 ∷ B 0 ∷ V 1 ∷ L 2 ∷ L 2 ∷ L 1 ∷ L 2 ∷ F ∷ L 2 ∷ F ∷ []) ∷
  (V 0 ∷ B 0 ∷ L 1 ∷ L 1 ∷ L 1 ∷ L 2 ∷ L 2 ∷ L 2 ∷ F ∷ B 2 ∷ []) ∷
  (F ∷ L 2 ∷ F ∷ W 2 ∷ L 1 ∷ W 2 ∷ F ∷ F ∷ W 2 ∷ F ∷ []) ∷
  []

p-u21 : code (chkAll ps-u21 u21 (tq 1 (suc zero))) ≡ 0
p-u21 = refl

ps-u3 : List (List Dir)
ps-u3 =
  (L 1 ∷ W 1 ∷ F ∷ W 0 ∷ L 1 ∷ W 0 ∷ W 0 ∷ B 1 ∷ L 2 ∷ W 1 ∷ []) ∷
  (F ∷ B 0 ∷ L 0 ∷ L 2 ∷ B 1 ∷ L 2 ∷ F ∷ L 1 ∷ W 1 ∷ L 0 ∷ []) ∷
  (L 2 ∷ L 1 ∷ L 2 ∷ L 0 ∷ W 0 ∷ L 1 ∷ B 1 ∷ V 0 ∷ L 0 ∷ L 0 ∷ []) ∷
  (W 2 ∷ W 2 ∷ V 0 ∷ F ∷ V 1 ∷ L 0 ∷ B 0 ∷ W 1 ∷ L 1 ∷ W 2 ∷ []) ∷
  (L 2 ∷ B 1 ∷ L 1 ∷ L 1 ∷ L 0 ∷ L 1 ∷ V 0 ∷ L 1 ∷ L 2 ∷ F ∷ []) ∷
  (F ∷ L 2 ∷ F ∷ B 1 ∷ V 0 ∷ L 0 ∷ B 1 ∷ L 2 ∷ L 1 ∷ F ∷ []) ∷
  (L 1 ∷ L 1 ∷ F ∷ F ∷ V 0 ∷ F ∷ W 0 ∷ F ∷ B 0 ∷ L 1 ∷ []) ∷
  []

p-u3 : code (chkAll ps-u3 u3 (tq 2 zero)) ≡ 0
p-u3 = refl

ps-uf0 : List (List Dir)
ps-uf0 =
  (L 1 ∷ W 2 ∷ F ∷ L 2 ∷ L 2 ∷ L 1 ∷ L 1 ∷ L 1 ∷ F ∷ L 1 ∷ []) ∷
  (L 1 ∷ F ∷ F ∷ L 2 ∷ L 1 ∷ B 0 ∷ F ∷ B 1 ∷ L 1 ∷ L 2 ∷ []) ∷
  (L 1 ∷ L 0 ∷ V 1 ∷ L 1 ∷ F ∷ L 2 ∷ L 0 ∷ L 0 ∷ L 1 ∷ L 2 ∷ []) ∷
  (L 2 ∷ L 1 ∷ F ∷ B 1 ∷ B 2 ∷ W 0 ∷ V 0 ∷ L 0 ∷ F ∷ L 2 ∷ []) ∷
  (F ∷ L 1 ∷ F ∷ B 2 ∷ F ∷ F ∷ B 0 ∷ V 0 ∷ W 0 ∷ F ∷ []) ∷
  (L 1 ∷ L 2 ∷ L 1 ∷ F ∷ L 0 ∷ W 0 ∷ F ∷ F ∷ L 2 ∷ L 1 ∷ []) ∷
  (L 1 ∷ W 0 ∷ W 1 ∷ W 2 ∷ W 0 ∷ L 1 ∷ L 1 ∷ L 2 ∷ L 2 ∷ B 0 ∷ []) ∷
  (L 1 ∷ F ∷ L 1 ∷ L 0 ∷ L 2 ∷ L 2 ∷ L 0 ∷ L 1 ∷ W 2 ∷ L 1 ∷ []) ∷
  []

p-uf0 : code (chkAll ps-uf0 uf0 (tqω)) ≡ 0
p-uf0 = refl

```

## §5 种类: 对记号

```agda
k-11 : dfZ 10 2 tΩ11 u11 ≡ nothing
k-11 = refl
```
