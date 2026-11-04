# `FeedGood`: 验收 (判决: 全部通过, 有限测试, 不是证明)

> **验收节, 记号只在本文件.** 结论写在 [FeedGood](FeedGood.lagda.md). 比较器 `dfL`, `dfZ`, `Tgt` 来自 [GuardTightAccept](GuardTightAccept.lagda.md). `dfs`: 两棵层号沿同样的路径比界, 第一个差别的路径 (下标: 极限第 $n$ 项; 闭包 0 是第一支, $k+1$ 是分支 界$+k$). **全部是有限测试.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FeedGoodAccept where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.GuardTightCum using (Ordᴵ; natᴵ; zero; suc; lim; _⊑ᴵ_; _≅ᴵ_; _<ᴵ_; z≅; s≅; s⊑; z⊑)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightUp using (F⁺; feedL; u₀; lvl)
open import OCF.Align.GuardReadRd using (Tc-Lv₅)
open import OCF.Align.FeedGoodFirst using (u₁; T₁; Cf-u₁)
open import OCF.Align.FeedGoodTc using (u₁ᵗ; T₁ᵗ)
open import OCF.Align.GuardTightAccept using (dfL; dfZ; is-ok; tF; tLv₅; tΩ₂Ω; module Tgt; τₙ; one⊑nat; toN; xΩ₁; Cf-xΩ₁; Tc-x1)
open import OCF.Align.EBO using (fsn; Ωt)
open import OCF.Align.Uniform5Wall using (ψ₁)
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (F; Lv₅; Cf-Lv₅)
```

## §1 第二项对 EBO

`feedL u₀` 对 $\psi_1(\Omega_\Omega)$ 的记号, 比种类 (界不比: `no-≈₁` 说界就是不同的). `T₁`, `T₁ᵗ` 对 $\psi_0(\Omega_{\Omega_2})$ 的第 2 项. 对照: 换一项就不一致.

```agda
c-u₁ : dfL 8 2 tLv₅ (feedL u₀) ≡ nothing
c-u₁ = refl

ctl-u₁ : is-ok (dfL 8 2 (tF 1) (feedL u₀)) ≡ false
ctl-u₁ = refl

c-T₁ : dfZ 6 2 (fsn tΩ₂Ω 1) T₁ ≡ nothing
c-T₁ = refl

c-T₁ᵗ : dfZ 6 2 (fsn tΩ₂Ω 1) T₁ᵗ ≡ nothing
c-T₁ᵗ = refl

ctl-T₁ : is-ok (dfZ 6 2 (fsn tΩ₂Ω 2) T₁) ≡ false
ctl-T₁ = refl

-- 第三项 feedL u₁: 输入的证书是真的 (`Cf-u₁`), 输出没有证书. 只比种类, 只到这个深度
c-u₂ⁱ : dfL 6 2 (ψ₁ (Ωt tLv₅)) (feedL u₁) ≡ nothing
c-u₂ⁱ = refl

c-u₂ᵗ : dfL 6 2 (ψ₁ (Ωt tLv₅)) (feedL u₁ᵗ) ≡ nothing
c-u₂ᵗ = refl

ctl-u₂ : is-ok (dfL 6 2 (ψ₁ (Ωt tLv₅)) (feedL u₀)) ≡ false
ctl-u₂ = refl
```

## §2 比较器: 沿路径比界

```agda
isN : (a : Ordᴵ) → Maybe (Σ ℕ λ k → a ≅ᴵ natᴵ k)
isN zero = just (0 , z≅)
isN (suc a) with isN a
... | just (k , e) = just (suc k , s≅ e)
... | nothing = nothing
isN (lim f s) = nothing

ltN : ∀ k m → Maybe (natᴵ k <ᴵ natᴵ m)
ltN k zero = nothing
ltN k (suc m) with k ≟ m
... | yes refl = just zero
... | no _ with ltN k m
...   | just q = just (suc q)
...   | nothing = nothing

grd : ∀ c m → Maybe (c ⊑ᴵ natᴵ m)
grd zero m = just z⊑
grd (suc a) m with isN a
... | nothing = nothing
... | just (k , e) with m
...   | zero = nothing
...   | suc m′ with ltN k (suc m′)
...     | just q = just (s⊑ e q)
...     | nothing = nothing
grd (lim f s) m = nothing

go : List ℕ → LG → LG
go [] x = x
go (n ∷ p) (suc x) = go (n ∷ p) x
go (n ∷ p) (lim f) = go p (f n)
go (zero ∷ p) (lc c t g) = go p t
go (suc k ∷ p) (lc c t g) with grd c (toN c + k)
... | just e = go p (g _ e)
... | nothing = zero
go (n ∷ p) zero = zero

data R : Set where
  ok : R
  dif : List ℕ → ℕ → ℕ → R

kd : LG → ℕ
kd zero = 0
kd (suc _) = 1
kd (lim _) = 2
kd (lc c _ _) = 10 + toN c

prep : ℕ → R → R
prep n ok = ok
prep n (dif p a b) = dif (n ∷ p) a b

orR : R → R → R
orR ok y = y
orR x y = x

dfs : ℕ → ℕ → LG → LG → R
dfLm : ℕ → ℕ → ℕ → (ℕ → LG) → (ℕ → LG) → R
dfB : ℕ → ℕ → ℕ → (c : Ordᴵ) → (g : (η : Ordᴵ) → c ⊑ᴵ η → LG) → (c′ : Ordᴵ) → (g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → LG) → ℕ → R
dfs zero w x y = ok
dfs (suc d) w zero zero = ok
dfs (suc d) w (suc x) (suc y) = dfs d w x y
dfs (suc d) w (lim f) (lim h) = dfLm d w w f h
dfs (suc d) w (lc c t g) (lc c′ t′ g′) with toN c ≟ toN c′
... | no _ = dif [] (toN c) (toN c′)
... | yes _ = orR (prep 0 (dfs d w t t′)) (dfB d w w c g c′ g′ (toN c))
dfs (suc d) w x y = dif [] (kd x) (kd y)
dfLm d w zero f h = ok
dfLm d w (suc n) f h = orR (dfLm d w n f h) (prep n (dfs d w (f n) (h n)))
dfB d w zero c g c′ g′ m = ok
dfB d w (suc k) c g c′ g′ m with grd c (m + k) | grd c′ (m + k)
... | just e | just e′ = orR (dfB d w k c g c′ g′ m) (prep (suc k) (dfs d w (g _ e) (g′ _ e′)))
... | _ | _ = dfB d w k c g c′ g′ m
```

## §3 恒等读法下界随穿过的分支变: 层号 $\Omega_1+1$

`g-id`, `g-ti`: $\psi_1(\Omega_{\Omega+1})$ 的读回, 恒等读法与紧读法. `Q`: 输出里的一个闭包 (界 2, 路径 `1, 0, 0, 2`). `G 2` 是它的分支 2, `G 3` 是分支 3, `G 3` 的第 0 项与 `G 2` 同形, 这是 `dir` 要的搬运. **恒等读法: 这两份在路径 `1, 0, 1` 上界是 2 对 3 (`c-sib-id`), 所以不是同一个键, `⊴-cross` 的情形. 紧读法: 到这个深度一致 (`c-sib-ti`).** 这两条是这一轮最要紧的测试, 它们说 `Tc-id` 不是 "暂时可用的读法", 而是 `cfF` 的障碍 (判断, 不是定理).

```agda
Eₐ : Ents
Eₐ = ∅ (natᴵ 2)

q₁₁ : suc zero < suc xΩ₁
q₁₁ = suc (bra (natᴵ 2) (one⊑nat 1) zero)

aq₁₁ : Adm (tab Eₐ) q₁₁
aq₁₁ = (natᴵ 2 , refl , zero) , tt

g-id g-ti : LG
g-id = F⁺ (suc xΩ₁) (proj₁ Cf-xΩ₁ , s≈ (proj₂ Cf-xΩ₁)) (Tc-id xΩ₁) Eₐ q₁₁ aq₁₁
g-ti = F⁺ (suc xΩ₁) (proj₁ Cf-xΩ₁ , s≈ (proj₂ Cf-xΩ₁)) Tc-x1 Eₐ q₁₁ aq₁₁

c-Q : kd (go (1 ∷ 0 ∷ 0 ∷ 2 ∷ []) g-id) ≡ 12
c-Q = refl

c-sib-id : dfs 7 2 (go (1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ []) g-id) (go (1 ∷ 0 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ []) g-id) ≡ dif (1 ∷ 0 ∷ 1 ∷ []) 2 3
c-sib-id = refl

c-sib-ti : dfs 7 2 (go (1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ []) g-ti) (go (1 ∷ 0 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ []) g-ti) ≡ ok
c-sib-ti = refl
```

## §4 第 5 站: 界对穿过的分支 $\tau$

`Tgt` 与 [GuardTightAccept](GuardTightAccept.lagda.md) 的 `c-bra*` 同形, 层号换成 `Lv₅`: 顶层 $\mathrm{Lv}_5+1$, 目标 $\Omega_1$ (字面的第一路径), 穿过分支 $\tau$. [GuardTight](GuardTight.lagda.md) 说这里 "判断, 没有测". **测了: 恒等读法界随 $\tau$ 变; `Tc-Lv₅` 不变.**

```agda
pFv : ∀ k → xΩ₁ < F (natᴵ (suc k))
pFv zero = fst (lim 2 (fst zero))
pFv (suc k) = lim 0 (pFv k)

adm-pFvv : ∀ k E → Adm E (pFv k)
adm-pFvv zero E = tt
adm-pFvv (suc k) E = adm-pFvv k E

module Y (k : ℕ) = Tgt {_} {_} {_} Cf-Lv₅ Tc-Lv₅ (τₙ k) (one⊑nat k) xΩ₁ (pFv k) (adm-pFvv k) (suc (τₙ k)) (suc zero)

b-id₁ : Y.Yid 1 ≡ 2
b-id₁ = refl
b-id₂ : Y.Yid 2 ≡ 3
b-id₂ = refl
b-id₄ : Y.Yid 4 ≡ 5
b-id₄ = refl

b-ti₁ : Y.Ytight 1 ≡ 1
b-ti₁ = refl
b-ti₂ : Y.Ytight 2 ≡ 1
b-ti₂ = refl
b-ti₄ : Y.Ytight 4 ≡ 1
b-ti₄ = refl
```
