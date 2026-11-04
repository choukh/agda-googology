# 树侧判据: 接受的测试与定理 (对的树)

> **检验旧树的文件.** 导入 `GuardTightAccept` 只为取现成的层号, 证书与读法; 那个文件读记号, 所以本文件不干净. 判据的定义不在这里. 结论写在 [TreeJudge](TreeJudge.lagda.md).
>
> **定理:** `accept-free` (`TΩ·2` 的 `Goodᴺ`), `accept-tight-Ω₁` (`Good-Ω₁`). 这两条都是搬现成的证书. **其余全部是有限测试 (`refl`):** `run d fd w`: 深度 $d$, 指纹深度 `fd`, 宽度 $w$ 的同头同界取样, `nclo` 是取样到的闭包数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Level using (Ordᴵ; _⊑ᴵ_; ⊑ᴵ-refl; ⊑ᴵ-trans; Sim→⊑ᴵ)
import OCF.Free.Level as FL
open import OCF.Free.Force using (Goodᴺ)
open import OCF.Free.Tree using (TΩ·2)
open import OCF.Free.Closed using (ev₀; certᵀ)
open import OCF.Align.GuardTightAccept using (t1; t11; t2; t21; t3; tf0; tf0s; tf0Ω)
open import OCF.Align.GuardTightCert using (Good-Ω₁)
open import OCF.Align.TreeJudgeObs
```

## §1 读成观察树

```agda
toN : Ordᴵ → ℕ
toN FL.zero = 0
toN (FL.suc a) = suc (toN a)
toN (FL.lim f s) = toN (f 1)

iterᴵ : Ordᴵ → ℕ → Ordᴵ
iterᴵ c zero = c
iterᴵ c (suc k) = FL.suc (iterᴵ c k)

up⊑ : ∀ {c} k → c ⊑ᴵ iterᴵ c k
up⊑ {c} zero = ⊑ᴵ-refl
up⊑ (suc k) = ⊑ᴵ-trans (up⊑ k) (Sim→⊑ᴵ (λ q → FL.suc q))

rd : Z → Obs
rd Z.zero = o0
rd (Z.suc x) = os (rd x)
rd (Z.lim f) = ol (λ n → rd (f n))
rd (Z.ĉᴸ c t₀ g o₀ o) = oc (toN c) (rd t₀) (rd o₀) (λ k → rd (o (iterᴵ c k) (up⊑ k)))
```

## §2 接受: `OCF/Free/Tree` 的 `TΩ·2`

**定理:** 有 `Goodᴺ`. **测试:** 同头同界. 102 个闭包是指纹深度 5 时的分母.

```agda
tfree : Z
tfree = toZ (TΩ·2 ev₀ FL.zero)

accept-free : Goodᴺ tfree
accept-free = certᵀ

n-free : nclo 9 2 (rd tfree) ≡ 102
n-free = refl

hf-free : run 9 7 2 (rd tfree) ≡ nothing
hf-free = refl
```

## §3 接受: `GuardTight` 的 `T₀`

**定理:** 只有 $\Omega_1$ 一处有证书 (`Good-Ω₁`). **测试:** 其余只有同头同界. `t3` 在指纹深度 6 有假警报 (见 [TreeJudgeObs](TreeJudgeObs.lagda.md)), 所以这一组都用 9.

```agda
accept-tight-Ω₁ = Good-Ω₁

hf-t1 : run 9 9 2 (rd t1) ≡ nothing
hf-t1 = refl
hf-t11 : run 9 9 2 (rd t11) ≡ nothing
hf-t11 = refl
hf-t2 : run 9 9 2 (rd t2) ≡ nothing
hf-t2 = refl
hf-t21 : run 9 9 2 (rd t21) ≡ nothing
hf-t21 = refl
hf-t3 : run 9 9 2 (rd t3) ≡ nothing
hf-t3 = refl
hf-tf0 : run 9 9 2 (rd tf0) ≡ nothing
hf-tf0 = refl
hf-tf0s : run 9 9 2 (rd tf0s) ≡ nothing
hf-tf0s = refl
hf-tf0Ω : run 9 9 2 (rd tf0Ω) ≡ nothing
hf-tf0Ω = refl

n-t21 : nclo 9 2 (rd t21) ≡ 250
n-t21 = refl

-- Bachmann 的取样: 没有反例. 大部分走步进了闭包 (超预算), 这个测试力量很弱
reg-t21 : reg 6 20 3 2 [] (rd t21) ≡ okv 42 172
reg-t21 = refl
reg-tf0s : reg 6 20 3 2 [] (rd tf0s) ≡ okv 40 48
reg-tf0s = refl
reg-free : reg 6 20 3 2 [] (rd tfree) ≡ okv 82 120
reg-free = refl
```
