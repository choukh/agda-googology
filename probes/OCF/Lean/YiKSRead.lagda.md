# 龙骨的陈述 (主线): 层号的读法, Q, K(n), 与 K(2) 的归约

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 读法 `Rd Lo ℓ ν` ("记号下标 ν 不高于层号 ℓ"; 零, 后继, ℕ 极限, Ω 形状各一条, 另有沿字面孩子的放宽) 以低层的树对记号的关系 `Lo` 为参数.
> 编译定理, 无前提: `rd-tw1` (`tw 1` 读作 Ω), `rd-fin`, `rd-kl→tw` (`tw (n+1)` 的读法不低于龙骨层号 `kl n` 的); `k1 : K 1`; `kl→K : KL n → K (suc n)`; `stepΩ` (Ω 形状一步的条件形式), `K2-red` (K(2) 归约到 `kl 1` 的逐行), `row0₂` (第 0 行成立).
> 只是陈述, 未证: `KL n` (n ≥ 1), `Stepᴷ`, `Rd … (kl 1) (ΩTower 2)`; 第 1 行起未走通, 没有编译的否定. 不涉及上界. 候选 A 的下降在 [YiKSDescA](YiKSDescA.lagda.md), 带前缀的有限层号在 [YiKSFin](YiKSFin.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKSRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
open import OCF.Lean.YiBRValue using (readRW; btbo-tw1ᴿ)
open import OCF.Lean.YiKSDesc
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
open import OCF.Lean.YiEXRow using (row₂-btbo)
open import OCF.Lean.YiANFam using (cof-nat; pred-nat)
import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; cof; c0; c1; cω; cΩ; pred; fsn; fsT; ΩTower; EBOψ; natT)
open import OCF.Align.EboLeanTree using (hc-tower)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; s≼s; ≼l; l≼; ≼-refl; ≼-trans)
```

## 读法

`Val s c`: 记号项 s 有推导, 它的参照不高于第 0 层的树 c 的读回. `Rd Lo ℓ ν` 的规则只经 `cof`, `pred`, `fsn`, `fsT` 看记号:
零 (`r0`), 后继 (`rS`), ℕ 极限 (`rL` 加 `rC`), Ω 形状 (`rΩ`: ν 的余尾是 Ω_{κ+1}, 下标层 k 读作不低于 κ, 被 `Lo k` 关联的 (s, c) 上孩子 `h c` 读作不低于 ν[s]), 沿字面的孩子放宽 (`rC`).

```agda
Val : E.T → Tr zero → Set
Val s c = Σ (HC s) λ h → Rt h ≼ readRW c

module Read (Lo : (k : L) → E.T → Tr k → Set) where
  data Rd : L → E.T → Set where
    r0 : ∀ {ℓ ν} → cof ν ≡ c0 → Rd ℓ ν
    rS : ∀ {h ν} → cof ν ≡ c1 → Rd (h tt) (pred ν) → Rd (nd sS h) ν
    rL : ∀ {ℓ ν} → cof ν ≡ cω → (∀ n → Rd ℓ (fsn ν n)) → Rd ℓ ν
    rΩ : ∀ {k h ν κ} → cof ν ≡ cΩ κ → Rd k κ → (∀ s c → Lo k s c → Rd (h c) (fsT ν s)) → Rd (nd (sΩ k) h) ν
    rC : ∀ {s h ν} (c : Ch s) → Rd (h c) ν → Rd (nd s h) ν
```

第 0 层的树读成层号: 值关系给出读法 (对推导与树的字典序归纳).

```agda
  rd↑ : ∀ {s} (h : HC s) (c : Tr zero) → Rt h ≼ readRW c → Rd (zero ⊕ ↑ zero c) s
  rd↑ (h0 e)    c         q        = r0 e
  rd↑ (h1 e hp) (suc c)   (s≼s q)  = rS e (rd↑ hp c q)
  rd↑ (h1 e hp) (lim f a) (≼l n q) = rC n (rd↑ (h1 e hp) (f n) q)
  rd↑ (hω e hs) c         q        = rL e (λ n → rd↑ (hs n) c (≼-trans (≼l n (≼-refl (Rt (hs n)))) q))
```

`tw 1` 读作 Ω (`ΩTower 1`), 只要 `Lo zero` 蕴涵值关系; 有限层号 `fin n` 读作 n; `tw (n+1)` 以龙骨层号 `kl n` 为字面的孩子.

```agda
  rd-tw1 : (∀ s c → Lo zero s c → Val s c) → Rd (tw 1) (ΩTower 1)
  rd-tw1 lo = rΩ {κ = []} refl (r0 refl) (λ s c l → rd↑ (proj₁ (lo s c l)) c (proj₂ (lo s c l)))

  fin : ℕ → L
  fin zero    = zero
  fin (suc n) = nd sS (λ _ → fin n)

  rd-fin : ∀ n → Rd (fin n) (natT n)
  rd-fin zero    = r0 refl
  rd-fin (suc n) = rS (cof-nat n) (subst (Rd (fin n)) (sym (pred-nat n)) (rd-fin n))

  rd-kl→tw : ∀ n {ν} → Rd (kl n) ν → Rd (tw (suc n)) ν
  rd-kl→tw n r = rC (proj₁ (Ωt (tw n))) r
```

前提可满足: 第 0 层取值关系, 其余层号取空关系.

```agda
Lo⁰ : (k : L) → E.T → Tr k → Set
Lo⁰ zero     = Val
Lo⁰ (nd _ _) = λ _ _ → ⊥

rd-tw1⁰ : Read.Rd Lo⁰ (tw 1) (ΩTower 1)
rd-tw1⁰ = Read.rd-tw1 Lo⁰ (λ s c l → l)
```

## Q 与 K

`Q₀ ℓ o ν`: ψ₀(Ω_ν) 的参照不高于层号 ℓ 上 Ω 树的标准折叠. `K n` 是台账 V140 的陈述 (`EBOψ (suc n)` 就是 ψ₀(Ω_{ΩTower n})); `KL n` 是龙骨层号上的同一陈述, 读法高一级.

```agda
Q₀ : (ℓ : L) → Ok ℓ → E.T → Set
Q₀ ℓ o ν = (h : HC (E.ψ [] (E.Ωt ν) ∷ [])) → Rt h ≼ readRW (F₀ ℓ o)

K KL Stepᴷ : ℕ → Set
K n     = Q₀ (tw n) (Ok-tw n) (ΩTower n)
KL n    = Q₀ (kl n) (okl n) (ΩTower (suc n))
Stepᴷ n = K n → KL n

_ : K 2 ≡ ((h : HC (EBOψ 3)) → Rt h ≼ readRW (twᶜ 2))
_ = refl

kl→K : ∀ n → KL n → K (suc n)
kl→K n q h = keel-from n (q h)

k1 : K 1
k1 h = ≼-trans (tree-≼ refl h (hc-tower 2)) (≼-trans row₂-btbo btbo-tw1ᴿ)
```

## K(2) 归约到 `kl 1` 的逐行

Ω 形状层号一步的条件形式 (`stepΩ`): 余尾 ω 的记号项, 每个基本列项不高于某个链点孩子上的标准折叠, 就不高于该层号上的标准折叠. `kl 1` 是 Ω 形状层号, 孩子 `hs c`; 它的标准折叠的第 m 行是孩子 `hs (z₂ m)` 上的标准折叠, 链 `z₂` 是折叠朝第 0 层的回灌.

```agda
fs-sup : ∀ {t} (h : HC t) (w : cof t ≡ cω) {Y : O.Ordᶜ O.zero} → (∀ n → Rt (hω-inv h w n) ≼ Y) → Rt h ≼ Y
fs-sup (h0 e)    w q with trans (sym e) w
... | ()
fs-sup (h1 e _)  w q with trans (sym e) w
... | ()
fs-sup (hω _ hs) w  q = l≼ q

stepΩ : ∀ {t} (hd : HC t) (w : cof t ≡ cω) (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h))
  → (∀ n → Σ ℕ λ m → Rt (hω-inv hd w n) ≼ readRW (F₀ (h (chΩ k h o m)) (proj₂ o (chΩ k h o m))))
  → Rt hd ≼ readRW (F₀ (nd (sΩ k) h) o)
stepΩ hd w k h o prem = fs-sup hd w (λ n → ≼-trans (proj₂ (prem n)) (rowsΩ k h o (proj₁ (prem n))))

hs : Tr zero → L
hs c = tw 1 ⊕ (zero ⊕ ↑ (zero ⊕ ↑ zero c) (proj₁ (Ωt (zero ⊕ ↑ zero c))))

z₂ : ℕ → Tr zero
z₂ = chΩ zero hs (okl 1)

Row₂ᴸ : ℕ → ℕ → Set
Row₂ᴸ n m = Rt (hω-inv (hc-tower 3) refl n) ≼ readRW (F₀ (hs (z₂ m)) (proj₂ (okl 1) (z₂ m)))

rows₂ : ∀ m → readRW (F₀ (hs (z₂ m)) (proj₂ (okl 1) (z₂ m))) ≼ readRW (twᶜ 2)
rows₂ m = ≼-trans (rowsΩ zero hs (okl 1) m) (keel 1)

K2-red : (∀ n → Σ ℕ λ m → Row₂ᴸ n m) → K 2
K2-red prem h = ≼-trans (tree-≼ refl h (hc-tower 3))
  (fs-sup (hc-tower 3) refl (λ n → ≼-trans (proj₂ (prem n)) (rows₂ (proj₁ (prem n)))))
```

第 0 行: 记号一侧是 ψ₀(Ω_Ω), 树一侧是层号 `suc (tw 1)` 上的标准折叠, 由 `k1` 与一步下降得出.

```agda
_ : hs (z₂ 0) ≡ nd sS (λ _ → tw 1)
_ = refl

row0₂ : Row₂ᴸ 0 0
row0₂ = ≼-trans (k1 (hω-inv (hc-tower 3) refl 0)) (step¹ sS (λ _ → tw 1) (proj₂ (okl 1) zero))
```
