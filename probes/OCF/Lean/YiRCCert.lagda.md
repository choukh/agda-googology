# 验收 (统一规则 `φ`, `YiCertFold`): 塔第 1 项上目标第 2 层的那一支, 形状与保留判定

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判据 `CritB n` 与 `YiRBCrit.CritAt` 同式, 折叠换成 `YiCertFold.ψ`. 判据未证也未否定 (未走通); `Self.PF`, `LF` 没有搬.
> 编译定理, 无前提: 那一支逐字是锚在第 2 层、目标第 2 层 (路径 `self`) 的 `φ` (`b-shape`); 孩子 `nat (n+2)` 的支是部分和极限, 各项是回灌链经 `φ` (`b-chain`); `φ` 的保留判定只留第 0 层的槽位 (`kcaseB`, `keep-0`, `drop-≥1`).
> 与 [YiRCCandA](YiRCCandA.lagda.md) 逐条同式 (候选 A 在这一支上 `cut` 交出 `tt`, 走的也是 `φ`); 卡在同一个结点: 第 1 层的槽位不保留 (`drop-1`, `node-1`), 记号一侧 ψ₂ 保持共尾 (`pen-1`). 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRCCert where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiCertPath
open import OCF.Lean.YiCertFold
open import OCF.Lean.YiCertCheck using (o¹; h₁; c2)
import OCF.Align.EboLeanDef as E
open E using (natT; sucT; cmpᵀ)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; Pen)
open import OCF.Lean.YiCLFam using (nat; fn; M)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pos⁼)

two : L
two = fn 2

o2 : Ok two
o2 = proj₂ o¹ c2

kk : zero ≤ two
kk = kh o¹ c2

okf : (n : ℕ) → Ok (fn n)
okf n = proj₂ o¹ (nat n)

abf : (m : ℕ) → Ab zero (fn m)
abf m = proj₂ (proj₁ o¹) (nat m)
```

## 那一支与判据

```agda
blk : (c : Tr zero) → Tr (tw 1)
blk c = up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))

gᴮ : Tr zero → Tr⁺ two
gᴮ c = ψ (tw 1) o¹ (B₀ (tw 1)) two (inc c2 self) (Ωt two) (blk c)

CritB : ℕ → Set
CritB n = M 2 (ψᴺ 2 (Ωᴺ n)) (proj₁ (gᴮ (nat n)))

wholeᴮ : Σ (Pos two) λ q → Σ (Br two q → Tr zero) λ cv →
  proj₁ (ψ (tw 1) o¹ (B₀ (tw 1)) two (inc c2 self) (Ωt two) (proj₁ (Ωt (tw 1))))
  ≡ Ω q (λ z → proj₁ (gᴮ (cv z)))
wholeᴮ = _ , _ , refl
```

## 形状

分支侧一行直接是 `φ`; 锚的底与源的底都是默认底.

```agda
φ₂ : (m : ℕ) → Base (fn m) → Tr⁺ two → Tr (fn m) → Tr⁺ two
φ₂ m Bm β y = φ two o2 (B₀ two) kk two self (fn m) (okf m) (abf m) Bm β y

b-shape : (c : Tr zero)
  → proj₁ (gᴮ c)
  ≡ proj₁ (φ two o2 (B₀ two) kk two self (h₁ c) (proj₂ o¹ c) (proj₂ (proj₁ o¹) c) (B₀ (h₁ c)) (Ωt two) (proj₁ (Ωt (h₁ c))))
b-shape c = refl

b-fin : ∀ n → proj₁ (gᴮ (nat n)) ≡ proj₁ (φ₂ n (B₀ (fn n)) (Ωt two) (proj₁ (Ωt (fn n))))
b-fin n = refl
```

孩子 `nat (n+2)`: 顶上的结点 (槽位在层号 `fn (n+1)`) 不保留; 各项是子层号上自身折叠的回灌链 `zᴮ n k` 再经 `φ`.

```agda
zᴮ : (n : ℕ) → ℕ → Tr (fn (suc n))
zᴮ n = iter (λ c → proj₁ (next⁺ (ψ (fn (suc n)) (okf (suc n)) (B₀ (fn (suc n))) (fn (suc n)) self (Ωt (fn (suc n))) c))) zero

b-chain : ∀ n → proj₁ (gᴮ (nat (suc (suc n))))
        ≡ proj₁ (limc⁺ (λ k → next⁺ (φ₂ (suc n) (B₀ (fn (suc n))) (Ωt two) (zᴮ n k))))
b-chain n = refl
```

## `φ` 的保留判定 (锚第 2 层, 目标第 2 层)

源层 `fn m` 里层号 i 的槽位: i ≥ 1 时不保留, i = 0 时保留.

```agda
KB : ∀ {m i} → Sb m i → Set
KB {m} si = Keep two (Br⁼ (fn m) (pos⁼ si)) (bz⁼ (fn m) (pos⁼ si))

kB : ∀ {m i} (si : Sb m i) → KB si
kB {m} si = kpA two o2 kk self (abf m) (pos⁼ si)

kcaseB : ∀ {m i} (si : Sb m i) (Q : KB si → Set)
       → (1 ≤ⁿ i → Q nothing)
       → ((q : Pos two) (cv : Br two q → Br⁼ (fn m) (pos⁼ si)) (eq : cv (fromBr two q zero) ≡ bz⁼ (fn m) (pos⁼ si))
            → i ≡ 0 → Q (just (q , cv , eq)))
       → Q (kB si)
kcaseB {m = zero}  s0      Q dr kc = kc _ _ refl refl
kcaseB {m = suc m} s0      Q dr kc = dr (s≤s z≤n)
kcaseB {m = suc m} (ss si) Q dr kc = kcaseB si Q dr kc

drop-≥1 : ∀ {m i} (si : Sb m (suc i)) → kB si ≡ nothing
drop-≥1 si = kcaseB si (λ K → K ≡ nothing) (λ _ → refl) (λ _ _ _ ())

IsJust : ∀ {m i} (si : Sb m i) → KB si → Set
IsJust si (just _) = ⊤
IsJust si nothing  = 1 ≤ⁿ 0

keep-0 : ∀ {m} (si : Sb m 0) → IsJust si (kB si)
keep-0 si = kcaseB si (IsJust si) (λ le → le) (λ _ _ _ _ → tt)
```

## 卡住的结点

第 1 层的槽位: 折叠不保留 (取回灌链的部分和极限), 记号一侧 ψ₂ 落在 "保持共尾" 的情形 (`Pen`, `cofK` 适用). `M 2` 里共尾是 Ω 的项只能对着保留的结点 (或经 `mw`, `mU` 松弛到一个).

```agda
drop-1 : ∀ {m} (si : Sb m 1) → kB si ≡ nothing
drop-1 = drop-≥1

s1 : ∀ m → Sb (suc m) 1
s1 zero    = s0
s1 (suc m) = ss (s1 m)

pen-1 : Pen (cmpᵀ (sucT (natT 1)) (natT 2))
pen-1 = inj₂ refl

isLim : ∀ {X : Set} {x₀ : X} (K : Keep two X x₀) → K ≡ nothing → (G : X → Tr⁺ two) (s : X → X)
  → Σ (ℕ → Tr two) λ F → Σ ((k : ℕ) → two ⊢ F k ◃ F (suc k)) λ a → proj₁ (node⁺ K G s) ≡ lim F a
isLim .nothing refl G s = _ , _ , refl

node-1 : ∀ m (Bm : Base (fn (suc (suc m)))) (β : Tr⁺ two) (g : Br⁼ (fn (suc m)) (pos⁼ (s1 m)) → Tr (fn (suc (suc m))))
  → Σ (ℕ → Tr two) λ F → Σ ((k : ℕ) → two ⊢ F k ◃ F (suc k)) λ a
  → proj₁ (φ₂ (suc (suc m)) Bm β (Ω (inj₂ (tt , pos⁼ (s1 m))) g)) ≡ lim F a
node-1 m Bm β g = isLim (kB (ss (s1 m))) (drop-1 (ss (s1 m))) _ _
```
