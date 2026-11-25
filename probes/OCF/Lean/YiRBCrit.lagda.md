# 验收 (换基): 塔第 1 项上目标第 2 层的判据, 三种写法并排

> 验收文件 (读记号), 不进成品. 判据 `CritAt g n`: 塔第 1 项的 Ω 树第 `nat n` 支经孩子 2 朝第 2 层的那一行, 对着 ψ₂(Ω_n) (`YiCLFam.M 2`). 编译定理, 无前提: 兄弟孩子写法 `sib-crit` 与目标层 ⊕ c 写法 `tgt-crit` 对一切 n ≥ 3 过判据; 不经上行的版本 `sib-shift`, `tgt-shift` 给 ψ₂(Ω_{n+2}) (n ≥ 1); 孩子取更大的自然数时仍成立 (`sib-crit≥`, `tgt-crit≥`).
> 主线原来那一行只有形状 (`main-shape`, 对一切 c: 第 2 层的 Ω 树加一棵第 0 层的树的嵌入), 判据没有证也没有否定. 目标层 ⊕ c 的写法只是对下标层为第 0 层的参数写出的原型 (`seenʳ`), 不是折叠里的一行; 换基后的层上用 `YiRBSib` 的折叠且不带证据, 那里各行逐字是主线的 (`YiRBSib.row-no`).
> 只到 c = `nat n`; 不涉及 ℕ 极限形状的孩子, 不涉及上界. 两种写法在别处的差别见文末的形状 (`refl`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRBCrit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
import OCF.Lean.YiRWFold as R
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBFam
open import OCF.Lean.YiKVRel using (M⁰; _⊴_; ⊴r; +⊴)
import OCF.Align.EboLeanDef as E
open E using (natT)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiCLFam using (nat; fn; M; m⊴N; Mβ)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth)
open import OCF.Lean.YiCLCrit using (natM)
```

## 判据

`blk c` 是塔第 1 项的 Ω 树的第 c 支 (`Ωtw1`). 前提 `M⁰ (natT n) (nat n)` 可满足 (`pre-ok`).

```agda
two : L
two = fn 2

h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

blk : (c : Tr zero) → Tr (tw 1)
blk c = up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))

Ωtw1 : proj₁ (Ωt (tw 1)) ≡ Ω (inj₁ (inj₁ tt)) blk
Ωtw1 = refl

CritAt : (Tr zero → Tr⁺ two) → ℕ → Set
CritAt g n = M 2 (ψᴺ 2 (Ωᴺ n)) (proj₁ (g (nat n)))

pre-ok : ∀ n → M⁰ (natT n) (nat n)
pre-ok = natM

ΩE : ∀ n → E.Ωt (natT n) ≡ Ωᴺ n
ΩE n = refl
```

## 主线原来那一行

整棵 Ω 树的折叠是保留的结点, 各支是 `gᴹ` (`wholeᴹ`). 各支是第 2 层的 Ω 树加上孩子 c 的 Ω 树折到第 0 层再嵌回.

```agda
gᴹ : Tr zero → Tr⁺ two
gᴹ c = R.ψ (tw 1) (Ok-tw 1) (B₀ (tw 1)) two (inc (nat 2) self) (Ωt two) (blk c)

wholeᴹ : Σ (Pos two) λ q → Σ (Br two q → Tr zero) λ cv →
  proj₁ (R.ψ (tw 1) (Ok-tw 1) (B₀ (tw 1)) two (inc (nat 2) self) (Ωt two) (proj₁ (Ωt (tw 1))))
  ≡ Ω q (λ z → proj₁ (gᴹ (cv z)))
wholeᴹ = _ , _ , refl

main-shape : (c : Tr zero)
  → proj₁ (gᴹ c) ≡ proj₁ (Ωt two) + ι two (proj₁ (R.ψ₀ (h₁ c) (proj₂ (Ok-tw 1) c) (proj₁ (Ωt (h₁ c)))))
main-shape c = refl
```

## 兄弟孩子 c′ + c

```agda
gˢ : Tr zero → Tr⁺ two
gˢ c = ψ (tw 1) (Ok-tw 1) (rb-tw 1) (B₀ (tw 1)) two (inc (nat 2) self) (Ωt two) (blk c)

wholeˢ : Σ (Pos two) λ q → Σ (Br two q → Tr zero) λ cv →
  proj₁ (ψ (tw 1) (Ok-tw 1) (rb-tw 1) (B₀ (tw 1)) two (inc (nat 2) self) (Ωt two) (proj₁ (Ωt (tw 1))))
  ≡ Ω q (λ z → proj₁ (gˢ (cv z)))
wholeˢ = _ , _ , refl

wˢ : (c : Tr zero) → two ≤ h₁ (nat 2 + c)
wˢ c = self ∙ wk (⊕⊑ zero (pre zero (nat 2) c))

sib-shape : (c : Tr zero)
  → proj₁ (gˢ c)
  ≡ proj₁ (ψ (h₁ (nat 2 + c)) (proj₂ (Ok-tw 1) (nat 2 + c)) (rb-no _) (B₀ (h₁ (nat 2 + c))) two (wˢ c) (Ωt two)
             (proj₁ (Ωt (h₁ (nat 2 + c)))))
    + ι two (proj₁ (ψ₀ʳ (h₁ c) (proj₂ (Ok-tw 1) c) (rb-no _) (proj₁ (Ωt (h₁ c)))))
sib-shape c = refl
```

## 目标层 ⊕ c (原型)

下标层是第 0 层时, 对一切目标层 j (带证据) 与一切 c 可写; 起点 β, 底取默认. 行里再 ⊞ 同一条回退项.

```agda
seenʳ : (j : L) → Ok j → Tr⁺ j → Tr zero → Tr⁺ j
seenʳ j oj β c =
  ψ (j ⊕ ↑ zero c) (Ok⊕ j (↑ zero c) oj (OkO↑ j zero tt (z≤ j) c)) (rb-no _) (B₀ (j ⊕ ↑ zero c)) j (lift j (↑ zero c)) β
    (proj₁ (Ωt (j ⊕ ↑ zero c)))

o2 : Ok two
o2 = proj₂ (Ok-tw 1) (nat 2)

gᵗ : Tr zero → Tr⁺ two
gᵗ c = seenʳ two o2 (Ωt two) c ⊞ ψ₀ʳ (h₁ c) (proj₂ (Ok-tw 1) c) (rb-no _) (proj₁ (Ωt (h₁ c)))
```

## 两种写法过判据

层号与路径成对地搬到 `fn (sh n)` 上 (`sh n` 是 n + 2): 兄弟孩子给 `inc` 链, 目标层 ⊕ c 给 `inu` 链.

```agda
sh : ℕ → ℕ
sh zero    = 2
sh (suc n) = suc (sh n)

sh+ : (k : ℕ) → _≡_ {A = ℕ} (suc (sh k)) (suc (suc (suc k)))
sh+ zero    = refl
sh+ (suc k) = cong suc (sh+ k)

sbk : ∀ k → Sb (sh k) 2
sbk zero    = s0
sbk (suc k) = ss (sbk k)

ptk : ∀ k → Pt (sh k) 2
ptk zero    = can s0
ptk (suc k) = pu (ptk k)

Pk : Set
Pk = Σ L λ ℓ → two ≤ ℓ

stepC stepU : Pk → Pk
stepC (ℓ , w) = nd sS (λ _ → ℓ) , inc tt w
stepU (ℓ , w) = nd sS (λ _ → ℓ) , inu (λ _ → w)

eqˢ : ∀ n → (h₁ (nat 2 + nat n) , wˢ (nat n)) ≡ (fn (sh n) , pth (sbk n))
eqˢ zero    = refl
eqˢ (suc n) = cong stepC (eqˢ n)

eqᵗ : ∀ n → (two ⊕ ↑ zero (nat n) , lift two (↑ zero (nat n))) ≡ (fn (sh n) , pt (ptk n))
eqᵗ zero    = refl
eqᵗ (suc n) = cong stepU (eqᵗ n)

SP : E.T → Pk → Set
SP t p = (o : Ok (proj₁ p)) (r : Rb (proj₁ p)) (B : Base (proj₁ p)) (β : Tr⁺ two) → OKB B → M 2 (Ωᴺ 2) (proj₁ β)
       → M 2 t (proj₁ (ψ (proj₁ p) o r B two (proj₂ p) β (proj₁ (Ωt (proj₁ p)))))
```

不经上行: 层号 `fn (sh (suc k))` 的 Ω 树朝第 2 层的折叠对着 ψ₂(Ω_{k+3}).

```agda
shiftC : ∀ k → SP (ψᴺ 2 (Ωᴺ (suc (sh k)))) (fn (sh (suc k)) , pth (sbk (suc k)))
shiftC k o r = sΩ-LF o r (tc (sbk k))

shiftU : ∀ k → SP (ψᴺ 2 (Ωᴺ (suc (sh k)))) (fn (sh (suc k)) , pt (ptk (suc k)))
shiftU k o r = sΩ-LF o r (tu (ptk k))
```

判据: 再上行两层, 层号 `fn (sh (3 + k))` 的 Ω 树的折叠对着 ψ₂(Ω_{3+k}).

```agda
critC : ∀ k → SP (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (fn (sh (suc (suc (suc k)))) , pth (sbk (suc (suc (suc k)))))
critC k o r = liftC o r (pth (sbk (suc (suc k))))
  (liftC (proj₂ o tt) (proj₂ r tt) (pth (sbk (suc k)))
    (subst (λ (m : ℕ) → SΩ (ψᴺ 2 (Ωᴺ m)) (suc (sh k)) 2 (proj₂ (proj₂ o tt) tt) (proj₂ (proj₂ r tt) tt) (pth (sbk (suc k))))
      (sh+ k) (shiftC k (proj₂ (proj₂ o tt) tt) (proj₂ (proj₂ r tt) tt))))

critU : ∀ k → SP (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (fn (sh (suc (suc (suc k)))) , pt (ptk (suc (suc (suc k)))))
critU k o r = liftU o r (pt (ptk (suc (suc k))))
  (liftU (proj₂ o tt) (proj₂ r tt) (pt (ptk (suc k)))
    (subst (λ (m : ℕ) → SΩ (ψᴺ 2 (Ωᴺ m)) (suc (sh k)) 2 (proj₂ (proj₂ o tt) tt) (proj₂ (proj₂ r tt) tt) (pt (ptk (suc k))))
      (sh+ k) (shiftU k (proj₂ (proj₂ o tt) tt) (proj₂ (proj₂ r tt) tt))))

okB₀ : (ℓ : L) → OKB (B₀ ℓ)
okB₀ ℓ i u = ⊴r

hβ₂ : M 2 (Ωᴺ 2) (proj₁ (Ωt two))
hβ₂ = Mβ 1
```

```agda
sib-at : ∀ {t} n → SP t (fn (sh n) , pth (sbk n)) → M 2 t (proj₁ (gˢ (nat n)))
sib-at {t} n s =
  m⊴N 2 (subst (SP t) (sym (eqˢ n)) s (proj₂ (Ok-tw 1) (nat 2 + nat n)) (rb-no _) (B₀ _) (Ωt two) (okB₀ _) hβ₂) (+⊴ _ _)

tgt-at : ∀ {t} n → SP t (fn (sh n) , pt (ptk n)) → M 2 t (proj₁ (gᵗ (nat n)))
tgt-at {t} n s =
  m⊴N 2 (subst (SP t) (sym (eqᵗ n)) s (Ok⊕ two (↑ zero (nat n)) o2 (OkO↑ two zero tt (z≤ two) (nat n))) (rb-no _) (B₀ _)
           (Ωt two) (okB₀ _) hβ₂) (+⊴ _ _)

sib-crit : ∀ k → CritAt gˢ (suc (suc (suc k)))
sib-crit k = sib-at (suc (suc (suc k))) (critC k)

tgt-crit : ∀ k → CritAt gᵗ (suc (suc (suc k)))
tgt-crit k = tgt-at (suc (suc (suc k))) (critU k)

sib-shift : ∀ k → M 2 (ψᴺ 2 (Ωᴺ (suc (sh k)))) (proj₁ (gˢ (nat (suc k))))
sib-shift k = sib-at (suc k) (shiftC k)

tgt-shift : ∀ k → M 2 (ψᴺ 2 (Ωᴺ (suc (sh k)))) (proj₁ (gᵗ (nat (suc k))))
tgt-shift k = tgt-at (suc k) (shiftU k)
```

孩子取更大的 `nat (d + n)` 时判据仍成立 (参照不变, 层号再上行 d 层): `M⁰ (natT n) c` 的松弛情形里 c 是自然数的那些.

```agda
add : ℕ → ℕ → ℕ
add zero    n = n
add (suc d) n = suc (add d n)

upC : ∀ {t} n → SP t (fn (sh n) , pth (sbk n)) → SP t (fn (sh (suc n)) , pth (sbk (suc n)))
upC n s o r = liftC o r (pth (sbk n)) (s (proj₂ o tt) (proj₂ r tt))

upU : ∀ {t} n → SP t (fn (sh n) , pt (ptk n)) → SP t (fn (sh (suc n)) , pt (ptk (suc n)))
upU n s o r = liftU o r (pt (ptk n)) (s (proj₂ o tt) (proj₂ r tt))

upsC : ∀ {t} n d → SP t (fn (sh n) , pth (sbk n)) → SP t (fn (sh (add d n)) , pth (sbk (add d n)))
upsC n zero    s = s
upsC n (suc d) s = upC (add d n) (upsC n d s)

upsU : ∀ {t} n d → SP t (fn (sh n) , pt (ptk n)) → SP t (fn (sh (add d n)) , pt (ptk (add d n)))
upsU n zero    s = s
upsU n (suc d) s = upU (add d n) (upsU n d s)

sib-crit≥ : ∀ k d → M 2 (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (proj₁ (gˢ (nat (add d (suc (suc (suc k)))))))
sib-crit≥ k d = sib-at (add d (suc (suc (suc k)))) (upsC (suc (suc (suc k))) d (critC k))

tgt-crit≥ : ∀ k d → M 2 (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (proj₁ (gᵗ (nat (add d (suc (suc (suc k)))))))
tgt-crit≥ k d = tgt-at (add d (suc (suc (suc k)))) (upsU (suc (suc (suc k))) d (critU k))
```

## 两种写法的差别 (形状, `refl`)

目标是孩子 3 里的第 2 层, 嵌入在孩子 1: 兄弟孩子在孩子 3 + 1 的层 (`fn 4`) 上折, 目标层 ⊕ c 在 `fn 3` 上折. 兄弟孩子的底读左项 x (`YiRBSib.row-tw`), 目标层 ⊕ c 的底是默认底.

```agda
lvlˢ : h₁ (nat 3 + nat 1) ≡ fn 4
lvlˢ = refl

lvlᵗ : two ⊕ ↑ zero (nat 1) ≡ fn 3
lvlᵗ = refl

sib-3-shape : (B : Base (tw 1)) (β : Tr⁺ two) (x : Tr (tw 1))
  → proj₁ (ψ (tw 1) (Ok-tw 1) (rb-tw 1) B two (inc (nat 3) (inc tt self)) β
             (up x (nat 1) (proj₁ (Ωt (h₁ (nat 1)))) (proj₂ (Ωt (h₁ (nat 1))))))
  ≡ proj₁ (ψ (fn 4) (proj₂ (Ok-tw 1) (nat 4)) (rb-no _)
             (λ i u → ψ (tw 1) (Ok-tw 1) (rb-tw 1) B i (inc (nat 4) u) (B i (inc (nat 4) u)) x) two
             (inc tt (inc tt self))
             (ψ (tw 1) (Ok-tw 1) (rb-tw 1) B two (inc (nat 3) (inc tt self)) β x) (proj₁ (Ωt (fn 4))))
    + ι two (proj₁ (ψ₀ʳ (h₁ (nat 1)) (proj₂ (Ok-tw 1) (nat 1)) (rb-no _) (proj₁ (Ωt (h₁ (nat 1))))))
sib-3-shape B β x = refl
```
