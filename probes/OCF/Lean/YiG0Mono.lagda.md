# 验收: 孩子层上 Ω 树的折叠 `G` 沿第一位置序跨层单调 (V128 的松弛情形)

> 验收文件, 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 对一切第 0 层的树. `G-mono : zero ⊢ x ◃ y → read (G x) ≼ read (G y)` (F2 的 `YiLSTw1.G`), `G-mono⊴`.
> 做法: F2 的第 0 层的树搬到精简块 (`toR`, 与原树相关), 两边的 `G` 相关 (`G-R`); 在精简块上用值关系的折叠保持 (`YiVRRead.fold-≼`, `kid-Ω`) 比较孩子层 c 与 c+1, 以及 ℕ 极限层号的第 n 行与孩子 n (`rowᴿ`), 再搬回.
> 不给出什么: 按值的单调 (`YiVRRead.GMono`, x 与 y 只有读回的 `≼`) 没有证; 这里的 x, y 要有字面的 `◃`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiG0Mono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBROps using (Ωt-R)
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBRTw using (tw-E; ψ₀-R)
open import OCF.Lean.YiBRValue using (readRW; rel≅)
open import OCF.Lean.YiVRRel using (Le; refl₀; Ωt≼; NoΩ; NoΩ≤; NoΩ↑)
open import OCF.Lean.YiVRFold using (_⊴_; Dflt-noΩ; infl; cb)
open import OCF.Lean.YiVRRead using (fold-≼; le→≼; kid-Ω; h₁; o₁)
open import OCF.Lean.YiLSRead using (read)
import OCF.Lean.YiLSRead as S
import OCF.Lean.YiLSTw1 as T1
import OCF.Align.Level as O
import OCF.Align.Value as V
open V using (_≼_)
```

## F2 的第 0 层的树搬到精简块

第 0 层只有零, 后继, ℕ 极限; 步进推导一起搬 (`toRm`). 搬过去的树与原树相关 (`toR-R`), 推导也相关.

```agda
mutual
  toR : F.Tr F.zero → Tr zero
  toR F.zero          = zero
  toR (F.suc x)       = suc (toR x)
  toR (F.lim f a)     = lim (λ n → toR (f n)) (λ n → toRm (a n))
  toR (F.Ω () _)
  toR (F.up _ () _ _)

  toRm : {x y : F.Tr F.zero} → F.zero F.⊢ x ◃ y → zero ⊢ toR x ◃ toR y
  toRm F.◃s             = ◃s
  toRm (F.◃l n)         = ◃l n
  toRm (F.◃w {p = ()})
  toRm (F.◃u _ () _ _)
  toRm (F.◃c _ () _)
  toRm (F.◃t d e)       = ◃t (toRm d) (toRm e)

mutual
  toR-R : (x : F.Tr F.zero) → RelT zero F.zero (toR x) x
  toR-R F.zero          = iz
  toR-R (F.suc x)       = is (toR-R x)
  toR-R (F.lim f a)     = il ((λ n → toR-R (f n)) , (λ n → toRm-R (a n)))
  toR-R (F.Ω () _)
  toR-R (F.up _ () _ _)

  toRm-R : {x y : F.Tr F.zero} (d : F.zero F.⊢ x ◃ y) → RelD zero F.zero (toRm d) d
  toRm-R F.◃s             = ds
  toRm-R (F.◃l n)         = dl
  toRm-R (F.◃w {p = ()})
  toRm-R (F.◃u _ () _ _)
  toRm-R (F.◃c _ () _)
  toRm-R (F.◃t d e)       = dt (toRm-R d , toRm-R e)
```

## 两边的 `G` 相关

精简块上孩子 c 的 Ω 树的折叠 `Gᴿ c`; 塔第 1 项的证据关系 (`YiBRTw.tw-E 1`) 在相关的孩子上给出孩子层的证据关系.

```agda
Gᴿ : Tr zero → Tr zero
Gᴿ c = proj₁ (ψ₀ (h₁ c) (proj₂ o₁ c) (proj₁ (Ωt (h₁ c))))

getΩ : ∀ {k h k′ h′ o ε ρ} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ
     → (c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelE (h c) (h′ c′) (proj₂ o c) (proj₂ (proj₂ ε c′)) (proj₂ ρ c′)
getΩ (eΩ _ _ rc) = rc

kidE : (c′ : F.Tr F.zero) → RelE (h₁ (toR c′)) (T1.h₁ c′) (proj₂ o₁ (toR c′)) (T1.εh c′) (T1.ρh c′)
kidE c′ = getΩ (tw-E 1) (toR c′) c′ (toR-R c′)

G-R : (c′ : F.Tr F.zero) → RelT zero F.zero (Gᴿ (toR c′)) (T1.G c′)
G-R c′ = ψ₀-R (kidE c′) (Ωt-R (E→L (kidE c′)))

G≼ᴿ : (c′ : F.Tr F.zero) → read (T1.G c′) ≼ readRW (Gᴿ (toR c′))
G≼ᴿ c′ = V.≅→≼ (O.≅-sym (rel≅ (G-R c′)))

G≽ᴿ : (c′ : F.Tr F.zero) → readRW (Gᴿ (toR c′)) ≼ read (T1.G c′)
G≽ᴿ c′ = V.≅→≼ (rel≅ (G-R c′))
```

## 精简块上: ℕ 极限层号的一行不低于孩子自己的折叠

层号 `nd sL g` 上嵌入 `up X n (Ωt (g n))` 的折叠是孩子 n 上的折叠, 底换成由 X 造的孩子底, 起点换成 X 的折叠. 默认底在每个分量上不高于它 (`infl`), 所以值不降 (`fold-≼`). 量化域: 孩子层号不含 Ω 形状 (`NoΩ`), 读自第 0 层的树的层号都满足.

```agda
rowᴿ : (g : ℕ → L) (o : Ok (nd sL g)) (n : ℕ) → NoΩ (g n) → (X : Tr (nd sL g))
     → readRW (proj₁ (ψ₀ (g n) (proj₂ o n) (proj₁ (Ωt (g n)))))
     ≼ readRW (proj₁ (ψ₀ (nd sL g) o (up X n (proj₁ (Ωt (g n))) (proj₂ (Ωt (g n))))))
rowᴿ g o n nΩ X =
  fold-≼ (g n) (proj₂ o n) (Dflt-noΩ (g n) nΩ) (B₀ (g n)) (cb sL g o (B₀ (nd sL g)) n X)
    (λ j w _ → infl (nd sL g) o (B₀ (nd sL g)) j (inc n w) (Ωt j) X (Ωt≼ j (NoΩ≤ w nΩ)))
    (z≤ (g n)) (Ωt zero) (ψ₀ (nd sL g) o X)
    (le→≼ (infl (nd sL g) o (B₀ (nd sL g)) zero (z≤ (nd sL g)) (Ωt zero) X (refl₀ (proj₁ (Ωt zero)))))
    (Ωt≼ (g n) nΩ)
```

ℕ 极限层号的 Ω 树是嵌入的部分和; 第 n 个部分和是 `up (前一个部分和) n (Ωt (g n))` (n = 0 时左边是零).

```agda
Fᴿ : (g : ℕ → L) → ℕ → Tr (nd sL g)
Fᴿ g n = proj₁ (upz n (Ωt (g n)))

Xᴿ : (g : ℕ → L) → ℕ → Tr (nd sL g)
Xᴿ g zero    = zero
Xᴿ g (suc n) = cum (Fᴿ g) n

cum-form : (g : ℕ → L) (n : ℕ) → cum (Fᴿ g) n ≡ up (Xᴿ g n) n (proj₁ (Ωt (g n))) (proj₂ (Ωt (g n)))
cum-form g zero    = refl
cum-form g (suc n) = refl

limᴿ : (f : ℕ → Tr zero) (a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)) (n : ℕ)
     → readRW (Gᴿ (f n)) ≼ readRW (Gᴿ (lim f a))
limᴿ f a n = V.≼l n (go n (cum-form (λ m → h₁ (f m)) n))
  where
  go : (n : ℕ) {Y : Tr (h₁ (lim f a))} → Y ≡ up (Xᴿ (λ m → h₁ (f m)) n) n (proj₁ (Ωt (h₁ (f n)))) (proj₂ (Ωt (h₁ (f n))))
     → readRW (Gᴿ (f n)) ≼ readRW (proj₁ (ψ₀ (h₁ (lim f a)) (proj₂ o₁ (lim f a)) Y))
  go n refl = rowᴿ (λ m → h₁ (f m)) (proj₂ o₁ (lim f a)) n (NoΩ↑ (f n)) (Xᴿ (λ m → h₁ (f m)) n)
```

## 沿第一位置序的单调 (F2)

```agda
G-mono : {x y : F.Tr F.zero} → F.zero F.⊢ x ◃ y → read (T1.G x) ≼ read (T1.G y)
G-mono (F.◃s {x = x}) =
  V.≼-trans (G≼ᴿ x) (V.≼-trans (kid-Ω (toR x)) (G≽ᴿ (F.suc x)))
G-mono (F.◃l {f = f} {a = a} n) =
  V.≼-trans (G≼ᴿ (f n)) (V.≼-trans (limᴿ (λ m → toR (f m)) (λ m → toRm (a m)) n) (G≽ᴿ (F.lim f a)))
G-mono (F.◃w {p = ()})
G-mono (F.◃u _ () _ _)
G-mono (F.◃c _ () _)
G-mono (F.◃t d e) = V.≼-trans (G-mono d) (G-mono e)

G-mono⊴ : {x y : F.Tr F.zero} → F.zero S.⊢ x ⊴ y → read (T1.G x) ≼ read (T1.G y)
G-mono⊴ {x} S.⊴r = V.≼-refl (read (T1.G x))
G-mono⊴ (S.⊴◃ d) = G-mono d
```
