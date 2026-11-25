# 最小比较表: 值

> 验收文件 (读记号), 不进成品; 树、折叠、表一行不改. 编译定理, 无前提. (a) `twᶻ 1` 与 F2 的 `twᶜ 1` 逐层相关 (`twᶻ1-R`), 与原主线第 1 项同值 (`same-tw1ᶻ`); 两个闭项不是逐字相同 (见回报). (b) 塔每一项不低于 BTBO (`btbo-twᶻ`); 塔第 2 项的结点、链元 1 与那一行的形状 (`tw2-formᶻ`, `ch1-same`, `row-zz`). (c) 终点第 1 支与 F2 上手造的底 `Bᶻᶠ` 的 `Fn 1 Bᶻᶠ` 相关 (`br1-Rᶻ`), 得 `btbo-EBOᶻ`. (d) `k1ᶻ : Kᶻ 1`; K(2) 归约到 `kl 1` 的逐行 (`K2-redᶻ`), 第 0 行成立 (`row0₂ᶻ`).
> 底的分量: 终点第 1 支里孩子 c′ 的底经 `inc c′ v` 的分量, 对一切 c′ 是 "1 沿 `z≤` 嵌进孩子 c′ 的层, 再在那一层上朝 j 折" (`B1-shape`, 按 c′ 的构造子 `refl`).
> 不给出什么: 新塔第 2 项与原塔第 2 项的值的关系; 终点经第 2 支的各条下界; K(2) 第 1 行起. 这三处都没有编译的否定. 搬运方法的边界有编译定理: 塔第 1 项的顶层上, 那一行的新值与 F2 回退行的值不满足 `RelT` (`norel`), 所以 `YiMTRel` 的关系不能原样延伸到 Ω 形状的层号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMTValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
import OCF.Lean.YiRWFold as RW
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiMTTab
open import OCF.Lean.YiMTRel using (A; S; topΩ; U0; u0)
open import OCF.Lean.YiMTKeel using (tw≼ᶻ; F₀ᶻ; step¹ᶻ; chΩᶻ; rowsΩᶻ; keelᶻ)
open import OCF.Lean.YiNRHit using (NoΩ; noΩ↑)
import OCF.Lean.YiSMValue as SM
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R; emb-R)
open import OCF.Lean.YiBRFold using (B₀-R; W→L)
open import OCF.Lean.YiBRTw using (tw-L; tw-E; ↑-L)
open import OCF.Lean.YiBRValue using (readRW; rel≅; up≼; same-tw)
open import OCF.Lean.YiLSRead using (_⊢_⊴_; ⊴r; ⊴◃; ⊴-◃)
open import OCF.Lean.YiLSFold using (OKB; ψs-⊵)
import OCF.Lean.YiLSTw1 as T1
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiEBShape using (dB; Fn; ok-dB)
open import OCF.Lean.YiEBBtbo using (Start; start-dB1; module Btbo)
open import OCF.Lean.YiKSDesc using (kl; okl)
open import OCF.Lean.YiKSRead using (k1; fs-sup)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
import OCF.Align.EboLeanDef as E
open E using (HC; ΩTower; EBOψ)
open import OCF.Align.EboLeanTree using (hc-tower)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; ≼-refl; ≼-trans; ≅→≼)
open import OCF.Align.YiBtValBT using (module D)
```

## (a) 塔第 1 项

```agda
h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

twᶻ1-R : RelT zero F.zero (twᶻ 1) (F.twᶜ 1)
twᶻ1-R = proj₁ (topΩ (tw-E 1) noΩ↑ (B₀ (tw 1)) (F.B₀ (F.tw 1)) (B₀-R (tw-L 1)) (Ωt zero) (Ωt-R lz) (Ωn-R lz)
                  (λ z → u0 z _ _) (Ωt-R (tw-L 1)))

same-tw1ᶻ : readRW (twᶻ 1) L.≅ readRW (RW.twᶜ 1)
same-tw1ᶻ = L.≅-trans (rel≅ twᶻ1-R) (L.≅-sym (same-tw 1))

btbo-tw1ᶻ : D.BTBOᴵ ≼ readRW (twᶻ 1)
btbo-tw1ᶻ = up≼ twᶻ1-R btbo-tw1
```

## (b) 塔第 2 项: 下界与形状

```agda
btbo-twᶻ : (n : ℕ) → D.BTBOᴵ ≼ readRW (twᶻ (suc n))
btbo-twᶻ zero    = btbo-tw1ᶻ
btbo-twᶻ (suc n) = ≼-trans (btbo-twᶻ n) (tw≼ᶻ (suc n))

h₂ : Tr (tw 1) → L
h₂ c = tw 1 ⊕ ↑ (tw 1) c

g₂ : Tr (tw 1) → Tr (tw 2)
g₂ z = proj₁ (upz {s = sΩ (tw 1)} {h = h₂} z (Ωt (h₂ z)))

chᶻ chᶜ : ℕ → Tr (tw 1)
chᶻ = iter (λ z → proj₁ (ψ (tw 2) (Ok-tw 2) (rbᶻ (tw 2)) (B₀ (tw 2)) (tw 1) (ink self) (Ωt (tw 1)) (g₂ z))) zero
chᶜ = iter (λ z → proj₁ (RW.ψ (tw 2) (Ok-tw 2) (B₀ (tw 2)) (tw 1) (ink self) (Ωt (tw 1)) (g₂ z))) zero

tw2-formᶻ : twᶻ 2 ≡ proj₁ (limc⁺ (λ n → ψ (tw 2) (Ok-tw 2) (rbᶻ (tw 2)) (B₀ (tw 2)) zero (z≤ (tw 2)) (Ωt zero) (g₂ (chᶻ n))))
tw2-formᶻ = refl

tw2-formᶜ : RW.twᶜ 2 ≡ proj₁ (limc⁺ (λ n → RW.ψ (tw 2) (Ok-tw 2) (B₀ (tw 2)) zero (z≤ (tw 2)) (Ωt zero) (g₂ (chᶜ n))))
tw2-formᶜ = refl

ch1-same : chᶻ 1 ≡ chᶜ 1
ch1-same = refl
```

那一行在 c′ = c = `zero` 处 (对一切层号, 目标, 底): 新的是孩子 0 的层上以左项的折叠为底朝 j 的折叠; 原来是左项的折叠加上孩子树折到第 0 层再嵌回.

```agda
row-zz : ∀ k h (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j (v : j ≤ h zero) β x y e
  → ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B j (inc zero v) β (up x zero y e)
  ≡ ψ (h zero) (proj₂ o zero) (rbᶻ (h zero)) (λ i u → ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B i (inc zero u) (B i (inc zero u)) x) j v
      (ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B j (inc zero v) β x) y
row-zz k h o B j v β x y e = refl

row-zzᶜ : ∀ k h (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j (v : j ≤ h zero) β x y e
  → RW.ψ (nd (sΩ k) h) o B j (inc zero v) β (up x zero y e)
  ≡ RW.ψ (nd (sΩ k) h) o B j (inc zero v) β x ⊞ RW.ψ₀ (h zero) (proj₂ o zero) y
row-zzᶜ k h o B j v β x y e = refl
```

## (c) 终点: 第 1 支

```agda
Fᴧ : ℕ → Tr Λ
Fᴧ n = proj₁ (upz {s = sL} {h = tw} n (Ωt (tw n)))

brᶻ : ℕ → Tr zero
brᶻ n = proj₁ (ψ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) zero (z≤ Λ) (Ωt zero) (cum Fᴧ n))

brᶻ≼ : (n : ℕ) → readRW (brᶻ n) ≼ readRW EBOᶻ
brᶻ≼ n = ≼l n (≼-refl _)

B1ᶻ : Base (tw 1)
B1ᶻ j u = ψ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) j (inc 1 u) (Ωt j) (cum Fᴧ 0)

β1ᶻ : Tr⁺ zero
β1ᶻ = ψ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) zero (z≤ Λ) (Ωt zero) (cum Fᴧ 0)

br1-formᶻ : brᶻ 1 ≡ proj₁ (ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B1ᶻ zero (z≤ (tw 1)) β1ᶻ (proj₁ (Ωt (tw 1))))
br1-formᶻ = refl

one⁺ : Tr⁺ zero
one⁺ = suc zero , ◃s

Bc : (c′ : Tr zero) (j : L) → j ≤ h₁ c′ → Tr⁺ j
Bc c′ j v = ψ (h₁ c′) (proj₂ (Ok-tw 1) c′) (rbᶻ (h₁ c′)) (λ i u → Ωt i) j v (Ωt j)
              (proj₁ (emb (h₁ c′) (proj₂ (Ok-tw 1) c′) (z≤ (h₁ c′)) one⁺))

B1-shape : (c′ : Tr zero) (j : L) (v : j ≤ h₁ c′) → B1ᶻ j (inc c′ v) ≡ Bc c′ j v
B1-shape zero      j v = refl
B1-shape (suc c′)  j v = refl
B1-shape (lim f a) j v = refl
```

F2 上的对应底: 经 `inb c v` 的分量照 `Bc` 手写, 其余分量与 `b⊥` 取第 1 支原来的底 `dB 1`.

```agda
one′ : F.Tr F.zero
one′ = F.suc F.zero

lz′ : (c : F.Tr F.zero) → F._≤_ F.zero (T1.h₁ c)
lz′ c = F.lift F.zero (F.↑ F.zero c)

bsᶻ : (j : F.L) → F._≤_ j (F.tw 1) → F.Tr j
bsᶻ j (F.inb c v) =
  F.ψs (T1.h₁ c) (T1.εh c) (T1.ρh c) (F.B₀ (T1.h₁ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.emb (T1.h₁ c) (T1.εh c) (lz′ c) one′ F.◃s)
bsᶻ j F.self     = F.bs (dB 1) j F.self
bsᶻ j (F.ink v)  = F.bs (dB 1) j (F.ink v)
bsᶻ j (F.inu vs) = F.bs (dB 1) j (F.inu vs)

nsᶻ : (j : F.L) (w : F._≤_ j (F.tw 1)) → F._⊢_◃_ j F.zero (bsᶻ j w)
nsᶻ j (F.inb c v) =
  F.nzs (T1.h₁ c) (T1.εh c) (T1.ρh c) (F.B₀ (T1.h₁ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.emb (T1.h₁ c) (T1.εh c) (lz′ c) one′ F.◃s)
nsᶻ j F.self     = F.ns (dB 1) j F.self
nsᶻ j (F.ink v)  = F.ns (dB 1) j (F.ink v)
nsᶻ j (F.inu vs) = F.ns (dB 1) j (F.inu vs)

Bᶻᶠ : F.Base (F.tw 1)
Bᶻᶠ = F.base (F.b⊥ (dB 1)) (F.n⊥ (dB 1)) bsᶻ nsᶻ

zW : ∀ {b b′} → RelL b b′ → RelW (z≤ (zero ⊕ b)) (F.lift F.zero b′)
zW lz         = wself
zW (lS r)     = winuS (zW r)
zW (lL r)     = winuL (λ n → zW (r n))
zW (lΩ rk rh) = winuΩ (λ c c′ rc → zW (rh c c′ rc))

rBc : ∀ {c c′} (rcc : RelT zero F.zero c c′) {j j′} {v : j ≤ h₁ c} {v′ : F._≤_ j′ (T1.h₁ c′)} → RelW v v′
    → RelT j j′ (proj₁ (Bc c j v)) (bsᶻ j′ (F.inb c′ v′)) × RelD j j′ (proj₂ (Bc c j v)) (nsᶻ j′ (F.inb c′ v′))
rBc {c} {c′} rcc {j} {j′} rv =
  let rec = SM.chE (tw-E 1) c c′ rcc
      rlj = W→L (E→L rec) rv
      em  = emb-R rec (zW (↑-L lz rcc)) one⁺ (is iz) ds
  in S rec (noΩ↑ c) (B₀ _) (F.B₀ _) (B₀-R (E→L rec)) rv (Ωt j) (Ωt-R rlj) (Ωn-R rlj) (proj₁ em)

rB1ᶻ : RelBase (tw 1) (F.tw 1) B1ᶻ Bᶻᶠ
rB1ᶻ j j′ w w′ rw@wself      = SM.cΛ j j′ w w′ rw
rB1ᶻ j j′ w w′ rw@(winuΩ _)  = SM.cΛ j j′ w w′ rw
rB1ᶻ j j′ w w′ rw@(wink _)   = SM.cΛ j j′ w w′ rw
rB1ᶻ j j′ w w′ (wincΩ {c = c} {c′ = c′} {v = v} {v′ = v′} rcc rv) =
  subst (λ Z → RelT j j′ (proj₁ Z) (bsᶻ j′ (F.inb c′ v′)) × RelD j j′ (proj₂ Z) (nsᶻ j′ (F.inb c′ v′)))
        (sym (B1-shape c j v)) (rBc rcc rv)

br1-Rᶻ : RelT zero F.zero (brᶻ 1) (Fn 1 Bᶻᶠ)
br1-Rᶻ = proj₁ (topΩ (tw-E 1) noΩ↑ B1ᶻ Bᶻᶠ rB1ᶻ β1ᶻ (proj₁ SM.β1-R) (proj₂ SM.β1-R) (λ z → u0 z _ _) (Ωt-R (tw-L 1)))

okᶻ : OKB (F.tw 1) Bᶻᶠ
okᶻ = proj₁ (ok-dB 1) , okbs
  where
  okbs : (j : F.L) (w : F._≤_ j (F.tw 1)) → j ⊢ F.Ωt j ⊴ bsᶻ j w
  okbs j (F.inb c v) = ψs-⊵ (T1.h₁ c) (T1.εh c) (T1.ρh c) (F.B₀ (T1.h₁ c)) j v (F.Ωt j) (F.Ωt-nz j) _
  okbs j F.self     = proj₂ (ok-dB 1) j F.self
  okbs j (F.ink v)  = proj₂ (ok-dB 1) j (F.ink v)
  okbs j (F.inu vs) = proj₂ (ok-dB 1) j (F.inu vs)

stᶻ : Start Bᶻᶠ
stᶻ = start-dB1

btbo-br1ᶻ : D.BTBOᴵ ≼ readRW (brᶻ 1)
btbo-br1ᶻ = up≼ br1-Rᶻ (Btbo.btbo-B Bᶻᶠ okᶻ stᶻ)

btbo-EBOᶻ : D.BTBOᴵ ≼ readRW EBOᶻ
btbo-EBOᶻ = ≼-trans btbo-br1ᶻ (brᶻ≼ 1)
```

## (d) 朝 K(2)

`Kᶻ n`: ψ₀(Ω_{ΩTower n}) 的参照不高于 `twᶻ n` (陈述照 `YiKSRead.K`, 闭项换成新的).

```agda
Kᶻ : ℕ → Set
Kᶻ n = (h : HC (E.ψ [] (E.Ωt (ΩTower n)) ∷ [])) → Rt h ≼ readRW (twᶻ n)

_ : Kᶻ 2 ≡ ((h : HC (EBOψ 3)) → Rt h ≼ readRW (twᶻ 2))
_ = refl

k1ᶻ : Kᶻ 1
k1ᶻ h = ≼-trans (k1 h) (≅→≼ (L.≅-sym same-tw1ᶻ))

hsᶻ : Tr zero → L
hsᶻ c = tw 1 ⊕ (zero ⊕ ↑ (zero ⊕ ↑ zero c) (proj₁ (Ωt (zero ⊕ ↑ zero c))))

z₂ᶻ : ℕ → Tr zero
z₂ᶻ = chΩᶻ zero hsᶻ (okl 1)

Row₂ᶻ : ℕ → ℕ → Set
Row₂ᶻ n m = Rt (hω-inv (hc-tower 3) refl n) ≼ readRW (F₀ᶻ (hsᶻ (z₂ᶻ m)) (proj₂ (okl 1) (z₂ᶻ m)))

rows₂ᶻ : ∀ m → readRW (F₀ᶻ (hsᶻ (z₂ᶻ m)) (proj₂ (okl 1) (z₂ᶻ m))) ≼ readRW (twᶻ 2)
rows₂ᶻ m = ≼-trans (rowsΩᶻ zero hsᶻ (okl 1) m) (keelᶻ 1)

K2-redᶻ : (∀ n → Σ ℕ λ m → Row₂ᶻ n m) → Kᶻ 2
K2-redᶻ prem h = ≼-trans (tree-≼ refl h (hc-tower 3))
  (fs-sup (hc-tower 3) refl (λ n → ≼-trans (proj₂ (prem n)) (rows₂ᶻ (proj₁ (prem n)))))

row0₂ᶻ : Row₂ᶻ 0 0
row0₂ᶻ = ≼-trans (k1ᶻ (hω-inv (hc-tower 3) refl 0)) (step¹ᶻ sS (λ _ → tw 1) (proj₂ (okl 1) zero))

btbo-row₂ᶻ : Rt (hω-inv (hc-tower 3) refl 0) ≼ readRW (twᶻ 2)
btbo-row₂ᶻ = ≼-trans row0₂ᶻ (rows₂ᶻ 0)
```

## 关系在 Ω 形状层号上的边界

塔第 1 项的顶层, 目标第 0 层经孩子 0, 树是 "1 嵌在孩子 0": 输入相关 (`rx`), 新的一行给 `next⁺ 1` (第 0 项是 1), F2 的回退行给 1 + ω (第 0 项是 2), 两个输出不相关.

```agda
x₁ : Tr (tw 1)
x₁ = up zero zero (suc zero) ◃s

x₁′ : F.Tr (F.tw 1)
x₁′ = F.up F.zero F.zero (F.suc F.zero) F.◃s

rx : RelT (tw 1) (F.tw 1) x₁ x₁′
rx = iu (iz , (iz , is iz , ds))

norel : RelT zero F.zero
          (proj₁ (ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) zero (inc zero self) (Ωt zero) x₁))
          (F.ψs (F.tw 1) (F.Ev-tw 1) (F.Rt-tw 1) (F.B₀ (F.tw 1)) F.zero (F.inb F.zero F.self) (F.Ωt F.zero) (F.Ωt-nz F.zero) x₁′)
      → ⊥
norel (il (rf , _)) with rf 0
... | is ()
```
