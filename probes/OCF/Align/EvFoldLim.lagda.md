# 事件世界上的真折叠 (七): 塔的 ℕ-极限, 拷贝回到极限界上

> 不含记号. 入口 [EvFold](EvFold.lagda.md). 接手清单的 "塔的 ℕ-极限" ([AdmEvFeed](AdmEvFeed.lagda.md) `Tower`, 读回作参数). `AdmEv` 的判断: 极限处要沿 `hlim n hself` 与 `stepsᴮ` 的复合改贴, 难点是 `fac` 只对 `⊞-⊲` 形的路径, 一般路径要 ⊞ 结合律. 本篇说: **在改贴的合法性之前还有一道墙**, 与 `fac` 的形状无关.
>
> 第 $n$ 站的种类 $(c,p)$, $p : c\lhd b_n$; 到了第 $n+1$ 站它是 $(c, p ⨾ \mathrm{wk}_n)$. 合到极限界 $L=\mathrm{hl}\,b$ 之下, 每一站要一条证据 $Z_n : b_n \lhd L$, 种类 $(c,p)\mapsto(c, p⨾Z_n)$. 相邻两站的同一个旧种类要落到同一个极限种类, 否则 $\rho_n(t_n)$ 与 $\rho_{n+1}(t_{n+1})$ 的种类不同, 前者不是后者的第一位置 (ℕ-极限的合法要的正是这个). 对 $p=\mathrm{hself}$, 这就是 **相干**: $Z_n = \mathrm{wk}_n ⨾ Z_{n+1}$.
>
> 1. **`no-coh-ev` (否定, 对 `AdmEvFeed.Inst` 的塔).** 没有相干的证据族 $Z$. 证明: $Z_n$ 都走 $L$ 的同一支 (`idx` 沿相干不变), 设为第 $m$ 支; 那么 $Z_{m+1}$ 给出 $b_{m+1}\lhd b_m$, 与 `inst-new` 矛盾. **只否定**: 以 `Inst` 塔的外层界的 ℕ-极限为界, 带证据的种类沿某族证据改贴, 且相邻站相干. 不否定别的极限界, 不否定种类不带证据的极限.
> 2. **`no-lim-n` (否定, 具体项).** `AdmEv` 建议的改贴 "第 $n$ 站沿 `hlim n hself`": 第 1, 2 站的高度改贴后, 前者不是后者在空事件表里的第一位置. 所以 $\mathrm{hl}(n\mapsto\rho_n t_n)$ 不合法.
>
> 读法 (判断): 这是拷贝墙 (`CohWNeg.no-cross` 一族) 在塔的极限上重现: 外层界固定时证据把拷贝分开 (`AdmEv`), 外层界的 ℕ-极限让同一个坐标在不同的支下各有一份证据, 而塔要求它们是同一份. "`fac` 推广 + 相干前提" 与 "换不要结合律的极限界" 这两条都只处理改贴的合法性, 不处理这一条; 后者若极限界仍是外层界序列的 ℕ-极限, 同一证明照样适用 (判断: 证明只用了 "相邻站的证据相干" 与 "第 $m+1$ 站的界不在第 $m$ 站之下"). 第三条路 (判断): 极限站不改贴旧种类, 而把各站的种类作为不同的种类保留 (极限世界的种类取 $\Sigma_n K_n$), 那时 $\mathrm{hl}(n\mapsto\iota_n t_n)$ 的相邻项种类也不同, 同样不合法; 要合法, 极限的高度不能是各站高度的 ℕ-极限. 没有写.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvFoldLim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; [])
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmEvFeed using (module Inst; module Tower)
open import OCF.Align.AdmWCoh using (wz; lg-wz)
```

## §1 `Inst` 塔的外层界

```agda
open Inst using (inst-new)
module TI = Tower azero tt wz lg-wz
module RI = TI.Run Inst.rd₁ Inst.s₀

bI : ℕ → HB S₀
bI n = TI.sb (RI.tower n)

bI-suc : ∀ n → bI (suc n) ≡ hs (bI n)
bI-suc n = refl

wkI : ∀ n {w} → bI n ⊲[ w ] bI (suc n)
wkI n = RI.b-step n

LI : HB S₀
LI = hl bI

-- 外层界都不是 ℕ-极限
NotL : HB S₀ → Set
NotL (hl _) = ⊥
NotL _ = ⊤

notL : ∀ n → NotL (bI n)
notL zero = tt
notL (suc n) = tt
```

## §2 证据走 $L$ 的哪一支

```agda
idx : ∀ {x} {f : ℕ → HB S₀} {w} → x ⊲[ w ] hl f → ℕ
idx hself = 0
idx (hlim m _) = m

body : ∀ {x} {f : ℕ → HB S₀} {w} (Z : x ⊲[ w ] hl f) → NotL x → x ⊲[ w ] f (idx Z)
body hself ()
body (hlim m Q) _ = Q

idx-tr : ∀ {y x} {f : ℕ → HB S₀} {w} (p : y ⊲[ w ] x) (Z : x ⊲[ w ] hl f) → NotL x → idx (⊲ᴮ-tr p Z) ≡ idx Z
idx-tr p hself ()
idx-tr p (hlim m Q) _ = refl
```

## §3 没有相干的证据族

```agda
Coh : Set
Coh = Σ (∀ n → bI n ⊲[ azero ] LI) (λ Z → ∀ n → Z n ≡ ⊲ᴮ-tr (wkI n) (Z (suc n)))

idx-const : (C : Coh) → ∀ n → idx (proj₁ C (suc n)) ≡ idx (proj₁ C n)
idx-const (Z , eq) n = trans (sym (idx-tr (wkI n) (Z (suc n)) (notL (suc n)))) (cong idx (sym (eq n)))

idx-0 : (C : Coh) → ∀ n → idx (proj₁ C n) ≡ idx (proj₁ C 0)
idx-0 C zero = refl
idx-0 C (suc n) = trans (idx-const C n) (idx-0 C n)

no-coh-ev : ¬ Coh
no-coh-ev C = inst-new m (subst (λ k → bI (suc m) ⊲[ azero ] bI k) (idx-0 C (suc m)) (body (proj₁ C (suc m)) (notL (suc m))))
  where
  m : ℕ
  m = idx (proj₁ C 0)
```

## §4 具体项: 第 $n$ 站沿第 $n$ 支改贴

`ρX X`: 种类 $(c,p)\mapsto(c, p⨾X)$, 不管合法性 (否定只要两个高度不是第一位置).

```agda
K∞ : KS
K∞ = TI.Kat LI ((λ n → wkI n) , (λ n → TI.slb (RI.tower n)))

module _ {b : HB S₀} {lb : LgB b} (X : b ⊲[ azero ] LI) where
  ρX : HB (TI.Kat b lb) → HB K∞
  ρX hz = hz
  ρX (hs t) = hs (ρX t)
  ρX (hl f) = hl (λ n → ρX (f n))
  ρX (hΩ (c , p) g) = hΩ (c , ⊲ᴮ-tr p X) (λ x → ρX (g x))

t₁ : HB (TI.Kat (bI 1) (TI.slb (RI.tower 1)))
t₁ = TI.st (RI.tower 1)

t₂ : HB (TI.Kat (bI 2) (TI.slb (RI.tower 2)))
t₂ = TI.st (RI.tower 2)

ρ₁t₁ : HB K∞
ρ₁t₁ = ρX {lb = TI.slb (RI.tower 1)} (hlim 1 hself) t₁

ρ₂t₂ : HB K∞
ρ₂t₂ = ρX {lb = TI.slb (RI.tower 2)} (hlim 2 hself) t₂

no-lim-n : ¬ (_⊲[_]_ {K∞} ρ₁t₁ [] ρ₂t₂)
no-lim-n (hLim e (hLim e′ ()))
```
