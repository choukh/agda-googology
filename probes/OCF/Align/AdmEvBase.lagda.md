# 种类带证据, 比较取 `cmpB₀` (一): 重放, 新事件处字面忠实

> 不含记号. 入口 [AdmEv](AdmEv.lagda.md). 作者选定的方向原话: "与 B 合流: 种类带证据". 本篇把 [EvWBase](EvWBase.lagda.md) 的重放 `Rp.rp` 里的比较 `cmpS = fix ∘ cmpB` 换成 [AdmWCmp](AdmWCmp.lagda.md) 的 `cmpB₀` (`S = S₀`, 外层世界是 `A` 的一个层 $a$ 与一个高度界 $b$). 事件表 `EvT`, 事件的贡献 `Cm.contrib` 原样从 `EvWBase` 导入, 不改.
>
> **本篇的定理** (对一切 $a$, $b$ 与它们的合法证明):
>
> 1. **`new-gen₀`** (接手清单第 1 条): 对**一切**证据 $p$, 在 $(c,p)$ 处加事件后, 那里的界**字面地**是旧界 ⊞ δ (命题相等, 不经自环搬运). 对照 `EvWBase.new-gen`: 那里只得到 "旧界 ⊞ (δ 沿某个 $e : c\equiv c$ 的搬运)". 原因: `cmpB₀-diag` 说 `cmpB₀ p p` 是 `inj₁ hself`, 于是 `emb⊲ hself δ` 定义地是 δ.
> 2. `rp-mono`, `rp-suf`, `Lg-rp`, `rp-below`, `rp-above`, `dir-indep`: 与 `EvWBase` 同陈述, 换比较后照样成立.
> 3. `evKS₀`: 带证据的种类 $(c,p)$ 上, 事件表是种类结构 (`KS`).
>
> 律里出现的每一对坐标都带在 $b$ 之下的证据. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmEvBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_)
open import OCF.Align.UniTrNeg using (emb⊲; Lg-emb⊲)
open import OCF.Align.EvWBase using (module EvT; module Cm)
open import OCF.Align.AdmWCmp using (cmpB₀; cmpB₀-diag)
```

## §1 重放

```agda
module Rp₀ (a : A) (b : HB S₀) (la : Lg a) (lb : LgB b) where
  open Cm {S₀} a public
  open EvT {S₀} a b public

  X : HB S₀ → Set
  X c = HB (Lev c)

  cmpS : ∀ {c c₀} → c ⊲[ a ] b → c₀ ⊲[ a ] b → Cmp c c₀
  cmpS p p₀ = fix (cmpB₀ p p₀ la lb)

  rp : Hist → (c : HB S₀) → c ⊲[ a ] b → X c
  rp [] c p = hz
  rp (e ∷ es) c p = contrib (cmpS p (ep e)) (eδ e) (rp es c p)
```

## §2 新事件处字面忠实

```agda
  new-gen₀ : ∀ c (p : c ⊲[ a ] b) δ lδ es → rp (ev c p δ lδ ∷ es) c p ≡ rp es c p ⊞ δ
  new-gen₀ c p δ lδ es = cong (λ r → contrib (fix r) δ (rp es c p)) (cmpB₀-diag p la lb)
```

## §3 其余的律

```agda
  contrib-fst : ∀ {c c₀} (r : Cmp c c₀) δ acc {v} → acc ⊲[ v ] contrib r δ acc
  contrib-fst (inj₁ q) δ acc = ⊞-fst acc (emb⊲ q δ)
  contrib-fst (inj₂ _) δ acc = hself

  rp-mono : ∀ e es c p {v} → rp es c p ⊲[ v ] rp (e ∷ es) c p
  rp-mono e es c p = contrib-fst (cmpS p (ep e)) (eδ e) (rp es c p)

  rp-suf : ∀ {H H′} → Suf H H′ → ∀ c p {v} → rp H c p ⊲[ v ] rp H′ c p
  rp-suf here c p = hself
  rp-suf (there e s) c p = ⊲ᴮ-tr (rp-suf s c p) (rp-mono e _ c p)

  Lg-contrib : ∀ {c c₀} (r : Cmp c c₀) δ acc → LgB δ → LgB acc → LgB (contrib r δ acc)
  Lg-contrib (inj₁ q) δ acc lδ lacc = Lg-⊞ acc (emb⊲ q δ) lacc (Lg-emb⊲ q δ lδ)
  Lg-contrib (inj₂ _) δ acc lδ lacc = lacc

  Lg-rp : ∀ H c p → LgB (rp H c p)
  Lg-rp [] c p = tt
  Lg-rp (e ∷ es) c p = Lg-contrib (cmpS p (ep e)) (eδ e) (rp es c p) (elδ e) (Lg-rp es c p)

  contrib-below : ∀ {c c₀} → c <ᴮ c₀ → (r : Cmp c c₀) → ∀ δ acc → contrib r δ acc ≡ acc
  contrib-below l (inj₁ q) δ acc = ⊥-elim (no-both q l)
  contrib-below l (inj₂ _) δ acc = refl

  rp-below : ∀ e es c p → c <ᴮ ec e → rp (e ∷ es) c p ≡ rp es c p
  rp-below e es c p l = contrib-below l (cmpS p (ep e)) (eδ e) (rp es c p)

  contrib-above : ∀ {c c₀} → c₀ ⊲[ a ] c → (r : Cmp c c₀) → ∀ δ acc →
                  Σ (c₀ ⊲[ a ] c) (λ q → contrib r δ acc ≡ acc ⊞ emb⊲ q δ)
  contrib-above q₀ (inj₁ q) δ acc = q , refl
  contrib-above q₀ (inj₂ l) δ acc = ⊥-elim (no-both q₀ l)

  rp-above : ∀ e es c p → ec e ⊲[ a ] c →
             Σ (ec e ⊲[ a ] c) (λ q → rp (e ∷ es) c p ≡ rp es c p ⊞ emb⊲ q (eδ e))
  rp-above e es c p q₀ = contrib-above q₀ (cmpS p (ep e)) (eδ e) (rp es c p)

  dir-indep : ∀ {c c₀} (p p′ : c ⊲[ a ] b) (p₀ p₀′ : c₀ ⊲[ a ] b) → Same (cmpS p p₀) (cmpS p′ p₀′)
  dir-indep p p′ p₀ p₀′ = same (cmpS p p₀) (cmpS p′ p₀′)
```

## §4 带证据的种类结构

与 `EvWBase.EvKS` 同形, 重放换成上面的 `rp`. 内层世界取固定的合法族 $v_0$.

```agda
module EvKS₀ (a : A) (b : HB S₀) (la : Lg a) (lb : LgB b)
             (v₀ : (c : HB S₀) → Wd (Lev c)) (lv₀ : ∀ c → LgW (Lev c) (v₀ c)) where
  open Rp₀ a b la lb public

  Kᵉ : Set
  Kᵉ = Σ (HB S₀) (λ c → c ⊲[ a ] b)

  Eᵉ : Kᵉ → Set
  Eᵉ κ = X (proj₁ κ)

  Bdᵉ : (κ : Kᵉ) → Eᵉ κ → Hist → Set
  Bdᵉ κ x H = x ⊲[ v₀ (proj₁ κ) ] rp H (proj₁ κ) (proj₂ κ)

  Prᵉ : (κ : Kᵉ) → Hist → Eᵉ κ → Eᵉ κ → Set
  Prᵉ κ H x x′ = x ⊲[ v₀ (proj₁ κ) ] x′

  Bd↑ᵉ : ∀ {κ x H H′} → Suf H H′ → Bdᵉ κ x H → Bdᵉ κ x H′
  Bd↑ᵉ {κ} s e = ⊲ᴮ-tr e (rp-suf s (proj₁ κ) (proj₂ κ))

  cmpKᵉ : ∀ {κ x x′ H} → Bdᵉ κ x H → Bdᵉ κ x′ H → ⊤ → Prᵉ κ H x′ x ⊎ Prᵉ κ H x x′
  cmpKᵉ {κ} {H = H} e e′ _ = cmpB e e′ (lv₀ (proj₁ κ)) (Lg-rp H (proj₁ κ) (proj₂ κ))

  lgBdᵉ : ∀ {κ x H} → Bdᵉ κ x H → ⊤ → LgB x
  lgBdᵉ {κ} {H = H} e _ = lgB⊲ e (lv₀ (proj₁ κ)) (Lg-rp H (proj₁ κ) (proj₂ κ))

  botBdᵉ : ∀ κ H → Bdᵉ κ hz H
  botBdᵉ κ H = z⊲ᴮ (rp H (proj₁ κ) (proj₂ κ))

  evKS₀ : KS
  evKS₀ = record
    { K = Kᵉ ; E = Eᵉ ; Wd = Hist ; LgW = λ _ → ⊤
    ; _≤w_ = Suf ; ≤w-rf = here ; ≤w-tr = suf-tr
    ; Bd = Bdᵉ ; Pr = Prᵉ ; Bd↑ = λ {κ} {c} {w} {w′} s e → Bd↑ᵉ {κ} {c} {w} {w′} s e
    ; cmpK = λ {κ} {c} {c′} {w} e e′ l → cmpKᵉ {κ} {c} {c′} {w} e e′ l
    ; LgE = λ κ → LgB ; lgBd = λ {κ} {c} {w} e l → lgBdᵉ {κ} {c} {w} e l
    ; bot = λ κ → hz ; botBd = botBdᵉ }

  -- 在种类 κ 上加事件: 界字面地接上 δ
  bd-new : ∀ (κ : Kᵉ) δ lδ H → Bdᵉ κ (rp H (proj₁ κ) (proj₂ κ) ⊞ δ) (ev (proj₁ κ) (proj₂ κ) δ lδ ∷ H)
  bd-new κ δ lδ H = subst (λ t → (rp H (proj₁ κ) (proj₂ κ) ⊞ δ) ⊲[ v₀ (proj₁ κ) ] t)
                          (sym (new-gen₀ (proj₁ κ) (proj₂ κ) δ lδ H)) hself
```
