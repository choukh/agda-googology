# 种类带证据, 比较取 `cmpB₀` (三): 外层 `A`-世界长高时的两条相干条件

> 不含记号. 入口 [AdmEv](AdmEv.lagda.md). 接手清单第 3 条 (`EvWGrow` 文件头): 外层 `A`-世界 $a\mapsto a'$ ($q : a\lhd a'$) 也长时, 证据 $p : c\lhd_{[a]} b$ 搬成 `⊲ᴮ↑ q p` (每个 `hLim e` 的坐标证据 $e$ 变成 $e ⨾ q$, 即 `⊲-tr e q`); 界 $b$ 的合法数据里, ℕ-极限的步进 `st` 与 $\Omega$-结点的单调 `mo` 都以世界为参数, `mo` 还以世界的合法证明为参数.
>
> **两条条件, 各自写清.**
>
> - **(C1) 世界的合法证明相干**: 旧世界的合法证明取新世界合法证明沿 $q$ 的限制, $\mathrm{la} = $ `lg⊲ q la′`. 在这条之下, 坐标证据接上 $q$ 后 `cmpF` 不变 (`cmpF-tr`, 定理, 无条件), 坐标的合法证明也不变 (`lg⊲-tr`). 所以 (C1) 处理了 "坐标证据的 `⊲-tr`" 这一条; 它是对世界数据的选择, 本篇把它直接写进陈述 (旧世界的合法证明就是 `lg⊲ q la′`).
> - **(C2) 界的合法数据对世界自然** (`NatB`): 每个 ℕ-极限结点 `st {a′} n ≡ ⊲ᴮ↑ q (st {a} n)`; 每个 $\Omega$-结点 `mo la′ (e ⨾ q) (e′ ⨾ q) r ≡ ⊲ᴮ↑ q (mo la e e′ r)`; 递归到子树. 这是 "`mo` 对世界合法证明的依赖" 这一条.
>
> **定理** `cmp-↑`: (C1), (C2) 之下, `cmpB₀` 与世界的长高交换 (结果路径也搬过去). **`wk-A`**: 于是重放不变. **前提可满足** (`nat-ΩA`): `EvWGrow.ΩA` (分支 $\iota_A$, 单调数据沿路径递归, 不看世界) 对一切 $q$ 满足 (C2); (C1) 对 $a' = \mathrm{asuc}\,a$, $q$ = `suc self` 定义地成立.
>
> **否定** `no-up-inv`: 只有 (C1) 不够. 实例: 外层界的单调数据按世界选进 $\omega_0$ 的不同项 (世界是极限时走第 0 项, 否则走第 1 项; 合法数据); 世界从 $a_0$ 长到 $\mathrm{asuc}\,a_0$ ((C1) 定义地成立), 同一事件表的重放从 $R_1$ 变成 $R_2$ (`EvWNeg` 的两个互不为第一位置的界). **只否定**: "对一切合法外层界, 只要 (C1), `A`-世界长高后重放与原来相等或可比". 不否定 (C2) 之下的不变性 (那是 `wk-A`, 定理).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmEvGrowA where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; cmpF; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; toLt)
open import OCF.Align.UniTrNeg using (emb⊲)
open import OCF.Align.AdmWCmp using (cmpB₀; dec-diag)
open import OCF.Align.EvWGrow using (ιA; ιA-⊲; Lg-ιA; ΩA; lΩA)
open import OCF.Align.EvWNeg using (ω₀; g; lgg; a₀; la₀; Ωz; lΩz; p₁; pz; R₁; R₂; R-ne; R₁⋬R₂; R₂⋬R₁; Rel)
open import OCF.Align.AdmEvBase
```

## §1 `A` 一侧: 坐标证据接上 $q$

```agda
lg⊲-tr : ∀ {x a a′} (e : x ⊲ a) (q : a ⊲ a′) (la′ : Lg a′) → lg⊲ (⊲-tr e q) la′ ≡ lg⊲ e (lg⊲ q la′)
lg⊲-tr e C.self la′ = refl
lg⊲-tr e (C.suc q) la′ = lg⊲-tr e q la′
lg⊲-tr e (C.lim n q) la′ = lg⊲-tr e q (proj₂ la′ n)

cmpF-tr : ∀ {x x′ a a′} (e : x ⊲ a) (e′ : x′ ⊲ a) (q : a ⊲ a′) (la′ : Lg a′) →
          cmpF (⊲-tr e q) (⊲-tr e′ q) la′ ≡ cmpF e e′ (lg⊲ q la′)
cmpF-tr e e′ C.self la′ = refl
cmpF-tr e e′ (C.suc q) la′ = cmpF-tr e e′ q la′
cmpF-tr e e′ (C.lim n q) (st , w) rewrite dec-diag n = cmpF-tr e e′ q (w n)
```

## §2 高度一侧: 路径随世界长高

```agda
module Up {a a′ : A} (q : a ⊲ a′) where
  ↑ : ∀ {x y : HB S₀} → x ⊲[ a ] y → x ⊲[ a′ ] y
  ↑ = ⊲ᴮ↑ {S₀} q

  ↑-tr : ∀ {x y z : HB S₀} (s : x ⊲[ a ] y) (t : y ⊲[ a ] z) → ↑ (⊲ᴮ-tr s t) ≡ ⊲ᴮ-tr (↑ s) (↑ t)
  ↑-tr s hself = refl
  ↑-tr s (hsuc t) = cong hsuc (↑-tr s t)
  ↑-tr s (hlim n t) = cong (hlim n) (↑-tr s t)
  ↑-tr s (hLim e t) = cong (hLim (⊲-tr e q)) (↑-tr s t)

  emb-↑ : ∀ {x y : HB S₀} (r : x ⊲[ a ] y) (v : HB (Lev x)) → emb⊲ (↑ r) v ≡ emb⊲ r v
  emb-↑ hself v = refl
  emb-↑ (hsuc r) v = cong up (emb-↑ r v)
  emb-↑ (hlim {f = f} n r) v = cong (ι {F = λ k → Lev (f k)} n) (emb-↑ r v)
  emb-↑ (hLim {g = g′} {c = c} e r) v = cong (ι {F = λ d → Lev (g′ d)} c) (emb-↑ r v)

  toLt-↑ : ∀ {x y : HB S₀} (r : x ⊲[ a ] y) → toLt (↑ r) ≡ toLt r
  toLt-↑ hself = refl
  toLt-↑ (hsuc r) rewrite toLt-↑ r = refl
  toLt-↑ (hlim n r) rewrite toLt-↑ r = refl
  toLt-↑ (hLim e r) rewrite toLt-↑ r = refl

  ↑⊎ : ∀ {x y : HB S₀} → (y ⊲[ a ] x) ⊎ (x ⊲[ a ] y) → (y ⊲[ a′ ] x) ⊎ (x ⊲[ a′ ] y)
  ↑⊎ (inj₁ r) = inj₁ (↑ r)
  ↑⊎ (inj₂ s) = inj₂ (↑ s)
```

**条件 (C2).** 旧世界的合法证明写成 `lg⊲ q la′` ((C1)).

```agda
module Nat {a a′ : A} (q : a ⊲ a′) (la′ : Lg a′) where
  open Up q

  la : Lg a
  la = lg⊲ q la′

  NatB : (t : HB S₀) → LgB t → Set
  NatB hz _ = ⊤
  NatB (hs t) l = NatB t l
  NatB (hl f) (st , l) = (∀ n → st {a′} n ≡ ↑ (st {a} n)) × (∀ n → NatB (f n) (l n))
  NatB (hΩ tt h) (mo , l) =
    (∀ {x x′} (e : x ⊲ a) (e′ : x′ ⊲ a) (r : x ⊲ x′) → mo la′ (⊲-tr e q) (⊲-tr e′ q) r ≡ ↑ (mo (lg⊲ q la′) e e′ r)) ×
    (∀ x (lx : Lg x) → NatB (h x) (l x lx))

  steps-↑ : ∀ {f : ℕ → HB S₀} (st : ∀ {w} n → f n ⊲[ w ] f (suc n)) → (∀ n → st {a′} n ≡ ↑ (st {a} n)) →
            ∀ {n m} (r : n <ᴺ m) → stepsᴮ st {a′} r ≡ ↑ (stepsᴮ st {a} r)
  steps-↑ st ns zero = ns _
  steps-↑ st ns (suc r) = trans (cong₂ ⊲ᴮ-tr (steps-↑ st ns r) (ns _)) (sym (↑-tr (stepsᴮ st r) (st _)))
```

## §3 比较与长高交换

```agda
  cmp-↑ : ∀ {c c₀ L : HB S₀} (lL : LgB L) → NatB L lL → (p : c ⊲[ a ] L) (p₀ : c₀ ⊲[ a ] L) →
          cmpB₀ (↑ p) (↑ p₀) la′ lL ≡ ↑⊎ (cmpB₀ p p₀ (lg⊲ q la′) lL)
  cmp-↑ lL nL hself p₀ = refl
  cmp-↑ lL nL (hsuc p) hself = refl
  cmp-↑ lL nL (hlim n p) hself = refl
  cmp-↑ lL nL (hLim e p) hself = refl
  cmp-↑ lL nL (hsuc p) (hsuc p₀) = cmp-↑ lL nL p p₀
  cmp-↑ (st , l) (nst , nl) (hlim n p) (hlim m p₀) with <ᴺ-dec n m
  ... | injᵃ n<m =
    trans (cong (λ t → cmpB₀ t (↑ p₀) la′ (l m))
                (trans (cong (⊲ᴮ-tr (↑ p)) (steps-↑ st nst n<m)) (sym (↑-tr p (stepsᴮ st n<m)))))
          (cmp-↑ (l m) (nl m) (⊲ᴮ-tr p (stepsᴮ st n<m)) p₀)
  ... | injᵇ m<n =
    trans (cong (λ t → cmpB₀ (↑ p) t la′ (l n))
                (trans (cong (⊲ᴮ-tr (↑ p₀)) (steps-↑ st nst m<n)) (sym (↑-tr p₀ (stepsᴮ st m<n)))))
          (cmp-↑ (l n) (nl n) p (⊲ᴮ-tr p₀ (stepsᴮ st m<n)))
  ... | injᶜ refl = cmp-↑ (l n) (nl n) p p₀
  cmp-↑ (mo , l) (nmo , nl) (hLim {c = x} e p) (hLim {c = x′} e′ p₀)
    rewrite cmpF-tr e e′ q la′ with cmpF e e′ (lg⊲ q la′)
  ... | inj₁ C.self =
    trans (cong (λ z → cmpB₀ (↑ p) (↑ p₀) la′ (l x z)) (lg⊲-tr e q la′))
          (cmp-↑ (l x (lg⊲ e (lg⊲ q la′))) (nl x _) p p₀)
  ... | inj₁ (C.suc r) =
    trans (cong₂ (λ t z → cmpB₀ (↑ p) t la′ (l x z))
                 (trans (cong (⊲ᴮ-tr (↑ p₀)) (nmo e′ e (C.suc r))) (sym (↑-tr p₀ (mo (lg⊲ q la′) e′ e (C.suc r)))))
                 (lg⊲-tr e q la′))
          (cmp-↑ (l x (lg⊲ e (lg⊲ q la′))) (nl x _) p (⊲ᴮ-tr p₀ (mo (lg⊲ q la′) e′ e (C.suc r))))
  ... | inj₁ (C.lim k r) =
    trans (cong₂ (λ t z → cmpB₀ (↑ p) t la′ (l x z))
                 (trans (cong (⊲ᴮ-tr (↑ p₀)) (nmo e′ e (C.lim k r))) (sym (↑-tr p₀ (mo (lg⊲ q la′) e′ e (C.lim k r)))))
                 (lg⊲-tr e q la′))
          (cmp-↑ (l x (lg⊲ e (lg⊲ q la′))) (nl x _) p (⊲ᴮ-tr p₀ (mo (lg⊲ q la′) e′ e (C.lim k r))))
  ... | inj₂ r =
    trans (cong₂ (λ t z → cmpB₀ t (↑ p₀) la′ (l x′ z))
                 (trans (cong (⊲ᴮ-tr (↑ p)) (nmo e e′ r)) (sym (↑-tr p (mo (lg⊲ q la′) e e′ r))))
                 (lg⊲-tr e′ q la′))
          (cmp-↑ (l x′ (lg⊲ e′ (lg⊲ q la′))) (nl x′ _) (⊲ᴮ-tr p (mo (lg⊲ q la′) e e′ r)) p₀)
```

## §4 重放不变

```agda
module GrowA {a a′ : A} (q : a ⊲ a′) (la′ : Lg a′) (b : HB S₀) (lb : LgB b) where
  open Up q
  open Nat q la′
  module O = Rp₀ a b (lg⊲ q la′) lb
  module N = Rp₀ a′ b la′ lb

  upE : O.Ev → N.Ev
  upE e = N.ev (O.ec e) (↑ (O.ep e)) (O.eδ e) (O.elδ e)

  contrib-↑ : ∀ {c c₀} (R : (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)) δ acc →
              N.contrib (N.fix (↑⊎ R)) δ acc ≡ O.contrib (O.fix R) δ acc
  contrib-↑ (inj₁ r) δ acc = cong (acc ⊞_) (emb-↑ r δ)
  contrib-↑ (inj₂ s) δ acc rewrite toLt-↑ s = fl (toLt s) δ acc
    where
    fl : ∀ {c c₀} (t : (c ≡ c₀) ⊎ (c <ᴮ c₀)) (δ : HB (Lev c₀)) (acc : HB (Lev c)) →
         N.contrib (N.fromLt t) δ acc ≡ O.contrib (O.fromLt t) δ acc
    fl (inj₁ refl) δ acc = refl
    fl (inj₂ _) δ acc = refl

  wk-A : NatB b lb → ∀ H c (p : c ⊲[ a ] b) → N.rp (map upE H) c (↑ p) ≡ O.rp H c p
  wk-A nb [] c p = refl
  wk-A nb (e ∷ H) c p =
    trans (cong₂ (λ r t → N.contrib (N.fix r) (O.eδ e) t) (cmp-↑ lb nb p (O.ep e)) (wk-A nb H c p))
          (contrib-↑ (cmpB₀ p (O.ep e) (lg⊲ q la′) lb) (O.eδ e) (O.rp H c p))
```

## §5 前提可满足

`ΩA`: 分支 $\iota_A$, 单调数据 `ιA-⊲ r`, 不看世界与坐标证据. 它的数据在一切 $q$ 下自然.

```agda
module _ {a a′ : A} (q : a ⊲ a′) (la′ : Lg a′) where
  open Up q
  open Nat q la′

  ιA-↑ : ∀ {x x′} (r : x ⊲ x′) → ιA-⊲ {w = a′} r ≡ ↑ (ιA-⊲ {w = a} r)
  ιA-↑ C.self = refl
  ιA-↑ (C.suc r) = cong hsuc (ιA-↑ r)
  ιA-↑ (C.lim n r) = cong (hlim n) (ιA-↑ r)

  nat-ιA : ∀ x (lx : Lg x) → NatB (ιA x) (Lg-ιA x lx)
  nat-ιA azero lx = tt
  nat-ιA (asuc x) lx = nat-ιA x lx
  nat-ιA (alim f) (st , l) = (λ n → ιA-↑ (st n)) , (λ n → nat-ιA (f n) (l n))

  nat-ΩA : NatB ΩA lΩA
  nat-ΩA = (λ e e′ r → ιA-↑ r) , nat-ιA

-- 实例: a′ = asuc a, q = suc self; (C1) 定义地成立: lg⊲ q la′ 就是 la′
inst-A : ∀ (a : A) (la : Lg a) H c (p : c ⊲[ a ] ΩA) →
  Rp₀.rp (asuc a) ΩA la lΩA (map (GrowA.upE (C.suc C.self) la ΩA lΩA) H) c (⊲ᴮ↑ {S₀} (C.suc C.self) p)
  ≡ Rp₀.rp a ΩA la lΩA H c p
inst-A a la H c p = GrowA.wk-A (C.suc C.self) la ΩA lΩA (nat-ΩA (C.suc C.self) la) H c p
```

## §6 只有 (C1) 不够

外层界 $b_w = \Omega$-结点, 分支同 `EvWNeg.g` ($g(0)=0$, 其余 $g(x)=\omega_0$, $\omega_0$ = 常值 $0$ 的 ℕ-极限). 单调数据从坐标 $0$ 到别的坐标走 $\omega_0$ 的第 `pick w` 项: 世界是 ℕ-极限时 $0$, 否则 $1$. 合法 (`LgB` 只要这样一个函数). 世界 $a_0=\lim_n 1$ 长到 $\mathrm{asuc}\,a_0$, 合法证明不变 ((C1) 定义地成立).

```agda
pick : A → ℕ
pick (alim _) = 0
pick _ = 1

mgw : ∀ {w} (x x′ : A) → x ⊲ x′ → g x ⊲[ w ] g x′
mgw azero azero _ = hself
mgw {w} azero (asuc _) _ = hlim (pick w) hself
mgw {w} azero (alim _) _ = hlim (pick w) hself
mgw (asuc _) azero ()
mgw (asuc _) (asuc _) _ = hself
mgw (asuc _) (alim _) _ = hself
mgw (alim _) azero ()
mgw (alim _) (asuc _) _ = hself
mgw (alim _) (alim _) _ = hself

bw : HB S₀
bw = hΩ tt g

lbw : LgB bw
lbw = (λ {w} {x} {x′} lw e e′ pr → mgw x x′ pr) , (λ x _ → lgg x)

pzw : hz ⊲[ a₀ ] bw
pzw = hLim {c = azero} (z⊲ a₀) hself

p₁w : ω₀ ⊲[ a₀ ] bw
p₁w = hLim {c = asuc azero} (C.lim 0 C.self) hself

Hw : Rp₀.Hist a₀ bw la₀ lbw
Hw = record { ec = hz ; ep = pzw ; eδ = Ωz ; elδ = lΩz } ∷ []

q₀ : a₀ ⊲ asuc a₀
q₀ = C.suc C.self

old-R₁ : Rp₀.rp a₀ bw la₀ lbw Hw ω₀ p₁w ≡ R₁
old-R₁ = refl

new-R₂ : Rp₀.rp (asuc a₀) bw la₀ lbw (map (GrowA.upE q₀ la₀ bw lbw) Hw) ω₀ (⊲ᴮ↑ {S₀} q₀ p₁w) ≡ R₂
new-R₂ = refl

UpInv : Set
UpInv = ∀ {a a′} (q : a ⊲ a′) (la′ : Lg a′) {b} (lb : LgB b) (H : Rp₀.Hist a b (lg⊲ q la′) lb) c (p : c ⊲[ a ] b) →
        Rel c (Rp₀.rp a′ b la′ lb (map (GrowA.upE q la′ b lb) H) c (⊲ᴮ↑ {S₀} q p)) (Rp₀.rp a b (lg⊲ q la′) lb H c p)

no-up-inv : ¬ UpInv
no-up-inv I with I q₀ la₀ lbw Hw ω₀ p₁w
... | inj₁ e = R-ne (sym e)
... | inj₂ (inj₁ (v , r)) = R₂⋬R₁ r
... | inj₂ (inj₂ (v , r)) = R₁⋬R₂ r
```
