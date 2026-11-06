# 带证据的回灌 (一): 每一层里下标可判定的种类的回灌件

> 不含记号. 入口 [SLFb](SLFb.lagda.md), 接口 [SLFbIf](SLFbIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 对层号 $k$ 的结构递归, 给 `Lv k` 的每个种类一个第 0 级的回灌件 `KC` (接口 §2) 或 "有损":
>
> - `step` 的新种类 (坐标是高度 `HB (Lv x)`, 对一切 $x$): **有**. 加法 $b\boxplus\mathrm{toB}\,a$, 升界只换 `step` 的第二分量 (`kcNew`, 对一切种类结构).
> - `step` 的旧种类: 沿用 (`kcOld`, 换第一分量).
> - `ll f` 的分量 $n$ (下标 $\mathbb N$): 沿用, 世界在 $n$ 处点更新 (`kcℕ`, `GenFoldInst.upd`).
> - `lΩ k g` 的分量 `inj₁ tt` (下标 $\top\uplus\ldots$ 的左边): 沿用, 世界在左分量更新 (`kcL`, `GenFoldInst.updL`).
> - `lΩ k g` 的分量 `inj₂ c` (下标是坐标 $c$, 含函数): **有损**. 不判定 $c$.
>
> 所以 "有回灌" 恰是 "从 `Lv k` 的根到该种类的路径不经过坐标下标" 的那些种类 (`kcLv`). 判定只发生在 $\mathbb N$ 与 $\top\uplus B$ 的构造子上, 不比较两个层号, 不比较两个坐标.
>
> 顶坐标 `topV` 与 [FabLFReGen](FabLFReGen.lagda.md) 的 `topLv` 逐行相同, 只是把 `lΩ` 一行的分量函数写成顶层名字 `topΩ` (这样 `kcL` 的类型与顶坐标定义相等, 不用比较两个 `where` 函数). 另给每个层号一个可读成 `A` 的种类 `akV` (接口 §2 `AK`): 第 0 层的新种类 (坐标 `HB S⊥`) 沿可判定的路径的拷贝; 第 0 层 (`lz`) 没有.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SLFbKit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; topBd)
open import OCF.Align.GenFoldTree using (topStepG)
open import OCF.Align.GenFoldInst using (topSupG; upd; upd-R; upd-Q; upd-at; updL)
open import OCF.Align.LFReTy
open import OCF.Align.FabLFReGen using (top⊥; LvΩ; frE⊥; frE⊥-⊲; frE⊥-lg)
open import OCF.Align.RsOwnIf using (RsK; rs; rs≤; rsLg; rs-top)
open import OCF.Align.SLFbIf
```

## §1 顶坐标 (同 `topLv`, 分量函数有名字)

```agda
topV : (k : LH) → TopG (Lv k)
topΩ : (k : LH) (g : HB (Lv k) → LH) (i : ⊤ ⊎ HB (Lv k)) → TopG (LvΩ k g i)
topV lz = top⊥
topV (ls x) = topStepG (topV x)
topV (ll f) = topSupG ℕ (λ n → Lv (f n)) (λ n → topV (f n))
topV (lΩ k g) = topSupG (⊤ ⊎ HB (Lv k)) (LvΩ k g) (topΩ k g)
topΩ k g (inj₁ _) = topStepG (topV k)
topΩ k g (inj₂ c) = topV (g c)
```

## §2 `A` 写成高度

```agda
toB : ∀ {S : KS} → A → HB S
toB azero = hz
toB (asuc a) = hs (toB a)
toB (alim f) = hl (λ n → toB (f n))

toB-⊲ : ∀ {S : KS} {a b} {w : Wd S} → a ⊲ b → toB {S} a ⊲[ w ] toB b
toB-⊲ C.self = hself
toB-⊲ (C.suc p) = hsuc (toB-⊲ p)
toB-⊲ (C.lim n p) = hlim n (toB-⊲ p)

Lg-toB : ∀ {S : KS} a → Lg a → LgB (toB {S} a)
Lg-toB azero l = tt
Lg-toB (asuc a) l = Lg-toB a l
Lg-toB (alim f) (st , l) = (λ n → toB-⊲ (st n)) , (λ n → Lg-toB (f n) (l n))
```

## §3 回灌件的四个构造

```agda
module _ {S : KS} (tp : TopG S) where
  kcNew : KC (step S) (topStepG tp) (inj₂ tt)
  kcNew = record
    { ad = λ b a → b ⊞ toB a
    ; ad-fst = λ b a → ⊞-fst b (toB a)
    ; ad-lg = λ {b} {a} lb la → Lg-⊞ b (toB a) lb (Lg-toB a la)
    ; rk = record
      { rs = λ w v → proj₁ w , v
      ; rs≤ = λ p → ≤w-rf S , p
      ; rsLg = λ lw lv → proj₁ lw , lv
      ; rs-top = refl } }

  kcOld : ∀ {κ} → KC S tp κ → KC (step S) (topStepG tp) (inj₁ κ)
  kcOld K = record
    { ad = ad K ; ad-fst = λ b a → ad-fst K b a ; ad-lg = ad-lg K
    ; rk = record
      { rs = λ w v → rs (rk K) (proj₁ w) v , proj₂ w
      ; rs≤ = λ p → rs≤ (rk K) p , hself
      ; rsLg = λ lw lv → rsLg (rk K) (proj₁ lw) lv , proj₂ lw
      ; rs-top = rs-top (rk K) } }

module _ (F : ℕ → KS) (tps : (n : ℕ) → TopG (F n)) where
  kcℕ : ∀ n {κ} → KC (F n) (tps n) κ → KC (sup ℕ F) (topSupG ℕ F tps) (n , κ)
  kcℕ n {κ} K = record
    { ad = ad K ; ad-fst = λ b a → ad-fst K b a ; ad-lg = ad-lg K
    ; rk = record
      { rs = λ w v → upd {λ m → Wd (F m)} w n (rs (rk K) (w n) v)
      ; rs≤ = λ {w} {v} p → upd-R {λ m → Wd (F m)} (λ m → _≤w_ (F m)) w n (rs (rk K) (w n) v) (λ m → ≤w-rf (F m)) (rs≤ (rk K) p)
      ; rsLg = λ {w} {v} lw lv → upd-Q {λ m → Wd (F m)} (λ m → LgW (F m)) w n (rs (rk K) (w n) v) lw (rsLg (rk K) (lw n) lv)
      ; rs-top = λ {w} {v} → upd-at {λ m → Wd (F m)} w n (rs (rk K) (w n) v) (λ u → top (tps n) κ u ≡ v) (rs-top (rk K)) } }

module _ {B : Set} (F : ⊤ ⊎ B → KS) (tps : (i : ⊤ ⊎ B) → TopG (F i)) where
  kcL : ∀ {κ} → KC (F (inj₁ tt)) (tps (inj₁ tt)) κ → KC (sup (⊤ ⊎ B) F) (topSupG (⊤ ⊎ B) F tps) (inj₁ tt , κ)
  kcL K = record
    { ad = ad K ; ad-fst = λ b a → ad-fst K b a ; ad-lg = ad-lg K
    ; rk = record
      { rs = λ w v → updL {P = λ j → Wd (F j)} w (rs (rk K) (w (inj₁ tt)) v)
      ; rs≤ = λ p → λ { (inj₁ tt) → rs≤ (rk K) p ; (inj₂ c) → ≤w-rf (F (inj₂ c)) }
      ; rsLg = λ lw lv → λ { (inj₁ tt) → rsLg (rk K) (lw (inj₁ tt)) lv ; (inj₂ c) → lw (inj₂ c) }
      ; rs-top = rs-top (rk K) } }
```

## §4 每一层: 路径不经坐标下标的种类有回灌件

```agda
mapS : ∀ {X Y : Set} → (X → Y) → X ⊎ ⊤ → Y ⊎ ⊤
mapS f (inj₁ x) = inj₁ (f x)
mapS f (inj₂ _) = inj₂ tt

kcLv : (k : LH) (κ : K (Lv k)) → KC (Lv k) (topV k) κ ⊎ ⊤
kcSt : (k : LH) (κ : K (step (Lv k))) → KC (step (Lv k)) (topStepG (topV k)) κ ⊎ ⊤
kcLv lz ()
kcLv (ls x) κ = kcSt x κ
kcLv (ll f) (n , κ) = mapS (kcℕ (λ m → Lv (f m)) (λ m → topV (f m)) n) (kcLv (f n) κ)
kcLv (lΩ k g) (inj₁ tt , κ) = mapS (kcL (LvΩ k g) (topΩ k g)) (kcSt k κ)
kcLv (lΩ k g) (inj₂ c , κ) = inj₂ tt
kcSt k (inj₁ κ) = mapS (kcOld (topV k)) (kcLv k κ)
kcSt k (inj₂ tt) = inj₁ (kcNew (topV k))
```

**可读成 `A` 的种类.** 第 0 层 `S⊥` 上的 `step` 的新种类, 坐标 `HB S⊥` 经 `frE⊥` 读成 `A`; 沿 `step` 的旧种类, $\mathbb N$ 分量 $0$, 左分量 `inj₁ tt` 搬上去.

```agda
akNew : AK (step S⊥)
akNew = record { κa = inj₂ tt ; fr = frE⊥ ; fr-lg = λ {e} l → frE⊥-lg e l ; fr-mono = λ lw e e′ p → frE⊥-⊲ p }

akOld : ∀ {Q : KS} → AK Q → AK (step Q)
akOld a = record { κa = inj₁ (κa a) ; fr = fr a ; fr-lg = fr-lg a ; fr-mono = λ lw e e′ p → fr-mono a (proj₁ lw) e e′ p }

akSup : ∀ {I : Set} {F : I → KS} (i : I) → AK (F i) → AK (sup I F)
akSup i a = record { κa = i , κa a ; fr = fr a ; fr-lg = fr-lg a ; fr-mono = λ lw e e′ p → fr-mono a (lw i) e e′ p }

akV : (k : LH) → AK (Lv k) ⊎ ⊤
akSt : (k : LH) → AK (step (Lv k)) ⊎ ⊤
akV lz = inj₂ tt
akV (ls x) = akSt x
akV (ll f) = mapS (akSup {F = λ n → Lv (f n)} 0) (akV (f 0))
akV (lΩ k g) = mapS (akSup {F = LvΩ k g} (inj₁ tt)) (akSt k)
akSt lz = inj₁ akNew
akSt (ls x) = mapS akOld (akV (ls x))
akSt (ll f) = mapS akOld (akV (ll f))
akSt (lΩ k g) = mapS akOld (akV (lΩ k g))
```

## §5 形状定理

```agda
-- 坐标下标之下的种类有损 (不判定 c)
deep-lossy-Lv : ∀ k g c κ → kcLv (lΩ k g) (inj₂ c , κ) ≡ inj₂ tt
deep-lossy-Lv k g c κ = refl

-- 一切 step 的新种类 (坐标是高度) 有回灌件, 不论层号是否含函数
new-fed : ∀ k → Σ (KC (step (Lv k)) (topStepG (topV k)) (inj₂ tt)) (λ K → kcSt k (inj₂ tt) ≡ inj₁ K)
new-fed k = kcNew (topV k) , refl

-- lΩ 层号里, 左分量 step (Lv k) 的新种类 (坐标 HB (Lv k)) 有回灌件, 对一切含函数的 g
lΩ-left-fed : ∀ k g → Σ (KC (Lv (lΩ k g)) (topV (lΩ k g)) (inj₁ tt , inj₂ tt)) (λ K → kcLv (lΩ k g) (inj₁ tt , inj₂ tt) ≡ inj₁ K)
lΩ-left-fed k g = _ , refl

-- 每个 lz 之上的 lΩ 层号都有可读成 A 的种类 (第 0 层新种类在左分量的拷贝)
akV-lΩ : ∀ g → Σ (AK (Lv (lΩ lz g))) (λ a → akV (lΩ lz g) ≡ inj₁ a)
akV-lΩ g = _ , refl
```
