# 可数层的对角 (三): 含 `Lev` 的级, 改一个分量要判定坐标相等

> 不含记号. 入口 [DiagK](DiagK.lagda.md). [HtTowerNStage](HtTowerNStage.lagda.md) 的带包含的塔 `L′ (k+1) = step (L′ k) ⊕ₖ Lev (Ωtop (L′ k))`. 读法 (判断) 上通向 EBO 的是 `Lev` 这一半: `Lev (Ωtop S) = sup (HB S) (c ↦ Lev (up c))`, 种类以 `HB S` 的高度为下标, **世界是坐标上的函数** $\prod_{c}\mathrm{Wd}(\mathrm{Lev}(\mathrm{up}\,c))$. 有限级的对角 (本路) 不造一切级的并, 但**每一级 $k\ge1$ 自己就含这个函数世界**.
>
> **`updL→wdec` (条件定理, 对一切 `S`):** 在 `Lev (Ωtop S)` 的世界上 "恰好换掉坐标 $c$ 处的分量, 其余不动" (`UpdS`, 律 `atS`, `offS`), 就能对 `HB S` 的任意两个高度判定 "不相等, 或者不是不相等". 实例: `S = L′ k` 对一切 $k$ (`updL′→wdec`); `S = S₀` 时坐标就是第二数类的高度 `H₀`. 证明是 `CohWUpd.upd→wdec` 的同形物: 每个分量的世界都有一个可判别的 "底" 与 "非底" (`tst`, `w0`, `w1`, 对一切高度 $x$ 的 `Lev x` 递归), 再看换过之后的分量.
>
> **范围.** 条件定理, 不是否定: 不说 `UpdS` 不存在 (经典地存在), 只说造它至少要判定高度相等. 判断 (同 `CohWUpd`): 高度有函数分支, 这样的判定在 `--safe --without-K` 里写不出. 不否定别的折叠设计 (例如回灌不改一个分量); 只对 `HtTowerFFold` 那样 "回灌时恰好升高一个种类的界, 低层输出落回原世界" 的写法有约束 (判断). 对照 [DiagKPos](DiagKPos.lagda.md): 有限多种类、按位置存时同样的更新是定义, 种类相等可判定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagKLev where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNStage using (L′; two)
```

## §1 每个 `Lev x` 的世界里有可判别的底

`tst x w`: 世界 $w$ 是不是 "底". 对 $x$ 结构递归: $0$ 级看 `A` 是不是 $0$; 后继看新分量是不是 $0$; 两种极限看第 $0$ 个 (或最小坐标 `bot`) 分量.

```agda
tst : ∀ {S} (x : HB S) → Wd (Lev x) → Bool
tst hz azero = true
tst hz (asuc _) = false
tst hz (alim _) = false
tst (hs x) (w , hz) = true
tst (hs x) (w , hs _) = false
tst (hs x) (w , hl _) = false
tst (hs x) (w , hΩ _ _) = false
tst (hl f) w = tst (f 0) (w 0)
tst {S} (hΩ κ g) w = tst (g (bot S κ)) (w (bot S κ))

w0 w1 : ∀ {S} (x : HB S) → Wd (Lev x)
w0 hz = azero
w0 (hs x) = w0 x , hz
w0 (hl f) = λ n → w0 (f n)
w0 (hΩ κ g) = λ c → w0 (g c)
w1 hz = asuc azero
w1 (hs x) = w0 x , hs hz
w1 (hl f) = λ n → w1 (f n)
w1 (hΩ κ g) = λ c → w1 (g c)

t0 : ∀ {S} (x : HB S) → tst x (w0 x) ≡ true
t0 hz = refl
t0 (hs x) = refl
t0 (hl f) = t0 (f 0)
t0 {S} (hΩ κ g) = t0 (g (bot S κ))

t1 : ∀ {S} (x : HB S) → tst x (w1 x) ≡ false
t1 hz = refl
t1 (hs x) = refl
t1 (hl f) = t1 (f 0)
t1 {S} (hΩ κ g) = t1 (g (bot S κ))
```

## §2 一般的并: 恰好改一个分量推出弱判定

```agda
module _ {I : Set} (F : I → KS)
  (t : ∀ i → Wd (F i) → Bool) (a b : ∀ i → Wd (F i))
  (ta : ∀ i → t i (a i) ≡ true) (tb : ∀ i → t i (b i) ≡ false) where

  record UpdS : Set where
    field
      upd  : (i : I) → Wd (F i) → Wd (sup I F) → Wd (sup I F)
      atS  : ∀ i v w → upd i v w i ≡ v
      offS : ∀ i v w i′ → ¬ (i ≡ i′) → upd i v w i′ ≡ w i′
  open UpdS

  t≢ : true ≡ false → ⊥
  t≢ ()

  module _ (U : UpdS) where
    look : ∀ i i′ (r : Bool) → t i′ (upd U i (b i) a i′) ≡ r → ¬ (i ≡ i′) ⊎ ¬ ¬ (i ≡ i′)
    look i i′ true e = inj₁ (λ { refl → t≢ (trans (sym e) (trans (cong (t i) (atS U i (b i) a)) (tb i))) })
    look i i′ false e = inj₂ (λ ne → t≢ (trans (sym (ta i′)) (trans (cong (t i′) (sym (offS U i (b i) a i′ ne))) e)))

    upd→wdec : ∀ i i′ → ¬ (i ≡ i′) ⊎ ¬ ¬ (i ≡ i′)
    upd→wdec i i′ = look i i′ (t i′ (upd U i (b i) a i′)) refl
```

## §3 实例: `Lev (Ωtop S)`, 一切 `S`; 带包含的塔的每一级

`Wd (Lev (Ωtop S))` 定义地就是 $\prod_{c:\mathrm{HB}\,S}\mathrm{Wd}(\mathrm{Lev}(\mathrm{up}\,c))$.

```agda
module _ (S : KS) where
  FΩ : HB S → KS
  FΩ c = Lev (up c)

  wd-Ωtop : Wd (Lev (Ωtop S)) ≡ ((c : HB S) → Wd (FΩ c))
  wd-Ωtop = refl

  UpdL : Set
  UpdL = UpdS FΩ (λ c → tst (up c)) (λ c → w0 (up c)) (λ c → w1 (up c)) (λ c → t0 (up c)) (λ c → t1 (up c))

  updL→wdec : UpdL → ∀ (y y′ : HB S) → ¬ (y ≡ y′) ⊎ ¬ ¬ (y ≡ y′)
  updL→wdec U = upd→wdec FΩ (λ c → tst (up c)) (λ c → w0 (up c)) (λ c → w1 (up c)) (λ c → t0 (up c)) (λ c → t1 (up c)) U

-- 带包含的塔的第 k+1 级里的 Lev 分量, 一切 k
updL′→wdec : ∀ k → UpdL (L′ k) → ∀ (y y′ : HB (L′ k)) → ¬ (y ≡ y′) ⊎ ¬ ¬ (y ≡ y′)
updL′→wdec k = updL→wdec (L′ k)

-- k = 0: 坐标是第二数类的高度
updH₀→wdec : UpdL S₀ → ∀ (y y′ : HB S₀) → ¬ (y ≡ y′) ⊎ ¬ ¬ (y ≡ y′)
updH₀→wdec = updL→wdec S₀
```

`L′ (k+1)` 的世界是 `Bool` 上的族, `false` 分量就是上面的函数世界:

```agda
wd-L′ : ∀ k → Wd (L′ (suc k)) ≡ ((b : Bool) → Wd (two (step (L′ k)) (Lev (Ωtop (L′ k))) b))
wd-L′ k = refl

wd-L′f : ∀ k → Wd (two (step (L′ k)) (Lev (Ωtop (L′ k))) false) ≡ ((c : HB (L′ k)) → Wd (Lev (up c)))
wd-L′f k = refl
```
