# 层号换类型, 否定一路 (一): 分量的陷阱, 对角与新站的层号

> 不含记号. 入口 [NegLvKt](NegLvKt.lagda.md). 对着接口 [LvKtIf](LvKtIf.lagda.md) ("接口定稿 2026-11-05 15:21 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> 接口的三个类型都是并 `sup I F`: 极限 `KΛc = sup ℕ Kc`, 下一站 `nxt K = sup (⊤ ⊎ HB K) (FN K)`, 以 $\Omega$-结点为层号的级 `Lev (hΩ κ g) = sup (E κ) (Lev ∘ g)`. 嵌入 `emb`, 读回注入 `injL c`, 进极限 `ιΛ s` 都是分量注入 `ι`. 本篇的一条引理对一切并成立:
>
> 1. **陷阱 (`Trap.trap`, 定理).** 并里, 第 $i$ 个分量注入的高度若是第 $j\ne i$ 个分量注入的高度的第一位置 (在任一世界里), 它就**没有 $\Omega$-结点** (`OmFree`). 推论 **`Trap.no-two`**: 一个合法高度在一个合法世界里, 不能同时以两个不同分量注入的、都含 $\Omega$-结点的高度为第一位置 (两个第一位置可比, `cmpB`, 再用陷阱). 这是 `HtTowerNeg.no-naive-diag` (只对 `Ωn k`) 推广到一切并、一切含 $\Omega$-结点的高度.
> 2. **对角 (`diag-trap`, 定理).** 若极限站的层号列取各站层号的注入 `ιΛ s (B s)`, 并且 ℕ-极限合法, 则**每一站的层号都没有 $\Omega$-结点**. 前提可满足 (`Lg-finDiag`: 有限层号); 有 $\Omega$-结点的层号使它不合法 (`diag-illegal`).
> 3. **新站 (`no-two-nxt`, 定理).** 在 `nxt K` 里, 旧层号的嵌入 `emb x` 与读回的注入 `injL c r` 不能同时是一个合法高度在一个合法世界里的第一位置, 除非其中一个没有 $\Omega$-结点. 两半各自可满足 (`satEmb`, 合法的 `ωK`).
> 4. **$\Omega$-结点层号 (`no-two-Ω`, 定理).** 层号是 $\mathrm{h\Omega}\,\kappa\,g$ 时, 级 `Lev` 的两个不同坐标 $x\ne x'$ 的分支读回 (各自注入自己的分量) 不能同时是读回的第一位置, 除非其中一个没有 $\Omega$-结点.
> 5. **出口 (定理).** 部分和的写法 (`LvTop.cum` 的形状) 不撞陷阱: 对角 `ΛΛ = hl cumΛ` 合法 (`Lg-ΛΛ`), 不纯于任何一站 (`mixed`, 在类型上不被困在某一站). 但代价是: 第 $s+1$ 站 ($s\ge0$) 的增量 (注入第 $s+1$ 个分量) **不是**对角的字面第一位置 (`stage-not-below`, 在玩具实例上), 只有第 0 站的是 (`stage0-below`). 所以 "对角越过每一站" 不能由字面第一位置给出, 只能是值的比较.
> 6. **前提可满足 (定理).** `foldSlot`: 对一切 `K`, `ck`, 读回取输入世界在码上的槽, 是 `FoldAllK` 的实例; 于是 `FoldTower`, `FoldLimK` 有实例 (`towerSlot`, `limSlot`), 并且实例依赖输入. 这不说明值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegLvKtTrap where

open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtCode using (CdK; cdLev; w0; lw0)
open import OCF.Align.LvKtIf
```

## §1 陷阱: 一切并

`OmFree x`: $x$ 里没有 $\Omega$-结点 (只有 $0$, 后继, ℕ-极限). `Pure j x`: $x$ 的一切 $\Omega$-结点的种类都在第 $j$ 个分量. 分量注入的高度纯于自己的分量 (`pure-ι`); 第一位置保持纯 (`pure⊲`); 纯于两个不同分量的高度没有 $\Omega$-结点 (`two-pure`). 证明只看构造子, 不判定任何高度.

```agda
OmFree : ∀ {S} → HB S → Set
OmFree hz = ⊤
OmFree (hs x) = OmFree x
OmFree (hl f) = ∀ n → OmFree (f n)
OmFree (hΩ κ g) = ⊥

module Trap (I : Set) (F : I → KS) where
  Pure : I → HB (sup I F) → Set
  Pure j hz = ⊤
  Pure j (hs x) = Pure j x
  Pure j (hl f) = ∀ n → Pure j (f n)
  Pure j (hΩ κ g) = (proj₁ κ ≡ j) × (∀ c → Pure j (g c))

  pure-ι : ∀ j x → Pure j (ι {I} {F} j x)
  pure-ι j hz = tt
  pure-ι j (hs x) = pure-ι j x
  pure-ι j (hl f) = λ n → pure-ι j (f n)
  pure-ι j (hΩ κ g) = refl , (λ c → pure-ι j (g c))

  pure⊲ : ∀ {j a b w} → a ⊲[ w ] b → Pure j b → Pure j a
  pure⊲ hself h = h
  pure⊲ (hsuc p) h = pure⊲ p h
  pure⊲ (hlim n p) h = pure⊲ p (h n)
  pure⊲ (hLim e p) h = pure⊲ p (proj₂ h _)

  two-pure : ∀ {i j} → ¬ (i ≡ j) → ∀ x → Pure i x → Pure j x → OmFree x
  two-pure d hz p q = tt
  two-pure d (hs x) p q = two-pure d x p q
  two-pure d (hl f) p q = λ n → two-pure d (f n) (p n) (q n)
  two-pure d (hΩ κ g) (e , _) (e′ , _) = d (trans (sym e) e′)

  free-ι : ∀ {i} x → OmFree (ι {I} {F} i x) → OmFree x
  free-ι hz h = tt
  free-ι (hs x) h = free-ι x h
  free-ι (hl f) h = λ n → free-ι (f n) (h n)
  free-ι (hΩ κ g) ()

  trap : ∀ {i j w} → ¬ (i ≡ j) → (x : HB (F i)) (y : HB (F j)) →
         ι {I} {F} i x ⊲[ w ] ι j y → OmFree x
  trap {i} {j} d x y p = free-ι x (two-pure d (ι i x) (pure-ι i x) (pure⊲ p (pure-ι j y)))

  no-two : ∀ {i j w L} → ¬ (i ≡ j) → LgW (sup I F) w → LgB L → (x : HB (F i)) (y : HB (F j)) →
           ι {I} {F} i x ⊲[ w ] L → ι j y ⊲[ w ] L → OmFree x ⊎ OmFree y
  no-two d lw lL x y p q with cmpB p q lw lL
  ... | inj₁ yx = inj₂ (trap (λ e → d (sym e)) y x yx)
  ... | inj₂ xy = inj₁ (trap d x y xy)

k≢sk : ∀ k → ¬ (k ≡ suc k)
k≢sk zero ()
k≢sk (suc k) e = k≢sk k (cong pred e)
```

## §2 对角: 各站层号的注入列

构造一路需要它的地方: 接口文件头 "对角在 `KΛc` 里另写一列 (`Bᴧ`), 相邻项同在 `HB KΛc` 里". 最直接的一列是各站的层号 `B s : HB (Kc s)` 经 `ιΛ s` 进极限; 下面说这一列合法时每站的层号都没有 $\Omega$-结点. 只用到一个世界里的一步 (ℕ-极限的合法性对一切世界成立, 取基世界 `w0 ckΛ` 即可).

```agda
module TΛ = Trap ℕ Kc

diag-trap : (w : Wd KΛc) (B : (s : ℕ) → HB (Kc s)) →
            LgB {KΛc} (hl (λ s → ιΛ s (B s))) → ∀ s → OmFree (B s)
diag-trap w B (st , _) s = TΛ.trap (k≢sk s) (B s) (B (suc s)) (st {w} s)
```

**前提可满足**: 层号取有限高度时这一列合法.

```agda
finB : ∀ {S} → ℕ → HB S
finB zero = hz
finB (suc n) = hs (finB n)

lgFin : ∀ {S} n → LgB {S} (finB n)
lgFin zero = tt
lgFin (suc n) = lgFin n

ι-fin : ∀ {I F} (i : I) n → ι {I} {F} i (finB n) ≡ finB n
ι-fin i zero = refl
ι-fin i (suc n) = cong hs (ι-fin i n)

step-fin : ∀ {w : Wd KΛc} n → ιΛ n (finB n) ⊲[ w ] ιΛ (suc n) (finB (suc n))
step-fin n rewrite ι-fin {ℕ} {Kc} n n | ι-fin {ℕ} {Kc} (suc n) (suc n) = hsuc hself

Lg-finDiag : LgB {KΛc} (hl (λ s → ιΛ s (finB s)))
Lg-finDiag = (λ n → step-fin n) , (λ n → Lg-ι n (finB n) (lgFin n))
```

**有 $\Omega$-结点时不合法**: `ωK s` 是底种类上的常值 $\Omega$-结点逐站嵌入 (合法, `lg-ωK`).

```agda
ωK : ∀ s → HB (Kc s)
ωK zero = hΩ tt (λ _ → hz)
ωK (suc s) = emb (ωK s)

lg-ωK : ∀ s → LgB (ωK s)
lg-ωK zero = (λ lw e e′ p → hself) , (λ c lc → tt)
lg-ωK (suc s) = Lg-ι (inj₁ tt) (ωK s) (lg-ωK s)

notFree : ∀ s → ¬ OmFree (ωK s)
notFree zero ()
notFree (suc s) h = notFree s (Trap.free-ι (⊤ ⊎ HB (Kc s)) (FN (Kc s)) (ωK s) h)

diag-illegal : ¬ LgB {KΛc} (hl (λ s → ιΛ s (ωK s)))
diag-illegal l = notFree 0 (diag-trap (w0 ckΛ) ωK l 0)
```

## §3 新站: 旧层号的嵌入与读回的注入

构造一路需要它的地方: 接口 "读回进新站: `injL c` ... 第 $s$ 站在层号 $c$ 处的读回原样成为第 $s+1$ 站层号所在类型里的高度", 以及 "塔只说 `emb (B s) ⊲[ w ] B (s+1)`". 若新层号 `B (s+1)` 要同时以旧层号的嵌入与读回的注入为字面第一位置, 两者至少一个没有 $\Omega$-结点.

```agda
inj≢ : ∀ {K : KS} {c : HB K} → ¬ (inj₁ tt ≡ inj₂ c)
inj≢ ()

no-two-nxt : ∀ {K} {w : Wd (nxt K)} {L : HB (nxt K)} → LgW (nxt K) w → LgB L →
  (x : HB K) (c : HB K) (r : HB (Lev c)) →
  emb x ⊲[ w ] L → injL c r ⊲[ w ] L → OmFree x ⊎ OmFree r
no-two-nxt {K} lw lL x c r p q = Trap.no-two (⊤ ⊎ HB K) (FN K) inj≢ lw lL x r p q
```

两半各自可满足: `L` 取 `emb (ωK s)` 本身 (合法, 有 $\Omega$-结点), 或取 `injL c r` 本身.

```agda
satEmb : ∀ s {w} → emb (ωK s) ⊲[ w ] emb (ωK s)
satEmb s = hself

lg-satEmb : ∀ s → LgB (emb (ωK s))
lg-satEmb s = Lg-ι (inj₁ tt) (ωK s) (lg-ωK s)
```

## §4 层号是 $\Omega$-结点时, 两个分支的读回

构造一路需要它的地方: 码目标 `tgt c` 是 $\Omega$-结点时, 槽类型 `HB (Lev (tgt c))` 是对坐标的并. 若读回 `rt` 要以各坐标分支的读回 (注入各自的分量) 为字面第一位置, 两个不同坐标的分支读回至少一个没有 $\Omega$-结点.

```agda
no-two-Ω : ∀ {S} (κ : K S) (g : E S κ → HB S) {x x′ : E S κ} → ¬ (x ≡ x′) →
  {w : Wd (Lev (hΩ κ g))} {L : HB (Lev (hΩ κ g))} → LgW (Lev (hΩ κ g)) w → LgB L →
  (r : HB (Lev (g x))) (r′ : HB (Lev (g x′))) →
  ι {E S κ} {λ c → Lev (g c)} x r ⊲[ w ] L → ι {E S κ} {λ c → Lev (g c)} x′ r′ ⊲[ w ] L → OmFree r ⊎ OmFree r′
no-two-Ω {S} κ g d lw lL r r′ p q = Trap.no-two (E S κ) (λ c → Lev (g c)) d lw lL r r′ p q
```

## §5 出口: 部分和的对角

增量 `δ s` 是第 $s$ 站底种类 (经嵌入) 上的常值 $\Omega$-结点. 部分和 `cumΛ` 照 `LvTop.cum` 的形状, 对角 `ΛΛ` 合法, 不纯于任何一站. 但第 $s+1$ 站的增量不是对角的字面第一位置.

```agda
κb : ∀ s → K (Kc s)
κb zero = tt
κb (suc s) = inj₁ tt , κb s

δ : ∀ s → HB (Kc s)
δ s = hΩ (κb s) (λ _ → hz)

Lg-δ : ∀ s → LgB (δ s)
Lg-δ s = (λ lw e e′ p → hself) , (λ c lc → tt)

cumΛ : ℕ → HB KΛc
cumΛ zero = ιΛ 0 (δ 0)
cumΛ (suc n) = cumΛ n ⊞ ιΛ (suc n) (δ (suc n))

Lg-cumΛ : ∀ n → LgB (cumΛ n)
Lg-cumΛ zero = Lg-ι 0 (δ 0) (Lg-δ 0)
Lg-cumΛ (suc n) = Lg-⊞ (cumΛ n) (ιΛ (suc n) (δ (suc n))) (Lg-cumΛ n) (Lg-ι (suc n) (δ (suc n)) (Lg-δ (suc n)))

ΛΛ : HB KΛc
ΛΛ = hl cumΛ

Lg-ΛΛ : LgB ΛΛ
Lg-ΛΛ = (λ n → ⊞-fst (cumΛ n) (ιΛ (suc n) (δ (suc n)))) , Lg-cumΛ

pure-cum : ∀ {t} n → TΛ.Pure t (cumΛ n) → t ≡ 0
pure-cum zero (e , _) = sym e
pure-cum {t} (suc n) (e , h) = pure-cum n (h (bot KΛc (suc n , κb (suc n))))

mixed : ∀ t → ¬ TΛ.Pure (suc t) ΛΛ
mixed t h with pure-cum (suc t) (h (suc t))
... | ()

below-cum : ∀ s n {w x} → x ⊲[ w ] cumΛ n → TΛ.Pure (suc s) x → OmFree x
below-cum s zero hself (() , _)
below-cum s zero (hLim e hself) p = tt
below-cum s (suc n) hself (_ , h) with pure-cum n (h (bot KΛc (suc n , κb (suc n))))
... | ()
below-cum s (suc n) (hLim e q) p = below-cum s n q p

stage-not-below : ∀ s {w} → ¬ (ιΛ (suc s) (δ (suc s)) ⊲[ w ] ΛΛ)
stage-not-below s (hlim n p) = below-cum s n p (TΛ.pure-ι (suc s) (δ (suc s)))

stage0-below : ∀ {w} → ιΛ 0 (δ 0) ⊲[ w ] ΛΛ
stage0-below = hlim 0 hself
```

## §6 接口的前提可满足 (依赖输入的实例)

```agda
foldSlot : ∀ K ck → FoldAllK K ck
foldSlot K ck = record
  { rt = λ la lb c cv w lw → w c ; lrt = λ la lb c cv w lw → lw c
  ; H = λ la lb c cv w lw → hz ; lgH = λ la lb c cv w lw → tt }

towerSlot : FoldTower
towerSlot s = foldSlot (Kc s) (ckc s)

limSlot : FoldLimK
limSlot = foldSlot KΛc ckΛ
```

## §7 只否定什么

- **否定**: (a) 极限站层号列取各站层号的注入 `ιΛ s (B s)` 而某站层号含 $\Omega$-结点 (`diag-trap`, `diag-illegal`); (b) 新站层号同时以 `emb x` 与 `injL c r` 为字面第一位置而两者都含 $\Omega$-结点 (`no-two-nxt`); (c) $\Omega$-结点层号上的读回同时以两个不同坐标的分支读回 (各自注入) 为字面第一位置而两者都含 $\Omega$-结点 (`no-two-Ω`); (d) 在部分和对角的玩具实例上, 第 $s+1$ 站的增量是对角的字面第一位置 (`stage-not-below`).
- **不否定**: 接口的任何记录或定义 (`FoldAtK`, `FoldTower`, `FoldLimK` 有依赖输入的实例 `foldSlot`); 部分和写法的对角 (`Lg-ΛΛ`, 合法且不纯于任一站); `emb (B s) ⊞ injL c r` 这种把读回接在旧层号之后的新层号 (不是两个分量各自的字面第一位置); 值的比较 ("对角的值不低于每一站" 可以成立, 这里只说它不能是字面第一位置).
- `stage-not-below` 只在玩具增量 `δ` 上证明; 一般的部分和是否以某站的整个层号为第一位置, 取决于构造一路的具体增量 (判断: 只要第 0 项含第 0 站的 $\Omega$-结点, 同一论证适用).
