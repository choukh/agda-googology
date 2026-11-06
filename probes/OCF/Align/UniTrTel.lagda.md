# 非选择性的增量搬运 (三): 望远镜版, 由外层界决定的内层界族

> 不含记号. 入口 [UniTr](UniTr.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> [TelW](TelW.lagda.md) 的第一个障碍留下的候选: 推入位置 (分支 $c_0$ 里的内层位置) 的界由外层位置的界 $b$ 决定, $F\,b$; 回灌升高外层界 ($b\mapsto b'$), 要求内层的格在当前分支 $c_0$ 处有界 (忠实), 别处单调. 固定 $c_0$, 设内层的层号比外层高一级 (内层值的种类结构是 `step S`, 外层是 `S`; 在 `LFReTy` 里就是 `Lv (ls ℓ) = step (Lv ℓ)`): 内层的高度里有以外层的值为坐标的种类 ($\Omega_{\ell+1}$ 的副本).
>
> - **`Mono`**: $x\lhd x'$ (都在内层世界的 $\Omega_{\ell+1}$-界之下) 推出 $F\,x\lhd F\,x'$. 这就是 "界族对外层界单调", 也是 "别的分支处单调" 的形式 (取 $x'=b'$, $x=b$).
> - **`Faith O b`**: 对一切合法的内层增量 $\delta'$, 有外层的新界 $b'$ 与内层世界 $(w,\beta)$, 其中 $b'\lhd_{[w]}\beta$ (内层世界看得见升高后的外层界, "相干"), 使格 $F\,b\boxplus\delta'$ 在 $(w,\beta)$ 里是 $F\,b'$ 的第一位置.
> - **`no-outer-lift`** (对一切 `S`, 否定): `Mono` + 合法 + `Faith` 推出 $\bot$. Burali-Forti 的形状: 对角增量 $\delta'^{*}=\Omega_{\ell+1}$ 上的结点, 坐标 $x$ 处的分支是 $1\boxplus F\,x$; 它合法 (`Lg-diag`, 用 `Mono`); 若有 $b'$ 使 $F\,b\boxplus\delta'^{*}\lhd F\,b'$, 沿坐标 $b'$ 走一步得到 $F\,b\boxplus(1\boxplus F\,b')\lhd F\,b'$, 与 `UniTrBase.no-1⊞` 矛盾. 不用判定, 结论是 $\bot$ (不是弱判定): 有判定也造不出这样的 $F$.
> - **前提可满足**: `upLift` (`F = up`) 满足 `Mono` 与合法; 它对一切有限增量满足 `Faith` 的形状 (`faith-fin`). 所以矛盾来自 "对一切合法增量忠实", 而不是某一条前提本身.
> - **`tel-no-lift`**: 同一件事写在 `TelWTy` 的望远镜上: 望远镜 `ls ℓ ∷ ℓ ∷ rest`, 内层条目由外层条目决定 (`((w , b′) , F b′)`), 种类 `(z , inj₂ tt)` 的有界性就是 `Faith` 里的格.
>
> **范围.** 只否定 "内层界只经外层界升高" 这一种取界; 内层层号不高于外层时不适用 (那时内层没有以外层的值为坐标的种类); 不否定直接升高内层位置 (那是 `TelWNeg` 的 `raise→¬cmp`, `sel→¬cmp`, `occ-find→dec` 管的), 不否定积世界版 (见 [UniTrNeg](UniTrNeg.lagda.md) 的开放点).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniTrTel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (LH; ls; Lv; FL)
open import OCF.Align.TelWTy using (Tel; ST; z)
import OCF.Align.TelWTy as TW
open import OCF.Align.UniTrBase using (no-1⊞)
```

## §1 一般形

```agda
module _ (S : KS) where
  Mono : (HB S → HB (step S)) → Set
  Mono F = ∀ {w β x x′} → LgW (step S) (w , β) → x ⊲[ w ] β → x′ ⊲[ w ] β → x ⊲[ w ] x′ →
           F x ⊲[ (w , β) ] F x′

  record OuterLift : Set where
    field
      F    : HB S → HB (step S)
      mono : Mono F
      lgF  : ∀ x → LgB x → LgB (F x)
  open OuterLift public

  Faith : OuterLift → HB S → Set
  Faith O b = ∀ δ′ → LgB δ′ → Σ (HB S) (λ b′ → Σ (Wd S) (λ w → Σ (HB S) (λ β →
              (b′ ⊲[ w ] β) × (F O b ⊞ δ′ ⊲[ (w , β) ] F O b′))))

  diag : OuterLift → HB (step S)
  diag O = hΩ (inj₂ tt) (λ x → hs hz ⊞ F O x)

  Lg-diag : ∀ O → LgB (diag O)
  Lg-diag O = (λ {W} lW e e′ p → ⊞-⊲ (hs hz) (mono O {proj₁ W} {proj₂ W} lW e e′ p)) ,
              (λ x lx → Lg-⊞ (hs hz) (F O x) tt (lgF O x lx))

  no-outer-lift : ∀ (O : OuterLift) b → ¬ Faith O b
  no-outer-lift O b fa with fa (diag O) (Lg-diag O)
  ... | b′ , w , β , e , cell = no-1⊞ (F O b) (F O b′) (⊲ᴮ-tr (hLim {c = b′} e hself) cell)
```

## §2 前提可满足

`F = up`: 单调 (`up-⊲`), 合法 (`Lg-up`). 对有限增量 $\delta'=n$ 取 $b'=b\boxplus n$, 格就是界本身 (`up-fin`).

```agda
  upLift : OuterLift
  upLift = record { F = up ; mono = λ lW e e′ p → up-⊲ p ; lgF = Lg-up }

  finS : ℕ → HB S
  finS zero = hz
  finS (suc n) = hs (finS n)

  finT : ℕ → HB (step S)
  finT zero = hz
  finT (suc n) = hs (finT n)

  up-fin : ∀ b n → up (b ⊞ finS n) ≡ up b ⊞ finT n
  up-fin b zero = refl
  up-fin b (suc n) = cong hs (up-fin b n)

  faith-fin : ∀ b n (w : Wd S) → Σ (HB S) (λ b′ → (b′ ⊲[ w ] b′) × (F upLift b ⊞ finT n ⊲[ (w , b′) ] F upLift b′))
  faith-fin b n w = b ⊞ finS n , hself , subst (λ t → up b ⊞ finT n ⊲[ (w , b ⊞ finS n) ] t) (sym (up-fin b n)) hself
```

## §3 在 `TelWTy` 的望远镜上

外层位置 `s z` 的层号 $\ell$, 内层位置 `z` 的层号 `ls ℓ`. 条目类型定义地是 `Wd (FL ℓ) = Wd (Lv ℓ) × HB (Lv ℓ)` 与 `Wd (FL (ls ℓ)) = (Wd (Lv ℓ) × HB (Lv ℓ)) × HB (step (Lv ℓ))`. 内层条目由外层条目决定: 内层世界就是外层条目 (相干), 内层的界是 $F\,b'$.

```agda
module _ (ℓ : LH) (rest : List LH) where
  tel-no-lift : (F : HB (Lv ℓ) → HB (Lv (ls ℓ))) → Mono (Lv ℓ) F → (∀ x → LgB x → LgB (F x)) →
    (w : Wd (Lv ℓ)) (Γr : Tel rest) (b : HB (Lv ℓ)) →
    ¬ (∀ δ′ → LgB δ′ → Σ (HB (Lv ℓ)) (λ b′ →
        Bd (ST (ls ℓ ∷ ℓ ∷ rest)) (z , inj₂ tt) (F b ⊞ δ′) (TW._∷_ ((w , b′) , F b′) (TW._∷_ (w , b′) Γr))))
  tel-no-lift F mo lg w Γr b fa =
    no-outer-lift (Lv ℓ) (record { F = F ; mono = mo ; lgF = lg }) b
      (λ δ′ lδ′ → proj₁ (fa δ′ lδ′) , w , proj₁ (fa δ′ lδ′) , hself , proj₂ (fa δ′ lδ′))
```
