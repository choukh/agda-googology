# 按级回灌 (一): 种类的嵌入与沿嵌入的连续分支

> 不含记号. 入口 [KindLv](KindLv.lagda.md), 接口 [KindLvIf](KindLvIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 嵌入的三个构造与复合.** 恒等 `idE`, `step` 的旧种类 `stepE` (`inj₁`, 世界取 `proj₁`), 并的一个分量 `supE i` (`(i , _)`, 世界取第 $i$ 个分量). 三者的坐标转换都是恒等函数 (坐标类型定义相等), 界与第一位置原样. 复合 `_∘E_`.
> - **§2 `nbJ`: 沿嵌入的连续分支.** `HtTowerCont.nbᴮ` 的推广: 坐标 $y$ 在 `S′` 里, 输出在 `S` 里, $y$ 的 $\Omega$-结点 (种类 $\kappa$) 读成输出的 $\Omega$-结点 (种类 `j κ`). `nbᴮ` 是 `stepE` 的特例 (构造文件 `KindLvCmp` 写对照). 单调对坐标的路径归纳 (`nbJ-mono`), 合法由形状给出 (`Lg-nbJ`).
> - **§3 `LgΩ`**: 嵌入的种类上的 $\Omega$-结点, 分支在被嵌入的结构里单调且合法, 就合法. 级读回的两种 $\Omega$-行都用它.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KindLvEmb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.KindLvIf
```

## §1 嵌入的构造

```agda
idE : ∀ {S : KS} → Emb S S
idE = record { j = λ κ → κ ; cv = λ e → e ; vc = λ c → c ; cv-vc = λ c → refl ; π = λ w → w ; lgπ = λ l → l
             ; bd→ = λ b → b ; bd← = λ b → b ; pr→ = λ p → p ; lgE→ = λ l → l }

stepE : ∀ {S : KS} → Emb S (step S)
stepE = record { j = inj₁ ; cv = λ e → e ; vc = λ c → c ; cv-vc = λ c → refl ; π = proj₁ ; lgπ = proj₁
               ; bd→ = λ b → b ; bd← = λ b → b ; pr→ = λ p → p ; lgE→ = λ l → l }

supE : ∀ {I : Set} {F : I → KS} (i : I) → Emb (F i) (sup I F)
supE i = record { j = λ κ → i , κ ; cv = λ e → e ; vc = λ c → c ; cv-vc = λ c → refl ; π = λ w → w i ; lgπ = λ l → l i
                ; bd→ = λ b → b ; bd← = λ b → b ; pr→ = λ p → p ; lgE→ = λ l → l }

infixr 9 _∘E_
_∘E_ : ∀ {S₁ S₂ S₃ : KS} → Emb S₂ S₃ → Emb S₁ S₂ → Emb S₁ S₃
F ∘E G = record
  { j = λ κ → j F (j G κ) ; cv = λ e → cv G (cv F e) ; vc = λ c → vc F (vc G c)
  ; cv-vc = λ c → trans (cong (cv G) (cv-vc F (vc G c))) (cv-vc G c)
  ; π = λ w → π G (π F w) ; lgπ = λ l → lgπ G (lgπ F l)
  ; bd→ = λ b → bd→ G (bd→ F b) ; bd← = λ b → bd← F (bd← G b)
  ; pr→ = λ p → pr→ G (pr→ F p) ; lgE→ = λ l → lgE→ G (lgE→ F l) }
```

## §2 沿嵌入的连续分支

```agda
module _ {S′ S : KS} (Em : Emb S′ S) where
  nbJ : HB S → (HB S′ → HB S → HB S) → HB S′ → HB S
  nbJ b s hz = b
  nbJ b s (hs y) = s y (nbJ b s y)
  nbJ b s (hl f) = hl (λ n → nbJ b s (f n))
  nbJ b s (hΩ κ h) = hΩ (j Em κ) (λ e → nbJ b s (h (cv Em e)))

  module _ {b : HB S} {s : HB S′ → HB S → HB S} (fs : ∀ y h {w} → h ⊲[ w ] s y h) where
    nbJ-mono : ∀ {y y′ w} → y ⊲[ π Em w ] y′ → nbJ b s y ⊲[ w ] nbJ b s y′
    nbJ-mono hself = hself
    nbJ-mono (hsuc p) = ⊲ᴮ-tr (nbJ-mono p) (fs _ _)
    nbJ-mono (hlim n p) = hlim n (nbJ-mono p)
    nbJ-mono {y} {w = w} (hLim {g = h} {c = c} bd p) =
      hLim (bd← Em bd) (subst (λ z → nbJ b s y ⊲[ w ] nbJ b s (h z)) (sym (cv-vc Em c)) (nbJ-mono p))

    nbJ-fst : ∀ y {w} → b ⊲[ w ] nbJ b s y
    nbJ-fst hz = hself
    nbJ-fst (hs y) = ⊲ᴮ-tr (nbJ-fst y) (fs _ _)
    nbJ-fst (hl f) = hlim 0 (nbJ-fst (f 0))
    nbJ-fst (hΩ κ h) {w} = hLim (botBd S (j Em κ) w) (nbJ-fst (h (cv Em (bot S (j Em κ)))))

    Lg-nbJ : LgB b → (∀ y h → LgB h → LgB (s y h)) → ∀ y → LgB y → LgB (nbJ b s y)
    Lg-nbJ lb ls hz _ = lb
    Lg-nbJ lb ls (hs y) l = ls y _ (Lg-nbJ lb ls y l)
    Lg-nbJ lb ls (hl f) (st , l) = (λ n → nbJ-mono (st n)) , (λ n → Lg-nbJ lb ls (f n) (l n))
    Lg-nbJ lb ls (hΩ κ h) (mo , l) =
      (λ lw e e′ p → nbJ-mono (mo (lgπ Em lw) (bd→ Em e) (bd→ Em e′) (pr→ Em p))) ,
      (λ e le → Lg-nbJ lb ls (h (cv Em e)) (l _ (lgE→ Em le)))
```

## §3 嵌入的种类上的 $\Omega$-结点

```agda
LgΩ : ∀ {S′ S : KS} (Em : Emb S′ S) (κ : K S′) (g : E S′ κ → HB S) →
      (∀ {w c c′} → LgW S w → Pr S′ κ (π Em w) c c′ → g c ⊲[ w ] g c′) →
      (∀ c → LgE S′ κ c → LgB (g c)) → LgB (hΩ (j Em κ) (λ e → g (cv Em e)))
LgΩ Em κ g mo lg = (λ lw e e′ p → mo lw (pr→ Em p)) , (λ e le → lg (cv Em e) (lgE→ Em le))
```
