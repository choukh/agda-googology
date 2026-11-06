# LHRec (一): 每一层的合法化 `leg`, 世界的自反, 实例 `J₁`

> 不含记号. 入口 [LHRec](LHRec.lagda.md), 接口 [LHRecIf](LHRecIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [LHRecTy](LHRecTy.lagda.md), [LHRecIf](LHRecIf.lagda.md).
>
> **RecB 卡点 3 (第 $k$ 层的回灌).** RecB 的回灌 $B\boxplus\mathrm{leg}\,c$ 只对可数树写了 `leg`. 这里对**一切层号** $k$ 写合法化 `leg k : HB (Lv k) → HB (Lv k)`, 输出对一切输入合法 (`Lg-leg`). ℕ-极限取部分和 (同 CRw 的 `leg`); $\Omega$-结点的分支按坐标累加 (θ 式, 推广 `NegRecBPre.Lg-ΩA` 到旧种类): 坐标 $d$ 的后继处 $\theta(d+1)=\theta(d)\boxplus g(d+1)$, ℕ-极限逐点, 坐标里的 $\Omega$-结点映成输出里**同一个种类**的结点 (沿种类所在的上下文 `Ctx` 嵌回). 一切种类一条定义 (`θK` 对层号递归, 找到种类所在的 `step`), 单调与合法各一条定理.
>
> **实例** `J₁` (Kripke 式可入, 与否定一路 `NegLHRecIf` 的 `Kr.inst` 同形; 它的 `naive-adm↓-fails` 说明只读当前低层世界的可入不满足 `adm↓`): `Adm k (u,B) e` = 有更大的合法低层世界 $u'$ 使 $B\lhd_{u'}e$ 且 $e$ 合法; 进入后世界 $(u', e+1)$; 回灌 $B\boxplus\mathrm{leg}\,k\,c$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LHRecLeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecIf
```

## §1 上下文: 种类所在的位置

`Ctx T S`: 种类结构 $S$ 在 $T$ 里的位置 (经 `step` 的旧种类, 或 `sup` 的某个分量). 沿上下文: 种类嵌入 `ek`, 坐标往返 `toC`/`frC`, 世界投影 `pw`; 界与第一位置两个方向都字面对上 (每一步归约).

```agda
data Ctx (T : KS) : KS → Set₁ where
  here : Ctx T T
  viaS : ∀ {S} → Ctx T (step S) → Ctx T S
  viaL : ∀ {I F} → Ctx T (sup I F) → (i : I) → Ctx T (F i)

module _ {T : KS} where
  ek : ∀ {S} → Ctx T S → K S → K T
  ek here κ = κ
  ek (viaS c) κ = ek c (inj₁ κ)
  ek (viaL c i) κ = ek c (i , κ)

  frC : ∀ {S} (c : Ctx T S) κ → E T (ek c κ) → E S κ
  frC here κ e = e
  frC (viaS c) κ e = frC c (inj₁ κ) e
  frC (viaL c i) κ e = frC c (i , κ) e

  toC : ∀ {S} (c : Ctx T S) κ → E S κ → E T (ek c κ)
  toC here κ e = e
  toC (viaS c) κ e = toC c (inj₁ κ) e
  toC (viaL c i) κ e = toC c (i , κ) e

  frto : ∀ {S} (c : Ctx T S) κ e → frC c κ (toC c κ e) ≡ e
  frto here κ e = refl
  frto (viaS c) κ e = frto c (inj₁ κ) e
  frto (viaL c i) κ e = frto c (i , κ) e

  pw : ∀ {S} → Ctx T S → Wd T → Wd S
  pw here W = W
  pw (viaS c) W = proj₁ (pw c W)
  pw (viaL c i) W = pw c W i

  lgpw : ∀ {S} (c : Ctx T S) {W} → LgW T W → LgW S (pw c W)
  lgpw here l = l
  lgpw (viaS c) l = proj₁ (lgpw c l)
  lgpw (viaL c i) l = lgpw c l i

  bdTo : ∀ {S} (c : Ctx T S) κ {e W} → Bd S κ e (pw c W) → Bd T (ek c κ) (toC c κ e) W
  bdTo here κ b = b
  bdTo (viaS c) κ b = bdTo c (inj₁ κ) b
  bdTo (viaL c i) κ b = bdTo c (i , κ) b

  bdFr : ∀ {S} (c : Ctx T S) κ {e W} → Bd T (ek c κ) e W → Bd S κ (frC c κ e) (pw c W)
  bdFr here κ b = b
  bdFr (viaS c) κ b = bdFr c (inj₁ κ) b
  bdFr (viaL c i) κ b = bdFr c (i , κ) b

  prFr : ∀ {S} (c : Ctx T S) κ {e e′ W} → Pr T (ek c κ) W e e′ → Pr S κ (pw c W) (frC c κ e) (frC c κ e′)
  prFr here κ p = p
  prFr (viaS c) κ p = prFr c (inj₁ κ) p
  prFr (viaL c i) κ p = prFr c (i , κ) p
```

## §2 新种类的 θ 累加 (对任一位置的 `step U`)

`c : Ctx T (step U)`: 新种类 `inj₂ tt` (坐标是 `HB U`) 在 $T$ 里的位置. 坐标里 $U$ 的种类 $\kappa'$ 映成 $T$ 的种类 `ek c (inj₁ κ')`.

```agda
module New {T U : KS} (c : Ctx T (step U)) (g : HB U → HB T) where
  θ : HB U → HB T
  θ hz = g hz
  θ (hs d) = θ d ⊞ g (hs d)
  θ (hl f) = hl (λ n → θ (f n))
  θ (hΩ κ h) = hΩ (ek c (inj₁ κ)) (λ e → θ (h (frC c (inj₁ κ) e)))

  θ-⊲ : ∀ {W d d′} → d ⊲[ proj₁ (pw c W) ] d′ → θ d ⊲[ W ] θ d′
  θ-⊲ hself = hself
  θ-⊲ {d′ = hs d″} (hsuc p) = ⊲ᴮ-tr (θ-⊲ p) (⊞-fst (θ d″) (g (hs d″)))
  θ-⊲ (hlim n p) = hlim n (θ-⊲ p)
  θ-⊲ {W} (hLim {κ = κ} {g = h} {c = e} b p) =
    hLim (bdTo c (inj₁ κ) b) (subst (λ z → _ ⊲[ W ] θ (h z)) (sym (frto c (inj₁ κ) e)) (θ-⊲ p))

  Lg-θ : (∀ d → LgB (g d)) → ∀ d → LgB d → LgB (θ d)
  Lg-θ lg hz l = lg hz
  Lg-θ lg (hs d) l = Lg-⊞ (θ d) (g (hs d)) (Lg-θ lg d l) (lg (hs d))
  Lg-θ lg (hl f) (st , l) = (λ {W} n → θ-⊲ {W} (st n)) , (λ n → Lg-θ lg (f n) (l n))
  Lg-θ lg (hΩ κ h) (mo , l) =
    (λ {W} lw b b′ p → θ-⊲ {W} (mo (proj₁ (lgpw c lw)) (bdFr c (inj₁ κ) b) (bdFr c (inj₁ κ) b′) (prFr c (inj₁ κ) p))) ,
    (λ {W} lw b → Lg-θ lg _ (l (proj₁ (lgpw c lw)) (bdFr c (inj₁ κ) b)))
```

## §3 一切种类: 找到种类所在的 `step`

`θK x c κ`: 第 $x$ 层 (位置 $c$) 的种类 $\kappa$ 的累加. 对层号递归: `ls x` 的新种类与 `lΩ k g` 的指标种类直接用 §2; 旧种类与分量的种类往里走一层.

```agda
module _ {T : KS} where
  θK : ∀ x (c : Ctx T (Lv x)) (κ : K (Lv x)) → (E (Lv x) κ → HB T) → E (Lv x) κ → HB T
  θK lz c () g d
  θK (ls x) c (inj₂ _) g d = New.θ c g d
  θK (ls x) c (inj₁ κ) g d = θK x (viaS c) κ g d
  θK (ll f) c (n , κ) g d = θK (f n) (viaL c n) κ g d
  θK (lΩ k h) c (inj₁ _ , inj₂ _) g d = New.θ (viaL {F = FXL k h} c (inj₁ tt)) g d
  θK (lΩ k h) c (inj₁ _ , inj₁ κ) g d = θK k (viaS (viaL {F = FXL k h} c (inj₁ tt))) κ g d
  θK (lΩ k h) c (inj₂ e , κ) g d = θK (h e) (viaL {F = FXL k h} c (inj₂ e)) κ g d

  θK-⊲ : ∀ x (c : Ctx T (Lv x)) κ g {W d d′} → Pr (Lv x) κ (pw c W) d d′ → θK x c κ g d ⊲[ W ] θK x c κ g d′
  θK-⊲ lz c () g p
  θK-⊲ (ls x) c (inj₂ _) g p = New.θ-⊲ c g p
  θK-⊲ (ls x) c (inj₁ κ) g p = θK-⊲ x (viaS c) κ g p
  θK-⊲ (ll f) c (n , κ) g p = θK-⊲ (f n) (viaL c n) κ g p
  θK-⊲ (lΩ k h) c (inj₁ _ , inj₂ _) g p = New.θ-⊲ (viaL {F = FXL k h} c (inj₁ tt)) g p
  θK-⊲ (lΩ k h) c (inj₁ _ , inj₁ κ) g p = θK-⊲ k (viaS (viaL {F = FXL k h} c (inj₁ tt))) κ g p
  θK-⊲ (lΩ k h) c (inj₂ e , κ) g p = θK-⊲ (h e) (viaL {F = FXL k h} c (inj₂ e)) κ g p

  -- 界之下的坐标给出合法的累加 (合法世界里)
  Lg-θK : ∀ x (c : Ctx T (Lv x)) κ g → (∀ d → LgB (g d)) → ∀ {W d} → LgW T W → Bd (Lv x) κ d (pw c W) → LgB (θK x c κ g d)
  Lg-θK lz c () g lg lw b
  Lg-θK (ls x) c (inj₂ _) g lg {W} {d} lw b = New.Lg-θ c g lg d (lgB⊲ b (proj₁ (lgpw c lw)) (proj₂ (lgpw c lw)))
  Lg-θK (ls x) c (inj₁ κ) g lg lw b = Lg-θK x (viaS c) κ g lg lw b
  Lg-θK (ll f) c (n , κ) g lg lw b = Lg-θK (f n) (viaL c n) κ g lg lw b
  Lg-θK (lΩ k h) c (inj₁ _ , inj₂ _) g lg {W} {d} lw b =
    New.Lg-θ (viaL {F = FXL k h} c (inj₁ tt)) g lg d
      (lgB⊲ b (proj₁ (lgpw (viaL {F = FXL k h} c (inj₁ tt)) lw)) (proj₂ (lgpw (viaL {F = FXL k h} c (inj₁ tt)) lw)))
  Lg-θK (lΩ k h) c (inj₁ _ , inj₁ κ) g lg lw b = Lg-θK k (viaS (viaL {F = FXL k h} c (inj₁ tt))) κ g lg lw b
  Lg-θK (lΩ k h) c (inj₂ e , κ) g lg lw b = Lg-θK (h e) (viaL {F = FXL k h} c (inj₂ e)) κ g lg lw b
```

## §4 合法化 `leg` (对一切层号)

```agda
module _ (x : LH) where
  Σᴸ : (ℕ → HB (Lv x)) → ℕ → HB (Lv x)
  Σᴸ f zero = f 0
  Σᴸ f (suc n) = Σᴸ f n ⊞ f (suc n)

  leg : HB (Lv x) → HB (Lv x)
  leg hz = hz
  leg (hs a) = hs (leg a)
  leg (hl f) = hl (Σᴸ (λ n → leg (f n)))
  leg (hΩ κ h) = hΩ κ (θK x here κ (λ e → leg (h e)))

  Lg-leg : ∀ a → LgB (leg a)
  Lg-Σᴸ : ∀ f n → LgB (Σᴸ (λ m → leg (f m)) n)
  Lg-leg hz = tt
  Lg-leg (hs a) = Lg-leg a
  Lg-leg (hl f) = (λ n → ⊞-fst (Σᴸ (λ m → leg (f m)) n) (leg (f (suc n)))) , Lg-Σᴸ f
  Lg-leg (hΩ κ h) =
    (λ lw b b′ p → θK-⊲ x here κ (λ e → leg (h e)) p) ,
    (λ lw b → Lg-θK x here κ (λ e → leg (h e)) (λ e → Lg-leg (h e)) lw b)
  Lg-Σᴸ f zero = Lg-leg (f 0)
  Lg-Σᴸ f (suc n) = Lg-⊞ _ (leg (f (suc n))) (Lg-Σᴸ f n) (Lg-leg (f (suc n)))
```

## §5 世界的自反, 每层的合法世界

```agda
rfL : ∀ x (w : Wd (Lv x)) → _≤w_ (Lv x) w w
rfL lz w = tt
rfL (ls x) w = rfL x (proj₁ w) , hself
rfL (ll f) w = λ n → rfL (f n) (w n)
rfL (lΩ k h) w (inj₁ _) = rfL k (proj₁ (w (inj₁ tt))) , hself
rfL (lΩ k h) w (inj₂ e) = rfL (h e) (w (inj₂ e))

w₀L : ∀ x → Wd (Lv x)
w₀L lz = tt
w₀L (ls x) = w₀L x , hz
w₀L (ll f) = λ n → w₀L (f n)
w₀L (lΩ k h) (inj₁ _) = w₀L k , hz
w₀L (lΩ k h) (inj₂ e) = w₀L (h e)

lw₀L : ∀ x → LgW (Lv x) (w₀L x)
lw₀L lz = tt
lw₀L (ls x) = lw₀L x , tt
lw₀L (ll f) = λ n → lw₀L (f n)
lw₀L (lΩ k h) (inj₁ _) = lw₀L k , tt
lw₀L (lΩ k h) (inj₂ e) = lw₀L (h e)
```

## §6 实例

```agda
AdmK : ∀ k → WL k → HB (Lv k) → Set
AdmK k (u , B) e = Σ (Wd (Lv k)) (λ u′ → _≤w_ (Lv k) u u′ × LgW (Lv k) u′ × (B ⊲[ u′ ] e) × LgB e)

J₁ : LHRecIf
J₁ = record
  { Adm = AdmK
  ; nxt = λ k W e a → proj₁ a , hs e
  ; sh = λ k W c → proj₂ W ⊞ leg k c
  ; adm-sh = λ k {W} c lW → proj₁ W , rfL k (proj₁ W) , proj₁ lW , ⊞-fst (proj₂ W) (leg k c) ,
                           Lg-⊞ (proj₂ W) (leg k c) (proj₂ lW) (Lg-leg k c)
  ; nx-up = λ k a → proj₁ (proj₂ a) , hsuc (proj₁ (proj₂ (proj₂ (proj₂ a))))
  ; lg-nx = λ k a lW → proj₁ (proj₂ (proj₂ a)) , proj₂ (proj₂ (proj₂ (proj₂ a)))
  ; adm↓ = λ k {W} {W′} q {e} a′ →
      (proj₁ a′ , ≤w-tr (Lv k) (proj₁ q) (proj₁ (proj₂ a′)) , proj₁ (proj₂ (proj₂ a′)) ,
        ⊲ᴮ-tr (⊲ᴮ↑ (proj₁ (proj₂ a′)) (proj₂ q)) (proj₁ (proj₂ (proj₂ (proj₂ a′)))) , proj₂ (proj₂ (proj₂ (proj₂ a′)))) ,
      (rfL k (proj₁ a′) , hself)
  ; W₀ = λ k → w₀L k , hs hz
  ; o₀ = λ k → hself
  ; lW₀ = λ k → lw₀L k , tt }
```
