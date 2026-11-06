# 可数层的对角, 第三轮 (二): 只增长的世界, 增量到第二数类为止

> 不含记号. 入口 [DiagK3](DiagK3.lagda.md). 选项 (ii) 要的世界操作: 回灌时不挑出哪个分量, **一切分量都接上同一个增量**, 世界只长不缩. [CohW2Grow](CohW2Grow.lagda.md) 在 `SL⋆` 上对可数增量做了这件事 (`growA`). 这里在 `towerL′` 的世界上做, 增量放宽一档: 一个 `A` 增量 (经 $f$, 同 `DiagK2Raise.mapA`) 与一个**第二数类的高度** $h:H_0$ (可以含 $\Omega$-节点, 只用底种类).
>
> - **`embL`** (定义): $H_0$ 进一切 `HB (Lev x)`, 只用 `up` 与 `ι` (对 $x$ 递归, 不判定). `embL hz` 字面上是恒等 (`Lev hz = S₀`).
> - **`growW`, `grow-≤`, `lg-grow`** (定理): `Lev x` 的世界里每个 `A` 界变成 $f$(旧界), 每个高度界 $b$ 变成 $b\boxplus$ `embL` $h$; 是世界的变大, 保合法, 对一切 $x$.
> - **`growL′`, `growL′-≤`, `lg-growL′`** (定理): 同样的操作在 `L′ k` 的整个世界上, 对一切 $k$ (链分量的高度界经 `embK`).
> - **恰好的位置** (定理, `refl`): `L′ 1` 的 `κH` 界变成 $\beta\boxplus h$ (`at-κH`); `Lev (Ωtop S₀)` 在坐标 `hs hz` 处的新种类 (坐标类型就是 $H_0$, `E-hs`) 的界变成 $b\boxplus h$ (`at-lev`). 这两处的回灌增量正是第 1 层的读回 (`HtTowerFRead.rd` 的值在 $H_0$ 里), 所以对坐标是 $H_0$ 的种类, 只增长的世界给出**忠实的**回灌世界, 不判定任何东西.
>
> **范围 (判断).** 坐标是 `HB (Lev x)`, $x$ 不是 `hz` 的种类, 回灌的增量应当是更高层的读回, 含底种类以外的 $\Omega$-节点; 这些种类不在一切分量里 (坐标 `hz` 处只有 `S₀`), 所以 "同一个增量进一切分量" 只能把它压成 $H_0$ 那一档, 有损. 有损的部分见入口第 3 条.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagK3Grow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNStage using (L′; two)

H₀ : Set
H₀ = HB S₀
```

## §1 第二数类进一切 `Lev x`

```agda
embL : ∀ {S} (x : HB S) → H₀ → HB (Lev x)
embL hz h = h
embL (hs x) h = up (embL x h)
embL (hl f) h = ι {F = λ n → Lev (f n)} 0 (embL (f 0) h)
embL {S} (hΩ κ g) h = ι {F = λ c → Lev (g c)} (bot S κ) (embL (g (bot S κ)) h)

Lg-embL : ∀ {S} (x : HB S) h → LgB h → LgB (embL x h)
Lg-embL hz h l = l
Lg-embL (hs x) h l = Lg-up (embL x h) (Lg-embL x h l)
Lg-embL (hl f) h l = Lg-ι {F = λ n → Lev (f n)} 0 (embL (f 0) h) (Lg-embL (f 0) h l)
Lg-embL {S} (hΩ κ g) h l = Lg-ι {F = λ c → Lev (g c)} (bot S κ) (embL (g (bot S κ)) h) (Lg-embL (g (bot S κ)) h l)
```

## §2 `Lev x` 的世界: 一切分量接同一个增量

```agda
module _ (f : A → A) (ffst : ∀ a → a ⊲ f a) (flg : ∀ a → Lg a → Lg (f a)) (h : H₀) (lh : LgB h) where
  growW : ∀ {S} (x : HB S) → Wd (Lev x) → Wd (Lev x)
  growW hz a = f a
  growW (hs x) (w , b) = growW x w , b ⊞ embL x h
  growW (hl g) w = λ n → growW (g n) (w n)
  growW (hΩ κ g) w = λ c → growW (g c) (w c)

  grow-≤ : ∀ {S} (x : HB S) w → _≤w_ (Lev x) w (growW x w)
  grow-≤ hz a = ffst a
  grow-≤ (hs x) (w , b) = grow-≤ x w , ⊞-fst b (embL x h)
  grow-≤ (hl g) w = λ n → grow-≤ (g n) (w n)
  grow-≤ (hΩ κ g) w = λ c → grow-≤ (g c) (w c)

  lg-grow : ∀ {S} (x : HB S) w → LgW (Lev x) w → LgW (Lev x) (growW x w)
  lg-grow hz a l = flg a l
  lg-grow (hs x) (w , b) (lw , lb) = lg-grow x w lw , Lg-⊞ b (embL x h) lb (Lg-embL x h lh)
  lg-grow (hl g) w l = λ n → lg-grow (g n) (w n) (l n)
  lg-grow (hΩ κ g) w l = λ c → lg-grow (g c) (w c) (l c)
```

## §3 `L′ k` 的整个世界, 一切 $k$

```agda
  embK : ∀ k → H₀ → HB (L′ k)
  embK zero x = x
  embK (suc k) x = ι {F = two (step (L′ k)) (Lev (Ωtop (L′ k)))} true (up (embK k x))

  Lg-embK : ∀ k x → LgB x → LgB (embK k x)
  Lg-embK zero x l = l
  Lg-embK (suc k) x l =
    Lg-ι {F = two (step (L′ k)) (Lev (Ωtop (L′ k)))} true (up (embK k x)) (Lg-up (embK k x) (Lg-embK k x l))

  growL′ : ∀ k → Wd (L′ k) → Wd (L′ k)
  growL′ zero a = f a
  growL′ (suc k) w true = growL′ k (proj₁ (w true)) , proj₂ (w true) ⊞ embK k h
  growL′ (suc k) w false = growW (Ωtop (L′ k)) (w false)

  growL′-≤ : ∀ k w → _≤w_ (L′ k) w (growL′ k w)
  growL′-≤ zero a = ffst a
  growL′-≤ (suc k) w true = growL′-≤ k (proj₁ (w true)) , ⊞-fst (proj₂ (w true)) (embK k h)
  growL′-≤ (suc k) w false = grow-≤ (Ωtop (L′ k)) (w false)

  lg-growL′ : ∀ k w → LgW (L′ k) w → LgW (L′ k) (growL′ k w)
  lg-growL′ zero a l = flg a l
  lg-growL′ (suc k) w l true =
    lg-growL′ k (proj₁ (w true)) (proj₁ (l true)) , Lg-⊞ (proj₂ (w true)) (embK k h) (proj₂ (l true)) (Lg-embK k h lh)
  lg-growL′ (suc k) w l false = lg-grow (Ωtop (L′ k)) (w false) (l false)
```

## §4 恰好的位置

```agda
  -- L′ 1 的 κH 界: β ⊞ h
  at-κH : ∀ (w : Wd (L′ 1)) → proj₂ (growL′ 1 w true) ≡ (proj₂ (w true) ⊞ h)
  at-κH w = refl

  -- Lev (Ωtop S₀) 在坐标 hs hz 处: 新种类的界 b ⊞ h
  at-lev : ∀ (w : Wd (L′ 1)) → proj₂ (growL′ 1 w false (hs hz)) ≡ (proj₂ (w false (hs hz)) ⊞ h)
  at-lev w = refl

  -- 底种类 (A) 的界: f(旧界)
  at-A : ∀ (w : Wd (L′ 1)) → proj₁ (growL′ 1 w true) ≡ f (proj₁ (w true))
  at-A w = refl

-- 那个新种类的坐标类型就是 H₀
E-hs : E (L′ 1) (false , (hs hz , inj₂ tt)) ≡ H₀
E-hs = refl
```
