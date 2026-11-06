# 差树上的值关系 (四): 折叠对它单调

> 不含记号. 入口 [DVal](DVal.lagda.md). **定理 `snd`**: 第 1 层差树 $x\sqsubseteq^{\mathsf d}x'$ ([DValTree](DValTree.lagda.md)) 推出折叠 (`SumOneClosed`, $S=\cdot\omega$, 输入层 `cnt one`, 世界 $W$) 在**目标第 0 层**上的输出单调: 对一切满足 `HA₁` 的动作, 一切抬升路径与坐标, 底 $c\le c'$ 且状态值 $\le$, 就有
>
> $$c+\mathrm{out}(x)\ \le\ c'+\mathrm{out}(x').$$
>
> - 目标路径固定为 $\tau_0=$ `inj₁ (⊲-tr (suc self) ll)`. 第 1 层的 `ni` 在世界 $W$ 里上升时读的正是它 (`SumOneFold.kk`), 所以不用对路径全称.
> - 动作 `HA₁`: 状态值 $\le$ 且底 $\le$ ⇒ 一步之后 $\le$; **不读第 1 层坐标**. $\psi_0(\Omega_{\Omega+1})$ 里第 1 层链用的动作 (顶层分支 `n1` 经 `Ai` 归约到 `Step`) 就是这样 (判断, 见 [DValInst](DValInst.lagda.md) 的 `StepV₀`).
> - 世界: 不含 `nκ` 时, 目标第 0 层的折叠不换世界 (`Ai` 在 `n1` 处以 `C.self` 调用), 所以两边在同一个世界 $W$ 里比. 树本身的世界可以不同 (`nw`).
>
> 每个构造子一步. 新用到的字段:
>
> | 构造子 | 用到 | 一步 |
> |---|---|---|
> | `n0⊑`, `n1⊑`, `⨾⊑`, `nl⊑`, `nw*`, `u*` | 和的结构 | 状态值沿 `⊕` 是 `sum` 的左折, 定义性相等 |
> | `as*` | 被重排的一段 $z$ **在两个字面不同、值相同的状态上走** | 要 `Rf z` |
> | `pre⊑`, `lim⊑` | `Rpt` 的状态与前缀 `pre₁` 的状态字面不同, 值相同 | `lim⊑` 要各项 `Rf` |
> | **`ni⊑`** | `RKi` 的 rise: 链 `Chn` 走状态在第 0 层的差 (`DValZero.chain`); 链的动作是 `Ai u` | 三条 `HAᶜ` 由分支的三条前提加归纳给出 |
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.LayerTrOne using (one)
module OCF.Align.DValSound {W : A} (lW : Lg W) (ll : one ⊲ W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (asuc; ss; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst; cnt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.BrwMidZero using (sum₀)
open import OCF.Align.DValTree
import OCF.Align.DValZero

k₀ : azero ⊲ W
k₀ = ⊲-tr (C.suc C.self) ll

module Z = OCF.Align.DValZero lW k₀
open Z using (τ₀; vY; HAᶜ; ac₀; Act)
```

## §1 语义

```agda
ac₁ : F.AccY (cnt one)
ac₁ = F.accCn one

Act₁ : Set
Act₁ = F.Ig (cnt one) W

Ob₁ : Act₁ → A → ∀ {V} → D one V → V ⊲ W → D one W → F.St W → A
Ob₁ A₀ c x q w Y = sum c (F.yc (F.Run ac₁ x q lW ll A₀ w Y) τ₀ tt)

HA₁ : Act₁ → Set
HA₁ A₀ = ∀ w w′ c c′ Y Y′ → c ≤ c′ → vY Y ≤ vY Y′ →
         sum c (F.yc (A₀ C.self lW w Y) τ₀ tt) ≤ sum c′ (F.yc (A₀ C.self lW w′ Y′) τ₀ tt)

OutLe₁ : ∀ {V V′} → D one V → D one V′ → Set
OutLe₁ x x′ = ∀ (A₀ : Act₁) → HA₁ A₀ → ∀ q q′ w w′ c c′ Y Y′ → c ≤ c′ → vY Y ≤ vY Y′ →
              Ob₁ A₀ c x q w Y ≤ Ob₁ A₀ c′ x′ q′ w′ Y′

toV0 : ∀ {V V′} (x : D azero V) (x′ : D azero V′) → sum azero x ≤ sum azero x′ → V0 x ≤ V0 x′
toV0 x x′ le = ≤-trans (proj₂ (sum₀ x)) (≤-trans le (proj₁ (sum₀ x′)))
```

## §2 对每个构造子一步

```agda
snd : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑ᵈ x′ → OutLe₁ x x′
snd n0⊑ A₀ ha q q′ w w′ c c′ Y Y′ cb r = ≤-trans cb (⊲→≤ (sum-fst c′ _))
snd n1⊑ A₀ ha q q′ w w′ c c′ Y Y′ cb r = ha w w′ c c′ Y Y′ cb r
snd (⨾⊑ hx hy) A₀ ha q q′ w w′ c c′ Y Y′ cb r =
  snd hy A₀ ha q q′ _ _ _ _ _ _ (snd hx A₀ ha q q′ w w′ c c′ Y Y′ cb r) (snd hx A₀ ha q q′ w w′ _ _ Y Y′ r r)
snd (nl⊑ {d = d} {d′} h) A₀ ha q q′ w w′ c c′ Y Y′ cb r = l≤ (λ n → ≤l n (proj₁ (go n)))
  where
  P = λ n → F.Rpt ac₁ d q lW ll A₀ w Y n
  P′ = λ n → F.Rpt ac₁ d′ q′ lW ll A₀ w′ Y′ n
  go : ∀ n → (pt c (λ m → F.yc (F.Run ac₁ (d m) q lW ll A₀ (proj₁ (P m)) (proj₂ (P m))) τ₀ tt) n ≤
              pt c′ (λ m → F.yc (F.Run ac₁ (d′ m) q′ lW ll A₀ (proj₁ (P′ m)) (proj₂ (P′ m))) τ₀ tt) n) ×
             (vY (proj₂ (P n)) ≤ vY (proj₂ (P′ n)))
  go zero = cb , r
  go (suc n) = let (gb , gs) = go n in snd (h n) A₀ ha q q′ _ _ _ _ _ _ gb gs , snd (h n) A₀ ha q q′ _ _ _ _ _ _ gs gs
snd (nwˡ {p = p} h) A₀ ha q q′ = snd h A₀ ha (⊲-tr p q) q′
snd (nwʳ {p = p} h) A₀ ha q q′ = snd h A₀ ha q (⊲-tr p q′)
snd (ni⊑ {u = u} {u′} mu mu′ cr) A₀ ha q q′ w w′ c c′ Y Y′ cb r = rs (F.rkT k₀ τ₀ lW) (F.rkT k₀ τ₀ lW)
  where
  A² A²′ : Act
  A² = F.Ai ac₁ (ss C.self) u q k₀ ll A₀ w
  A²′ = F.Ai ac₁ (ss C.self) u′ q′ k₀ ll A₀ w′
  -- 链的动作: 在坐标 z 上走分支 u z. 归纳假设给它的单调
  hx : HAᶜ A² A²′
  hx z z′ e e′ Z′ Z″ le eb er = snd (cr q q′ lW z z′ (toV0 z z′ le)) (F.Ig↾ C.self A₀) ha C.self C.self _ _ e e′ Z′ Z″ eb er
  h0 : HAᶜ A² A²
  h0 z z′ e e′ Z′ Z″ le eb er = snd (mu q q lW z z′ (toV0 z z′ le)) (F.Ig↾ C.self A₀) ha C.self C.self _ _ e e′ Z′ Z″ eb er
  h1 : HAᶜ A²′ A²′
  h1 z z′ e e′ Z′ Z″ le eb er = snd (mu′ q′ q′ lW z z′ (toV0 z z′ le)) (F.Ig↾ C.self A₀) ha C.self C.self _ _ e e′ Z′ Z″ eb er
  -- 目标第 0 层: 节点层 0 不高于目标, 只有 rise
  rs : ∀ (rk rk′ : F.Rk′ azero azero) →
       sum c (F.RKi ac₁ ac₀ (ss C.self) u q lW ll A₀ w Y τ₀ tt rk) ≤ sum c′ (F.RKi ac₁ ac₀ (ss C.self) u′ q′ lW ll A₀ w′ Y′ τ₀ tt rk′)
  rs (F.keep ()) rk′
  rs (F.rise _) (F.keep ())
  rs (F.rise _) (F.rise _) = Z.chain {A²} {A²′} h0 h1 hx Y Y′ c c′ cb r
snd (trˡ h h′) A₀ ha q q″ w w″ c c″ Y Y″ cb r =
  ≤-trans (snd h A₀ ha q q w w c c Y Y (≤-refl c) (≤-refl _)) (snd h′ A₀ ha q q″ w w″ c c″ Y Y″ cb r)
snd (trʳ h h′) A₀ ha q q″ w w″ c c″ Y Y″ cb r =
  ≤-trans (snd h A₀ ha q q″ w w″ c c″ Y Y″ cb r) (snd h′ A₀ ha q″ q″ w″ w″ c″ c″ Y″ Y″ (≤-refl c″) (≤-refl _))
snd (u0ˡ h) A₀ ha q q′ w w′ c c′ Y Y′ cb r = snd h A₀ ha q q′ (w ⨾ nw q n0) w′ c c′ (Y F.⊕ F.zeroD) Y′ cb r
snd (u0ʳ h) A₀ ha q q′ w w′ c c′ Y Y′ cb r = snd h A₀ ha q q′ w (w′ ⨾ nw q′ n0) c c′ Y (Y′ F.⊕ F.zeroD) cb r
snd (u1ˡ h) = snd h
snd (u1ʳ h) = snd h
snd (asˡ {x = x} {y} {z} hz h) A₀ ha q q′ w w′ c c′ Y Y′ cb r =
  ≤-trans (snd hz A₀ ha q q (w ⨾ nw q (x ⨾ y)) ((w ⨾ nw q x) ⨾ nw q y) B B (Y F.⊕ (Rx F.⨾ᴰ Ry)) ((Y F.⊕ Rx) F.⊕ Ry) (≤-refl B) (≤-refl _))
          (snd h A₀ ha q q′ w w′ c c′ Y Y′ cb r)
  where
  Rx = F.Run ac₁ x q lW ll A₀ w Y
  Ry = F.Run ac₁ y q lW ll A₀ (w ⨾ nw q x) (Y F.⊕ Rx)
  B = sum (sum c (F.yc Rx τ₀ tt)) (F.yc Ry τ₀ tt)
snd (asˡ′ {x = x} {y} {z} hz h) A₀ ha q q′ w w′ c c′ Y Y′ cb r =
  ≤-trans (snd hz A₀ ha q q ((w ⨾ nw q x) ⨾ nw q y) (w ⨾ nw q (x ⨾ y)) B B ((Y F.⊕ Rx) F.⊕ Ry) (Y F.⊕ (Rx F.⨾ᴰ Ry)) (≤-refl B) (≤-refl _))
          (snd h A₀ ha q q′ w w′ c c′ Y Y′ cb r)
  where
  Rx = F.Run ac₁ x q lW ll A₀ w Y
  Ry = F.Run ac₁ y q lW ll A₀ (w ⨾ nw q x) (Y F.⊕ Rx)
  B = sum (sum c (F.yc Rx τ₀ tt)) (F.yc Ry τ₀ tt)
snd (asʳ {x = x} {y} {z} hz h) A₀ ha q q′ w w′ c c′ Y Y′ cb r =
  ≤-trans (snd h A₀ ha q q′ w w′ c c′ Y Y′ cb r)
          (snd hz A₀ ha q′ q′ (w′ ⨾ nw q′ (x ⨾ y)) ((w′ ⨾ nw q′ x) ⨾ nw q′ y) B B (Y′ F.⊕ (Rx F.⨾ᴰ Ry)) ((Y′ F.⊕ Rx) F.⊕ Ry) (≤-refl B) (≤-refl _))
  where
  Rx = F.Run ac₁ x q′ lW ll A₀ w′ Y′
  Ry = F.Run ac₁ y q′ lW ll A₀ (w′ ⨾ nw q′ x) (Y′ F.⊕ Rx)
  B = sum (sum c′ (F.yc Rx τ₀ tt)) (F.yc Ry τ₀ tt)
snd (asʳ′ {x = x} {y} {z} hz h) A₀ ha q q′ w w′ c c′ Y Y′ cb r =
  ≤-trans (snd h A₀ ha q q′ w w′ c c′ Y Y′ cb r)
          (snd hz A₀ ha q′ q′ ((w′ ⨾ nw q′ x) ⨾ nw q′ y) (w′ ⨾ nw q′ (x ⨾ y)) B B ((Y′ F.⊕ Rx) F.⊕ Ry) (Y′ F.⊕ (Rx F.⨾ᴰ Ry)) (≤-refl B) (≤-refl _))
  where
  Rx = F.Run ac₁ x q′ lW ll A₀ w′ Y′
  Ry = F.Run ac₁ y q′ lW ll A₀ (w′ ⨾ nw q′ x) (Y′ F.⊕ Rx)
  B = sum (sum c′ (F.yc Rx τ₀ tt)) (F.yc Ry τ₀ tt)
snd (pre⊑ {x = x} {x′} {d} {d′} hx hd k) A₀ ha q q′ w w′ c c′ Y Y′ cb r =
  ≤l k (proj₁ (go k (snd hx A₀ ha q q′ w w′ c c′ Y Y′ cb r) (snd hx A₀ ha q q′ w w′ _ _ Y Y′ r r)))
  where
  go : ∀ k {w₁ w₁′ e e′ Z Z′} → e ≤ e′ → vY Z ≤ vY Z′ →
       (Ob₁ A₀ e (pre₁ d k) q w₁ Z ≤
        pt e′ (λ m → F.yc (F.Run ac₁ (d′ m) q′ lW ll A₀ (proj₁ (F.Rpt ac₁ d′ q′ lW ll A₀ w₁′ Z′ m)) (proj₂ (F.Rpt ac₁ d′ q′ lW ll A₀ w₁′ Z′ m))) τ₀ tt) k) ×
       (vY (Z F.⊕ F.Run ac₁ (pre₁ d k) q lW ll A₀ w₁ Z) ≤ vY (proj₂ (F.Rpt ac₁ d′ q′ lW ll A₀ w₁′ Z′ k)))
  go zero e r′ = e , r′
  go (suc k) e r′ = let (gb , gs) = go k e r′ in
    snd (hd k) A₀ ha q q′ _ _ _ _ _ _ gb gs , snd (hd k) A₀ ha q q′ _ _ _ _ _ _ gs gs
snd (lim⊑ {x = x} {d} hr h) A₀ ha q q′ w w′ c c′ Y Y′ cb r =
  l≤ (λ k → ≤-trans (proj₁ (go k {w ⨾ nw q x} {w ⨾ nw q x} {sum c (F.yc Rx τ₀ tt)} {Y F.⊕ Rx}))
                    (snd (h k) A₀ ha q q′ w w′ c c′ Y Y′ cb r))
  where
  Rx = F.Run ac₁ x q lW ll A₀ w Y
  go : ∀ k {w₁ w₁′ e Z} →
       (pt e (λ m → F.yc (F.Run ac₁ (d m) q lW ll A₀ (proj₁ (F.Rpt ac₁ d q lW ll A₀ w₁ Z m)) (proj₂ (F.Rpt ac₁ d q lW ll A₀ w₁ Z m))) τ₀ tt) k
        ≤ Ob₁ A₀ e (pre₁ d k) q w₁′ Z) ×
       (vY (proj₂ (F.Rpt ac₁ d q lW ll A₀ w₁ Z k)) ≤ vY (Z F.⊕ F.Run ac₁ (pre₁ d k) q lW ll A₀ w₁′ Z))
  go zero = ≤-refl _ , ≤-refl _
  go (suc k) = let (gb , gs) = go k in
    snd (hr k) A₀ ha q q _ _ _ _ _ _ gb gs , snd (hr k) A₀ ha q q _ _ _ _ _ _ gs gs
```

## §3 推论

自比的树对值相同的状态给出值相同的输出 (不看状态的字面, 不看坐标).

```agda
Rf-sound : ∀ {V} {x : D one V} → Rf x → ∀ (A₀ : Act₁) → HA₁ A₀ → ∀ q w w′ c Y Y′ → vY Y ≤ vY Y′ → vY Y′ ≤ vY Y →
           (Ob₁ A₀ c x q w Y ≤ Ob₁ A₀ c x q w′ Y′) × (Ob₁ A₀ c x q w′ Y′ ≤ Ob₁ A₀ c x q w Y)
Rf-sound h A₀ ha q w w′ c Y Y′ r r′ = snd h A₀ ha q q w w′ c c Y Y′ (≤-refl c) r , snd h A₀ ha q q w′ w c c Y′ Y (≤-refl c) r′
```
