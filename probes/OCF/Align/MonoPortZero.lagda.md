# 单调的移植 (二): 高度树折叠的第 0 层, 值同余与链

> 不含记号. 入口 [MonoPort](MonoPort.lagda.md). [DValZero](DValZero.lagda.md) 在高度树主线 (`HtFeedFold`) 上的同形物. **对一切实例** $\Lambda$, 一切一步 $S$, 一切世界 $W$ 与第 0 层到 $\Lambda$ 的路径 `hk`: 第 0 层输入 (`D hz`) 折叠后在第 0 层目标 $T_0=$ `tg self hk lW` 上的读数
>
> - 对输入的**值**单调, 两边动作可以不同 (`cong0`, 前提是动作的三条 `HAᶜ`);
> - 链 (`Chn`, 节点在第 0 层目标上上升时走的那条) 的读数对起点单调: 底 $\le$, 状态在 $T_0$ 上的值 $\le$ ⇒ 链的极限 $\le$ (`chain`).
>
> 与 `DValZero` 的差别只有三处: 折叠换成 `HtFeedFold S Λ lΛ`, 目标是一个高度目标 $T_0$, 树的值直接用 `sum azero` (`val`), 不经 `toA`. 规范形那一段**不重写**: 关系经 [MonoPortBridge](MonoPortBridge.lagda.md) 的翻译 `ofS` 拉回到 `SumOneTree.D azero` 上, 原样套 `DValCanon.Gen` (§3).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (D₊; H; LgH; hz; _⊲[_]_; AccY)
module OCF.Align.MonoPortZero
  (S : ∀ {Kd : A → H → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W)
  (Λ : H) (lΛ : LgH Λ) {W : A} (lW : Lg W) (hk : hz ⊲[ W ] Λ) (ac₀ : AccY hz) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.CumReadCF using (asuc; alim; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst)
import OCF.Align.HtFeedFold as Fold
import OCF.Align.SumOneTree as SO
import OCF.Align.DValCanon as DC
open import OCF.Align.MonoPortBridge using (toS; ofS; preH; ofS-pre; val; toV; smono)

module F = Fold S Λ lΛ
```

## §1 值, 动作, 关系

```agda
T₀ : F.Tg W hz W
T₀ = F.tg C.self hk lW

Act : Set
Act = F.Ig hz W

vY : F.St W → A
vY Y = sum azero (F.yc (F.d Y) T₀)

Rn : Act → ∀ {W₀} → D hz W₀ → W₀ ⊲ W → D hz W → F.St W → F.Df W
Rn A₀ z q w Y = F.Run ac₀ z q lW hk A₀ w Y

-- 从底 c 起, 在状态 Y 里走 z, 目标 T₀ 上的读数
Ob : Act → A → ∀ {W₀} → D hz W₀ → W₀ ⊲ W → D hz W → F.St W → A
Ob A₀ c z q w Y = sum c (F.yc (Rn A₀ z q w Y) T₀)

HAᶜ : Act → Act → Set
HAᶜ A₀ A₁ = ∀ w w′ c c′ Y Y′ → val w ≤ val w′ → c ≤ c′ → vY Y ≤ vY Y′ →
            sum c (F.yc (A₀ C.self lW w Y) T₀) ≤ sum c′ (F.yc (A₁ C.self lW w′ Y′) T₀)

OutLe : Act → Act → ∀ {V₁ V₂} → D hz V₁ → D hz V₂ → Set
OutLe A₀ A₁ z z′ = ∀ q q′ w w′ c c′ Y Y′ → val w ≤ val w′ → c ≤ c′ → vY Y ≤ vY Y′ → Ob A₀ c z q w Y ≤ Ob A₁ c′ z′ q′ w′ Y′

Rl : Act → Act → ∀ {V₁ V₂} → D hz V₁ → D hz V₂ → Set
Rl A₀ A₁ z z′ = OutLe A₀ A₁ z z′ × (val z ≤ val z′)

ptV : ∀ {V₁ V₂} {b b′} (d : ℕ → D hz V₁) (d′ : ℕ → D hz V₂) → b ≤ b′ → (∀ n → val (d n) ≤ val (d′ n)) → ∀ k → pt b d k ≤ pt b′ d′ k
ptV d d′ hb h zero = hb
ptV d d′ hb h (suc k) = smono (ptV d d′ hb h k) (h k)

preV : ∀ {V₁ V₂} {b b′} (d : ℕ → D hz V₁) (d′ : ℕ → D hz V₂) → b ≤ b′ → (∀ n → val (d n) ≤ val (d′ n)) → ∀ k → sum b (preH d k) ≤ pt b′ d′ k
preV d d′ hb h zero = hb
preV {b = b} d d′ hb h (suc k) = smono {b = sum b (preH d k)} {x = d k} (preV d d′ hb h k) (h k)

preV′ : ∀ {V₁ V₂} {b b′} (d : ℕ → D hz V₁) (d′ : ℕ → D hz V₂) → b ≤ b′ → (∀ n → val (d n) ≤ val (d′ n)) → ∀ k → pt b d k ≤ sum b′ (preH d′ k)
preV′ d d′ hb h zero = hb
preV′ {b′ = b′} d d′ hb h (suc k) = smono {b′ = sum b′ (preH d′ k)} {x′ = d′ k} (preV′ d d′ hb h k) (h k)
```

## §2 结构律

逐条照 `DValZero` §2: 状态沿 `⊕` 的值是 `sum` 的左折, 上下文沿 `⨾ nw` 也是, 都是定义性的.

```agda
module _ {A₀ A₁ : Act} where
  ⨾-mono : ∀ {V₁ V₂} {x y : D hz V₁} {x′ y′ : D hz V₂} → Rl A₀ A₁ x x′ → Rl A₀ A₁ y y′ → Rl A₀ A₁ (x ⨾ y) (x′ ⨾ y′)
  ⨾-mono (hx , ax) (hy , ay) =
    (λ q q′ w w′ b b′ Y Y′ c cb r → hy q q′ _ _ _ _ _ _ (smono c ax) (hx q q′ w w′ b b′ Y Y′ c cb r) (hx q q′ w w′ _ _ Y Y′ c r r)) ,
    smono ax ay

  nl-mono : ∀ {V₁ V₂} {d : ℕ → D hz V₁} {d′ : ℕ → D hz V₂} → (∀ n → Rl A₀ A₁ (d n) (d′ n)) → Rl A₀ A₁ (nl d) (nl d′)
  nl-mono {d = d} {d′} h = O , l≤ (λ n → ≤l n (ptV d d′ z≤ (λ m → proj₂ (h m)) n))
    where
    O : OutLe A₀ A₁ (nl d) (nl d′)
    O q q′ w w′ b b′ Y Y′ c cb r = l≤ (λ n → ≤l n (proj₁ (proj₂ (go n))))
      where
      P = λ n → F.Rpt ac₀ d q lW hk A₀ w Y n
      P′ = λ n → F.Rpt ac₀ d′ q′ lW hk A₁ w′ Y′ n
      go : ∀ n → (val (proj₁ (P n)) ≤ val (proj₁ (P′ n))) ×
                 ((pt b (λ m → F.yc (Rn A₀ (d m) q (proj₁ (P m)) (proj₂ (P m))) T₀) n ≤
                   pt b′ (λ m → F.yc (Rn A₁ (d′ m) q′ (proj₁ (P′ m)) (proj₂ (P′ m))) T₀) n) ×
                  (vY (proj₂ (P n)) ≤ vY (proj₂ (P′ n))))
      go zero = c , (cb , r)
      go (suc n) = let (gc , (gb , gs)) = go n in
        smono gc (proj₂ (h n)) , (proj₁ (h n) q q′ _ _ _ _ _ _ gc gb gs , proj₁ (h n) q q′ _ _ _ _ _ _ gc gs gs)

  nw-l : ∀ {V₀ V V₂} {p : V₀ ⊲ V} {x : D hz V₀} {z : D hz V₂} → Rl A₀ A₁ x z → Rl A₀ A₁ (nw p x) z
  nw-l {p = p} (h , a) = (λ q q′ w w′ b b′ Y Y′ c cb r → h (⊲-tr p q) q′ w w′ b b′ Y Y′ c cb r) , a

  nw-r : ∀ {V₀ V V₁} {p : V₀ ⊲ V} {x : D hz V₀} {z : D hz V₁} → Rl A₀ A₁ z x → Rl A₀ A₁ z (nw p x)
  nw-r {p = p} (h , a) = (λ q q′ w w′ b b′ Y Y′ c cb r → h q (⊲-tr p q′) w w′ b b′ Y Y′ c cb r) , a

  n1⊑ : HAᶜ A₀ A₁ → ∀ {V₁ V₂} → Rl A₀ A₁ (n1 {W = V₁}) (n1 {W = V₂})
  n1⊑ ha = (λ q q′ w w′ b b′ Y Y′ c cb r → ha w w′ b b′ Y Y′ c cb r) , ≤-refl _

  infl : ∀ {V₁ V₂} (z : D hz V₂) → Rl A₀ A₁ (n0 {W = V₁}) z
  infl z = (λ q q′ w w′ b b′ Y Y′ c cb r → ≤-trans cb (⊲→≤ (sum-fst b′ (F.yc (Rn A₁ z q′ w′ Y′) T₀)))) , z≤

  refl⊑ : HAᶜ A₀ A₁ → ∀ {V} (z : D hz V) → Rl A₀ A₁ z z
  refl⊑ ha n0 = infl n0
  refl⊑ ha n1 = n1⊑ ha
  refl⊑ ha (x ⨾ y) = ⨾-mono (refl⊑ ha x) (refl⊑ ha y)
  refl⊑ ha (nl d) = nl-mono (λ n → refl⊑ ha (d n))
  refl⊑ ha (ni () u)
  refl⊑ ha (nκ () u)
  refl⊑ ha (nw p x) = nw-l (nw-r (refl⊑ ha x))

  pre-le : ∀ {V₁ V₂} (x : D hz V₁) (x′ : D hz V₂) (d : ℕ → D hz V₁) (d′ : ℕ → D hz V₂) →
           Rl A₀ A₁ x x′ → (∀ n → Rl A₀ A₁ (d n) (d′ n)) → ∀ k → Rl A₀ A₁ (x ⨾ preH d k) (x′ ⨾ nl d′)
  pre-le x x′ d d′ hx hd k =
    (λ q q′ w w′ b b′ Y Y′ c cb r →
      ≤l k (proj₁ (proj₂ (go q q′ k (smono c (proj₂ hx)) (proj₁ hx q q′ w w′ b b′ Y Y′ c cb r) (proj₁ hx q q′ w w′ _ _ Y Y′ c r r))))) ,
    ≤l k (preV d d′ (proj₂ hx) (λ m → proj₂ (hd m)) k)
    where
    go : ∀ q q′ k {w₁ w₁′ e e′ Z Z′} → val w₁ ≤ val w₁′ → e ≤ e′ → vY Z ≤ vY Z′ →
         (val (w₁ ⨾ nw q (preH d k)) ≤ val (proj₁ (F.Rpt ac₀ d′ q′ lW hk A₁ w₁′ Z′ k))) ×
         ((Ob A₀ e (preH d k) q w₁ Z ≤
           pt e′ (λ m → F.yc (Rn A₁ (d′ m) q′ (proj₁ (F.Rpt ac₀ d′ q′ lW hk A₁ w₁′ Z′ m)) (proj₂ (F.Rpt ac₀ d′ q′ lW hk A₁ w₁′ Z′ m))) T₀) k) ×
          (vY (F._⊕⟨_⟩_ Z lW (Rn A₀ (preH d k) q w₁ Z)) ≤ vY (proj₂ (F.Rpt ac₀ d′ q′ lW hk A₁ w₁′ Z′ k))))
    go q q′ zero c′ e r′ = c′ , (e , r′)
    go q q′ (suc k) c′ e r′ = let (gc , (gb , gs)) = go q q′ k c′ e r′ in
      smono gc (proj₂ (hd k)) , (proj₁ (hd k) q q′ _ _ _ _ _ _ gc gb gs , proj₁ (hd k) q q′ _ _ _ _ _ _ gc gs gs)

module _ {A₀ : Act} (ha : HAᶜ A₀ A₀) where
  private rf = refl⊑ {A₀} {A₀} ha

  unit-l : ∀ {V} (x : D hz V) → Rl A₀ A₀ (n0 ⨾ x) x × Rl A₀ A₀ x (n0 ⨾ x)
  unit-l x = ((λ q q′ w w′ b b′ Y Y′ c cb r → proj₁ (rf x) q q′ _ w′ _ b′ _ Y′ c cb r) , ≤-refl _) ,
             ((λ q q′ w w′ b b′ Y Y′ c cb r → proj₁ (rf x) q q′ w _ b _ Y _ c cb r) , ≤-refl _)

  unit-r : ∀ {V} (x : D hz V) → Rl A₀ A₀ (x ⨾ n0) x × Rl A₀ A₀ x (x ⨾ n0)
  unit-r x = (proj₁ (rf x) , ≤-refl _) , (proj₁ (rf x) , ≤-refl _)

  assoc : ∀ {V} (x y z : D hz V) → Rl A₀ A₀ ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z)) × Rl A₀ A₀ (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
  assoc x y z = (A1 , ≤-refl _) , (A1′ , ≤-refl _)
    where
    A1 : OutLe A₀ A₀ ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z))
    A1 q q′ w w′ b b′ Y Y′ c cb r =
      proj₁ (rf z) q q′ _ _ _ _ _ _ (smono (smono c (≤-refl (val x))) (≤-refl (val y)))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (smono c (≤-refl (val x))) (proj₁ (rf x) q q′ w w′ b b′ Y Y′ c cb r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (smono c (≤-refl (val x))) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r))
    A1′ : OutLe A₀ A₀ (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
    A1′ q q′ w w′ b b′ Y Y′ c cb r =
      proj₁ (rf z) q q′ _ _ _ _ _ _ (smono (smono c (≤-refl (val x))) (≤-refl (val y)))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (smono c (≤-refl (val x))) (proj₁ (rf x) q q′ w w′ b b′ Y Y′ c cb r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (smono c (≤-refl (val x))) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r))

module _ {A₀ A₁ : Act} where
  lim-leP : HAᶜ A₀ A₀ → ∀ {V₁ V₂} (x : D hz V₁) (d : ℕ → D hz V₁) (z : D hz V₂) →
            (∀ k → Rl A₀ A₁ (x ⨾ preH d k) z) → Rl A₀ A₁ (x ⨾ nl d) z
  lim-leP ha x d z h =
    (λ q q′ w w′ b b′ Y Y′ c cb r →
      l≤ (λ k → ≤-trans (proj₁ (proj₂ (go q k))) (proj₁ (h k) q q′ w w′ b b′ Y Y′ c cb r))) ,
    l≤ (λ k → ≤-trans (preV′ d d (≤-refl (val x)) (λ m → ≤-refl _) k) (proj₂ (h k)))
    where
    go : ∀ q k {w₁ e Z} → (val (proj₁ (F.Rpt ac₀ d q lW hk A₀ w₁ Z k)) ≤ val (w₁ ⨾ nw q (preH d k))) ×
                          ((pt e (λ m → F.yc (Rn A₀ (d m) q (proj₁ (F.Rpt ac₀ d q lW hk A₀ w₁ Z m)) (proj₂ (F.Rpt ac₀ d q lW hk A₀ w₁ Z m))) T₀) k
                            ≤ Ob A₀ e (preH d k) q w₁ Z) ×
                           (vY (proj₂ (F.Rpt ac₀ d q lW hk A₀ w₁ Z k)) ≤ vY (F._⊕⟨_⟩_ Z lW (Rn A₀ (preH d k) q w₁ Z))))
    go q zero = ≤-refl _ , (≤-refl _ , ≤-refl _)
    go q (suc k) = let (gc , (gb , gs)) = go q k in
      smono gc (≤-refl (val (d k))) , (proj₁ (refl⊑ {A₀} {A₀} ha (d k)) q q _ _ _ _ _ _ gc gb gs , proj₁ (refl⊑ {A₀} {A₀} ha (d k)) q q _ _ _ _ _ _ gc gs gs)

  tr⊑ : ∀ {V V₃} {z z′ : D hz V} {z″ : D hz V₃} → Rl A₀ A₀ z z′ → Rl A₀ A₁ z′ z″ → Rl A₀ A₁ z z″
  tr⊑ (h , a) (h′ , a′) =
    (λ q q″ w w″ b b″ Y Y″ c cb r → ≤-trans (h q q w w b b Y Y (≤-refl _) (≤-refl _) (≤-refl _)) (h′ q q″ w w″ b b″ Y Y″ c cb r)) , ≤-trans a a′

  tr⊑ʳ : ∀ {V V₁} {z : D hz V₁} {z′ z″ : D hz V} → Rl A₀ A₁ z z′ → Rl A₁ A₁ z′ z″ → Rl A₀ A₁ z z″
  tr⊑ʳ (h , a) (h′ , a′) =
    (λ q q″ w w″ b b″ Y Y″ c cb r → ≤-trans (h q q″ w w″ b b″ Y Y″ c cb r) (h′ q″ q″ w″ w″ b″ b″ Y″ Y″ (≤-refl _) (≤-refl _) (≤-refl _))) , ≤-trans a a′
```

## §3 规范形: 拉回 `SumOneTree`, 套 `Gen`

`Rˢ i j z z′`: 两棵 `SumOneTree.D azero` 树翻译成高度树的第 0 层树之后相关. 结构律都由 §2 给出 (翻译与构造子定义性交换; 部分和用 `ofS-pre` 搬一次). `Gen` 的结论是 `SumOne` 一侧的; 回到高度树一侧要往返 `ofS (toS z)` 与 $z$ 相关 (`rt`, 对 $z$ 归纳, 用 §2 的同余).

```agda
Rˢ : Act → Act → ∀ {V₁ V₂} → SO.D azero V₁ → SO.D azero V₂ → Set
Rˢ A₀ A₁ z z′ = Rl A₀ A₁ (ofS z) (ofS z′)

private
  module GG = DC.Gen HAᶜ Rˢ
    (λ {i} {j} h → n1⊑ {i} {j} h) (λ {i} {j} z → infl {i} {j} (ofS z))
    (λ {i} {j} → ⨾-mono {i} {j}) (λ {i} {j} h → nl-mono {i} {j} h) (λ {i} {j} → nw-l {i} {j}) (λ {i} {j} → nw-r {i} {j})
    (λ {i} {j} → tr⊑ {i} {j}) (λ {i} {j} → tr⊑ʳ {i} {j})
    (λ {i} h x → unit-l {i} h (ofS x)) (λ {i} h x → unit-r {i} h (ofS x)) (λ {i} h x y z → assoc {i} h (ofS x) (ofS y) (ofS z))
    (λ {i} {j} x x′ d d′ hx hd k →
       subst (λ t → Rl i j (ofS x ⨾ t) (ofS x′ ⨾ nl (λ n → ofS (d′ n)))) (sym (ofS-pre d k))
             (pre-le {i} {j} (ofS x) (ofS x′) (λ n → ofS (d n)) (λ n → ofS (d′ n)) hx hd k))
    (λ {i} {j} h x d z hk′ →
       lim-leP {i} {j} h (ofS x) (λ n → ofS (d n)) (ofS z)
         (λ k → subst (λ t → Rl i j (ofS x ⨾ t) (ofS z)) (ofS-pre d k) (hk′ k)))

-- 往返
rt  : ∀ {A₀ : Act} → HAᶜ A₀ A₀ → ∀ {V} (z : D hz V) → Rl A₀ A₀ z (ofS (toS z))
rt′ : ∀ {A₀ : Act} → HAᶜ A₀ A₀ → ∀ {V} (z : D hz V) → Rl A₀ A₀ (ofS (toS z)) z
rt ha n0 = infl n0
rt ha n1 = n1⊑ ha
rt ha (x ⨾ y) = ⨾-mono (rt ha x) (rt ha y)
rt ha (nl d) = nl-mono (λ n → rt ha (d n))
rt ha (ni () u)
rt ha (nκ () u)
rt ha (nw p x) = nw-l (nw-r (rt ha x))
rt′ ha n0 = infl n0
rt′ ha n1 = n1⊑ ha
rt′ ha (x ⨾ y) = ⨾-mono (rt′ ha x) (rt′ ha y)
rt′ ha (nl d) = nl-mono (λ n → rt′ ha (d n))
rt′ ha (ni () u)
rt′ ha (nκ () u)
rt′ ha (nw p x) = nw-l (nw-r (rt′ ha x))

-- 值同余: 第 0 层值 ≤ 则走起来 ≤, 两边动作可以不同
cong0 : ∀ {A₀ A₁ : Act} → HAᶜ A₀ A₀ → HAᶜ A₁ A₁ → HAᶜ A₀ A₁ →
        ∀ {W₀ W₀′} (z : D hz W₀) (z′ : D hz W₀′) → val z ≤ val z′ → Rl A₀ A₁ z z′
cong0 {A₀} {A₁} ha ha′ hx z z′ le =
  tr⊑ (rt ha z) (tr⊑ʳ (GG.Two.cong0 {A₀} {A₁} ha ha′ hx (toS z) (toS z′) (toV z z′ le)) (rt′ ha′ z′))
```

## §4 链

`Chn` 从状态在 $T_0$ 上的差 $\delta_0$ 出发, 每一段沿链点 $\delta_n$ 走, 上下文接上 $\delta_n$, 下一个链点是这一段在 $T_0$ 上的输出. 不变量四件: 上下文值, 链点值, 状态值, 部分和. 每一步用一次 `cong0`. 与 `DValZero.chain` 逐行相同.

```agda
module _ {A₀ A₁ : Act} (ha : HAᶜ A₀ A₀) (ha′ : HAᶜ A₁ A₁) (hx : HAᶜ A₀ A₁) where
  CC : Act → F.St W → ℕ → D hz W × (D hz W × F.St W)
  CC A Y = F.Chn ac₀ hk lW A Y

  segs : Act → F.St W → ℕ → D hz W
  segs A Y n = F.yc (Rn A (proj₁ (proj₂ (CC A Y n))) C.self (proj₁ (CC A Y n)) (proj₂ (proj₂ (CC A Y n)))) T₀

  chain : ∀ (Y Y′ : F.St W) b b′ → b ≤ b′ → vY Y ≤ vY Y′ → sum b (nl (segs A₀ Y)) ≤ sum b′ (nl (segs A₁ Y′))
  chain Y Y′ b b′ cb r = l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (go n)))))
    where
    c  = λ n → proj₁ (CC A₀ Y n)
    c′ = λ n → proj₁ (CC A₁ Y′ n)
    δ  = λ n → proj₁ (proj₂ (CC A₀ Y n))
    δ′ = λ n → proj₁ (proj₂ (CC A₁ Y′ n))
    Yn  = λ n → proj₂ (proj₂ (CC A₀ Y n))
    Yn′ = λ n → proj₂ (proj₂ (CC A₁ Y′ n))
    go : ∀ n → (val (c n) ≤ val (c′ n)) × ((val (δ n) ≤ val (δ′ n)) × ((vY (Yn n) ≤ vY (Yn′ n)) × (pt b (segs A₀ Y) n ≤ pt b′ (segs A₁ Y′) n)))
    go zero = z≤ , (r , (r , cb))
    go (suc n) =
      let (gc , (gd , (gs , gb))) = go n
          h = proj₁ (cong0 {A₀} {A₁} ha ha′ hx (δ n) (δ′ n) gd)
      in smono gc gd ,
         (h C.self C.self (c n) (c′ n) azero azero (Yn n) (Yn′ n) gc z≤ gs ,
          (h C.self C.self (c n) (c′ n) _ _ (Yn n) (Yn′ n) gc gs gs ,
           h C.self C.self (c n) (c′ n) _ _ (Yn n) (Yn′ n) gc gb gs))
```
