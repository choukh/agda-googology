# 差树上的值关系 (二): 目标第 0 层, 第 0 层输入, 两边动作不同

> 不含记号. 入口 [DVal](DVal.lagda.md). 对象是 `SumOneClosed` 的折叠 `Run` 在**目标第 0 层**上的输出, 输入是第 0 层差树 (这正是第 1 层树里 `ni` 节点在目标第 0 层上升时, 链 `Chn` 每一段走的东西, `SumOneFold.RKi` 的 rise).
>
> 与 [CvLayerRun](CvLayerRun.lagda.md) 的差别:
>
> - 目标是第 0 层: 值在 `A` 里, 用 `sum` 与 $\le$, 不用 `B₁`, `S`, $\preccurlyeq$. 目标的路径固定为 $\tau_0=$ `inj₁ k₀` (模块参数); 第 1 层的 `ni` 在世界 $W$ 里读的正是这条路径 (`DValSound`).
> - **两边的动作可以不同**: `OutLe A A′ z z′`. 第 1 层的 `ni u` 对 `ni u′` 时, 两边的链分别用 `Ai u`, `Ai u′` 作动作.
> - 前提 `HAᶜ A A′`: 坐标的值 $\le$, 底 $\le$, 状态在 $\tau_0$ 上的值 $\le$ ⇒ 左边动作一步加在底上 $\le$ 右边的. `cong0` 要三条: `HAᶜ A A`, `HAᶜ A′ A′`, `HAᶜ A A′`.
> - 规范形那一段不重写, 套 [DValCanon](DValCanon.lagda.md) 的 `Gen`.
>
> 末尾 §4 是链: 两边的链点从值可比的状态出发, 动作满足上面三条, 则链的输出 (`RKi` rise 的那个 `nl`) 可比 (`chain`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.DValZero {W : A} (lW : Lg W) (k₀ : azero ⊲ W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (asuc; alim; z⊲; ⊲-tr; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; _⊞_; ⊞-mono; ⊞-asso; ⊞-assoʳ)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst; cnt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.BrwMidZero using (toA; sum₀; sum-toA; z⊞; pts)
open import OCF.Align.DValCanon using (pre; module Gen)
```

## §1 值, 动作, 关系

```agda
τ₀ : Tg azero W
τ₀ = inj₁ k₀

ac₀ : F.AccY (cnt azero)
ac₀ = F.accCn azero

Act : Set
Act = F.Ig (cnt azero) W

val : ∀ {V} → D azero V → A
val w = sum azero w

V0 : ∀ {V} → D azero V → A
V0 z = proj₁ (toA z)

vY : F.St W → A
vY Y = sum azero (F.yc (F.d Y) τ₀ tt)

Rn : Act → ∀ {W₀} → D azero W₀ → W₀ ⊲ W → D azero W → F.St W → F.Df W
Rn A₀ z q w Y = F.Run ac₀ z q lW k₀ A₀ w Y

-- 从底 c 起, 加上状态 Y 走 z 之后目标第 0 层的差
Ob : Act → A → ∀ {W₀} → D azero W₀ → W₀ ⊲ W → D azero W → F.St W → A
Ob A₀ c z q w Y = sum c (F.yc (Rn A₀ z q w Y) τ₀ tt)

HAᶜ : Act → Act → Set
HAᶜ A₀ A₁ = ∀ w w′ c c′ Y Y′ → val w ≤ val w′ → c ≤ c′ → vY Y ≤ vY Y′ →
            sum c (F.yc (A₀ C.self lW w Y) τ₀ tt) ≤ sum c′ (F.yc (A₁ C.self lW w′ Y′) τ₀ tt)

OutLe : Act → Act → ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
OutLe A₀ A₁ z z′ = ∀ q q′ w w′ c c′ Y Y′ → val w ≤ val w′ → c ≤ c′ → vY Y ≤ vY Y′ → Ob A₀ c z q w Y ≤ Ob A₁ c′ z′ q′ w′ Y′

-- 第二件: 树自己的第 0 层值, 让 ⨾ 之后坐标仍可比
Rl : Act → Act → ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
Rl A₀ A₁ z z′ = OutLe A₀ A₁ z z′ × (V0 z ≤ V0 z′)

smono : ∀ {V₁ V₂} {b b′ : A} {x : D azero V₁} {x′ : D azero V₂} → b ≤ b′ → V0 x ≤ V0 x′ → sum b x ≤ sum b′ x′
smono {b = b} {b′} {x} {x′} h hx = ≤-trans (proj₁ (sum-toA b x)) (≤-trans (⊞-mono h hx) (proj₂ (sum-toA b′ x′)))

ptsV : ∀ {V₁ V₂} (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) → (∀ n → V0 (d n) ≤ V0 (d′ n)) →
       ∀ k → proj₁ (pts (azero , tt) (λ n → toA (d n)) k) ≤ proj₁ (pts (azero , tt) (λ n → toA (d′ n)) k)
ptsV d d′ h zero = ≤-refl azero
ptsV d d′ h (suc k) = ⊞-mono (ptsV d d′ h k) (h k)

preV : ∀ {V₁ V₂} (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) → (∀ n → V0 (d n) ≤ V0 (d′ n)) →
       ∀ k → V0 (pre d k) ≤ proj₁ (pts (azero , tt) (λ n → toA (d′ n)) k)
preV d d′ h zero = ≤-refl azero
preV d d′ h (suc k) = ⊞-mono (preV d d′ h k) (h k)

preV′ : ∀ {V₁ V₂} (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) → (∀ n → V0 (d n) ≤ V0 (d′ n)) →
        ∀ k → proj₁ (pts (azero , tt) (λ n → toA (d n)) k) ≤ V0 (pre d′ k)
preV′ d d′ h zero = ≤-refl azero
preV′ d d′ h (suc k) = ⊞-mono (preV′ d d′ h k) (h k)
```

## §2 结构律

```agda
module _ {A₀ A₁ : Act} where
  ⨾-mono : ∀ {V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → Rl A₀ A₁ x x′ → Rl A₀ A₁ y y′ → Rl A₀ A₁ (x ⨾ y) (x′ ⨾ y′)
  ⨾-mono (hx , ax) (hy , ay) =
    (λ q q′ w w′ b b′ Y Y′ c cb r → hy q q′ _ _ _ _ _ _ (smono c ax) (hx q q′ w w′ b b′ Y Y′ c cb r) (hx q q′ w w′ _ _ Y Y′ c r r)) ,
    ⊞-mono ax ay

  nl-mono : ∀ {V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → Rl A₀ A₁ (d n) (d′ n)) → Rl A₀ A₁ (nl d) (nl d′)
  nl-mono {d = d} {d′} h = O , l≤ (λ n → ≤l n (ptsV d d′ (λ m → proj₂ (h m)) n))
    where
    O : OutLe A₀ A₁ (nl d) (nl d′)
    O q q′ w w′ b b′ Y Y′ c cb r = l≤ (λ n → ≤l n (proj₁ (proj₂ (go n))))
      where
      P = λ n → F.Rpt ac₀ d q lW k₀ A₀ w Y n
      P′ = λ n → F.Rpt ac₀ d′ q′ lW k₀ A₁ w′ Y′ n
      go : ∀ n → (val (proj₁ (P n)) ≤ val (proj₁ (P′ n))) ×
                 ((pt b (λ m → F.yc (Rn A₀ (d m) q (proj₁ (P m)) (proj₂ (P m))) τ₀ tt) n ≤
                   pt b′ (λ m → F.yc (Rn A₁ (d′ m) q′ (proj₁ (P′ m)) (proj₂ (P′ m))) τ₀ tt) n) ×
                  (vY (proj₂ (P n)) ≤ vY (proj₂ (P′ n))))
      go zero = c , (cb , r)
      go (suc n) = let (gc , (gb , gs)) = go n in
        smono gc (proj₂ (h n)) , (proj₁ (h n) q q′ _ _ _ _ _ _ gc gb gs , proj₁ (h n) q q′ _ _ _ _ _ _ gc gs gs)

  nw-l : ∀ {V₀ V V₂} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₂} → Rl A₀ A₁ x z → Rl A₀ A₁ (nw p x) z
  nw-l {p = p} (h , a) = (λ q q′ w w′ b b′ Y Y′ c cb r → h (⊲-tr p q) q′ w w′ b b′ Y Y′ c cb r) , a

  nw-r : ∀ {V₀ V V₁} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₁} → Rl A₀ A₁ z x → Rl A₀ A₁ z (nw p x)
  nw-r {p = p} (h , a) = (λ q q′ w w′ b b′ Y Y′ c cb r → h q (⊲-tr p q′) w w′ b b′ Y Y′ c cb r) , a

  n1⊑ : HAᶜ A₀ A₁ → ∀ {V₁ V₂} → Rl A₀ A₁ (n1 {W = V₁}) (n1 {W = V₂})
  n1⊑ ha = (λ q q′ w w′ b b′ Y Y′ c cb r → ha w w′ b b′ Y Y′ c cb r) , ≤-refl _

  infl : ∀ {V₁ V₂} (z : D azero V₂) → Rl A₀ A₁ (n0 {W = V₁}) z
  infl z = (λ q q′ w w′ b b′ Y Y′ c cb r → ≤-trans cb (⊲→≤ (sum-fst b′ (F.yc (Rn A₁ z q′ w′ Y′) τ₀ tt)))) , z≤

  refl⊑ : HAᶜ A₀ A₁ → ∀ {V} (z : D azero V) → Rl A₀ A₁ z z
  refl⊑ ha n0 = infl n0
  refl⊑ ha n1 = n1⊑ ha
  refl⊑ ha (x ⨾ y) = ⨾-mono (refl⊑ ha x) (refl⊑ ha y)
  refl⊑ ha (nl d) = nl-mono (λ n → refl⊑ ha (d n))
  refl⊑ ha (ni () u)
  refl⊑ ha (nκ () u)
  refl⊑ ha (nw p x) = nw-l (nw-r (refl⊑ ha x))

  pre-le : ∀ {V₁ V₂} (x : D azero V₁) (x′ : D azero V₂) (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) →
           Rl A₀ A₁ x x′ → (∀ n → Rl A₀ A₁ (d n) (d′ n)) → ∀ k → Rl A₀ A₁ (x ⨾ pre d k) (x′ ⨾ nl d′)
  pre-le x x′ d d′ hx hd k =
    (λ q q′ w w′ b b′ Y Y′ c cb r →
      ≤l k (proj₁ (proj₂ (go q q′ k (smono c (proj₂ hx)) (proj₁ hx q q′ w w′ b b′ Y Y′ c cb r) (proj₁ hx q q′ w w′ _ _ Y Y′ c r r))))) ,
    ⊞-mono (proj₂ hx) (≤l k (preV d d′ (λ m → proj₂ (hd m)) k))
    where
    go : ∀ q q′ k {w₁ w₁′ e e′ Z Z′} → val w₁ ≤ val w₁′ → e ≤ e′ → vY Z ≤ vY Z′ →
         (val (w₁ ⨾ nw q (pre d k)) ≤ val (proj₁ (F.Rpt ac₀ d′ q′ lW k₀ A₁ w₁′ Z′ k))) ×
         ((Ob A₀ e (pre d k) q w₁ Z ≤
           pt e′ (λ m → F.yc (Rn A₁ (d′ m) q′ (proj₁ (F.Rpt ac₀ d′ q′ lW k₀ A₁ w₁′ Z′ m)) (proj₂ (F.Rpt ac₀ d′ q′ lW k₀ A₁ w₁′ Z′ m))) τ₀ tt) k) ×
          (vY (Z F.⊕ Rn A₀ (pre d k) q w₁ Z) ≤ vY (proj₂ (F.Rpt ac₀ d′ q′ lW k₀ A₁ w₁′ Z′ k))))
    go q q′ zero c′ e r′ = c′ , (e , r′)
    go q q′ (suc k) c′ e r′ = let (gc , (gb , gs)) = go q q′ k c′ e r′ in
      smono gc (proj₂ (hd k)) , (proj₁ (hd k) q q′ _ _ _ _ _ _ gc gb gs , proj₁ (hd k) q q′ _ _ _ _ _ _ gc gs gs)

-- 下面几条只用同一个动作
module _ {A₀ : Act} (ha : HAᶜ A₀ A₀) where
  private rf = refl⊑ {A₀} {A₀} ha

  unit-l : ∀ {V} (x : D azero V) → Rl A₀ A₀ (n0 ⨾ x) x × Rl A₀ A₀ x (n0 ⨾ x)
  unit-l x = ((λ q q′ w w′ b b′ Y Y′ c cb r → proj₁ (rf x) q q′ _ w′ _ b′ _ Y′ c cb r) , proj₂ (z⊞ (V0 x))) ,
             ((λ q q′ w w′ b b′ Y Y′ c cb r → proj₁ (rf x) q q′ w _ b _ Y _ c cb r) , proj₁ (z⊞ (V0 x)))

  unit-r : ∀ {V} (x : D azero V) → Rl A₀ A₀ (x ⨾ n0) x × Rl A₀ A₀ x (x ⨾ n0)
  unit-r x = (proj₁ (rf x) , ≤-refl _) , (proj₁ (rf x) , ≤-refl _)

  assoc : ∀ {V} (x y z : D azero V) → Rl A₀ A₀ ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z)) × Rl A₀ A₀ (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
  assoc x y z = (A1 , ⊞-assoʳ (V0 x) (V0 y) (V0 z)) , (A1′ , ⊞-asso (V0 x) (V0 y) (V0 z))
    where
    A1 : OutLe A₀ A₀ ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z))
    A1 q q′ w w′ b b′ Y Y′ c cb r =
      proj₁ (rf z) q q′ _ _ _ _ _ _ (smono (smono c (≤-refl (V0 x))) (≤-refl (V0 y)))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (smono c (≤-refl (V0 x))) (proj₁ (rf x) q q′ w w′ b b′ Y Y′ c cb r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (smono c (≤-refl (V0 x))) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r))
    A1′ : OutLe A₀ A₀ (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
    A1′ q q′ w w′ b b′ Y Y′ c cb r =
      proj₁ (rf z) q q′ _ _ _ _ _ _ (smono (smono c (≤-refl (V0 x))) (≤-refl (V0 y)))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (smono c (≤-refl (V0 x))) (proj₁ (rf x) q q′ w w′ b b′ Y Y′ c cb r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (smono c (≤-refl (V0 x))) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ c r r))

module _ {A₀ A₁ : Act} where
  lim-leP : HAᶜ A₀ A₀ → ∀ {V₁ V₂} (x : D azero V₁) (d : ℕ → D azero V₁) (z : D azero V₂) →
            (∀ k → Rl A₀ A₁ (x ⨾ pre d k) z) → Rl A₀ A₁ (x ⨾ nl d) z
  lim-leP ha x d z h =
    (λ q q′ w w′ b b′ Y Y′ c cb r →
      l≤ (λ k → ≤-trans (proj₁ (proj₂ (go q k))) (proj₁ (h k) q q′ w w′ b b′ Y Y′ c cb r))) ,
    l≤ (λ k → ≤-trans (⊞-mono (≤-refl (V0 x)) (preV′ d d (λ m → ≤-refl _) k)) (proj₂ (h k)))
    where
    go : ∀ q k {w₁ e Z} → (val (proj₁ (F.Rpt ac₀ d q lW k₀ A₀ w₁ Z k)) ≤ val (w₁ ⨾ nw q (pre d k))) ×
                          ((pt e (λ m → F.yc (Rn A₀ (d m) q (proj₁ (F.Rpt ac₀ d q lW k₀ A₀ w₁ Z m)) (proj₂ (F.Rpt ac₀ d q lW k₀ A₀ w₁ Z m))) τ₀ tt) k
                            ≤ Ob A₀ e (pre d k) q w₁ Z) ×
                           (vY (proj₂ (F.Rpt ac₀ d q lW k₀ A₀ w₁ Z k)) ≤ vY (Z F.⊕ Rn A₀ (pre d k) q w₁ Z)))
    go q zero = ≤-refl _ , (≤-refl _ , ≤-refl _)
    go q (suc k) = let (gc , (gb , gs)) = go q k in
      smono gc (≤-refl (V0 (d k))) , (proj₁ (refl⊑ {A₀} {A₀} ha (d k)) q q _ _ _ _ _ _ gc gb gs , proj₁ (refl⊑ {A₀} {A₀} ha (d k)) q q _ _ _ _ _ _ gc gs gs)

  tr⊑ : ∀ {V V₃} {z z′ : D azero V} {z″ : D azero V₃} → Rl A₀ A₀ z z′ → Rl A₀ A₁ z′ z″ → Rl A₀ A₁ z z″
  tr⊑ (h , a) (h′ , a′) =
    (λ q q″ w w″ b b″ Y Y″ c cb r → ≤-trans (h q q w w b b Y Y (≤-refl _) (≤-refl _) (≤-refl _)) (h′ q q″ w w″ b b″ Y Y″ c cb r)) , ≤-trans a a′

  tr⊑ʳ : ∀ {V V₁} {z : D azero V₁} {z′ z″ : D azero V} → Rl A₀ A₁ z z′ → Rl A₁ A₁ z′ z″ → Rl A₀ A₁ z z″
  tr⊑ʳ (h , a) (h′ , a′) =
    (λ q q″ w w″ b b″ Y Y″ c cb r → ≤-trans (h q q″ w w″ b b″ Y Y″ c cb r) (h′ q″ q″ w″ w″ b″ b″ Y″ Y″ (≤-refl _) (≤-refl _) (≤-refl _))) , ≤-trans a a′
```

## §3 规范形: 套 `Gen`

```agda
private
  module GG = Gen HAᶜ Rl (λ {i} {j} h → n1⊑ {i} {j} h) (λ {i} {j} z → infl {i} {j} z)
                 (λ {i} {j} → ⨾-mono {i} {j}) (λ {i} {j} → nl-mono {i} {j}) (λ {i} {j} → nw-l {i} {j}) (λ {i} {j} → nw-r {i} {j})
                 (λ {i} {j} → tr⊑ {i} {j}) (λ {i} {j} → tr⊑ʳ {i} {j})
                 (λ {i} h → unit-l {i} h) (λ {i} h → unit-r {i} h) (λ {i} h → assoc {i} h)
                 (λ {i} {j} → pre-le {i} {j}) (λ {i} {j} h → lim-leP {i} {j} h)

-- 值同余: 第 0 层值 ≤ 则走起来 ≤, 两边动作可以不同
cong0 : ∀ {A₀ A₁ : Act} → HAᶜ A₀ A₀ → HAᶜ A₁ A₁ → HAᶜ A₀ A₁ →
        ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → V0 z ≤ V0 z′ → Rl A₀ A₁ z z′
cong0 {A₀} {A₁} ha ha′ hx = GG.Two.cong0 {A₀} {A₁} ha ha′ hx
```

## §4 链

`Chn` 从状态的第 0 层差 $\delta_0$ 出发 (坐标 `n0`), 每一段沿链点 $\delta_n$ 走, 坐标接上 $\delta_n$, 下一个链点是这一段在 $\tau_0$ 上的输出. 不变量四件: 坐标值, 链点值, 状态值, 部分和. 每一步用一次 `cong0`.

```agda
module _ {A₀ A₁ : Act} (ha : HAᶜ A₀ A₀) (ha′ : HAᶜ A₁ A₁) (hx : HAᶜ A₀ A₁) where
  CC : Act → F.St W → ℕ → D azero W × (D azero W × F.St W)
  CC A Y = F.Chn ac₀ k₀ lW tt A Y

  segs : Act → F.St W → ℕ → D azero W
  segs A Y n = F.yc (Rn A (proj₁ (proj₂ (CC A Y n))) C.self (proj₁ (CC A Y n)) (proj₂ (proj₂ (CC A Y n)))) τ₀ tt

  toV0 : ∀ {V V′} (x : D azero V) (x′ : D azero V′) → sum azero x ≤ sum azero x′ → V0 x ≤ V0 x′
  toV0 x x′ le = ≤-trans (proj₂ (sum₀ x)) (≤-trans le (proj₁ (sum₀ x′)))

  chain : ∀ (Y Y′ : F.St W) b b′ → b ≤ b′ → vY Y ≤ vY Y′ → sum b (nl (segs A₀ Y)) ≤ sum b′ (nl (segs A₁ Y′))
  chain Y Y′ b b′ cb r = l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (go n)))))
    where
    c  = λ n → proj₁ (CC A₀ Y n)
    c′ = λ n → proj₁ (CC A₁ Y′ n)
    δ  = λ n → proj₁ (proj₂ (CC A₀ Y n))
    δ′ = λ n → proj₁ (proj₂ (CC A₁ Y′ n))
    Yn  = λ n → proj₂ (proj₂ (CC A₀ Y n))
    Yn′ = λ n → proj₂ (proj₂ (CC A₁ Y′ n))
    go : ∀ n → (val (c n) ≤ val (c′ n)) × ((V0 (δ n) ≤ V0 (δ′ n)) × ((vY (Yn n) ≤ vY (Yn′ n)) × (pt b (segs A₀ Y) n ≤ pt b′ (segs A₁ Y′) n)))
    go zero = z≤ , (toV0 (δ 0) (δ′ 0) r , (r , cb))
    go (suc n) =
      let (gc , (gd , (gs , gb))) = go n
          h = proj₁ (cong0 {A₀} {A₁} ha ha′ hx (δ n) (δ′ n) gd)
      in smono gc gd ,
         (toV0 _ _ (h C.self C.self (c n) (c′ n) azero azero (Yn n) (Yn′ n) gc z≤ gs) ,
          (h C.self C.self (c n) (c′ n) _ _ (Yn n) (Yn′ n) gc gs gs ,
           h C.self C.self (c n) (c′ n) _ _ (Yn n) (Yn′ n) gc gb gs))
```
