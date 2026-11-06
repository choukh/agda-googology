# 带坐标的值同余: 动作可以读坐标的值

> 不含记号. 入口 [CvLayer](CvLayer.lagda.md). [CvFoldRun](CvFoldRun.lagda.md) 与 [CvHighCong](CvHighCong.lagda.md) 的前提 `HA` 要动作一步之后的值对**一切**坐标都只依赖状态的值; 第 1 层输入的分支读坐标, 那不成立. 这里换成
>
> - `HAᶜ`: 底 $\preccurlyeq$, 状态的值 $\preccurlyeq$, **且坐标的第 0 层值 $\le$** ⇒ 动作这一段加在底上 $\preccurlyeq$.
> - `z ⊑ z′`: 两件同时: (走) 从底小、状态值小、坐标小的起点走 $z$ 不超过从底大、状态值大、坐标大的起点走 $z'$ (`Ob`: 底与状态分开, `Out` 是底取状态值的特例); (值) $\mathrm{toA}\,z\le\mathrm{toA}\,z'$. 第二件让 `⨾` 之后的坐标仍然可比.
> - **`canon`**, **`cong0`** 照搬到这个关系上. 第二件全部由结构律 (`⨾`, `nl`, 单位, 结合) 拼出, 不要消去律.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.SumOneClosed as F
open import OCF.Align.SumOneTree using (cnt)
open import OCF.Align.LayerTrOne using (one)
module OCF.Align.CvLayerRun {W : A} (lW : Lg W) (t1 : one ⊲ W) (ac : F.AccY (cnt azero)) (ll : azero ⊲ W) (A₀ : F.Ig (cnt azero) W) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-comm)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
open import OCF.Align.CumReadCF using (z⊲; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; _⊞_; ⊞-mono; ⊞-asso; ⊞-assoʳ)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; tailP; sum)
open import OCF.Align.BrwMidZero using (dif; toA; sum₀; sum-toA; z⊞; pts; ⊞-fst; ⊞-⊲; Lg-⊞)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (S; Sp; S-fst; ok-yes)
open import OCF.Align.LayerTrRound using (cw)
open import OCF.Align.CvFoldRun lW t1 ac ll A₀ using (τ₁; v; R; Out; Sp≡)
open import OCF.Align.CvHighCong lW t1 ac ll A₀ using (Anc; an-s; an-l; G; ⊲→≼; pre; z0)
```

## §1 关系

```agda
val : ∀ {V} → D azero V → A
val w = sum azero w

V0 : ∀ {V} → D azero V → A
V0 z = proj₁ (toA z)

-- 从底 c 起, 加上状态 Y 走 z 之后目标第 1 层的差. Out z q w Y = Ob (v Y) z q w Y
Ob : ∀ {W₀} → B₁ W → D azero W₀ → W₀ ⊲ W → D azero W → F.St W → B₁ W
Ob c z q w Y = S C.self lW c (F.yc (R z q w Y) τ₁ tt)

HAᶜ : Set
HAᶜ = ∀ w w′ c c′ Y Y′ → val w ≤ val w′ → c ≼ c′ → v Y ≼ v Y′ →
      S C.self lW c (F.yc (A₀ C.self lW w Y) τ₁ tt) ≼ S C.self lW c′ (F.yc (A₀ C.self lW w′ Y′) τ₁ tt)

OutLe : ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
OutLe z z′ = ∀ q q′ w w′ c c′ Y Y′ → val w ≤ val w′ → c ≼ c′ → v Y ≼ v Y′ → Ob c z q w Y ≼ Ob c′ z′ q′ w′ Y′

infix 4 _⊑_ _~_
_⊑_ : ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
z ⊑ z′ = OutLe z z′ × (V0 z ≤ V0 z′)

_~_ : ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
z ~ z′ = (z ⊑ z′) × (z′ ⊑ z)

-- 和对两边单调
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
module _ (ha : HAᶜ) where

  ⨾-mono : ∀ {V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → x ⊑ x′ → y ⊑ y′ → (x ⨾ y) ⊑ (x′ ⨾ y′)
  ⨾-mono (hx , ax) (hy , ay) =
    (λ q q′ w w′ b b′ Y Y′ c cb r → hy q q′ _ _ _ _ _ _ (smono c ax) (hx q q′ w w′ b b′ Y Y′ c cb r) (hx q q′ w w′ _ _ Y Y′ c r r)) ,
    ⊞-mono ax ay

  nl-mono : ∀ {V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → d n ⊑ d′ n) → nl d ⊑ nl d′
  nl-mono {d = d} {d′} h = O , l≤ (λ n → ≤l n (ptsV d d′ (λ m → proj₂ (h m)) n))
    where
    O : OutLe (nl d) (nl d′)
    O q q′ w w′ b b′ Y Y′ c cb r = l≼ (λ n → ≼l n (proj₁ (proj₂ (go n))))
      where
      P = λ n → F.Rpt ac d q lW ll A₀ w Y n
      P′ = λ n → F.Rpt ac d′ q′ lW ll A₀ w′ Y′ n
      go : ∀ n → (val (proj₁ (P n)) ≤ val (proj₁ (P′ n))) ×
                 ((Sp C.self lW b (λ m → F.yc (R (d m) q (proj₁ (P m)) (proj₂ (P m))) τ₁ tt) n ≼
                   Sp C.self lW b′ (λ m → F.yc (R (d′ m) q′ (proj₁ (P′ m)) (proj₂ (P′ m))) τ₁ tt) n) ×
                  (v (proj₂ (P n)) ≼ v (proj₂ (P′ n))))
      go zero = c , (cb , r)
      go (suc n) = let (gc , (gb , gs)) = go n in
        smono gc (proj₂ (h n)) , (proj₁ (h n) q q′ _ _ _ _ _ _ gc gb gs , proj₁ (h n) q q′ _ _ _ _ _ _ gc gs gs)

  nw-l : ∀ {V₀ V V₂} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₂} → x ⊑ z → nw p x ⊑ z
  nw-l {p = p} (h , a) = (λ q q′ w w′ b b′ Y Y′ c cb r → h (⊲-tr p q) q′ w w′ b b′ Y Y′ c cb r) , a

  nw-r : ∀ {V₀ V V₁} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₁} → z ⊑ x → z ⊑ nw p x
  nw-r {p = p} (h , a) = (λ q q′ w w′ b b′ Y Y′ c cb r → h q (⊲-tr p q′) w w′ b b′ Y Y′ c cb r) , a

  refl⊑ : ∀ {V} (z : D azero V) → z ⊑ z
  refl⊑ n0 = (λ q q′ w w′ b b′ Y Y′ c cb r → cb) , ≤-refl azero
  refl⊑ n1 = (λ q q′ w w′ b b′ Y Y′ c cb r → ha w w′ b b′ Y Y′ c cb r) , ≤-refl _
  refl⊑ (x ⨾ y) = ⨾-mono (refl⊑ x) (refl⊑ y)
  refl⊑ (nl d) = nl-mono (λ n → refl⊑ (d n))
  refl⊑ (ni () u)
  refl⊑ (nκ () u)
  refl⊑ (nw p x) = nw-l (nw-r (refl⊑ x))

  rf~ : ∀ {V} (z : D azero V) → z ~ z
  rf~ z = refl⊑ z , refl⊑ z

  sym~ : ∀ {V₁ V₂} {z : D azero V₁} {z′ : D azero V₂} → z ~ z′ → z′ ~ z
  sym~ (h , h′) = h′ , h

  tr⊑ : ∀ {V V₃} {z z′ : D azero V} {z″ : D azero V₃} → z ⊑ z′ → z′ ⊑ z″ → z ⊑ z″
  tr⊑ (h , a) (h′ , a′) =
    (λ q q″ w w″ b b″ Y Y″ c cb r → ≼-trans (h q q w w b b Y Y (≤-refl _) (≼-refl _) (≼-refl _)) (h′ q q″ w w″ b b″ Y Y″ c cb r)) , ≤-trans a a′

  tr⊑ʳ : ∀ {V V₁} {z : D azero V₁} {z′ z″ : D azero V} → z ⊑ z′ → z′ ⊑ z″ → z ⊑ z″
  tr⊑ʳ (h , a) (h′ , a′) =
    (λ q q″ w w″ b b″ Y Y″ c cb r → ≼-trans (h q q″ w w″ b b″ Y Y″ c cb r) (h′ q″ q″ w″ w″ b″ b″ Y″ Y″ (≤-refl _) (≼-refl _) (≼-refl _))) , ≤-trans a a′

  tr~ : ∀ {V V₃} {z z′ : D azero V} {z″ : D azero V₃} → z ~ z′ → z′ ~ z″ → z ~ z″
  tr~ (a , a′) (b , b′) = tr⊑ a b , tr⊑ʳ b′ a′

  ⨾~ : ∀ {V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → x ~ x′ → y ~ y′ → (x ⨾ y) ~ (x′ ⨾ y′)
  ⨾~ (a , a′) (b , b′) = ⨾-mono a b , ⨾-mono a′ b′

  nl~ : ∀ {V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → d n ~ d′ n) → nl d ~ nl d′
  nl~ h = nl-mono (λ n → proj₁ (h n)) , nl-mono (λ n → proj₂ (h n))

  nw~ : ∀ {V₀ V} {p : V₀ ⊲ V} (x : D azero V₀) → nw p x ~ x
  nw~ x = nw-l (refl⊑ x) , nw-r (refl⊑ x)

  unit-l : ∀ {V} (x : D azero V) → (n0 ⨾ x) ~ x
  unit-l x = ((λ q q′ w w′ b b′ Y Y′ c cb r → proj₁ (refl⊑ x) q q′ _ w′ _ b′ _ Y′ c cb r) , proj₂ (z⊞ (V0 x))) ,
             ((λ q q′ w w′ b b′ Y Y′ c cb r → proj₁ (refl⊑ x) q q′ w _ b _ Y _ c cb r) , proj₁ (z⊞ (V0 x)))

  unit-r : ∀ {V} (x : D azero V) → (x ⨾ n0) ~ x
  unit-r x = (proj₁ (refl⊑ x) , ≤-refl _) , (proj₁ (refl⊑ x) , ≤-refl _)

  assoc : ∀ {V} (x y z : D azero V) → ((x ⨾ y) ⨾ z) ~ (x ⨾ (y ⨾ z))
  assoc x y z = (A1 , ⊞-assoʳ (V0 x) (V0 y) (V0 z)) , (A1′ , ⊞-asso (V0 x) (V0 y) (V0 z))
    where
    A1 : OutLe ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z))
    A1 q q′ w w′ b b′ Y Y′ c cb r =
      proj₁ (refl⊑ z) q q′ _ _ _ _ _ _ (smono (smono c (≤-refl (V0 x))) (≤-refl (V0 y)))
        (proj₁ (refl⊑ y) q q′ _ _ _ _ _ _ (smono c (≤-refl (V0 x))) (proj₁ (refl⊑ x) q q′ w w′ b b′ Y Y′ c cb r) (proj₁ (refl⊑ x) q q′ w w′ _ _ Y Y′ c r r))
        (proj₁ (refl⊑ y) q q′ _ _ _ _ _ _ (smono c (≤-refl (V0 x))) (proj₁ (refl⊑ x) q q′ w w′ _ _ Y Y′ c r r) (proj₁ (refl⊑ x) q q′ w w′ _ _ Y Y′ c r r))
    A1′ : OutLe (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
    A1′ q q′ w w′ b b′ Y Y′ c cb r =
      proj₁ (refl⊑ z) q q′ _ _ _ _ _ _ (smono (smono c (≤-refl (V0 x))) (≤-refl (V0 y)))
        (proj₁ (refl⊑ y) q q′ _ _ _ _ _ _ (smono c (≤-refl (V0 x))) (proj₁ (refl⊑ x) q q′ w w′ b b′ Y Y′ c cb r) (proj₁ (refl⊑ x) q q′ w w′ _ _ Y Y′ c r r))
        (proj₁ (refl⊑ y) q q′ _ _ _ _ _ _ (smono c (≤-refl (V0 x))) (proj₁ (refl⊑ x) q q′ w w′ _ _ Y Y′ c r r) (proj₁ (refl⊑ x) q q′ w w′ _ _ Y Y′ c r r))

  infl : ∀ {V₁ V₂} (z : D azero V₂) → z0 {V₁} ⊑ z
  infl z = (λ q q′ w w′ b b′ Y Y′ c cb r → ≼-trans cb (⊲→≼ (S-fst yes C.self lW b′ (F.yc (R z q′ w′ Y′) τ₁ tt) (ok-yes _)))) , z≤

  infl-r : ∀ {V} (x y : D azero V) → x ⊑ (x ⨾ y)
  infl-r x y = tr⊑ (proj₂ (unit-r x)) (⨾-mono (refl⊑ x) (infl y))
```

## §3 部分和

```agda
  pre-le : ∀ {V₁ V₂} (x : D azero V₁) (x′ : D azero V₂) (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) →
           x ⊑ x′ → (∀ n → d n ⊑ d′ n) → ∀ k → (x ⨾ pre d k) ⊑ (x′ ⨾ nl d′)
  pre-le x x′ d d′ hx hd k =
    (λ q q′ w w′ b b′ Y Y′ c cb r →
      ≼l k (proj₁ (proj₂ (go q q′ k (smono c (proj₂ hx)) (proj₁ hx q q′ w w′ b b′ Y Y′ c cb r) (proj₁ hx q q′ w w′ _ _ Y Y′ c r r))))) ,
    ⊞-mono (proj₂ hx) (≤l k (preV d d′ (λ m → proj₂ (hd m)) k))
    where
    go : ∀ q q′ k {w₁ w₁′ e e′ Z Z′} → val w₁ ≤ val w₁′ → e ≼ e′ → v Z ≼ v Z′ →
         (val (w₁ ⨾ nw q (pre d k)) ≤ val (proj₁ (F.Rpt ac d′ q′ lW ll A₀ w₁′ Z′ k))) ×
         ((Ob e (pre d k) q w₁ Z ≼
           Sp C.self lW e′ (λ m → F.yc (R (d′ m) q′ (proj₁ (F.Rpt ac d′ q′ lW ll A₀ w₁′ Z′ m)) (proj₂ (F.Rpt ac d′ q′ lW ll A₀ w₁′ Z′ m))) τ₁ tt) k) ×
          (Out (pre d k) q w₁ Z ≼ v (proj₂ (F.Rpt ac d′ q′ lW ll A₀ w₁′ Z′ k))))
    go q q′ zero c′ e r′ = c′ , (e , r′)
    go q q′ (suc k) c′ e r′ = let (gc , (gb , gs)) = go q q′ k c′ e r′ in
      smono gc (proj₂ (hd k)) , (proj₁ (hd k) q q′ _ _ _ _ _ _ gc gb gs , proj₁ (hd k) q q′ _ _ _ _ _ _ gc gs gs)

  lim-leP : ∀ {V₁ V₂} (x : D azero V₁) (d : ℕ → D azero V₁) (z : D azero V₂) →
            (∀ k → (x ⨾ pre d k) ⊑ z) → (x ⨾ nl d) ⊑ z
  lim-leP x d z h =
    (λ q q′ w w′ b b′ Y Y′ c cb r →
      l≼ (λ k → ≼-trans (proj₁ (proj₂ (go q k))) (proj₁ (h k) q q′ w w′ b b′ Y Y′ c cb r))) ,
    l≤ (λ k → ≤-trans (⊞-mono (≤-refl (V0 x)) (preV′ d d (λ m → ≤-refl _) k)) (proj₂ (h k)))
    where
    go : ∀ q k {w₁ e Z} → (val (proj₁ (F.Rpt ac d q lW ll A₀ w₁ Z k)) ≤ val (w₁ ⨾ nw q (pre d k))) ×
                          ((Sp C.self lW e (λ m → F.yc (R (d m) q (proj₁ (F.Rpt ac d q lW ll A₀ w₁ Z m)) (proj₂ (F.Rpt ac d q lW ll A₀ w₁ Z m))) τ₁ tt) k
                            ≼ Ob e (pre d k) q w₁ Z) ×
                           (v (proj₂ (F.Rpt ac d q lW ll A₀ w₁ Z k)) ≼ Out (pre d k) q w₁ Z))
    go q zero = ≤-refl _ , (≼-refl _ , ≼-refl _)
    go q (suc k) = let (gc , (gb , gs)) = go q k in
      smono gc (≤-refl (V0 (d k))) , (proj₁ (refl⊑ (d k)) q q _ _ _ _ _ _ gc gb gs , proj₁ (refl⊑ (d k)) q q _ _ _ _ _ _ gc gs gs)
```

## §4 读回的差的形状 (照 `CvFoldRun`, `CvHighCong`)

```agda
  TI : ∀ {V} c e {x} (q : x ⊲ e) (lc : Lg c) (le : Lg e) → dif {V} (c ⊞ e) (⊞-⊲ c q) (Lg-⊞ c e lc le) ~ dif {V} e q le
  TI c e C.self lc le = rf~ n0
  TI c (asuc e) (C.suc q) lc le = ⨾~ (TI c e q lc le) (rf~ n1)
  TI c (alim h) (C.lim n q) lc (st , wl) =
    ⨾~ (TI c (h n) q lc (wl n)) (nl~ (λ m → TI c (h (suc (m + n))) (st (m + n)) lc (wl (suc (m + n)))))

  DEC : ∀ {V} a X B (la : Lg a) (lx : Lg X) (lB : Lg B) →
        dif {V} (a ⊞ (X ⊞ B)) (⊞-fst a (X ⊞ B)) (Lg-⊞ a (X ⊞ B) la (Lg-⊞ X B lx lB)) ~
        (dif {V} (a ⊞ X) (⊞-fst a X) (Lg-⊞ a X la lx) ⨾ dif {V} ((a ⊞ X) ⊞ B) (⊞-fst (a ⊞ X) B) (Lg-⊞ (a ⊞ X) B (Lg-⊞ a X la lx) lB))
  DEC a X azero la lx lB = sym~ (unit-r _)
  DEC a X (asuc B) la lx lB = tr~ (⨾~ (DEC a X B la lx lB) (rf~ n1)) (assoc _ _ _)
  DEC a X (alim h) la lx (st , wl) =
    tr~ (⨾~ (DEC a X (h 0) la lx (wl 0))
            (nl~ (λ m → tr~ (TI a (X ⊞ h (suc (m + 0))) (⊞-⊲ X (st (m + 0))) la (Lg-⊞ X (h (suc (m + 0))) lx (wl (suc (m + 0)))))
                       (tr~ (TI X (h (suc (m + 0))) (st (m + 0)) lx (wl (suc (m + 0))))
                            (sym~ (TI (a ⊞ X) (h (suc (m + 0))) (st (m + 0)) (Lg-⊞ a X la lx) (wl (suc (m + 0)))))))))
        (assoc _ _ _)

  Cc : ∀ {V W₀} (z : D azero W₀) a (la : Lg a) →
       dif {V} (a ⊞ proj₁ (toA z)) (⊞-fst a (proj₁ (toA z))) (Lg-⊞ a (proj₁ (toA z)) la (proj₂ (toA z))) ~ z
  Cc n0 a la = ((λ q q′ w w′ b b′ Y Y′ c cb r → cb) , ≤-refl azero) , ((λ q q′ w w′ b b′ Y Y′ c cb r → cb) , ≤-refl azero)
  Cc n1 a la = ((λ q q′ w w′ b b′ Y Y′ c cb r → ha _ w′ _ b′ _ Y′ c cb r) , ≤-refl _) , ((λ q q′ w w′ b b′ Y Y′ c cb r → ha w _ b _ Y _ c cb r) , ≤-refl _)
  Cc (x ⨾ y) a la =
    tr~ (DEC a (proj₁ (toA x)) (proj₁ (toA y)) la (proj₂ (toA x)) (proj₂ (toA y)))
        (⨾~ (Cc x a la) (Cc y (a ⊞ proj₁ (toA x)) (Lg-⊞ a (proj₁ (toA x)) la (proj₂ (toA x)))))
  Cc {V} (nl d) a la = tr~ (unit-l _) (nl~ E)
    where
    P : ℕ → A
    P k = proj₁ (pts (azero , tt) (λ n → toA (d n)) k)
    lP : ∀ k → Lg (P k)
    lP k = proj₂ (pts (azero , tt) (λ n → toA (d n)) k)
    EL : ℕ → D azero V
    EL m = dif {V} (a ⊞ P (suc (m + 0))) (⊞-⊲ a (⊞-fst (P (m + 0)) (proj₁ (toA (d (m + 0)))))) (Lg-⊞ a (P (suc (m + 0))) la (lP (suc (m + 0))))
    E′ : ∀ m → EL m ~ d (m + 0)
    E′ m = tr~ (TI a (P (suc (m + 0))) (⊞-fst (P (m + 0)) (proj₁ (toA (d (m + 0))))) la (lP (suc (m + 0))))
               (Cc (d (m + 0)) (P (m + 0)) (lP (m + 0)))
    E : ∀ m → EL m ~ d m
    E m = subst (λ j → EL m ~ d j) (+-identityʳ m) (E′ m)
  Cc (ni () u) a la
  Cc (nκ () u) a la
  Cc (nw p x) a la = let (h , h′) = Cc x a la in nw-r h , nw-l h′

  ZL : ∀ {V} X (lx : Lg X) → dif {V} X (z⊲ X) lx ~ dif {V} (azero ⊞ X) (⊞-fst azero X) (Lg-⊞ azero X tt lx)
  ZL azero lx = rf~ n0
  ZL (asuc X) lx = ⨾~ (ZL X lx) (rf~ n1)
  ZL (alim f) (st , w) =
    ⨾~ (ZL (f 0) (w 0)) (nl~ (λ m → sym~ (TI azero (f (suc (m + 0))) (st (m + 0)) tt (w (suc (m + 0))))))

  canon : ∀ {W₀} (z : D azero W₀) → cw z ~ z
  canon z =
    tr~ (unit-l _)
    (tr~ (nw~ (dif (proj₁ (toA z)) (z⊲ (proj₁ (toA z))) (proj₂ (toA z))))
    (tr~ (ZL (proj₁ (toA z)) (proj₂ (toA z)))
         (Cc z azero tt)))

  T : ∀ {V} {a b c} (p : a ⊲ b) (q : b ⊲ c) (lc : Lg c) →
      dif {V} c (⊲-tr p q) lc ~ (dif {V} b p (lg⊲ q lc) ⨾ dif {V} c q lc)
  T p C.self lc = sym~ (unit-r _)
  T p (C.suc q) lc = tr~ (⨾~ (T p q lc) (rf~ n1)) (assoc _ _ _)
  T p (C.lim n q) (st , w) = tr~ (⨾~ (T p q (w n)) (rf~ _)) (assoc _ _ _)

  substD : ∀ {V} (h : ℕ → A) (w : ∀ n → Lg (h n)) {a x x′} (eq : x ≡ x′) (P : a ⊲ h x) →
           dif {V} (h x′) (subst (λ y → a ⊲ h y) eq P) (w x′) ~ dif {V} (h x) P (w x)
  substD h w refl P = rf~ _
```

## §5 与路径无关, 对 $\le$ 单调

```agda
  PI  : ∀ {V} b {a} (p p′ : a ⊲ b) (l l′ : Lg b) → dif {V} b p l ~ dif {V} b p′ l′
  PI′ : ∀ {V} b {a a′} (e : a ≡ a′) (p : a ⊲ b) (p′ : a′ ⊲ b) (l l′ : Lg b) → dif {V} b p l ~ dif {V} b p′ l′
  PIL : ∀ {V} (h : ℕ → A) {a} n (p₁ : a ⊲ h n) (st : ∀ n → h n ⊲ h (suc n)) (w : ∀ n → Lg (h n))
        m (p₂ : a ⊲ h m) (st′ : ∀ n → h n ⊲ h (suc n)) (w′ : ∀ n → Lg (h n)) →
        dif {V} (alim h) (C.lim n p₁) (st , w) ⊑ dif {V} (alim h) (C.lim m p₂) (st′ , w′)
  L4′ : ∀ {V} (h : ℕ → A) (st : ∀ n → h n ⊲ h (suc n)) (w : ∀ n → Lg (h n)) {a n} (p : a ⊲ h n) m →
        dif {V} (h (m + n)) (tailP h st p m) (w (m + n)) ~
        (dif {V} (h n) p (w n) ⨾ pre (λ k → dif {V} (h (suc (k + n))) (st (k + n)) (w (suc (k + n)))) m)

  PI b p p′ l l′ = PI′ b refl p p′ l l′
  PI′ b e C.self C.self l l′ = rf~ n0
  PI′ (asuc c) e C.self (C.suc q) l l′ = ⊥-elim (G c (subst (λ x → x ⊲ c) (sym e) q) (an-s C.self))
  PI′ (alim f) e C.self (C.lim n q) l l′ = ⊥-elim (G (f n) (subst (λ x → x ⊲ f n) (sym e) q) (an-l n C.self))
  PI′ (asuc c) e (C.suc q) C.self l l′ = ⊥-elim (G c (subst (λ x → x ⊲ c) e q) (an-s C.self))
  PI′ (alim f) e (C.lim n q) C.self l l′ = ⊥-elim (G (f n) (subst (λ x → x ⊲ f n) e q) (an-l n C.self))
  PI′ (asuc c) e (C.suc p) (C.suc p′) l l′ = ⨾~ (PI′ c e p p′ l l′) (rf~ n1)
  PI′ (alim h) refl (C.lim n p₁) (C.lim m p₂) (st , w) (st′ , w′) =
    PIL h n p₁ st w m p₂ st′ w′ , PIL h m p₂ st′ w′ n p₁ st w

  PIL {V} h {a} n p₁ st w m p₂ st′ w′ = lim-leP _ _ _ (λ k → tr⊑ (proj₂ (L4′ h st w p₁ k)) (bound k))
    where
    bound : ∀ k → dif {V} (h (k + n)) (tailP h st p₁ k) (w (k + n)) ⊑ dif {V} (alim h) (C.lim m p₂) (st′ , w′)
    bound k =
      tr⊑ (proj₁ (PI (h (k + n)) (tailP h st p₁ k) (tailP h st p₁ k) (w (k + n)) (lg⊲ r (w′ i))))
      (tr⊑ (infl-r _ (dif (h i) r (w′ i)))
      (tr⊑ (proj₂ (T (tailP h st p₁ k) r (w′ i)))
      (tr⊑ (proj₁ (PI (h i) (⊲-tr (tailP h st p₁ k) r) (subst (λ y → a ⊲ h y) eq (tailP h st′ p₂ (k + n))) (w′ i) (w′ i)))
      (tr⊑ (proj₁ (substD h w′ eq (tailP h st′ p₂ (k + n))))
      (tr⊑ (proj₁ (L4′ h st′ w′ p₂ (k + n)))
           (pre-le _ _ _ _ (refl⊑ _) (λ j → refl⊑ _) (k + n)))))))
      where
      i = m + (k + n)
      r : h (k + n) ⊲ h i
      r = tailP h st′ C.self m
      eq : (k + n) + m ≡ i
      eq = +-comm (k + n) m

  L4′ h st w {n = n} p zero = sym~ (unit-r _)
  L4′ h st w {n = n} p (suc m) =
    tr~ (T (tailP h st p m) (st (m + n)) (w (suc (m + n))))
    (tr~ (⨾~ (PI (h (m + n)) (tailP h st p m) (tailP h st p m) (lg⊲ (st (m + n)) (w (suc (m + n)))) (w (m + n))) (rf~ _))
    (tr~ (⨾~ (L4′ h st w p m) (rf~ _))
         (assoc _ _ _)))

  o1 : ∀ {V} → D azero V
  o1 = n1

  n1⊑ : ∀ {V₁ V₂} → o1 {V₁} ⊑ o1 {V₂}
  n1⊑ = (λ q q′ w w′ b b′ Y Y′ c cb r → ha w w′ b b′ Y Y′ c cb r) , ≤-refl _

  Dz : ∀ {V} b → Lg b → D azero V
  Dz b lb = dif b (z⊲ b) lb

  DzT : ∀ {V} (f : ℕ → A) st w n → Dz {V} (f n) (w n) ~ dif {V} (f (n + 0)) (tailP f st (z⊲ (f 0)) n) (w (n + 0))
  DzT {V} f st w n =
    tr~ (PI (f n) (z⊲ (f n)) (subst (λ y → azero ⊲ f y) (+-identityʳ n) (tailP f st (z⊲ (f 0)) n)) (w n) (w n))
        (substD f w (+-identityʳ n) (tailP f st (z⊲ (f 0)) n))

  DzE : ∀ {V} (f : ℕ → A) st w n → Dz {V} (f n) (w n) ⊑ Dz {V} (alim f) (st , w)
  DzE f st w n =
    tr⊑ (proj₁ (DzT f st w n)) (tr⊑ (proj₁ (L4′ f st w (z⊲ (f 0)) n)) (pre-le _ _ _ _ (refl⊑ _) (λ j → refl⊑ _) n))

  lim-bd : ∀ {V V′} (f : ℕ → A) st w (z : D azero V′) → (∀ n → Dz {V} (f n) (w n) ⊑ z) → Dz {V} (alim f) (st , w) ⊑ z
  lim-bd f st w z h =
    lim-leP _ _ z (λ k → tr⊑ (proj₂ (L4′ f st w (z⊲ (f 0)) k)) (tr⊑ (proj₂ (DzT f st w k)) (h k)))

  M : ∀ {V V′} {a b} → a ≤ b → (la : Lg a) (lb : Lg b) → Dz {V} a la ⊑ Dz {V′} b lb
  M z≤ la lb = infl _
  M (s≤ p) la lb = ⨾-mono (M p la lb) n1⊑
  M {b = alim f} (≤l n p) la (st , w) = tr⊑ʳ (M p la (w n)) (DzE f st w n)
  M {a = alim f} (l≤ p) (st , w) lb = lim-bd f st w _ (λ n → M (p n) (w n) lb)
```

## §6 值同余

```agda
  cong0 : ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → V0 z ≤ V0 z′ → z ⊑ z′
  cong0 z z′ le =
    tr⊑ (proj₂ (canon z))
    (tr⊑ʳ (⨾-mono ((λ q q′ w w′ b b′ Y Y′ c cb r → cb) , ≤-refl azero) (nw-l (nw-r (M le (proj₂ (toA z)) (proj₂ (toA z′))))))
          (proj₁ (canon z′)))

  cong-sum : ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → sum azero z ≤ sum azero z′ → z ⊑ z′
  cong-sum z z′ le = cong0 z z′ (≤-trans (proj₂ (sum₀ z)) (≤-trans le (proj₁ (sum₀ z′))))
```
