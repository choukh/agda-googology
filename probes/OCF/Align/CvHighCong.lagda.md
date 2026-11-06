# 折叠对第 0 层输入的值同余

> 不含记号. 入口 [CvHigh](CvHigh.lagda.md). 接 [CvFoldRun](CvFoldRun.lagda.md) (同样的参数与前提 `HA`). 那里只有规范化 `canon : cw z ~ᴼ z`; 这里补一般的值同余:
>
> - **`cong0`**: $\mathrm{toA}\,z\le\mathrm{toA}\,z'$ (第 0 层值) 推出 $z\sqsubseteq^{\mathsf O}z'$: 从值小的状态走 $z$ 不超过从值大的状态走 $z'$. `cong0≈`, `cong-sum`: 值相等则走起来值相等.
> - 缺的那一条 (读回的差对 $A$ 树的 $\le$ 单调) 是 `M`. 它要两件: 读回的差与路径和合法性证明无关 (**`PI`**), 沿复合路径读差就是分段读 (`T`). `PI` 在极限处不比较两条路径的下标, 只用部分和上界 (`lim-leP`, `pre-le`); 自身到自身的非平凡路径由无环 (`G`) 排除.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.SumOneClosed as F
open import OCF.Align.SumOneTree using (cnt)
open import OCF.Align.LayerTrOne using (one)
module OCF.Align.CvHighCong {W : A} (lW : Lg W) (t1 : one ⊲ W) (ac : F.AccY (cnt azero)) (ll : azero ⊲ W) (A₀ : F.Ig (cnt azero) W) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-comm)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
open import OCF.Align.CumReadCF using (z⊲; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; tailP; sum)
open import OCF.Align.BrwMidZero using (dif; toA; sum₀)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (S; S-fst; ok-yes)
open import OCF.Align.CvFoldSub using (≼-suc)
open import OCF.Align.CvFoldRun lW t1 ac ll A₀
```

## §1 第 0 层的无环

`Anc x y`: $y$ 是 $x$ 的一个直接子树的第一位置. `G`: 若 $x\lhd y$ 则不然.

```agda
data Anc : A → A → Set where
  an-s : ∀ {c y} → y ⊲ c → Anc (asuc c) y
  an-l : ∀ {f y} n → y ⊲ f n → Anc (alim f) y

G : ∀ y {x} → x ⊲ y → ¬ Anc x y
G (asuc c) C.self (an-s q) = G c q (an-s C.self)
G (alim f) C.self (an-l n q) = G (f n) q (an-l n C.self)
G (asuc y) (C.suc p) (an-s q) = G y p (an-s (⊲-tr (C.suc C.self) q))
G (asuc y) (C.suc p) (an-l n q) = G y p (an-l n (⊲-tr (C.suc C.self) q))
G (alim g) (C.lim k p) (an-s q) = G (g k) p (an-s (⊲-tr (C.lim k C.self) q))
G (alim g) (C.lim k p) (an-l n q) = G (g k) p (an-l n (⊲-tr (C.lim k C.self) q))
```

## §2 第一位置推出值前序

```agda
⊲→≼ : ∀ {V V′} {a : B₁ V} {b : B₁ V′} → a ⊲⟨ yes ⟩ b → a ≼ b
⊲→≼ self = ≼-refl _
⊲→≼ (suc p) = ≼-suc (⊲→≼ p)
⊲→≼ (lim n p) = ≼l n (⊲→≼ p)
⊲→≼ (wR p) = ≼w (⊲→≼ p)
⊲→≼ (wL p) = w≼ (⊲→≼ p)
⊲→≼ (ini l p) = ≼i C.self l azero tt (⊲→≼ p)
⊲→≼ (inκ l p) = ≼κ C.self l (⊲→≼ p)
```

## §3 部分和

```agda
z0 : ∀ {V} → D azero V
z0 = n0

pre : ∀ {V} → (ℕ → D azero V) → ℕ → D azero V
pre d zero = n0
pre d (suc k) = pre d k ⨾ d k

module _ (ha : HA) where

  rf = refl⊑ ha
  rf~ = refl~ ha

  -- 走什么都不低于起点
  infl : ∀ {V₁ V₂} (z : D azero V₂) → z0 {V₁} ⊑ᴼ z
  infl z q q′ w w′ Y Y′ r =
    ≼-trans r (⊲→≼ (S-fst yes C.self lW (v Y′) (F.yc (R z q′ w′ Y′) τ₁ tt) (ok-yes _)))

  infl-r : ∀ {V} (x y : D azero V) → x ⊑ᴼ (x ⨾ y)
  infl-r x y = tr⊑ ha (proj₂ (unit-r ha x)) (⨾-mono ha (rf x) (infl y))

  pre-le : ∀ {V₁ V₂} (x : D azero V₁) (x′ : D azero V₂) (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) →
           x ⊑ᴼ x′ → (∀ n → d n ⊑ᴼ d′ n) → ∀ k → (x ⨾ pre d k) ⊑ᴼ (x′ ⨾ nl d′)
  pre-le x x′ d d′ hx hd k q q′ w w′ Y Y′ r =
    ≼l k (subst (λ c → Out (pre d k) q _ (Y F.⊕ R x q w Y) ≼ c) (sym (Sp≡ d′ q′ _ _ k)) (go k (hx q q′ w w′ Y Y′ r)))
    where
    go : ∀ k {w₁ w₁′ Z Z′} → v Z ≼ v Z′ → Out (pre d k) q w₁ Z ≼ v (proj₂ (F.Rpt ac d′ q′ lW ll A₀ w₁′ Z′ k))
    go zero r′ = r′
    go (suc k) r′ = hd k q q′ _ _ _ _ (go k r′)

  lim-leP : ∀ {V₁ V₂} (x : D azero V₁) (d : ℕ → D azero V₁) (z : D azero V₂) →
            (∀ k → (x ⨾ pre d k) ⊑ᴼ z) → (x ⨾ nl d) ⊑ᴼ z
  lim-leP x d z h q q′ w w′ Y Y′ r =
    l≼ (λ k → subst (λ c → c ≼ Out z q′ w′ Y′) (sym (Sp≡ d q _ _ k)) (≼-trans (go k) (h k q q′ w w′ Y Y′ r)))
    where
    go : ∀ k {w₁ w₁′ Z} → v (proj₂ (F.Rpt ac d q lW ll A₀ w₁ Z k)) ≼ Out (pre d k) q w₁′ Z
    go zero = ≼-refl _
    go (suc k) = rf (d k) q q _ _ _ _ (go k)
```

## §4 沿复合路径读差

```agda
  T : ∀ {V} {a b c} (p : a ⊲ b) (q : b ⊲ c) (lc : Lg c) →
      dif {V} c (⊲-tr p q) lc ~ᴼ (dif {V} b p (lg⊲ q lc) ⨾ dif {V} c q lc)
  T p C.self lc = sym~ ha (unit-r ha _)
  T p (C.suc q) lc = tr~ ha (⨾~ ha (T p q lc) (rf~ n1)) (assoc ha _ _ _)
  T p (C.lim n q) (st , w) = tr~ ha (⨾~ ha (T p q (w n)) (rf~ _)) (assoc ha _ _ _)

  substD : ∀ {V} (h : ℕ → A) (w : ∀ n → Lg (h n)) {a x x′} (eq : x ≡ x′) (P : a ⊲ h x) →
           dif {V} (h x′) (subst (λ y → a ⊲ h y) eq P) (w x′) ~ᴼ dif {V} (h x) P (w x)
  substD h w refl P = rf~ _
```

## §5 与路径无关

`L4′`: 沿尾路径 `tailP` 读到 $h(m+n)$ 的差, 就是先读到 $h\,n$ 再接极限节点的前 $m$ 项. `PI`: 同一对端点之间, 读回的差与路径、与合法性证明都无关.

```agda
  PI  : ∀ {V} b {a} (p p′ : a ⊲ b) (l l′ : Lg b) → dif {V} b p l ~ᴼ dif {V} b p′ l′
  PI′ : ∀ {V} b {a a′} (e : a ≡ a′) (p : a ⊲ b) (p′ : a′ ⊲ b) (l l′ : Lg b) → dif {V} b p l ~ᴼ dif {V} b p′ l′
  PIL : ∀ {V} (h : ℕ → A) {a} n (p₁ : a ⊲ h n) (st : ∀ n → h n ⊲ h (suc n)) (w : ∀ n → Lg (h n))
        m (p₂ : a ⊲ h m) (st′ : ∀ n → h n ⊲ h (suc n)) (w′ : ∀ n → Lg (h n)) →
        dif {V} (alim h) (C.lim n p₁) (st , w) ⊑ᴼ dif {V} (alim h) (C.lim m p₂) (st′ , w′)
  L4′ : ∀ {V} (h : ℕ → A) (st : ∀ n → h n ⊲ h (suc n)) (w : ∀ n → Lg (h n)) {a n} (p : a ⊲ h n) m →
        dif {V} (h (m + n)) (tailP h st p m) (w (m + n)) ~ᴼ
        (dif {V} (h n) p (w n) ⨾ pre (λ k → dif {V} (h (suc (k + n))) (st (k + n)) (w (suc (k + n)))) m)

  PI b p p′ l l′ = PI′ b refl p p′ l l′
  PI′ b e C.self C.self l l′ = rf~ n0
  PI′ (asuc c) e C.self (C.suc q) l l′ = ⊥-elim (G c (subst (λ x → x ⊲ c) (sym e) q) (an-s C.self))
  PI′ (alim f) e C.self (C.lim n q) l l′ = ⊥-elim (G (f n) (subst (λ x → x ⊲ f n) (sym e) q) (an-l n C.self))
  PI′ (asuc c) e (C.suc q) C.self l l′ = ⊥-elim (G c (subst (λ x → x ⊲ c) e q) (an-s C.self))
  PI′ (alim f) e (C.lim n q) C.self l l′ = ⊥-elim (G (f n) (subst (λ x → x ⊲ f n) e q) (an-l n C.self))
  PI′ (asuc c) e (C.suc p) (C.suc p′) l l′ = ⨾~ ha (PI′ c e p p′ l l′) (rf~ n1)
  PI′ (alim h) refl (C.lim n p₁) (C.lim m p₂) (st , w) (st′ , w′) =
    PIL h n p₁ st w m p₂ st′ w′ , PIL h m p₂ st′ w′ n p₁ st w

  PIL {V} h {a} n p₁ st w m p₂ st′ w′ = lim-leP _ _ _ (λ k → tr⊑ ha (proj₂ (L4′ h st w p₁ k)) (bound k))
    where
    bound : ∀ k → dif {V} (h (k + n)) (tailP h st p₁ k) (w (k + n)) ⊑ᴼ dif {V} (alim h) (C.lim m p₂) (st′ , w′)
    bound k =
      tr⊑ ha (proj₁ (PI (h (k + n)) (tailP h st p₁ k) (tailP h st p₁ k) (w (k + n)) (lg⊲ r (w′ i))))
      (tr⊑ ha (infl-r _ (dif (h i) r (w′ i)))
      (tr⊑ ha (proj₂ (T (tailP h st p₁ k) r (w′ i)))
      (tr⊑ ha (proj₁ (PI (h i) (⊲-tr (tailP h st p₁ k) r) (subst (λ y → a ⊲ h y) eq (tailP h st′ p₂ (k + n))) (w′ i) (w′ i)))
      (tr⊑ ha (proj₁ (substD h w′ eq (tailP h st′ p₂ (k + n))))
      (tr⊑ ha (proj₁ (L4′ h st′ w′ p₂ (k + n)))
              (pre-le _ _ _ _ (rf _) (λ j → rf _) (k + n)))))))
      where
      i = m + (k + n)
      r : h (k + n) ⊲ h i
      r = tailP h st′ C.self m
      eq : (k + n) + m ≡ i
      eq = +-comm (k + n) m

  L4′ h st w {n = n} p zero = sym~ ha (unit-r ha _)
  L4′ h st w {n = n} p (suc m) =
    tr~ ha (T (tailP h st p m) (st (m + n)) (w (suc (m + n))))
    (tr~ ha (⨾~ ha (PI (h (m + n)) (tailP h st p m) (tailP h st p m) (lg⊲ (st (m + n)) (w (suc (m + n)))) (w (m + n))) (rf~ _))
    (tr~ ha (⨾~ ha (L4′ h st w p m) (rf~ _))
            (assoc ha _ _ _)))
```

## §6 读回的差对 $\le$ 单调

```agda
  Dz : ∀ {V} b → Lg b → D azero V
  Dz b lb = dif b (z⊲ b) lb

  E₀ : ∀ {V} (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (w : ∀ n → Lg (f n)) → ℕ → D azero V
  E₀ f st w k = dif (f (suc (k + 0))) (st (k + 0)) (w (suc (k + 0)))

  -- 第 n 项到极限节点的前 n 项
  DzT : ∀ {V} (f : ℕ → A) st w n → Dz {V} (f n) (w n) ~ᴼ dif {V} (f (n + 0)) (tailP f st (z⊲ (f 0)) n) (w (n + 0))
  DzT {V} f st w n =
    tr~ ha (PI (f n) (z⊲ (f n)) (subst (λ y → azero ⊲ f y) (+-identityʳ n) (tailP f st (z⊲ (f 0)) n)) (w n) (w n))
           (substD f w (+-identityʳ n) (tailP f st (z⊲ (f 0)) n))

  DzE : ∀ {V} (f : ℕ → A) st w n → Dz {V} (f n) (w n) ⊑ᴼ Dz {V} (alim f) (st , w)
  DzE f st w n =
    tr⊑ ha (proj₁ (DzT f st w n))
    (tr⊑ ha (proj₁ (L4′ f st w (z⊲ (f 0)) n))
            (pre-le _ _ _ _ (rf _) (λ j → rf _) n))

  lim-bd : ∀ {V V′} (f : ℕ → A) st w (z : D azero V′) → (∀ n → Dz {V} (f n) (w n) ⊑ᴼ z) → Dz {V} (alim f) (st , w) ⊑ᴼ z
  lim-bd f st w z h =
    lim-leP _ _ z (λ k → tr⊑ ha (proj₂ (L4′ f st w (z⊲ (f 0)) k)) (tr⊑ ha (proj₂ (DzT f st w k)) (h k)))

  M : ∀ {V V′} {a b} → a ≤ b → (la : Lg a) (lb : Lg b) → Dz {V} a la ⊑ᴼ Dz {V′} b lb
  M z≤ la lb = infl _
  M (s≤ p) la lb = ⨾-mono ha (M p la lb) (λ q q′ w w′ Y Y′ r → ha w w′ Y Y′ r)
  M {b = alim f} (≤l n p) la (st , w) = tr⊑ʳ ha (M p la (w n)) (DzE f st w n)
  M {a = alim f} (l≤ p) (st , w) lb = lim-bd f st w _ (λ n → M (p n) (w n) lb)
```

## §7 值同余

```agda
  cong0 : ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → proj₁ (toA z) ≤ proj₁ (toA z′) → z ⊑ᴼ z′
  cong0 z z′ le =
    tr⊑ ha (proj₂ (canon ha z))
    (tr⊑ʳ ha (⨾-mono ha (λ q q′ w w′ Y Y′ r → r) (nw-l ha (nw-r ha (M le (proj₂ (toA z)) (proj₂ (toA z′))))))
             (proj₁ (canon ha z′)))

  cong0≈ : ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) →
           proj₁ (toA z) ≤ proj₁ (toA z′) → proj₁ (toA z′) ≤ proj₁ (toA z) → z ~ᴼ z′
  cong0≈ z z′ le le′ = cong0 z z′ le , cong0 z′ z le′

  -- 用第 0 层的和 (SumOneTree.sum) 陈述
  cong-sum : ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → sum azero z ≤ sum azero z′ → z ⊑ᴼ z′
  cong-sum z z′ le = cong0 z z′ (≤-trans (proj₂ (sum₀ z)) (≤-trans le (proj₁ (sum₀ z′))))
```
