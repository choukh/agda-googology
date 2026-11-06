# `nκ` 的值语义 (五): 区间的和, 只看差树

> 不含记号, 不提折叠. 入口 [KVal](KVal.lagda.md). `SumOneTree.Cut u b p` 是 "从 $a$ 走到 $b$, 每个层 $c$ 上放 $u(c)$" 的第 1 层树: 它就是 `dif` (每格放 $1$) 的带分支版. 本文在 `lo` 档关系里证四件 (分支对层的值单调, `KMono`):
>
> - `CutX`, `CutRf`: 同一条路径, 分支逐格对齐 ⇒ 相关; 每个区间和自比.
> - `T`: 沿复合路径的区间和是两段之和 (两个方向).
> - `PI`: 同一对端点之间, 区间和与路径、与合法性证明都无关 (照 `CvHighCong.PI` 搬, 无环 `G` 排除自身到自身的非平凡路径).
> - **`CutM`**: 区间 $[a,b)$ 对 $[a',b')$, $a'\le a$, $b\le b'$ (**按值**), 分支按层的值对齐 ⇒ 区间和相关. 这是 "包含式" 对齐. 证法照 `CvHighCong.M`, 但不能从 $0$ 起算 (起点 $a'$ 不一定是 $b'$ 的字面第一位置), 所以对两端的树归纳, 右边是极限时用尾路径 (`TailE`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValCut where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤lim⁻; irr; ⊲→≤)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nw; Cut; tailP)
open import OCF.Align.BrwMidZero using (steps≤)
open import OCF.Align.DValCanon using (G; an-s; an-l)
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree
open import OCF.Align.KValSound using (KX)
```

## §1 记号

```agda
infix 4 _≈ᵏ_
_≈ᵏ_ : ∀ {V V′} → D one V → D one V′ → Set
x ≈ᵏ y = (x ⊑[ lo ] y) × (y ⊑[ lo ] x)

-- 中间的树与左边同世界
tr≈ : ∀ {V V′} {x y : D one V} {z : D one V′} → x ≈ᵏ y → y ≈ᵏ z → x ≈ᵏ z
tr≈ (a , a′) (b , b′) = trˡ a b , trʳ b′ a′

sym≈ : ∀ {V V′} {x : D one V} {y : D one V′} → x ≈ᵏ y → y ≈ᵏ x
sym≈ (a , b) = b , a

infl-r : ∀ {V} {x : D one V} (y : D one V) → Rfᵏ lo x → x ⊑[ lo ] (x ⨾ y)
infl-r y rx = trˡ (u1ʳ rx) (⨾⊑ rx n0⊑)

-- 区间和: 同一条路径, 分支逐格对齐
CutX : ∀ {V V′} {u : Bk V} {u′ : Bk V′} → KX u u′ → ∀ b {a} (p : a ⊲ b) (ab : V ⊲ a) (ab′ : V′ ⊲ a) (lb : Lg b)
       {W W′} (bW : b ⊲ W) (bW′ : b ⊲ W′) → Cut u b p ab lb bW ⊑[ lo ] Cut u′ b p ab′ lb bW′
CutX kx b C.self ab ab′ lb bW bW′ = n0⊑
CutX {u = u} {u′} kx (asuc c) (C.suc p) ab ab′ lb bW bW′ =
  ⨾⊑ (CutX kx c p ab ab′ lb _ _) (nwˡ (nwʳ (kx (⊲-tr ab p) (⊲-tr ab′ p) lb lb (≤-refl c))))
CutX kx (alim f) (C.lim n p) ab ab′ (st , w) bW bW′ =
  ⨾⊑ (CutX kx (f n) p ab ab′ (w n) _ _)
     (nl⊑ (λ m → CutX kx (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (⊲-tr ab′ (tailP f st p m)) (w (suc (m + n))) _ _))
```

## §2 单一族: 复合, 与路径无关, 尾路径

```agda
module One {V : A} (u : Bk V) (mono : KMono u) where
  CutI : ∀ b {a} (p : a ⊲ b) (ab ab′ : V ⊲ a) (lb : Lg b) {W W′} (bW : b ⊲ W) (bW′ : b ⊲ W′) → Cut u b p ab lb bW ⊑[ lo ] Cut u b p ab′ lb bW′
  CutI = CutX mono

  CutRf : ∀ b {a} (p : a ⊲ b) (ab : V ⊲ a) (lb : Lg b) {W} (bW : b ⊲ W) → Rfᵏ lo (Cut u b p ab lb bW)
  CutRf b p ab lb bW = CutI b p ab ab lb bW bW

  cell : ∀ {c W} (p : V ⊲ c) (p′ : V ⊲ c) (l : Lg c) (q : c ⊲ W) (q′ : c ⊲ W) → nw q (u p l) ⊑[ lo ] nw q′ (u p′ l)
  cell {c} p p′ l q q′ = nwˡ (nwʳ (mono p p′ l l (≤-refl c)))

  T : ∀ {a b c} (p : a ⊲ b) (q : b ⊲ c) (ab : V ⊲ a) (lc : Lg c) {W} (cW : c ⊲ W) →
      Cut u c (⊲-tr p q) ab lc cW ≈ᵏ (Cut u b p ab (lg⊲ q lc) (⊲-tr q cW) ⨾ Cut u c q (⊲-tr ab p) lc cW)
  T {b = b} p C.self ab lc cW = u1ʳ (CutI b p ab ab lc cW (⊲-tr C.self cW)) , u1ˡ (CutI b p ab ab lc (⊲-tr C.self cW) cW)
  T {b = b} p (C.suc {b = c₀} q) ab lc cW =
    trˡ (⨾⊑ (trˡ (proj₁ IH) (⨾⊑ (CutI b p ab ab (lg⊲ q lc) (⊲-tr q X) (⊲-tr (C.suc q) cW)) (CutRf c₀ q (⊲-tr ab p) lc X))) (cell (⊲-tr ab (⊲-tr p q)) (⊲-tr (⊲-tr ab p) q) lc X X))
        (asʳ (cell (⊲-tr (⊲-tr ab p) q) (⊲-tr (⊲-tr ab p) q) lc X X) (⨾⊑ (⨾⊑ (CutRf b p ab (lg⊲ q lc) (⊲-tr (C.suc q) cW)) (CutRf c₀ q (⊲-tr ab p) lc X)) (cell (⊲-tr (⊲-tr ab p) q) (⊲-tr (⊲-tr ab p) q) lc X X))) ,
    asˡ′ (cell (⊲-tr (⊲-tr ab p) q) (⊲-tr (⊲-tr ab p) q) lc X X)
      (⨾⊑ (trˡ (⨾⊑ (CutI b p ab ab (lg⊲ q lc) (⊲-tr (C.suc q) cW) (⊲-tr q X)) (CutRf c₀ q (⊲-tr ab p) lc X)) (proj₂ IH)) (cell (⊲-tr (⊲-tr ab p) q) (⊲-tr ab (⊲-tr p q)) lc X X))
    where
    X = ⊲-tr (C.suc C.self) cW
    IH = T p q ab lc X
  T {b = b} p (C.lim {f = f} n q) ab (st , w) cW =
    trˡ (⨾⊑ (trˡ (proj₁ IH) (⨾⊑ (CutI b p ab ab (lg⊲ q (w n)) (⊲-tr q X) (⊲-tr (C.lim n q) cW)) (CutRf (f n) q (⊲-tr ab p) (w n) X))) NL)
        (asʳ (nl⊑ (λ m → CutRf _ _ _ _ _)) (⨾⊑ (⨾⊑ (CutRf b p ab (lg⊲ q (w n)) (⊲-tr (C.lim n q) cW)) (CutRf (f n) q (⊲-tr ab p) (w n) X)) (nl⊑ (λ m → CutRf _ _ _ _ _)))) ,
    asˡ′ (nl⊑ (λ m → CutRf _ _ _ _ _))
      (⨾⊑ (trˡ (⨾⊑ (CutI b p ab ab (lg⊲ q (w n)) (⊲-tr (C.lim n q) cW) (⊲-tr q X)) (CutRf (f n) q (⊲-tr ab p) (w n) X)) (proj₂ IH)) NL′)
    where
    X = ⊲-tr (C.lim n C.self) cW
    IH = T p q ab (w n) X
    NL = nl⊑ (λ m → CutI (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st (⊲-tr p q) m)) (⊲-tr (⊲-tr ab p) (tailP f st q m)) (w (suc (m + n))) _ _)
    NL′ = nl⊑ (λ m → CutI (f (suc (m + n))) (st (m + n)) (⊲-tr (⊲-tr ab p) (tailP f st q m)) (⊲-tr ab (tailP f st (⊲-tr p q) m)) (w (suc (m + n))) _ _)

  substD : ∀ (h : ℕ → A) (w : ∀ n → Lg (h n)) {a x x′} (eq : x ≡ x′) (P : a ⊲ h x) (ab : V ⊲ a) {W W′} (b : h x′ ⊲ W) (b′ : h x ⊲ W′) →
           Cut u (h x′) (subst (λ y → a ⊲ h y) eq P) ab (w x′) b ≈ᵏ Cut u (h x) P ab (w x) b′
  substD h w refl P ab b b′ = CutI _ P ab ab (w _) b b′ , CutI _ P ab ab (w _) b′ b

  Items : ∀ (h : ℕ → A) (st : ∀ n → h n ⊲ h (suc n)) (w : ∀ n → Lg (h n)) {a n} (p : a ⊲ h n) (ab : V ⊲ a) {W} (bW : alim h ⊲ W) → ℕ → D one W
  Items h st w {n = n} p ab bW m = Cut u (h (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP h st p m)) (w (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW)

  PI  : ∀ b {a} (p p′ : a ⊲ b) (ab ab′ : V ⊲ a) (l l′ : Lg b) {W W′} (bW : b ⊲ W) (bW′ : b ⊲ W′) →
        Cut u b p ab l bW ≈ᵏ Cut u b p′ ab′ l′ bW′
  PI′ : ∀ b {a a′} (e : a ≡ a′) (p : a ⊲ b) (p′ : a′ ⊲ b) (ab : V ⊲ a) (ab′ : V ⊲ a′) (l l′ : Lg b) {W W′} (bW : b ⊲ W) (bW′ : b ⊲ W′) →
        Cut u b p ab l bW ≈ᵏ Cut u b p′ ab′ l′ bW′
  PIL : ∀ (h : ℕ → A) {a} n (p₁ : a ⊲ h n) (st : ∀ n → h n ⊲ h (suc n)) (w : ∀ n → Lg (h n))
        m (p₂ : a ⊲ h m) (st′ : ∀ n → h n ⊲ h (suc n)) (w′ : ∀ n → Lg (h n)) (ab ab′ : V ⊲ a) {W W′} (bW : alim h ⊲ W) (bW′ : alim h ⊲ W′) →
        Cut u (alim h) (C.lim n p₁) ab (st , w) bW ⊑[ lo ] Cut u (alim h) (C.lim m p₂) ab′ (st′ , w′) bW′
  L4′ : ∀ (h : ℕ → A) (st : ∀ n → h n ⊲ h (suc n)) (w : ∀ n → Lg (h n)) {a n} (p : a ⊲ h n) (ab : V ⊲ a) m {W} (bW : alim h ⊲ W) →
        Cut u (h (m + n)) (tailP h st p m) ab (w (m + n)) (⊲-tr (C.lim (m + n) C.self) bW) ≈ᵏ
        (Cut u (h n) p ab (w n) (⊲-tr (C.lim n C.self) bW) ⨾ pre₁ (Items h st w p ab bW) m)

  PI b p p′ ab ab′ l l′ bW bW′ = PI′ b refl p p′ ab ab′ l l′ bW bW′
  PI′ b e C.self C.self ab ab′ l l′ bW bW′ = n0⊑ , n0⊑
  PI′ (asuc c) e C.self (C.suc q) ab ab′ l l′ bW bW′ = ⊥-elim (G c (subst (λ x → x ⊲ c) (sym e) q) (an-s C.self))
  PI′ (alim f) e C.self (C.lim n q) ab ab′ l l′ bW bW′ = ⊥-elim (G (f n) (subst (λ x → x ⊲ f n) (sym e) q) (an-l n C.self))
  PI′ (asuc c) e (C.suc q) C.self ab ab′ l l′ bW bW′ = ⊥-elim (G c (subst (λ x → x ⊲ c) e q) (an-s C.self))
  PI′ (alim f) e (C.lim n q) C.self ab ab′ l l′ bW bW′ = ⊥-elim (G (f n) (subst (λ x → x ⊲ f n) e q) (an-l n C.self))
  PI′ (asuc c) e (C.suc p) (C.suc p′) ab ab′ l l′ bW bW′ =
    let (h , h′) = PI′ c e p p′ ab ab′ l l′ (⊲-tr (C.suc C.self) bW) (⊲-tr (C.suc C.self) bW′)
    in ⨾⊑ h (nwˡ (nwʳ (mono _ _ l l′ (≤-refl c)))) , ⨾⊑ h′ (nwˡ (nwʳ (mono _ _ l′ l (≤-refl c))))
  PI′ (alim h) refl (C.lim n p₁) (C.lim m p₂) ab ab′ (st , w) (st′ , w′) bW bW′ =
    PIL h n p₁ st w m p₂ st′ w′ ab ab′ bW bW′ , PIL h m p₂ st′ w′ n p₁ st w ab′ ab bW′ bW

  PIL h {a} n p₁ st w m p₂ st′ w′ ab ab′ bW bW′ =
    lim⊑ (λ j → CutRf _ _ _ _ _) (λ k → trˡ (proj₂ (L4′ h st w p₁ ab k bW)) (bound k))
    where
    bound : ∀ k → Cut u (h (k + n)) (tailP h st p₁ k) ab (w (k + n)) (⊲-tr (C.lim (k + n) C.self) bW) ⊑[ lo ]
                  Cut u (alim h) (C.lim m p₂) ab′ (st′ , w′) bW′
    bound k =
      trˡ (proj₁ (PI (h (k + n)) (tailP h st p₁ k) (tailP h st p₁ k) ab ab (w (k + n)) (lg⊲ r (w′ i)) _ (⊲-tr r Bi)))
      (trˡ (infl-r (Cut u (h i) r (⊲-tr ab (tailP h st p₁ k)) (w′ i) Bi) (CutRf _ _ _ _ _))
      (trˡ (proj₂ (T (tailP h st p₁ k) r ab (w′ i) Bi))
      (trˡ (proj₁ (PI (h i) (⊲-tr (tailP h st p₁ k) r) (subst (λ y → a ⊲ h y) eq (tailP h st′ p₂ (k + n))) ab ab′ (w′ i) (w′ i) Bi Bi))
      (trʳ (proj₁ (substD h w′ eq (tailP h st′ p₂ (k + n)) ab′ Bi (⊲-tr (C.lim ((k + n) + m) C.self) bW′)))
      (trʳ (proj₁ (L4′ h st′ w′ p₂ ab′ (k + n) bW′))
           (pre⊑ (CutRf _ _ _ _ _) (λ j → CutRf _ _ _ _ _) (k + n)))))))
      where
      i = m + (k + n)
      r : h (k + n) ⊲ h i
      r = tailP h st′ C.self m
      Bi = ⊲-tr (C.lim i C.self) bW
      eq : (k + n) + m ≡ i
      eq = +-comm (k + n) m

  L4′ h st w {n = n} p ab zero bW = u1ʳ (CutRf _ _ _ _ _) , u1ˡ (CutRf _ _ _ _ _)
  L4′ h st w {n = n} p ab (suc m) bW =
    tr≈ (T (tailP h st p m) (st (m + n)) ab (w (suc (m + n))) B₊)
    (tr≈ (⨾⊑ (proj₁ (PI (h (m + n)) (tailP h st p m) (tailP h st p m) ab ab (lg⊲ (st (m + n)) (w (suc (m + n)))) (w (m + n)) _ _))
             (CutI _ _ _ _ _ _ _) ,
          ⨾⊑ (proj₂ (PI (h (m + n)) (tailP h st p m) (tailP h st p m) ab ab (lg⊲ (st (m + n)) (w (suc (m + n)))) (w (m + n)) _ _))
             (CutI _ _ _ _ _ _ _))
    (tr≈ (⨾⊑ (proj₁ (L4′ h st w p ab m bW)) (CutRf _ _ _ _ _) , ⨾⊑ (proj₂ (L4′ h st w p ab m bW)) (CutRf _ _ _ _ _))
         (asʳ (CutRf _ _ _ _ _) (⨾⊑ (⨾⊑ (CutRf _ _ _ _ _) (rfpre m)) (CutRf _ _ _ _ _)) ,
          asˡ′ (CutRf _ _ _ _ _) (⨾⊑ (⨾⊑ (CutRf _ _ _ _ _) (rfpre m)) (CutRf _ _ _ _ _)))))
    where
    B₊ = ⊲-tr (C.lim (suc (m + n)) C.self) bW
    rfpre : ∀ k → Rfᵏ lo (pre₁ (Items h st w p ab bW) k)
    rfpre zero = n0⊑
    rfpre (suc k) = ⨾⊑ (rfpre k) (CutRf _ _ _ _ _)

  -- 尾路径上的区间和在极限的区间和之下
  TailE : ∀ (h : ℕ → A) (st : ∀ n → h n ⊲ h (suc n)) (w : ∀ n → Lg (h n)) {a k} (p : a ⊲ h k) (ab : V ⊲ a) j {W} (bW : alim h ⊲ W) →
          Cut u (h (j + k)) (tailP h st p j) ab (w (j + k)) (⊲-tr (C.lim (j + k) C.self) bW) ⊑[ lo ] Cut u (alim h) (C.lim k p) ab (st , w) bW
  TailE h st w p ab j bW = trʳ (proj₁ (L4′ h st w p ab j bW)) (pre⊑ (CutRf _ _ _ _ _) (λ i → CutRf _ _ _ _ _) j)
```

## §3 包含式对齐: `CutM`

左边区间 $[a,b)$, 右边 $[a',b')$, 只要 $a'\le a$ 且 $b\le b'$ (按值). 对两端的树归纳 (先左后右).

```agda
module Two {V V′ : A} (u : Bk V) (u′ : Bk V′) (mono : KMono u) (mono′ : KMono u′) (kx : KX u u′) where
  module L = One u mono
  module R = One u′ mono′

  CutM : ∀ b b′ {a a′} (p : a ⊲ b) (p′ : a′ ⊲ b′) (ab : V ⊲ a) (ab′ : V′ ⊲ a′) (lb : Lg b) (lb′ : Lg b′) {W W′} (bW : b ⊲ W) (bW′ : b′ ⊲ W′) →
         a′ ≤ a → b ≤ b′ → Cut u b p ab lb bW ⊑[ lo ] Cut u′ b′ p′ ab′ lb′ bW′
  CutM b b′ C.self p′ ab ab′ lb lb′ bW bW′ a≤ le = n0⊑
  CutM (asuc c) azero (C.suc p) p′ ab ab′ lb lb′ bW bW′ a≤ ()
  CutM (asuc c) (asuc c′) (C.suc p) C.self ab ab′ lb lb′ bW bW′ a≤ (s≤ c≤) = ⊥-elim (irr c (≤-trans (s≤ c≤) (≤-trans a≤ (⊲→≤ p))))
  CutM (asuc c) (asuc c′) (C.suc p) (C.suc p′) ab ab′ lb lb′ bW bW′ a≤ (s≤ c≤) =
    ⨾⊑ (CutM c c′ p p′ ab ab′ lb lb′ _ _ a≤ c≤) (nwˡ (nwʳ (kx (⊲-tr ab p) (⊲-tr ab′ p′) lb lb′ c≤)))
  CutM (asuc c) (alim g) (C.suc p) C.self ab ab′ lb lb′ bW bW′ a≤ le = ⊥-elim (irr c (≤-trans le (≤-trans a≤ (⊲→≤ p))))
  CutM (asuc c) (alim g) (C.suc p) (C.lim k p′) ab ab′ lb (st′ , w′) bW bW′ a≤ le with ≤lim⁻ le
  ... | n , le′ =
    trʳ (CutM (asuc c) (g (n + k)) (C.suc p) (tailP g st′ p′ n) ab ab′ lb (w′ (n + k)) bW (⊲-tr (C.lim (n + k) C.self) bW′)
              a≤ (≤-trans le′ (steps≤ g st′ n k)))
        (R.TailE g st′ w′ p′ ab′ n bW′)
  CutM (alim f) b′ (C.lim n p) p′ ab ab′ (st , w) lb′ bW bW′ a≤ le =
    lim⊑ (λ j → L.CutRf _ _ _ _ _)
         (λ k → trˡ (proj₂ (L.L4′ f st w p ab k bW))
                    (CutM (f (k + n)) b′ (tailP f st p k) p′ ab ab′ (w (k + n)) lb′ _ bW′ a≤ (≤-trans (≤l (k + n) (≤-refl _)) le)))
```
