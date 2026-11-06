# 差树上的值关系 (一): 规范形论证, 对关系抽象

> 不含记号. 入口 [DVal](DVal.lagda.md). [CvLayerRun](CvLayerRun.lagda.md) 与 [CvHighCong](CvHighCong.lagda.md) 的 `canon`, `M`, `cong0` 只用到关系的十几条结构律 (单位, 结合, 部分和是上确界, `n1` 自比, 抬升透明, 两种传递), 不用到关系是什么. 这里把那段论证对关系抽象出来, 再加一处推广: **关系带两个下标** $i,j$ (两边各一个动作), 结论 `cong0 i j` 要三条前提 `Hy i i`, `Hy j j`, `Hy i j`.
>
> 用处: [DValZero](DValZero.lagda.md) 取下标为第 0 层输入的动作 (两边动作不同, 来自第 1 层 `ni` 的两组分支), 得出目标第 0 层的值同余. 别的实例 (例如第 1 层无节点的部分) 也可以直接套.
>
> 证明逐行照 `CvLayerRun` §4 到 §6 搬来, 只把关系换成参数. 第 0 层布劳威尔树的无环 `G` 照 `CvHighCong` §1 抄写 (那里在一个带参数的模块里).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DValCanon where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-comm)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; _⊞_)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; tailP)
open import OCF.Align.BrwMidZero using (dif; toA; pts; ⊞-fst; ⊞-⊲; Lg-⊞)
open import OCF.Align.LayerTrRound using (cw)
```

## §1 无环与部分和

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

pre : ∀ {V} → (ℕ → D azero V) → ℕ → D azero V
pre d zero = n0
pre d (suc k) = pre d k ⨾ d k
```

## §2 参数: 关系与它的结构律

`R i j z z′`: 左边用下标 $i$, 右边用下标 $j$. `Hy i j`: 两个下标之间的前提 (实例里是 "动作一步对状态与坐标的值单调").

```agda
module Gen {I : Set} (Hy : I → I → Set)
  (R : I → I → ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set)
  (n1⊑ : ∀ {i j} → Hy i j → ∀ {V₁ V₂} → R i j (n1 {W = V₁}) (n1 {W = V₂}))
  (infl : ∀ {i j V₁ V₂} (z : D azero V₂) → R i j (n0 {W = V₁}) z)
  (⨾-mono : ∀ {i j V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → R i j x x′ → R i j y y′ → R i j (x ⨾ y) (x′ ⨾ y′))
  (nl-mono : ∀ {i j V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → R i j (d n) (d′ n)) → R i j (nl d) (nl d′))
  (nw-l : ∀ {i j V₀ V V₂} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₂} → R i j x z → R i j (nw p x) z)
  (nw-r : ∀ {i j V₀ V V₁} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₁} → R i j z x → R i j z (nw p x))
  (tr⊑ : ∀ {i j V V₃} {z z′ : D azero V} {z″ : D azero V₃} → R i i z z′ → R i j z′ z″ → R i j z z″)
  (tr⊑ʳ : ∀ {i j V V₁} {z : D azero V₁} {z′ z″ : D azero V} → R i j z z′ → R j j z′ z″ → R i j z z″)
  (unit-l : ∀ {i} → Hy i i → ∀ {V} (x : D azero V) → R i i (n0 ⨾ x) x × R i i x (n0 ⨾ x))
  (unit-r : ∀ {i} → Hy i i → ∀ {V} (x : D azero V) → R i i (x ⨾ n0) x × R i i x (x ⨾ n0))
  (assoc : ∀ {i} → Hy i i → ∀ {V} (x y z : D azero V) → R i i ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z)) × R i i (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z))
  (pre-le : ∀ {i j V₁ V₂} (x : D azero V₁) (x′ : D azero V₂) (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) →
            R i j x x′ → (∀ n → R i j (d n) (d′ n)) → ∀ k → R i j (x ⨾ pre d k) (x′ ⨾ nl d′))
  (lim-leP : ∀ {i j V₁ V₂} → Hy i i → (x : D azero V₁) (d : ℕ → D azero V₁) (z : D azero V₂) →
             (∀ k → R i j (x ⨾ pre d k) z) → R i j (x ⨾ nl d) z)
  where

  refl⊑ : ∀ {i j} → Hy i j → ∀ {V} (z : D azero V) → R i j z z
  refl⊑ h n0 = infl n0
  refl⊑ h n1 = n1⊑ h
  refl⊑ h (x ⨾ y) = ⨾-mono (refl⊑ h x) (refl⊑ h y)
  refl⊑ h (nl d) = nl-mono (λ n → refl⊑ h (d n))
  refl⊑ h (ni () u)
  refl⊑ h (nκ () u)
  refl⊑ h (nw p x) = nw-l (nw-r (refl⊑ h x))
```

## §3 单个下标: 规范化

```agda
  module One {i : I} (hi : Hy i i) where
    infix 4 _~_
    _~_ : ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
    z ~ z′ = R i i z z′ × R i i z′ z

    rf : ∀ {V} (z : D azero V) → R i i z z
    rf = refl⊑ hi

    rf~ : ∀ {V} (z : D azero V) → z ~ z
    rf~ z = rf z , rf z

    sym~ : ∀ {V₁ V₂} {z : D azero V₁} {z′ : D azero V₂} → z ~ z′ → z′ ~ z
    sym~ (h , h′) = h′ , h

    tr~ : ∀ {V V₃} {z z′ : D azero V} {z″ : D azero V₃} → z ~ z′ → z′ ~ z″ → z ~ z″
    tr~ (a , a′) (b , b′) = tr⊑ a b , tr⊑ʳ b′ a′

    ⨾~ : ∀ {V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → x ~ x′ → y ~ y′ → (x ⨾ y) ~ (x′ ⨾ y′)
    ⨾~ (a , a′) (b , b′) = ⨾-mono a b , ⨾-mono a′ b′

    nl~ : ∀ {V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → d n ~ d′ n) → nl d ~ nl d′
    nl~ h = nl-mono (λ n → proj₁ (h n)) , nl-mono (λ n → proj₂ (h n))

    nw~ : ∀ {V₀ V} {p : V₀ ⊲ V} (x : D azero V₀) → nw p x ~ x
    nw~ x = nw-l (rf x) , nw-r (rf x)

    ul : ∀ {V} (x : D azero V) → (n0 ⨾ x) ~ x
    ul x = unit-l hi x

    ur : ∀ {V} (x : D azero V) → (x ⨾ n0) ~ x
    ur x = unit-r hi x

    as : ∀ {V} (x y z : D azero V) → ((x ⨾ y) ⨾ z) ~ (x ⨾ (y ⨾ z))
    as x y z = assoc hi x y z

    infl-r : ∀ {V} (x y : D azero V) → R i i x (x ⨾ y)
    infl-r x y = tr⊑ (proj₂ (ur x)) (⨾-mono (rf x) (infl y))

    TI : ∀ {V} c e {x} (q : x ⊲ e) (lc : Lg c) (le : Lg e) → dif {V} (c ⊞ e) (⊞-⊲ c q) (Lg-⊞ c e lc le) ~ dif {V} e q le
    TI c e C.self lc le = rf~ n0
    TI c (asuc e) (C.suc q) lc le = ⨾~ (TI c e q lc le) (rf~ n1)
    TI c (alim h) (C.lim n q) lc (st , wl) =
      ⨾~ (TI c (h n) q lc (wl n)) (nl~ (λ m → TI c (h (suc (m + n))) (st (m + n)) lc (wl (suc (m + n)))))

    DEC : ∀ {V} a X B (la : Lg a) (lx : Lg X) (lB : Lg B) →
          dif {V} (a ⊞ (X ⊞ B)) (⊞-fst a (X ⊞ B)) (Lg-⊞ a (X ⊞ B) la (Lg-⊞ X B lx lB)) ~
          (dif {V} (a ⊞ X) (⊞-fst a X) (Lg-⊞ a X la lx) ⨾ dif {V} ((a ⊞ X) ⊞ B) (⊞-fst (a ⊞ X) B) (Lg-⊞ (a ⊞ X) B (Lg-⊞ a X la lx) lB))
    DEC a X azero la lx lB = sym~ (ur _)
    DEC a X (asuc B) la lx lB = tr~ (⨾~ (DEC a X B la lx lB) (rf~ n1)) (as _ _ _)
    DEC a X (alim h) la lx (st , wl) =
      tr~ (⨾~ (DEC a X (h 0) la lx (wl 0))
              (nl~ (λ m → tr~ (TI a (X ⊞ h (suc (m + 0))) (⊞-⊲ X (st (m + 0))) la (Lg-⊞ X (h (suc (m + 0))) lx (wl (suc (m + 0)))))
                         (tr~ (TI X (h (suc (m + 0))) (st (m + 0)) lx (wl (suc (m + 0))))
                              (sym~ (TI (a ⊞ X) (h (suc (m + 0))) (st (m + 0)) (Lg-⊞ a X la lx) (wl (suc (m + 0)))))))))
          (as _ _ _)

    Cc : ∀ {V W₀} (z : D azero W₀) a (la : Lg a) →
         dif {V} (a ⊞ proj₁ (toA z)) (⊞-fst a (proj₁ (toA z))) (Lg-⊞ a (proj₁ (toA z)) la (proj₂ (toA z))) ~ z
    Cc n0 a la = infl n0 , infl n0
    Cc n1 a la = tr⊑ (proj₁ (ul n1)) (n1⊑ hi) , tr⊑ʳ (n1⊑ hi) (proj₂ (ul n1))
    Cc (x ⨾ y) a la =
      tr~ (DEC a (proj₁ (toA x)) (proj₁ (toA y)) la (proj₂ (toA x)) (proj₂ (toA y)))
          (⨾~ (Cc x a la) (Cc y (a ⊞ proj₁ (toA x)) (Lg-⊞ a (proj₁ (toA x)) la (proj₂ (toA x)))))
    Cc {V} (nl d) a la = tr~ (ul _) (nl~ E)
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
      tr~ (ul _)
      (tr~ (nw~ (dif (proj₁ (toA z)) (z⊲ (proj₁ (toA z))) (proj₂ (toA z))))
      (tr~ (ZL (proj₁ (toA z)) (proj₂ (toA z)))
           (Cc z azero tt)))

    T : ∀ {V} {a b c} (p : a ⊲ b) (q : b ⊲ c) (lc : Lg c) →
        dif {V} c (⊲-tr p q) lc ~ (dif {V} b p (lg⊲ q lc) ⨾ dif {V} c q lc)
    T p C.self lc = sym~ (ur _)
    T p (C.suc q) lc = tr~ (⨾~ (T p q lc) (rf~ n1)) (as _ _ _)
    T p (C.lim n q) (st , w) = tr~ (⨾~ (T p q (w n)) (rf~ _)) (as _ _ _)

    substD : ∀ {V} (h : ℕ → A) (w : ∀ n → Lg (h n)) {a x x′} (eq : x ≡ x′) (P : a ⊲ h x) →
             dif {V} (h x′) (subst (λ y → a ⊲ h y) eq P) (w x′) ~ dif {V} (h x) P (w x)
    substD h w refl P = rf~ _

    PI  : ∀ {V} b {a} (p p′ : a ⊲ b) (l l′ : Lg b) → dif {V} b p l ~ dif {V} b p′ l′
    PI′ : ∀ {V} b {a a′} (e : a ≡ a′) (p : a ⊲ b) (p′ : a′ ⊲ b) (l l′ : Lg b) → dif {V} b p l ~ dif {V} b p′ l′
    PIL : ∀ {V} (h : ℕ → A) {a} n (p₁ : a ⊲ h n) (st : ∀ n → h n ⊲ h (suc n)) (w : ∀ n → Lg (h n))
          m (p₂ : a ⊲ h m) (st′ : ∀ n → h n ⊲ h (suc n)) (w′ : ∀ n → Lg (h n)) →
          R i i (dif {V} (alim h) (C.lim n p₁) (st , w)) (dif {V} (alim h) (C.lim m p₂) (st′ , w′))
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

    PIL {V} h {a} n p₁ st w m p₂ st′ w′ = lim-leP hi _ _ _ (λ k → tr⊑ (proj₂ (L4′ h st w p₁ k)) (bound k))
      where
      bound : ∀ k → R i i (dif {V} (h (k + n)) (tailP h st p₁ k) (w (k + n))) (dif {V} (alim h) (C.lim m p₂) (st′ , w′))
      bound k =
        tr⊑ (proj₁ (PI (h (k + n)) (tailP h st p₁ k) (tailP h st p₁ k) (w (k + n)) (lg⊲ r (w′ ix))))
        (tr⊑ (infl-r _ (dif (h ix) r (w′ ix)))
        (tr⊑ (proj₂ (T (tailP h st p₁ k) r (w′ ix)))
        (tr⊑ (proj₁ (PI (h ix) (⊲-tr (tailP h st p₁ k) r) (subst (λ y → a ⊲ h y) eq (tailP h st′ p₂ (k + n))) (w′ ix) (w′ ix)))
        (tr⊑ (proj₁ (substD h w′ eq (tailP h st′ p₂ (k + n))))
        (tr⊑ (proj₁ (L4′ h st′ w′ p₂ (k + n)))
             (pre-le _ _ _ _ (rf _) (λ j → rf _) (k + n)))))))
        where
        ix = m + (k + n)
        r : h (k + n) ⊲ h ix
        r = tailP h st′ C.self m
        eq : (k + n) + m ≡ ix
        eq = +-comm (k + n) m

    L4′ h st w {n = n} p zero = sym~ (ur _)
    L4′ h st w {n = n} p (suc m) =
      tr~ (T (tailP h st p m) (st (m + n)) (w (suc (m + n))))
      (tr~ (⨾~ (PI (h (m + n)) (tailP h st p m) (tailP h st p m) (lg⊲ (st (m + n)) (w (suc (m + n)))) (w (m + n))) (rf~ _))
      (tr~ (⨾~ (L4′ h st w p m) (rf~ _))
           (as _ _ _)))

    Dz : ∀ {V} b → Lg b → D azero V
    Dz b lb = dif b (z⊲ b) lb

    DzT : ∀ {V} (f : ℕ → A) st w n → Dz {V} (f n) (w n) ~ dif {V} (f (n + 0)) (tailP f st (z⊲ (f 0)) n) (w (n + 0))
    DzT {V} f st w n =
      tr~ (PI (f n) (z⊲ (f n)) (subst (λ y → azero ⊲ f y) (+-identityʳ n) (tailP f st (z⊲ (f 0)) n)) (w n) (w n))
          (substD f w (+-identityʳ n) (tailP f st (z⊲ (f 0)) n))

    DzE : ∀ {V} (f : ℕ → A) st w n → R i i (Dz {V} (f n) (w n)) (Dz {V} (alim f) (st , w))
    DzE f st w n =
      tr⊑ (proj₁ (DzT f st w n)) (tr⊑ (proj₁ (L4′ f st w (z⊲ (f 0)) n)) (pre-le _ _ _ _ (rf _) (λ j → rf _) n))
```

## §4 两个下标: 对 $\le$ 单调, 值同余

```agda
  module Two {i j : I} (hi : Hy i i) (hj : Hy j j) (hij : Hy i j) where
    open One hi using (Dz; L4′; DzT; canon)
    open One hj using () renaming (DzE to DzEʲ; canon to canonʲ)

    lim-bd : ∀ {V V′} (f : ℕ → A) st w (z : D azero V′) → (∀ n → R i j (Dz {V} (f n) (w n)) z) → R i j (Dz {V} (alim f) (st , w)) z
    lim-bd f st w z h =
      lim-leP hi _ _ z (λ k → tr⊑ (proj₂ (L4′ f st w (z⊲ (f 0)) k)) (tr⊑ (proj₂ (DzT f st w k)) (h k)))

    M : ∀ {V V′} {a b} → a ≤ b → (la : Lg a) (lb : Lg b) → R i j (Dz {V} a la) (Dz {V′} b lb)
    M z≤ la lb = infl _
    M (s≤ p) la lb = ⨾-mono (M p la lb) (n1⊑ hij)
    M {b = alim f} (≤l n p) la (st , w) = tr⊑ʳ (M p la (w n)) (DzEʲ f st w n)
    M {a = alim f} (l≤ p) (st , w) lb = lim-bd f st w _ (λ n → M (p n) (w n) lb)

    cong0 : ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → proj₁ (toA z) ≤ proj₁ (toA z′) → R i j z z′
    cong0 z z′ le =
      tr⊑ (proj₂ (canon z))
      (tr⊑ʳ (⨾-mono (infl n0) (nw-l (nw-r (M le (proj₂ (toA z)) (proj₂ (toA z′))))))
            (proj₁ (canonʲ z′)))
```
