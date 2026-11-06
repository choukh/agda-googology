# 规范形论证对树类型抽象 (二): `Gen` 写一次

> 不含记号. 入口 [GenAbs](GenAbs.lagda.md). [DValCanon](DValCanon.lagda.md) 的 `Gen` 对签名 [`Sig`](GenAbsSig.lagda.md) 重写. 关系的十四条结构律与原文逐字相同, 只把 `D azero` 换成签名的 `T`, `⊲` (世界) 换成签名的 `≺`.
>
> 证明有一处改写: 原文的规范形是 `cw z` (经 `toA` 读成 `L₀` 再造差树), 要 `TI`, `DEC`, `ZL` 三条引理把 `toA` 的 $\oplus$ 拆开. 这里规范形直接是 `Dz (sum 0 z)`, 引理 `Cc` 说的是 "从底 $a$ 到 `sum a z` 的差与 $z$ 等价, 对一切第一位置与合法性证据": 情形 `⨾` 用传递引理 `T`, 情形 `nl` 直接展开 `dif` 的极限一行. 于是 `TI`, `DEC`, `ZL`, `toA`, `pts`, `⊞-fst`, `⊞-⊲`, `Lg-⊞` 都不需要. 计算方程只经 `dif≡` (目标相等的两个差等价, `PI` 的推论) 进来.
>
> 结论: `canon : Dz (sum 0 z) ~ z`, `Two.M` (对 $\le$ 单调), `Two.cong0 : sum 0 z ≤ sum 0 z′ → R i j z z′`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenAbsCanon where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-comm)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤)
open import OCF.Align.GenAbsSig using (Sig; module Ops; tailP)
```

## §1 无环

照 `DValCanon` §1.

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

## §2 参数

与 `DValCanon.Gen` 的参数逐条相同.

```agda
module Canon (σ : Sig) where
  open Sig σ
  open Ops σ using (pre; dif; val)

  module Gen {I : Set} (Hy : I → I → Set)
    (R : I → I → ∀ {V₁ V₂} → T V₁ → T V₂ → Set)
    (n1⊑ : ∀ {i j} → Hy i j → ∀ {V₁ V₂} → R i j (n1 {V₁}) (n1 {V₂}))
    (infl : ∀ {i j V₁ V₂} (z : T V₂) → R i j (n0 {V₁}) z)
    (⨾-mono : ∀ {i j V₁ V₂} {x y : T V₁} {x′ y′ : T V₂} → R i j x x′ → R i j y y′ → R i j (x ⨾ y) (x′ ⨾ y′))
    (nl-mono : ∀ {i j V₁ V₂} {d : ℕ → T V₁} {d′ : ℕ → T V₂} → (∀ n → R i j (d n) (d′ n)) → R i j (nl d) (nl d′))
    (nw-l : ∀ {i j V₀ V V₂} {p : V₀ ≺ V} {x : T V₀} {z : T V₂} → R i j x z → R i j (nw p x) z)
    (nw-r : ∀ {i j V₀ V V₁} {p : V₀ ≺ V} {x : T V₀} {z : T V₁} → R i j z x → R i j z (nw p x))
    (tr⊑ : ∀ {i j V V₃} {z z′ : T V} {z″ : T V₃} → R i i z z′ → R i j z′ z″ → R i j z z″)
    (tr⊑ʳ : ∀ {i j V V₁} {z : T V₁} {z′ z″ : T V} → R i j z z′ → R j j z′ z″ → R i j z z″)
    (unit-l : ∀ {i} → Hy i i → ∀ {V} (x : T V) → R i i (n0 ⨾ x) x × R i i x (n0 ⨾ x))
    (unit-r : ∀ {i} → Hy i i → ∀ {V} (x : T V) → R i i (x ⨾ n0) x × R i i x (x ⨾ n0))
    (assoc : ∀ {i} → Hy i i → ∀ {V} (x y z : T V) → R i i ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z)) × R i i (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z))
    (pre-le : ∀ {i j V₁ V₂} (x : T V₁) (x′ : T V₂) (d : ℕ → T V₁) (d′ : ℕ → T V₂) →
              R i j x x′ → (∀ n → R i j (d n) (d′ n)) → ∀ k → R i j (x ⨾ pre d k) (x′ ⨾ nl d′))
    (lim-leP : ∀ {i j V₁ V₂} → Hy i i → (x : T V₁) (d : ℕ → T V₁) (z : T V₂) →
               (∀ k → R i j (x ⨾ pre d k) z) → R i j (x ⨾ nl d) z)
    where

    refl⊑ : ∀ {i j} → Hy i j → ∀ {V} (z : T V) → R i j z z
    refl⊑ {i} {j} h = ind (λ z → R i j z z) (infl n0) (n1⊑ h) ⨾-mono nl-mono (λ hx → nw-l (nw-r hx))
```

## §3 单个下标

`T`, `substD`, `PI`, `PIL`, `L4′`, `Dz`, `DzT`, `DzE` 逐行照 `DValCanon` §3. 新的是 `dif≡` 与 `Cc`.

```agda
    module One {i : I} (hi : Hy i i) where
      infix 4 _~_
      _~_ : ∀ {V₁ V₂} → T V₁ → T V₂ → Set
      z ~ z′ = R i i z z′ × R i i z′ z

      rf : ∀ {V} (z : T V) → R i i z z
      rf = refl⊑ hi

      rf~ : ∀ {V} (z : T V) → z ~ z
      rf~ z = rf z , rf z

      sym~ : ∀ {V₁ V₂} {z : T V₁} {z′ : T V₂} → z ~ z′ → z′ ~ z
      sym~ (h , h′) = h′ , h

      tr~ : ∀ {V V₃} {z z′ : T V} {z″ : T V₃} → z ~ z′ → z′ ~ z″ → z ~ z″
      tr~ (a , a′) (b , b′) = tr⊑ a b , tr⊑ʳ b′ a′

      ⨾~ : ∀ {V₁ V₂} {x y : T V₁} {x′ y′ : T V₂} → x ~ x′ → y ~ y′ → (x ⨾ y) ~ (x′ ⨾ y′)
      ⨾~ (a , a′) (b , b′) = ⨾-mono a b , ⨾-mono a′ b′

      nl~ : ∀ {V₁ V₂} {d : ℕ → T V₁} {d′ : ℕ → T V₂} → (∀ n → d n ~ d′ n) → nl d ~ nl d′
      nl~ h = nl-mono (λ n → proj₁ (h n)) , nl-mono (λ n → proj₂ (h n))

      ul : ∀ {V} (x : T V) → (n0 ⨾ x) ~ x
      ul x = unit-l hi x

      ur : ∀ {V} (x : T V) → (x ⨾ n0) ~ x
      ur x = unit-r hi x

      as : ∀ {V} (x y z : T V) → ((x ⨾ y) ⨾ z) ~ (x ⨾ (y ⨾ z))
      as x y z = assoc hi x y z

      infl-r : ∀ {V} (x y : T V) → R i i x (x ⨾ y)
      infl-r x y = tr⊑ (proj₂ (ur x)) (⨾-mono (rf x) (infl y))

      T′ : ∀ {V} {a b c} (p : a ⊲ b) (q : b ⊲ c) (lc : Lg c) →
           dif {V} c (⊲-tr p q) lc ~ (dif {V} b p (lg⊲ q lc) ⨾ dif {V} c q lc)
      T′ p C.self lc = sym~ (ur _)
      T′ p (C.suc q) lc = tr~ (⨾~ (T′ p q lc) (rf~ n1)) (as _ _ _)
      T′ p (C.lim n q) (st , w) = tr~ (⨾~ (T′ p q (w n)) (rf~ _)) (as _ _ _)

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
          (tr⊑ (proj₂ (T′ (tailP h st p₁ k) r (w′ ix)))
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
        tr~ (T′ (tailP h st p m) (st (m + n)) (w (suc (m + n))))
        (tr~ (⨾~ (PI (h (m + n)) (tailP h st p m) (tailP h st p m) (lg⊲ (st (m + n)) (w (suc (m + n)))) (w (m + n))) (rf~ _))
        (tr~ (⨾~ (L4′ h st w p m) (rf~ _))
             (as _ _ _)))

      Dz : ∀ {V} b → Lg b → T V
      Dz b lb = dif b (z⊲ b) lb

      DzT : ∀ {V} (f : ℕ → A) st w n → Dz {V} (f n) (w n) ~ dif {V} (f (n + 0)) (tailP f st (z⊲ (f 0)) n) (w (n + 0))
      DzT {V} f st w n =
        tr~ (PI (f n) (z⊲ (f n)) (subst (λ y → azero ⊲ f y) (+-identityʳ n) (tailP f st (z⊲ (f 0)) n)) (w n) (w n))
            (substD f w (+-identityʳ n) (tailP f st (z⊲ (f 0)) n))

      DzE : ∀ {V} (f : ℕ → A) st w n → R i i (Dz {V} (f n) (w n)) (Dz {V} (alim f) (st , w))
      DzE f st w n =
        tr⊑ (proj₁ (DzT f st w n)) (tr⊑ (proj₁ (L4′ f st w (z⊲ (f 0)) n)) (pre-le _ _ _ _ (rf _) (λ j → rf _) n))
```

**规范形.** 目标相等的两个差等价 (`dif≡`, 由 `PI`); 从底 $a$ 走到 `sum a z` 的差与 $z$ 等价 (`Cc`, 对 $z$ 用 `ind`). 计算方程只在 `dif≡` 的第一个参数里出现.

```agda
      dif≡ : ∀ {V b b′ a} → b ≡ b′ → (p : a ⊲ b) (p′ : a ⊲ b′) (l : Lg b) (l′ : Lg b′) → dif {V} b p l ~ dif {V} b′ p′ l′
      dif≡ refl p p′ l l′ = PI _ p p′ l l′

      CP : ∀ {W₀} → T W₀ → Set
      CP z = ∀ {V} a (p : a ⊲ sum a z) (l : Lg (sum a z)) → dif {V} (sum a z) p l ~ z

      Cc : ∀ {W₀} (z : T W₀) → CP z
      Cc = ind CP c0 c1 c⨾ cl cw
        where
        c0 : ∀ {W} → CP (n0 {W})
        c0 a p l = tr~ (dif≡ (sum-n0 a) p C.self l (subst Lg (sum-n0 a) l)) (infl n0 , infl n0)
        c1 : ∀ {W} → CP (n1 {W})
        c1 a p l = tr~ (dif≡ (sum-n1 a) p (C.suc C.self) l (subst Lg (sum-n1 a) l))
                       (tr⊑ (proj₁ (ul n1)) (n1⊑ hi) , tr⊑ʳ (n1⊑ hi) (proj₂ (ul n1)))
        c⨾ : ∀ {W} {x y : T W} → CP x → CP y → CP (x ⨾ y)
        c⨾ {x = x} {y} hx hy a p l =
          tr~ (dif≡ e p (⊲-tr p₁ p₂) l l′) (tr~ (T′ p₁ p₂ l′) (⨾~ (hx a p₁ (lg⊲ p₂ l′)) (hy (sum a x) p₂ l′)))
          where
          e = sum-⨾ a x y
          l′ = subst Lg e l
          p₁ = sum-fst a x
          p₂ = sum-fst (sum a x) y
        cl : ∀ {W} {d : ℕ → T W} → (∀ n → CP (d n)) → CP (nl d)
        cl {d = d} h {V} a p l =
          tr~ (dif≡ (sum-nl a d) p (C.lim 0 p₀) l l′) (tr~ (⨾~ Z (rf~ _)) (tr~ (ul _) (nl~ E)))
          where
          l′ = subst Lg (sum-nl a d) l
          st = proj₁ l′
          w = proj₂ l′
          p₀ : a ⊲ pt a d 0
          p₀ = subst (a ⊲_) (sym (pt-z a d)) C.self
          Z : dif {V} (pt a d 0) p₀ (w 0) ~ n0 {V}
          Z = dif≡ (pt-z a d) p₀ C.self (w 0) (subst Lg (pt-z a d) (w 0))
          E′ : ∀ k → dif {V} (pt a d (suc k)) (st k) (w (suc k)) ~ d k
          E′ k = tr~ (dif≡ (pt-s a d k) (st k) (sum-fst (pt a d k) (d k)) (w (suc k)) (subst Lg (pt-s a d k) (w (suc k))))
                     (h k (pt a d k) (sum-fst (pt a d k) (d k)) _)
          E : ∀ m → dif {V} (pt a d (suc (m + 0))) (st (m + 0)) (w (suc (m + 0))) ~ d m
          E m = subst (λ j → dif {V} (pt a d (suc (m + 0))) (st (m + 0)) (w (suc (m + 0))) ~ d j) (+-identityʳ m) (E′ (m + 0))
        cw : ∀ {W₀ W} {q : W₀ ≺ W} {x : T W₀} → CP x → CP (nw q x)
        cw {q = q} {x} hx a p l =
          let (h , h′) = hx a (sum-fst a x) (subst Lg (sum-nw a q x) l)
          in tr~ (dif≡ (sum-nw a q x) p (sum-fst a x) l (subst Lg (sum-nw a q x) l)) (nw-r h , nw-l h′)

      canon : ∀ {V W₀} (z : T W₀) → Dz {V} (val z) (Lg-sum azero z tt) ~ z
      canon z = Cc z azero (z⊲ _) _
```

## §4 两个下标: 对 $\le$ 单调, 值同余

`lim-bd`, `M` 逐行照 `DValCanon` §4. `cong0` 的前提是读法的值 `sum 0 z ≤ sum 0 z′`.

```agda
    module Two {i j : I} (hi : Hy i i) (hj : Hy j j) (hij : Hy i j) where
      open One hi using (Dz; L4′; DzT; canon)
      open One hj using () renaming (DzE to DzEʲ; canon to canonʲ)

      lim-bd : ∀ {V V′} (f : ℕ → A) st w (z : T V′) → (∀ n → R i j (Dz {V} (f n) (w n)) z) → R i j (Dz {V} (alim f) (st , w)) z
      lim-bd f st w z h =
        lim-leP hi _ _ z (λ k → tr⊑ (proj₂ (L4′ f st w (z⊲ (f 0)) k)) (tr⊑ (proj₂ (DzT f st w k)) (h k)))

      M : ∀ {V V′} {a b} → a ≤ b → (la : Lg a) (lb : Lg b) → R i j (Dz {V} a la) (Dz {V′} b lb)
      M z≤ la lb = infl _
      M (s≤ p) la lb = ⨾-mono (M p la lb) (n1⊑ hij)
      M {b = alim f} (≤l n p) la (st , w) = tr⊑ʳ (M p la (w n)) (DzEʲ f st w n)
      M {a = alim f} (l≤ p) (st , w) lb = lim-bd f st w _ (λ n → M (p n) (w n) lb)

      cong0 : ∀ {W₀ W₀′} (z : T W₀) (z′ : T W₀′) → val z ≤ val z′ → R i j z z′
      cong0 {W₀} {W₀′} z z′ le =
        tr⊑ (proj₂ (canon {W₀} z)) (tr⊑ʳ (M le (Lg-sum azero z tt) (Lg-sum azero z′ tt)) (proj₁ (canonʲ {W₀′} z′)))
```
