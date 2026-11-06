# 第 1 层的值关系 (二): 第 0 层输入, 两个读数一起比

> 不含记号. 入口 [MonoPort2](MonoPort2.lagda.md). 实例 $\Lambda=2$ 里第 0 层输入的折叠. 与 [MonoPortZero](MonoPortZero.lagda.md) 的差别: 状态不只比 $T_0$ 上的值, 还比 $T_1$ 上的差 (`SRel`, `Good`); 输出两个读数一起比 (`Obs`: $T_0$ 上加底后 $\le$, $T_1$ 上 $\sqsubseteq$). 第 1 层节点上升时的链要它: 链的每一段把状态在 $T_1$ 上的差也改了, 下一段的分支又读它.
>
> - 下标 `I`: 第 0 层的动作带着自己的单调证明 (同 `DValKn`), 所以输出的自比可以对树归纳得出 (`rO`), 结构律不必另带自比.
> - 结构律 (§2, §3), 套 `DValCanon.Gen` (§4, 经 `ofS` 拉回), 得 **`cong0₂`**: 第 0 层值 $\le$ ⇒ 两个读数都可比. **`chain₂`**: 链的极限对起点单调 (起点: 底 $\le$, 状态 `SRel`, 两边 `Good`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.MonoPort2Zero {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (D; hz; hs; AccY; accL; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst)
import OCF.Align.SumOneTree as SO
import OCF.Align.DValCanon as DC
open import OCF.Align.MonoPortBridge using (toS; ofS; val; toV; smono)
open import OCF.Align.MonoPort2Rel lW
```

## §1 动作, 下标, 关系

```agda
Act₀ : Set
Act₀ = P.Ig hz W

ac₀ : AccY hz
ac₀ = accL hz

R₀ : Act₀ → ∀ {V} → D hz V → V ⊲ W → D hz W → P.St W → P.Df W
R₀ A₀ z q w Y = P.Run ac₀ z q lW k0 A₀ w Y

HA0 : Act₀ → Act₀ → Set
HA0 A₀ A₁ = ∀ w w′ c c′ Y Y′ → val w ≤ val w′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (A₀ C.self lW w Y) (A₁ C.self lW w′ Y′)

I : Set
I = Σ Act₀ (λ (A₀ : Act₀) → HA0 A₀ A₀)

Hy : I → I → Set
Hy i j = HA0 (proj₁ i) (proj₁ j)

Sem0 : Act₀ → Act₀ → ∀ {V₁ V₂} → D hz V₁ → D hz V₂ → Set
Sem0 A₀ A₁ z z′ = ∀ q q′ w w′ c c′ Y Y′ → val w ≤ val w′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ →
                  Obs c c′ (R₀ A₀ z q w Y) (R₀ A₁ z′ q′ w′ Y′)

Rl : I → I → ∀ {V₁ V₂} → D hz V₁ → D hz V₂ → Set
Rl i j z z′ = Sem0 (proj₁ i) (proj₁ j) z z′ × (val z ≤ val z′)

-- 自比的 T₁ 输出 (取底 0)
rf₁ : ∀ {A₀ : Act₀} {V} {z : D hz V} → Sem0 A₀ A₀ z z → ∀ q w Y → Good Y → Rf (o₁ (R₀ A₀ z q w Y))
rf₁ h q w Y g = proj₂ (h q q w w azero azero Y Y (≤-refl _) g g (sr g) z≤)

rPre : ∀ {e : ℕ → D₁} → (∀ n → Rf (e n)) → ∀ k → Rf (preL e k)
rPre r zero = n0⊑
rPre r (suc k) = ⨾⊑ (rPre r k) (rPre r k) (rPre r k) (r k)

preV : ∀ {V₁ V₂} {b b′} (d : ℕ → D hz V₁) (d′ : ℕ → D hz V₂) → b ≤ b′ → (∀ n → val (d n) ≤ val (d′ n)) → ∀ k → sum b (preL d k) ≤ pt b′ d′ k
preV d d′ hb h zero = hb
preV {b = b} d d′ hb h (suc k) = smono {b = sum b (preL d k)} {x = d k} (preV d d′ hb h k) (h k)

preV′ : ∀ {V₁ V₂} {b b′} (d : ℕ → D hz V₁) (d′ : ℕ → D hz V₂) → b ≤ b′ → (∀ n → val (d n) ≤ val (d′ n)) → ∀ k → pt b d k ≤ sum b′ (preL d′ k)
preV′ d d′ hb h zero = hb
preV′ {b′ = b′} d d′ hb h (suc k) = smono {b′ = sum b′ (preL d′ k)} {x′ = d′ k} (preV′ d d′ hb h k) (h k)

ptV : ∀ {V₁ V₂} {b b′} (d : ℕ → D hz V₁) (d′ : ℕ → D hz V₂) → b ≤ b′ → (∀ n → val (d n) ≤ val (d′ n)) → ∀ k → pt b d k ≤ pt b′ d′ k
ptV d d′ hb h zero = hb
ptV d d′ hb h (suc k) = smono (ptV d d′ hb h k) (h k)
```

## §2 和的结构律

```agda
module _ {i j : I} where
  private
    A₀ = proj₁ i
    A₁ = proj₁ j

  semi⨾ : ∀ {V₁ V₂} {x y : D hz V₁} {x′ y′ : D hz V₂} → Sem0 A₀ A₀ x x → Sem0 A₁ A₁ x′ x′ →
          Rl i j x x′ → Rl i j y y′ → Rl i j (x ⨾ y) (x′ ⨾ y′)
  semi⨾ {x = x} {y} {x′} {y′} rx rx′ (hx , vx) (hy , vy) = S , smono vx vy
    where
    S : Sem0 A₀ A₁ (x ⨾ y) (x′ ⨾ y′)
    S q q′ w w′ c c′ Y Y′ hw g g′ s cb =
      let ox = hx q q′ w w′ c c′ Y Y′ hw g g′ s cb
          os = hx q q′ w w′ (vY Y) (vY Y′) Y Y′ hw g g′ s (proj₁ s)
          r  = rf₁ rx q w Y g
          r′ = rf₁ rx′ q′ w′ Y′ g′
          oy = hy q q′ (w ⨾ nw q x) (w′ ⨾ nw q′ x′) _ _ (Y ⊕ R₀ A₀ x q w Y) (Y′ ⊕ R₀ A₁ x′ q′ w′ Y′)
                  (smono {b = val w} {b′ = val w′} {x = x} {x′ = x′} hw vx) (G⊕ g r) (G⊕ g′ r′) (S⊕ g g′ s os) (proj₁ ox)
      in proj₁ oy , ⨾⊑ r r′ (proj₂ ox) (proj₂ oy)

  semiNl : ∀ {V₁ V₂} {d : ℕ → D hz V₁} {d′ : ℕ → D hz V₂} → (∀ n → Sem0 A₀ A₀ (d n) (d n)) → (∀ n → Sem0 A₁ A₁ (d′ n) (d′ n)) →
           (∀ n → Rl i j (d n) (d′ n)) → Rl i j (nl d) (nl d′)
  semiNl {d = d} {d′} rd rd′ hd = S , l≤ (λ n → ≤l n (ptV d d′ z≤ (λ m → proj₂ (hd m)) n))
    where
    S : Sem0 A₀ A₁ (nl d) (nl d′)
    S q q′ w w′ c c′ Y Y′ hw g g′ s cb = l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (proj₂ (go n)))))) , nl⊑ rE rE′ hE
      where
      Q  = λ n → P.Rpt ac₀ d q lW k0 A₀ w Y n
      Q′ = λ n → P.Rpt ac₀ d′ q′ lW k0 A₁ w′ Y′ n
      E  = λ n → R₀ A₀ (d n) q (proj₁ (Q n)) (proj₂ (Q n))
      E′ = λ n → R₀ A₁ (d′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n))
      go : ∀ n → (val (proj₁ (Q n)) ≤ val (proj₁ (Q′ n))) × (Good (proj₂ (Q n)) × (Good (proj₂ (Q′ n)) ×
                 (SRel (proj₂ (Q n)) (proj₂ (Q′ n)) × (pt c (λ m → o₀ (E m)) n ≤ pt c′ (λ m → o₀ (E′ m)) n))))
      go zero = hw , (g , (g′ , (s , cb)))
      go (suc n) =
        let (a , (b , (b′ , (e , f)))) = go n
            h = λ e₁ e₂ (eb : e₁ ≤ e₂) → proj₁ (hd n) q q′ (proj₁ (Q n)) (proj₁ (Q′ n)) e₁ e₂ (proj₂ (Q n)) (proj₂ (Q′ n)) a b b′ e eb
        in smono a (proj₂ (hd n)) ,
           (G⊕ b (rf₁ (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) b) ,
            (G⊕ b′ (rf₁ (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) b′) ,
             (S⊕ b b′ e (h _ _ (proj₁ e)) , proj₁ (h _ _ f))))
      rE : ∀ n → Rf (o₁ (E n))
      rE n = rf₁ (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) (proj₁ (proj₂ (go n)))
      rE′ : ∀ n → Rf (o₁ (E′ n))
      rE′ n = rf₁ (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) (proj₁ (proj₂ (proj₂ (go n))))
      hE : ∀ n → o₁ (E n) ⊑ o₁ (E′ n)
      hE n = let (a , (b , (b′ , (e , f)))) = go n in
        proj₂ (proj₁ (hd n) q q′ (proj₁ (Q n)) (proj₁ (Q′ n)) azero azero (proj₂ (Q n)) (proj₂ (Q′ n)) a b b′ e z≤)

  nw-l : ∀ {V₀ V V₂} {p : V₀ ⊲ V} {x : D hz V₀} {z : D hz V₂} → Rl i j x z → Rl i j (nw p x) z
  nw-l {p = p} (h , a) = (λ q q′ → h (C.⊲-tr p q) q′) , a

  nw-r : ∀ {V₀ V V₁} {p : V₀ ⊲ V} {x : D hz V₀} {z : D hz V₁} → Rl i j z x → Rl i j z (nw p x)
  nw-r {p = p} (h , a) = (λ q q′ → h q (C.⊲-tr p q′)) , a

  n1L : Hy i j → ∀ {V₁ V₂} → Rl i j (n1 {W = V₁}) (n1 {W = V₂})
  n1L h = (λ q q′ w w′ c c′ Y Y′ hw g g′ s cb → h w w′ c c′ Y Y′ hw g g′ s cb) , ≤-refl _

  infl : ∀ {V₁ V₂} (z : D hz V₂) → Rl i j (n0 {W = V₁}) z
  infl z = (λ q q′ w w′ c c′ Y Y′ hw g g′ s cb → ≤-trans cb (⊲→≤ (sum-fst c′ (o₀ (R₀ A₁ z q′ w′ Y′)))) , n0⊑) , z≤

  tr⊑ : ∀ {V V₃} {z z′ : D hz V} {z″ : D hz V₃} → Rl i i z z′ → Rl i j z′ z″ → Rl i j z z″
  tr⊑ (h , a) (h′ , a′) =
    (λ q q″ w w″ c c″ Y Y″ hw g g″ s cb →
       let o = h q q w w c c Y Y (≤-refl _) g g (sr g) (≤-refl c)
           o′ = h′ q q″ w w″ c c″ Y Y″ hw g g″ s cb
       in ≤-trans (proj₁ o) (proj₁ o′) , tr (proj₂ o) (proj₂ o′)) ,
    ≤-trans a a′

  tr⊑ʳ : ∀ {V V₁} {z : D hz V₁} {z′ z″ : D hz V} → Rl i j z z′ → Rl j j z′ z″ → Rl i j z z″
  tr⊑ʳ (h , a) (h′ , a′) =
    (λ q q″ w w″ c c″ Y Y″ hw g g″ s cb →
       let o = h q q″ w w″ c c″ Y Y″ hw g g″ s cb
           o′ = h′ q″ q″ w″ w″ c″ c″ Y″ Y″ (≤-refl _) g″ g″ (sr g″) (≤-refl c″)
       in ≤-trans (proj₁ o) (proj₁ o′) , tr (proj₂ o) (proj₂ o′)) ,
    ≤-trans a a′

-- 自比, 对树归纳
rO : ∀ (i : I) {V} (z : D hz V) → Rl i i z z
rO i n0 = infl {i} {i} n0
rO i n1 = n1L {i} {i} (proj₂ i)
rO i (x ⨾ y) = semi⨾ {i} {i} (proj₁ (rO i x)) (proj₁ (rO i x)) (rO i x) (rO i y)
rO i (nl d) = semiNl {i} {i} (λ n → proj₁ (rO i (d n))) (λ n → proj₁ (rO i (d n))) (λ n → rO i (d n))
rO i (ni () u)
rO i (nκ () u)
rO i (nw p x) = nw-l {i} {i} (nw-r {i} {i} (rO i x))

module _ {i j : I} where
  ⨾-mono : ∀ {V₁ V₂} {x y : D hz V₁} {x′ y′ : D hz V₂} → Rl i j x x′ → Rl i j y y′ → Rl i j (x ⨾ y) (x′ ⨾ y′)
  ⨾-mono {x = x} {x′ = x′} = semi⨾ (proj₁ (rO i x)) (proj₁ (rO j x′))

  nl-mono : ∀ {V₁ V₂} {d : ℕ → D hz V₁} {d′ : ℕ → D hz V₂} → (∀ n → Rl i j (d n) (d′ n)) → Rl i j (nl d) (nl d′)
  nl-mono {d = d} {d′} = semiNl (λ n → proj₁ (rO i (d n))) (λ n → proj₁ (rO j (d′ n)))
```

## §3 单位, 结合, 极限

```agda
module _ (i : I) where
  private
    A₀ = proj₁ i
    r = λ {V} (x : D hz V) → proj₁ (rO i x)

  unit-l : ∀ {V} (x : D hz V) → Rl i i (n0 ⨾ x) x × Rl i i x (n0 ⨾ x)
  unit-l x =
    ((λ q q′ w w′ c c′ Y Y′ hw g g′ s cb →
        let o = r x q q′ (w ⨾ nw q n0) w′ c c′ (Y ⊕ P.zeroD) Y′ hw (G⊕0 g) g′ (S0ˡ s) cb in proj₁ o , u0ˡ (proj₂ o)) , ≤-refl _) ,
    ((λ q q′ w w′ c c′ Y Y′ hw g g′ s cb →
        let o = r x q q′ w (w′ ⨾ nw q′ n0) c c′ Y (Y′ ⊕ P.zeroD) hw g (G⊕0 g′) (S0ʳ s) cb in proj₁ o , u0ʳ (proj₂ o)) , ≤-refl _)

  unit-r : ∀ {V} (x : D hz V) → Rl i i (x ⨾ n0) x × Rl i i x (x ⨾ n0)
  unit-r x =
    ((λ q q′ w w′ c c′ Y Y′ hw g g′ s cb → let o = r x q q′ w w′ c c′ Y Y′ hw g g′ s cb in proj₁ o , u1ˡ (proj₂ o)) , ≤-refl _) ,
    ((λ q q′ w w′ c c′ Y Y′ hw g g′ s cb → let o = r x q q′ w w′ c c′ Y Y′ hw g g′ s cb in proj₁ o , u1ʳ (proj₂ o)) , ≤-refl _)

  -- 三段 x, y, z: 两边各自走 x, y 的数据
  module Three {V} (x y z : D hz V) q q′ w w′ Y Y′ (hw : val w ≤ val w′) (g : Good Y) (g′ : Good Y′) (s : SRel Y Y′) where
    Rx = R₀ A₀ x q w Y
    Rx′ = R₀ A₀ x q′ w′ Y′
    Ry = R₀ A₀ y q (w ⨾ nw q x) (Y ⊕ Rx)
    Ry′ = R₀ A₀ y q′ (w′ ⨾ nw q′ x) (Y′ ⊕ Rx′)
    rX = rf₁ (r x) q w Y g
    rX′ = rf₁ (r x) q′ w′ Y′ g′
    hwx : val (w ⨾ nw q x) ≤ val (w′ ⨾ nw q′ x)
    hwx = smono {b = val w} {b′ = val w′} {x = x} {x′ = x} hw (≤-refl _)
    gx = G⊕ {Y} {Rx} g rX
    gx′ = G⊕ {Y′} {Rx′} g′ rX′
    sx : SRel (Y ⊕ Rx) (Y′ ⊕ Rx′)
    sx = S⊕ g g′ s (r x q q′ w w′ (vY Y) (vY Y′) Y Y′ hw g g′ s (proj₁ s))
    rY = rf₁ (r y) q (w ⨾ nw q x) (Y ⊕ Rx) gx
    rY′ = rf₁ (r y) q′ (w′ ⨾ nw q′ x) (Y′ ⊕ Rx′) gx′
    hwxy : val (w ⨾ nw q (x ⨾ y)) ≤ val ((w′ ⨾ nw q′ x) ⨾ nw q′ y)
    hwxy = smono {b = val (w ⨾ nw q x)} {b′ = val (w′ ⨾ nw q′ x)} {x = y} {x′ = y} hwx (≤-refl _)
    hwxy′ : val ((w ⨾ nw q x) ⨾ nw q y) ≤ val (w′ ⨾ nw q′ (x ⨾ y))
    hwxy′ = smono {b = val (w ⨾ nw q x)} {b′ = val (w′ ⨾ nw q′ x)} {x = y} {x′ = y} hwx (≤-refl _)
    oX = λ c c′ (cb : c ≤ c′) → r x q q′ w w′ c c′ Y Y′ hw g g′ s cb
    oY = λ c c′ (cb : c ≤ c′) → r y q q′ (w ⨾ nw q x) (w′ ⨾ nw q′ x) c c′ (Y ⊕ Rx) (Y′ ⊕ Rx′) hwx gx gx′ sx cb
    -- y 走完的状态: 一起加 (S1) 与分开加 (S2)
    S1 = Y ⊕ (Rx P.⨾ᴰ Ry)
    S2′ = (Y′ ⊕ Rx′) ⊕ Ry′
    S2 = (Y ⊕ Rx) ⊕ Ry
    S1′ = Y′ ⊕ (Rx′ P.⨾ᴰ Ry′)
    gS1 = G⨾ᴰ {Y} {Rx} {Ry} g rX rY
    gS2′ = G⊕ {Y′ ⊕ Rx′} {Ry′} gx′ rY′
    gS2 = G⊕ {Y ⊕ Rx} {Ry} gx rY
    gS1′ = G⨾ᴰ {Y′} {Rx′} {Ry′} g′ rX′ rY′
    -- d₁Y ⨾ (Ox ⨾ Oy) 对 d₁Y′ ⨾ (Ox′ ⨾ Oy′)
    inner : (d₁ Y ⨾ (o₁ Rx ⨾ o₁ Ry)) ⊑ (d₁ Y′ ⨾ (o₁ Rx′ ⨾ o₁ Ry′))
    inner = ⨾⊑ g g′ (proj₂ s) (⨾⊑ rX rX′ (proj₂ (oX azero azero z≤)) (proj₂ (oY azero azero z≤)))
    s12 : SRel S1 S2′
    s12 = proj₁ (oY (sum (vY Y) (o₀ Rx)) (sum (vY Y′) (o₀ Rx′)) (proj₁ (oX (vY Y) (vY Y′) (proj₁ s)))) ,
          asʳ′ g′ rX′ rY′ inner
    s21 : SRel S2 S1′
    s21 = proj₁ (oY (sum (vY Y) (o₀ Rx)) (sum (vY Y′) (o₀ Rx′)) (proj₁ (oX (vY Y) (vY Y′) (proj₁ s)))) ,
          asˡ g rX rY inner

  assoc : ∀ {V} (x y z : D hz V) → Rl i i ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z)) × Rl i i (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
  assoc x y z =
    ((λ q q′ w w′ c c′ Y Y′ hw g g′ s cb →
       let open Three x y z q q′ w w′ Y Y′ hw g g′ s
           oz = r z q q′ (w ⨾ nw q (x ⨾ y)) ((w′ ⨾ nw q′ x) ⨾ nw q′ y) _ _ S1 S2′ hwxy gS1 gS2′ s12
                  (proj₁ (oY _ _ (proj₁ (oX c c′ cb))))
           rZ′ = rf₁ (r z) q′ ((w′ ⨾ nw q′ x) ⨾ nw q′ y) S2′ gS2′
       in proj₁ oz ,
          asʳ rX′ rY′ rZ′ (⨾⊑ (⨾⊑ rX rX rX rY) (⨾⊑ rX′ rX′ rX′ rY′) (⨾⊑ rX rX′ (proj₂ (oX c c′ cb)) (proj₂ (oY _ _ (proj₁ (oX c c′ cb))))) (proj₂ oz))) ,
     ≤-refl _) ,
    ((λ q q′ w w′ c c′ Y Y′ hw g g′ s cb →
       let open Three x y z q q′ w w′ Y Y′ hw g g′ s
           oz = r z q q′ ((w ⨾ nw q x) ⨾ nw q y) (w′ ⨾ nw q′ (x ⨾ y)) _ _ S2 S1′ hwxy′ gS2 gS1′ s21
                  (proj₁ (oY _ _ (proj₁ (oX c c′ cb))))
           rZ = rf₁ (r z) q ((w ⨾ nw q x) ⨾ nw q y) S2 gS2
       in proj₁ oz ,
          asˡ′ rX rY rZ (⨾⊑ (⨾⊑ rX rX rX rY) (⨾⊑ rX′ rX′ rX′ rY′) (⨾⊑ rX rX′ (proj₂ (oX c c′ cb)) (proj₂ (oY _ _ (proj₁ (oX c c′ cb))))) (proj₂ oz))) ,
     ≤-refl _)
```

**部分和与极限.** 左边走 `x ⨾ preL d k`, 右边走 `x′ ⨾ nl d′`: 前缀的状态是一次加上的 (`Z ⊕ Rp n`), `Rpt` 的状态是逐段加的, 由结合律逐段对上; `T₁` 上的输出用 `PreOut.O≡` 改写成各段输出的部分和, 再用 `pre⊑`.

```agda
module _ {i j : I} where
  private
    A₀ = proj₁ i
    A₁ = proj₁ j

  pre-le : ∀ {V₁ V₂} (x : D hz V₁) (x′ : D hz V₂) (d : ℕ → D hz V₁) (d′ : ℕ → D hz V₂) →
           Rl i j x x′ → (∀ n → Rl i j (d n) (d′ n)) → ∀ k → Rl i j (x ⨾ preL d k) (x′ ⨾ nl d′)
  pre-le {V₁} {V₂} x x′ d d′ (hx , vx) hd k = S , ≤l k (preV d d′ vx (λ m → proj₂ (hd m)) k)
    where
    S : Sem0 A₀ A₁ (x ⨾ preL d k) (x′ ⨾ nl d′)
    S q q′ w w′ c c′ Y Y′ hw g g′ s cb =
      ≤l k (proj₂ (proj₂ (proj₂ (go k)))) ,
      subst (λ t → (o₁ Rx ⨾ t) ⊑ (o₁ Rx′ ⨾ nl (λ n → o₁ (E′ n)))) (sym (L.O≡ k))
            (pre⊑ rX rX′ rE rE′ (proj₂ ox) hE k)
      where
      Rx = R₀ A₀ x q w Y
      Rx′ = R₀ A₁ x′ q′ w′ Y′
      ox = hx q q′ w w′ c c′ Y Y′ hw g g′ s cb
      rX = rf₁ (proj₁ (rO i x)) q w Y g
      rX′ = rf₁ (proj₁ (rO j x′)) q′ w′ Y′ g′
      Z = Y ⊕ Rx
      Z′ = Y′ ⊕ Rx′
      w₁ = w ⨾ nw q x
      w₁′ = w′ ⨾ nw q′ x′
      gZ : Good Z
      gZ = G⊕ {Y} {Rx} g rX
      gZ′ : Good Z′
      gZ′ = G⊕ {Y′} {Rx′} g′ rX′
      sZ : SRel Z Z′
      sZ = S⊕ g g′ s (hx q q′ w w′ (vY Y) (vY Y′) Y Y′ hw g g′ s (proj₁ s))
      module L = PreOut ac₀ k0 A₀ d q w₁ Z
      Q′ = λ n → P.Rpt ac₀ d′ q′ lW k0 A₁ w₁′ Z′ n
      E′ = λ n → R₀ A₁ (d′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n))
      gL : ∀ n → Good (Z ⊕ L.Rp n)
      gL n = G⊕ {Z} {L.Rp n} gZ (rf₁ (proj₁ (rO i (preL d n))) q w₁ Z gZ)
      b₁ = sum c (o₀ Rx)
      b₁′ = sum c′ (o₀ Rx′)
      go : ∀ n → (val (w₁ ⨾ nw q (preL d n)) ≤ val (proj₁ (Q′ n))) × (Good (proj₂ (Q′ n)) ×
                 (SRel (Z ⊕ L.Rp n) (proj₂ (Q′ n)) × (sum b₁ (o₀ (L.Rp n)) ≤ pt b₁′ (λ m → o₀ (E′ m)) n)))
      go zero = smono {b = val w} {b′ = val w′} {x = x} {x′ = x′} hw vx , (gZ′ , (S0ˡ sZ , proj₁ ox))
      go (suc n) =
        let (a , (gr , (e , f))) = go n
            h = λ e₁ e₂ (eb : e₁ ≤ e₂) → proj₁ (hd n) q q′ (w₁ ⨾ nw q (preL d n)) (proj₁ (Q′ n)) e₁ e₂ (Z ⊕ L.Rp n) (proj₂ (Q′ n)) a (gL n) gr e eb
            rEn = rf₁ (proj₁ (rO i (d n))) q (w₁ ⨾ nw q (preL d n)) (Z ⊕ L.Rp n) (gL n)
            rRp = rf₁ (proj₁ (rO i (preL d n))) q w₁ Z gZ
        in smono {b = val (w₁ ⨾ nw q (preL d n))} {b′ = val (proj₁ (Q′ n))} {x = d n} {x′ = d′ n} a (proj₂ (hd n)) ,
           (G⊕ gr (rf₁ (proj₁ (rO j (d′ n))) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) gr) ,
            ((proj₁ (h _ _ (proj₁ e)) , asˡ′ gZ rRp rEn (⨾⊑ (gL n) gr (proj₂ e) (proj₂ (h azero azero z≤)))) ,
             proj₁ (h _ _ f)))
      rE : ∀ n → Rf (o₁ (L.Ek n))
      rE n = rf₁ (proj₁ (rO i (d n))) q (w₁ ⨾ nw q (preL d n)) (Z ⊕ L.Rp n) (gL n)
      rE′ : ∀ n → Rf (o₁ (E′ n))
      rE′ n = rf₁ (proj₁ (rO j (d′ n))) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) (proj₁ (proj₂ (go n)))
      hE : ∀ n → o₁ (L.Ek n) ⊑ o₁ (E′ n)
      hE n = let (a , (gr , (e , f))) = go n in
        proj₂ (proj₁ (hd n) q q′ (w₁ ⨾ nw q (preL d n)) (proj₁ (Q′ n)) azero azero (Z ⊕ L.Rp n) (proj₂ (Q′ n)) a (gL n) gr e z≤)

  lim-leP : Hy i i → ∀ {V₁ V₂} (x : D hz V₁) (d : ℕ → D hz V₁) (z : D hz V₂) →
            (∀ k → Rl i j (x ⨾ preL d k) z) → Rl i j (x ⨾ nl d) z
  lim-leP _ x d z hk = S , l≤ (λ k → ≤-trans (preV′ d d (≤-refl (val x)) (λ m → ≤-refl _) k) (proj₂ (hk k)))
    where
    S : Sem0 A₀ A₁ (x ⨾ nl d) z
    S q q′ w w′ c c′ Y Y′ hw g g′ s cb =
      l≤ (λ k → ≤-trans (proj₂ (proj₂ (proj₂ (go k)))) (proj₁ (proj₁ (hk k) q q′ w w′ c c′ Y Y′ hw g g′ s cb))) ,
      lim⊑ rX rEL (λ k → tr (⨾⊑ rX rX rX (PL k))
                            (subst (λ t → (o₁ Rx ⨾ t) ⊑ o₁ (R₀ A₁ z q′ w′ Y′)) (L.O≡ k) (proj₂ (proj₁ (hk k) q q′ w w′ c c′ Y Y′ hw g g′ s cb))))
      where
      Rx = R₀ A₀ x q w Y
      rX = rf₁ (proj₁ (rO i x)) q w Y g
      Z = Y ⊕ Rx
      w₁ = w ⨾ nw q x
      gZ : Good Z
      gZ = G⊕ {Y} {Rx} g rX
      module L = PreOut ac₀ k0 A₀ d q w₁ Z
      Q = λ n → P.Rpt ac₀ d q lW k0 A₀ w₁ Z n
      EL = λ n → R₀ A₀ (d n) q (proj₁ (Q n)) (proj₂ (Q n))
      gL : ∀ n → Good (Z ⊕ L.Rp n)
      gL n = G⊕ {Z} {L.Rp n} gZ (rf₁ (proj₁ (rO i (preL d n))) q w₁ Z gZ)
      b₁ = sum c (o₀ Rx)
      rd = λ n → proj₁ (rO i (d n))
      go : ∀ n → (val (proj₁ (Q n)) ≤ val (w₁ ⨾ nw q (preL d n))) × (Good (proj₂ (Q n)) ×
                 (SRel (proj₂ (Q n)) (Z ⊕ L.Rp n) × (pt b₁ (λ m → o₀ (EL m)) n ≤ sum b₁ (o₀ (L.Rp n)))))
      go zero = ≤-refl _ , (gZ , (S0ʳ (sr gZ) , ≤-refl _))
      go (suc n) =
        let (a , (gq , (e , f))) = go n
            h = λ e₁ e₂ (eb : e₁ ≤ e₂) → rd n q q (proj₁ (Q n)) (w₁ ⨾ nw q (preL d n)) e₁ e₂ (proj₂ (Q n)) (Z ⊕ L.Rp n) a gq (gL n) e eb
            rEn = rf₁ (rd n) q (w₁ ⨾ nw q (preL d n)) (Z ⊕ L.Rp n) (gL n)
            rRp = rf₁ (proj₁ (rO i (preL d n))) q w₁ Z gZ
        in smono {b = val (proj₁ (Q n))} {b′ = val (w₁ ⨾ nw q (preL d n))} {x = d n} {x′ = d n} a (≤-refl _) ,
           (G⊕ gq (rf₁ (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) gq) ,
            ((proj₁ (h _ _ (proj₁ e)) , asʳ gZ rRp rEn (⨾⊑ gq (gL n) (proj₂ e) (proj₂ (h azero azero z≤)))) ,
             proj₁ (h _ _ f)))
      rEL : ∀ n → Rf (o₁ (EL n))
      rEL n = rf₁ (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) (proj₁ (proj₂ (go n)))
      hEL : ∀ n → o₁ (EL n) ⊑ o₁ (L.Ek n)
      hEL n = let (a , (gq , (e , f))) = go n in
        proj₂ (rd n q q (proj₁ (Q n)) (w₁ ⨾ nw q (preL d n)) azero azero (proj₂ (Q n)) (Z ⊕ L.Rp n) a gq (gL n) e z≤)
      rEk : ∀ n → Rf (o₁ (L.Ek n))
      rEk n = rf₁ (rd n) q (w₁ ⨾ nw q (preL d n)) (Z ⊕ L.Rp n) (gL n)
      PL : ∀ k → preL (λ n → o₁ (EL n)) k ⊑ preL (λ n → o₁ (L.Ek n)) k
      PL zero = n0⊑
      PL (suc k) = ⨾⊑ (rPre rEL k) (rPre rEk k) (PL k) (hEL k)
```

## §4 规范形: 套 `Gen`

```agda
ofS-preL : ∀ {V} (d : ℕ → SO.D azero V) k → ofS (DC.pre d k) ≡ preL (λ n → ofS (d n)) k
ofS-preL d zero = refl
ofS-preL d (suc k) = cong (λ t → t ⨾ ofS (d k)) (ofS-preL d k)

Rˢ : I → I → ∀ {V₁ V₂} → SO.D azero V₁ → SO.D azero V₂ → Set
Rˢ i j z z′ = Rl i j (ofS z) (ofS z′)

private
  module GG = DC.Gen Hy Rˢ
    (λ {i} {j} h → n1L {i} {j} h) (λ {i} {j} z → infl {i} {j} (ofS z))
    (λ {i} {j} → ⨾-mono {i} {j}) (λ {i} {j} h → nl-mono {i} {j} h) (λ {i} {j} → nw-l {i} {j}) (λ {i} {j} → nw-r {i} {j})
    (λ {i} {j} → tr⊑ {i} {j}) (λ {i} {j} → tr⊑ʳ {i} {j})
    (λ {i} _ x → unit-l i (ofS x)) (λ {i} _ x → unit-r i (ofS x)) (λ {i} _ x y z → assoc i (ofS x) (ofS y) (ofS z))
    (λ {i} {j} x x′ d d′ hx hd k →
       subst (λ t → Rl i j (ofS x ⨾ t) (ofS x′ ⨾ nl (λ n → ofS (d′ n)))) (sym (ofS-preL d k))
             (pre-le {i} {j} (ofS x) (ofS x′) (λ n → ofS (d n)) (λ n → ofS (d′ n)) hx hd k))
    (λ {i} {j} h x d z hk′ →
       lim-leP {i} {j} h (ofS x) (λ n → ofS (d n)) (ofS z)
         (λ k → subst (λ t → Rl i j (ofS x ⨾ t) (ofS z)) (ofS-preL d k) (hk′ k)))

rt  : ∀ (i : I) {V} (z : D hz V) → Rl i i z (ofS (toS z))
rt′ : ∀ (i : I) {V} (z : D hz V) → Rl i i (ofS (toS z)) z
rt i n0 = infl {i} {i} n0
rt i n1 = n1L {i} {i} (proj₂ i)
rt i (x ⨾ y) = ⨾-mono {i} {i} (rt i x) (rt i y)
rt i (nl d) = nl-mono {i} {i} (λ n → rt i (d n))
rt i (ni () u)
rt i (nκ () u)
rt i (nw p x) = nw-l {i} {i} (nw-r {i} {i} (rt i x))
rt′ i n0 = infl {i} {i} n0
rt′ i n1 = n1L {i} {i} (proj₂ i)
rt′ i (x ⨾ y) = ⨾-mono {i} {i} (rt′ i x) (rt′ i y)
rt′ i (nl d) = nl-mono {i} {i} (λ n → rt′ i (d n))
rt′ i (ni () u)
rt′ i (nκ () u)
rt′ i (nw p x) = nw-l {i} {i} (nw-r {i} {i} (rt′ i x))

-- 值同余: 两个读数一起
cong0₂ : ∀ (i j : I) → Hy i j → ∀ {W₀ W₀′} (z : D hz W₀) (z′ : D hz W₀′) → val z ≤ val z′ → Rl i j z z′
cong0₂ i j hx z z′ le =
  tr⊑ {i} {j} (rt i z) (tr⊑ʳ {i} {j} (GG.Two.cong0 {i} {j} (proj₂ i) (proj₂ j) hx (toS z) (toS z′) (toV z z′ le)) (rt′ j z′))
```

## §5 链

第 1 层节点在 $T_0$ 上上升时的链 (`Chn`, 第 0 层的点). 不变量六件: 上下文值, 链点值, 两边状态 `Good`, 状态 `SRel`, 部分和.

```agda
module _ (i j : I) (hx : Hy i j) where
  private
    A₀ = proj₁ i
    A₁ = proj₁ j

  CC : Act₀ → P.St W → ℕ → D hz W × (D hz W × P.St W)
  CC A₂ Y = P.Chn ac₀ k0 lW A₂ Y

  segs : Act₀ → P.St W → ℕ → D hz W
  segs A₂ Y n = o₀ (R₀ A₂ (proj₁ (proj₂ (CC A₂ Y n))) C.self (proj₁ (CC A₂ Y n)) (proj₂ (proj₂ (CC A₂ Y n))))

  chain₂ : ∀ (Y Y′ : P.St W) b b′ → Good Y → Good Y′ → SRel Y Y′ → b ≤ b′ → sum b (nl (segs A₀ Y)) ≤ sum b′ (nl (segs A₁ Y′))
  chain₂ Y Y′ b b′ g g′ s cb = l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (go n)))))))
    where
    c  = λ n → proj₁ (CC A₀ Y n)
    c′ = λ n → proj₁ (CC A₁ Y′ n)
    δ  = λ n → proj₁ (proj₂ (CC A₀ Y n))
    δ′ = λ n → proj₁ (proj₂ (CC A₁ Y′ n))
    Yn  = λ n → proj₂ (proj₂ (CC A₀ Y n))
    Yn′ = λ n → proj₂ (proj₂ (CC A₁ Y′ n))
    go : ∀ n → (val (c n) ≤ val (c′ n)) × ((val (δ n) ≤ val (δ′ n)) × (Good (Yn n) × (Good (Yn′ n) ×
               (SRel (Yn n) (Yn′ n) × (pt b (segs A₀ Y) n ≤ pt b′ (segs A₁ Y′) n)))))
    go zero = z≤ , (proj₁ s , (g , (g′ , (s , cb))))
    go (suc n) =
      let (gc , (gd , (gy , (gy′ , (sy , gb))))) = go n
          h = λ e₁ e₂ (eb : e₁ ≤ e₂) → proj₁ (cong0₂ i j hx (δ n) (δ′ n) gd) C.self C.self (c n) (c′ n) e₁ e₂ (Yn n) (Yn′ n) gc gy gy′ sy eb
      in smono gc gd ,
         (proj₁ (h azero azero z≤) ,
          (G⊕ gy (rf₁ (proj₁ (rO i (δ n))) C.self (c n) (Yn n) gy) ,
           (G⊕ gy′ (rf₁ (proj₁ (rO j (δ′ n))) C.self (c′ n) (Yn′ n) gy′) ,
            (S⊕ gy gy′ sy (h _ _ (proj₁ sy)) ,
             proj₁ (h _ _ gb)))))
```
