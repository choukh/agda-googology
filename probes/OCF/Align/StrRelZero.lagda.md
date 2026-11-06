# 结构关系 (二): 第 0 层输入的折叠保持结构关系

> 不含记号. 入口 [StrRel](StrRel.lagda.md). 实例 $\Lambda=2$ 里第 0 层输入的折叠 (`Run` 在第 0 层只有 `n0`, `n1`, `⨾`, `nl`, `nw` 五句; `ni`, `nκ` 在第 0 层是空的). 一切比较都是结构的: 坐标 $w\sqsubseteq_0 w'$, 状态 `SRel`, 输出 `Obs`.
>
> - 下标 `I`: 第 0 层动作带着自己的自比 `HA0 A A` (同 `MonoPort2Zero`).
> - **`snd₀`**: $z\sqsubseteq_0 z'$, 两个动作满足 `HA0` ⇒ 对一切坐标 $w\sqsubseteq_0 w'$、一切 `SRel` 且 `Good` 的状态, 两个输出 `Obs` (两个目标上都是结构关系). 对推导归纳, 每个构造子一步.
> - **`chainˢ`**: 第 1 层节点在 $T_0$ 上上升时的链, 链点与坐标都 $\sqsubseteq_0$, 输出 $\mathrm{nl}$ 逐项 $\sqsubseteq_0$.
>
> **与 `MonoPort2Zero` 的差别.** 那里第 0 层输入只按值比, 要经 `DValCanon.Gen` 的规范形 (用到 `lim-leP`) 才能把值的比较变成语义的比较 (`cong0₂`). 这里输入按结构关系比, **不要规范形**: 每一句折叠子句把结构相关的输入送到结构相关的输出, 证明就是逐句的. 坐标必须作为结构关系带着 (`n1` 那一句把坐标交给动作, 动作在节点的分支里用它选分支).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.StrRelZero {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (D; hz; hs; AccY; accL; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.StrRelDef lW
```

## §1 动作, 下标, 语义

```agda
Act₀ : Set
Act₀ = P.Ig hz W

ac₀ : AccY hz
ac₀ = accL hz

R₀ : Act₀ → ∀ {V} → D hz V → V ⊲ W → D hz W → P.St W → P.Df W
R₀ A₀ z q w Y = P.Run ac₀ z q lW k0 A₀ w Y

HA0 : Act₀ → Act₀ → Set
HA0 A₀ A₁ = ∀ (w w′ : D hz W) → w ⊑₀ w′ → ∀ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (A₀ C.self lW w Y) (A₁ C.self lW w′ Y′)

I : Set
I = Σ Act₀ (λ (A₀ : Act₀) → HA0 A₀ A₀)

Sem0 : Act₀ → Act₀ → ∀ {V₁ V₂} → D hz V₁ → D hz V₂ → Set
Sem0 A₀ A₁ z z′ = ∀ q q′ (w w′ : D hz W) → w ⊑₀ w′ → ∀ Y Y′ → Good Y → Good Y′ → SRel Y Y′ →
                  Obs (R₀ A₀ z q w Y) (R₀ A₁ z′ q′ w′ Y′)

rf₁ : ∀ {A₀ : Act₀} {V} {z : D hz V} → Sem0 A₀ A₀ z z → ∀ q w Y → Good Y → Rf (o₁ (R₀ A₀ z q w Y))
rf₁ h q w Y g = proj₂ (h q q w w (refl₀ w) Y Y g g (sr g))
```

## §2 每个构造子一步

```agda
module Steps (A₀ A₁ : Act₀) where
  n0S : ∀ {V₁ V₂} {z : D hz V₂} → Sem0 A₀ A₁ (n0 {W = V₁}) z
  n0S q q′ w w′ hw Y Y′ g g′ s = z0 , n0⊑

  n1S : HA0 A₀ A₁ → ∀ {V₁ V₂} → Sem0 A₀ A₁ (n1 {W = V₁}) (n1 {W = V₂})
  n1S h q q′ w w′ hw Y Y′ g g′ s = h w w′ hw Y Y′ g g′ s

  ⨾S : ∀ {V₁ V₂} {x y : D hz V₁} {x′ y′ : D hz V₂} → Sem0 A₀ A₀ x x → Sem0 A₁ A₁ x′ x′ → x ⊑₀ x′ →
       Sem0 A₀ A₁ x x′ → Sem0 A₀ A₁ y y′ → Sem0 A₀ A₁ (x ⨾ y) (x′ ⨾ y′)
  ⨾S {x = x} {y} {x′} {y′} rx rx′ hxd hx hy q q′ w w′ hw Y Y′ g g′ s =
    let ox = hx q q′ w w′ hw Y Y′ g g′ s
        r  = rf₁ rx q w Y g
        r′ = rf₁ rx′ q′ w′ Y′ g′
        oy = hy q q′ (w ⨾ nw q x) (w′ ⨾ nw q′ x′) (sq hw (wl (wr hxd))) (Y ⊕ R₀ A₀ x q w Y) (Y′ ⊕ R₀ A₁ x′ q′ w′ Y′)
                (G⊕ g r) (G⊕ g′ r′) (S⊕ g g′ s ox)
    in sq (proj₁ ox) (proj₁ oy) , ⨾⊑ r r′ (proj₂ ox) (proj₂ oy)

  nlS : ∀ {V₁ V₂} {d : ℕ → D hz V₁} {d′ : ℕ → D hz V₂} → (∀ n → Sem0 A₀ A₀ (d n) (d n)) → (∀ n → Sem0 A₁ A₁ (d′ n) (d′ n)) →
        (∀ n → d n ⊑₀ d′ n) → (∀ n → Sem0 A₀ A₁ (d n) (d′ n)) → Sem0 A₀ A₁ (nl d) (nl d′)
  nlS {d = d} {d′} rd rd′ hdd hd q q′ w w′ hw Y Y′ g g′ s = lm hE₀ , nl⊑ rE rE′ hE
    where
    Q  = λ n → P.Rpt ac₀ d q lW k0 A₀ w Y n
    Q′ = λ n → P.Rpt ac₀ d′ q′ lW k0 A₁ w′ Y′ n
    E  = λ n → R₀ A₀ (d n) q (proj₁ (Q n)) (proj₂ (Q n))
    E′ = λ n → R₀ A₁ (d′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n))
    go : ∀ n → (proj₁ (Q n) ⊑₀ proj₁ (Q′ n)) × (Good (proj₂ (Q n)) × (Good (proj₂ (Q′ n)) × SRel (proj₂ (Q n)) (proj₂ (Q′ n))))
    go zero = hw , (g , (g′ , s))
    go (suc n) =
      let (a , (b , (b′ , e))) = go n
          h = hd n q q′ (proj₁ (Q n)) (proj₁ (Q′ n)) a (proj₂ (Q n)) (proj₂ (Q′ n)) b b′ e
      in sq a (wl (wr (hdd n))) ,
         (G⊕ b (rf₁ (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) b) ,
          (G⊕ b′ (rf₁ (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) b′) ,
           S⊕ b b′ e h))
    oE : ∀ n → Obs (E n) (E′ n)
    oE n = let (a , (b , (b′ , e))) = go n in hd n q q′ (proj₁ (Q n)) (proj₁ (Q′ n)) a (proj₂ (Q n)) (proj₂ (Q′ n)) b b′ e
    hE₀ : ∀ n → o₀ (E n) ⊑₀ o₀ (E′ n)
    hE₀ n = proj₁ (oE n)
    hE : ∀ n → o₁ (E n) ⊑₁ o₁ (E′ n)
    hE n = proj₂ (oE n)
    rE : ∀ n → Rf (o₁ (E n))
    rE n = rf₁ (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) (proj₁ (proj₂ (go n)))
    rE′ : ∀ n → Rf (o₁ (E′ n))
    rE′ n = rf₁ (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) (proj₁ (proj₂ (proj₂ (go n))))

  nwSˡ : ∀ {V₀ V V₂} {p : V₀ ⊲ V} {x : D hz V₀} {z : D hz V₂} → Sem0 A₀ A₁ x z → Sem0 A₀ A₁ (nw p x) z
  nwSˡ {p = p} h q q′ = h (C.⊲-tr p q) q′

  nwSʳ : ∀ {V₀ V V₁} {p : V₀ ⊲ V} {x : D hz V₀} {z : D hz V₁} → Sem0 A₀ A₁ z x → Sem0 A₀ A₁ z (nw p x)
  nwSʳ {p = p} h q q′ = h q (C.⊲-tr p q′)

  u0lS : ∀ {V₁ V₂} {x : D hz V₁} {x′ : D hz V₂} → Sem0 A₀ A₁ x x′ → Sem0 A₀ A₁ (n0 ⨾ x) x′
  u0lS h q q′ w w′ hw Y Y′ g g′ s =
    let o = h q q′ (w ⨾ nw q n0) w′ (tr (sq hw (wl z0)) (u1l (refl₀ w′))) (Y ⊕ P.zeroD) Y′ (G⊕0 g) g′ (S0ˡ s)
    in u0l (proj₁ o) , u0ˡ (proj₂ o)

  u0rS : ∀ {V₁ V₂} {x : D hz V₁} {x′ : D hz V₂} → Sem0 A₀ A₁ x x′ → Sem0 A₀ A₁ x (n0 ⨾ x′)
  u0rS h q q′ w w′ hw Y Y′ g g′ s =
    let o = h q q′ w (w′ ⨾ nw q′ n0) (tr (u1r (refl₀ w)) (sq hw (wr z0))) Y (Y′ ⊕ P.zeroD) g (G⊕0 g′) (S0ʳ s)
    in u0r (proj₁ o) , u0ʳ (proj₂ o)

  u1lS : ∀ {V₁ V₂} {x : D hz V₁} {x′ : D hz V₂} → Sem0 A₀ A₁ x x′ → Sem0 A₀ A₁ (x ⨾ n0) x′
  u1lS h q q′ w w′ hw Y Y′ g g′ s = let o = h q q′ w w′ hw Y Y′ g g′ s in u1l (proj₁ o) , u1ˡ (proj₂ o)

  u1rS : ∀ {V₁ V₂} {x : D hz V₁} {x′ : D hz V₂} → Sem0 A₀ A₁ x x′ → Sem0 A₀ A₁ x (x′ ⨾ n0)
  u1rS h q q′ w w′ hw Y Y′ g g′ s = let o = h q q′ w w′ hw Y Y′ g g′ s in u1r (proj₁ o) , u1ʳ (proj₂ o)
```

**结合律.** 三段 $x,y,z$ 在一边走: 一起加 ($Y⊕(R_x⨾R_y)$, 坐标 $w⨾\mathrm{nw}(x⨾y)$) 与分开加 ($(Y⊕R_x)⊕R_y$, 坐标 $(w⨾\mathrm{nw}\,x)⨾\mathrm{nw}\,y$) 的两个状态、两个坐标都由结合律对上, $z$ 的两次运行由 $z$ 的自比比较.

```agda
module Assoc (B : Act₀) where
  module Three {V} (x y z : D hz V) (sx : Sem0 B B x x) (sy : Sem0 B B y y) (q : V ⊲ W) (w : D hz W) (Y : P.St W) (g : Good Y) where
    Rx = R₀ B x q w Y
    rX = rf₁ sx q w Y g
    gx = G⊕ {Y} {Rx} g rX
    Ry = R₀ B y q (w ⨾ nw q x) (Y ⊕ Rx)
    rY = rf₁ sy q (w ⨾ nw q x) (Y ⊕ Rx) gx
    S1 = Y ⊕ (Rx P.⨾ᴰ Ry)
    S2 = (Y ⊕ Rx) ⊕ Ry
    gS1 = G⨾ᴰ {Y} {Rx} {Ry} g rX rY
    gS2 = G⊕ {Y ⊕ Rx} {Ry} gx rY
    s12 = proj₁ (asS {Y} {Rx} {Ry} g rX rY)
    s21 = proj₂ (asS {Y} {Rx} {Ry} g rX rY)
    rXY = ⨾⊑ rX rX rX rY
    w1 = w ⨾ nw q (x ⨾ y)
    w2 = (w ⨾ nw q x) ⨾ nw q y
    w12 : w1 ⊑₀ w2
    w12 = ar′ (sq (refl₀ w) (nwd x y))
    w21 : w2 ⊑₀ w1
    w21 = al (sq (refl₀ w) (nwd′ x y))
    r0 : ∀ {V′} (t : D hz V′) → t ⊑₀ t
    r0 = refl₀

module _ (A₀ A₁ : Act₀) where
  open Assoc
  alS : ∀ {V V′} {x y z : D hz V} {t : D hz V′} → Sem0 A₀ A₀ x x → Sem0 A₀ A₀ y y → Sem0 A₀ A₀ z z → Sem0 A₀ A₁ (x ⨾ (y ⨾ z)) t →
        Sem0 A₀ A₁ ((x ⨾ y) ⨾ z) t
  alS {x = x} {y} {z} sx sy sz h q q′ w w′ hw Y Y′ g g′ s =
    let open Three A₀ x y z sx sy q w Y g
        oz = sz q q w1 w2 w12 S1 S2 gS1 gS2 s12
        rZ = rf₁ sz q w1 S1 gS1
        oh = h q q′ w w′ hw Y Y′ g g′ s
    in al (tr (sq (r0 (o₀ Rx)) (sq (r0 (o₀ Ry)) (proj₁ oz))) (proj₁ oh)) ,
       asˡ rX rY rZ (tr (⨾⊑ rX rX rX (⨾⊑ rY rY rY (proj₂ oz))) (proj₂ oh))

  al′S : ∀ {V V′} {x y z : D hz V} {t : D hz V′} → Sem0 A₀ A₀ x x → Sem0 A₀ A₀ y y → Sem0 A₀ A₀ z z → Sem0 A₀ A₁ ((x ⨾ y) ⨾ z) t →
         Sem0 A₀ A₁ (x ⨾ (y ⨾ z)) t
  al′S {x = x} {y} {z} sx sy sz h q q′ w w′ hw Y Y′ g g′ s =
    let open Three A₀ x y z sx sy q w Y g
        oz = sz q q w2 w1 w21 S2 S1 gS2 gS1 s21
        rZ = rf₁ sz q w2 S2 gS2
        oh = h q q′ w w′ hw Y Y′ g g′ s
    in al′ (tr (sq (r0 (o₀ Rx ⨾ o₀ Ry)) (proj₁ oz)) (proj₁ oh)) ,
       asˡ′ rX rY rZ (tr (⨾⊑ rXY rXY rXY (proj₂ oz)) (proj₂ oh))

  arS : ∀ {V V′} {x y z : D hz V′} {t : D hz V} → Sem0 A₁ A₁ x x → Sem0 A₁ A₁ y y → Sem0 A₁ A₁ z z → Sem0 A₀ A₁ t ((x ⨾ y) ⨾ z) →
        Sem0 A₀ A₁ t (x ⨾ (y ⨾ z))
  arS {x = x} {y} {z} sx sy sz h q q′ w w′ hw Y Y′ g g′ s =
    let open Three A₁ x y z sx sy q′ w′ Y′ g′
        oz = sz q′ q′ w1 w2 w12 S1 S2 gS1 gS2 s12
        rZ = rf₁ sz q′ w2 S2 gS2
        oh = h q q′ w w′ hw Y Y′ g g′ s
    in ar (tr (proj₁ oh) (sq (r0 (o₀ Rx ⨾ o₀ Ry)) (proj₁ oz))) ,
       asʳ rX rY rZ (tr (proj₂ oh) (⨾⊑ rXY rXY rXY (proj₂ oz)))

  ar′S : ∀ {V V′} {x y z : D hz V′} {t : D hz V} → Sem0 A₁ A₁ x x → Sem0 A₁ A₁ y y → Sem0 A₁ A₁ z z → Sem0 A₀ A₁ t (x ⨾ (y ⨾ z)) →
         Sem0 A₀ A₁ t ((x ⨾ y) ⨾ z)
  ar′S {x = x} {y} {z} sx sy sz h q q′ w w′ hw Y Y′ g g′ s =
    let open Three A₁ x y z sx sy q′ w′ Y′ g′
        oz = sz q′ q′ w2 w1 w21 S2 S1 gS2 gS1 s21
        rZ = rf₁ sz q′ w1 S1 gS1
        oh = h q q′ w w′ hw Y Y′ g g′ s
    in ar′ (tr (proj₁ oh) (sq (r0 (o₀ Rx)) (sq (r0 (o₀ Ry)) (proj₁ oz)))) ,
       asʳ′ rX rY rZ (tr (proj₂ oh) (⨾⊑ rX rX rX (⨾⊑ rY rY rY (proj₂ oz))))

  trS : ∀ {V V′} {x y : D hz V} {z : D hz V′} → Sem0 A₀ A₀ x y → Sem0 A₀ A₁ y z → Sem0 A₀ A₁ x z
  trS h h′ q q′ w w′ hw Y Y′ g g′ s =
    let o = h q q w w (refl₀ w) Y Y g g (sr g)
        o′ = h′ q q′ w w′ hw Y Y′ g g′ s
    in tr (proj₁ o) (proj₁ o′) , tr (proj₂ o) (proj₂ o′)
```

**部分和.** 左边走 $x⨾\mathrm{pre}\,d\,k$, 右边走 $x'⨾\mathrm{nl}\,d'$. 前缀的坐标与状态是一次加上的, `Rpt` 的是逐段加的, 由结合律逐段对上 (两层都是); 输出用 `PreOut.O≡₀`, `O≡` 改写成各段输出的部分和, 再用 `pr`, `pre⊑`.

```agda
  preS : ∀ {V₁ V₂} {x : D hz V₁} {x′ : D hz V₂} {d : ℕ → D hz V₁} {d′ : ℕ → D hz V₂} →
         Sem0 A₀ A₀ x x → Sem0 A₁ A₁ x′ x′ → (∀ n → Sem0 A₀ A₀ (d n) (d n)) → (∀ n → Sem0 A₀ A₀ (preL d n) (preL d n)) →
         (∀ n → Sem0 A₁ A₁ (d′ n) (d′ n)) →
         x ⊑₀ x′ → (∀ n → d n ⊑₀ d′ n) → Sem0 A₀ A₁ x x′ → (∀ n → Sem0 A₀ A₁ (d n) (d′ n)) → ∀ k →
         Sem0 A₀ A₁ (x ⨾ preL d k) (x′ ⨾ nl d′)
  preS {x = x} {x′} {d} {d′} rx rx′ rd rp rd′ hxd hdd hx hd k q q′ w w′ hw Y Y′ g g′ s =
    subst (λ t → (o₀ Rx ⨾ t) ⊑₀ (o₀ Rx′ ⨾ nl (λ n → o₀ (E′ n)))) (sym (L.O≡₀ k)) (pr (proj₁ ox) hE₀ k) ,
    subst (λ t → (o₁ Rx ⨾ t) ⊑₁ (o₁ Rx′ ⨾ nl (λ n → o₁ (E′ n)))) (sym (L.O≡ k)) (pre⊑ rX rX′ rE rE′ (proj₂ ox) hE k)
    where
    Rx = R₀ A₀ x q w Y
    Rx′ = R₀ A₁ x′ q′ w′ Y′
    ox = hx q q′ w w′ hw Y Y′ g g′ s
    rX = rf₁ rx q w Y g
    rX′ = rf₁ rx′ q′ w′ Y′ g′
    Z = Y ⊕ Rx
    Z′ = Y′ ⊕ Rx′
    w₁ = w ⨾ nw q x
    w₁′ = w′ ⨾ nw q′ x′
    gZ : Good Z
    gZ = G⊕ {Y} {Rx} g rX
    gZ′ : Good Z′
    gZ′ = G⊕ {Y′} {Rx′} g′ rX′
    sZ : SRel Z Z′
    sZ = S⊕ g g′ s ox
    module L = PreOut ac₀ k0 A₀ d q w₁ Z
    Q′ = λ n → P.Rpt ac₀ d′ q′ lW k0 A₁ w₁′ Z′ n
    E′ = λ n → R₀ A₁ (d′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n))
    gL : ∀ n → Good (Z ⊕ L.Rp n)
    gL n = G⊕ {Z} {L.Rp n} gZ (rf₁ (rp n) q w₁ Z gZ)
    hw₁ : w₁ ⊑₀ w₁′
    hw₁ = sq hw (wl (wr hxd))
    go : ∀ n → ((w₁ ⨾ nw q (preL d n)) ⊑₀ proj₁ (Q′ n)) × (Good (proj₂ (Q′ n)) × SRel (Z ⊕ L.Rp n) (proj₂ (Q′ n)))
    go zero = tr (sq hw₁ (wl z0)) (u1l (refl₀ w₁′)) , (gZ′ , S0ˡ sZ)
    go (suc n) =
      let (a , (gr , e)) = go n
          h = hd n q q′ (w₁ ⨾ nw q (preL d n)) (proj₁ (Q′ n)) a (Z ⊕ L.Rp n) (proj₂ (Q′ n)) (gL n) gr e
          rEn = rf₁ (rd n) q (w₁ ⨾ nw q (preL d n)) (Z ⊕ L.Rp n) (gL n)
          rRp = rf₁ (rp n) q w₁ Z gZ
      in tr (sq (refl₀ w₁) (nwd (preL d n) (d n))) (al′ (sq a (wl (wr (hdd n))))) ,
         (G⊕ gr (rf₁ (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) gr) ,
          (al′ (sq (proj₁ e) (proj₁ h)) , asˡ′ gZ rRp rEn (⨾⊑ (gL n) gr (proj₂ e) (proj₂ h))))
    oE : ∀ n → Obs (L.Ek n) (E′ n)
    oE n = let (a , (gr , e)) = go n in hd n q q′ (w₁ ⨾ nw q (preL d n)) (proj₁ (Q′ n)) a (Z ⊕ L.Rp n) (proj₂ (Q′ n)) (gL n) gr e
    hE₀ : ∀ n → o₀ (L.Ek n) ⊑₀ o₀ (E′ n)
    hE₀ n = proj₁ (oE n)
    hE : ∀ n → o₁ (L.Ek n) ⊑₁ o₁ (E′ n)
    hE n = proj₂ (oE n)
    rE : ∀ n → Rf (o₁ (L.Ek n))
    rE n = rf₁ (rd n) q (w₁ ⨾ nw q (preL d n)) (Z ⊕ L.Rp n) (gL n)
    rE′ : ∀ n → Rf (o₁ (E′ n))
    rE′ n = rf₁ (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) (proj₁ (proj₂ (go n)))
```

## §3 自比与可靠性

`rS`: 一切第 0 层树对同一个动作自比, 对树归纳 (不经推导, 所以 `snd₀` 里取自比不破坏结构递归).

```agda
rS : ∀ (i : I) {V} (z : D hz V) → Sem0 (proj₁ i) (proj₁ i) z z
rSp : ∀ (i : I) {V} (d : ℕ → D hz V) n → Sem0 (proj₁ i) (proj₁ i) (preL d n) (preL d n)
rS i n0 = Steps.n0S (proj₁ i) (proj₁ i)
rS i n1 = Steps.n1S (proj₁ i) (proj₁ i) (proj₂ i)
rS i (x ⨾ y) = Steps.⨾S (proj₁ i) (proj₁ i) (rS i x) (rS i x) (refl₀ x) (rS i x) (rS i y)
rS i (nl d) = Steps.nlS (proj₁ i) (proj₁ i) (λ n → rS i (d n)) (λ n → rS i (d n)) (λ n → refl₀ (d n)) (λ n → rS i (d n))
rS i (ni () u)
rS i (nκ () u)
rS i (nw p x) = Steps.nwSˡ (proj₁ i) (proj₁ i) (Steps.nwSʳ (proj₁ i) (proj₁ i) (rS i x))
rSp i d zero = Steps.n0S (proj₁ i) (proj₁ i)
rSp i d (suc n) = Steps.⨾S (proj₁ i) (proj₁ i) (rSp i d n) (rSp i d n) (refl₀ (preL d n)) (rSp i d n) (rS i (d n))

snd₀ : ∀ (i j : I) → HA0 (proj₁ i) (proj₁ j) → ∀ {V₁ V₂} {z : D hz V₁} {z′ : D hz V₂} → z ⊑₀ z′ → Sem0 (proj₁ i) (proj₁ j) z z′
snd₀ i j h z0 = Steps.n0S (proj₁ i) (proj₁ j)
snd₀ i j h o1 = Steps.n1S (proj₁ i) (proj₁ j) h
snd₀ i j h (sq {x = x} {x′ = x′} hx hy) = Steps.⨾S (proj₁ i) (proj₁ j) (rS i x) (rS j x′) hx (snd₀ i j h hx) (snd₀ i j h hy)
snd₀ i j h (lm {d = d} {d′} hd) = Steps.nlS (proj₁ i) (proj₁ j) (λ n → rS i (d n)) (λ n → rS j (d′ n)) hd (λ n → snd₀ i j h (hd n))
snd₀ i j h (wl hx) = Steps.nwSˡ (proj₁ i) (proj₁ j) (snd₀ i j h hx)
snd₀ i j h (wr hx) = Steps.nwSʳ (proj₁ i) (proj₁ j) (snd₀ i j h hx)
snd₀ i j h (pr {x = x} {x′} {d} {d′} hx hd k) =
  preS (proj₁ i) (proj₁ j) (rS i x) (rS j x′) (λ n → rS i (d n)) (rSp i d) (λ n → rS j (d′ n)) hx hd (snd₀ i j h hx) (λ n → snd₀ i j h (hd n)) k
snd₀ i j h (tr hx hy) = trS (proj₁ i) (proj₁ j) (snd₀ i i (proj₂ i) hx) (snd₀ i j h hy)
snd₀ i j h (u0l hx) = Steps.u0lS (proj₁ i) (proj₁ j) (snd₀ i j h hx)
snd₀ i j h (u0r hx) = Steps.u0rS (proj₁ i) (proj₁ j) (snd₀ i j h hx)
snd₀ i j h (u1l hx) = Steps.u1lS (proj₁ i) (proj₁ j) (snd₀ i j h hx)
snd₀ i j h (u1r hx) = Steps.u1rS (proj₁ i) (proj₁ j) (snd₀ i j h hx)
snd₀ i j h (al {x = x} {y} {z} hx) = alS (proj₁ i) (proj₁ j) (rS i x) (rS i y) (rS i z) (snd₀ i j h hx)
snd₀ i j h (al′ {x = x} {y} {z} hx) = al′S (proj₁ i) (proj₁ j) (rS i x) (rS i y) (rS i z) (snd₀ i j h hx)
snd₀ i j h (ar {x = x} {y} {z} hx) = arS (proj₁ i) (proj₁ j) (rS j x) (rS j y) (rS j z) (snd₀ i j h hx)
snd₀ i j h (ar′ {x = x} {y} {z} hx) = ar′S (proj₁ i) (proj₁ j) (rS j x) (rS j y) (rS j z) (snd₀ i j h hx)
```

## §4 链

第 1 层节点在 $T_0$ 上上升时的链 (`Chn`, 第 0 层的点). 不变量: 坐标 $\sqsubseteq_0$, 链点 $\sqsubseteq_0$, 两边状态 `Good`, 状态 `SRel`. 每一步用一次 `snd₀`: 下一个链点是上一个链点的输出在 $T_0$ 上的读数, 所以 "链点结构相关" 正是 "输出结构相关".

```agda
module _ (i j : I) (hx : HA0 (proj₁ i) (proj₁ j)) where
  private
    A₀ = proj₁ i
    A₁ = proj₁ j

  CC : Act₀ → P.St W → ℕ → D hz W × (D hz W × P.St W)
  CC A₂ Y = P.Chn ac₀ k0 lW A₂ Y

  segs : Act₀ → P.St W → ℕ → D hz W
  segs A₂ Y n = o₀ (R₀ A₂ (proj₁ (proj₂ (CC A₂ Y n))) C.self (proj₁ (CC A₂ Y n)) (proj₂ (proj₂ (CC A₂ Y n))))

  chainˢ : ∀ (Y Y′ : P.St W) → Good Y → Good Y′ → SRel Y Y′ → nl (segs A₀ Y) ⊑₀ nl (segs A₁ Y′)
  chainˢ Y Y′ g g′ s = lm (λ n → proj₁ (step n))
    where
    c  = λ n → proj₁ (CC A₀ Y n)
    c′ = λ n → proj₁ (CC A₁ Y′ n)
    δ  = λ n → proj₁ (proj₂ (CC A₀ Y n))
    δ′ = λ n → proj₁ (proj₂ (CC A₁ Y′ n))
    Yn  = λ n → proj₂ (proj₂ (CC A₀ Y n))
    Yn′ = λ n → proj₂ (proj₂ (CC A₁ Y′ n))
    go : ∀ n → (c n ⊑₀ c′ n) × ((δ n ⊑₀ δ′ n) × (Good (Yn n) × (Good (Yn′ n) × SRel (Yn n) (Yn′ n))))
    step : ∀ n → Obs (R₀ A₀ (δ n) C.self (c n) (Yn n)) (R₀ A₁ (δ′ n) C.self (c′ n) (Yn′ n))
    step n = let (gc , (gd , (gy , (gy′ , sy)))) = go n in snd₀ i j hx gd C.self C.self (c n) (c′ n) gc (Yn n) (Yn′ n) gy gy′ sy
    go zero = z0 , (proj₁ s , (g , (g′ , s)))
    go (suc n) =
      let (gc , (gd , (gy , (gy′ , sy)))) = go n
      in sq gc gd ,
         (proj₁ (step n) ,
          (G⊕ gy (rf₁ (rS i (δ n)) C.self (c n) (Yn n) gy) ,
           (G⊕ gy′ (rf₁ (rS j (δ′ n)) C.self (c′ n) (Yn′ n) gy′) ,
            S⊕ gy gy′ sy (step n))))
```
