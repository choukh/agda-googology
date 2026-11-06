# 结构关系 (三): 第 1 层的折叠保持结构关系, 一个证明

> 不含记号. 入口 [StrRel](StrRel.lagda.md). **定理 `snd₁`**: 实例 $\Lambda=2$, 世界 $W$ 里, $x\sqsubseteq_1 x'$ ([StrRelDef](StrRelDef.lagda.md)) 推出: 对一切满足 `HA₁` 的动作、一切 `SRel` 相关且各自 `Good` 的状态,
>
> - (a) 第 0 层输出 $\mathrm{out}_{T_0}(x)\sqsubseteq_0\mathrm{out}_{T_0}(x')$ (**结构的**, 由 `val₀` 得值的单调);
> - (b) 第 1 层输出 $\mathrm{out}_{T_1}(x)\sqsubseteq_1\mathrm{out}_{T_1}(x')$.
>
> 两件一起对推导归纳. 证明的骨架照 [MonoPort2Sound](MonoPort2Sound.lagda.md); 差别只在两处:
>
> | 构造子 | `MonoPort2Sound` | 这里 |
> |---|---|---|
> | (a) 的所有情形 | 值的 $\le$, 带底 | 结构关系 $\sqsubseteq_0$ 的同名构造子 (`sq`, `lm`, `al`, `pr`, ...) |
> | `ni⊑`, (a) | `chain₂`, 链点按值比 (经 `cong0₂`, 即 `Gen` 与 `lim-leP`) | `chainˢ`, 链点按结构比, 每一步是 `snd₀` |
> | `ni⊑`, (b) | 输出分支在 $\mathrm{val}\,z\le\mathrm{val}\,z'$ 上比, 经 `cong0₂` | 在 $z\sqsubseteq_0 z'$ 上比, 经 `snd₀` |
> | `lim⊑` | `limS` | **没有这个构造子, 也不需要** |
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.StrRelSound {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (D; hz; hs; hself; ss; accL; outS; ⊲ᴴ↑; n0; n1; _⨾_; nl; ni; nw)
open import OCF.Align.StrRelDef lW
open import OCF.Align.StrRelZero lW using (Act₀; ac₀; R₀; HA0; I; rf₁; rS; snd₀; segs; chainˢ)
```

## §1 语义

```agda
ac₁ = accL (hs hz)

R₁ : Act₁ → D₁ → D₁ → P.St W → P.Df W
R₁ A₀ x w Y = P.Run ac₁ x C.self lW k1 A₀ w Y

Sem₁ : D₁ → D₁ → Set
Sem₁ x x′ = ∀ (A₀ : Act₁) → HA₁ A₀ → ∀ (w w′ : D₁) Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ x w Y) (R₁ A₀ x′ w′ Y′)

rf : ∀ {x} → Sem₁ x x → ∀ (A₀ : Act₁) → HA₁ A₀ → ∀ w Y → Good Y → Rf (o₁ (R₁ A₀ x w Y))
rf h A₀ hA w Y g = proj₂ (h A₀ hA w w Y Y g g (sr g))

-- 节点上升时链的动作
Ai : Act₁ → Br → D₁ → Act₀
Ai A₀ u w = P.Ai ac₁ ac₀ (ss hself) u C.self k0 k1 A₀ w
```

## §2 每个构造子一步

```agda
module _ (A₀ : Act₁) (hA : HA₁ A₀) where
  ⨾S : ∀ {x y x′ y′} → Sem₁ x x → Sem₁ x′ x′ → Sem₁ x x′ → Sem₁ y y′ →
       ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ (x ⨾ y) w Y) (R₁ A₀ (x′ ⨾ y′) w′ Y′)
  ⨾S {x} {y} {x′} {y′} rx rx′ hx hy w w′ Y Y′ g g′ s =
    let ox = hx A₀ hA w w′ Y Y′ g g′ s
        r  = rf rx A₀ hA w Y g
        r′ = rf rx′ A₀ hA w′ Y′ g′
        oy = hy A₀ hA (w ⨾ nw C.self x) (w′ ⨾ nw C.self x′) (Y ⊕ R₁ A₀ x w Y) (Y′ ⊕ R₁ A₀ x′ w′ Y′)
               (G⊕ g r) (G⊕ g′ r′) (S⊕ g g′ s ox)
    in sq (proj₁ ox) (proj₁ oy) , ⨾⊑ r r′ (proj₂ ox) (proj₂ oy)

  nlS : ∀ {d d′ : ℕ → D₁} → (∀ n → Sem₁ (d n) (d n)) → (∀ n → Sem₁ (d′ n) (d′ n)) → (∀ n → Sem₁ (d n) (d′ n)) →
        ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ (nl d) w Y) (R₁ A₀ (nl d′) w′ Y′)
  nlS {d} {d′} rd rd′ hd w w′ Y Y′ g g′ s = lm (λ n → proj₁ (oE n)) , nl⊑ rE rE′ (λ n → proj₂ (oE n))
    where
    Q  = λ n → P.Rpt ac₁ d C.self lW k1 A₀ w Y n
    Q′ = λ n → P.Rpt ac₁ d′ C.self lW k1 A₀ w′ Y′ n
    E  = λ n → R₁ A₀ (d n) (proj₁ (Q n)) (proj₂ (Q n))
    E′ = λ n → R₁ A₀ (d′ n) (proj₁ (Q′ n)) (proj₂ (Q′ n))
    go : ∀ n → Good (proj₂ (Q n)) × (Good (proj₂ (Q′ n)) × SRel (proj₂ (Q n)) (proj₂ (Q′ n)))
    oE : ∀ n → Obs (E n) (E′ n)
    oE n = let (b , (b′ , e)) = go n in hd n A₀ hA (proj₁ (Q n)) (proj₁ (Q′ n)) (proj₂ (Q n)) (proj₂ (Q′ n)) b b′ e
    go zero = g , (g′ , s)
    go (suc n) =
      let (b , (b′ , e)) = go n
      in G⊕ b (rf (rd n) A₀ hA (proj₁ (Q n)) (proj₂ (Q n)) b) ,
         (G⊕ b′ (rf (rd′ n) A₀ hA (proj₁ (Q′ n)) (proj₂ (Q′ n)) b′) , S⊕ b b′ e (oE n))
    rE : ∀ n → Rf (o₁ (E n))
    rE n = rf (rd n) A₀ hA (proj₁ (Q n)) (proj₂ (Q n)) (proj₁ (go n))
    rE′ : ∀ n → Rf (o₁ (E′ n))
    rE′ n = rf (rd′ n) A₀ hA (proj₁ (Q′ n)) (proj₂ (Q′ n)) (proj₁ (proj₂ (go n)))

  -- 三段 x, y, z 在一边走
  module Three (x y z : D₁) (sx : Sem₁ x x) (sy : Sem₁ y y) (w : D₁) (Y : P.St W) (g : Good Y) where
    Rx = R₁ A₀ x w Y
    rX = rf sx A₀ hA w Y g
    gx = G⊕ {Y} {Rx} g rX
    Ry = R₁ A₀ y (w ⨾ nw C.self x) (Y ⊕ Rx)
    rY = rf sy A₀ hA (w ⨾ nw C.self x) (Y ⊕ Rx) gx
    S1 = Y ⊕ (Rx P.⨾ᴰ Ry)
    S2 = (Y ⊕ Rx) ⊕ Ry
    gS1 = G⨾ᴰ {Y} {Rx} {Ry} g rX rY
    gS2 = G⊕ {Y ⊕ Rx} {Ry} gx rY
    s12 = proj₁ (asS {Y} {Rx} {Ry} g rX rY)
    s21 = proj₂ (asS {Y} {Rx} {Ry} g rX rY)
    rXY = ⨾⊑ rX rX rX rY
    w1 = w ⨾ nw C.self (x ⨾ y)
    w2 = (w ⨾ nw C.self x) ⨾ nw C.self y
    r0 : ∀ {V′} (t : D hz V′) → t ⊑₀ t
    r0 = refl₀

  asˡS : ∀ {x y z t} → Sem₁ x x → Sem₁ y y → Sem₁ z z → Sem₁ (x ⨾ (y ⨾ z)) t →
         ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ ((x ⨾ y) ⨾ z) w Y) (R₁ A₀ t w′ Y′)
  asˡS {x} {y} {z} sx sy sz h w w′ Y Y′ g g′ s =
    let open Three x y z sx sy w Y g
        oz = sz A₀ hA w1 w2 S1 S2 gS1 gS2 s12
        rZ = rf sz A₀ hA w1 S1 gS1
        oh = h A₀ hA w w′ Y Y′ g g′ s
    in al (tr (sq (r0 (o₀ Rx)) (sq (r0 (o₀ Ry)) (proj₁ oz))) (proj₁ oh)) ,
       asˡ rX rY rZ (tr (⨾⊑ rX rX rX (⨾⊑ rY rY rY (proj₂ oz))) (proj₂ oh))

  asˡ′S : ∀ {x y z t} → Sem₁ x x → Sem₁ y y → Sem₁ z z → Sem₁ ((x ⨾ y) ⨾ z) t →
          ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ (x ⨾ (y ⨾ z)) w Y) (R₁ A₀ t w′ Y′)
  asˡ′S {x} {y} {z} sx sy sz h w w′ Y Y′ g g′ s =
    let open Three x y z sx sy w Y g
        oz = sz A₀ hA w2 w1 S2 S1 gS2 gS1 s21
        rZ = rf sz A₀ hA w2 S2 gS2
        oh = h A₀ hA w w′ Y Y′ g g′ s
    in al′ (tr (sq (r0 (o₀ Rx ⨾ o₀ Ry)) (proj₁ oz)) (proj₁ oh)) ,
       asˡ′ rX rY rZ (tr (⨾⊑ rXY rXY rXY (proj₂ oz)) (proj₂ oh))

  asʳS : ∀ {x y z t} → Sem₁ x x → Sem₁ y y → Sem₁ z z → Sem₁ t ((x ⨾ y) ⨾ z) →
         ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ t w Y) (R₁ A₀ (x ⨾ (y ⨾ z)) w′ Y′)
  asʳS {x} {y} {z} sx sy sz h w w′ Y Y′ g g′ s =
    let open Three x y z sx sy w′ Y′ g′
        oz = sz A₀ hA w1 w2 S1 S2 gS1 gS2 s12
        rZ = rf sz A₀ hA w2 S2 gS2
        oh = h A₀ hA w w′ Y Y′ g g′ s
    in ar (tr (proj₁ oh) (sq (r0 (o₀ Rx ⨾ o₀ Ry)) (proj₁ oz))) ,
       asʳ rX rY rZ (tr (proj₂ oh) (⨾⊑ rXY rXY rXY (proj₂ oz)))

  asʳ′S : ∀ {x y z t} → Sem₁ x x → Sem₁ y y → Sem₁ z z → Sem₁ t (x ⨾ (y ⨾ z)) →
          ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ t w Y) (R₁ A₀ ((x ⨾ y) ⨾ z) w′ Y′)
  asʳ′S {x} {y} {z} sx sy sz h w w′ Y Y′ g g′ s =
    let open Three x y z sx sy w′ Y′ g′
        oz = sz A₀ hA w2 w1 S2 S1 gS2 gS1 s21
        rZ = rf sz A₀ hA w1 S1 gS1
        oh = h A₀ hA w w′ Y Y′ g g′ s
    in ar′ (tr (proj₁ oh) (sq (r0 (o₀ Rx)) (sq (r0 (o₀ Ry)) (proj₁ oz)))) ,
       asʳ′ rX rY rZ (tr (proj₂ oh) (⨾⊑ rX rX rX (⨾⊑ rY rY rY (proj₂ oz))))

  trS : ∀ {x y z} → Sem₁ x y → Sem₁ y z →
        ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ x w Y) (R₁ A₀ z w′ Y′)
  trS h h′ w w′ Y Y′ g g′ s =
    let o = h A₀ hA w w Y Y g g (sr g)
        o′ = h′ A₀ hA w w′ Y Y′ g g′ s
    in tr (proj₁ o) (proj₁ o′) , tr (proj₂ o) (proj₂ o′)

  u0ˡS : ∀ {x x′} → Sem₁ x x′ → ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ (n0 ⨾ x) w Y) (R₁ A₀ x′ w′ Y′)
  u0ˡS h w w′ Y Y′ g g′ s =
    let o = h A₀ hA (w ⨾ nw C.self n0) w′ (Y ⊕ P.zeroD) Y′ (G⊕0 g) g′ (S0ˡ s) in u0l (proj₁ o) , u0ˡ (proj₂ o)

  u0ʳS : ∀ {x x′} → Sem₁ x x′ → ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ x w Y) (R₁ A₀ (n0 ⨾ x′) w′ Y′)
  u0ʳS h w w′ Y Y′ g g′ s =
    let o = h A₀ hA w (w′ ⨾ nw C.self n0) Y (Y′ ⊕ P.zeroD) g (G⊕0 g′) (S0ʳ s) in u0r (proj₁ o) , u0ʳ (proj₂ o)

  u1ˡS : ∀ {x x′} → Sem₁ x x′ → ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ (x ⨾ n0) w Y) (R₁ A₀ x′ w′ Y′)
  u1ˡS h w w′ Y Y′ g g′ s = let o = h A₀ hA w w′ Y Y′ g g′ s in u1l (proj₁ o) , u1ˡ (proj₂ o)

  u1ʳS : ∀ {x x′} → Sem₁ x x′ → ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ x w Y) (R₁ A₀ (x′ ⨾ n0) w′ Y′)
  u1ʳS h w w′ Y Y′ g g′ s = let o = h A₀ hA w w′ Y Y′ g g′ s in u1r (proj₁ o) , u1ʳ (proj₂ o)
```

**部分和.** 同 [StrRelZero](StrRelZero.lagda.md) 的 `preS`, 少了坐标的比较 (第 1 层的坐标只流进动作, `HA₁` 不看它); 多了一件: 前缀输出的自比沿归纳带着.

```agda
  preS : ∀ {x x′} {d d′ : ℕ → D₁} → Sem₁ x x → Sem₁ x′ x′ → (∀ n → Sem₁ (d n) (d n)) → (∀ n → Sem₁ (d′ n) (d′ n)) →
         Sem₁ x x′ → (∀ n → Sem₁ (d n) (d′ n)) → ∀ k →
         ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ (x ⨾ preL d k) w Y) (R₁ A₀ (x′ ⨾ nl d′) w′ Y′)
  preS {x} {x′} {d} {d′} rx rx′ rd rd′ hx hd k w w′ Y Y′ g g′ s =
    subst (λ t → (o₀ Rx ⨾ t) ⊑₀ (o₀ Rx′ ⨾ nl (λ n → o₀ (E′ n)))) (sym (L.O≡₀ k)) (pr (proj₁ ox) hE₀ k) ,
    subst (λ t → (o₁ Rx ⨾ t) ⊑₁ (o₁ Rx′ ⨾ nl (λ n → o₁ (E′ n)))) (sym (L.O≡ k)) (pre⊑ rX rX′ rE rE′ (proj₂ ox) hE k)
    where
    Rx = R₁ A₀ x w Y
    Rx′ = R₁ A₀ x′ w′ Y′
    ox = hx A₀ hA w w′ Y Y′ g g′ s
    rX = rf rx A₀ hA w Y g
    rX′ = rf rx′ A₀ hA w′ Y′ g′
    Z = Y ⊕ Rx
    Z′ = Y′ ⊕ Rx′
    w₁ = w ⨾ nw C.self x
    w₁′ = w′ ⨾ nw C.self x′
    gZ : Good Z
    gZ = G⊕ {Y} {Rx} g rX
    gZ′ : Good Z′
    gZ′ = G⊕ {Y′} {Rx′} g′ rX′
    sZ : SRel Z Z′
    sZ = S⊕ g g′ s ox
    module L = PreOut ac₁ k1 A₀ d C.self w₁ Z
    Q′ = λ n → P.Rpt ac₁ d′ C.self lW k1 A₀ w₁′ Z′ n
    E′ = λ n → R₁ A₀ (d′ n) (proj₁ (Q′ n)) (proj₂ (Q′ n))
    go : ∀ n → Rf (o₁ (L.Rp n)) × (Good (proj₂ (Q′ n)) × SRel (Z ⊕ L.Rp n) (proj₂ (Q′ n)))
    go zero = n0⊑ , (gZ′ , S0ˡ sZ)
    go (suc n) =
      let (a , (gr , e)) = go n
          gLn = G⊕ {Z} {L.Rp n} gZ a
          h = hd n A₀ hA (w₁ ⨾ nw C.self (preL d n)) (proj₁ (Q′ n)) (Z ⊕ L.Rp n) (proj₂ (Q′ n)) gLn gr e
          rEn = rf (rd n) A₀ hA (w₁ ⨾ nw C.self (preL d n)) (Z ⊕ L.Rp n) gLn
      in ⨾⊑ a a a rEn ,
         (G⊕ gr (rf (rd′ n) A₀ hA (proj₁ (Q′ n)) (proj₂ (Q′ n)) gr) ,
          (al′ (sq (proj₁ e) (proj₁ h)) , asˡ′ gZ a rEn (⨾⊑ gLn gr (proj₂ e) (proj₂ h))))
    gL : ∀ n → Good (Z ⊕ L.Rp n)
    gL n = G⊕ {Z} {L.Rp n} gZ (proj₁ (go n))
    oE : ∀ n → Obs (L.Ek n) (E′ n)
    oE n = let (a , (gr , e)) = go n in
      hd n A₀ hA (w₁ ⨾ nw C.self (preL d n)) (proj₁ (Q′ n)) (Z ⊕ L.Rp n) (proj₂ (Q′ n)) (gL n) gr e
    hE₀ : ∀ n → o₀ (L.Ek n) ⊑₀ o₀ (E′ n)
    hE₀ n = proj₁ (oE n)
    hE : ∀ n → o₁ (L.Ek n) ⊑₁ o₁ (E′ n)
    hE n = proj₂ (oE n)
    rE : ∀ n → Rf (o₁ (L.Ek n))
    rE n = rf (rd n) A₀ hA (w₁ ⨾ nw C.self (preL d n)) (Z ⊕ L.Rp n) (gL n)
    rE′ : ∀ n → Rf (o₁ (E′ n))
    rE′ n = rf (rd′ n) A₀ hA (proj₁ (Q′ n)) (proj₂ (Q′ n)) (proj₁ (proj₂ (go n)))
```

**节点.** 输出节点的分支 `outB` 字面就是 `RKi` 保留时给的 (`BNi` 在 `self` 上): 先在第 0 层以动作 `Ai v ww` 走坐标 $z$ (状态 `cv self Z`, 坐标 `n0`), 加进状态, 再走分支 $v(z)$, 读 $T_1$. `branch`: 坐标 $z\sqsubseteq_0 z'$ 时两边的这个读数可比: 第 0 层那一步由 `snd₀` (输入就是坐标的推导), 分支那一步由归纳. 节点在 $T_0$ 上上升, 读数是链 (`chainˢ`).

```agda
  outB : Br → D₁ → P.St W → Br
  outB v ww Z {W′} p lW′ y =
    P.yc (P.BNi ac₁ ac₀ (ss hself) v C.self k1 A₀ ww Z k0 (C.⊲-tr (C.self {W}) p) lW′ (outS (ss (hself {W = W})) y)) (P.tg C.self (⊲ᴴ↑ p k1) lW′)

  branch : ∀ (v v′ : Br) ww ww′ → (hv : HA0 (Ai A₀ v ww) (Ai A₀ v ww)) → (hv′ : HA0 (Ai A₀ v′ ww′) (Ai A₀ v′ ww′)) →
           HA0 (Ai A₀ v ww) (Ai A₀ v′ ww′) →
           (∀ (z z′ : D hz W) → z ⊑₀ z′ → Sem₁ (ap v z) (ap v′ z′)) → ∀ (Z Z′ : P.St W) → Good Z → Good Z′ → SRel Z Z′ →
           ∀ (z z′ : D hz W) → z ⊑₀ z′ → ap (outB v ww Z) z ⊑₁ ap (outB v′ ww′ Z′) z′
  branch v v′ ww ww′ hv hv′ hvv cv Z Z′ gZ gZ′ sZ z z′ le =
    proj₂ (cv z z′ le (P.Ig↾ C.self A₀) hA _ _ S S′ (G⊕ {Z₁} {Δ} gZ rΔ) (G⊕ {Z₁′} {Δ′} gZ′ rΔ′) (S⊕ {Z₁} {Z₁′} {Δ} {Δ′} gZ gZ′ sZ o))
    where
    a b : I
    a = P.Ig↾ C.self (Ai A₀ v ww) , hv
    b = P.Ig↾ C.self (Ai A₀ v′ ww′) , hv′
    Z₁ = P.cv C.self Z
    Z₁′ = P.cv C.self Z′
    Δ = R₀ (proj₁ a) z C.self n0 Z₁
    Δ′ = R₀ (proj₁ b) z′ C.self n0 Z₁′
    S = Z₁ ⊕ Δ
    S′ = Z₁′ ⊕ Δ′
    o = snd₀ a b hvv le C.self C.self n0 n0 z0 Z₁ Z₁′ gZ gZ′ sZ
    rΔ = rf₁ (rS a z) C.self n0 Z₁ gZ
    rΔ′ = rf₁ (rS b z′) C.self n0 Z₁′ gZ′

  niS : ∀ {u u′ : Br} → (∀ (z z′ : D hz W) → z ⊑₀ z′ → Sem₁ (ap u z) (ap u z′)) → (∀ (z z′ : D hz W) → z ⊑₀ z′ → Sem₁ (ap u′ z) (ap u′ z′)) →
        (∀ (z z′ : D hz W) → z ⊑₀ z′ → Sem₁ (ap u z) (ap u′ z′)) →
        ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (R₁ A₀ (ni (ss hself) u) w Y) (R₁ A₀ (ni (ss hself) u′) w′ Y′)
  niS {u} {u′} mu mu′ cr w w′ Y Y′ g g′ s =
    chainˢ i j hij Y Y′ g g′ s ,
    ni⊑ (λ z z′ le → branch u u w w h0 h0 h0 mu Y Y g g (sr g) z z′ le)
        (λ z z′ le → branch u′ u′ w′ w′ h1 h1 h1 mu′ Y′ Y′ g′ g′ (sr g′) z z′ le)
        (λ z z′ le → branch u u′ w w′ h0 h1 hij cr Y Y′ g g′ s z z′ le)
    where
    h0 : HA0 (Ai A₀ u w) (Ai A₀ u w)
    h0 z z′ le Z Z′ gz gz′ sz = mu z z′ le (P.Ig↾ C.self A₀) hA _ _ Z Z′ gz gz′ sz
    h1 : HA0 (Ai A₀ u′ w′) (Ai A₀ u′ w′)
    h1 z z′ le Z Z′ gz gz′ sz = mu′ z z′ le (P.Ig↾ C.self A₀) hA _ _ Z Z′ gz gz′ sz
    hij : HA0 (Ai A₀ u w) (Ai A₀ u′ w′)
    hij z z′ le Z Z′ gz gz′ sz = cr z z′ le (P.Ig↾ C.self A₀) hA _ _ Z Z′ gz gz′ sz
    i j : I
    i = Ai A₀ u w , h0
    j = Ai A₀ u′ w′ , h1
```

## §3 定理

```agda
snd₁ : ∀ {x x′} → x ⊑₁ x′ → Sem₁ x x′
snd₁ n0⊑ A₀ hA w w′ Y Y′ g g′ s = z0 , n0⊑
snd₁ n1⊑ A₀ hA = hA
snd₁ (⨾⊑ rx rx′ hx hy) A₀ hA = ⨾S A₀ hA (snd₁ rx) (snd₁ rx′) (snd₁ hx) (snd₁ hy)
snd₁ (nl⊑ rd rd′ hd) A₀ hA = nlS A₀ hA (λ n → snd₁ (rd n)) (λ n → snd₁ (rd′ n)) (λ n → snd₁ (hd n))
snd₁ (ni⊑ mu mu′ cr) A₀ hA = niS A₀ hA (λ z z′ le → snd₁ (mu z z′ le)) (λ z z′ le → snd₁ (mu′ z z′ le)) (λ z z′ le → snd₁ (cr z z′ le))
snd₁ (tr h h′) A₀ hA = trS A₀ hA (snd₁ h) (snd₁ h′)
snd₁ (u0ˡ h) A₀ hA = u0ˡS A₀ hA (snd₁ h)
snd₁ (u0ʳ h) A₀ hA = u0ʳS A₀ hA (snd₁ h)
snd₁ (u1ˡ h) A₀ hA = u1ˡS A₀ hA (snd₁ h)
snd₁ (u1ʳ h) A₀ hA = u1ʳS A₀ hA (snd₁ h)
snd₁ (asˡ rx ry rz h) A₀ hA = asˡS A₀ hA (snd₁ rx) (snd₁ ry) (snd₁ rz) (snd₁ h)
snd₁ (asˡ′ rx ry rz h) A₀ hA = asˡ′S A₀ hA (snd₁ rx) (snd₁ ry) (snd₁ rz) (snd₁ h)
snd₁ (asʳ rx ry rz h) A₀ hA = asʳS A₀ hA (snd₁ rx) (snd₁ ry) (snd₁ rz) (snd₁ h)
snd₁ (asʳ′ rx ry rz h) A₀ hA = asʳ′S A₀ hA (snd₁ rx) (snd₁ ry) (snd₁ rz) (snd₁ h)
snd₁ (pre⊑ rx rx′ rd rd′ hx hd k) A₀ hA =
  preS A₀ hA (snd₁ rx) (snd₁ rx′) (λ n → snd₁ (rd n)) (λ n → snd₁ (rd′ n)) (snd₁ hx) (λ n → snd₁ (hd n)) k
```

**输出封闭, 拆成两句.** `out₀`, `out₁`: 一对结构相关的第 1 层输入, 走同一个满足 `HA₁` 的动作, 它们在 $T_0$ 上的输出结构相关, 在 $T_1$ 上的输出结构相关; 第 0 层的值单调是 `val₀` 的推论 (`read₀`).

```agda
out₀ : ∀ {x x′} → x ⊑₁ x′ → ∀ (A₀ : Act₁) → HA₁ A₀ → ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ →
       o₀ (R₁ A₀ x w Y) ⊑₀ o₀ (R₁ A₀ x′ w′ Y′)
out₀ h A₀ hA w w′ Y Y′ g g′ s = proj₁ (snd₁ h A₀ hA w w′ Y Y′ g g′ s)

out₁ : ∀ {x x′} → x ⊑₁ x′ → ∀ (A₀ : Act₁) → HA₁ A₀ → ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ →
       o₁ (R₁ A₀ x w Y) ⊑₁ o₁ (R₁ A₀ x′ w′ Y′)
out₁ h A₀ hA w w′ Y Y′ g g′ s = proj₂ (snd₁ h A₀ hA w w′ Y Y′ g g′ s)
```
