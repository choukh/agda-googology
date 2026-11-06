# 第 1 层的值关系 (三): 读数单调, 输出封闭, 一个证明

> 不含记号. 入口 [MonoPort2](MonoPort2.lagda.md). **定理 `snd`**: 在实例 $\Lambda=2$, 世界 $W$ 里, $x\sqsubseteq x'$ ([MonoPort2Rel](MonoPort2Rel.lagda.md)) 推出: 对一切满足 `HA₁` 的动作, 一切 `SRel` 相关且各自 `Good` 的状态, 一切底 $c\le c'$,
>
> - (a) 第 0 层读数 $c+\mathrm{out}_{T_0}(x)\le c'+\mathrm{out}_{T_0}(x')$;
> - (b) **第 1 层输出封闭**: $\mathrm{out}_{T_1}(x)\sqsubseteq\mathrm{out}_{T_1}(x')$.
>
> 两件一起对推导归纳. 每个构造子一步; 新用到的东西:
>
> | 构造子 | 一步 |
> |---|---|
> | 和的结构 (`⨾⊑`, `nl⊑`, `u*`, `tr`) | 状态沿 `⊕` 在两个目标上都是左折; 加进状态的那一段的输出自比, 由构造子带的自比给出 |
> | `as*`, `pre⊑`, `lim⊑` | 两个字面不同、值相同的状态 (`asS`); 部分和的输出是各段输出的部分和 (`PreOut.O≡`) |
> | **`ni⊑`, (a)** | 节点在 $T_0$ 上上升: 链 (`MonoPort2Zero.chain₂`), 链的动作是 `Ai u`, 三条前提由分支的三条判据加归纳给出 |
> | **`ni⊑`, (b)** | 节点在 $T_1$ 上保留: 输出节点的分支在坐标 $z$ 上是 "先在第 0 层走 $z$ (动作 `Ai u`), 再走分支 $u(z)$, 读 $T_1$" (`BNi`). 状态的比较由 `cong0₂` (两个读数一起) 给出, 分支的比较由归纳给出; 三条判据都这样来 |
>
> **为什么只看 `self`.** 这一实例里第 1 层的折叠只从路径 `self` 进 (链 `Chn` 与 `RKi` 的上升都在当前世界里调动作, `Ai` 在 `self` 上取分支), 输出节点在 $T_1$ (世界 $W$) 上, 它的分支以后也只在 `self` 上被取. `cv self Y` 在 $T_0$, $T_1$ 上的读数与 $Y$ 定义性相同. 所以关系与语义都只在世界 $W$ 里说.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.MonoPort2Sound {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (D; hz; hs; hself; ss; accL; outS; ⊲ᴴ↑; n0; n1; _⨾_; nl; ni; nw; sum; pt; sum-fst)
open import OCF.Align.MonoPortBridge using (val)
open import OCF.Align.MonoPort2Rel lW
open import OCF.Align.MonoPort2Zero lW using (Act₀; ac₀; R₀; HA0; I; Rl; rO; rf₁; rPre; cong0₂; chain₂)
```

## §1 语义

```agda
ac₁ = accL (hs hz)

R₁ : Act₁ → D₁ → D₁ → P.St W → P.Df W
R₁ A₀ x w Y = P.Run ac₁ x C.self lW k1 A₀ w Y

Sem₁ : D₁ → D₁ → Set
Sem₁ x x′ = ∀ (A₀ : Act₁) → HA₁ A₀ → ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ →
            Obs c c′ (R₁ A₀ x w Y) (R₁ A₀ x′ w′ Y′)

rf : ∀ {x} → Sem₁ x x → ∀ (A₀ : Act₁) → HA₁ A₀ → ∀ w Y → Good Y → Rf (o₁ (R₁ A₀ x w Y))
rf h A₀ hA w Y g = proj₂ (h A₀ hA w w azero azero Y Y g g (sr g) z≤)

-- 节点上升时链的动作
Ai : Act₁ → Br → D₁ → Act₀
Ai A₀ u w = P.Ai ac₁ ac₀ (ss hself) u C.self k0 k1 A₀ w
```

## §2 每个构造子一步 (对语义)

```agda
module _ (A₀ : Act₁) (hA : HA₁ A₀) where
  ⨾S : ∀ {x y x′ y′} → Sem₁ x x → Sem₁ x′ x′ → Sem₁ x x′ → Sem₁ y y′ →
       ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ (x ⨾ y) w Y) (R₁ A₀ (x′ ⨾ y′) w′ Y′)
  ⨾S {x} {y} {x′} {y′} rx rx′ hx hy w w′ c c′ Y Y′ g g′ s cb =
    let ox = hx A₀ hA w w′ c c′ Y Y′ g g′ s cb
        os = hx A₀ hA w w′ (vY Y) (vY Y′) Y Y′ g g′ s (proj₁ s)
        r  = rf rx A₀ hA w Y g
        r′ = rf rx′ A₀ hA w′ Y′ g′
        oy = hy A₀ hA (w ⨾ nw C.self x) (w′ ⨾ nw C.self x′) _ _ (Y ⊕ R₁ A₀ x w Y) (Y′ ⊕ R₁ A₀ x′ w′ Y′)
               (G⊕ g r) (G⊕ g′ r′) (S⊕ g g′ s os) (proj₁ ox)
    in proj₁ oy , ⨾⊑ r r′ (proj₂ ox) (proj₂ oy)

  nlS : ∀ {d d′ : ℕ → D₁} → (∀ n → Sem₁ (d n) (d n)) → (∀ n → Sem₁ (d′ n) (d′ n)) → (∀ n → Sem₁ (d n) (d′ n)) →
        ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ (nl d) w Y) (R₁ A₀ (nl d′) w′ Y′)
  nlS {d} {d′} rd rd′ hd w w′ c c′ Y Y′ g g′ s cb =
    l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (go n))))) , nl⊑ rE rE′ hE
    where
    Q  = λ n → P.Rpt ac₁ d C.self lW k1 A₀ w Y n
    Q′ = λ n → P.Rpt ac₁ d′ C.self lW k1 A₀ w′ Y′ n
    E  = λ n → R₁ A₀ (d n) (proj₁ (Q n)) (proj₂ (Q n))
    E′ = λ n → R₁ A₀ (d′ n) (proj₁ (Q′ n)) (proj₂ (Q′ n))
    go : ∀ n → Good (proj₂ (Q n)) × (Good (proj₂ (Q′ n)) × (SRel (proj₂ (Q n)) (proj₂ (Q′ n)) ×
               (pt c (λ m → o₀ (E m)) n ≤ pt c′ (λ m → o₀ (E′ m)) n)))
    go zero = g , (g′ , (s , cb))
    go (suc n) =
      let (b , (b′ , (e , f))) = go n
          h = λ e₁ e₂ (eb : e₁ ≤ e₂) → hd n A₀ hA (proj₁ (Q n)) (proj₁ (Q′ n)) e₁ e₂ (proj₂ (Q n)) (proj₂ (Q′ n)) b b′ e eb
      in G⊕ b (rf (rd n) A₀ hA (proj₁ (Q n)) (proj₂ (Q n)) b) ,
         (G⊕ b′ (rf (rd′ n) A₀ hA (proj₁ (Q′ n)) (proj₂ (Q′ n)) b′) ,
          (S⊕ b b′ e (h _ _ (proj₁ e)) , proj₁ (h _ _ f)))
    rE : ∀ n → Rf (o₁ (E n))
    rE n = rf (rd n) A₀ hA (proj₁ (Q n)) (proj₂ (Q n)) (proj₁ (go n))
    rE′ : ∀ n → Rf (o₁ (E′ n))
    rE′ n = rf (rd′ n) A₀ hA (proj₁ (Q′ n)) (proj₂ (Q′ n)) (proj₁ (proj₂ (go n)))
    hE : ∀ n → o₁ (E n) ⊑ o₁ (E′ n)
    hE n = let (b , (b′ , (e , f))) = go n in
      proj₂ (hd n A₀ hA (proj₁ (Q n)) (proj₁ (Q′ n)) azero azero (proj₂ (Q n)) (proj₂ (Q′ n)) b b′ e z≤)

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

  asˡS : ∀ {x y z t} → Sem₁ x x → Sem₁ y y → Sem₁ z z → Sem₁ (x ⨾ (y ⨾ z)) t →
         ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ ((x ⨾ y) ⨾ z) w Y) (R₁ A₀ t w′ Y′)
  asˡS {x} {y} {z} sx sy sz h w w′ c c′ Y Y′ g g′ s cb =
    let open Three x y z sx sy w Y g
        b = sum (sum c (o₀ Rx)) (o₀ Ry)
        oz = sz A₀ hA w1 w2 b b S1 S2 gS1 gS2 s12 (≤-refl b)
        rZ = rf sz A₀ hA w1 S1 gS1
        oh = h A₀ hA w w′ c c′ Y Y′ g g′ s cb
    in ≤-trans (proj₁ oz) (proj₁ oh) , asˡ rX rY rZ (tr (⨾⊑ rX rX rX (⨾⊑ rY rY rY (proj₂ oz))) (proj₂ oh))

  asˡ′S : ∀ {x y z t} → Sem₁ x x → Sem₁ y y → Sem₁ z z → Sem₁ ((x ⨾ y) ⨾ z) t →
          ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ (x ⨾ (y ⨾ z)) w Y) (R₁ A₀ t w′ Y′)
  asˡ′S {x} {y} {z} sx sy sz h w w′ c c′ Y Y′ g g′ s cb =
    let open Three x y z sx sy w Y g
        b = sum (sum c (o₀ Rx)) (o₀ Ry)
        oz = sz A₀ hA w2 w1 b b S2 S1 gS2 gS1 s21 (≤-refl b)
        rZ = rf sz A₀ hA w2 S2 gS2
        oh = h A₀ hA w w′ c c′ Y Y′ g g′ s cb
    in ≤-trans (proj₁ oz) (proj₁ oh) , asˡ′ rX rY rZ (tr (⨾⊑ rXY rXY rXY (proj₂ oz)) (proj₂ oh))

  asʳS : ∀ {x y z t} → Sem₁ x x → Sem₁ y y → Sem₁ z z → Sem₁ t ((x ⨾ y) ⨾ z) →
         ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ t w Y) (R₁ A₀ (x ⨾ (y ⨾ z)) w′ Y′)
  asʳS {x} {y} {z} sx sy sz h w w′ c c′ Y Y′ g g′ s cb =
    let open Three x y z sx sy w′ Y′ g′
        b = sum (sum c′ (o₀ Rx)) (o₀ Ry)
        oz = sz A₀ hA w1 w2 b b S1 S2 gS1 gS2 s12 (≤-refl b)
        rZ = rf sz A₀ hA w2 S2 gS2
        oh = h A₀ hA w w′ c c′ Y Y′ g g′ s cb
    in ≤-trans (proj₁ oh) (proj₁ oz) , asʳ rX rY rZ (tr (proj₂ oh) (⨾⊑ rXY rXY rXY (proj₂ oz)))

  asʳ′S : ∀ {x y z t} → Sem₁ x x → Sem₁ y y → Sem₁ z z → Sem₁ t (x ⨾ (y ⨾ z)) →
          ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ t w Y) (R₁ A₀ ((x ⨾ y) ⨾ z) w′ Y′)
  asʳ′S {x} {y} {z} sx sy sz h w w′ c c′ Y Y′ g g′ s cb =
    let open Three x y z sx sy w′ Y′ g′
        b = sum (sum c′ (o₀ Rx)) (o₀ Ry)
        oz = sz A₀ hA w2 w1 b b S2 S1 gS2 gS1 s21 (≤-refl b)
        rZ = rf sz A₀ hA w1 S1 gS1
        oh = h A₀ hA w w′ c c′ Y Y′ g g′ s cb
    in ≤-trans (proj₁ oh) (proj₁ oz) , asʳ′ rX rY rZ (tr (proj₂ oh) (⨾⊑ rX rX rX (⨾⊑ rY rY rY (proj₂ oz))))
```

```agda
  trS : ∀ {x y z} → Sem₁ x y → Sem₁ y z →
        ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ x w Y) (R₁ A₀ z w′ Y′)
  trS h h′ w w′ c c′ Y Y′ g g′ s cb =
    let o = h A₀ hA w w c c Y Y g g (sr g) (≤-refl c)
        o′ = h′ A₀ hA w w′ c c′ Y Y′ g g′ s cb
    in ≤-trans (proj₁ o) (proj₁ o′) , tr (proj₂ o) (proj₂ o′)

  u0ˡS : ∀ {x x′} → Sem₁ x x′ → ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ (n0 ⨾ x) w Y) (R₁ A₀ x′ w′ Y′)
  u0ˡS h w w′ c c′ Y Y′ g g′ s cb =
    let o = h A₀ hA (w ⨾ nw C.self n0) w′ c c′ (Y ⊕ P.zeroD) Y′ (G⊕0 g) g′ (S0ˡ s) cb in proj₁ o , u0ˡ (proj₂ o)

  u0ʳS : ∀ {x x′} → Sem₁ x x′ → ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ x w Y) (R₁ A₀ (n0 ⨾ x′) w′ Y′)
  u0ʳS h w w′ c c′ Y Y′ g g′ s cb =
    let o = h A₀ hA w (w′ ⨾ nw C.self n0) c c′ Y (Y′ ⊕ P.zeroD) g (G⊕0 g′) (S0ʳ s) cb in proj₁ o , u0ʳ (proj₂ o)

  u1ˡS : ∀ {x x′} → Sem₁ x x′ → ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ (x ⨾ n0) w Y) (R₁ A₀ x′ w′ Y′)
  u1ˡS h w w′ c c′ Y Y′ g g′ s cb = let o = h A₀ hA w w′ c c′ Y Y′ g g′ s cb in proj₁ o , u1ˡ (proj₂ o)

  u1ʳS : ∀ {x x′} → Sem₁ x x′ → ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ x w Y) (R₁ A₀ (x′ ⨾ n0) w′ Y′)
  u1ʳS h w w′ c c′ Y Y′ g g′ s cb = let o = h A₀ hA w w′ c c′ Y Y′ g g′ s cb in proj₁ o , u1ʳ (proj₂ o)
```

**部分和与极限.** 同 [MonoPort2Zero](MonoPort2Zero.lagda.md) 的 `pre-le`, `lim-leP`, 少了上下文的比较 (第 1 层的上下文只流进动作, 动作不看它); 多了一件: 前缀输出的自比要沿归纳带着 (第 1 层不是一切树都自比, 没有 `rO`).

```agda
  preS : ∀ {x x′} {d d′ : ℕ → D₁} → Sem₁ x x → Sem₁ x′ x′ → (∀ n → Sem₁ (d n) (d n)) → (∀ n → Sem₁ (d′ n) (d′ n)) →
         Sem₁ x x′ → (∀ n → Sem₁ (d n) (d′ n)) → ∀ k →
         ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ (x ⨾ preL d k) w Y) (R₁ A₀ (x′ ⨾ nl d′) w′ Y′)
  preS {x} {x′} {d} {d′} rx rx′ rd rd′ hx hd k w w′ c c′ Y Y′ g g′ s cb =
    ≤l k (proj₂ (proj₂ (proj₂ (go k)))) ,
    subst (λ t → (o₁ Rx ⨾ t) ⊑ (o₁ Rx′ ⨾ nl (λ n → o₁ (E′ n)))) (sym (L.O≡ k)) (pre⊑ rX rX′ rE rE′ (proj₂ ox) hE k)
    where
    Rx = R₁ A₀ x w Y
    Rx′ = R₁ A₀ x′ w′ Y′
    ox = hx A₀ hA w w′ c c′ Y Y′ g g′ s cb
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
    sZ = S⊕ g g′ s (hx A₀ hA w w′ (vY Y) (vY Y′) Y Y′ g g′ s (proj₁ s))
    module L = PreOut ac₁ k1 A₀ d C.self w₁ Z
    Q′ = λ n → P.Rpt ac₁ d′ C.self lW k1 A₀ w₁′ Z′ n
    E′ = λ n → R₁ A₀ (d′ n) (proj₁ (Q′ n)) (proj₂ (Q′ n))
    b₁ = sum c (o₀ Rx)
    b₁′ = sum c′ (o₀ Rx′)
    go : ∀ n → Rf (o₁ (L.Rp n)) × (Good (proj₂ (Q′ n)) ×
               (SRel (Z ⊕ L.Rp n) (proj₂ (Q′ n)) × (sum b₁ (o₀ (L.Rp n)) ≤ pt b₁′ (λ m → o₀ (E′ m)) n)))
    go zero = n0⊑ , (gZ′ , (S0ˡ sZ , proj₁ ox))
    go (suc n) =
      let (a , (gr , (e , f))) = go n
          gLn = G⊕ {Z} {L.Rp n} gZ a
          h = λ e₁ e₂ (eb : e₁ ≤ e₂) → hd n A₀ hA (w₁ ⨾ nw C.self (preL d n)) (proj₁ (Q′ n)) e₁ e₂ (Z ⊕ L.Rp n) (proj₂ (Q′ n)) gLn gr e eb
          rEn = rf (rd n) A₀ hA (w₁ ⨾ nw C.self (preL d n)) (Z ⊕ L.Rp n) gLn
      in ⨾⊑ a a a rEn ,
         (G⊕ gr (rf (rd′ n) A₀ hA (proj₁ (Q′ n)) (proj₂ (Q′ n)) gr) ,
          ((proj₁ (h _ _ (proj₁ e)) , asˡ′ gZ a rEn (⨾⊑ gLn gr (proj₂ e) (proj₂ (h azero azero z≤)))) ,
           proj₁ (h _ _ f)))
    gL : ∀ n → Good (Z ⊕ L.Rp n)
    gL n = G⊕ {Z} {L.Rp n} gZ (proj₁ (go n))
    rE : ∀ n → Rf (o₁ (L.Ek n))
    rE n = rf (rd n) A₀ hA (w₁ ⨾ nw C.self (preL d n)) (Z ⊕ L.Rp n) (gL n)
    rE′ : ∀ n → Rf (o₁ (E′ n))
    rE′ n = rf (rd′ n) A₀ hA (proj₁ (Q′ n)) (proj₂ (Q′ n)) (proj₁ (proj₂ (go n)))
    hE : ∀ n → o₁ (L.Ek n) ⊑ o₁ (E′ n)
    hE n = let (a , (gr , (e , f))) = go n in
      proj₂ (hd n A₀ hA (w₁ ⨾ nw C.self (preL d n)) (proj₁ (Q′ n)) azero azero (Z ⊕ L.Rp n) (proj₂ (Q′ n)) (gL n) gr e z≤)

  limS : ∀ {x t} {d : ℕ → D₁} → Sem₁ x x → (∀ n → Sem₁ (d n) (d n)) → (∀ k → Sem₁ (x ⨾ preL d k) t) →
         ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ (x ⨾ nl d) w Y) (R₁ A₀ t w′ Y′)
  limS {x} {t} {d} rx rd hk w w′ c c′ Y Y′ g g′ s cb =
    l≤ (λ k → ≤-trans (proj₂ (proj₂ (proj₂ (go k)))) (proj₁ (hk k A₀ hA w w′ c c′ Y Y′ g g′ s cb))) ,
    lim⊑ rX rEL (λ k → tr (⨾⊑ rX rX rX (PL k))
                          (subst (λ t′ → (o₁ Rx ⨾ t′) ⊑ o₁ (R₁ A₀ t w′ Y′)) (L.O≡ k) (proj₂ (hk k A₀ hA w w′ c c′ Y Y′ g g′ s cb))))
    where
    Rx = R₁ A₀ x w Y
    rX = rf rx A₀ hA w Y g
    Z = Y ⊕ Rx
    w₁ = w ⨾ nw C.self x
    gZ : Good Z
    gZ = G⊕ {Y} {Rx} g rX
    module L = PreOut ac₁ k1 A₀ d C.self w₁ Z
    Q = λ n → P.Rpt ac₁ d C.self lW k1 A₀ w₁ Z n
    EL = λ n → R₁ A₀ (d n) (proj₁ (Q n)) (proj₂ (Q n))
    b₁ = sum c (o₀ Rx)
    go : ∀ n → Rf (o₁ (L.Rp n)) × (Good (proj₂ (Q n)) ×
               (SRel (proj₂ (Q n)) (Z ⊕ L.Rp n) × (pt b₁ (λ m → o₀ (EL m)) n ≤ sum b₁ (o₀ (L.Rp n)))))
    go zero = n0⊑ , (gZ , (S0ʳ (sr gZ) , ≤-refl _))
    go (suc n) =
      let (a , (gq , (e , f))) = go n
          gLn = G⊕ {Z} {L.Rp n} gZ a
          h = λ e₁ e₂ (eb : e₁ ≤ e₂) → rd n A₀ hA (proj₁ (Q n)) (w₁ ⨾ nw C.self (preL d n)) e₁ e₂ (proj₂ (Q n)) (Z ⊕ L.Rp n) gq gLn e eb
          rEk = rf (rd n) A₀ hA (w₁ ⨾ nw C.self (preL d n)) (Z ⊕ L.Rp n) gLn
      in ⨾⊑ a a a rEk ,
         (G⊕ gq (rf (rd n) A₀ hA (proj₁ (Q n)) (proj₂ (Q n)) gq) ,
          ((proj₁ (h _ _ (proj₁ e)) , asʳ gZ a rEk (⨾⊑ gq gLn (proj₂ e) (proj₂ (h azero azero z≤)))) ,
           proj₁ (h _ _ f)))
    gL : ∀ n → Good (Z ⊕ L.Rp n)
    gL n = G⊕ {Z} {L.Rp n} gZ (proj₁ (go n))
    rEL : ∀ n → Rf (o₁ (EL n))
    rEL n = rf (rd n) A₀ hA (proj₁ (Q n)) (proj₂ (Q n)) (proj₁ (proj₂ (go n)))
    rEk : ∀ n → Rf (o₁ (L.Ek n))
    rEk n = rf (rd n) A₀ hA (w₁ ⨾ nw C.self (preL d n)) (Z ⊕ L.Rp n) (gL n)
    hEL : ∀ n → o₁ (EL n) ⊑ o₁ (L.Ek n)
    hEL n = let (a , (gq , (e , f))) = go n in
      proj₂ (rd n A₀ hA (proj₁ (Q n)) (w₁ ⨾ nw C.self (preL d n)) azero azero (proj₂ (Q n)) (Z ⊕ L.Rp n) gq (gL n) e z≤)
    PL : ∀ k → preL (λ n → o₁ (EL n)) k ⊑ preL (λ n → o₁ (L.Ek n)) k
    PL zero = n0⊑
    PL (suc k) = ⨾⊑ (rPre rEL k) (rPre rEk k) (PL k) (hEL k)
```

**节点.** 输出节点的分支 `outB` 字面就是 `RKi` 保留时给的 (`BNi` 在 `self` 上): 先在第 0 层以动作 `Ai v ww` 走坐标 $z$ (状态 `cv self Z`, 上下文 `n0`), 加进状态, 再走分支 $v(z)$, 读 $T_1$. `branch`: 两边的这个读数可比, 只要第 0 层那一步可比 (`cong0₂`, 两个读数一起) 且分支可比 (前提 `cv`).

```agda
  outB : Br → D₁ → P.St W → Br
  outB v ww Z {W′} p lW′ y =
    P.yc (P.BNi ac₁ ac₀ (ss hself) v C.self k1 A₀ ww Z k0 (C.⊲-tr (C.self {W}) p) lW′ (outS (ss (hself {W = W})) y)) (P.tg C.self (⊲ᴴ↑ p k1) lW′)

  branch : ∀ (v v′ : Br) ww ww′ → HA0 (Ai A₀ v ww) (Ai A₀ v ww) → HA0 (Ai A₀ v′ ww′) (Ai A₀ v′ ww′) → HA0 (Ai A₀ v ww) (Ai A₀ v′ ww′) →
           (∀ z z′ → val z ≤ val z′ → Sem₁ (ap v z) (ap v′ z′)) → ∀ (Z Z′ : P.St W) → Good Z → Good Z′ → SRel Z Z′ →
           ∀ z z′ → val z ≤ val z′ → ap (outB v ww Z) z ⊑ ap (outB v′ ww′ Z′) z′
  branch v v′ ww ww′ hv hv′ hvv cv Z Z′ gZ gZ′ sZ z z′ le =
    proj₂ (cv z z′ le (P.Ig↾ C.self A₀) hA _ _ azero azero S S′ (G⊕ {Z₁} {Δ} gZ rΔ) (G⊕ {Z₁′} {Δ′} gZ′ rΔ′) (S⊕ {Z₁} {Z₁′} {Δ} {Δ′} gZ gZ′ sZ o) z≤)
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
    o = proj₁ (cong0₂ a b hvv z z′ le) C.self C.self n0 n0 (vY Z) (vY Z′) Z₁ Z₁′ (≤-refl _) gZ gZ′ sZ (proj₁ sZ)
    rΔ = rf₁ (proj₁ (rO a z)) C.self n0 Z₁ gZ
    rΔ′ = rf₁ (proj₁ (rO b z′)) C.self n0 Z₁′ gZ′

  niS : ∀ {u u′ : Br} → (∀ z z′ → val z ≤ val z′ → Sem₁ (ap u z) (ap u z′)) → (∀ z z′ → val z ≤ val z′ → Sem₁ (ap u′ z) (ap u′ z′)) →
        (∀ z z′ → val z ≤ val z′ → Sem₁ (ap u z) (ap u′ z′)) →
        ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (R₁ A₀ (ni (ss hself) u) w Y) (R₁ A₀ (ni (ss hself) u′) w′ Y′)
  niS {u} {u′} mu mu′ cr w w′ c c′ Y Y′ g g′ s cb =
    chain₂ i j hij Y Y′ c c′ g g′ s cb ,
    ni⊑ (λ z z′ le → branch u u w w h0 h0 h0 mu Y Y g g (sr g) z z′ le)
        (λ z z′ le → branch u′ u′ w′ w′ h1 h1 h1 mu′ Y′ Y′ g′ g′ (sr g′) z z′ le)
        (λ z z′ le → branch u u′ w w′ h0 h1 hij cr Y Y′ g g′ s z z′ le)
    where
    h0 : HA0 (Ai A₀ u w) (Ai A₀ u w)
    h0 z z′ e e′ Z Z′ le gz gz′ sz eb = mu z z′ le (P.Ig↾ C.self A₀) hA _ _ e e′ Z Z′ gz gz′ sz eb
    h1 : HA0 (Ai A₀ u′ w′) (Ai A₀ u′ w′)
    h1 z z′ e e′ Z Z′ le gz gz′ sz eb = mu′ z z′ le (P.Ig↾ C.self A₀) hA _ _ e e′ Z Z′ gz gz′ sz eb
    hij : HA0 (Ai A₀ u w) (Ai A₀ u′ w′)
    hij z z′ e e′ Z Z′ le gz gz′ sz eb = cr z z′ le (P.Ig↾ C.self A₀) hA _ _ e e′ Z Z′ gz gz′ sz eb
    i j : I
    i = Ai A₀ u w , h0
    j = Ai A₀ u′ w′ , h1
```

## §3 定理

```agda
snd : ∀ {x x′} → x ⊑ x′ → Sem₁ x x′
snd n0⊑ A₀ hA w w′ c c′ Y Y′ g g′ s cb = ≤-trans cb (⊲→≤ (sum-fst c′ _)) , n0⊑
snd n1⊑ A₀ hA = hA
snd (⨾⊑ rx rx′ hx hy) A₀ hA = ⨾S A₀ hA (snd rx) (snd rx′) (snd hx) (snd hy)
snd (nl⊑ rd rd′ hd) A₀ hA = nlS A₀ hA (λ n → snd (rd n)) (λ n → snd (rd′ n)) (λ n → snd (hd n))
snd (ni⊑ mu mu′ cr) A₀ hA = niS A₀ hA (λ z z′ le → snd (mu z z′ le)) (λ z z′ le → snd (mu′ z z′ le)) (λ z z′ le → snd (cr z z′ le))
snd (tr h h′) A₀ hA = trS A₀ hA (snd h) (snd h′)
snd (u0ˡ h) A₀ hA = u0ˡS A₀ hA (snd h)
snd (u0ʳ h) A₀ hA = u0ʳS A₀ hA (snd h)
snd (u1ˡ h) A₀ hA = u1ˡS A₀ hA (snd h)
snd (u1ʳ h) A₀ hA = u1ʳS A₀ hA (snd h)
snd (asˡ rx ry rz h) A₀ hA = asˡS A₀ hA (snd rx) (snd ry) (snd rz) (snd h)
snd (asˡ′ rx ry rz h) A₀ hA = asˡ′S A₀ hA (snd rx) (snd ry) (snd rz) (snd h)
snd (asʳ rx ry rz h) A₀ hA = asʳS A₀ hA (snd rx) (snd ry) (snd rz) (snd h)
snd (asʳ′ rx ry rz h) A₀ hA = asʳ′S A₀ hA (snd rx) (snd ry) (snd rz) (snd h)
snd (pre⊑ rx rx′ rd rd′ hx hd k) A₀ hA =
  preS A₀ hA (snd rx) (snd rx′) (λ n → snd (rd n)) (λ n → snd (rd′ n)) (snd hx) (λ n → snd (hd n)) k
snd (lim⊑ rx rd h) A₀ hA = limS A₀ hA (snd rx) (λ n → snd (rd n)) (λ k → snd (h k))
```
