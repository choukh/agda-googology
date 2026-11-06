# 一步对一切有限高度 (三): 上下文律与 `Int` 的单调, 对一切层对

> 入口 [MonoPort6](MonoPort6.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 第 $\ge1$ 层的上下文关系 `Ctx (hs b)` 的律只用 `RelM` 的构造子, 对 $b$ 写一次 (§1, 与 `MonoPort5One.cl₁` 同一组论证). §2–§3 是上一组列为第二个障碍的 `IntM`: 节点的动作 `Ai` 把坐标 $z$ (层 $k$) 经 `Int` 嵌进节点层的上下文, 实例 $\ge4$ 时这个上下文被更高的节点读作坐标, 所以 `Int` 必须单调. 源层带节点时, `Int` 的 `ni` 句造一个新节点, 它的分支里再 `Int` 一次坐标 (层 $j<k$ 进层 $k$). 证明对 (源层的良基证明, 推导) 字典序归纳: 内层那次 `Int` 用节点给出的更小的良基证明 `g R`, 外层对分支的推导结构归纳. 源层是第 0 层时 (`IntM₀`) 照搬 `MonoPort5Int.IntM`, 目标层换成任意层.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (H; LgH; hz; _⊲[_]_)
module OCF.Align.MonoPort6Int (Λ : H) (lΛ : LgH Λ) {W : A} (lW : Lg W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hs; hl; hΩ; ss; StH; Vs; NZ; NZ-S; D; AccY; acc; Int; Pre; mkOf; Kup; outS; inS; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.StrRelDef lW using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀; preL)
  renaming (tr to tr₀; nwd to nwd₀; nwd′ to nwd₀′)
open import OCF.Align.MonoPort6Rel Λ lΛ lW t₀
open import OCF.Align.MonoPort5Rel lW using (module RelM)
```

## 1 第 $\ge1$ 层的上下文律

```agda
module CxS (b : H) where
  open R b hiding (Rf)

  C : D (hs b) W → D (hs b) W → Set
  C = Ctx (hs b)

  okRf : ∀ {w} → Ok w → Rf (hs b) w
  okRf = OkRf

  cx⨾ : ∀ {w w′ x x′} → C w w′ → Rf (hs b) x → Rf (hs b) x′ → Rel (hs b) x x′ → C (w ⨾ nw C.self x) (w′ ⨾ nw C.self x′)
  cx⨾ (hw , (o , o′)) rx rx′ hx = ⨾⊑ (OkRf o) (OkRf o′) hw (nwˡ (nwʳ hx)) , ((o , rnw rx) , (o′ , rnw rx′))

  cx0l : ∀ {w w′} → C w w′ → C (w ⨾ nw C.self n0) w′
  cx0l (hw , (o , o′)) = tr (⨾⊑ (OkRf o) (OkRf o) (OkRf o) (nwˡ n0⊑)) (u1ˡ hw) , ((o , rnw n0⊑) , o′)

  cx0r : ∀ {w w′} → C w w′ → C w (w′ ⨾ nw C.self n0)
  cx0r (hw , (o , o′)) = tr (u1ʳ hw) (⨾⊑ (OkRf o′) (OkRf o′) (OkRf o′) n0⊑) , (o , (o′ , rnw n0⊑))

  cxas : ∀ {w w′ x y} → C w w′ → Rf (hs b) x → Rf (hs b) y → C (w ⨾ nw C.self (x ⨾ y)) ((w ⨾ nw C.self x) ⨾ nw C.self y)
  cxas (_ , (o , _)) rx ry =
    asʳ′ (OkRf o) (rnw rx) (rnw ry) (⨾⊑ (OkRf o) (OkRf o) (OkRf o) (nwd rx ry)) , ((o , rnw (⨾⊑ rx rx rx ry)) , ((o , rnw rx) , rnw ry))

  cxas′ : ∀ {w w′ x y} → C w w′ → Rf (hs b) x → Rf (hs b) y → C ((w ⨾ nw C.self x) ⨾ nw C.self y) (w ⨾ nw C.self (x ⨾ y))
  cxas′ (_ , (o , _)) rx ry =
    asˡ (OkRf o) (rnw rx) (rnw ry) (⨾⊑ (OkRf o) (OkRf o) (OkRf o) (nwd′ rx ry)) , (((o , rnw rx) , rnw ry) , (o , rnw (⨾⊑ rx rx rx ry)))

  -- 节点分支的上下文: nw w ⨾ (内层 Int)
  ctxN : ∀ {w w′ I I′} → C w w′ → Rel (hs b) I I′ → Rf (hs b) I → Rf (hs b) I′ → C (nw C.self w ⨾ I) (nw C.self w′ ⨾ I′)
  ctxN {w} {w′} (hw , (o , o′)) hI r r′ =
    ⨾⊑ (rnw (OkRf {w} o)) (rnw (OkRf {w′} o′)) (nwˡ (nwʳ hw)) hI , ((rnw (OkRf {w} o) , r) , (rnw (OkRf {w′} o′) , r′))

  -- Int 走极限时的上下文: w ⨾ Pre d n
  preR : ∀ {d d′ : ℕ → D (hs b) W} → (∀ n → Rf (hs b) (d n)) → (∀ n → Rf (hs b) (d′ n)) → (∀ n → Rel (hs b) (d n) (d′ n)) →
         ∀ n → Rel (hs b) (Pre C.self d n) (Pre C.self d′ n)
  preR rd rd′ hd zero = n0⊑
  preR rd rd′ hd (suc n) = ⨾⊑ (preR rd rd rd n) (preR rd′ rd′ rd′ n) (preR rd rd′ hd n) (nwˡ (nwʳ (hd n)))

  cxPre : ∀ {w w′} {d d′ : ℕ → D (hs b) W} → C w w′ → (∀ n → Rf (hs b) (d n)) → (∀ n → Rf (hs b) (d′ n)) → (∀ n → Rel (hs b) (d n) (d′ n)) →
          ∀ n → C (w ⨾ Pre C.self d n) (w′ ⨾ Pre C.self d′ n)
  cxPre (hw , (o , o′)) rd rd′ hd n =
    ⨾⊑ (OkRf o) (OkRf o′) hw (preR rd rd′ hd n) , ((o , preR rd rd rd n) , (o′ , preR rd′ rd′ rd′ n))

  -- 部分和对 Pre
  preM : ∀ {d d′ : ℕ → D (hs b) W} → (∀ n → Rf (hs b) (d n)) → (∀ n → Rf (hs b) (d′ n)) → (∀ n → Rel (hs b) (d n) (d′ n)) →
         ∀ n → Rel (hs b) (preL d n) (Pre C.self d′ n)
  preM rd rd′ hd zero = n0⊑
  preM rd rd′ hd (suc n) = ⨾⊑ (rPre rd n) (preR rd′ rd′ rd′ n) (preM rd rd′ hd n) (nwʳ (hd n))
```

## 2 第 0 层进任意层

```agda
U : H → H → Set
U k ly = ∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → D ly W′

Mk : H → H → Set
Mk k ly = ∀ {W₁ j} → W ⊲ W₁ → StH W₁ j k → StH W₁ j ly

Mo : ∀ k ly → U k ly → U k ly → Set
Mo k ly u u′ = ∀ (z z′ : D k W) → Ctx k z z′ → Rel ly (u C.self lW z) (u′ C.self lW z′)

cx00 : ∀ j → Ctx j n0 n0
cx00 hz = z0
cx00 (hs b) = RelM.n0⊑ , (RelM.n0⊑ , RelM.n0⊑)
cx00 (hl f) = tt
cx00 (hΩ g) = tt

-- Int 走部分和, 输出字面就是部分和 (对一切源层)
ILpre : ∀ {k ly V} (ac : AccY k) (zy : NZ ly) (mk : Mk k ly) (u : U k ly) (d : ℕ → D k V) (q : V ⊲ W) (w : D k W) k′ →
        Int ac (preL d k′) q lW zy mk u w ≡ preL (λ n → Int ac (d n) q lW zy mk u (w ⨾ nw q (preL d n))) k′
ILpre ac zy mk u d q w zero = refl
ILpre ac zy mk u d q w (suc k′) = cong (λ t → t ⨾ Int ac (d k′) q lW zy mk u (w ⨾ nw q (preL d k′))) (ILpre ac zy mk u d q w k′)

module Z (ly : H) (zy : NZ ly) where
  IL : AccY hz → Mk hz ly → U hz ly → ∀ {V} → D hz V → V ⊲ W → D hz W → D ly W
  IL ac mk u x q w = Int ac x q lW zy mk u w

  module _ {ac : AccY hz} {mk : Mk hz ly} {u : U hz ly} (mu : Mo hz ly u u) where
    IntS : ∀ {V} (x : D hz V) (q : V ⊲ W) {w w′ : D hz W} → w ⊑₀ w′ → Rel ly (IL ac mk u x q w) (IL ac mk u x q w′)
    IntS n0 q hw = r0 ly
    IntS n1 q {w} {w′} hw = mu w w′ hw
    IntS (x ⨾ y) q {w} {w′} hw =
      r⨾ ly (IntS x q (refl₀ w)) (IntS x q (refl₀ w′)) (IntS x q hw) (IntS y q (sq hw (wl (wr (refl₀ x)))))
    IntS (nl d) q {w} {w′} hw =
      rnl ly (λ n → IntS (d n) q (refl₀ (w ⨾ Pre q d n))) (λ n → IntS (d n) q (refl₀ (w′ ⨾ Pre q d n)))
             (λ n → IntS (d n) q (sq hw (refl₀ (Pre q d n))))
    IntS (ni () v) q hw
    IntS (nκ () v) q hw
    IntS (nw p x) q hw = IntS x (C.⊲-tr p q) hw

    IntR : ∀ {V} (x : D hz V) (q : V ⊲ W) (w : D hz W) → Rf ly (IL ac mk u x q w)
    IntR x q w = IntS x q (refl₀ w)

  PreM : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} {q′ : V′ ⊲ W} → (∀ n → d n ⊑₀ d′ n) → ∀ n → preL d n ⊑₀ Pre q′ d′ n
  PreM hd zero = z0
  PreM hd (suc n) = sq (PreM hd n) (wr (hd n))

  PreM′ : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} {q : V ⊲ W} {q′ : V′ ⊲ W} → (∀ n → d n ⊑₀ d′ n) → ∀ n → Pre q d n ⊑₀ Pre q′ d′ n
  PreM′ hd zero = z0
  PreM′ hd (suc n) = sq (PreM′ hd n) (wl (wr (hd n)))

  IntM₀ : ∀ {ac ac′ : AccY hz} {mk mk′ : Mk hz ly} {u u′ : U hz ly} → Mo hz ly u u → Mo hz ly u′ u′ → Mo hz ly u u′ →
       ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → ∀ (q : V ⊲ W) (q′ : V′ ⊲ W) {w w′ : D hz W} → w ⊑₀ w′ →
       Rel ly (IL ac mk u x q w) (IL ac′ mk′ u′ x′ q′ w′)
  IntM₀ mu mu′ cr z0 q q′ hw = r0 ly
  IntM₀ mu mu′ cr o1 q q′ {w} {w′} hw = cr w w′ hw
  IntM₀ mu mu′ cr (sq {x = x} {x′ = x′} hx hy) q q′ {w} {w′} hw =
    r⨾ ly (IntR mu x q w) (IntR mu′ x′ q′ w′) (IntM₀ mu mu′ cr hx q q′ hw) (IntM₀ mu mu′ cr hy q q′ (sq hw (wl (wr hx))))
  IntM₀ mu mu′ cr (lm {d = d} {d′} hd) q q′ {w} {w′} hw =
    rnl ly (λ n → IntR mu (d n) q _) (λ n → IntR mu′ (d′ n) q′ _) (λ n → IntM₀ mu mu′ cr (hd n) q q′ (sq hw (PreM′ hd n)))
  IntM₀ mu mu′ cr (wl {p = p} h) q q′ hw = IntM₀ mu mu′ cr h (C.⊲-tr p q) q′ hw
  IntM₀ mu mu′ cr (wr {p = p} h) q q′ hw = IntM₀ mu mu′ cr h q (C.⊲-tr p q′) hw
  IntM₀ {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (pr {x = x} {x′} {d} {d′} hx hd k) q q′ {w} {w′} hw =
    subst (λ t → Rel ly (IL ac mk u x q w ⨾ t) (IL ac′ mk′ u′ (x′ ⨾ nl d′) q′ w′)) (sym (ILpre ac zy mk u d q (w ⨾ nw q x) k))
      (rpre ly (IntR mu x q w) (IntR mu′ x′ q′ w′) (λ n → IntR mu (d n) q _) (λ n → IntR mu′ (d′ n) q′ _)
               (IntM₀ mu mu′ cr hx q q′ hw) (λ n → IntM₀ mu mu′ cr (hd n) q q′ (sq (sq hw (wl (wr hx))) (wl (PreM hd n)))) k)
  IntM₀ {ac} {ac′} {mk} {mk′} {u} mu mu′ cr (tr₀ h h′) q q′ {w} hw =
    rtr ly (IntM₀ {ac} {ac} {mk} {mk} {u} {u} mu mu mu h q q (refl₀ w)) (IntM₀ mu mu′ cr h′ q q′ hw)
  IntM₀ mu mu′ cr (u0l h) q q′ {w} {w′} hw = u0L ly (IntM₀ mu mu′ cr h q q′ (tr₀ (sq hw (wl z0)) (u1l (refl₀ w′))))
  IntM₀ mu mu′ cr (u0r h) q q′ {w} {w′} hw = u0R ly (IntM₀ mu mu′ cr h q q′ (tr₀ (u1r (refl₀ w)) (sq hw (wr z0))))
  IntM₀ mu mu′ cr (u1l h) q q′ hw = u1L ly (IntM₀ mu mu′ cr h q q′ hw)
  IntM₀ mu mu′ cr (u1r h) q q′ hw = u1R ly (IntM₀ mu mu′ cr h q q′ hw)
  IntM₀ mu mu′ cr (al {x = x} {y} {z} h) q q′ {w} hw =
    asL ly rX rY rZ (rtr ly (r⨾ ly rX rX rX (r⨾ ly rY rY rY (IntS mu z q (ar′ (sq (refl₀ w) (nwd₀ x y)))))) (IntM₀ mu mu′ cr h q q′ hw))
    where rX = IntR mu x q w ; rY = IntR mu y q (w ⨾ nw q x) ; rZ = IntR mu z q (w ⨾ nw q (x ⨾ y))
  IntM₀ mu mu′ cr (al′ {x = x} {y} {z} h) q q′ {w} hw =
    asL′ ly rX rY rZ (rtr ly (r⨾ ly rXY rXY rXY (IntS mu z q (al (sq (refl₀ w) (nwd₀′ x y))))) (IntM₀ mu mu′ cr h q q′ hw))
    where rX = IntR mu x q w ; rY = IntR mu y q (w ⨾ nw q x) ; rZ = IntR mu z q ((w ⨾ nw q x) ⨾ nw q y) ; rXY = r⨾ ly rX rX rX rY
  IntM₀ mu mu′ cr (ar {x = x} {y} {z} h) q q′ {w′ = w} hw =
    asR ly rX rY rZ (rtr ly (IntM₀ mu mu′ cr h q q′ hw) (r⨾ ly rXY rXY rXY (IntS mu′ z q′ (ar′ (sq (refl₀ w) (nwd₀ x y))))))
    where rX = IntR mu′ x q′ w ; rY = IntR mu′ y q′ (w ⨾ nw q′ x) ; rZ = IntR mu′ z q′ ((w ⨾ nw q′ x) ⨾ nw q′ y) ; rXY = r⨾ ly rX rX rX rY
  IntM₀ mu mu′ cr (ar′ {x = x} {y} {z} h) q q′ {w′ = w} hw =
    asR′ ly rX rY rZ (rtr ly (IntM₀ mu mu′ cr h q q′ hw) (r⨾ ly rX rX rX (r⨾ ly rY rY rY (IntS mu′ z q′ (al (sq (refl₀ w) (nwd₀′ x y)))))))
    where rX = IntR mu′ x q′ w ; rY = IntR mu′ y q′ (w ⨾ nw q′ x) ; rZ = IntR mu′ z q′ (w ⨾ nw q′ (x ⨾ y))
```

## 3 带节点的源层: 对 (良基证明, 推导) 字典序归纳

源层 `hs b` 的关系只在世界 $W$ 上, 所以 `Int` 的位置取 `C.self`; 两边用同一个良基证明与同一个节点嵌入 `mk` (折叠里 `Ai` 两边的 `f r` 与 `mkOf r …` 相同), 分支 `u`, `u′` 不同.

```agda
IntMK : ∀ k → Fin k → (ac : AccY k) → ∀ {ly} (zy : NZ ly) (mk : Mk k ly) {u u′ : U k ly} → Mo k ly u u → Mo k ly u′ u′ → Mo k ly u u′ →
        ∀ {x x′ w w′} → Ctx k x x′ → Ctx k w w′ → Rel ly (Int ac x C.self lW zy mk u w) (Int ac x′ C.self lW zy mk u′ w′)
IntMS : ∀ b → Fin b → (ac : AccY (hs b)) → ∀ {ly} (zy : NZ ly) (mk : Mk (hs b) ly) {u u′ : U (hs b) ly} →
        Mo (hs b) ly u u → Mo (hs b) ly u′ u′ → Mo (hs b) ly u u′ →
        ∀ {x x′ w w′} → Rel (hs b) x x′ → Ctx (hs b) w w′ → Rel ly (Int ac x C.self lW zy mk u w) (Int ac x′ C.self lW zy mk u′ w′)

IntMK hz fk ac {ly} zy mk mu mu′ cr hx hw = Z.IntM₀ ly zy mu mu′ cr hx C.self C.self hw
IntMK (hs b) fk ac zy mk mu mu′ cr hx hw = IntMS b fk ac zy mk mu mu′ cr (proj₁ hx) hw

IntMS b fb ac {ly} zy mk mu mu′ cr RelM.n0⊑ hw = r0 ly
IntMS b fb ac zy mk mu mu′ cr RelM.n1⊑ hw = cr _ _ hw
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.⨾⊑ rx rx′ hx hy) hw =
  r⨾ ly (IntMS b fb ac zy mk mu mu mu rx (cxL (hs b) hw)) (IntMS b fb ac zy mk mu′ mu′ mu′ rx′ (cxR (hs b) hw))
        (IntMS b fb ac zy mk mu mu′ cr hx hw) (IntMS b fb ac zy mk mu mu′ cr hy (CxS.cx⨾ b hw rx rx′ hx))
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.nl⊑ rd rd′ hd) hw =
  rnl ly (λ n → IntMS b fb ac zy mk mu mu mu (rd n) (CxS.cxPre b (cxL (hs b) hw) rd rd rd n))
         (λ n → IntMS b fb ac zy mk mu′ mu′ mu′ (rd′ n) (CxS.cxPre b (cxR (hs b) hw) rd′ rd′ rd′ n))
         (λ n → IntMS b fb ac zy mk mu mu′ cr (hd n) (CxS.cxPre b hw rd rd′ hd n))
IntMS b fb (acc g) {ly} zy mk {u} {u′} mu mu′ cr {w = w} {w′ = w′} (RelM.ni⊑ {k = j} (ss P) {u = v} {u′ = v′} hv hv′ hc) hw =
  rni ly R*
    (λ y y′ l → IntMS b fb (acc g) zy mk′ mu mu mu (hv _ _ (lowIn (hs b) (ss P) (lowOut ly R* l)))
                  (CxS.ctxN b (cxL (hs b) hw)
                     (IntMK j fj (g (ss P)) tt mkR (moV {v} {v} hv) (moV {v} {v} hv) (moV {v} {v} hv) (lowOut ly R* l) (cx00 j))
                     (IntMK j fj (g (ss P)) tt mkR (moV {v} {v} hv) (moV {v} {v} hv) (moV {v} {v} hv) (cxL j (lowOut ly R* l)) (cx00 j))
                     (IntMK j fj (g (ss P)) tt mkR (moV {v} {v} hv) (moV {v} {v} hv) (moV {v} {v} hv) (cxR j (lowOut ly R* l)) (cx00 j))))
    (λ y y′ l → IntMS b fb (acc g) zy mk′ mu′ mu′ mu′ (hv′ _ _ (lowIn (hs b) (ss P) (lowOut ly R* l)))
                  (CxS.ctxN b (cxR (hs b) hw)
                     (IntMK j fj (g (ss P)) tt mkR (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (lowOut ly R* l) (cx00 j))
                     (IntMK j fj (g (ss P)) tt mkR (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (cxL j (lowOut ly R* l)) (cx00 j))
                     (IntMK j fj (g (ss P)) tt mkR (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (cxR j (lowOut ly R* l)) (cx00 j))))
    (λ y y′ l → IntMS b fb (acc g) zy mk′ mu mu′ cr (hc _ _ (lowIn (hs b) (ss P) (lowOut ly R* l)))
                  (CxS.ctxN b hw
                     (IntMK j fj (g (ss P)) tt mkR (moV {v} {v} hv) (moV {v′} {v′} hv′) (moV {v} {v′} hc) (lowOut ly R* l) (cx00 j))
                     (IntMK j fj (g (ss P)) tt mkR (moV {v} {v} hv) (moV {v} {v} hv) (moV {v} {v} hv) (cxL j (lowOut ly R* l)) (cx00 j))
                     (IntMK j fj (g (ss P)) tt mkR (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (cxR j (lowOut ly R* l)) (cx00 j))))
  where
  R* = mk C.self (Kup C.self (ss P))
  mk′ : Mk (hs b) ly
  mk′ p′ = mk (C.⊲-tr C.self p′)
  mkR : Mk j (hs b)
  mkR = mkOf (ss P) C.self
  fj = fin⊲ P fb
  Vb : Set
  Vb = ∀ {W′} → W ⊲ W′ → Lg W′ → Vs (hs b) (ss P) W′ → D (hs b) W′
  -- 节点分支的单调 ⇒ 内层 Int 的分支单调 (不递归)
  moV : ∀ {v₁ v₂ : Vb} → (∀ z z′ → LowT (hs b) (ss P) z z′ → Rel (hs b) (v₁ C.self lW z) (v₂ C.self lW z′)) →
        Mo j (hs b) (λ p′ l′ z′ → v₁ (C.⊲-tr C.self p′) l′ (inS (ss P) z′)) (λ p′ l′ z′ → v₂ (C.⊲-tr C.self p′) l′ (inS (ss P) z′))
  moV h z z′ c = h (inS (ss P) z) (inS (ss P) z′) (lowIn (hs b) (ss P) c)
IntMS b fb ac zy mk mu mu′ cr (RelM.nwˡ h) hw = IntMS b fb ac zy mk mu mu′ cr h hw
IntMS b fb ac zy mk mu mu′ cr (RelM.nwʳ h) hw = IntMS b fb ac zy mk mu mu′ cr h hw
IntMS b fb ac zy mk mu mu′ cr (RelM.nwᵉ h) hw = IntMS b fb ac zy mk mu mu′ cr h hw
IntMS b fb ac {ly} zy mk {u} mu mu′ cr (RelM.tr h h′) hw =
  rtr ly (IntMS b fb ac zy mk {u} {u} mu mu mu h (cxL (hs b) hw)) (IntMS b fb ac zy mk mu mu′ cr h′ hw)
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.u0ˡ h) hw = u0L ly (IntMS b fb ac zy mk mu mu′ cr h (CxS.cx0l b hw))
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.u0ʳ h) hw = u0R ly (IntMS b fb ac zy mk mu mu′ cr h (CxS.cx0r b hw))
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.u1ˡ h) hw = u1L ly (IntMS b fb ac zy mk mu mu′ cr h hw)
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.u1ʳ h) hw = u1R ly (IntMS b fb ac zy mk mu mu′ cr h hw)
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.asˡ rx ry rz h) hw =
  asL ly rX rY rZ (rtr ly (r⨾ ly rX rX rX (r⨾ ly rY rY rY (IntMS b fb ac zy mk mu mu mu rz (CxS.cxas b w0 rx ry)))) (IntMS b fb ac zy mk mu mu′ cr h hw))
  where
  w0 = cxL (hs b) hw
  rX = IntMS b fb ac zy mk mu mu mu rx w0
  rY = IntMS b fb ac zy mk mu mu mu ry (CxS.cx⨾ b w0 rx rx rx)
  rZ = IntMS b fb ac zy mk mu mu mu rz (CxS.cx⨾ b w0 (RelM.⨾⊑ rx rx rx ry) (RelM.⨾⊑ rx rx rx ry) (RelM.⨾⊑ rx rx rx ry))
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.asˡ′ rx ry rz h) hw =
  asL′ ly rX rY rZ (rtr ly (r⨾ ly rXY rXY rXY (IntMS b fb ac zy mk mu mu mu rz (CxS.cxas′ b w0 rx ry))) (IntMS b fb ac zy mk mu mu′ cr h hw))
  where
  w0 = cxL (hs b) hw
  rX = IntMS b fb ac zy mk mu mu mu rx w0
  rY = IntMS b fb ac zy mk mu mu mu ry (CxS.cx⨾ b w0 rx rx rx)
  rZ = IntMS b fb ac zy mk mu mu mu rz (CxS.cx⨾ b (CxS.cx⨾ b w0 rx rx rx) ry ry ry)
  rXY = r⨾ ly rX rX rX rY
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.asʳ rx ry rz h) hw =
  asR ly rX rY rZ (rtr ly (IntMS b fb ac zy mk mu mu′ cr h hw) (r⨾ ly rXY rXY rXY (IntMS b fb ac zy mk mu′ mu′ mu′ rz (CxS.cxas b w0 rx ry))))
  where
  w0 = cxR (hs b) hw
  rX = IntMS b fb ac zy mk mu′ mu′ mu′ rx w0
  rY = IntMS b fb ac zy mk mu′ mu′ mu′ ry (CxS.cx⨾ b w0 rx rx rx)
  rZ = IntMS b fb ac zy mk mu′ mu′ mu′ rz (CxS.cx⨾ b (CxS.cx⨾ b w0 rx rx rx) ry ry ry)
  rXY = r⨾ ly rX rX rX rY
IntMS b fb ac {ly} zy mk mu mu′ cr (RelM.asʳ′ rx ry rz h) hw =
  asR′ ly rX rY rZ (rtr ly (IntMS b fb ac zy mk mu mu′ cr h hw) (r⨾ ly rX rX rX (r⨾ ly rY rY rY (IntMS b fb ac zy mk mu′ mu′ mu′ rz (CxS.cxas′ b w0 rx ry)))))
  where
  w0 = cxR (hs b) hw
  rX = IntMS b fb ac zy mk mu′ mu′ mu′ rx w0
  rY = IntMS b fb ac zy mk mu′ mu′ mu′ ry (CxS.cx⨾ b w0 rx rx rx)
  rZ = IntMS b fb ac zy mk mu′ mu′ mu′ rz (CxS.cx⨾ b w0 (RelM.⨾⊑ rx rx rx ry) (RelM.⨾⊑ rx rx rx ry) (RelM.⨾⊑ rx rx rx ry))
IntMS b fb ac {ly} zy mk {u} {u′} mu mu′ cr {w = w} {w′ = w′} (RelM.pre⊑ {x} {x′} {d} {d′} rx rx′ rd rd′ hx hd k) hw =
  subst (λ t → Rel ly (Int ac x C.self lW zy mk u w ⨾ t) (Int ac (x′ ⨾ nl d′) C.self lW zy mk u′ w′))
        (sym (ILpre ac zy mk u d C.self (w ⨾ nw C.self x) k))
    (rpre ly (IntMS b fb ac zy mk mu mu mu rx (cxL (hs b) hw)) (IntMS b fb ac zy mk mu′ mu′ mu′ rx′ (cxR (hs b) hw))
             (λ n → IntMS b fb ac zy mk mu mu mu (rd n) (cn n)) (λ n → IntMS b fb ac zy mk mu′ mu′ mu′ (rd′ n) (CxS.cxPre b w1′ rd′ rd′ rd′ n))
             (IntMS b fb ac zy mk mu mu′ cr hx hw) (λ n → IntMS b fb ac zy mk mu mu′ cr (hd n) (cx n)) k)
  where
  w1 = CxS.cx⨾ b (cxL (hs b) hw) rx rx rx
  w1′ = CxS.cx⨾ b (cxR (hs b) hw) rx′ rx′ rx′
  w1x = CxS.cx⨾ b hw rx rx′ hx
  rP = λ n → R.rPre b rd n
  cn : ∀ n → Ctx (hs b) ((w ⨾ nw C.self x) ⨾ nw C.self (preL d n)) ((w ⨾ nw C.self x) ⨾ nw C.self (preL d n))
  cn n = CxS.cx⨾ b w1 (rP n) (rP n) (rP n)
  cx : ∀ n → Ctx (hs b) ((w ⨾ nw C.self x) ⨾ nw C.self (preL d n)) ((w′ ⨾ nw C.self x′) ⨾ Pre C.self d′ n)
  cx n = RelM.⨾⊑ (CxS.okRf b (proj₁ (proj₂ w1x))) (CxS.okRf b (proj₂ (proj₂ w1x))) (proj₁ w1x) (RelM.nwˡ (CxS.preM b rd rd′ hd n)) ,
         ((proj₁ (proj₂ w1x) , R.rnw b (rP n)) , (proj₂ (proj₂ w1x) , CxS.preR b rd′ rd′ rd′ n))
```
