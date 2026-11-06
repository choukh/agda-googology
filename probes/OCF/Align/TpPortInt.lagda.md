# 两种种类的单调 (九): `Int` 单调

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [MonoPort7Int](MonoPort7Int.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. 两种种类的 `Int` 多一个参数 (`NZ₁` 的搬运), 所以 `ILpre`, `Z`, `IntMK`, `IntMS` 都多一个 `zy₁`; 节点一句内层 `Int` 多 `NZ₁-S r`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY; D)
module OCF.Align.TpPortInt (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy using (hl; hΩ)
open import OCF.Align.HtTowerFTree using (ss; sl; sL; StH; Vs; NZ; NZ-S; NZ₁; NZ₁-S; acc; Int; Pre; mkOf; Kup; outS; inS; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; ≤rf; ≤tr) renaming (_≤_ to _≤ʷ_)
open import OCF.Align.TpPortDef using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀; preL)
  renaming (tr to tr₀; nwd to nwd₀; nwd′ to nwd₀′)
open import OCF.Align.TpPortRel Λ lΛ oΛ lW t₀
open import OCF.Align.TpPortRelM lW using (module RelM)

```
```agda
module CxS (L : Ht) where
  open RL L hiding (Rf)

  Rf′ : D L W → Set
  Rf′ x = RelN L x x

  C : D L W → D L W → Set
  C = CxN L

  okRf : ∀ {w} → Ok w → Rf′ w
  okRf = OkRf

  cx⨾ : ∀ {w w′ x x′} → C w w′ → Rf′ x → Rf′ x′ → RelN L x x′ → C (w ⨾ nw ≤rf x) (w′ ⨾ nw ≤rf x′)
  cx⨾ (hw , (o , o′)) rx rx′ hx = ⨾⊑ (OkRf o) (OkRf o′) hw (nwˡ (nwʳ hx)) , ((o , rnw rx) , (o′ , rnw rx′))

  cx0l : ∀ {w w′} → C w w′ → C (w ⨾ nw ≤rf n0) w′
  cx0l (hw , (o , o′)) = tr (⨾⊑ (OkRf o) (OkRf o) (OkRf o) (nwˡ n0⊑)) (u1ˡ hw) , ((o , rnw n0⊑) , o′)

  cx0r : ∀ {w w′} → C w w′ → C w (w′ ⨾ nw ≤rf n0)
  cx0r (hw , (o , o′)) = tr (u1ʳ hw) (⨾⊑ (OkRf o′) (OkRf o′) (OkRf o′) n0⊑) , (o , (o′ , rnw n0⊑))

  cxas : ∀ {w w′ x y} → C w w′ → Rf′ x → Rf′ y → C (w ⨾ nw ≤rf (x ⨾ y)) ((w ⨾ nw ≤rf x) ⨾ nw ≤rf y)
  cxas (_ , (o , _)) rx ry =
    asʳ′ (OkRf o) (rnw rx) (rnw ry) (⨾⊑ (OkRf o) (OkRf o) (OkRf o) (nwd rx ry)) , ((o , rnw (⨾⊑ rx rx rx ry)) , ((o , rnw rx) , rnw ry))

  cxas′ : ∀ {w w′ x y} → C w w′ → Rf′ x → Rf′ y → C ((w ⨾ nw ≤rf x) ⨾ nw ≤rf y) (w ⨾ nw ≤rf (x ⨾ y))
  cxas′ (_ , (o , _)) rx ry =
    asˡ (OkRf o) (rnw rx) (rnw ry) (⨾⊑ (OkRf o) (OkRf o) (OkRf o) (nwd′ rx ry)) , (((o , rnw rx) , rnw ry) , (o , rnw (⨾⊑ rx rx rx ry)))

  -- 节点分支的上下文: nw w ⨾ (内层 Int)
  ctxN : ∀ {w w′ I I′} → C w w′ → RelN L I I′ → Rf′ I → Rf′ I′ → C (nw ≤rf w ⨾ I) (nw ≤rf w′ ⨾ I′)
  ctxN {w} {w′} (hw , (o , o′)) hI r r′ =
    ⨾⊑ (rnw (OkRf {w} o)) (rnw (OkRf {w′} o′)) (nwˡ (nwʳ hw)) hI , ((rnw (OkRf {w} o) , r) , (rnw (OkRf {w′} o′) , r′))

  -- Int 走极限时的上下文: w ⨾ Pre d n
  preR : ∀ {d d′ : ℕ → D L W} → (∀ n → Rf′ (d n)) → (∀ n → Rf′ (d′ n)) → (∀ n → RelN L (d n) (d′ n)) →
         ∀ n → RelN L (Pre ≤rf d n) (Pre ≤rf d′ n)
  preR rd rd′ hd zero = n0⊑
  preR rd rd′ hd (suc n) = ⨾⊑ (preR rd rd rd n) (preR rd′ rd′ rd′ n) (preR rd rd′ hd n) (nwˡ (nwʳ (hd n)))

  cxPre : ∀ {w w′} {d d′ : ℕ → D L W} → C w w′ → (∀ n → Rf′ (d n)) → (∀ n → Rf′ (d′ n)) → (∀ n → RelN L (d n) (d′ n)) →
          ∀ n → C (w ⨾ Pre ≤rf d n) (w′ ⨾ Pre ≤rf d′ n)
  cxPre (hw , (o , o′)) rd rd′ hd n =
    ⨾⊑ (OkRf o) (OkRf o′) hw (preR rd rd′ hd n) , ((o , preR rd rd rd n) , (o′ , preR rd′ rd′ rd′ n))

  -- 部分和对 Pre
  preM : ∀ {d d′ : ℕ → D L W} → (∀ n → Rf′ (d n)) → (∀ n → Rf′ (d′ n)) → (∀ n → RelN L (d n) (d′ n)) →
         ∀ n → RelN L (preL d n) (Pre ≤rf d′ n)
  preM rd rd′ hd zero = n0⊑
  preM rd rd′ hd (suc n) = ⨾⊑ (rPre rd n) (preR rd′ rd′ rd′ n) (preM rd rd′ hd n) (nwʳ (hd n))
```
```agda
U : Ht → Ht → Set
U k ly = ∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → D k W′ → D ly W′

Mk : Ht → Ht → Set
Mk k ly = ∀ {W₁ j} → W ≤ʷ W₁ → StH W₁ j k → StH W₁ j ly

Mo : ∀ k ly → U k ly → U k ly → Set
Mo k ly u u′ = ∀ (z z′ : D k W) → Ctx k z z′ → Rel ly (u ≤rf lW z) (u′ ≤rf lW z′)

cx00 : ∀ j → Ctx j n0 n0
cx00 hz = z0
cx00 (hs b) = RelM.n0⊑ , (RelM.n0⊑ , RelM.n0⊑)
cx00 (hl f) = RelM.n0⊑ , (RelM.n0⊑ , RelM.n0⊑)
cx00 (hΩ _ g) = tt

-- Int 走部分和, 输出字面就是部分和 (对一切源层)
ILpre : ∀ {k ly V} (ac : AccY k) (zy : NZ ly) (zy₁ : NZ₁ k → NZ₁ ly) (mk : Mk k ly) (u : U k ly) (d : ℕ → D k V) (q : V ≤ʷ W) (w : D k W) k′ →
        Int ac (preL d k′) q lW zy zy₁ mk u w ≡ preL (λ n → Int ac (d n) q lW zy zy₁ mk u (w ⨾ nw q (preL d n))) k′
ILpre ac zy zy₁ mk u d q w zero = refl
ILpre ac zy zy₁ mk u d q w (suc k′) = cong (λ t → t ⨾ Int ac (d k′) q lW zy zy₁ mk u (w ⨾ nw q (preL d k′))) (ILpre ac zy zy₁ mk u d q w k′)

module Z (ly : Ht) (zy : NZ ly) (zy₁ : NZ₁ hz → NZ₁ ly) where
  IL : AccY hz → Mk hz ly → U hz ly → ∀ {V} → D hz V → V ≤ʷ W → D hz W → D ly W
  IL ac mk u x q w = Int ac x q lW zy zy₁ mk u w

  module _ {ac : AccY hz} {mk : Mk hz ly} {u : U hz ly} (mu : Mo hz ly u u) where
    IntS : ∀ {V} (x : D hz V) (q : V ≤ʷ W) {w w′ : D hz W} → w ⊑₀ w′ → Rel ly (IL ac mk u x q w) (IL ac mk u x q w′)
    IntS n0 q hw = r0 ly
    IntS n1 q {w} {w′} hw = mu w w′ hw
    IntS (x ⨾ y) q {w} {w′} hw =
      r⨾ ly (IntS x q (refl₀ w)) (IntS x q (refl₀ w′)) (IntS x q hw) (IntS y q (sq hw (wl (wr (refl₀ x)))))
    IntS (nl d) q {w} {w′} hw =
      rnl ly (λ n → IntS (d n) q (refl₀ (w ⨾ Pre q d n))) (λ n → IntS (d n) q (refl₀ (w′ ⨾ Pre q d n)))
             (λ n → IntS (d n) q (sq hw (refl₀ (Pre q d n))))
    IntS (ni () v) q hw
    IntS (nκ () v) q hw
    IntS (nμ () v) q hw
    IntS (nw p x) q hw = IntS x (≤tr p q) hw

    IntR : ∀ {V} (x : D hz V) (q : V ≤ʷ W) (w : D hz W) → Rf ly (IL ac mk u x q w)
    IntR x q w = IntS x q (refl₀ w)

  PreM : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} {q′ : V′ ≤ʷ W} → (∀ n → d n ⊑₀ d′ n) → ∀ n → preL d n ⊑₀ Pre q′ d′ n
  PreM hd zero = z0
  PreM hd (suc n) = sq (PreM hd n) (wr (hd n))

  PreM′ : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} {q : V ≤ʷ W} {q′ : V′ ≤ʷ W} → (∀ n → d n ⊑₀ d′ n) → ∀ n → Pre q d n ⊑₀ Pre q′ d′ n
  PreM′ hd zero = z0
  PreM′ hd (suc n) = sq (PreM′ hd n) (wl (wr (hd n)))

  IntM₀ : ∀ {ac ac′ : AccY hz} {mk mk′ : Mk hz ly} {u u′ : U hz ly} → Mo hz ly u u → Mo hz ly u′ u′ → Mo hz ly u u′ →
       ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → ∀ (q : V ≤ʷ W) (q′ : V′ ≤ʷ W) {w w′ : D hz W} → w ⊑₀ w′ →
       Rel ly (IL ac mk u x q w) (IL ac′ mk′ u′ x′ q′ w′)
  IntM₀ mu mu′ cr z0 q q′ hw = r0 ly
  IntM₀ mu mu′ cr o1 q q′ {w} {w′} hw = cr w w′ hw
  IntM₀ mu mu′ cr (sq {x = x} {x′ = x′} hx hy) q q′ {w} {w′} hw =
    r⨾ ly (IntR mu x q w) (IntR mu′ x′ q′ w′) (IntM₀ mu mu′ cr hx q q′ hw) (IntM₀ mu mu′ cr hy q q′ (sq hw (wl (wr hx))))
  IntM₀ mu mu′ cr (lm {d = d} {d′} hd) q q′ {w} {w′} hw =
    rnl ly (λ n → IntR mu (d n) q _) (λ n → IntR mu′ (d′ n) q′ _) (λ n → IntM₀ mu mu′ cr (hd n) q q′ (sq hw (PreM′ hd n)))
  IntM₀ mu mu′ cr (wl {p = p} h) q q′ hw = IntM₀ mu mu′ cr h (≤tr p q) q′ hw
  IntM₀ mu mu′ cr (wr {p = p} h) q q′ hw = IntM₀ mu mu′ cr h q (≤tr p q′) hw
  IntM₀ {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (pr {x = x} {x′} {d} {d′} hx hd k) q q′ {w} {w′} hw =
    subst (λ t → Rel ly (IL ac mk u x q w ⨾ t) (IL ac′ mk′ u′ (x′ ⨾ nl d′) q′ w′)) (sym (ILpre ac zy zy₁ mk u d q (w ⨾ nw q x) k))
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
```agda
-- 一般层的分支单调 (上下文取 CxN), 上下文两边自比, 节点子层的有限
MoN : ∀ L ly → U L ly → U L ly → Set
MoN L ly u u′ = ∀ (z z′ : D L W) → CxN L z z′ → Rel ly (u ≤rf lW z) (u′ ≤rf lW z′)

cxLN : ∀ L {z z′} → CxN L z z′ → CxN L z z
cxLN L (_ , (o , _)) = RL.OkRf L o , (o , o)

cxRN : ∀ L {z z′} → CxN L z z′ → CxN L z′ z′
cxRN L (_ , (_ , o′)) = RL.OkRf L o′ , (o′ , o′)

finS : ∀ {L j} → StH W j L → Fin L → Fin j
finS (ss P) f = fin⊲ P f
finS (sl n P) f = fin⊲ P (f n)
finS (sL e P) ()

-- 带节点的层上 Rel 就是 RelN (两个方向, 定义性)
toN : ∀ L → NZ L → Fin L → ∀ {x y} → Rel L x y → RelN L x y
toN (hs b) _ _ h = h
toN (hl f) _ _ h = h

fromN : ∀ L → NZ L → Fin L → ∀ {x y} → RelN L x y → Rel L x y
fromN (hs b) _ _ h = h
fromN (hl f) _ _ h = h

IntMK : ∀ k → Fin k → (ac : AccY k) → ∀ {ly} (zy : NZ ly) (zy₁ : NZ₁ k → NZ₁ ly) (mk : Mk k ly) {u u′ : U k ly} → Mo k ly u u → Mo k ly u′ u′ → Mo k ly u u′ →
        ∀ {x x′ w w′} → Ctx k x x′ → Ctx k w w′ → Rel ly (Int ac x ≤rf lW zy zy₁ mk u w) (Int ac x′ ≤rf lW zy zy₁ mk u′ w′)
IntMS : ∀ L → Fin L → (ac : AccY L) → ∀ {ly} (zy : NZ ly) (zy₁ : NZ₁ L → NZ₁ ly) (mk : Mk L ly) {u u′ : U L ly} →
        MoN L ly u u → MoN L ly u′ u′ → MoN L ly u u′ →
        ∀ {x x′ w w′} → RelN L x x′ → CxN L w w′ → Rel ly (Int ac x ≤rf lW zy zy₁ mk u w) (Int ac x′ ≤rf lW zy zy₁ mk u′ w′)

IntMK hz fk ac {ly} zy zy₁ mk mu mu′ cr hx hw = Z.IntM₀ ly zy zy₁ mu mu′ cr hx ≤rf ≤rf hw
IntMK (hs b) fk ac zy zy₁ mk mu mu′ cr hx hw = IntMS (hs b) fk ac zy zy₁ mk mu mu′ cr (proj₁ hx) hw
IntMK (hl f) fk ac zy zy₁ mk mu mu′ cr hx hw = IntMS (hl f) fk ac zy zy₁ mk mu mu′ cr (proj₁ hx) hw

IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr RelM.n0⊑ hw = r0 ly
IntMS L fb ac zy zy₁ mk mu mu′ cr RelM.n1⊑ hw = cr _ _ hw
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.⨾⊑ rx rx′ hx hy) hw =
  r⨾ ly (IntMS L fb ac zy zy₁ mk mu mu mu rx (cxLN L hw)) (IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ rx′ (cxRN L hw))
        (IntMS L fb ac zy zy₁ mk mu mu′ cr hx hw) (IntMS L fb ac zy zy₁ mk mu mu′ cr hy (CxS.cx⨾ L hw rx rx′ hx))
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.nl⊑ rd rd′ hd) hw =
  rnl ly (λ n → IntMS L fb ac zy zy₁ mk mu mu mu (rd n) (CxS.cxPre L (cxLN L hw) rd rd rd n))
         (λ n → IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ (rd′ n) (CxS.cxPre L (cxRN L hw) rd′ rd′ rd′ n))
         (λ n → IntMS L fb ac zy zy₁ mk mu mu′ cr (hd n) (CxS.cxPre L hw rd rd′ hd n))
IntMS L fb (acc g) {ly} zy zy₁ mk {u} {u′} mu mu′ cr {w = w} {w′ = w′} (RelM.ni⊑ {k = j} r {u = v} {u′ = v′} hv hv′ hc) hw =
  rni ly R*
    (λ y y′ l → IntMS L fb (acc g) zy zy₁ mk′ mu mu mu (hv _ _ (lowIn L r (lowOut ly R* l)))
                  (CxS.ctxN L (cxLN L hw)
                     (toN L (NZ-S r) fb (IntMK j fj (g r) (NZ-S r) (NZ₁-S r) mkR (moV {v} {v} hv) (moV {v} {v} hv) (moV {v} {v} hv) (lowOut ly R* l) (cx00 j)))
                     (toN L (NZ-S r) fb (IntMK j fj (g r) (NZ-S r) (NZ₁-S r) mkR (moV {v} {v} hv) (moV {v} {v} hv) (moV {v} {v} hv) (cxL j (lowOut ly R* l)) (cx00 j)))
                     (toN L (NZ-S r) fb (IntMK j fj (g r) (NZ-S r) (NZ₁-S r) mkR (moV {v} {v} hv) (moV {v} {v} hv) (moV {v} {v} hv) (cxR j (lowOut ly R* l)) (cx00 j)))))
    (λ y y′ l → IntMS L fb (acc g) zy zy₁ mk′ mu′ mu′ mu′ (hv′ _ _ (lowIn L r (lowOut ly R* l)))
                  (CxS.ctxN L (cxRN L hw)
                     (toN L (NZ-S r) fb (IntMK j fj (g r) (NZ-S r) (NZ₁-S r) mkR (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (lowOut ly R* l) (cx00 j)))
                     (toN L (NZ-S r) fb (IntMK j fj (g r) (NZ-S r) (NZ₁-S r) mkR (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (cxL j (lowOut ly R* l)) (cx00 j)))
                     (toN L (NZ-S r) fb (IntMK j fj (g r) (NZ-S r) (NZ₁-S r) mkR (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (cxR j (lowOut ly R* l)) (cx00 j)))))
    (λ y y′ l → IntMS L fb (acc g) zy zy₁ mk′ mu mu′ cr (hc _ _ (lowIn L r (lowOut ly R* l)))
                  (CxS.ctxN L hw
                     (toN L (NZ-S r) fb (IntMK j fj (g r) (NZ-S r) (NZ₁-S r) mkR (moV {v} {v} hv) (moV {v′} {v′} hv′) (moV {v} {v′} hc) (lowOut ly R* l) (cx00 j)))
                     (toN L (NZ-S r) fb (IntMK j fj (g r) (NZ-S r) (NZ₁-S r) mkR (moV {v} {v} hv) (moV {v} {v} hv) (moV {v} {v} hv) (cxL j (lowOut ly R* l)) (cx00 j)))
                     (toN L (NZ-S r) fb (IntMK j fj (g r) (NZ-S r) (NZ₁-S r) mkR (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (moV {v′} {v′} hv′) (cxR j (lowOut ly R* l)) (cx00 j)))))
  where
  R* = mk ≤rf (Kup ≤rf r)
  mk′ : Mk L ly
  mk′ p′ = mk (≤tr ≤rf p′)
  mkR : Mk j L
  mkR = mkOf r ≤rf
  fj = finS r fb
  Vb : Set
  Vb = ∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → Vs L r W′ → D L W′
  -- 节点分支的单调 ⇒ 内层 Int 的分支单调 (不递归)
  moV : ∀ {v₁ v₂ : Vb} → (∀ z z′ → LowT L r z z′ → RelN L (v₁ ≤rf lW z) (v₂ ≤rf lW z′)) →
        Mo j L (λ p′ l′ z′ → v₁ (≤tr ≤rf p′) l′ (inS r z′)) (λ p′ l′ z′ → v₂ (≤tr ≤rf p′) l′ (inS r z′))
  moV h z z′ c = fromN L (NZ-S r) fb (h (inS r z) (inS r z′) (lowIn L r c))
IntMS L fb ac zy zy₁ mk mu mu′ cr (RelM.nwˡ h) hw = IntMS L fb ac zy zy₁ mk mu mu′ cr h hw
IntMS L fb ac zy zy₁ mk mu mu′ cr (RelM.nwʳ h) hw = IntMS L fb ac zy zy₁ mk mu mu′ cr h hw
IntMS L fb ac zy zy₁ mk mu mu′ cr (RelM.nwᵉ h) hw = IntMS L fb ac zy zy₁ mk mu mu′ cr h hw
IntMS L fb ac {ly} zy zy₁ mk {u} mu mu′ cr (RelM.tr h h′) hw =
  rtr ly (IntMS L fb ac zy zy₁ mk {u} {u} mu mu mu h (cxLN L hw)) (IntMS L fb ac zy zy₁ mk mu mu′ cr h′ hw)
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.u0ˡ h) hw = u0L ly (IntMS L fb ac zy zy₁ mk mu mu′ cr h (CxS.cx0l L hw))
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.u0ʳ h) hw = u0R ly (IntMS L fb ac zy zy₁ mk mu mu′ cr h (CxS.cx0r L hw))
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.u1ˡ h) hw = u1L ly (IntMS L fb ac zy zy₁ mk mu mu′ cr h hw)
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.u1ʳ h) hw = u1R ly (IntMS L fb ac zy zy₁ mk mu mu′ cr h hw)
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.asˡ rx ry rz h) hw =
  asL ly rX rY rZ (rtr ly (r⨾ ly rX rX rX (r⨾ ly rY rY rY (IntMS L fb ac zy zy₁ mk mu mu mu rz (CxS.cxas L w0 rx ry)))) (IntMS L fb ac zy zy₁ mk mu mu′ cr h hw))
  where
  w0 = cxLN L hw
  rX = IntMS L fb ac zy zy₁ mk mu mu mu rx w0
  rY = IntMS L fb ac zy zy₁ mk mu mu mu ry (CxS.cx⨾ L w0 rx rx rx)
  rZ = IntMS L fb ac zy zy₁ mk mu mu mu rz (CxS.cx⨾ L w0 (RelM.⨾⊑ rx rx rx ry) (RelM.⨾⊑ rx rx rx ry) (RelM.⨾⊑ rx rx rx ry))
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.asˡ′ rx ry rz h) hw =
  asL′ ly rX rY rZ (rtr ly (r⨾ ly rXY rXY rXY (IntMS L fb ac zy zy₁ mk mu mu mu rz (CxS.cxas′ L w0 rx ry))) (IntMS L fb ac zy zy₁ mk mu mu′ cr h hw))
  where
  w0 = cxLN L hw
  rX = IntMS L fb ac zy zy₁ mk mu mu mu rx w0
  rY = IntMS L fb ac zy zy₁ mk mu mu mu ry (CxS.cx⨾ L w0 rx rx rx)
  rZ = IntMS L fb ac zy zy₁ mk mu mu mu rz (CxS.cx⨾ L (CxS.cx⨾ L w0 rx rx rx) ry ry ry)
  rXY = r⨾ ly rX rX rX rY
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.asʳ rx ry rz h) hw =
  asR ly rX rY rZ (rtr ly (IntMS L fb ac zy zy₁ mk mu mu′ cr h hw) (r⨾ ly rXY rXY rXY (IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ rz (CxS.cxas L w0 rx ry))))
  where
  w0 = cxRN L hw
  rX = IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ rx w0
  rY = IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ ry (CxS.cx⨾ L w0 rx rx rx)
  rZ = IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ rz (CxS.cx⨾ L (CxS.cx⨾ L w0 rx rx rx) ry ry ry)
  rXY = r⨾ ly rX rX rX rY
IntMS L fb ac {ly} zy zy₁ mk mu mu′ cr (RelM.asʳ′ rx ry rz h) hw =
  asR′ ly rX rY rZ (rtr ly (IntMS L fb ac zy zy₁ mk mu mu′ cr h hw) (r⨾ ly rX rX rX (r⨾ ly rY rY rY (IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ rz (CxS.cxas′ L w0 rx ry)))))
  where
  w0 = cxRN L hw
  rX = IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ rx w0
  rY = IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ ry (CxS.cx⨾ L w0 rx rx rx)
  rZ = IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ rz (CxS.cx⨾ L w0 (RelM.⨾⊑ rx rx rx ry) (RelM.⨾⊑ rx rx rx ry) (RelM.⨾⊑ rx rx rx ry))
IntMS L fb ac {ly} zy zy₁ mk {u} {u′} mu mu′ cr {w = w} {w′ = w′} (RelM.pre⊑ {x} {x′} {d} {d′} rx rx′ rd rd′ hx hd k) hw =
  subst (λ t → Rel ly (Int ac x ≤rf lW zy zy₁ mk u w ⨾ t) (Int ac (x′ ⨾ nl d′) ≤rf lW zy zy₁ mk u′ w′))
        (sym (ILpre ac zy zy₁ mk u d ≤rf (w ⨾ nw ≤rf x) k))
    (rpre ly (IntMS L fb ac zy zy₁ mk mu mu mu rx (cxLN L hw)) (IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ rx′ (cxRN L hw))
             (λ n → IntMS L fb ac zy zy₁ mk mu mu mu (rd n) (cn n)) (λ n → IntMS L fb ac zy zy₁ mk mu′ mu′ mu′ (rd′ n) (CxS.cxPre L w1′ rd′ rd′ rd′ n))
             (IntMS L fb ac zy zy₁ mk mu mu′ cr hx hw) (λ n → IntMS L fb ac zy zy₁ mk mu mu′ cr (hd n) (cx n)) k)
  where
  w1 = CxS.cx⨾ L (cxLN L hw) rx rx rx
  w1′ = CxS.cx⨾ L (cxRN L hw) rx′ rx′ rx′
  w1x = CxS.cx⨾ L hw rx rx′ hx
  rP = λ n → RL.rPre L rd n
  cn : ∀ n → CxN L ((w ⨾ nw ≤rf x) ⨾ nw ≤rf (preL d n)) ((w ⨾ nw ≤rf x) ⨾ nw ≤rf (preL d n))
  cn n = CxS.cx⨾ L w1 (rP n) (rP n) (rP n)
  cx : ∀ n → CxN L ((w ⨾ nw ≤rf x) ⨾ nw ≤rf (preL d n)) ((w′ ⨾ nw ≤rf x′) ⨾ Pre ≤rf d′ n)
  cx n = RelM.⨾⊑ (CxS.okRf L (proj₁ (proj₂ w1x))) (CxS.okRf L (proj₂ (proj₂ w1x))) (proj₁ w1x) (RelM.nwˡ (CxS.preM L rd rd′ hd n)) ,
         ((proj₁ (proj₂ w1x) , RL.rnw L (rP n)) , (proj₂ (proj₂ w1x) , CxS.preR L rd′ rd′ rd′ n))
```
