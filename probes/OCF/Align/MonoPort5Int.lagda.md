# 第三站 (二): 第 0 层树嵌进第 1 层, 对结构关系单调

> 不含记号. 入口 [MonoPort5](MonoPort5.lagda.md). 实例 3 里第 1 层节点的动作 `Ai` 把坐标 $z$ (第 0 层树) 经 `Int` 嵌进第 1 层, 作分支运行的**上下文**: `nw p w ⨾ Int z`. 第 1 层的上下文又被第 2 层节点的 `Ai` 当坐标读, 所以第 1 层的上下文关系必须是 $\sqsubseteq_1$, 而 `Int` 必须把 $\sqsubseteq_0$ 送到 $\sqsubseteq_1$. 这一件在实例 2 不出现 (那里第 1 层是顶层, 上下文不被读); 上一组的缺件表没有列它.
>
> - `IntS`: 分支 $u$ 对坐标单调 ⇒ `Int u x` 对上下文单调 (对树 $x$ 归纳), 于是自比.
> - `IntM`: 三条分支前提 (同 `ni⊑` 的三个字段) 与 $x\sqsubseteq_0x'$, $w\sqsubseteq_0w'$ ⇒ `Int u x w` $\sqsubseteq_1$ `Int u' x' w'` (对推导归纳). 部分和那一句要 `Int` 走部分和的输出字面就是部分和 (`ILpre`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
module OCF.Align.MonoPort5Int {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (D; hz; AccY; StH; Int; Pre; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.MonoPort5Rel lW
open import OCF.Align.StrRelDef lW using (nwd; nwd′)

U₁ : Set
U₁ = ∀ {W′} → W ⊲ W′ → Lg W′ → D hz W′ → D L1 W′

Mk : Set
Mk = ∀ {W₁ j} → W ⊲ W₁ → StH W₁ j hz → StH W₁ j L1

IL : AccY hz → Mk → U₁ → ∀ {V} → D hz V → V ⊲ W → D hz W → D L1 W
IL ac mk u x q w = Int ac x q lW tt mk u w

Mo : U₁ → U₁ → Set
Mo u u′ = ∀ (z z′ : D hz W) → z ⊑₀ z′ → u C.self lW z ⊑₁ u′ C.self lW z′

module _ {ac : AccY hz} {mk : Mk} {u : U₁} (mu : Mo u u) where
  IntS : ∀ {V} (x : D hz V) (q : V ⊲ W) {w w′ : D hz W} → w ⊑₀ w′ → IL ac mk u x q w ⊑₁ IL ac mk u x q w′
  IntS n0 q hw = R1.n0⊑
  IntS n1 q {w} {w′} hw = mu w w′ hw
  IntS (x ⨾ y) q {w} {w′} hw =
    R1.⨾⊑ (IntS x q (refl₀ w)) (IntS x q (refl₀ w′)) (IntS x q hw) (IntS y q (sq hw (wl (wr (refl₀ x)))))
  IntS (nl d) q {w} {w′} hw =
    R1.nl⊑ (λ n → IntS (d n) q (refl₀ (w ⨾ Pre q d n))) (λ n → IntS (d n) q (refl₀ (w′ ⨾ Pre q d n)))
           (λ n → IntS (d n) q (sq hw (refl₀ (Pre q d n))))
  IntS (ni () v) q hw
  IntS (nκ () v) q hw
  IntS (nw p x) q hw = IntS x (C.⊲-tr p q) hw

  IntR : ∀ {V} (x : D hz V) (q : V ⊲ W) (w : D hz W) → Rf₁ (IL ac mk u x q w)
  IntR x q w = IntS x q (refl₀ w)

-- Int 走部分和, 输出字面就是部分和
ILpre : ∀ {ac : AccY hz} {mk : Mk} {u : U₁} {V} (d : ℕ → D hz V) (q : V ⊲ W) (w : D hz W) k →
        IL ac mk u (preL d k) q w ≡ preL (λ n → IL ac mk u (d n) q (w ⨾ nw q (preL d n))) k
ILpre d q w zero = refl
ILpre {ac} {mk} {u} d q w (suc k) = cong (λ t → t ⨾ IL ac mk u (d k) q (w ⨾ nw q (preL d k))) (ILpre d q w k)

PreM : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} {q′ : V′ ⊲ W} → (∀ n → d n ⊑₀ d′ n) → ∀ n → preL d n ⊑₀ Pre q′ d′ n
PreM hd zero = z0
PreM hd (suc n) = sq (PreM hd n) (wr (hd n))

PreM′ : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} {q : V ⊲ W} {q′ : V′ ⊲ W} → (∀ n → d n ⊑₀ d′ n) → ∀ n → Pre q d n ⊑₀ Pre q′ d′ n
PreM′ hd zero = z0
PreM′ hd (suc n) = sq (PreM′ hd n) (wl (wr (hd n)))

IntM : ∀ {ac ac′ : AccY hz} {mk mk′ : Mk} {u u′ : U₁} → Mo u u → Mo u′ u′ → Mo u u′ →
     ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → ∀ (q : V ⊲ W) (q′ : V′ ⊲ W) {w w′ : D hz W} → w ⊑₀ w′ →
     IL ac mk u x q w ⊑₁ IL ac′ mk′ u′ x′ q′ w′
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr z0 q q′ hw = R1.n0⊑
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr o1 q q′ {w} {w′} hw = cr w w′ hw
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (sq {x = x} {x′ = x′} hx hy) q q′ {w} {w′} hw =
  R1.⨾⊑ (IntR mu x q w) (IntR mu′ x′ q′ w′) (IntM mu mu′ cr hx q q′ hw) (IntM mu mu′ cr hy q q′ (sq hw (wl (wr hx))))
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (lm {d = d} {d′} hd) q q′ {w} {w′} hw =
  R1.nl⊑ (λ n → IntR mu (d n) q _) (λ n → IntR mu′ (d′ n) q′ _) (λ n → IntM mu mu′ cr (hd n) q q′ (sq hw (PreM′ hd n)))
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (wl {p = p} h) q q′ hw = IntM mu mu′ cr h (C.⊲-tr p q) q′ hw
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (wr {p = p} h) q q′ hw = IntM mu mu′ cr h q (C.⊲-tr p q′) hw
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (pr {x = x} {x′} {d} {d′} hx hd k) q q′ {w} {w′} hw =
  subst (λ t → (IL ac mk u x q w ⨾ t) ⊑₁ IL ac′ mk′ u′ (x′ ⨾ nl d′) q′ w′) (sym (ILpre d q (w ⨾ nw q x) k))
    (R1.pre⊑ (IntR mu x q w) (IntR mu′ x′ q′ w′) (λ n → IntR mu (d n) q _) (λ n → IntR mu′ (d′ n) q′ _)
             (IntM mu mu′ cr hx q q′ hw) (λ n → IntM mu mu′ cr (hd n) q q′ (sq (sq hw (wl (wr hx))) (wl (PreM hd n)))) k)
IntM {ac} {ac′} {mk} {mk′} {u} mu mu′ cr (tr₀ h h′) q q′ {w} hw = R1.tr (IntM {ac} {ac} {mk} {mk} {u} {u} mu mu mu h q q (refl₀ w)) (IntM mu mu′ cr h′ q q′ hw)
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (u0l h) q q′ {w} {w′} hw = R1.u0ˡ (IntM mu mu′ cr h q q′ (tr₀ (sq hw (wl z0)) (u1l (refl₀ w′))))
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (u0r h) q q′ {w} {w′} hw = R1.u0ʳ (IntM mu mu′ cr h q q′ (tr₀ (u1r (refl₀ w)) (sq hw (wr z0))))
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (u1l h) q q′ hw = R1.u1ˡ (IntM mu mu′ cr h q q′ hw)
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (u1r h) q q′ hw = R1.u1ʳ (IntM mu mu′ cr h q q′ hw)
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (al {x = x} {y} {z} h) q q′ {w} hw =
  R1.asˡ rX rY rZ (R1.tr (R1.⨾⊑ rX rX rX (R1.⨾⊑ rY rY rY (IntS mu z q (ar′ (sq (refl₀ w) (nwd x y)))))) (IntM mu mu′ cr h q q′ hw))
  where rX = IntR mu x q w ; rY = IntR mu y q (w ⨾ nw q x) ; rZ = IntR mu z q (w ⨾ nw q (x ⨾ y))
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (al′ {x = x} {y} {z} h) q q′ {w} hw =
  R1.asˡ′ rX rY rZ (R1.tr (R1.⨾⊑ rXY rXY rXY (IntS mu z q (al (sq (refl₀ w) (nwd′ x y))))) (IntM mu mu′ cr h q q′ hw))
  where rX = IntR mu x q w ; rY = IntR mu y q (w ⨾ nw q x) ; rZ = IntR mu z q ((w ⨾ nw q x) ⨾ nw q y) ; rXY = R1.⨾⊑ rX rX rX rY
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (ar {x = x} {y} {z} h) q q′ {w′ = w} hw =
  R1.asʳ rX rY rZ (R1.tr (IntM mu mu′ cr h q q′ hw) (R1.⨾⊑ rXY rXY rXY (IntS mu′ z q′ (ar′ (sq (refl₀ w) (nwd x y))))))
  where rX = IntR mu′ x q′ w ; rY = IntR mu′ y q′ (w ⨾ nw q′ x) ; rZ = IntR mu′ z q′ ((w ⨾ nw q′ x) ⨾ nw q′ y) ; rXY = R1.⨾⊑ rX rX rX rY
IntM {ac} {ac′} {mk} {mk′} {u} {u′} mu mu′ cr (ar′ {x = x} {y} {z} h) q q′ {w′ = w} hw =
  R1.asʳ′ rX rY rZ (R1.tr (IntM mu mu′ cr h q q′ hw) (R1.⨾⊑ rX rX rX (R1.⨾⊑ rY rY rY (IntS mu′ z q′ (al (sq (refl₀ w) (nwd′ x y)))))))
  where rX = IntR mu′ x q′ w ; rY = IntR mu′ y q′ (w ⨾ nw q′ x) ; rZ = IntR mu′ z q′ (w ⨾ nw q′ (x ⨾ y))
```
