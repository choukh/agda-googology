# 非选择性的增量搬运 (一): 命题 W′ 的一般形式

> 不含记号. 入口 [UniTr](UniTr.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> [ClosedTermReview](../../Survey/ClosedTermReview.md) §1.2 的命题 W′ 说: 世界操作不选择 $i_0$ 时, 增量进分量 $i$ 的映射 $\mathrm{tr}_{i_0\to i}$ 要对一切 $i$ 定义, 在 $i_0$ 处忠实, 在别处合法 (世界只增). 这一篇把它写成对抽象下标的类型, 并证明它与 "积世界上的非选择性回灌" 等价, 所以 W′ 只是**槽族** (每个分量被升高的那个界的类型) 上的一个性质, 与世界的其余部分无关.
>
> - **`W′.UniTr`** (定义): 下标 $I$, 增量族 $X : I\to\mathrm{Set}$, 合法 `LgX`, 忠实关系 `_≃_`. 字段 `tr i₀ i : X i₀ → X i` (对一切 $i_0, i$), **忠实** `faith : tr i₀ i₀ δ ≃ δ` (合法的 $\delta$), **合法** `legal : LgX (tr i₀ i δ)`. "不判定" 不是字段: 它是对构造的要求, 否定的形式是 "`UniTr` 推出相等的 (弱) 判定".
> - **`Slot`**: 积世界 `sup I (step ∘ G)` (每个分量是 `step`, 被升高的槽是新种类的界, 与 `TelWTy.raiseE`, `HtTowerFFold` 的回灌同形). `NonSel`: 非选择性回灌 `R i₀ δ`, 律 `R-at` (分量 $i_0$ 的槽与 "旧界 ⊞ δ" 互模拟), `R-≤` (一切分量只增), `R-lg` (保合法); **没有** "别处不变" 的律. **`toNS`, `fromNS`**: `UniTr` (忠实 = 互模拟 `≈`) 与 `NonSel` 互推. 字面版 (`SlotL`): 忠实取 "δ 是字面第一位置", 则 `UniTrˡ` 给出回灌的格字面有界 (`toNSˡ`).
> - **`LevSlot`**: 实例. `Lev (Ωtop S)` 的世界在后继坐标 `hs c` 处的分量就是 `step (Lev (up c))`, 槽就是种类 `(hs c , inj₂ tt)` 的界 (`lev-bd`, `refl`). `NonSel` 经 `ext`/`res` 成为 `Lev (Ωtop S)` 整个世界上的回灌 (`liftR-at`, `liftR-≤`, `liftR-lg`); 对头构造子分情形, 不比较高度.
> - **`Off`**: W′ 加上 "别处不变" 的律就推出弱判定 (`off→wdec`, `DiagKLev.upd→wdec` 的同形物). 所以命题 W (选择性) 是 W′ 加 `off`.
> - **前提可满足**: 常值族 (`Const.constU`), 下标相等可判定 (`Inst.decU`, 用 Hedberg, 不用 K; 它满足 `off`: `decU-off`); `Lev` 形的槽族配可判定下标 ℕ (`FinInst.finU`).
> - **`Generic.generic→dec`**: 对**一切**增量族都给出 `UniTr` 的构造, 在族 `X i = (i₀ ≡ i) ⊎ ⊤` 上推出 $i_0$ 与 $i$ 的相等可判定. 所以能成立的构造必须用到槽族本身的结构, 不能对族一般.
> - 共用引理: 互模拟 `≈` 与它的律; `no-1⊞` ($Y\boxplus(1\boxplus Z)$ 不是 $Z$ 的第一位置), `hs≈⊲`, `≈hs⊲` (与 $Z$ 互模拟的树的后继不是 $Z$ 的第一位置).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniTrBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
```

## §1 互模拟与几条第一位置的引理

`a ≈ b`: 同一棵树 (逐构造子, 分支逐点). 不用函数外延时, "忠实" 只能说到这一步.

```agda
module _ {S : KS} where
  infix 4 _≈_
  data _≈_ : HB S → HB S → Set where
    ≈z : hz ≈ hz
    ≈s : ∀ {a b} → a ≈ b → hs a ≈ hs b
    ≈l : ∀ {f g} → (∀ n → f n ≈ g n) → hl f ≈ hl g
    ≈Ω : ∀ {κ g g′} → (∀ c → g c ≈ g′ c) → hΩ κ g ≈ hΩ κ g′

  ≈-rf : ∀ a → a ≈ a
  ≈-rf hz = ≈z
  ≈-rf (hs a) = ≈s (≈-rf a)
  ≈-rf (hl f) = ≈l (λ n → ≈-rf (f n))
  ≈-rf (hΩ κ g) = ≈Ω (λ c → ≈-rf (g c))

  ≈-tr : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
  ≈-tr ≈z ≈z = ≈z
  ≈-tr (≈s p) (≈s q) = ≈s (≈-tr p q)
  ≈-tr (≈l p) (≈l q) = ≈l (λ n → ≈-tr (p n) (q n))
  ≈-tr (≈Ω p) (≈Ω q) = ≈Ω (λ c → ≈-tr (p c) (q c))

  hz⊞ : ∀ a → hz ⊞ a ≈ a
  hz⊞ hz = ≈z
  hz⊞ (hs a) = ≈s (hz⊞ a)
  hz⊞ (hl f) = ≈l (λ n → hz⊞ (f n))
  hz⊞ (hΩ κ g) = ≈Ω (λ c → hz⊞ (g c))

  ⊞-≈ : ∀ a {x y} → x ≈ y → a ⊞ x ≈ a ⊞ y
  ⊞-≈ a ≈z = ≈-rf a
  ⊞-≈ a (≈s p) = ≈s (⊞-≈ a p)
  ⊞-≈ a (≈l p) = ≈l (λ n → ⊞-≈ a (p n))
  ⊞-≈ a (≈Ω p) = ≈Ω (λ c → ⊞-≈ a (p c))

  ≈-hs : ∀ {a} → ¬ (a ≈ hs a)
  ≈-hs (≈s p) = ≈-hs p

module _ {S : KS} where
  up-≈ : ∀ {a b : HB S} → a ≈ b → up a ≈ up b
  up-≈ ≈z = ≈z
  up-≈ (≈s p) = ≈s (up-≈ p)
  up-≈ (≈l p) = ≈l (λ n → up-≈ (p n))
  up-≈ (≈Ω p) = ≈Ω (λ c → up-≈ (p c))
```

**第一位置的反演.** 头是构造子的两棵树之间的第一位置, 拆成 "相等" 或 "落在子项里". 用它们避免对非构造子的项做合一.

```agda
module _ {S : KS} where
  inv-hs : ∀ {a b : HB S} {w} → a ⊲[ w ] hs b → (a ≡ hs b) ⊎ (a ⊲[ w ] b)
  inv-hs hself = inj₁ refl
  inv-hs (hsuc p) = inj₂ p

  hs-inj : ∀ {a b : HB S} → hs a ≡ hs b → a ≡ b
  hs-inj refl = refl

  inv-hl : ∀ {a} {f : ℕ → HB S} {w} → a ⊲[ w ] hl f → (a ≡ hl f) ⊎ Σ ℕ (λ n → a ⊲[ w ] f n)
  inv-hl hself = inj₁ refl
  inv-hl (hlim n p) = inj₂ (n , p)

  inv-hΩ : ∀ {a κ} {g : E S κ → HB S} {w} → a ⊲[ w ] hΩ κ g →
           (a ≡ hΩ κ g) ⊎ Σ (E S κ) (λ c → Bd S κ c w × a ⊲[ w ] g c)
  inv-hΩ hself = inj₁ refl
  inv-hΩ (hLim {c = c} e p) = inj₂ (c , e , p)

  private
    hd0 : HB S → HB S
    hd0 (hl h) = h 0
    hd0 t = t

    hdΩ : HB S → HB S
    hdΩ (hΩ κ h) = h (bot S κ)
    hdΩ t = t
```

**`no-1⊞`**: $Y\boxplus(1\boxplus Z)$ 不是 $Z$ 的第一位置 (任意世界). 对 $Z$ 结构归纳; 这是望远镜版否定 ([UniTrTel](UniTrTel.lagda.md)) 的良基一步.

```agda
  no-1⊞ : ∀ (Y Z : HB S) {w} → ¬ (Y ⊞ (hs hz ⊞ Z) ⊲[ w ] Z)
  no-1⊞ Y hz ()
  no-1⊞ Y (hs Z) {w} p with inv-hs p
  ... | inj₁ e = no-1⊞ Y Z (subst (λ t → Y ⊞ (hs hz ⊞ Z) ⊲[ w ] t) (hs-inj e) hself)
  ... | inj₂ q = no-1⊞ Y Z (⊲ᴮ-tr (hsuc hself) q)
  no-1⊞ Y (hl f) {w} p with inv-hl p
  ... | inj₁ e = no-1⊞ Y (f 0) (subst (λ t → Y ⊞ (hs hz ⊞ f 0) ⊲[ w ] t) (cong hd0 e) hself)
  ... | inj₂ (n , q) = no-1⊞ Y (f n) (⊲ᴮ-tr (hlim n hself) q)
  no-1⊞ Y (hΩ κ g) {w} p with inv-hΩ p
  ... | inj₁ e = no-1⊞ Y (g (bot S κ)) (subst (λ t → Y ⊞ (hs hz ⊞ g (bot S κ)) ⊲[ w ] t) (cong hdΩ e) hself)
  ... | inj₂ (c , e , q) = no-1⊞ Y (g c) (⊲ᴮ-tr (hLim e hself) q)
```

**`hs≈⊲`**: 与 $X$ 互模拟的树的后继不是 $X$ 的第一位置; `≈hs⊲`: 与 $\mathrm{hs}\,X$ 互模拟的树不是 $X$ 的第一位置. 先证一般形 `L≈`: $Z\approx X$, $Z\lhd Y$ 时 $\mathrm{hs}\,Y$ 不是 $X$ 的第一位置; 对 $X$ 结构归纳.

```agda
  L≈ : ∀ {X Z Y : HB S} {w} → Z ≈ X → Z ⊲[ w ] Y → ¬ (hs Y ⊲[ w ] X)
  L≈ ≈z zy ()
  L≈ {w = w} (≈s {a = Z′} e) zy p with inv-hs p
  ... | inj₁ eq = L≈ e hself (subst (λ t → hs Z′ ⊲[ w ] t) (hs-inj eq) zy)
  ... | inj₂ q = L≈ e (⊲ᴮ-tr (hsuc hself) zy) q
  L≈ (≈l e) zy (hlim n q) = L≈ (e n) (⊲ᴮ-tr (hlim n hself) zy) q
  L≈ (≈Ω e) zy (hLim {c = c} b q) = L≈ (e c) (⊲ᴮ-tr (hLim b hself) zy) q

  hs≈⊲ : ∀ {Z X : HB S} {w} → Z ≈ X → ¬ (hs Z ⊲[ w ] X)
  hs≈⊲ e p = L≈ e hself p

  ≈hs⊲ : ∀ {Z X : HB S} {w} → Z ≈ hs X → ¬ (Z ⊲[ w ] X)
  ≈hs⊲ (≈s e) p = hs≈⊲ e p
```

## §2 W′ 的一般形式

```agda
module W′ (I : Set) (X : I → Set) (LgX : ∀ {i} → X i → Set) (_≃_ : ∀ {i} → X i → X i → Set) where
  record UniTr : Set where
    field
      tr    : (i₀ i : I) → X i₀ → X i
      faith : ∀ i₀ δ → LgX δ → tr i₀ i₀ δ ≃ δ
      legal : ∀ i₀ i δ → LgX δ → LgX (tr i₀ i δ)
  open UniTr public
```

**W 是 W′ 加 `off`.** 若还要求 "别处是零" (`off`), 再有一个分开零与某个合法增量的布尔观察量, 就推出弱判定. 证明与 `DiagKLev.look` 同形; 这一条说明判定恰好来自 `off`.

```agda
  module Off (U : UniTr) (zr : ∀ i → X i) (t : ∀ i → X i → Bool) (tz : ∀ i → t i (zr i) ≡ true)
    (δ* : ∀ i → X i) (lδ* : ∀ i → LgX (δ* i)) (tδ : ∀ i x → x ≃ δ* i → t i x ≡ false)
    (off : ∀ i₀ i δ → ¬ (i₀ ≡ i) → tr U i₀ i δ ≡ zr i) where

    private
      t≢ : true ≡ false → ⊥
      t≢ ()

    look : ∀ i₀ i (r : Bool) → t i (tr U i₀ i (δ* i₀)) ≡ r → ¬ (i₀ ≡ i) ⊎ ¬ ¬ (i₀ ≡ i)
    look i₀ i true e = inj₁ (λ q → t≢ (trans (sym e) (subst (λ j → t j (tr U i₀ j (δ* i₀)) ≡ false) q
                                    (tδ i₀ _ (faith U i₀ (δ* i₀) (lδ* i₀))))))
    look i₀ i false e = inj₂ (λ ne → t≢ (trans (sym (tz i)) (trans (cong (t i) (sym (off i₀ i (δ* i₀) ne))) e)))

    off→wdec : ∀ i₀ i → ¬ (i₀ ≡ i) ⊎ ¬ ¬ (i₀ ≡ i)
    off→wdec i₀ i = look i₀ i _ refl
```

**前提可满足.** 常值族上恒等搬运; 下标相等可判定时沿等式搬, 不等处取一个合法的点 (`decU`; 它也满足 `Off` 的 `off` 律, `decU-off`). 后者要 "`i ≡ i` 的证明是 `refl`", 由 Hedberg 定理 (相等可判定 ⇒ UIP) 给出, 不用 K.

```agda
  module Inst (rf : ∀ {i} (x : X i) → x ≃ x) (_≟_ : (i j : I) → Dec (i ≡ j))
              (pt : ∀ i → X i) (lpt : ∀ i → LgX (pt i)) where
    open Decidable⇒UIP _≟_ using (≡-irrelevant)

    goD : ∀ i₀ i → Dec (i₀ ≡ i) → X i₀ → X i
    goD i₀ i (yes e) δ = subst X e δ
    goD i₀ i (no _) δ = pt i

    trD : (i₀ i : I) → X i₀ → X i
    trD i₀ i = goD i₀ i (i₀ ≟ i)

    private
      ⊥-elim′ : ∀ {A : Set} → ⊥ → A
      ⊥-elim′ ()

    faD : ∀ i₀ δ → LgX δ → trD i₀ i₀ δ ≃ δ
    faD i₀ δ l with i₀ ≟ i₀
    ... | yes e = subst (λ q → subst X q δ ≃ δ) (≡-irrelevant refl e) (rf δ)
    ... | no ne = ⊥-elim′ (ne refl)

    lgD : ∀ i₀ i δ → LgX δ → LgX (trD i₀ i δ)
    lgD i₀ i δ l with i₀ ≟ i
    ... | yes refl = l
    ... | no _ = lpt i

    decU : UniTr
    decU = record { tr = trD ; faith = faD ; legal = lgD }

    -- 不等处输出就是那个点: Off 的 off 律在这里成立
    decU-off : ∀ i₀ i δ → ¬ (i₀ ≡ i) → trD i₀ i δ ≡ pt i
    decU-off i₀ i δ ne with i₀ ≟ i
    ... | yes e = ⊥-elim′ (ne e)
    ... | no _ = refl

-- 常值族: 恒等搬运
module Const (I Y : Set) (LgY : Y → Set) (_≃_ : Y → Y → Set) (rf : ∀ y → y ≃ y) where
  open W′ I (λ _ → Y) LgY _≃_
  constU : UniTr
  constU = record { tr = λ _ _ δ → δ ; faith = λ _ δ _ → rf δ ; legal = λ _ _ _ l → l }
```

**对族一般的构造推出判定.** 族 $X\,i=(i_0\equiv i)\uplus\top$: 在 $i_0$ 处忠实地搬 `inj₁ refl`, 看它在 $i$ 处落在哪一边.

```agda
module Generic {I : Set} (i₀ : I) where
  Xid : I → Set
  Xid i = (i₀ ≡ i) ⊎ ⊤

  open W′ I Xid (λ _ → ⊤) _≡_

  module _ (U : UniTr) where
    private
      P : I → Set
      P j = tr U i₀ j (inj₁ refl) ≡ inj₂ tt → ⊥

      base : P i₀
      base e with trans (sym (faith U i₀ (inj₁ refl) tt)) e
      ... | ()

    decide : ∀ i (r : Xid i) → tr U i₀ i (inj₁ refl) ≡ r → (i₀ ≡ i) ⊎ ¬ (i₀ ≡ i)
    decide i (inj₁ q) _ = inj₁ q
    decide i (inj₂ tt) e = inj₂ (λ q → subst P q base e)

    generic→dec : ∀ i → (i₀ ≡ i) ⊎ ¬ (i₀ ≡ i)
    generic→dec i = decide i _ refl
```

## §3 积世界上的非选择性回灌

每个分量是 `step (G i)`: 世界 $(w_i, b_i)$, 被升高的槽是新种类的界 $b_i$, 类型 `HB (G i)`.

```agda
module Slot (I : Set) (G : I → KS) where
  P : KS
  P = sup I (λ i → step (G i))

  X : I → Set
  X i = HB (G i)

  open W′ I X (λ {i} x → LgB {G i} x) (λ {i} x y → _≈_ {G i} x y) public

  record NonSel : Set where
    field
      R    : (i₀ : I) → X i₀ → Wd P → Wd P
      R-at : ∀ i₀ δ w → LgB δ → proj₂ (R i₀ δ w i₀) ≈ proj₂ (w i₀) ⊞ δ
      R-≤  : ∀ i₀ δ w → LgB δ → _≤w_ P w (R i₀ δ w)
      R-lg : ∀ i₀ δ w → LgW P w → LgB δ → LgW P (R i₀ δ w)
  open NonSel public

  -- UniTr ⇒ NonSel: 每个分量的槽接上搬过来的增量
  raiseU : UniTr → (i₀ : I) → X i₀ → Wd P → Wd P
  raiseU U i₀ δ w i = proj₁ (w i) , (proj₂ (w i) ⊞ tr U i₀ i δ)

  toNS : UniTr → NonSel
  toNS U = record
    { R = raiseU U
    ; R-at = λ i₀ δ w l → ⊞-≈ (proj₂ (w i₀)) (faith U i₀ δ l)
    ; R-≤ = λ i₀ δ w l i → ≤w-rf (G i) , ⊞-fst (proj₂ (w i)) (tr U i₀ i δ)
    ; R-lg = λ i₀ δ w lw l i → proj₁ (lw i) , Lg-⊞ (proj₂ (w i)) (tr U i₀ i δ) (proj₂ (lw i)) (legal U i₀ i δ l) }

  -- NonSel ⇒ UniTr: 在槽为 0 的合法世界上回灌, 读出各分量的槽
  module From (u : ∀ i → Wd (G i)) (lu : ∀ i → LgW (G i) (u i)) where
    w₀ : Wd P
    w₀ i = u i , hz

    lw₀ : LgW P w₀
    lw₀ i = lu i , tt

    fromNS : NonSel → UniTr
    fromNS N = record
      { tr = λ i₀ i δ → proj₂ (R N i₀ δ w₀ i)
      ; faith = λ i₀ δ l → ≈-tr (R-at N i₀ δ w₀ l) (hz⊞ δ)
      ; legal = λ i₀ i δ l → proj₂ (R-lg N i₀ δ w₀ lw₀ l i) }
```

**字面版.** 忠实取 "δ 在一切世界里是 `tr i₀ i₀ δ` 的第一位置"; 这时回灌的格 "旧界 ⊞ δ" 字面地在新界之下 (`HtTowerFFold` 的格要的就是这个).

```agda
module SlotL (I : Set) (G : I → KS) where
  open Slot I G using (P; X)
  open W′ I X (λ {i} x → LgB {G i} x) (λ {i} x δ → ∀ {w} → _⊲[_]_ {G i} δ w x)
    renaming (UniTr to UniTrˡ) public

  raiseˡ : UniTrˡ → (i₀ : I) → X i₀ → Wd P → Wd P
  raiseˡ U i₀ δ w i = proj₁ (w i) , (proj₂ (w i) ⊞ tr U i₀ i δ)

  toNSˡ-cell : ∀ U i₀ δ w → LgB δ →
    Bd P (i₀ , inj₂ tt) (proj₂ (w i₀) ⊞ δ) (raiseˡ U i₀ δ w)
  toNSˡ-cell U i₀ δ w l = ⊞-⊲ (proj₂ (w i₀)) (faith U i₀ δ l)

  toNSˡ-≤ : ∀ U i₀ δ w → _≤w_ P w (raiseˡ U i₀ δ w)
  toNSˡ-≤ U i₀ δ w i = ≤w-rf (G i) , ⊞-fst (proj₂ (w i)) (tr U i₀ i δ)

  toNSˡ-lg : ∀ U i₀ δ w → LgW P w → LgB δ → LgW P (raiseˡ U i₀ δ w)
  toNSˡ-lg U i₀ δ w lw l i = proj₁ (lw i) , Lg-⊞ (proj₂ (w i)) (tr U i₀ i δ) (proj₂ (lw i)) (legal U i₀ i δ l)
```

## §4 实例: `Lev (Ωtop S)` 的后继分量

`Wd (Lev (Ωtop S))` 定义地是 $\prod_{c:\mathrm{HB}\,S}\mathrm{Wd}(\mathrm{Lev}(\mathrm{up}\,c))$; 在坐标 `hs c` 处是 `Wd (step (Lev (up c)))`. 种类 `(hs c , inj₂ tt)` 的界就是这个分量的槽.

```agda
module LevSlot (S : KS) where
  G : HB S → KS
  G c = Lev (up c)

  open Slot (HB S) G public

  WΩ : Set
  WΩ = Wd (Lev (Ωtop S))

  lev-bd : ∀ (c : HB S) x (w : WΩ) → Bd (Lev (Ωtop S)) (hs c , inj₂ tt) x w ≡ (x ⊲[ proj₁ (w (hs c)) ] proj₂ (w (hs c)))
  lev-bd c x w = refl

  res : WΩ → Wd P
  res w c = w (hs c)

  ext : Wd P → WΩ → WΩ
  ext v w hz = w hz
  ext v w (hs c) = v c
  ext v w (hl f) = w (hl f)
  ext v w (hΩ κ g) = w (hΩ κ g)

  liftR : NonSel → (c₀ : HB S) → X c₀ → WΩ → WΩ
  liftR N c₀ δ w = ext (R N c₀ δ (res w)) w

  liftR-at : ∀ N c₀ δ w → LgB δ → proj₂ (liftR N c₀ δ w (hs c₀)) ≈ proj₂ (w (hs c₀)) ⊞ δ
  liftR-at N c₀ δ w l = R-at N c₀ δ (res w) l

  liftR-≤ : ∀ N c₀ δ w → LgB δ → _≤w_ (Lev (Ωtop S)) w (liftR N c₀ δ w)
  liftR-≤ N c₀ δ w l hz = ≤w-rf (Lev (up {S} hz))
  liftR-≤ N c₀ δ w l (hs c) = R-≤ N c₀ δ (res w) l c
  liftR-≤ N c₀ δ w l (hl f) = ≤w-rf (Lev (up (hl f)))
  liftR-≤ N c₀ δ w l (hΩ κ g) = ≤w-rf (Lev (up (hΩ κ g)))

  liftR-lg : ∀ N c₀ δ w → LgW (Lev (Ωtop S)) w → LgB δ → LgW (Lev (Ωtop S)) (liftR N c₀ δ w)
  liftR-lg N c₀ δ w lw l hz = lw hz
  liftR-lg N c₀ δ w lw l (hs c) = R-lg N c₀ δ (res w) (λ c′ → lw (hs c′)) l c
  liftR-lg N c₀ δ w lw l (hl f) = lw (hl f)
  liftR-lg N c₀ δ w lw l (hΩ κ g) = lw (hΩ κ g)
```

**可判定下标上的 `Lev` 形实例.** 下标取 ℕ, 第 $n$ 个分量是 `step (Lev (fin n))` ($\mathrm{fin}\,n$ 是第二数类里的 $n$): `UniTr` 存在, 所以 W′ 的三个字段在 `Lev` 形的槽族上可以同时满足; 积世界版的困难只在下标 (`HB S`) 不可判定.

```agda
module FinInst where
  open import Data.Nat.Properties using (_≟_)

  fin : ℕ → HB S₀
  fin zero = hz
  fin (suc n) = hs (fin n)

  open Slot ℕ (λ n → Lev (fin n))

  finU : UniTr
  finU = Inst.decU (λ x → ≈-rf x) _≟_ (λ _ → hz) (λ _ → tt)
```
