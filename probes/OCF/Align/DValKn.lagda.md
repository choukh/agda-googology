# 差树上的值关系 (七): 折叠产出的读坐标节点满足判据

> 不含记号. 入口 [DVal](DVal.lagda.md). **定理 `Kn-Rf`**: `CvFoldInst.Kn w Y` (折叠在目标第 1 层上走顶层节点 `ni self (λ _ _ _ → n1)` 得到的树; 分支在坐标 $z$ 上是 `Step (Y₂ ⊕ Run z …)`, 读坐标) 自比, 只要状态 $Y$ 的第 1 层差**一致** (`Good`: 一切目标路径上的差两两 $\sqsubseteq^{\mathsf d}$). 推论 `Pk-Rf`: `mid₁` 的第二段自比.
>
> 证法是 [DValCanon](DValCanon.lagda.md) `Gen` 的第三个实例: 第 0 层输入, **目标第 1 层**, 输出用 $\sqsubseteq^{\mathsf d}$ 比 (不是 `toB` 的 $\preccurlyeq$). 下标是 (路径, 动作, 动作自身的单调证明), 两边下标可以不同 (两个抬升路径给出两个动作 `Ig↾ p …`).
>
> - `Out i j z z′`: 状态一致且两两 $\sqsubseteq^{\mathsf d}$ ⇒ 输出在一切目标路径上 $\sqsubseteq^{\mathsf d}$. 和的结构律直接由 `⊑ᵈ` 的构造子给出; 结合律与极限要输出自比, 由下标自带的单调证明归纳给出 (`rO`).
> - `cv-l`, `cv-r`: 换世界 (`cv`) 只把一致状态的差包上 `nw`, 仍一致.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DValKn where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ss; ⊲-tr; cmpF; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; D̂; n0; n1; _⨾_; nl; ni; nκ; nw; cnt; Ωd)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.DValTree
open import OCF.Align.DValCanon using (pre; module Gen)
open import OCF.Align.DValInst using (rf-Ω)
open import OCF.Align.CvFoldInst using (StepA; Kn; Pk; Y₁)
```

## §1 一致的状态, 动作, 关系

```agda
SRel : ∀ {W W′} → F.St W → F.St W′ → Set
SRel {W} {W′} Y Y′ = ∀ (τ : Tg one W) (τ′ : Tg one W′) → F.yc (F.d Y) τ tt ⊑ᵈ F.yc (F.d Y′) τ′ tt

Good : ∀ {W} → F.St W → Set
Good Y = SRel Y Y

module T1 {W : A} (lW : Lg W) where

  Act₀ : Set
  Act₀ = F.Ig (cnt azero) W

  HSA : Act₀ → Act₀ → Set
  HSA A₀ A₁ = ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → ∀ τ τ′ →
              F.yc (A₀ C.self lW w Y) τ tt ⊑ᵈ F.yc (A₁ C.self lW w′ Y′) τ′ tt

  I : Set
  I = Σ (azero ⊲ W) (λ _ → Σ Act₀ (λ A₀ → HSA A₀ A₀))

  Hy : I → I → Set
  Hy i j = HSA (proj₁ (proj₂ i)) (proj₁ (proj₂ j))

  Rn : I → ∀ {V} → D azero V → V ⊲ W → D azero W → F.St W → F.Df W
  Rn i z q w Y = F.Run (F.accCn azero) z q lW (proj₁ i) (proj₁ (proj₂ i)) w Y

  Out : I → I → ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
  Out i j z z′ = ∀ q q′ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → ∀ τ τ′ →
                 F.yc (Rn i z q w Y) τ tt ⊑ᵈ F.yc (Rn j z′ q′ w′ Y′) τ′ tt
```

## §2 和的结构律

`semi⨾`, `semiNl` 带着两边各自的自比; `rO` 用下标自带的单调证明对树归纳给出自比.

```agda
  module _ {i j : I} where
    semi⨾ : ∀ {V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → Out i i x x → Out j j x′ x′ → Out i j x x′ → Out i j y y′ → Out i j (x ⨾ y) (x′ ⨾ y′)
    semi⨾ rx rx′ hx hy q q′ w w′ Y Y′ g g′ s τ τ′ =
      ⨾⊑ (hx q q′ w w′ Y Y′ g g′ s τ τ′)
         (hy q q′ _ _ _ _ (λ σ σ′ → ⨾⊑ (g σ σ′) (rx q q w w Y Y g g g σ σ′))
                          (λ σ σ′ → ⨾⊑ (g′ σ σ′) (rx′ q′ q′ w′ w′ Y′ Y′ g′ g′ g′ σ σ′))
                          (λ σ σ′ → ⨾⊑ (s σ σ′) (hx q q′ w w′ Y Y′ g g′ s σ σ′)) τ τ′)

    semiNl : ∀ {V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → Out i i (d n) (d n)) → (∀ n → Out j j (d′ n) (d′ n)) →
             (∀ n → Out i j (d n) (d′ n)) → Out i j (nl d) (nl d′)
    semiNl {d = d} {d′} rd rd′ hd q q′ w w′ Y Y′ g g′ s τ τ′ = nl⊑ (λ n → let (a , b , c) = go n in hd n q q′ _ _ _ _ a b c τ τ′)
      where
      P = λ n → F.Rpt (F.accCn azero) d q lW (proj₁ i) (proj₁ (proj₂ i)) w Y n
      P′ = λ n → F.Rpt (F.accCn azero) d′ q′ lW (proj₁ j) (proj₁ (proj₂ j)) w′ Y′ n
      go : ∀ n → Good (proj₂ (P n)) × (Good (proj₂ (P′ n)) × SRel (proj₂ (P n)) (proj₂ (P′ n)))
      go zero = g , (g′ , s)
      go (suc n) = let (a , b , c) = go n in
        (λ σ σ′ → ⨾⊑ (a σ σ′) (rd n q q _ _ _ _ a a a σ σ′)) ,
        ((λ σ σ′ → ⨾⊑ (b σ σ′) (rd′ n q′ q′ _ _ _ _ b b b σ σ′)) ,
         (λ σ σ′ → ⨾⊑ (c σ σ′) (hd n q q′ _ _ _ _ a b c σ σ′)))

    nwL : ∀ {V₀ V V₂} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₂} → Out i j x z → Out i j (nw p x) z
    nwL {p = p} h q = h (⊲-tr p q)

    nwR : ∀ {V₀ V V₁} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₁} → Out i j z x → Out i j z (nw p x)
    nwR {p = p} h q q′ = h q (⊲-tr p q′)

    n1O : Hy i j → ∀ {V₁ V₂} → Out i j (n1 {W = V₁}) (n1 {W = V₂})
    n1O h q q′ w w′ Y Y′ g g′ s τ τ′ = h w w′ Y Y′ g g′ s τ τ′

    inflO : ∀ {V₁ V₂} (z : D azero V₂) → Out i j (n0 {W = V₁}) z
    inflO z q q′ w w′ Y Y′ g g′ s τ τ′ = n0⊑

  rO : ∀ (i : I) {V} (z : D azero V) → Out i i z z
  rO i n0 = inflO n0
  rO i n1 = n1O (proj₂ (proj₂ i))
  rO i (x ⨾ y) = semi⨾ (rO i x) (rO i x) (rO i x) (rO i y)
  rO i (nl d) = semiNl (λ n → rO i (d n)) (λ n → rO i (d n)) (λ n → rO i (d n))
  rO i (ni () u)
  rO i (nκ () u)
  rO i (nw p x) = nwL (nwR (rO i x))

  module _ {i j : I} where
    ⨾O : ∀ {V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → Out i j x x′ → Out i j y y′ → Out i j (x ⨾ y) (x′ ⨾ y′)
    ⨾O {x = x} {x′ = x′} = semi⨾ (rO i x) (rO j x′)

    nlO : ∀ {V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → Out i j (d n) (d′ n)) → Out i j (nl d) (nl d′)
    nlO {d = d} {d′} = semiNl (λ n → rO i (d n)) (λ n → rO j (d′ n))

    trO : ∀ {V V₃} {z z′ : D azero V} {z″ : D azero V₃} → Out i i z z′ → Out i j z′ z″ → Out i j z z″
    trO h h′ q q″ w w″ Y Y″ g g″ s τ τ′ = trˡ (h q q w w Y Y g g g τ τ) (h′ q q″ w w″ Y Y″ g g″ s τ τ′)

    trOʳ : ∀ {V V₁} {z : D azero V₁} {z′ z″ : D azero V} → Out i j z z′ → Out j j z′ z″ → Out i j z z″
    trOʳ h h′ q q″ w w″ Y Y″ g g″ s τ τ′ = trʳ (h q q″ w w″ Y Y″ g g″ s τ τ′) (h′ q″ q″ w″ w″ Y″ Y″ g″ g″ g″ τ′ τ′)
```

## §3 单位, 结合, 极限

```agda
  module _ (i : I) where
    private r = rO i

    ulO : ∀ {V} (x : D azero V) → Out i i (n0 ⨾ x) x × Out i i x (n0 ⨾ x)
    ulO x = (λ q q′ w w′ Y Y′ g g′ s τ τ′ →
               u0ˡ (r x q q′ _ w′ _ Y′ (λ σ σ′ → ⨾⊑ (g σ σ′) n0⊑) g′ (λ σ σ′ → u1ˡ (s σ σ′)) τ τ′)) ,
            (λ q q′ w w′ Y Y′ g g′ s τ τ′ →
               u0ʳ (r x q q′ w _ Y _ g (λ σ σ′ → ⨾⊑ (g′ σ σ′) n0⊑) (λ σ σ′ → u1ʳ (s σ σ′)) τ τ′))

    urO : ∀ {V} (x : D azero V) → Out i i (x ⨾ n0) x × Out i i x (x ⨾ n0)
    urO x = (λ q q′ w w′ Y Y′ g g′ s τ τ′ → u1ˡ (r x q q′ w w′ Y Y′ g g′ s τ τ′)) ,
            (λ q q′ w w′ Y Y′ g g′ s τ τ′ → u1ʳ (r x q q′ w w′ Y Y′ g g′ s τ τ′))

    -- 走 x 之后的状态
    G⊕ : ∀ {V} (x : D azero V) q w Y → Good Y → Good (Y F.⊕ Rn i x q w Y)
    G⊕ x q w Y g σ σ′ = ⨾⊑ (g σ σ′) (r x q q w w Y Y g g g σ σ′)

    S⊕ : ∀ {V} (x : D azero V) q q′ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → SRel (Y F.⊕ Rn i x q w Y) (Y′ F.⊕ Rn i x q′ w′ Y′)
    S⊕ x q q′ w w′ Y Y′ g g′ s σ σ′ = ⨾⊑ (s σ σ′) (r x q q′ w w′ Y Y′ g g′ s σ σ′)

    asO : ∀ {V} (x y z : D azero V) → Out i i ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z)) × Out i i (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
    asO x y z = O₁ , O₂
      where
      O₁ : Out i i ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z))
      O₁ q q′ w w′ Y Y′ g g′ s τ τ′ =
        asʳ (r z q′ q′ _ _ S2′ S2′ gS2′ gS2′ gS2′ τ′ τ′)
            (⨾⊑ (⨾⊑ (r x q q′ w w′ Y Y′ g g′ s τ τ′) (r y q q′ _ _ _ _ gx gx′ sx τ τ′))
                (r z q q′ _ _ S1 S2′ gS1 gS2′ s12 τ τ′))
        where
        Rx = Rn i x q w Y
        Rx′ = Rn i x q′ w′ Y′
        Ry = Rn i y q (w ⨾ nw q x) (Y F.⊕ Rx)
        Ry′ = Rn i y q′ (w′ ⨾ nw q′ x) (Y′ F.⊕ Rx′)
        S1 = Y F.⊕ (Rx F.⨾ᴰ Ry)
        S2′ = (Y′ F.⊕ Rx′) F.⊕ Ry′
        gx = G⊕ x q w Y g
        gx′ = G⊕ x q′ w′ Y′ g′
        sx = S⊕ x q q′ w w′ Y Y′ g g′ s
        gS1 : Good S1
        gS1 σ σ′ = ⨾⊑ (g σ σ′) (⨾⊑ (r x q q w w Y Y g g g σ σ′) (r y q q _ _ _ _ gx gx gx σ σ′))
        gS2′ : Good S2′
        gS2′ = G⊕ y q′ (w′ ⨾ nw q′ x) (Y′ F.⊕ Rx′) gx′
        s12 : SRel S1 S2′
        s12 σ σ′ = asʳ′ (r y q′ q′ _ _ _ _ gx′ gx′ gx′ σ′ σ′) (⨾⊑ (s σ σ′) (⨾⊑ (r x q q′ w w′ Y Y′ g g′ s σ σ′) (r y q q′ _ _ _ _ gx gx′ sx σ σ′)))
      O₂ : Out i i (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
      O₂ q q′ w w′ Y Y′ g g′ s τ τ′ =
        asˡ′ (r z q q _ _ S2 S2 gS2 gS2 gS2 τ τ)
             (⨾⊑ (⨾⊑ (r x q q′ w w′ Y Y′ g g′ s τ τ′) (r y q q′ _ _ _ _ gx gx′ sx τ τ′))
                 (r z q q′ _ _ S2 S1′ gS2 gS1′ s21 τ τ′))
        where
        Rx = Rn i x q w Y
        Rx′ = Rn i x q′ w′ Y′
        Ry = Rn i y q (w ⨾ nw q x) (Y F.⊕ Rx)
        Ry′ = Rn i y q′ (w′ ⨾ nw q′ x) (Y′ F.⊕ Rx′)
        S2 = (Y F.⊕ Rx) F.⊕ Ry
        S1′ = Y′ F.⊕ (Rx′ F.⨾ᴰ Ry′)
        gx = G⊕ x q w Y g
        gx′ = G⊕ x q′ w′ Y′ g′
        sx = S⊕ x q q′ w w′ Y Y′ g g′ s
        gS2 : Good S2
        gS2 = G⊕ y q (w ⨾ nw q x) (Y F.⊕ Rx) gx
        gS1′ : Good S1′
        gS1′ σ σ′ = ⨾⊑ (g′ σ σ′) (⨾⊑ (r x q′ q′ w′ w′ Y′ Y′ g′ g′ g′ σ σ′) (r y q′ q′ _ _ _ _ gx′ gx′ gx′ σ σ′))
        s21 : SRel S2 S1′
        s21 σ σ′ = asˡ (r y q q _ _ _ _ gx gx gx σ σ) (⨾⊑ (s σ σ′) (⨾⊑ (r x q q′ w w′ Y Y′ g g′ s σ σ′) (r y q q′ _ _ _ _ gx gx′ sx σ σ′)))
```

**极限.** 前缀 `pre d k` 走出来的输出字面就是各段输出的 `pre₁` (`O≡`); `Rpt` 的状态与前缀的状态字面不同, 由 `asˡ′`, `asʳ` 逐段对上.

```agda
  module _ (i : I) {V} (d : ℕ → D azero V) (q : V ⊲ W) (w₁ : D azero W) (Z : F.St W) where
    oL : (τ : Tg one W) → ℕ → D one (F.wm τ)
    oL τ n = F.yc (Rn i (d n) q (w₁ ⨾ nw q (pre d n)) (Z F.⊕ Rn i (pre d n) q w₁ Z)) τ tt

    O≡ : ∀ τ k → F.yc (Rn i (pre d k) q w₁ Z) τ tt ≡ pre₁ (oL τ) k
    O≡ τ zero = refl
    O≡ τ (suc k) = cong (λ t → t ⨾ oL τ k) (O≡ τ k)

  pre₁⊑ : ∀ {V V′} {a : ℕ → D one V} {b : ℕ → D one V′} → (∀ n → a n ⊑ᵈ b n) → ∀ k → pre₁ a k ⊑ᵈ pre₁ b k
  pre₁⊑ h zero = n0⊑
  pre₁⊑ h (suc k) = ⨾⊑ (pre₁⊑ h k) (h k)

  module _ {i j : I} where
    preO : ∀ {V₁ V₂} (x : D azero V₁) (x′ : D azero V₂) (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) →
           Out i j x x′ → (∀ n → Out i j (d n) (d′ n)) → ∀ k → Out i j (x ⨾ pre d k) (x′ ⨾ nl d′)
    preO x x′ d d′ hx hd k q q′ w w′ Y Y′ g g′ s τ τ′ =
      subst (λ t → (F.yc (Rn i x q w Y) τ tt ⨾ t) ⊑ᵈ _) (sym (O≡ i d q w₁ Z τ k))
        (pre⊑ (hx q q′ w w′ Y Y′ g g′ s τ τ′) (λ n → let (a , b , c) = go n in hd n q q′ _ _ _ _ a b c τ τ′) k)
      where
      w₁ = w ⨾ nw q x
      Z = Y F.⊕ Rn i x q w Y
      Z′ = Y′ F.⊕ Rn j x′ q′ w′ Y′
      gZ = λ σ σ′ → ⨾⊑ (g σ σ′) (rO i x q q w w Y Y g g g σ σ′)
      gZ′ = λ σ σ′ → ⨾⊑ (g′ σ σ′) (rO j x′ q′ q′ w′ w′ Y′ Y′ g′ g′ g′ σ σ′)
      sZ = λ σ σ′ → ⨾⊑ (s σ σ′) (hx q q′ w w′ Y Y′ g g′ s σ σ′)
      P′ = λ n → F.Rpt (F.accCn azero) d′ q′ lW (proj₁ j) (proj₁ (proj₂ j)) (w′ ⨾ nw q′ x′) Z′ n
      ZL = λ n → Z F.⊕ Rn i (pre d n) q w₁ Z
      go : ∀ n → Good (ZL n) × (Good (proj₂ (P′ n)) × SRel (ZL n) (proj₂ (P′ n)))
      go zero = (λ σ σ′ → ⨾⊑ (gZ σ σ′) n0⊑) , (gZ′ , (λ σ σ′ → u1ˡ (sZ σ σ′)))
      go (suc n) = let (a , b , c) = go n in
        (λ σ σ′ → ⨾⊑ (gZ σ σ′) (rO i (pre d (suc n)) q q w₁ w₁ Z Z gZ gZ gZ σ σ′)) ,
        ((λ σ σ′ → ⨾⊑ (b σ σ′) (rO j (d′ n) q′ q′ _ _ _ _ b b b σ σ′)) ,
         (λ σ σ′ → asˡ′ (rO i (d n) q q _ _ _ _ a a a σ σ) (⨾⊑ (c σ σ′) (hd n q q′ _ _ _ _ a b c σ σ′))))

    limO : Hy i i → ∀ {V₁ V₂} (x : D azero V₁) (d : ℕ → D azero V₁) (z : D azero V₂) →
           (∀ k → Out i j (x ⨾ pre d k) z) → Out i j (x ⨾ nl d) z
    limO _ x d z hk q q′ w w′ Y Y′ g g′ s τ τ′ =
      lim⊑ (λ n → let (a , b) = go n in rO i (d n) q q _ _ _ _ a a a τ τ)
           (λ k → trˡ (⨾⊑ (rO i x q q w w Y Y g g g τ τ)
                          (subst (λ t → pre₁ (oR τ) k ⊑ᵈ t) (sym (O≡ i d q w₁ Z τ k))
                                 (pre₁⊑ (λ n → let (a , b , c) = go n in rO i (d n) q q _ _ _ _ a b c τ τ) k)))
                      (hk k q q′ w w′ Y Y′ g g′ s τ τ′))
      where
      w₁ = w ⨾ nw q x
      Z = Y F.⊕ Rn i x q w Y
      gZ = λ σ σ′ → ⨾⊑ (g σ σ′) (rO i x q q w w Y Y g g g σ σ′)
      P = λ n → F.Rpt (F.accCn azero) d q lW (proj₁ i) (proj₁ (proj₂ i)) w₁ Z n
      ZL = λ n → Z F.⊕ Rn i (pre d n) q w₁ Z
      oR : (τ : Tg one W) → ℕ → D one (F.wm τ)
      oR τ n = F.yc (Rn i (d n) q (proj₁ (P n)) (proj₂ (P n))) τ tt
      go : ∀ n → Good (proj₂ (P n)) × (Good (ZL n) × SRel (proj₂ (P n)) (ZL n))
      go zero = gZ , ((λ σ σ′ → ⨾⊑ (gZ σ σ′) n0⊑) , (λ σ σ′ → u1ʳ (gZ σ σ′)))
      go (suc n) = let (a , b , c) = go n in
        (λ σ σ′ → ⨾⊑ (a σ σ′) (rO i (d n) q q _ _ _ _ a a a σ σ′)) ,
        ((λ σ σ′ → ⨾⊑ (gZ σ σ′) (rO i (pre d (suc n)) q q w₁ w₁ Z Z gZ gZ gZ σ σ′)) ,
         (λ σ σ′ → asʳ (rO i (d n) q q _ _ _ _ b b b σ′ σ′) (⨾⊑ (c σ σ′) (rO i (d n) q q _ _ _ _ a b c σ σ′))))
```

## §4 套 `Gen`: 目标第 1 层的值同余

```agda
  private
    module GT = Gen Hy Out (λ {i} {j} h → n1O {i} {j} h) (λ {i} {j} z → inflO {i} {j} z)
      (λ {i} {j} → ⨾O {i} {j}) (λ {i} {j} → nlO {i} {j}) (λ {i} {j} → nwL {i} {j}) (λ {i} {j} → nwR {i} {j})
      (λ {i} {j} → trO {i} {j}) (λ {i} {j} → trOʳ {i} {j})
      (λ {i} _ → ulO i) (λ {i} _ → urO i) (λ {i} _ → asO i)
      (λ {i} {j} → preO {i} {j}) (λ {i} {j} h → limO {i} {j} h)

  cong1 : ∀ (i j : I) → Hy i j → ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → V0 z ≤ V0 z′ → Out i j z z′
  cong1 i j h = GT.Two.cong0 {i} {j} (proj₂ (proj₂ i)) (proj₂ (proj₂ j)) h
```

## §5 `Step` 与换世界

```agda
Ω⊑ : ∀ {V V′} → Ωd one {L = one} {W = V} C.self tt ⊑ᵈ Ωd one {L = one} {W = V′} C.self tt
Ω⊑ = ⨾⊑ n1⊑ (⨾⊑ n0⊑ (ni⊑ (λ q q′ l z z′ le → n1⊑) (λ q q′ l z z′ le → n1⊑) (λ q q′ l z z′ le → n1⊑)))

module _ {W : A} where
  -- Step 在目标第 1 层: 状态的差逐对 ⊑ᵈ 则输出逐对 ⊑ᵈ
  stepS : ∀ {W′} (Y : F.St W) (Y′ : F.St W′) → SRel Y Y′ → ∀ τ τ′ → F.yc (F.Step Y) τ tt ⊑ᵈ F.yc (F.Step Y′) τ′ tt
  stepS Y Y′ s τ τ′ = nl⊑ (λ _ → ⨾⊑ Ω⊑ (s τ τ′))

module _ {W W′ : A} (Y : F.St W) where
  -- cv 的差是旧差 (某条路径上) 包一层 nw
  cv-l : ∀ (q : W ⊲ W′) (lW′ : Lg W′) {V} (X : D one V) → (∀ τ → F.yc (F.d Y) τ tt ⊑ᵈ X) →
         ∀ τ → F.yc (F.d (F.cv q lW′ Y)) τ tt ⊑ᵈ X
  cv-l q lW′ X h (inj₁ τ₁) with cmpF q τ₁ lW′
  ... | inj₁ t⊲W = nwˡ (h (inj₁ t⊲W))
  ... | inj₂ W⊲t = nwˡ (h (inj₂ W⊲t))
  cv-l q lW′ X h (inj₂ τ₂) = h (inj₂ (⊲-tr q τ₂))

  cv-r : ∀ (q : W ⊲ W′) (lW′ : Lg W′) {V} (X : D one V) → (∀ τ → X ⊑ᵈ F.yc (F.d Y) τ tt) →
         ∀ τ → X ⊑ᵈ F.yc (F.d (F.cv q lW′ Y)) τ tt
  cv-r q lW′ X h (inj₁ τ₁) with cmpF q τ₁ lW′
  ... | inj₁ t⊲W = nwʳ (h (inj₁ t⊲W))
  ... | inj₂ W⊲t = nwʳ (h (inj₂ W⊲t))
  cv-r q lW′ X h (inj₂ τ₂) = h (inj₂ (⊲-tr q τ₂))

cvS : ∀ {W W′} (Y : F.St W) (lW′ : Lg W′) (q q′ : W ⊲ W′) → Good Y → SRel (F.cv q lW′ Y) (F.cv q′ lW′ Y)
cvS Y lW′ q q′ g τ τ′ = cv-l Y q lW′ _ (λ σ → cv-r Y q′ lW′ _ (λ σ′ → g σ σ′) τ′) τ
```

## §6 `Kn` 自比

`Kn w Y` 字面归约到 `ni (ss self) u`, $u$ 在路径 $p$、坐标 $z$ 上是 `Step (cv p Y ⊕ Run z …)` 在目标第 1 层的差. 链的动作 `Ig↾ p (Ai accTop …)` 在 `C.self` 处字面就是 `Step` (`hA` 由检查器归约). 判据 `Mono` 的三件: 换世界的状态一致 (`cvS`), 走 $z$ 与 $z'$ 的输出 $\sqsubseteq^{\mathsf d}$ (`cong1`), `Step` 保持 (`stepS`).

```agda
brK : ∀ {W} → D one W → ∀ {W′} → W ⊲ W′ → Lg W′ → D azero W′ → D one W′
brK (ni (ss C.self) u) p l z = u p l z
brK _ p l z = n0

module _ (w : D̂ one) (Y : F.St one) (g : Good Y) where
  module _ {W′} (l : Lg W′) where
    open T1 l
    kW₀ : azero ⊲ one
    kW₀ = ⊲-tr C.self (C.suc C.self)

    Aq : one ⊲ W′ → Act₀
    Aq p = F.Ig↾ (⊲-tr C.self p) (F.Ai F.accTop C.self (λ _ _ _ → n1) (C.suc C.self) kW₀ tt StepA w)

    hA : ∀ p p′ → HSA (Aq p) (Aq p′)
    hA p p′ w₁ w₁′ Z Z′ gZ gZ′ s τ τ′ = stepS Z Z′ s τ τ′

    ix : one ⊲ W′ → I
    ix p = ⊲-tr kW₀ (⊲-tr C.self p) , (Aq p , hA p p)

    mK : ∀ (p p′ : one ⊲ W′) (z z′ : D azero W′) → V0 z ≤ V0 z′ → brK (Kn w Y) p l z ⊑ᵈ brK (Kn w Y) p′ l z′
    mK p p′ z z′ le = stepS (Y₂ p F.⊕ Rn (ix p) z C.self n0 (Y₂ p)) (Y₂ p′ F.⊕ Rn (ix p′) z′ C.self n0 (Y₂ p′)) srel
                            (inj₁ (⊲-tr C.self p)) (inj₁ (⊲-tr C.self p′))
      where
      Y₂ : one ⊲ W′ → F.St W′
      Y₂ p = F.cv (⊲-tr C.self p) l Y
      srel : SRel (Y₂ p F.⊕ Rn (ix p) z C.self n0 (Y₂ p)) (Y₂ p′ F.⊕ Rn (ix p′) z′ C.self n0 (Y₂ p′))
      srel = λ σ σ′ → ⨾⊑ (cvS Y l _ _ g σ σ′)
        (cong1 (ix p) (ix p′) (hA p p′) z z′ le C.self C.self n0 n0 (Y₂ p) (Y₂ p′)
               (cvS Y l _ _ g) (cvS Y l _ _ g) (cvS Y l _ _ g) σ σ′)

  Kn-Rf : Rf (Kn w Y)
  Kn-Rf = ni⊑ (λ p p′ l z z′ le → mK l p p′ z z′ le) (λ p p′ l z z′ le → mK l p p′ z z′ le) (λ p p′ l z z′ le → mK l p p′ z z′ le)

-- mid₁ 的第二段
gY₀ : Good F.Y₀
gY₀ τ τ′ = n0⊑

g⊕S : ∀ {W} (Y : F.St W) → Good Y → Good (Y F.⊕ F.Step Y)
g⊕S Y g τ τ′ = ⨾⊑ (g τ τ′) (stepS Y Y g τ τ′)

gY₁ : Good (Y₁ F.⊕ F.zeroD)
gY₁ τ τ′ = ⨾⊑ (cvS (F.Y₀ F.⊕ F.Step F.Y₀) tt C.self C.self (g⊕S F.Y₀ gY₀) τ τ′) n0⊑

Pk-Rf : Rf Pk
Pk-Rf = ⨾⊑ n0⊑ (Kn-Rf _ (Y₁ F.⊕ F.zeroD) gY₁)
```
