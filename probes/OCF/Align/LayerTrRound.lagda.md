# 差树按层互译 (五): 条件定理 — 分支对规范坐标不变时往返保值

> 不含记号. 入口 [LayerTr](LayerTr.lagda.md).
>
> - `S-mono`: $b\preccurlyeq b'\Rightarrow b+x\preccurlyeq b'+x$, 对一切第 1 层差树 (含 `ni`, `nκ`).
> - `Cv x`: $x$ 里每个 `ni` 的分支 $u$ 在坐标 $w$ 与它的规范形 `cw w = n0 ⨾ nw self (dif (toA w))` 上给出值相等的段 (对一切底 $b$), 遗传.
> - **`round-Cv`**: 没有 `nκ` 且满足 `Cv` 的差树, 差 → 树 → 差 → 树, 值不变.
> - `Ω-Cv`: 前提可满足 ($\Omega_1$ 的差树).
> - `xᶜ-not-Cv`: [LayerTrNeg](LayerTrNeg.lagda.md) 的反例不满足 `Cv`. 所以 `Cv` 不能去掉.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LayerTrRound where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; z⊲; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.BrwMidZero using (dif; toA)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne
import OCF.Align.LayerTrNeg as N
open import OCF.Align.LayerTrOmega using (Ωx; okΩ)
```

## §1 和对底单调

```agda
≈-refl : ∀ {W} (a : B₁ W) → a ≈ a
≈-refl a = ≼-refl a , ≼-refl a

≈-sym : ∀ {W W′} {a : B₁ W} {b : B₁ W′} → a ≈ b → b ≈ a
≈-sym (p , q) = q , p

I-mono  : ∀ {W₀ W} (e e′ : D azero W → B₁ W → B₁ W) → (∀ w {b b′} → b ≼ b′ → e w b ≼ e′ w b′) →
          (z : D azero W₀) (q : W₀ ⊲ W) → ∀ w {b b′} → b ≼ b′ → I e z q w b ≼ I e′ z q w b′
Ip-mono : ∀ {W₀ W} (e e′ : D azero W → B₁ W → B₁ W) → (∀ w {b b′} → b ≼ b′ → e w b ≼ e′ w b′) →
          (d : ℕ → D azero W₀) (q : W₀ ⊲ W) → ∀ w {b b′} → b ≼ b′ → ∀ n → Ip e d q w b n ≼ Ip e′ d q w b′ n
I-mono e e′ h n0 q w r = r
I-mono e e′ h n1 q w r = h w r
I-mono e e′ h (x ⨾ y) q w r = I-mono e e′ h y q _ (I-mono e e′ h x q w r)
I-mono e e′ h (nl d) q w r = l≼ (λ n → ≼l n (Ip-mono e e′ h d q w r n))
I-mono e e′ h (ni () u) q w r
I-mono e e′ h (nκ () u) q w r
I-mono e e′ h (nw p x) q w r = I-mono e e′ h x (⊲-tr p q) w r
Ip-mono e e′ h d q w r zero = r
Ip-mono e e′ h d q w r (suc n) = I-mono e e′ h (d n) q _ (Ip-mono e e′ h d q w r n)

S-mono  : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (x : D one W₀) {b b′ : B₁ W} → b ≼ b′ → S q l b x ≼ S q l b′ x
Sp-mono : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (d : ℕ → D one W₀) {b b′ : B₁ W} → b ≼ b′ → ∀ n → Sp q l b d n ≼ Sp q l b′ d n
K-mono  : ∀ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) b {a} (p : a ⊲ b) (aW : W₀ ⊲ a) (lb : Lg b) {x x′ : B₁ a} →
          x ≼ x′ → K u b p aW lb x ≼ K u b p aW lb x′
KR-mono : ∀ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) →
          ∀ {a n} (p : a ⊲ f n) (aW : W₀ ⊲ a) {x x′ : B₁ a} → x ≼ x′ → ∀ m → KR u f st wl p aW x m ≼ KR u f st wl p aW x′ m
S-mono q l n0 r = r
S-mono q l n1 r = s≼s r
S-mono q l (x ⨾ y) r = S-mono q l y (S-mono q l x r)
S-mono q l (nl d) r = l≼ (λ n → ≼l n (Sp-mono q l d r n))
S-mono q l (ni (ss C.self) u) r =
  i≼ (λ p l′ y ly → ≼i p l′ y ly
    (I-mono _ _ (λ w r′ → S-mono C.self l′ (u (⊲-tr q p) l′ w) r′) (dif y (z⊲ y) ly) C.self n0 (w≼ (≼w r))))
S-mono q l (nκ zz u) r = κ≼ (λ p lc → ≼κ p lc (S-mono C.self lc (u (⊲-tr q p) lc) (K-mono u _ p q lc r)))
S-mono q l (nw p x) r = S-mono (⊲-tr p q) l x r
Sp-mono q l d r zero = r
Sp-mono q l d r (suc n) = S-mono q l (d n) (Sp-mono q l d r n)
K-mono u b C.self aW lb r = r
K-mono u (asuc c) (C.suc p) aW lb r = w≼ (≼w (S-mono C.self lb (u (⊲-tr aW p) lb) (K-mono u c p aW lb r)))
K-mono u (alim f) (C.lim n p) aW (st , wl) r = l≼ (λ m → ≼l m (w≼ (≼w (KR-mono u f st wl p aW r m))))
KR-mono u f st wl p aW r zero = K-mono u (f _) p aW (wl _) r
KR-mono u f st wl {n = n} p aW r (suc m) =
  K-mono u (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP′ f st p m)) (wl (suc (m + n))) (KR-mono u f st wl p aW r m)
  where open import OCF.Align.SumOneTree using () renaming (tailP to tailP′)

S-cong : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (x : D one W₀) {b b′ : B₁ W} → b ≈ b′ → S q l b x ≈ S q l b′ x
S-cong q l x (r , r′) = S-mono q l x r , S-mono q l x r′
```

## §2 条件

```agda
cw : ∀ {W} → D azero W → D azero W
cw w = n0 ⨾ nw C.self (dif (proj₁ (toA w)) (z⊲ (proj₁ (toA w))) (proj₂ (toA w)))

Cv : ∀ {W} → D one W → Set
Cv n0 = ⊤
Cv n1 = ⊤
Cv (x ⨾ y) = Cv x × Cv y
Cv (nl d) = ∀ n → Cv (d n)
Cv (ni (ss C.self) u) = ∀ {W′} p l w → Cv (u {W′} p l w) × (∀ b → S C.self l b (u p l (cw w)) ≈ S C.self l b (u p l w))
Cv (nκ zz u) = ⊤
Cv (nw p x) = Cv x

⊲-idˡ : ∀ {a b} (p : a ⊲ b) → ⊲-tr C.self p ≡ p
⊲-idˡ C.self = refl
⊲-idˡ (C.suc p) = cong C.suc (⊲-idˡ p)
⊲-idˡ (C.lim n p) = cong (C.lim n) (⊲-idˡ p)
```

## §3 往返

`RT`: 从任意一条到底 $B$ 的路径 $P$ 接着走 $x$, 读回的差加在任意 $B'$ 上, 等于先加 $P$ 的差再加 $x$. 归纳只沿 $x$; `S-fstᵃ` 是累积的, 所以 $x ⨾ y$ 不要路径的结合律.

```agda
bi-≈ : ∀ {W} {f g : ∀ {W′} → W ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′} →
       (∀ {W′} p l y ly → f {W′} p l y ly ≈ g p l y ly) → bi f ≈ bi g
bi-≈ h = i≼ (λ p l y ly → ≼i p l y ly (proj₁ (h p l y ly))) , i≼ (λ p l y ly → ≼i p l y ly (proj₂ (h p l y ly)))

RT  : ∀ {W₀ W W′} (x : D one W₀) (o : Ok no x) (cv : Cv x) (s : W₀ ⊲ W) (l : Lg W) (B : B₁ W) (lB : LgB no B)
      {a : B₁ W′} (P : a ⊲⟨ no ⟩ B) (B′ : B₁ W) →
      S C.self l B′ (dif₁ (S s l B x) (S-fstᵃ no s l B x o P) (Lg-S no s l B x o lB)) ≈ S s l (S C.self l B′ (dif₁ B P lB)) x
RTp : ∀ {W₀ W} (d : ℕ → D one W₀) (o : ∀ n → Ok no (d n)) (cv : ∀ n → Cv (d n)) (s : W₀ ⊲ W) (l : Lg W) (B : B₁ W) (lB : LgB no B)
      (X : B₁ W) → ∀ k →
      Sp C.self l X (λ m → dif₁ (Sp s l B d (suc (m + 0))) (S-fst no s l (Sp s l B d (m + 0)) (d (m + 0)) (o (m + 0)))
                                 (Lg-Sp no s l B d o lB (suc (m + 0)))) k
      ≈ Sp s l X d k
RT n0 o cv s l B lB P B′ = ≈-refl _
RT n1 o cv s l B lB P B′ = ≈-refl _
RT (x ⨾ y) (o , o′) (cv , cv′) s l B lB P B′ =
  ≈-trans (RT y o′ cv′ s l (S s l B x) (Lg-S no s l B x o lB) (S-fstᵃ no s l B x o P) B′)
          (S-cong s l y (RT x o cv s l B lB P B′))
RT (nl d) o cv s l B lB P B′ =
  l≼ (λ n → ≼l n (proj₁ (RTp d o cv s l B lB _ n))) , l≼ (λ n → ≼l n (proj₂ (RTp d o cv s l B lB _ n)))
RT (ni (ss C.self) u) o cv s l B lB P B′ = bi-≈ (λ p l′ y ly →
  I-mono _ _ (λ w r → ≼-trans (S-mono C.self l′ _ r) (proj₁ (step p l′ w _))) (dif y (z⊲ y) ly) C.self n0 (≼-refl _) ,
  I-mono _ _ (λ w r → ≼-trans (S-mono C.self l′ _ r) (proj₂ (step p l′ w _))) (dif y (z⊲ y) ly) C.self n0 (≼-refl _))
  where
  -- 一格: 读回的段加在 b 上, 等于原来的段加在 b 上
  step : ∀ {W′} (p : _ ⊲ W′) (l′ : Lg W′) (w : D azero W′) (b : B₁ W′) →
         S C.self l′ b (dif₁ (S C.self l′ (I (λ w′ b′ → S C.self l′ b′ (u (⊲-tr s (⊲-tr C.self p)) l′ w′))
                                               (dif (proj₁ (toA w)) (z⊲ _) (proj₂ (toA w))) C.self n0 (bw (⊲-tr C.self p) B))
                                       (u (⊲-tr s (⊲-tr C.self p)) l′ (cw w)))
                              (S-fst no C.self l′ _ (u (⊲-tr s (⊲-tr C.self p)) l′ (cw w)) (o (⊲-tr s (⊲-tr C.self p)) l′ (cw w)))
                              (Lg-S no C.self l′ _ (u (⊲-tr s (⊲-tr C.self p)) l′ (cw w)) (o _ l′ (cw w))
                                    (Lg-I _ (λ w′ b′ → S-fst no C.self l′ b′ (u (⊲-tr s (⊲-tr C.self p)) l′ w′) (o _ l′ w′))
                                            (λ w′ b′ lb′ → Lg-S no C.self l′ b′ (u (⊲-tr s (⊲-tr C.self p)) l′ w′) (o _ l′ w′) lb′)
                                            (dif (proj₁ (toA w)) (z⊲ _) (proj₂ (toA w))) C.self n0 (bw (⊲-tr C.self p) B) lB)))
         ≈ S C.self l′ b (u (⊲-tr s p) l′ w)
  step {W′} p l′ w b =
    ≈-trans (RT (u (⊲-tr s (⊲-tr C.self p)) l′ (cw w)) (o _ l′ (cw w)) (proj₁ (cv _ l′ (cw w))) C.self l′ _ _ self b)
    (≈-trans (proj₂ (cv (⊲-tr s (⊲-tr C.self p)) l′ w) b)
             (subst (λ r → S C.self l′ b (u (⊲-tr s r) l′ w) ≈ S C.self l′ b (u (⊲-tr s p) l′ w)) (Relation.Binary.PropositionalEquality.sym (⊲-idˡ p)) (≈-refl _)))
RT (nκ zz u) (() , o) cv s l B lB P B′
RT (nw p x) o cv s l B lB P B′ = RT x o cv (⊲-tr p s) l B lB P B′
RTp d o cv s l B lB X zero = ≈-refl _
RTp d o cv s l B lB X (suc k) =
  ≈-trans (S-cong C.self l _ (RTp d o cv s l B lB X k))
  (≈-trans (RT (d (k + 0)) (o (k + 0)) (cv (k + 0)) s l (Sp s l B d (k + 0)) (Lg-Sp no s l B d o lB (k + 0)) self (Sp s l X d k))
           (subst (λ j → S s l (Sp s l X d k) (d j) ≈ S s l (Sp s l X d k) (d k)) (Relation.Binary.PropositionalEquality.sym (+-identityʳ k)) (≈-refl _)))
```

## §4 结论

```agda
round-Cv : ∀ {W} (l : Lg W) (x : D one W) (o : Ok no x) → Cv x → toB l (difT l x o) ≈ toB l x
round-Cv l x o cv = RT x o cv C.self l bz tt self bz

-- 前提可满足: Ω₁ 的差树
Ω-Cv : Cv Ωx
Ω-Cv = tt , (tt , λ p l w → tt , (λ b → ≈-refl _))

Ω-round≈ : toB tt (difT tt Ωx okΩ) ≈ toB tt Ωx
Ω-round≈ = round-Cv tt Ωx okΩ Ω-Cv

-- 反例不满足条件
xᶜ-not-Cv : ¬ Cv N.xᶜ
xᶜ-not-Cv cv = N.no-round (proj₂ (round-Cv tt N.xᶜ N.okᶜ cv))
```
