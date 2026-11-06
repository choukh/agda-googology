# 折叠的输出是否世界稳定 (一): 跨世界的值相等

> 不含记号. 入口 [BrwHW](BrwHW.lagda.md). 第 1 层 View 的条件 `HW` ([BrwViewOne](BrwViewOne.lagda.md)) 在每个 `ni`/`nκ` 节点要 `WSq`: 同一棵树在世界 $W$ 与更大的世界 $W'$ 里求值, 值相等. 对折叠的输出, 这不够用: `ni` 节点的分支在两个**互不可比**的世界里 (左边的 $W''\ge W$, 右边的 $W_2$) 要比. 所以这里用更强、也更好合成的关系:
>
> - `R2 x x′`: 两棵树 (各在自己的世界 $W_0$, $W_0'$ 上) 沿**任意**路径抬到**任意**世界求值, 底值相等则结果值相等. `R2 x x` 推出 `WSq x` (`R2→WSq`).
> - `Sh z z′`: 两个世界上的第 0 层坐标树形状相同 (`nw` 两边都可以插, 极限逐项). 不用 `Funext`.
> - `R2-ni`: `ni` 节点在两边的分支对形状相同的坐标 `R2`, 则节点 `R2`. 证明: 左边在 $(W'',p,y)$ 的分支对右边在世界本身 (路径 `self`) 上同一坐标 $y$ 的分支; 积分沿 `dif y` 两边形状相同 (`Sh-dif`), 逐段比 (`Ic`).
> - `R2-Ω`: $\Omega_1$ 的差树 `Ωd one self tt` 在一切世界之间 `R2` (分支是常数 `n1`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwHWBase where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; Pre; Ωd)
open import OCF.Align.BrwMidZero using (dif)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; Sp; I; Ip)
open import OCF.Align.LayerTrRound using (≈-sym; ≈-refl)
open import OCF.Align.BrwViewOne using (WSq; HW; bl-≈; bw-≈)
```

## §1 形状相同的坐标

```agda
data Sh : ∀ {V V′} → D azero V → D azero V′ → Set where
  sh0 : ∀ {V V′} → Sh (n0 {W = V}) (n0 {W = V′})
  sh1 : ∀ {V V′} → Sh (n1 {W = V}) (n1 {W = V′})
  sh⨾ : ∀ {V V′} {x y : D azero V} {x′ y′ : D azero V′} → Sh x x′ → Sh y y′ → Sh (x ⨾ y) (x′ ⨾ y′)
  shl : ∀ {V V′} {d : ℕ → D azero V} {d′ : ℕ → D azero V′} → (∀ n → Sh (d n) (d′ n)) → Sh (nl d) (nl d′)
  shwL : ∀ {V₀ V V′} {p : V₀ ⊲ V} {x : D azero V₀} {x′ : D azero V′} → Sh x x′ → Sh (nw p x) x′
  shwR : ∀ {V V₀′ V′} {p : V₀′ ⊲ V′} {x : D azero V} {x′ : D azero V₀′} → Sh x x′ → Sh x (nw p x′)

Sh-dif : ∀ {V V′} y {a} (p : a ⊲ y) (ly : Lg y) → Sh (dif {V} y p ly) (dif {V′} y p ly)
Sh-dif y C.self ly = sh0
Sh-dif (asuc c) (C.suc p) ly = sh⨾ (Sh-dif c p ly) sh1
Sh-dif (alim f) (C.lim n p) (st , w) = sh⨾ (Sh-dif (f n) p (w n)) (shl (λ m → Sh-dif (f (suc (m + n))) (st (m + n)) (w (suc (m + n)))))

Sh-Pre : ∀ {Z₀ Z₀′ X X′} (q : Z₀ ⊲ X) (q′ : Z₀′ ⊲ X′) {d : ℕ → D azero Z₀} {d′ : ℕ → D azero Z₀′} →
         (∀ n → Sh (d n) (d′ n)) → ∀ n → Sh (Pre q d n) (Pre q′ d′ n)
Sh-Pre q q′ h zero = sh0
Sh-Pre q q′ h (suc n) = sh⨾ (Sh-Pre q q′ h n) (shwL (shwR (h n)))
```

## §2 `R2`

```agda
R2 : ∀ {W₀ W₀′} → D one W₀ → D one W₀′ → Set
R2 {W₀} {W₀′} x x′ = ∀ {W W′} (q : W₀ ⊲ W) (q′ : W₀′ ⊲ W′) (l : Lg W) (l′ : Lg W′) {b : B₁ W} {b′ : B₁ W′} →
                     b ≈ b′ → S q l b x ≈ S q′ l′ b′ x′

R2→WSq : ∀ {W₀} {x : D one W₀} → R2 x x → WSq x
R2→WSq h q p l l′ e = h q (⊲-tr q p) l l′ e

R2-n0 : ∀ {W₀ W₀′} → R2 (n0 {W = W₀}) (n0 {W = W₀′})
R2-n0 q q′ l l′ e = e

R2-n1 : ∀ {W₀ W₀′} → R2 (n1 {W = W₀}) (n1 {W = W₀′})
R2-n1 q q′ l l′ e = s≼s (proj₁ e) , s≼s (proj₂ e)

R2-⨾ : ∀ {W₀ W₀′} {x y : D one W₀} {x′ y′ : D one W₀′} → R2 x x′ → R2 y y′ → R2 (x ⨾ y) (x′ ⨾ y′)
R2-⨾ hx hy q q′ l l′ e = hy q q′ l l′ (hx q q′ l l′ e)

R2-nl : ∀ {W₀ W₀′} {d : ℕ → D one W₀} {d′ : ℕ → D one W₀′} → (∀ n → R2 (d n) (d′ n)) → R2 (nl d) (nl d′)
R2-nl {d = d} {d′} h q q′ l l′ {b} {b′} e = bl-≈ go
  where
  go : ∀ n → Sp q l b d n ≈ Sp q′ l′ b′ d′ n
  go zero = e
  go (suc n) = h n q q′ l l′ (go n)

R2-nwL : ∀ {V₀ W₀ W₀′} {p : V₀ ⊲ W₀} {x : D one V₀} {x′ : D one W₀′} → R2 x x′ → R2 (nw p x) x′
R2-nwL {p = p} h q q′ l l′ e = h (⊲-tr p q) q′ l l′ e

R2-nwR : ∀ {W₀ V₀′ W₀′} {p : V₀′ ⊲ W₀′} {x : D one W₀} {x′ : D one V₀′} → R2 x x′ → R2 x (nw p x′)
R2-nwR {p = p} h q q′ l l′ e = h q (⊲-tr p q′) l l′ e
```

## §3 积分跨世界, `ni` 节点

```agda
Ic  : ∀ {X X′ Z₀ Z₀′} (e : D azero X → B₁ X → B₁ X) (e′ : D azero X′ → B₁ X′ → B₁ X′) →
      (∀ {w w′} → Sh w w′ → ∀ {c c′} → c ≈ c′ → e w c ≈ e′ w′ c′) →
      ∀ {z : D azero Z₀} {z′ : D azero Z₀′} → Sh z z′ → (q : Z₀ ⊲ X) (q′ : Z₀′ ⊲ X′) →
      ∀ {w w′} → Sh w w′ → ∀ {c c′} → c ≈ c′ → I e z q w c ≈ I e′ z′ q′ w′ c′
Icp : ∀ {X X′ Z₀ Z₀′} (e : D azero X → B₁ X → B₁ X) (e′ : D azero X′ → B₁ X′ → B₁ X′) →
      (∀ {w w′} → Sh w w′ → ∀ {c c′} → c ≈ c′ → e w c ≈ e′ w′ c′) →
      ∀ {d : ℕ → D azero Z₀} {d′ : ℕ → D azero Z₀′} → (∀ n → Sh (d n) (d′ n)) → (q : Z₀ ⊲ X) (q′ : Z₀′ ⊲ X′) →
      ∀ {w w′} → Sh w w′ → ∀ {c c′} → c ≈ c′ → ∀ n → Ip e d q w c n ≈ Ip e′ d′ q′ w′ c′ n
Ic e e′ he sh0 q q′ hw hc = hc
Ic e e′ he sh1 q q′ hw hc = he hw hc
Ic e e′ he (sh⨾ hx hy) q q′ hw hc = Ic e e′ he hy q q′ (sh⨾ hw (shwL (shwR hx))) (Ic e e′ he hx q q′ hw hc)
Ic e e′ he (shl hd) q q′ hw hc = bl-≈ (Icp e e′ he hd q q′ hw hc)
Ic e e′ he (shwL {p = p} h) q q′ hw hc = Ic e e′ he h (⊲-tr p q) q′ hw hc
Ic e e′ he (shwR {p = p} h) q q′ hw hc = Ic e e′ he h q (⊲-tr p q′) hw hc
Icp e e′ he hd q q′ hw hc zero = hc
Icp e e′ he hd q q′ hw hc (suc n) = Ic e e′ he (hd n) q q′ (sh⨾ hw (Sh-Pre q q′ hd n)) (Icp e e′ he hd q q′ hw hc n)

-- 分支对形状相同的坐标 R2
UI : ∀ {W₀ W₀′} → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → D azero W′ → D one W′) → (∀ {W′} → W₀′ ⊲ W′ → Lg W′ → D azero W′ → D one W′) → Set
UI {W₀} {W₀′} u u′ = ∀ {V V′} (r : W₀ ⊲ V) (r′ : W₀′ ⊲ V′) (l : Lg V) (l′ : Lg V′) {w : D azero V} {w′ : D azero V′} →
                      Sh w w′ → R2 (u r l w) (u′ r′ l′ w′)

R2-ni : ∀ {W₀ W₀′} (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → D azero W′ → D one W′) (u′ : ∀ {W′} → W₀′ ⊲ W′ → Lg W′ → D azero W′ → D one W′) →
        UI u u′ → R2 (ni (ss C.self) u) (ni (ss C.self) u′)
R2-ni u u′ h q q′ l l′ {b} {b′} e =
  i≼ (λ {X} p lX y ly → ≼i C.self l′ y ly (proj₁ (br p lX y ly))) ,
  i≼ (λ {X} p lX y ly → ≼i C.self l y ly (proj₂ (br′ p lX y ly)))
  where
  br : ∀ {X} (p : _ ⊲ X) (lX : Lg X) y ly →
       I (λ w b″ → S C.self lX b″ (u (⊲-tr q p) lX w)) (dif {X} y (z⊲ y) ly) C.self n0 (bw p b) ≈
       I (λ w b″ → S C.self l′ b″ (u′ q′ l′ w)) (dif {_} y (z⊲ y) ly) C.self n0 (bw C.self b′)
  br p lX y ly = Ic _ _ (λ hw hc → h (⊲-tr q p) q′ lX l′ hw C.self C.self lX l′ hc) (Sh-dif y (z⊲ y) ly) C.self C.self sh0
                    (≈-trans (bw-≈ p b) (≈-trans e (≈-sym (bw-≈ C.self b′))))
  br′ : ∀ {X} (p : _ ⊲ X) (lX : Lg X) y ly →
        I (λ w b″ → S C.self l b″ (u q l w)) (dif {_} y (z⊲ y) ly) C.self n0 (bw C.self b) ≈
        I (λ w b″ → S C.self lX b″ (u′ (⊲-tr q′ p) lX w)) (dif {X} y (z⊲ y) ly) C.self n0 (bw p b′)
  br′ p lX y ly = Ic _ _ (λ hw hc → h q (⊲-tr q′ p) l lX hw C.self C.self l lX hc) (Sh-dif y (z⊲ y) ly) C.self C.self sh0
                     (≈-trans (bw-≈ C.self b) (≈-trans e (≈-sym (bw-≈ p b′))))
```

## §4 $\Omega_1$

```agda
R2-Ω : ∀ {W₀ W₀′} → R2 (Ωd one {W = W₀} C.self tt) (Ωd one {W = W₀′} C.self tt)
R2-Ω = R2-⨾ R2-n1 (R2-⨾ R2-n0 (R2-ni _ _ (λ r r′ l l′ sh → R2-n1)))

HW-Ω : ∀ {W₀} → HW (Ωd one {W = W₀} C.self tt)
HW-Ω = tt , (tt , ((λ p l w → tt) , R2→WSq (R2-ni _ _ (λ r r′ l l′ sh → R2-n1))))
```
