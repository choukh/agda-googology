# `nκ` 的值语义 (四): 折叠单调, 跨世界, 两档

> 不含记号. 入口 [KVal](KVal.lagda.md). [DValSound](DValSound.lagda.md) 的 `snd` 推广到:
>
> - **两边在不同世界里折叠.** 一边 (`Sd`) 是世界 $W$, 合法性, 输入层路径 `ll`, 动作. 动作的前提 `HA⁺` 对两边的一切抬升、一切到第 0 层的路径陈述 (`nκ` 的格在更高的世界里用同一个动作).
> - **上下文** `Cx m`: 两边状态路径一致, 状态值可比; `hi` 档另加回灌层可比 $\ell=W+z\le W'+z'$ (`Hℓ`). `lo` 档没有这一条.
> - **两档一个证明.** `snd kh` 对一切档; `κ⊑` 那一格交给参数 `kh` (只在 `hi` 档有). `snd-lo = snd tt`; `hi` 档的处理 (`KValKappa.κ-sound`) 只用 `snd-lo`, 所以没有循环, 也不要停机检查认可新造的推导.
>
> 每个构造子一步, 新用到的字段同 `DValSound` 的表; 新的只有: 每一步之后把上下文推进一格 (`next`), 用到状态的 $z$ 在路径 `z⊲ W` 上的读数 (由路径一致换到规范路径).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValSound where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ss; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst; cnt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree
open import OCF.Align.KValSem
import OCF.Align.KValZero as Z
```

## §1 两边, 前提, 上下文

```agda
record Sd : Set where
  constructor sd
  field
    W   : A
    lW  : Lg W
    ll  : one ⊲ W
    act : F.Ig (cnt one) W
open Sd public

vY : (s : Sd) → F.St (W s) → A
vY s Y = vYk (κ₀ (ll s)) Y

Rn : (s : Sd) → ∀ {V} → D one V → V ⊲ W s → D one (W s) → F.St (W s) → F.Df (W s)
Rn s x q w Y = F.Run ac₁ x q (lW s) (ll s) (act s) w Y

Ob : (s : Sd) → A → ∀ {V} → D one V → V ⊲ W s → D one (W s) → F.St (W s) → A
Ob s c x q w Y = sum c (F.yc (Rn s x q w Y) (inj₁ (κ₀ (ll s))) tt)

HA⁺ : Sd → Sd → Set
HA⁺ s s′ = ∀ {V V′} (p : W s ⊲ V) (p′ : W s′ ⊲ V′) (lV : Lg V) (lV′ : Lg V′) w w′ (Y : F.St V) (Y′ : F.St V′)
           (k : azero ⊲ V) (k′ : azero ⊲ V′) → CohY Y → CohY Y′ → vYk k Y ≤ vYk k′ Y′ → ∀ c c′ → c ≤ c′ →
           sum c (F.yc (act s p lV w Y) (inj₁ k) tt) ≤ sum c′ (F.yc (act s′ p′ lV′ w′ Y′) (inj₁ k′) tt)

record Ok (s s′ : Sd) : Set where
  constructor ok
  field
    hx : HA⁺ s s′
    h0 : HA⁺ s s
    h1 : HA⁺ s′ s′
    c0 : CohA (act s)
    c1 : CohA (act s′)
open Ok public

okL : ∀ {s s′} → Ok s s′ → Ok s s
okL o = ok (h0 o) (h0 o) (h0 o) (c0 o) (c0 o)

okR : ∀ {s s′} → Ok s s′ → Ok s′ s′
okR o = ok (h1 o) (h1 o) (h1 o) (c1 o) (c1 o)

-- 抬升一边的世界: 动作换成 Ig↾
lift : (s : Sd) → ∀ {V} → W s ⊲ V → Lg V → Sd
lift s {V} p lV = sd V lV (⊲-tr (ll s) p) (F.Ig↾ p (act s))

ok↾ : ∀ {s s′} → Ok s s′ → ∀ {V V′} (p : W s ⊲ V) (p′ : W s′ ⊲ V′) (lV : Lg V) (lV′ : Lg V′) → Ok (lift s p lV) (lift s′ p′ lV′)
ok↾ o p p′ lV lV′ =
  ok (λ r r′ → hx o (⊲-tr p r) (⊲-tr p′ r′)) (λ r r′ → h0 o (⊲-tr p r) (⊲-tr p r′)) (λ r r′ → h1 o (⊲-tr p′ r) (⊲-tr p′ r′))
     (cohA↾ p (c0 o)) (cohA↾ p′ (c1 o))

Hℓ : Md → ∀ {W W′} → F.St W → F.St W′ → Set
Hℓ lo Y Y′ = ⊤
Hℓ hi {W} {W′} Y Y′ = sum W (F.z Y) ≤ sum W′ (F.z Y′)

hℓ-refl : ∀ m {W} (Y : F.St W) → Hℓ m Y Y
hℓ-refl lo Y = tt
hℓ-refl hi {W} Y = ≤-refl _

-- 状态值定义性相等的几种改写 (档是变量时 Hℓ 不归约, 要分情形)
module _ {W W′ : A} where
  hℓ0ˡ : ∀ m {Y : F.St W} {Y′ : F.St W′} → Hℓ m Y Y′ → Hℓ m (Y F.⊕ F.zeroD) Y′
  hℓ0ˡ lo h = tt
  hℓ0ˡ hi h = h
  hℓ0ʳ : ∀ m {Y : F.St W} {Y′ : F.St W′} → Hℓ m Y Y′ → Hℓ m Y (Y′ F.⊕ F.zeroD)
  hℓ0ʳ lo h = tt
  hℓ0ʳ hi h = h
  hℓAˡ : ∀ m {Y : F.St W} {a b : F.Df W} {Y′ : F.St W′} → Hℓ m ((Y F.⊕ a) F.⊕ b) Y′ → Hℓ m (Y F.⊕ (a F.⨾ᴰ b)) Y′
  hℓAˡ lo h = tt
  hℓAˡ hi h = h
  hℓAʳ : ∀ m {Y′ : F.St W} {Y : F.St W′} {a b : F.Df W′} → Hℓ m Y′ ((Y F.⊕ a) F.⊕ b) → Hℓ m Y′ (Y F.⊕ (a F.⨾ᴰ b))
  hℓAʳ lo h = tt
  hℓAʳ hi h = h

hℓ0r : ∀ m {W} (Y : F.St W) → Hℓ m Y (Y F.⊕ F.zeroD)
hℓ0r lo Y = tt
hℓ0r hi Y = ≤-refl _

hℓAs : ∀ m {W} (Y : F.St W) (a b : F.Df W) → Hℓ m (Y F.⊕ (a F.⨾ᴰ b)) ((Y F.⊕ a) F.⊕ b)
hℓAs lo Y a b = tt
hℓAs hi Y a b = ≤-refl _

hℓAs′ : ∀ m {W} (Y : F.St W) (a b : F.Df W) → Hℓ m ((Y F.⊕ a) F.⊕ b) (Y F.⊕ (a F.⨾ᴰ b))
hℓAs′ lo Y a b = tt
hℓAs′ hi Y a b = ≤-refl _

record Cx (m : Md) (s s′ : Sd) (Y : F.St (W s)) (Y′ : F.St (W s′)) : Set where
  constructor cx
  field
    cL  : CohY Y
    cR  : CohY Y′
    vle : vY s Y ≤ vY s′ Y′
    hl  : Hℓ m Y Y′
open Cx public

cx-refl : ∀ m (s : Sd) (Y : F.St (W s)) → CohY Y → Cx m s s Y Y
cx-refl m s Y cY = cx cY cY (≤-refl _) (hℓ-refl m Y)

OutLe : Md → ∀ {V V′} → D one V → D one V′ → Set
OutLe m {V} {V′} x x′ = ∀ (s s′ : Sd) → Ok s s′ → ∀ (q : V ⊲ W s) (q′ : V′ ⊲ W s′) w w′ Y Y′ → Cx m s s′ Y Y′ →
                        ∀ c c′ → c ≤ c′ → Ob s c x q w Y ≤ Ob s′ c′ x′ q′ w′ Y′
```

## §2 上下文推进一格

```agda
cR₁ : ∀ (s : Sd) → CohA (act s) → ∀ {V} (x : D one V) (q : V ⊲ W s) w Y → CohY Y → CohY (Y F.⊕ Rn s x q w Y)
cR₁ s cA x q w Y cY = coh⊕ cY (coh₁ x q (lW s) (ll s) (act s) w Y cA cY)

hℓ⊕ : ∀ m {s s′ : Sd} {Y Y′} {Δ : F.Df (W s)} {Δ′ : F.Df (W s′)} → Hℓ m Y Y′ → CohD Δ → CohD Δ′ →
      (∀ c c′ → c ≤ c′ → sum c (F.yc Δ (inj₁ (κ₀ (ll s))) tt) ≤ sum c′ (F.yc Δ′ (inj₁ (κ₀ (ll s′))) tt)) →
      Hℓ m (Y F.⊕ Δ) (Y′ F.⊕ Δ′)
hℓ⊕ lo h cD cD′ O = tt
hℓ⊕ hi {s} {s′} h cD cD′ O =
  ≤-trans (cdA cD (inj₁ (z⊲ (W s))) (inj₁ (κ₀ (ll s))) _)
          (≤-trans (O _ _ h) (cdA cD′ (inj₁ (κ₀ (ll s′))) (inj₁ (z⊲ (W s′))) _))

next : ∀ {m s s′} → Ok s s′ → ∀ {V V′} {x : D one V} {x′ : D one V′} {q q′ w w′ Y Y′} →
       (∀ c c′ → c ≤ c′ → Ob s c x q w Y ≤ Ob s′ c′ x′ q′ w′ Y′) → Cx m s s′ Y Y′ →
       Cx m s s′ (Y F.⊕ Rn s x q w Y) (Y′ F.⊕ Rn s′ x′ q′ w′ Y′)
next {m} {s} {s′} o {x = x} {x′} {q} {q′} {w} {w′} {Y} {Y′} O (cx a b v h) =
  cx (cR₁ s (c0 o) x q w Y a) (cR₁ s′ (c1 o) x′ q′ w′ Y′ b) (O _ _ v)
     (hℓ⊕ m {s} {s′} h (coh₁ x q (lW s) (ll s) (act s) w Y (c0 o) a) (coh₁ x′ q′ (lW s′) (ll s′) (act s′) w′ Y′ (c1 o) b) O)

-- 同一边上两次走: 左右都是 s
cohOf : ∀ {m s s′ Y Y′} → Cx m s s′ Y Y′ → CohY Y
cohOf = cL
```

## §3 `κ⊑` 的处理是参数

```agda
KX : ∀ {V V′} → Bk V → Bk V′ → Set
KX {V} {V′} u u′ = ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u p l ⊑[ lo ] u′ p′ l′

KH : Md → Set
KH lo = ⊤
KH hi = ∀ {V V′ zz zz′} {u : Bk V} {u′ : Bk V′} → V′ ≤ V → KMono u → KMono u′ → KX u u′ → OutLe hi (nκ zz u) (nκ zz′ u′)
```

## §4 对每个构造子一步

```agda
snd : ∀ {m V V′} {x : D one V} {x′ : D one V′} → KH m → x ⊑[ m ] x′ → OutLe m x x′
snd kh n0⊑ s s′ o q q′ w w′ Y Y′ k c c′ cb = ≤-trans cb (⊲→≤ (sum-fst c′ _))
snd kh n1⊑ s s′ o q q′ w w′ Y Y′ (cx a b v h) c c′ cb = hx o C.self C.self (lW s) (lW s′) w w′ Y Y′ _ _ a b v c c′ cb
snd kh (⨾⊑ hx′ hy) s s′ o q q′ w w′ Y Y′ k c c′ cb =
  snd kh hy s s′ o q q′ _ _ _ _ (next o Hx k) _ _ (Hx c c′ cb)
  where Hx = snd kh hx′ s s′ o q q′ w w′ Y Y′ k
snd kh (nl⊑ {d = d} {d′} h) s s′ o q q′ w w′ Y Y′ k c c′ cb = l≤ (λ n → ≤l n (proj₁ (go n)))
  where
  P = λ n → F.Rpt ac₁ d q (lW s) (ll s) (act s) w Y n
  P′ = λ n → F.Rpt ac₁ d′ q′ (lW s′) (ll s′) (act s′) w′ Y′ n
  go : ∀ n → (pt c (λ m → F.yc (Rn s (d m) q (proj₁ (P m)) (proj₂ (P m))) (inj₁ (κ₀ (ll s))) tt) n ≤
              pt c′ (λ m → F.yc (Rn s′ (d′ m) q′ (proj₁ (P′ m)) (proj₂ (P′ m))) (inj₁ (κ₀ (ll s′))) tt) n) ×
             Cx _ s s′ (proj₂ (P n)) (proj₂ (P′ n))
  go zero = cb , k
  go (suc n) = let (gb , gk) = go n
                   H = snd kh (h n) s s′ o q q′ _ _ _ _ gk
               in H _ _ gb , next o H gk
snd kh (nwˡ {p = p} h) s s′ o q q′ = snd kh h s s′ o (⊲-tr p q) q′
snd kh (nwʳ {p = p} h) s s′ o q q′ = snd kh h s s′ o q (⊲-tr p q′)
snd kh (ni⊑ {u = u} {u′} mu mu′ cr) s s′ o q q′ w w′ Y Y′ k c c′ cb = rs (F.rkT kW (inj₁ kW) (lW s)) (F.rkT kW′ (inj₁ kW′) (lW s′))
  where
  kW = κ₀ (ll s)
  kW′ = κ₀ (ll s′)
  A² = F.Ai ac₁ (ss C.self) u q kW (ll s) (act s) w
  A²′ = F.Ai ac₁ (ss C.self) u′ q′ kW′ (ll s′) (act s′) w′
  cA² : CohA A²
  cA² p lV z Y₁ cY₁ = coh₁ (u (⊲-tr q p) lV z) C.self lV (⊲-tr (ll s) p) (F.Ig↾ p (act s)) _ Y₁ (cohA↾ p (c0 o)) cY₁
  cA²′ : CohA A²′
  cA²′ p lV z Y₁ cY₁ = coh₁ (u′ (⊲-tr q′ p) lV z) C.self lV (⊲-tr (ll s′) p) (F.Ig↾ p (act s′)) _ Y₁ (cohA↾ p (c1 o)) cY₁
  i j : Z.S₀
  i = Z.s0 (W s) (lW s) kW A² cA²
  j = Z.s0 (W s′) (lW s′) kW′ A²′ cA²′
  sL = lift s C.self (lW s)
  sR = lift s′ C.self (lW s′)
  hxx : Z.HAᶜ i j
  hxx z z′ e e′ Z₁ Z₁′ cZ cZ′ le eb er =
    snd tt (cr q q′ (lW s) (lW s′) z z′ (toV0 z z′ le)) sL sR (ok↾ o C.self C.self (lW s) (lW s′)) C.self C.self _ _ Z₁ Z₁′
        (cx cZ cZ′ er tt) e e′ eb
  h00 : Z.HAᶜ i i
  h00 z z′ e e′ Z₁ Z₁′ cZ cZ′ le eb er =
    snd tt (mu q q (lW s) (lW s) z z′ (toV0 z z′ le)) sL sL (ok↾ (okL o) C.self C.self (lW s) (lW s)) C.self C.self _ _ Z₁ Z₁′
        (cx cZ cZ′ er tt) e e′ eb
  h11 : Z.HAᶜ j j
  h11 z z′ e e′ Z₁ Z₁′ cZ cZ′ le eb er =
    snd tt (mu′ q′ q′ (lW s′) (lW s′) z z′ (toV0 z z′ le)) sR sR (ok↾ (okR o) C.self C.self (lW s′) (lW s′)) C.self C.self _ _ Z₁ Z₁′
        (cx cZ cZ′ er tt) e e′ eb
  rs : ∀ (rk rk′ : F.Rk′ azero azero) →
       sum c (F.RKi ac₁ Z.ac₀ (ss C.self) u q (lW s) (ll s) (act s) w Y (inj₁ kW) tt rk) ≤
       sum c′ (F.RKi ac₁ Z.ac₀ (ss C.self) u′ q′ (lW s′) (ll s′) (act s′) w′ Y′ (inj₁ kW′) tt rk′)
  rs (F.keep ()) rk′
  rs (F.rise _) (F.keep ())
  rs (F.rise _) (F.rise _) = Z.chain {i} {j} h00 h11 hxx Y Y′ (cL k) (cR k) c c′ cb (vle k)
snd kh (κ⊑ v a b cr) = kh v a b cr
snd {m} kh (trˡ h h′) s s″ o q q″ w w″ Y Y″ k c c″ cb =
  ≤-trans (snd kh h s s (okL o) q q w w Y Y (cx-refl m s Y (cL k)) c c (≤-refl c)) (snd kh h′ s s″ o q q″ w w″ Y Y″ k c c″ cb)
snd {m} kh (trʳ h h′) s s″ o q q″ w w″ Y Y″ k c c″ cb =
  ≤-trans (snd kh h s s″ o q q″ w w″ Y Y″ k c c″ cb) (snd kh h′ s″ s″ (okR o) q″ q″ w″ w″ Y″ Y″ (cx-refl m s″ Y″ (cR k)) c″ c″ (≤-refl c″))
snd {m} kh (u0ˡ h) s s′ o q q′ w w′ Y Y′ (cx a b v hl) = snd kh h s s′ o q q′ (w ⨾ nw q n0) w′ (Y F.⊕ F.zeroD) Y′ (cx (coh⊕ a cohZ) b v (hℓ0ˡ m hl))
snd {m} kh (u0ʳ h) s s′ o q q′ w w′ Y Y′ (cx a b v hl) = snd kh h s s′ o q q′ w (w′ ⨾ nw q′ n0) Y (Y′ F.⊕ F.zeroD) (cx a (coh⊕ b cohZ) v (hℓ0ʳ m hl))
snd kh (u1ˡ h) = snd kh h
snd kh (u1ʳ h) = snd kh h
snd {m} kh (asˡ {x = x} {y} {z} hz h) s s′ o q q′ w w′ Y Y′ k c c′ cb =
  ≤-trans (snd kh hz s s (okL o) q q (w ⨾ nw q (x ⨾ y)) ((w ⨾ nw q x) ⨾ nw q y) (Y F.⊕ (Rx F.⨾ᴰ Ry)) ((Y F.⊕ Rx) F.⊕ Ry)
             (cx (coh⊕ (cL k) (coh⨾ cx′ cy′)) (coh⊕ (coh⊕ (cL k) cx′) cy′) (≤-refl _) (hℓAs m Y Rx Ry)) B B (≤-refl B))
          (snd kh h s s′ o q q′ w w′ Y Y′ k c c′ cb)
  where
  Rx = Rn s x q w Y
  Ry = Rn s y q (w ⨾ nw q x) (Y F.⊕ Rx)
  cx′ = coh₁ x q (lW s) (ll s) (act s) w Y (c0 o) (cL k)
  cy′ = coh₁ y q (lW s) (ll s) (act s) _ _ (c0 o) (coh⊕ (cL k) cx′)
  B = sum (sum c (F.yc Rx (inj₁ (κ₀ (ll s))) tt)) (F.yc Ry (inj₁ (κ₀ (ll s))) tt)
snd {m} kh (asˡ′ {x = x} {y} {z} hz h) s s′ o q q′ w w′ Y Y′ k c c′ cb =
  ≤-trans (snd kh hz s s (okL o) q q ((w ⨾ nw q x) ⨾ nw q y) (w ⨾ nw q (x ⨾ y)) ((Y F.⊕ Rx) F.⊕ Ry) (Y F.⊕ (Rx F.⨾ᴰ Ry))
             (cx (coh⊕ (coh⊕ (cL k) cx′) cy′) (coh⊕ (cL k) (coh⨾ cx′ cy′)) (≤-refl _) (hℓAs′ m Y Rx Ry)) B B (≤-refl B))
          (snd kh h s s′ o q q′ w w′ Y Y′ k c c′ cb)
  where
  Rx = Rn s x q w Y
  Ry = Rn s y q (w ⨾ nw q x) (Y F.⊕ Rx)
  cx′ = coh₁ x q (lW s) (ll s) (act s) w Y (c0 o) (cL k)
  cy′ = coh₁ y q (lW s) (ll s) (act s) _ _ (c0 o) (coh⊕ (cL k) cx′)
  B = sum (sum c (F.yc Rx (inj₁ (κ₀ (ll s))) tt)) (F.yc Ry (inj₁ (κ₀ (ll s))) tt)
snd {m} kh (asʳ {x = x} {y} {z} hz h) s s′ o q q′ w w′ Y Y′ k c c′ cb =
  ≤-trans (snd kh h s s′ o q q′ w w′ Y Y′ k c c′ cb)
          (snd kh hz s′ s′ (okR o) q′ q′ (w′ ⨾ nw q′ (x ⨾ y)) ((w′ ⨾ nw q′ x) ⨾ nw q′ y) (Y′ F.⊕ (Rx F.⨾ᴰ Ry)) ((Y′ F.⊕ Rx) F.⊕ Ry)
             (cx (coh⊕ (cR k) (coh⨾ cx′ cy′)) (coh⊕ (coh⊕ (cR k) cx′) cy′) (≤-refl _) (hℓAs m Y′ Rx Ry)) B B (≤-refl B))
  where
  Rx = Rn s′ x q′ w′ Y′
  Ry = Rn s′ y q′ (w′ ⨾ nw q′ x) (Y′ F.⊕ Rx)
  cx′ = coh₁ x q′ (lW s′) (ll s′) (act s′) w′ Y′ (c1 o) (cR k)
  cy′ = coh₁ y q′ (lW s′) (ll s′) (act s′) _ _ (c1 o) (coh⊕ (cR k) cx′)
  B = sum (sum c′ (F.yc Rx (inj₁ (κ₀ (ll s′))) tt)) (F.yc Ry (inj₁ (κ₀ (ll s′))) tt)
snd {m} kh (asʳ′ {x = x} {y} {z} hz h) s s′ o q q′ w w′ Y Y′ k c c′ cb =
  ≤-trans (snd kh h s s′ o q q′ w w′ Y Y′ k c c′ cb)
          (snd kh hz s′ s′ (okR o) q′ q′ ((w′ ⨾ nw q′ x) ⨾ nw q′ y) (w′ ⨾ nw q′ (x ⨾ y)) ((Y′ F.⊕ Rx) F.⊕ Ry) (Y′ F.⊕ (Rx F.⨾ᴰ Ry))
             (cx (coh⊕ (coh⊕ (cR k) cx′) cy′) (coh⊕ (cR k) (coh⨾ cx′ cy′)) (≤-refl _) (hℓAs′ m Y′ Rx Ry)) B B (≤-refl B))
  where
  Rx = Rn s′ x q′ w′ Y′
  Ry = Rn s′ y q′ (w′ ⨾ nw q′ x) (Y′ F.⊕ Rx)
  cx′ = coh₁ x q′ (lW s′) (ll s′) (act s′) w′ Y′ (c1 o) (cR k)
  cy′ = coh₁ y q′ (lW s′) (ll s′) (act s′) _ _ (c1 o) (coh⊕ (cR k) cx′)
  B = sum (sum c′ (F.yc Rx (inj₁ (κ₀ (ll s′))) tt)) (F.yc Ry (inj₁ (κ₀ (ll s′))) tt)
snd {m} kh (pre⊑ {x = x} {x′} {d} {d′} hx′ hd k₀) s s′ o q q′ w w′ Y Y′ k c c′ cb =
  ≤l k₀ (proj₁ (go k₀ (next o Hx k) (Hx c c′ cb)))
  where
  Hx = snd kh hx′ s s′ o q q′ w w′ Y Y′ k
  go : ∀ n {w₁ w₁′ e e′ Z Z′} → Cx m s s′ Z Z′ → e ≤ e′ →
       (Ob s e (pre₁ d n) q w₁ Z ≤
        pt e′ (λ j → F.yc (Rn s′ (d′ j) q′ (proj₁ (F.Rpt ac₁ d′ q′ (lW s′) (ll s′) (act s′) w₁′ Z′ j))
                            (proj₂ (F.Rpt ac₁ d′ q′ (lW s′) (ll s′) (act s′) w₁′ Z′ j))) (inj₁ (κ₀ (ll s′))) tt) n) ×
       Cx m s s′ (Z F.⊕ Rn s (pre₁ d n) q w₁ Z) (proj₂ (F.Rpt ac₁ d′ q′ (lW s′) (ll s′) (act s′) w₁′ Z′ n))
  go zero (cx a b v h) e = e , cx (coh⊕ a cohZ) b v (hℓ0ˡ m h)
  go (suc n) {w₁} {Z = Z} kk e =
    let (gb , gk) = go n kk e
        H = snd kh (hd n) s s′ o q q′ _ _ _ _ gk
        (cx _ nb nv nh) = next o H gk
    in H _ _ gb , cx (coh⊕ (cL kk) (coh₁ (pre₁ d (suc n)) q (lW s) (ll s) (act s) w₁ Z (c0 o) (cL kk))) nb nv (hℓAˡ m nh)
snd {m} kh (lim⊑ {x = x} {d} hr h) s s′ o q q′ w w′ Y Y′ k c c′ cb =
  l≤ (λ n → ≤-trans (proj₁ (go n {w ⨾ nw q x} {w ⨾ nw q x} {sum c (F.yc Rx (inj₁ (κ₀ (ll s))) tt)} {Y F.⊕ Rx} (cR₁ s (c0 o) x q w Y (cL k))))
                    (snd kh (h n) s s′ o q q′ w w′ Y Y′ k c c′ cb))
  where
  Rx = Rn s x q w Y
  go : ∀ n {w₁ w₁′ e Z} → CohY Z →
       (pt e (λ j → F.yc (Rn s (d j) q (proj₁ (F.Rpt ac₁ d q (lW s) (ll s) (act s) w₁ Z j))
                           (proj₂ (F.Rpt ac₁ d q (lW s) (ll s) (act s) w₁ Z j))) (inj₁ (κ₀ (ll s))) tt) n
        ≤ Ob s e (pre₁ d n) q w₁′ Z) ×
       Cx m s s (proj₂ (F.Rpt ac₁ d q (lW s) (ll s) (act s) w₁ Z n)) (Z F.⊕ Rn s (pre₁ d n) q w₁′ Z)
  go zero {Z = Z} cZ = ≤-refl _ , cx cZ (coh⊕ cZ cohZ) (≤-refl _) (hℓ0r m Z)
  go (suc n) {w₁′ = w₁′} {Z = Z} cZ =
    let (gb , gk) = go n cZ
        H = snd kh (hr n) s s (okL o) q q _ _ _ _ gk
        (cx na _ nv nh) = next (okL o) H gk
    in H _ _ gb , cx na (coh⊕ cZ (coh₁ (pre₁ d (suc n)) q (lW s) (ll s) (act s) w₁′ Z (c0 o) cZ)) nv (hℓAʳ m nh)

snd-lo : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑[ lo ] x′ → OutLe lo x x′
snd-lo = snd tt
```
