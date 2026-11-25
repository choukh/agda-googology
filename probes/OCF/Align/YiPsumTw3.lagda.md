# YiPsumTw3：`tw 3` 的根，各支用逐项的折叠

**判决 (编译定理，无前提)：闭项 `T₃ᵗ : R` 合法 (`T₃ᵗ-legal`)。链点取累加归一的坐标 `κ v = 1 + cum v`，与 `YiRawFoldTw3.T₃ᶜ` 是同一条根链；第 `κ v` 支的折叠是
`closedᵗ (read0 (κ v))`，里面没有部分和。`κ v` 的读回在域 `Domᵗ` 里：证书一致 (`κ-coh`)，每一步路径在极限处只取第 0 支 (`κ-zc`)。**
没有的：根上不改行的版本 (链点 `1 + v`，像 `YiRawFoldTw3.T₃ᵐ`) 在逐项的折叠下没有做，它另要折叠输出的证书一致与 `Zp`；值定理没有。部分和仍在根的坐标里 (`cum`)，这一条与 `T₃ᶜ` 相同。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPsumTw3 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; up)
open import OCF.Align.YiIrrIf
  using (R; one; _+ʳ_; iterate; read0; read0-cp; read0-dn; read0-legal)
open import OCF.Align.YiIrrFoldBase using (add-legal; add-cp; add-dn)
open import OCF.Align.YiLvNegCompare using (branch₃)
open import OCF.Align.YiLvNegRestrict using (Coh)
open import OCF.Align.YiLvNegCum using (cum; weak; cum-legal)
  renaming (psum to psum⁰; psum-legal to psum⁰-legal)
open import OCF.Align.YiRawIf using (base; branch-is-top)
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiRawFoldUp using (Zp)
open import OCF.Align.YiRawFoldTw3
  using (rplain; pair-read0; read0-cohP; κ; κ-lgl; κ-coh; κ-guard; κ-step; κ-restrict)
open import OCF.Align.YiPsumBase
open import OCF.Align.YiPsumFold
open import OCF.Align.YiPsumZp
open import OCF.Align.YiPsumInst using (module C; Domᵗ; dm-gen; closedᵗ; closedᵗ-legal)
```

## 1 累加归一的坐标的读回在 `ZpL` 里

`ZC a l`：`a` 的每个极限处，证书里这一步的路径读回以后是 `Zp` 的。加法的证书把加数的路径原样搬过去 (`zp-add-cp`)，
`cum` 的证书在极限处是 `x ⊲ x + suc y` (`weak`)，沿加数的第 0 支走。

```agda
ZC : ∀ a → Lgl zero a → Set
ZC G.zero l = ⊤
ZC (G.suc a) l = ZC a l
ZC (G.lim f) l =
  (∀ n → Zp (read0-cp (f (suc n)) (proj₁ l n))) × (∀ n → ZC (f n) (proj₂ l n))
ZC (G.lc () c t g) l
ZC (G.em () T) l
ZC G.top l = ⊤

zc→zpL : ∀ a l → ZC a l → ZpL (read0 a) (read0-legal a l)
zc→zpL G.zero l h = tt
zc→zpL (G.suc a) l h = zc→zpL a l h
zc→zpL (G.lim f) (st , lf) (z , zs) = z , (λ n → zc→zpL (f n) (lf n) (zs n))
zc→zpL G.top l h = tt

zp-add-cp : ∀ x {a} b (p : Cp zero a b) → Zp (read0-cp b p) →
  Zp (read0-cp (x +ʳ b) (add-cp x p))
zp-add-dn : ∀ x {a} b (p : Dn zero a b) → Zp (read0-dn b p) →
  Zp (read0-dn (x +ʳ b) (add-dn x b p))
zp-add-cp x b (inj₁ refl) z = tt
zp-add-cp x b (inj₂ p) z = zp-add-dn x b p z
zp-add-dn x (G.suc b) p z = zp-add-cp x b p z
zp-add-dn x (G.lim f) (zero , p) z = zp-add-cp x (f zero) p z
zp-add-dn x (G.lim f) (suc n , p) ()
zp-add-dn x (G.lc () c t g) p z
zp-add-dn x (G.em () T) p z
zp-add-dn x G.top () z

add-zc : ∀ x y lx ly → ZC x lx → ZC y ly → ZC (x +ʳ y) (add-legal x y lx ly)
add-zc x G.zero lx ly hx hy = hx
add-zc x (G.suc y) lx ly hx hy = add-zc x y lx ly hx hy
add-zc x (G.lim f) lx (st , lf) hx (z , zs) =
  (λ n → zp-add-cp x (f (suc n)) (st n) (z n)) ,
  (λ n → add-zc x (f n) lx (lf n) hx (zs n))
add-zc x G.top lx ly hx hy = hx

zp-weak : ∀ x y → Zp (read0-cp (x +ʳ y) (weak x y))
zp-weak x G.zero = tt
zp-weak x (G.suc y) = zp-weak x y
zp-weak x (G.lim f) = zp-weak x (f zero)
zp-weak x G.top = tt

psum-zc : ∀ (g : ℕ → R) (lg : ∀ n → Lgl zero (g n)) → (∀ n → ZC (g n) (lg n)) →
  ∀ n → ZC (psum⁰ g n) (psum⁰-legal g lg n)
psum-zc g lg h zero = h zero
psum-zc g lg h (suc n) =
  add-zc (psum⁰ g n) (G.suc (g (suc n))) (psum⁰-legal g lg n) (lg (suc n))
    (psum-zc g lg h n) (h (suc n))

cum-zc : ∀ a → ZC (cum a) (cum-legal a)
cum-zc G.zero = tt
cum-zc (G.suc a) = cum-zc a
cum-zc (G.lim f) =
  (λ n → zp-weak (psum⁰ (λ k → cum (f k)) n) (G.suc (cum (f (suc n))))) ,
  psum-zc (λ k → cum (f k)) (λ k → cum-legal (f k)) (λ k → cum-zc (f k))
cum-zc G.top = tt

κ-zc : ∀ v → ZC (κ v) (κ-lgl v)
κ-zc v = add-zc one (cum v) tt (cum-legal v) tt (cum-zc v)

-- 一般地: 证书一致并且 ZC 的坐标, 读回在域里.
read0-dom : ∀ a (l : Lgl zero a) → ZC a l → Coh a l → Domᵗ (read0 a) (rplain a) (read0-legal a l)
read0-dom a l z ch = zc→zpL a l z , read0-cohP a l ch

κ-dom : ∀ v → Domᵗ (read0 (κ v)) (rplain (κ v)) (read0-legal (κ v) (κ-lgl v))
κ-dom v = read0-dom (κ v) (κ-lgl v) (κ-zc v) (κ-coh v)
```

## 2 闭项

观察 `yᵗ v` 是第 `κ v` 支的逐项折叠，下一个累计是 `v + yᵗ v`。相邻两项的第一位置由 `belowᵗ` 给出 (对一切路径成立)，再把限制下来的
(`Plain`, `Legal`) 换成 `κ v` 自己的 (`pair-read0`, `κ-restrict`)；`low` 的限制还是 `low`。

```agda
yᵗ : R → R
yᵗ v = closedᵗ (read0 (κ v)) (rplain (κ v)) (read0-legal (κ v) (κ-lgl v)) (κ-dom v)

yᵗ-legal : ∀ v → Lgl zero (yᵗ v)
yᵗ-legal v = closedᵗ-legal (read0 (κ v)) (rplain (κ v)) (read0-legal (κ v) (κ-lgl v)) (κ-dom v)

dmκ : ∀ v → C.Dm (read0 (κ v)) (rplain (κ v)) (read0-legal (κ v) (κ-lgl v))
dmκ v = dm-gen (read0 (κ v)) (rplain (κ v)) (read0-legal (κ v) (κ-lgl v)) (κ-dom v)

yᵗ-step : ∀ v a → Cp zero (yᵗ v) (yᵗ (v +ʳ a))
yᵗ-step v a =
  C.recoh (λ z D x → C.Ψᵗ zero (read0 (κ v)) (proj₁ z) (proj₂ z) D x G.top tt tt)
    (trans (pair-read0 (κ (v +ʳ a)) (κ-step v a) (κ-lgl (v +ʳ a)))
      (cong (λ z → rplain (κ v) , read0-legal (κ v) z) (κ-restrict v a)))
    (C.restrictD (read0 (κ (v +ʳ a))) (read0-cp (κ (v +ʳ a)) (κ-step v a))
      (rplain (κ (v +ʳ a))) (read0-legal (κ (v +ʳ a)) (κ-lgl (v +ʳ a))) (dmκ (v +ʳ a)))
    (dmκ v)
    (restrict-low (read0 (κ (v +ʳ a))) (read0-cp (κ (v +ʳ a)) (κ-step v a))
      (rplain (κ (v +ʳ a))))
    (C.belowᵗ zero (read0 (κ (v +ʳ a))) (read0-cp (κ (v +ʳ a)) (κ-step v a))
      (rplain (κ (v +ʳ a))) (read0-legal (κ (v +ʳ a)) (κ-lgl (v +ʳ a))) (dmκ (v +ʳ a)) low)

nextᵗ : R → R
nextᵗ v = v +ʳ yᵗ v

accumᵗ : ℕ → R
accumᵗ = iterate nextᵗ G.zero

T₃ᵗ : R
T₃ᵗ = G.lim (λ n → yᵗ (accumᵗ n))

T₃ᵗ-legal : Lgl zero T₃ᵗ
T₃ᵗ-legal = (λ n → yᵗ-step (accumᵗ n) (yᵗ (accumᵗ n))) , (λ n → yᵗ-legal (accumᵗ n))
```

行，都是 `refl`：起点的坐标是下界 1；第 `n` 项折的是 `tw 3` 在坐标 `κ (accumᵗ n)` 上的分支 (的原像 `top`)；累计加上它。

```agda
T₃ᵗ-start : κ (accumᵗ 0) ≡ one
T₃ᵗ-start = refl

T₃ᵗ-feedback : ∀ n → accumᵗ (suc n) ≡ accumᵗ n +ʳ yᵗ (accumᵗ n)
T₃ᵗ-feedback n = refl

T₃ᵗ-branch : ∀ n → branch₃ (κ (accumᵗ n)) (κ-guard (accumᵗ n)) ≡
  up (read0 (κ (accumᵗ n))) G.top tt
T₃ᵗ-branch n = branch-is-top (κ (accumᵗ n)) (κ-guard (accumᵗ n))
```
