# 桥 (三): 界比对面的高 (编译的否定)

> 不含记号. 结论写在 [GuardBridge](GuardBridge.lagda.md). 这里杀的是写明的桥 (`≲ᶻ` 到 [OCF.Free.Tree](../Free/Tree.lagda.md)), **不说 `T₀`, `T₀′` 没有 `Goodᴺ`**.
>
> - `T₀-too-high`: $\psi_0(\Omega_{\Omega+1})$ 这棵树 (`T₀ (suc c₁)`) 与对面 (`ψ̄ (Ω̇ 1)`) 之间没有 `≲ᶻ`. 第 2 项, 分支 3, $1, 0, 2, 0$, 第一支, $2, 0$: 这里界 2, 对面界 1. 判断: 原因在 `owk` 那一行, [GuardBridgeTree](GuardBridgeTree.lagda.md) 把它改掉.
> - `floor-gap`: 改掉之后的差别. **这是表的路线本身: 帧的分支值是极限 $L$ 时, 表要字面的 $L<\ell$ (`pr L = L`), 地板是 `fk L`, 界是 $L+1$; 对面的地板是 `flo L = fb L`, 界是 $L$.** 这里对 $L=\omega$ 写成定理: 两个界不满足 $\sqsubseteq$. 这样的闭包确实在树里: [GuardBridgeAccept](GuardBridgeAccept.lagda.md) 的 `lim-u`, `lim-f`, `lim-q` (有限测试, 路径 `p₁`: $\psi_0(\Omega_{\Omega+1})$ 的第 1 项, 分支 $\omega+1$, 这里界 $\omega+1$, 对面与塔都是 $\omega$). 把这条路径写成 `T₀′ (suc c₁) ≲ᶻ 对面 → ⊥` 的定理, 合一耗尽了 6 GB 堆, 所以这一半只是测试.
> - `no-join`: 这个差距改不掉的理由. 如果界只到 $L$, 分支 $\eta$ 上只有 $L\sqsubseteq\eta$, 而表要 $L,\eta$ 的字面公共上界. **有 $L\sqsubseteq\eta$ 没有字面公共上界** (偶数列与奇数列的极限). 这是壁垒的同一个现象: 两个下标有字面公共上界就可比 (`<ᴵ-dec`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardBridgeNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Free.Floor using (fk; fb; _⊔_; Top; bound; Bd; evF; FM; ubd; inl; inr; ink; inb)
import OCF.Free.Tree as FT
open import OCF.Align.GuardTightLv using (module Lv; Dom₀)
open Lv Dom₀ using (suc; s≈)
import OCF.Align.GuardTightLv as GL
open import OCF.Align.GuardTightTree using (T₀)
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁; tc₁)
open import OCF.Align.GuardBridgeZ
open import OCF.Align.GuardBridgeTree using (T₀′)
```

## §1 沿路径走

```agda
data Dir : Set where
  L : ℕ → Dir
  F : Dir
  B : (η : Ordᴵ) → suc zero ⊑ᴵ η → Dir

stepZ : Dir → Z → Z → Z × Z
stepZ (L n) (Z.lim f) (Z.lim g) = f n , g n
stepZ F (Z.ĉᴸ c _ _ o₀ _) (Z.ĉᴸ c′ _ _ o₀′ _) = o₀ , o₀′
stepZ (B η e) (Z.ĉᴸ (suc zero) _ _ _ o) (Z.ĉᴸ (suc zero) _ _ _ o′) = o η e , o′ η e
stepZ _ _ _ = Z.zero , Z.zero

walkP : List Dir → Z → Z → Z × Z
walkP [] x y = x , y
walkP (d ∷ p) x y with stepZ d x y
... | x′ , y′ = walkP p x′ y′

step≲ : ∀ d {x y} → x ≲ᶻ y → proj₁ (stepZ d x y) ≲ᶻ proj₂ (stepZ d x y)
step≲ (L n) zl = zl
step≲ (L n) (sl r) = zl
step≲ (L n) (ll h) = h n
step≲ (L n) (ĉl _ _ _ _ _) = zl
step≲ F zl = zl
step≲ F (sl r) = zl
step≲ F (ll h) = zl
step≲ F (ĉl _ _ _ dp _) = dp
step≲ (B η e) zl = zl
step≲ (B η e) (sl r) = zl
step≲ (B η e) (ll h) = zl
step≲ (B η e) (ĉl {c = zero} _ _ _ _ _) = zl
step≲ (B η e) (ĉl {c = lim _ _} _ _ _ _ _) = zl
step≲ (B η e) (ĉl {c = suc (suc _)} _ _ _ _ _) = zl
step≲ (B η e) (ĉl {c = suc (lim _ _)} _ _ _ _ _) = zl
step≲ (B η e) (ĉl {c = suc zero} {c′ = zero} _ _ _ _ _) = zl
step≲ (B η e) (ĉl {c = suc zero} {c′ = lim _ _} _ _ _ _ _) = zl
step≲ (B η e) (ĉl {c = suc zero} {c′ = suc (suc _)} _ _ _ _ _) = zl
step≲ (B η e) (ĉl {c = suc zero} {c′ = suc (lim _ _)} _ _ _ _ _) = zl
step≲ (B η e) (ĉl {c = suc zero} {c′ = suc zero} _ _ _ _ dO) = dO η e e

walk≲ : ∀ p {x y} → x ≲ᶻ y → proj₁ (walkP p x y) ≲ᶻ proj₂ (walkP p x y)
walk≲ [] r = r
walk≲ (d ∷ p) {x} {y} r with stepZ d x y | step≲ d r
... | x′ , y′ | r′ = walk≲ p r′

bdOf : Z → Ordᴵ
bdOf (Z.ĉᴸ c _ _ _ _) = c
bdOf _ = zero

bd≲ : ∀ {x y} → x ≲ᶻ y → bdOf x ⊑ᴵ bdOf y
bd≲ zl = z⊑
bd≲ (sl _) = z⊑
bd≲ (ll _) = z⊑
bd≲ (ĉl ec _ _ _ _) = ec
```

## §2 `T₀`

```agda
Lc : GL.Lv.LG Dom₀
Lc = suc c₁

freeTree : Z
freeTree = toZ (FT.ψ̄ (FT.Ω̇ (suc zero)) {zero} {suc zero} (tt , (λ q → q)) zero)

tgt₁ tgt₁′ : Z
tgt₁ = T₀ Lc (wf₁ , s≈ sf₁) tc₁
tgt₁′ = T₀′ Lc (wf₁ , s≈ sf₁) tc₁

iterᴵ : Ordᴵ → ℕ → Ordᴵ
iterᴵ c zero = c
iterᴵ c (suc k) = suc (iterᴵ c k)

up⊑ : ∀ {c} k → c ⊑ᴵ iterᴵ c k
up⊑ {c} zero = ⊑ᴵ-refl
up⊑ (suc k) = ⊑ᴵ-trans (up⊑ k) (Sim→⊑ᴵ (λ q → suc q))

two⋢one : suc (suc zero) ⊑ᴵ suc zero → ⊥
two⋢one (s⊑ () zero)
two⋢one (s⊑ e (suc ()))

p₀ : List Dir
p₀ = L 2 ∷ B (iterᴵ (suc zero) 2) (up⊑ 2) ∷ L 1 ∷ L 0 ∷ L 2 ∷ L 0 ∷ F ∷ L 2 ∷ L 0 ∷ []

T₀-too-high : tgt₁ ≲ᶻ freeTree → ⊥
T₀-too-high r = two⋢one (bd≲ (walk≲ p₀ r))
```

## §3 `T′`: 分支 $\omega+1$

```agda
data Fin : Ordᴵ → Set where
  fz : Fin zero
  fs : ∀ {a} → Fin a → Fin (suc a)

fin< : ∀ {a r} → Fin a → r <ᴵ a → Fin r
fin< (fs h) zero = h
fin< (fs h) (suc q) = fin< h q

finNat : ∀ n → Fin (natᴵ n)
finNat zero = fz
finNat (suc n) = fs (finNat n)

¬ω≅fin : ∀ {r} → ωᴵ ≅ᴵ r → Fin r → ⊥
¬ω≅fin (l≅ _) ()

¬sω⊑ω : suc ωᴵ ⊑ᴵ ωᴵ → ⊥
¬sω⊑ω (s⊑ e (lim n q)) = ¬ω≅fin e (fin< (finNat n) q)

ℓ₀ : Ordᴵ
ℓ₀ = suc (suc ωᴵ)

z<ℓ₀ : zero <ᴵ ℓ₀
z<ℓ₀ = suc (suc (lim 1 zero))

-- 表的路线的地板: fk ω. 对面的地板: fb ω = flo ω.
Bₜ : Top zero ℓ₀ (fk ωᴵ ⊔ fk zero)
Bₜ = bound (fk ωᴵ ⊔ fk zero) ((λ q → suc q) , (λ { zero → z<ℓ₀ ; (suc ()) })) z<ℓ₀

B_f : Top zero ℓ₀ (fb ωᴵ ⊔ fk zero)
B_f = bound (fb ωᴵ ⊔ fk zero) ((λ q → suc (suc q)) , (λ { zero → z<ℓ₀ ; (suc ()) })) z<ℓ₀

floor-gap : Bd Bₜ ⊑ᴵ Bd B_f → ⊥
floor-gap e = ¬sω⊑ω (⊑ᴵ-trans low (⊑ᴵ-trans e high))
  where
  low : suc ωᴵ ⊑ᴵ Bd Bₜ
  low = ⊑ᴵ-trans (Sim→⊑ᴵ (proj₁ (evF Bₜ))) (FM Bₜ)
  high : Bd B_f ⊑ᴵ ωᴵ
  high = ubd B_f (via z≅ (lim 1 zero)) (λ { (inl inb) → ⊑ᴵ-refl ; (inr ink) → inj₂ z≅ })

oneω : suc zero ⊑ᴵ suc ωᴵ
oneω = ⊑ᴵ-trans (s⊑ z≅ (lim 1 zero)) (Sim→⊑ᴵ (λ q → suc q))

p₁ : List Dir
p₁ = L 1 ∷ B (suc ωᴵ) oneω ∷ L 1 ∷ L 0 ∷ L 2 ∷ F ∷ L 2 ∷ L 1 ∷ F ∷ L 2 ∷ L 2 ∷ L 0 ∷ L 2 ∷ L 0 ∷ L 2 ∷ []

```

## §4 为什么改不掉: 没有字面的公共上界

$L=\lim_n 2n$, $\eta=\lim_n (2n+1)$. $L\sqsubseteq\eta$, 但没有 $X$ 使 $L<X$ 且 $\eta<X$: 否则 `<ᴵ-dec` 比较这两个, 三种答案都假.

```agda
dbl : ℕ → ℕ
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

Evn Odd : ℕ → Ordᴵ
Evn n = natᴵ (dbl n)
Odd n = natᴵ (suc (dbl n))

Lₑ ηₒ : Ordᴵ
Lₑ = lim Evn (λ n → Sim→⊑ᴵ (λ q → suc (suc q)))
ηₒ = lim Odd (λ n → Sim→⊑ᴵ (λ q → suc (suc q)))

L⊑η : Lₑ ⊑ᴵ ηₒ
L⊑η = l⊑ (λ n → ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (Sim→⊑ᴵ (λ q → lim n q)))

¬lim≅fin : ∀ {f s r} → lim f s ≅ᴵ r → Fin r → ⊥
¬lim≅fin (l≅ _) ()

no-join : Σ Ordᴵ (λ X → (Lₑ <ᴵ X) × (ηₒ <ᴵ X)) → ⊥
no-join (X , p , q) with <ᴵ-dec p q
... | injᵃ (via e (lim n r)) = ¬lim≅fin e (fin< (finNat (suc (dbl n))) r)
... | injᵇ (via e (lim n r)) = ¬lim≅fin e (fin< (finNat (dbl n)) r)
... | injᶜ (l≅ h) with h 0
...   | ()
```
