# 阶梯 (二): 种类与界的有限测试

> **验收节, 有限测试, 不是证明.** 比较器取自 [UniformLvAccept](UniformLvAccept.lagda.md). 结论写在 [ScafLadder](ScafLadder.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderWalk where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.ScafLadderZPrefix using (Ord₊ˢ; Ordˢ)
open import OCF.Align.Level
open import OCF.Align.ScafLadderZUniform3Base using (Ev; fz; fk; _⊔_; ψ₀ᵗ; bound; Bd)
open import OCF.Align.ScafLadderZUniform4Base using (Fl)
open import OCF.Align.ScafLadderZUniform4Two using (O; oŝ; oΩ; ol)
open import OCF.Align.ScafLadderZUniform4Head using (Ωp)
import OCF.Align.EBO as E
open E using (T; PT; fsn; cof; c0; c1; cω; cΩ; pred; Ωt; natT; sucT; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.ScafLadderZLvWalk
import OCF.Align.Level as Lv
open import Data.Bool using (Bool; true; false)
open import Data.List using (_++_)
open import Data.Product using (_×_)
open import OCF.Align.ScafLadderTree
import OCF.Align.ScafLadderQ as QQ
```

## §0 比较器 (抄自 `UniformLvAccept`)

```agda
data Tag : Set where
  kindBad : Tag        -- 种类不符
  headBad : Tag        -- 都是极限, 但一边是闭包一边不是
  ended   : Tag        -- 走到了非极限节点

strip : T → Ordˢ Lv.zero → T × Ordˢ Lv.zero
strip t (Ord₊ˢ.suc x) = strip (pred t) x
strip t x = t , x

data WR : Set where
  at  : T → Ordˢ Lv.zero → WR
  bad : Tag → List ℕ → WR

pre : ℕ → WR → WR
pre n (bad g p) = bad g (n ∷ p)
pre n r = r

walk⁺ : ℕ → List ℕ → T → Ordˢ Lv.zero → WR
walk⁺ d [] t x = at t x
walk⁺ d (n ∷ r) t x with strip t x
... | t′ , x′ with kid⁺ d n x′
...   | ok y = pre n (walk⁺ d r (fsn t′ n) y)
...   | stop = bad ended (n ∷ [])

-- 闭包节点 `ŝ` 必须对应 (`ĉᴸ` 是嵌在尾巴里的可数值, 不查) ψ_u(a), cof a = cΩ [] (反过来不要求: Ω₁ 节点也有这个共尾度, 而它是普通的 lim).
-- 这比种类严: 两边都是 cω 时也能查出走错了位置
last : PT → T → PT
last x []       = x
last x (y ∷ ys) = last y ys

isClo : T → Bool
isClo [] = false
isClo (x ∷ xs) with last x xs
... | ψᵗ u a with cof a
...   | cΩ [] = true
...   | _ = false

df⁺  : ℕ → ℕ → ℕ → T → Ordˢ Lv.zero → Maybe (Tag × List ℕ)
df⁺s : ℕ → ℕ → ℕ → ℕ → T → Ordˢ Lv.zero → Maybe (Tag × List ℕ)
df⁺ a zero w t x = nothing
df⁺ a (suc d) w t Ord₊ˢ.zero with cof t
... | c0 = nothing
... | _  = just (kindBad , [])
df⁺ a (suc d) w t (Ord₊ˢ.suc x) with cof t
... | c1 = df⁺ a d w (pred t) x
... | _  = just (kindBad , [])
df⁺ a (suc d) w t (Ord₊ˢ.lim f) with cof t
... | cω = df⁺s a w d w t (Ord₊ˢ.lim f)
... | _  = just (kindBad , [])
df⁺ a (suc d) w t x@(Ord₊ˢ.ĉᴸ _ _ _ _ _) with cof t
... | cω = df⁺s a w d w t x
... | _  = just (kindBad , [])
df⁺ a (suc d) w t x with cof t | isClo t
... | cω | true  = df⁺s a w d w t x
... | cω | false = just (headBad , [])
... | _  | _     = just (kindBad , [])
df⁺s a zero d w t x = nothing
df⁺s a (suc n) d w t x with kid⁺ a n x
... | stop = just (ended , n ∷ [])
... | ok y with df⁺ a d w (fsn t n) y
...   | just (g , p) = just (g , n ∷ p)
...   | nothing = df⁺s a n d w t x

dfAt : ℕ → List ℕ → ℕ → ℕ → T → Ordˢ Lv.zero → Maybe (Tag × List ℕ)
dfAt a q d w t x with walk⁺ a q t x
... | at t′ x′ = df⁺ a d w t′ x′
... | bad g p  = just (g , p)

```

### 精确的比较器: 闭包只走第 0 个孩子

闭包的第 0 个孩子不用链点, 所以 `dfᵉ` 没有近似: 树与记号都是精确的. 第 $\ge1$ 个孩子另外在字面的分支值上测 (§4), 或用近似测 (§5).

```agda
dfᵉ  : ℕ → ℕ → T → Ordˢ Lv.zero → Maybe (Tag × List ℕ)
dfᵉs : ℕ → ℕ → ℕ → T → (ℕ → Ordˢ Lv.zero) → Maybe (Tag × List ℕ)
dfᵉ zero w t x = nothing
dfᵉ (suc d) w t Ord₊ˢ.zero with cof t
... | c0 = nothing
... | _  = just (kindBad , [])
dfᵉ (suc d) w t (Ord₊ˢ.suc x) with cof t
... | c1 = dfᵉ d w (pred t) x
... | _  = just (kindBad , [])
dfᵉ (suc d) w t (Ord₊ˢ.lim f) with cof t
... | cω = dfᵉs w d w t f
... | _  = just (kindBad , [])
dfᵉ (suc d) w t (Ord₊ˢ.ŝ c t₀ g) with cof t | isClo t
... | cω | true with dfᵉ d w (fsn t 0) t₀
...   | just (g′ , p) = just (g′ , 0 ∷ p)
...   | nothing = nothing
dfᵉ (suc d) w t (Ord₊ˢ.ŝ c t₀ g) | cω | false = just (headBad , [])
dfᵉ (suc d) w t (Ord₊ˢ.ŝ c t₀ g) | _ | _ = just (kindBad , [])
dfᵉ (suc d) w t (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) with cof t
... | cω with dfᵉ d w (fsn t 0) o₀
...   | just (g′ , p) = just (g′ , 0 ∷ p)
...   | nothing = nothing
dfᵉ (suc d) w t (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) | _ = just (kindBad , [])
dfᵉ (suc d) w t (Ord₊ˢ.limᵢ () f)
dfᵉ (suc d) w t (Ord₊ˢ.up () x)
dfᵉs zero d w t f = nothing
dfᵉs (suc n) d w t f with dfᵉ d w (fsn t n) (f n)
... | just (g , p) = just (g , n ∷ p)
... | nothing = dfᵉs n d w t f
```


```agda
Ω·2 : T
Ω·2 = Ωp ∷ Ωp ∷ []

t₁ : T
t₁ = ψ₀ᵗ (Ωt (sucT Ω·2))

ΩΩ·2 : PT
ΩΩ·2 = ψᵗ Ω·2 []

Ω+1 : T
Ω+1 = sucT (Ωp ∷ [])

W : T
W = ψ₀ᵗ (ψᵗ Ω·2 (ΩΩ·2 ∷ ψᵗ Ω+1 (ΩΩ·2 ∷ []) ∷ []) ∷ [])
```

## §1 $\psi_0(\Omega_{\Omega\cdot2+\alpha})$

```agda
ev₁ : Ev (suc zero) Fl
ev₁ = tt , (λ q → q)

X : ∀ α → Ordˢ zero
X α = Tᴾ α ev₁ zero

t₂ : T
t₂ = ψ₀ᵗ (Ωt Ω·2)

t₂₂ : T
t₂₂ = ψ₀ᵗ (Ωt (sucT (sucT Ω·2)))

c-t₂ : dfᵉ 14 2 t₂ (X zero) ≡ nothing
c-t₂ = refl

c-t₁ : dfᵉ 16 2 t₁ (X (suc zero)) ≡ nothing
c-t₁ = refl

c-t₁′ : dfᵉ 12 3 t₁ (X (suc zero)) ≡ nothing
c-t₁′ = refl

c-t₂₂ : dfᵉ 14 2 t₂₂ (X (suc (suc zero))) ≡ nothing
c-t₂₂ = refl
```

## §2 $W$: 第一个没有字面界的比较

$W=\psi_0(\psi_{\Omega\cdot2}(\Omega_{\Omega\cdot2}+\psi_{\Omega+1}(\Omega_{\Omega\cdot2})))$. `Ψ` 的世界取 3, 目标 1.

```agda
two three : Ordᴵ
two = suc (suc zero)
three = suc two

ev₃ : Ev three Fl
ev₃ = tt , λ { zero → suc (suc zero) ; (suc ()) }

1<3 : suc zero <ᴵ three
1<3 = suc zero

zy : O (suc zero) (Fl ⊔ Fl)
zy = Ψ ev₃ 1<3 (Ω̇ᴾ zero)

W̃ : P zero (Fl ⊔ (Fl ⊔ (Fl ⊔ Fl))) (Fl ⊔ (Fl ⊔ fk zero))
W̃ = ψᵖ zero (ι zero (Ω̇ᴾ zero) ⊞ ι↓ zy)

ev₄ : Ev (suc zero) (Fl ⊔ (Fl ⊔ fk zero))
ev₄ = ev₁ , (ev₁ , (λ q → q))

ev₅ : Ev (suc zero) (Fl ⊔ (Fl ⊔ (Fl ⊔ Fl)))
ev₅ = ev₁ , (ev₁ , (ev₁ , ev₁))

Xw : Ordˢ zero
Xw = ψ̄ᴾ ev₄ zero W̃ ev₅ zero

c-W : dfᵉ 22 1 W Xw ≡ nothing
c-W = refl

c-W₂ : dfᵉ 12 2 W Xw ≡ nothing
c-W₂ = refl

c-W⁺ : df⁺ 14 10 2 W Xw ≡ nothing
c-W⁺ = refl

c-dev : dfAt 14 (0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []) 4 2 W Xw ≡ nothing
c-dev = refl

-- 对照: 换层号, 比较器报告不一致
ctl : dfᵉ 12 2 t₁ (X zero) ≡ just (headBad , [])
ctl = refl
```

## §3 塔 ([ScafLadderQ](ScafLadderQ.lagda.md))

`Tᵠ m α` 是 $\psi_0(\Omega_{\Omega\cdot(m+1)+\alpha})$. 这些是有限测试, 塔上没有标签.

```agda
Xq : ∀ m α → Ordˢ zero
Xq m α = QQ.Tᵠ m α ev₁ zero

Xω : Ordˢ zero
Xω = QQ.Tω ev₁ zero

t₃ : T
t₃ = ψ₀ᵗ (Ωt (Ωp ∷ Ωp ∷ Ωp ∷ []))

t₄ : T
t₄ = ψ₀ᵗ (Ωt (Ωp ∷ Ωp ∷ Ωp ∷ Ωp ∷ []))

tω : T
tω = ψ₀ᵗ (Ωt (ψᵗ (natT 1) (natT 1) ∷ []))

q-t₂ : dfᵉ 14 2 t₂ (Xq 1 zero) ≡ nothing
q-t₂ = refl

q-t₁ : dfᵉ 14 2 t₁ (Xq 1 (suc zero)) ≡ nothing
q-t₁ = refl

q-t₃ : dfᵉ 14 2 t₃ (Xq 2 zero) ≡ nothing
q-t₃ = refl

q-t₃₁ : dfᵉ 12 2 (ψ₀ᵗ (Ωt (sucT (Ωp ∷ Ωp ∷ Ωp ∷ [])))) (Xq 2 (suc zero)) ≡ nothing
q-t₃₁ = refl

q-t₄ : dfᵉ 12 2 t₄ (Xq 3 zero) ≡ nothing
q-t₄ = refl

q-tω : dfᵉ 12 3 tω Xω ≡ nothing
q-tω = refl
```
