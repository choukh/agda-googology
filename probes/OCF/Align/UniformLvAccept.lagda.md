# 同层上界: 验收 (与 EBO 比较)

> **验收节.** 记号只在本文件. 结论写在 [UniformLv](UniformLv.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformLvAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ)
import OCF.Align.Level as Lv
open Lv using (Ordᴵ; natᴵ)
import OCF.Align.EBO as E
open E using (T; PT; fsn; cof; c0; c1; cω; cΩ; pred; Ωt; natT; sucT; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.UniformLvWalk
open import OCF.Align.UniformLvBase
open import OCF.Align.UniformLvTree hiding (T)
open import OCF.Align.UniformLvTheta using (F; Lv₅)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Uniform5Wall using (t₁; t₃; W; Ω·2; ΩΩ·2; ψ₁)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ)
open import OCF.Align.Uniform4Head using (Ωp)
```

## §1 比较器

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

## §2 精确的比较器: 闭包只走第 0 个孩子

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

## §3 决定性检验: 字面层号上的目标

`T₀ L cf`: 封闭计值. 下面都是 `refl`, 有限宽度与深度, 比种类再加上 `ŝ` 必须对应 $\Omega$-共尾的尾巴 (`headBad`). 目标包括过 $\Omega+\eta$ 范围的第一点, $\Omega\cdot3$, $\psi_1(1)=\Omega\cdot\omega$, 以及再往上 $\psi_1(1)+1$, $\psi_1(1)+\Omega$, $\psi_1(1)+\Omega\cdot2$.

```agda
t₂ tω tω1 tω2 tω3 ψ1 : T
ψ1 = ψ₁ (natT 1)
t₂ = ψ₀ᵗ (Ωt Ω·2)
tω = ψ₀ᵗ (Ωt ψ1)
tω1 = ψ₀ᵗ (Ωt (sucT ψ1))
tω2 = ψ₀ᵗ (Ωt (ψ1 ++ (Ωp ∷ [])))
tω3 = ψ₀ᵗ (Ωt (ψ1 ++ (Ωp ∷ Ωp ∷ [])))

X₂ X₂₁ X₃ Xω Xω1 Xω2 Xω3 : Ordˢ Lv.zero
X₂  = T₀ (Ω· 2) (WFΩ 2 , selfΩ 2)
X₂₁ = T₀ (suc (Ω· 2)) (WFΩ 2 , s≈ (selfΩ 2))
X₃  = T₀ (Ω· 3) (WFΩ 3 , selfΩ 3)
Xω  = T₀ Ω·ω (WFΩ·ω , selfΩ·ω)
Xω1 = T₀ (suc Ω·ω) (WFΩ·ω , s≈ selfΩ·ω)
Xω2 = T₀ (times Ω·ω) (Mono.WF-times Ω·ω selfΩ·ω WFΩ·ω , ≈times selfΩ·ω)
Xω3 = T₀ (times (times Ω·ω)) (Mono.WF-times _ (≈times selfΩ·ω) (Mono.WF-times Ω·ω selfΩ·ω WFΩ·ω) , ≈times (≈times selfΩ·ω))

c-t₂ : dfᵉ 14 2 t₂ X₂ ≡ nothing
c-t₂ = refl
c-t₁ : dfᵉ 16 2 t₁ X₂₁ ≡ nothing
c-t₁ = refl
c-t₁′ : dfᵉ 12 3 t₁ X₂₁ ≡ nothing
c-t₁′ = refl
c-t₃ : dfᵉ 14 2 t₃ X₃ ≡ nothing
c-t₃ = refl
c-tω : dfᵉ 12 3 tω Xω ≡ nothing
c-tω = refl
c-tω1 : dfᵉ 10 2 tω1 Xω1 ≡ nothing
c-tω1 = refl
c-tω2 : dfᵉ 10 2 tω2 Xω2 ≡ nothing
c-tω2 = refl
c-tω3 : dfᵉ 10 2 tω3 Xω3 ≡ nothing
c-tω3 = refl
```

## §4 $W$ 与分支值: 目标 $\Omega+1$, 节点 $\Omega+\eta$

`Xw`: $W$ 的树, 直接由折叠写出 (不走链点, 没有近似). 目标 $\Omega+1$ 是 $\Omega\cdot2$ 里分支 2 的第一个前驱, 地板 `tk 1 two`. 比较的答案是 `<-dec` 在世界 $w\,1=3$ 里算的.

```agda
L₂ : LI
L₂ = Ω· 2

module F₂  = Fold {L₂} (WFΩ 2 , selfΩ 2)
module F₂₁ = Fold {suc L₂} (WFΩ 2 , s≈ (selfΩ 2))

two : Ordᴵ
two = natᴵ 2

tgt₁ : (base ⊞ one) <ᴸ L₂
tgt₁ = bra two zero

χ₁ : Fᵗ
χ₁ = Fl₀ ∪ tk 1 two

in₁ : O (base ⊞ one) (χ₁ ∪ Fl₀)
in₁ = F₂.ψᵒ {χ = χ₁} tgt₁ proj₁ (λ e → proj₂ e Lv.zero , tt) (Ω̇ L₂)

Φ : Fᵗ
Φ = Fl₀ ∪ ((Fl₀ ∪ tz) ∪ ((((χ₁ ∪ Fl₀) ∪ tz) ∪ tk 1 two) ∪ tz))

W̃ : O L₂ Φ
W̃ = F₂₁.ψᵒ zero idF (λ _ → tt) ((ι ds (Ω̇ L₂)) ⊕ (ι ds (ι (db two) (ι ds in₁))))

w₂ : Wd
w₂ zero = natᴵ 1
w₂ (suc _) = natᴵ 3

ok₂ : Wok w₂
ok₂ zero = Lv.zero
ok₂ (suc _) = Lv.suc (Lv.suc Lv.zero)

F₀ : Evt w₂ Fl₀
F₀ = tt , (λ q → q)

k₂ : Evt w₂ (tk 1 two)
k₂ = λ q → q

ev₂ : Evt w₂ Φ
ev₂ = F₀ , ((F₀ , tt) , ((((((F₀ , k₂) , F₀) , tt) , k₂) , tt)))

Xw : Ordˢ Lv.zero
Xw = F₂.ψ̄ W̃ {w = w₂} ok₂ ev₂ Lv.zero

-- 精确: 闭包只走第 0 个孩子
c-W : dfᵉ 24 1 W Xw ≡ nothing
c-W = refl

c-W₂ : dfᵉ 12 2 W Xw ≡ nothing
c-W₂ = refl

-- 带近似 (闭包的第 1 个孩子用 apx⁺): 宽 2 深 10
c-W⁺ : df⁺ 14 10 2 W Xw ≡ nothing
c-W⁺ = refl

-- InaccFloorAccept.Zero.dev 报告的路径 (从 W 走): W[0] 之下深度 10
c-dev : dfAt 14 (0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []) 4 2 W Xw ≡ nothing
c-dev = refl
```

**分支值逐点.** $\psi_0(\psi_{\Omega\cdot2}(\Omega_{\Omega\cdot2}+\psi_{\Omega+1}(\Omega_{\Omega+\eta})))$, $\eta$ 取字面值. $\eta=1$ 穿透, $\eta=2,3$ 折叠, $\eta=\omega$ 是极限, 比较在不同的 `lim` 分支上用 `s` 搬运.

```agda
χη : Ordᴵ → Fᵗ
χη η = (χ₁ ∪ (Fl₀ ∪ tk 1 η))

Φη : Ordᴵ → Fᵗ
Φη η = Fl₀ ∪ ((Fl₀ ∪ tz) ∪ (((χη η ∪ tz) ∪ tk 1 two) ∪ tz))

Bη : ∀ η → O L₂ (Φη η)
Bη η = F₂₁.ψᵒ zero idF (λ _ → tt)
         ((ι ds (Ω̇ L₂)) ⊕ (ι ds (ι (db two) (ι ds (F₂.ψᵒ {χ = χ₁} tgt₁ proj₁ (λ e → proj₂ e Lv.zero , tt) (ι (db η) (Ω̇ (base ⊞ η))))))))

tBη : T → T
tBη x = ψ₀ᵗ (ψᵗ Ω·2 (ΩΩ·2 ∷ ψᵗ (sucT (Ωp ∷ [])) (ψᵗ (Ωp ∷ x) [] ∷ []) ∷ []) ∷ [])

wη : Ordᴵ → Wd
wη c zero = natᴵ 1
wη c (suc _) = c

evη : ∀ η c → (Lv.Simᴵ (Lv.suc η) c) → (Lv.Simᴵ (natᴵ 3) c) → Evt (wη c) (Φη η)
evη η c a b = Fw , ((Fw , tt) , ((((((Fw , b) , (Fw , a)) , tt) , b) , tt)))
  where
  Fw : Evt (wη c) Fl₀
  Fw = tt , (λ q → q)

Yη : ∀ η c → Lv.zero Lv.<ᴵ c → Lv.Simᴵ (Lv.suc η) c → Lv.Simᴵ (natᴵ 3) c → Ordˢ Lv.zero
Yη η c z a b = F₂.ψ̄ (Bη η) {w = wη c} okc (evη η c a b) Lv.zero
  where
  okc : Wok (wη c)
  okc zero = Lv.zero
  okc (suc _) = z

-- η = 1, 2, 3: 世界 c = 5
s5 : ∀ n → Lv.Simᴵ (natᴵ n) (natᴵ n)
s5 n q = q

y1 y2 y3 : Ordˢ Lv.zero
y1 = Yη (natᴵ 1) (natᴵ 5) (Lv.suc (Lv.suc (Lv.suc (Lv.suc Lv.zero)))) (λ q → Lv.suc (Lv.suc (Lv.suc q))) (λ q → Lv.suc (Lv.suc q))
y2 = Yη (natᴵ 2) (natᴵ 5) (Lv.suc (Lv.suc (Lv.suc (Lv.suc Lv.zero)))) (λ q → Lv.suc (Lv.suc q)) (λ q → Lv.suc (Lv.suc q))
y3 = Yη (natᴵ 3) (natᴵ 5) (Lv.suc (Lv.suc (Lv.suc (Lv.suc Lv.zero)))) (λ q → Lv.suc q) (λ q → Lv.suc (Lv.suc q))

-- η = ω: 世界 c = ω + 2
ω₂ : Ordᴵ
ω₂ = Lv.suc (Lv.suc Lv.ωᴵ)

yω : Ordˢ Lv.zero
yω = Yη Lv.ωᴵ ω₂ (Lv.suc (Lv.suc (Lv.lim 1 Lv.zero))) (λ q → Lv.suc q) n3
  where
  n3 : Lv.Simᴵ (natᴵ 3) ω₂
  n3 q = Lv.suc (Lv.suc (Lv.lim 3 q))

ωt : T
ωt = ψ₀ᵗ (natT 1)

c-y1 : dfᵉ 8 2 (tBη (natT 1)) y1 ≡ nothing
c-y1 = refl
c-y2 : dfᵉ 8 2 (tBη (natT 2)) y2 ≡ nothing
c-y2 = refl
c-y3 : dfᵉ 8 2 (tBη (natT 3)) y3 ≡ nothing
c-y3 = refl
c-yω : dfᵉ 8 2 (tBη ωt) yω ≡ nothing
c-yω = refl
```

## §5 一致族与第 5 站: 证书是变量

`F θ`, `Lv₅` 的 `WF` 没有写, 所以 `cf` 是变量: `refl` 说明这段路径上证书**没有被问到**, 与 [InaccFloorAccept](InaccFloorAccept.lagda.md) 的 `AllS` 同类. 闭包只走第 0 个孩子, 所以比较器没有近似.

`walkᵉ`: 同样的精确走法. 从第 5 站走 `0 ∷ 0 ∷ 3 ∷ 0` 就是 [Uniform5Wall](Uniform5Wall.lagda.md) 的路径 `p₁` 的后 4 步, 到 $\psi_0(\Omega_{\Omega\cdot2+1})$. 这里的层号由 `F` 算出, 与 §3 的字面层号不是同一个项.

```agda
fam : T → T
fam θ = ψ₀ᵗ (Ωt (ψ₁ (Ωt θ)))

walkᵉ : List ℕ → T → Ordˢ Lv.zero → T × Ordˢ Lv.zero
walkᵉ [] t x = t , x
walkᵉ (n ∷ r) t x with strip t x
... | t′ , Ord₊ˢ.lim f = walkᵉ r (fsn t′ n) (f n)
... | t′ , Ord₊ˢ.ŝ c t₀ g = walkᵉ r (fsn t′ 0) t₀
... | t′ , Ord₊ˢ.ĉᴸ c t₀ g o₀ o = walkᵉ r (fsn t′ 0) o₀
... | t′ , x′ = t′ , x′

module AllCf (c₁ : Cf (F (natᴵ 1))) (c₂ : Cf (F (natᴵ 2))) (c₃ : Cf (F (natᴵ 3))) (cω : Cf (F Lv.ωᴵ)) (c₅ : Cf Lv₅) where
  c-θ1 : dfᵉ 20 2 (fam (natT 1)) (T₀ _ c₁) ≡ nothing
  c-θ1 = refl
  c-θ2 : dfᵉ 20 2 (fam (natT 2)) (T₀ _ c₂) ≡ nothing
  c-θ2 = refl
  c-θ3 : dfᵉ 20 2 (fam (natT 3)) (T₀ _ c₃) ≡ nothing
  c-θ3 = refl
  c-θω : dfᵉ 20 2 (fam ωt) (T₀ _ cω) ≡ nothing
  c-θω = refl
  c-5 : dfᵉ 20 2 (fam Ωᵗ) (T₀ _ c₅) ≡ nothing
  c-5 = refl
  c-5′ : dfᵉ 10 3 (fam Ωᵗ) (T₀ _ c₅) ≡ nothing
  c-5′ = refl

  -- 第 5 站到 t₁. 深度 3 处 `cf` 被问到 (探针: 对变量 `c₅` 不归约, 这不是编译的否定), 所以再往下只有 §3 的字面层号
  to-t₁ : proj₁ (walkᵉ (0 ∷ 0 ∷ 3 ∷ 0 ∷ []) (fam Ωᵗ) (T₀ _ c₅)) ≡ t₁
  to-t₁ = refl
  c-5t₁ : dfᵉ 2 2 t₁ (proj₂ (walkᵉ (0 ∷ 0 ∷ 3 ∷ 0 ∷ []) (fam Ωᵗ) (T₀ _ c₅))) ≡ nothing
  c-5t₁ = refl
```

## §6 对照: 比较器分得开

下面每条都是不一致的报告, 说明上面的 `nothing` 不是空话. 第一条: 记号的分支值 2 对上树的分支值 1, 在第 1 个孩子处错. 第三条: 层号换掉.

```agda
ctl₁ : dfᵉ 8 2 (tBη (natT 2)) y1 ≡ just (headBad , 1 ∷ [])
ctl₁ = refl
ctl₂ : dfᵉ 8 2 (tBη (natT 1)) y2 ≡ just (headBad , 1 ∷ 1 ∷ [])
ctl₂ = refl
ctl₃ : dfᵉ 12 2 t₂ Xω ≡ just (headBad , 1 ∷ [])
ctl₃ = refl
```
