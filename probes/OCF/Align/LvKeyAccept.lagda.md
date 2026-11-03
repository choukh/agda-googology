# 键即节点: 验收 (与 EBO 比较)

> **验收节.** 记号只在本文件. 结论写在 [LvKey](LvKey.lagda.md). 比较器直接取自 [UniformLvAccept](UniformLvAccept.lagda.md), 同一套.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKeyAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ)
import OCF.Align.Level as Lv
open Lv using (Ordᴵ; natᴵ)
import OCF.Align.EBO as E
open E using (T; PT; fsn; cof; c0; c1; cω; cΩ; pred; Ωt; natT; sucT; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.UniformLvAccept using (Tag; kindBad; headBad; ended; dfᵉ; df⁺; dfAt; walkᵉ; strip; fam; ωt; tBη)
open import OCF.Align.LvKeyBase
open import OCF.Align.LvKeyTree renaming (T to Tv)
open import OCF.Align.LvKeyTheta using (F; Lv₅)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Uniform5Wall using (t₁; t₃; W; Ω·2; ΩΩ·2; ψ₁)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ)
open import OCF.Align.Uniform4Head using (Ωp)
```

## §1 回归: 字面层号上的目标

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

## §2 $W$ 与分支值: 目标 $\Omega+1$, 节点 $\Omega+\eta$

全部在同一个顶层 `suc L₂` 上: 这个设计的地板项的键是顶层里的位置, 所以 [UniformLvAccept](UniformLvAccept.lagda.md) 里跨两个 `Fold` 的写法不再适用, 目标写成 `suc tgt₁`. 世界是 `wd 1 (∅ 3)`: 一切节点的界都是 3.

```agda
L₂ : LI
L₂ = Ω· 2

c₂₁ : LI
c₂₁ = suc L₂

cf₂₁ : Cf c₂₁
cf₂₁ = WFΩ 2 , s≈ (selfΩ 2)

open Over c₂₁
open Fold cf₂₁

two : Ordᴵ
two = natᴵ 2

P₂ : Cp L₂ c₂₁
P₂ = suc Cp.self

tgt₁ : (base ⊞ one) <ᴸ c₂₁
tgt₁ = suc (bra two zero)

χ₁ : Fᵗ
χ₁ = Fl₀ ∪ tk P₂ two

Ω̇L₂ : O L₂ Fl₀
Ω̇L₂ = Ω̇ᵖ L₂ P₂ idF (λ _ → tt)

in₁ : O (base ⊞ one) (χ₁ ∪ (Fl₀ ∪ tz))
in₁ = ψᵒ {χ = χ₁} tgt₁ proj₁ (λ {w} e → S→B {Ε w} (proj₂ (proj₂ e)) , tt) (ι ds Ω̇L₂)

Φ : Fᵗ
Φ = Fl₀ ∪ ((Fl₀ ∪ tz) ∪ (((((χ₁ ∪ (Fl₀ ∪ tz)) ∪ tz) ∪ tk P₂ two) ∪ tz)))

W̃ : O L₂ Φ
W̃ = ψᵒ zero idF (λ _ → tt) ((ι ds Ω̇L₂) ⊕ (ι ds (ι (db two P₂) (ι ds in₁))))

w₂ : Wd
w₂ = wd (natᴵ 1) (∅ (natᴵ 3))

ok₂ : Wok w₂
ok₂ = Lv.zero , Lv.suc (Lv.suc Lv.zero)

F₀ : Evt w₂ Fl₀
F₀ = tt , (λ q → q)

k₂ : Evt w₂ (tk P₂ two)
k₂ = tt , natᴵ 3 , refl , (λ q → q)

ev₂ : Evt w₂ Φ
ev₂ = F₀ , ((F₀ , tt) , ((((((F₀ , k₂) , (F₀ , tt)) , tt) , k₂) , tt)))

Xw : Ordˢ Lv.zero
Xw = ψ̄ (ι ds W̃) {w = w₂} ok₂ (ev₂ , tt) Lv.zero

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

**分支值逐点.** $\psi_0(\psi_{\Omega\cdot2}(\Omega_{\Omega\cdot2}+\psi_{\Omega+1}(\Omega_{\Omega+\eta})))$. 第二个分支 $\eta$ 带自己的地板项, 键与 `two` 相同 (`P₂`); `<-dec` 在世界 $c$ 里比较.

```agda
Φη : Ordᴵ → Fᵗ
Φη η = Fl₀ ∪ ((Fl₀ ∪ tz) ∪ (((((χ₁ ∪ (((Fl₀ ∪ tk P₂ η) ∪ tk P₂ η) ∪ tz)) ∪ tz) ∪ tk P₂ two) ∪ tz)))

Bη : ∀ η → O L₂ (Φη η)
Bη η = ψᵒ zero idF (λ _ → tt)
         ((ι ds Ω̇L₂) ⊕ (ι ds (ι (db two P₂) (ι ds (ψᵒ {χ = χ₁} tgt₁ proj₁ (λ {w} e → S→B {Ε w} (proj₂ (proj₂ e)) , tt)
            (ι ds (ι (db η P₂) (Ω̇ᵖ (base ⊞ η) {Fl₀ ∪ tk P₂ η} (suc (bra η Cp.self)) proj₁ (λ {w} e → S→B {Ε w} (proj₂ (proj₂ e)) , tt)))))))))

wη : Ordᴵ → Wd
wη c = wd (natᴵ 1) (∅ c)

evη : ∀ η c → (Lv.Simᴵ (Lv.suc η) c) → (Lv.Simᴵ (natᴵ 3) c) → Evt (wη c) (Φη η)
evη η c a b = Fw , ((Fw , tt) , ((((((Fw , ktwo) , (((Fw , kη) , kη) , tt)) , tt) , ktwo) , tt)))
  where
  Fw : Evt (wη c) Fl₀
  Fw = tt , (λ q → q)
  ktwo : Evt (wη c) (tk P₂ two)
  ktwo = tt , c , refl , b
  kη : Evt (wη c) (tk P₂ η)
  kη = tt , c , refl , a

Yη : ∀ η c → Lv.zero Lv.<ᴵ c → Lv.Simᴵ (Lv.suc η) c → Lv.Simᴵ (natᴵ 3) c → Ordˢ Lv.zero
Yη η c z a b = ψ̄ (ι ds (Bη η)) {w = wη c} (Lv.zero , z) (evη η c a b , tt) Lv.zero

y1 y2 y3 : Ordˢ Lv.zero
y1 = Yη (natᴵ 1) (natᴵ 5) (Lv.suc (Lv.suc (Lv.suc (Lv.suc Lv.zero)))) (λ q → Lv.suc (Lv.suc (Lv.suc q))) (λ q → Lv.suc (Lv.suc q))
y2 = Yη (natᴵ 2) (natᴵ 5) (Lv.suc (Lv.suc (Lv.suc (Lv.suc Lv.zero)))) (λ q → Lv.suc (Lv.suc q)) (λ q → Lv.suc (Lv.suc q))
y3 = Yη (natᴵ 3) (natᴵ 5) (Lv.suc (Lv.suc (Lv.suc (Lv.suc Lv.zero)))) (λ q → Lv.suc q) (λ q → Lv.suc (Lv.suc q))

ω₂ : Ordᴵ
ω₂ = Lv.suc (Lv.suc Lv.ωᴵ)

yω : Ordˢ Lv.zero
yω = Yη Lv.ωᴵ ω₂ (Lv.suc (Lv.suc (Lv.lim 1 Lv.zero))) (λ q → Lv.suc q) n3
  where
  n3 : Lv.Simᴵ (natᴵ 3) ω₂
  n3 q = Lv.suc (Lv.suc (Lv.lim 3 q))

c-y1 : dfᵉ 8 2 (tBη (natT 1)) y1 ≡ nothing
c-y1 = refl
c-y2 : dfᵉ 8 2 (tBη (natT 2)) y2 ≡ nothing
c-y2 = refl
c-y3 : dfᵉ 8 2 (tBη (natT 3)) y3 ≡ nothing
c-y3 = refl
c-yω : dfᵉ 8 2 (tBη ωt) yω ≡ nothing
c-yω = refl
```

## §3 对照: 比较器分得开

```agda
ctl₁ : dfᵉ 8 2 (tBη (natT 2)) y1 ≡ just (headBad , 1 ∷ [])
ctl₁ = refl
ctl₂ : dfᵉ 8 2 (tBη (natT 1)) y2 ≡ just (headBad , 1 ∷ 1 ∷ [])
ctl₂ = refl
ctl₃ : dfᵉ 12 2 t₂ Xω ≡ just (headBad , 1 ∷ [])
ctl₃ = refl
```

## §4 一致族与第 5 站: 证书是变量

`F θ`, `Lv₅` 的 `WF` 没有写 (§6). `refl` 说明这段路径上证书没有被问到.

```agda
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

  to-t₁ : proj₁ (walkᵉ (0 ∷ 0 ∷ 3 ∷ 0 ∷ []) (fam Ωᵗ) (T₀ _ c₅)) ≡ t₁
  to-t₁ = refl
```

## §5 $\psi_1(1)+\Omega$ 上的闭包走到第 1 个孩子

旧树在这里的标签相撞 ([LvKeyNeg](LvKeyNeg.lagda.md)). 这里走第 $\ge1$ 个孩子, 带近似 (`df⁺`), 跑的是真的 `kdec` 与 `selF`.

```agda
c-ω2⁺ : df⁺ 8 6 2 tω2 Xω2 ≡ nothing
c-ω2⁺ = refl
c-ω3⁺ : df⁺ 8 6 2 tω3 Xω3 ≡ nothing
c-ω3⁺ = refl
```
