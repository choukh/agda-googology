# 序数值验收: $T^c$ 与 $\psi_0(\Omega_\Omega)$ 互相 $\preccurlyeq$

> **验收文件**, 读 `NoCumsum`, `BTBOFull`, `Label` 贴标签的树. 判决: **HOLDS**, 档次是**序数值验收** (互相 $\preccurlyeq$), 不是基本列验收, 也不是前驱结构验收. 主定理 `Tᶜ≈`:
>
>     fr Tᶜ ≈ᵛ BTBOᴵ
>
> `BTBOᴵ` 是通过基本列验收的 $\psi_0(\Omega_\Omega)$ 的树 (`Label.BTBO-label`). 所以累加**这一站不改序数值**; 基本列不同, FGH 的值这里不说 (账在 [CumUpAcceptLedger](CumUpAcceptLedger.lagda.md)).
>
> 方法: 桥 [CumUpAcceptSim](CumUpAcceptSim.lagda.md) 把 $y_n$ 换成 $\psi^0(\Omega_{\tau\hat\eta_n})$, 其中 $\hat\eta_n$ 是 `Ordᴰ` 里的**累加和** `cumsum Ô n`, $\hat O_{n+1}=\mathrm{ord}^D(y_n)$. 这是 $T^c$ 特有的形状, 不是 src 的 $x_k$: 下标把**整条链**的输出加起来. 然后用 `BTBOFull` 的 `V1`, `V2`, `V3`, `Ψ-emb`.
>
> - 下界 `Low`: $\gamma_k\preccurlyeq y_{k+1}$. 下标里的最后一块就够了 (`Eb-off`).
> - 上界 `Upp`: $y_k\preccurlyeq\gamma_{m_k}$, 要把整条累加和嵌进 $\gamma$ (`Eb-plus`): $a+(b+1)$ 落到 $A+(A+A)\preccurlyeq\gamma_{m+2}$. 嵌入里不判定值, 只用 `inv` 的字面分块, 不触壁垒.
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUpAcceptVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; module Trich)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum) renaming (_+_ to _+ᴰ_)
open S using (ordᴰ)
open import OCF.Align.Level hiding (below)
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼l; l≼; ≼-trans; ≅→≼; ⊑→≼; 1≼ψ⁰)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValDn using (τ; τ-<; via<)
open import OCF.Align.BTBOValAbsorb using (St)
open import OCF.Align.BTBOValNeg using (add-≺)
open import OCF.Align.BTBOFullLv using (SV; svz; svs; svl; SV-L; St-≅; St-F; Pos; ps; z<SV)
open import OCF.Align.BTBOFullEmb using (Ψ-emb)
open import OCF.Align.BTBOFullEb using (V2; Eb-off; 𝕆; module Blocks; inv; Inv; inl; inr; cancel<; cancel≡; add-not<)
open import OCF.Align.BTBOFullV3 using (V3; bkᴵ; Fʸ; T3; T3≺; T3⊑; Fstep; add-left; 𝕋₀; ≺→⊑₀)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃; module WO; module WT)
open import OCF.Align.BTBOFull using (St-bk; bk≅γ; γ-step)
import OCF.Align.BTBOFullQ
import OCF.Free.Level as FL
open import OCF.Align.CumReadBase using (Ord₀; cumA; cs; _⊞_; next)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.CumReadTop using (Tᶜ; ysᶜ; chainᶜ; η; lg)
open import OCF.Align.CumUpAcceptSim using (Ix; iz; is; il; fr; Y-sim)
```

## §1 下标链落进 `Ordᴰ`

```agda
sr : Ord₀ → S.Ord₀
sr FL.zero = S.zero
sr (FL.suc a) = S.suc (sr a)
sr (FL.lim f) = S.lim (λ n → sr (f n))
sr (FL.limᵢ () f)
sr (FL.up () x)

tr₀-sr : ∀ y → tr₀ (sr y) ≅ fr y
tr₀-sr FL.zero = z≅
tr₀-sr (FL.suc a) = s≅ (tr₀-sr a)
tr₀-sr (FL.lim f) = l≅ (λ n → tr₀-sr (f n))
tr₀-sr (FL.limᵢ () f)
tr₀-sr (FL.up () x)

Ix-⊞ : ∀ {a b} a′ b′ → Ix a (τ a′) → Ix b (τ b′) → Ix (a ⊞ b) (τ (a′ +ᴰ b′))
Ix-⊞ a′ B.zero ia iz = ia
Ix-⊞ a′ (B.suc b′) ia (is ib) = is (Ix-⊞ a′ b′ ia ib)
Ix-⊞ a′ (B.lim f m) ia (il h) = il (λ n → Ix-⊞ a′ (f n) ia (h n))

Ix-cs : (g : ℕ → A) (O : ℕ → Ordᴰ) → (∀ n → Ix (g n) (τ (O n))) → ∀ n → Ix (cs g n) (τ (cumsum O n))
Ix-cs g O h zero = h 0
Ix-cs g O h (suc n) = Ix-⊞ (cumsum O n) (B.suc (O (suc n))) (Ix-cs g O h n) (is (h (suc n)))

Ix-cum : ∀ y → Ix (cumA y) (τ (ordᴰ (sr y)))
Ix-cum FL.zero = iz
Ix-cum (FL.suc a) = is (Ix-cum a)
Ix-cum (FL.lim f) = il (Ix-cs (λ n → cumA (f n)) (λ n → ordᴰ (sr (f n))) (λ n → Ix-cum (f n)))
Ix-cum (FL.limᵢ () f)
Ix-cum (FL.up () x)

Ô : ℕ → Ordᴰ
Ô zero = B.suc B.zero
Ô (suc n) = ordᴰ (sr (ysᶜ n))

η̂ : ℕ → Ordᴰ
η̂ = cumsum Ô

Ix-η : ∀ n → Ix (η (chainᶜ n)) (τ (η̂ (suc n)))
Ix-η zero = Ix-⊞ (B.suc B.zero) (B.suc (Ô 1)) (is iz) (is (Ix-cum (ysᶜ 0)))
Ix-η (suc n) = Ix-⊞ (η̂ (suc n)) (B.suc (Ô (suc (suc n)))) (Ix-η n) (is (Ix-cum (ysᶜ (suc n))))

τ-SV : ∀ a → SV (τ a)
τ-SV B.zero = svz
τ-SV (B.suc a) = svs (τ-SV a)
τ-SV (B.lim f m) = svl (λ n → τ-SV (f n)) (λ n → τ (f n) , via< (τ-< (m Trich.zero)) , ⊑ᴵ-refl)

Pos-η : ∀ n → Pos (τ (η̂ n))
Pos-η zero = ps
Pos-η (suc n) = ps

z : ℕ → Ordᶜ zero
z n = fr (ysᶜ n)

z-all : ∀ n → z n ≅ Fʸ (τ (η̂ n))
z-all zero = Y-sim _ (is iz) (z<SV (τ-SV (η̂ 0)) ps)
z-all (suc n) = Y-sim (lg (chainᶜ n)) (Ix-η n) (z<SV (τ-SV (η̂ (suc n))) ps)

St-z : ∀ n → St (z n)
St-z n = St-≅ (z-all n) (St-F (τ-SV (η̂ n)) (Pos-η n))

St-sr : ∀ n → St (tr₀ (sr (ysᶜ n)))
St-sr n = St-≅ (tr₀-sr (ysᶜ n)) (St-z n)
```

## §2 下界

```agda
Eb-id : ∀ {T} → WO.Eb T T
Eb-id = record { map = λ {c} _ → c ; below = λ p → p ; mono = λ p q r → r ; coh = λ p q r → r }

Low : ∀ k → N.γ k ≼ z (suc k)
Low zero = ≼-trans (1≼ψ⁰ (Ω (τ (η̂ 1)))) (≅→≼ (≅-sym (z-all 1)))
Low (suc k) =
  ≼-trans (Ψ-emb (PW₃ (V1 (SV-L k))))
  (≼-trans (Ψ-emb (PW₁ (V2 (bkᴵ (N.L k)) (sr (ysᶜ (suc k))) (St-bk (SV-L k)) (St-sr (suc k))
                         (≼-trans (≅→≼ (bk≅γ k)) (≼-trans (Low k) (≅→≼ (≅-sym (tr₀-sr (ysᶜ (suc k)))))))))) 
  (≼-trans (Ψ-emb (PW₁ (Eb-off Ô (suc (suc k)) (Eb-id {T = Ô (suc (suc k))}))))
           (≅→≼ (≅-sym (z-all (suc (suc k)))))))
```

## §3 上界

```agda
compose : ∀ {X T} {Bd : Ordᶜ zero} → WO.Eb X T → WT.Eb T Bd → WT.Eb X Bd
compose e e′ = record
  { map = λ p → WT.map e′ (WO.below e p)
  ; below = λ p → WT.below e′ (WO.below e p)
  ; mono = λ p q r → WT.mono e′ _ _ (WO.mono e p q r)
  ; coh = λ p q r → WT.coh e′ _ _ (WO.coh e p q r) }

module Plus {a b : Ordᴰ} (c : Ordᴵ) (ea : WT.Eb a (Fʸ c)) (eb : WT.Eb b (Fʸ c)) where
  AA : Ordᶜ zero
  AA = Fʸ c

  N′ : ∀ {x} → x B.< B.suc b → Ordᶜ zero
  N′ B.zero = AA + AA
  N′ (B.suc p) = AA + WT.map eb p

  Nb : ∀ {x} (p : x B.< B.suc b) → N′ p ≺ T3 c
  Nb B.zero = T3≺ c
  Nb (B.suc p) = ≺→⊑₀ (T3≺ c) (add-≺ AA (WT.below eb p))

  Nm : ∀ {x y} (p : x B.< B.suc b) (q : y B.< B.suc b) → x B.< y → N′ p ≺ N′ q
  Nm B.zero B.zero r = ⊥-elim (OCF.Align.BTBOFullQ.<ᴰ-irrefl r)
  Nm B.zero (B.suc q) r = ⊥-elim (OCF.Align.BTBOFullQ.clash-lt r q)
  Nm (B.suc p) B.zero r = add-≺ AA (WT.below eb p)
  Nm (B.suc p) (B.suc q) r = add-≺ AA (WT.mono eb p q r)

  Nc : ∀ {x y} (p : x B.< B.suc b) (q : y B.< B.suc b) → x ≡ y → N′ p ≅ N′ q
  Nc B.zero B.zero r = ≅-refl⁰ _
  Nc B.zero (B.suc q) refl = ⊥-elim (OCF.Align.BTBOFullQ.<ᴰ-irrefl q)
  Nc (B.suc p) B.zero refl = ⊥-elim (OCF.Align.BTBOFullQ.<ᴰ-irrefl p)
  Nc (B.suc p) (B.suc q) r = add-≅ (≅-refl⁰ _) (WT.coh eb p q r)

  fl : ∀ {u x} → u ≺ AA → (p : x B.< B.suc b) → u ≺ N′ p
  fl h B.zero = add-left h _
  fl h (B.suc p) = add-left h _

  disp : ∀ {x} → Inv a (B.suc b) x → Ordᶜ zero
  disp (inl q) = WT.map ea q
  disp (inr d r e) = N′ r

  Eb-plus : WT.Eb (a +ᴰ B.suc b) (T3 c)
  Eb-plus = record { map = m ; below = bl ; mono = mn ; coh = ch }
    where
    m : ∀ {x} → x B.< a +ᴰ B.suc b → Ordᶜ zero
    m p = disp (inv {a} {B.suc b} p)
    bl : ∀ {x} (p : x B.< a +ᴰ B.suc b) → m p ≺ T3 c
    bl p with inv {a} {B.suc b} p
    ... | inl q = add-left (WT.below ea q) _
    ... | inr d r _ = Nb r
    mn : ∀ {x y} (p : x B.< a +ᴰ B.suc b) (q : y B.< a +ᴰ B.suc b) → x B.< y → m p ≺ m q
    mn p q r with inv {a} {B.suc b} p | inv {a} {B.suc b} q
    ... | inl p′ | inl q′ = WT.mono ea p′ q′ r
    ... | inl p′ | inr d t _ = fl (WT.below ea p′) t
    ... | inr d t refl | inl q′ = ⊥-elim (add-not< a d (B.<-trans r q′))
    ... | inr d₁ t₁ refl | inr d₂ t₂ refl = Nm t₁ t₂ (cancel< t₁ t₂ r)
    ch : ∀ {x y} (p : x B.< a +ᴰ B.suc b) (q : y B.< a +ᴰ B.suc b) → x ≡ y → m p ≅ m q
    ch p q r with inv {a} {B.suc b} p | inv {a} {B.suc b} q
    ... | inl p′ | inl q′ = WT.coh ea p′ q′ r
    ... | inl p′ | inr d t refl with r
    ...   | refl = ⊥-elim (add-not< a d p′)
    ch p q r | inr d t refl | inl q′ with r
    ...   | refl = ⊥-elim (add-not< a d q′)
    ch p q r | inr d₁ t₁ refl | inr d₂ t₂ refl = Nc t₁ t₂ (cancel≡ t₁ t₂ r)

γ-≺ : ∀ m → N.γ m ≺ N.γ (suc m)
γ-≺ zero = ≺l 0 (≺l 2 (≺z (≅-refl⁰ _)))
γ-≺ (suc m) = Ψ⁰-mono (s⊑′ (toLevel-≺ (N.cert m) (N.cert (suc m)) (γ-≺ m))) (Fstep (N.L m))

L-≺ : ∀ m → N.L m ≺ᴵ N.L (suc m)
L-≺ m = toLevel-≺ (N.cert m) (N.cert (suc m)) (γ-≺ m)

record Up (k : ℕ) : Set where
  field
    m   : ℕ
    zle : z k ≼ N.γ m
    E   : WT.Eb (η̂ k) (N.γ m)
open Up

Up-0 : Up 0
Up-0 = record
  { m = 1
  ; zle = ≅→≼ (z-all 0)
  ; E = WT.Eb-suc {Bd = zero} WT.Eb-zero zero (λ p → p) (z≺ψ⁰ (Ω (suc zero))) }

Up-s : ∀ {k} → Up k → Up (suc k)
Up-s {k} u = record { m = suc (suc (suc m₀)) ; zle = ≼-trans (≅→≼ (z-all (suc k))) (Ψ-emb (PW₂ (N.cert (suc (suc m₀))) E″)) ; E = WT.Eb-wk E″ (N.D.diag-step (suc (suc m₀))) }
  where
  m₀ = m u
  w : tr₀ (sr (ysᶜ k)) ≼ tr₀ (bkᴵ (N.L m₀))
  w = ≼-trans (≅→≼ (tr₀-sr (ysᶜ k))) (≼-trans (zle u) (≅→≼ (≅-sym (bk≅γ m₀))))
  Fe : WT.Eb (ordᴰ (sr (ysᶜ k))) (N.γ (suc m₀))
  Fe = compose (V2 (sr (ysᶜ k)) (bkᴵ (N.L m₀)) (St-sr k) (St-bk (SV-L m₀)) w) (V3 (SV-L m₀))
  E′ : WT.Eb (η̂ k) (N.γ (suc m₀))
  E′ = WT.Eb-wk (E u) (N.D.diag-step m₀)
  E″ : WT.Eb (η̂ (suc k)) (N.γ (suc (suc m₀)))
  E″ = WT.Eb-wk (Plus.Eb-plus (N.L m₀) E′ Fe) (λ h → Ψ⁰-mono (s⊑′ (L-≺ m₀)) (T3⊑ (N.L m₀) h))

Upp : ∀ k → Up k
Upp zero = Up-0
Upp (suc k) = Up-s (Upp k)
```

## §4 主定理

```agda
Tᶜ≈ : fr Tᶜ ≈ᵛ BTBOᴵ
Tᶜ≈ = l≼ (λ n → ≼l (m (Upp n)) (≼-trans (zle (Upp n)) (γ-step (m (Upp n))))) ,
      l≼ (λ k → ≼l (suc (suc k)) (Low (suc k)))
```

与 src 的 `BTBO`: 传递 `BTBOFull.BTBO≈`. 第 0 层翻译 `fr` 与 `tr₀` 都不改树.

```agda
open import OCF.Align.BTBOFull using (BTBO≈)


Tᶜ≈src : fr Tᶜ ≈ᵛ tr₀ S.BTBO
Tᶜ≈src = ≼-trans (proj₁ Tᶜ≈) (proj₂ BTBO≈) , ≼-trans (proj₁ BTBO≈) (proj₂ Tᶜ≈)
```

## §5 逐项比较: 毛刺在序数值上的方向

$T^c$ 的第 $k$ 项是 $y_k$, `BTBOᴵ` 的第 $k$ 项是 $\gamma_{k+1}$.

- `y₀≅γ₁`: 第 0 项结构相同.
- `term-≥`: **每一项** $\gamma_{k+1}\preccurlyeq y_k$.
- `term₁-strict`: 第 1 项**严格更大**, $\gamma_2+1\preccurlyeq y_1$. 所以两棵树的基本列在序数值上就不同, 不只是形状不同. 这条是编译过的定理, 不是测试. 它不说 FGH 的大小.

```agda
y₀≅γ₁ : z 0 ≅ N.γ 1
y₀≅γ₁ = z-all 0

term-≥ : ∀ k → N.γ (suc k) ≼ z k
term-≥ zero = ≅→≼ (≅-sym (z-all 0))
term-≥ (suc k) =
  ≼-trans (Ψ-emb (PW₃ (V1 (SV-L (suc k)))))
  (≼-trans (Ψ-emb (PW₁ (V2 (bkᴵ (N.L (suc k))) (sr (ysᶜ k)) (St-bk (SV-L (suc k))) (St-sr k)
                         (≼-trans (≅→≼ (bk≅γ (suc k))) (≼-trans (term-≥ k) (≅→≼ (≅-sym (tr₀-sr (ysᶜ k)))))))))
  (≼-trans (Ψ-emb (PW₁ (Eb-off Ô (suc k) (Eb-id {T = Ô (suc k)}))))
           (≅→≼ (≅-sym (z-all (suc k))))))

open import OCF.Align.Value using (≺→s≼)

term₁-strict : suc (N.γ 2) ≼ z 1
term₁-strict =
  ≼-trans (≺→s≼ (Fstep (N.L 1)))
  (≼-trans (Ψ-emb (PW₃ (V1 (svs (SV-L 1)))))
  (≼-trans (Ψ-emb (PW₁ E₁))
           (≅→≼ (≅-sym (z-all 1)))))
  where
  a₀ = bkᴵ (N.L 1)
  e₀ : WO.Eb (ordᴰ a₀) (Ô 1)
  e₀ = V2 a₀ (sr (ysᶜ 0)) (St-bk (SV-L 1)) (St-sr 0)
         (≼-trans (≅→≼ (bk≅γ 1)) (≼-trans (term-≥ 0) (≅→≼ (≅-sym (tr₀-sr (ysᶜ 0))))))
  top : Ordᴰ
  top = B.suc B.zero +ᴰ Ô 1
  e₁ : WO.Eb (ordᴰ a₀) top
  e₁ = record
    { map = λ p → B.suc B.zero +ᴰ WO.map e₀ p
    ; below = λ p → B.+-mono (WO.below e₀ p)
    ; mono = λ p q r → B.+-mono (WO.mono e₀ p q r)
    ; coh = λ p q r → cong (B.suc B.zero +ᴰ_) (WO.coh e₀ p q r) }
  E₁ : WO.Eb (B.suc (ordᴰ a₀)) (η̂ 1)
  E₁ = WO.Eb-suc e₁ top (λ p → p) B.zero
```
