# 终局 (二): 低端实例, 接口在 $\psi_0(\Omega_\Omega)$ 上完全居留

> 不含记号. 结论写在 [EBOTop](EBOTop.lagda.md). 这是 `Stage` 的一个**无条件的闭实例** `inst`: 世界是 [Level](Level.lagda.md) 的 `Ordᴵ`/`Ordᶜ`, 回灌是 "折叠到第 0 层再读成层号", 证书的内容是 [Uniform](Uniform.lagda.md) 的 `Uniform`. 通用的 `Top` 在它上面给出的闭项就是 [Diagonal](Diagonal.lagda.md) 的 `BTBOᴵ` (`≅⁰`, `EBOᵀ≅BTBO`, 在 [EBOTopAccept](EBOTopAccept.lagda.md)), 其标签 $\psi_0(\Omega_\Omega)$ 是 [Label](Label.lagda.md) 的定理. 不动点是 $\psi_0(\Omega_x)\simeq x$ (`Low-fix`, 编译过的定理, 此前只是估计).
>
> 这个实例的用处: 接口不空, 全部字段可以同时成立而不用 LPO; `no-WLPO`: 如果 `Stage → WLPO` 可证, WLPO 就可证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EBOTopLow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level hiding (back-≅)
open import OCF.Align.Uniform using (Uniform)
open import OCF.Align.InaccSingularBase using (WLPO)
import OCF.Align.EBOTopStage as St
open St using (O₀; Stage; module Top; _≅⁰_; _≺⁰_)
```

## §1 第 0 层的读出

`Ordᶜ zero` 与 `O₀` 差两个没有居民的构造子. `HS` 的翻译要一个反向的 `back`, 因为 Level 的 $\sqsubseteq^0$ 对一切层的前驱量化.

```agda
rd : Ordᶜ zero → O₀
rd zero        = O₀.zero
rd (suc a)     = O₀.suc (rd a)
rd (lim f)     = O₀.lim (λ n → rd (f n))
rd (limᵢ () f)
rd (up () x)

back : O₀ → Ordᶜ zero
back O₀.zero    = zero
back (O₀.suc a) = suc (back a)
back (O₀.lim f) = lim (λ n → back (f n))

rd-back : ∀ c → rd (back c) ≅⁰ c
rd-back O₀.zero    = St.z≅
rd-back (O₀.suc a) = St.s≅ (rd-back a)
rd-back (O₀.lim f) = St.l≅ (λ n → rd-back (f n))

rd-≅ : ∀ {a b : Ordᶜ zero} → a ≅ b → rd a ≅⁰ rd b
rd-≅ z≅     = St.z≅
rd-≅ (s≅ e) = St.s≅ (rd-≅ e)
rd-≅ (l≅ h) = St.l≅ (λ n → rd-≅ (h n))
rd-≅ (lᵢ≅ {p = ()} e h)
rd-≅ (upˡ {r = ()} e)
rd-≅ (upʳ {r = ()} e)

back-≅ : ∀ {c} {a : Ordᶜ zero} → c ≅⁰ rd a → back c ≅ a
back-≅ {a = zero}      St.z≅     = z≅
back-≅ {a = suc a}     (St.s≅ e) = s≅ (back-≅ e)
back-≅ {a = lim f}     (St.l≅ h) = l≅ (λ n → back-≅ (h n))
back-≅ {a = limᵢ () f} e
back-≅ {a = up () x}   e

rd-≺ : ∀ {c a : Ordᶜ zero} → c ≺ a → rd c ≺⁰ rd a
rd-≺ (≺z e)   = St.≺z (rd-≅ e)
rd-≺ (≺s h)   = St.≺s (rd-≺ h)
rd-≺ (≺l n h) = St.≺l n (rd-≺ h)
rd-≺ (≺i {p = ()} x ex h)
rd-≺ (≺u {r = ()} h)

back-≺ : ∀ {c} {a : Ordᶜ zero} → c ≺⁰ rd a → back c ≺ a
back-≺ {a = zero}      ()
back-≺ {a = suc a}     (St.≺z e)   = ≺z (back-≅ e)
back-≺ {a = suc a}     (St.≺s h)   = ≺s (back-≺ h)
back-≺ {a = lim f}     (St.≺l n h) = ≺l n (back-≺ h)
back-≺ {a = limᵢ () f} h
back-≺ {a = up () x}   h

rd-⊑ : ∀ {a b} → a ⊑⁰ b → rd a St.⊑⁰ rd b
rd-⊑ k {c} h = St.≺⁰-respˡ (rd-back c) (rd-≺ (k (back-≺ h)))

rd-HS : ∀ {x} → HS x → St.HS (rd x)
rd-HS hz        = St.hz
rd-HS (hs h)    = St.hs (rd-HS h)
rd-HS (hl h st) = St.hl (λ n → rd-HS (h n)) (λ n → rd-⊑ (st n))
```

## §2 实例

好层号是 "$\ell\sqsubseteq^\mathsf I$ 它的下一项". [Diagonal](Diagonal.lagda.md) 的 §5 第 3 条说种子一步缺一个一般的证明; 这里不要它: 好的谓词本身就是种子一步, 闭包是 `Ψ⁰-mono`, 起点是 `diag-step zero`.

```agda
≅→⊑ᴸ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅→⊑ᴸ z≅     = z⊑
≅→⊑ᴸ (s≅ e) = s⊑ e zero
≅→⊑ᴸ (l≅ h) = l⊑ (λ n → ⊑ᴵ-trans (≅→⊑ᴸ (h n)) (Sim→⊑ᴵ (λ q → lim n q)))

module Low (Uni : ∀ a → HS (ψ⁰ (Ω a))) where
  nx : Ordᴵ → Ordᴵ
  nx ℓ = toLevel (ψ⁰ (Ω ℓ)) (Uni ℓ)

  GoodLᴸ : Ordᴵ → Set
  GoodLᴸ ℓ = ℓ ⊑ᴵ nx ℓ

  GoodTᴸ : ∀ {ℓ} → Ordᶜ ℓ → Set
  GoodTᴸ t = Σ (HS (ψ⁰ t)) λ h → GoodLᴸ (toLevel (ψ⁰ t) h)

  clo : ∀ {ℓ} → GoodLᴸ ℓ → GoodLᴸ (nx ℓ)
  clo {ℓ} g = toLevel-⊑ (Uni ℓ) (Uni (nx ℓ)) (Ψ⁰-mono g)

  seed-step : suc zero ⊑⁰ ψ⁰ (Ω (suc zero))
  seed-step (≺z e) = ≺-respˡ (≅-sym e) (z≺ψ⁰ (Ω (suc zero)))

  seed-good : GoodLᴸ (suc zero)
  seed-good = toLevel-⊑ (hs hz) (Uni (suc zero)) seed-step

  nextᴸ : Σ Ordᴵ GoodLᴸ → Σ Ordᴵ GoodLᴸ
  nextᴸ p = nx (proj₁ p) , clo (proj₂ p)

  Towᴸ : ℕ → Σ Ordᴵ GoodLᴸ
  Towᴸ = St.tow (suc zero , seed-good) nextᴸ

  Lᴸ : ℕ → Ordᴵ
  Lᴸ n = proj₁ (Towᴸ n)

  Gᴸ : ∀ n → GoodLᴸ (Lᴸ n)
  Gᴸ n = proj₂ (Towᴸ n)

  Λᴸ : Ordᴵ
  Λᴸ = lim Lᴸ Gᴸ

  good-Λᴸ : GoodLᴸ Λᴸ
  good-Λᴸ = l⊑ λ n → ⊑ᴵ-trans (Gᴸ n)
    (⊑ᴵ-trans (≅→⊑ᴸ (toLevel-≅ (Uni (Lᴸ n)) (hl₁ (Uni Λᴸ) n) (≅-refl⁰ _))) (Sim→⊑ᴵ (λ q → lim n q)))

  Ω-Λᴸ : ∀ b → (∀ n → Lᴸ (suc n) ⊑ᴵ b) → nx Λᴸ ⊑ᴵ b
  Ω-Λᴸ b H = l⊑ λ n → ⊑ᴵ-trans (≅→⊑ᴸ (toLevel-≅ (hl₁ (Uni Λᴸ) n) (Uni (Lᴸ n)) (≅-refl⁰ _))) (H n)

  inst : Stage
  inst = record
    { Lv = Ordᴵ ; Tr = Ordᶜ ; base = zero ; out = rd ; Ω = Ω ; ψ₀ = ψ⁰
    ; GoodL = GoodLᴸ ; GoodT = GoodTᴸ
    ; seed = suc zero ; good-seed = seed-good
    ; good-Ω = λ {ℓ} g → Uni ℓ , clo g
    ; cert = λ g → rd-HS (proj₁ g)
    ; feed = λ t g → toLevel (ψ⁰ t) (proj₁ g)
    ; good-feed = λ t g → proj₂ g
    ; _⊑_ = _⊑ᴵ_
    ; infl = λ g → g
    ; lub = lim
    ; ub = λ f s n → Sim→⊑ᴵ (λ q → lim n q)
    ; lub-Ω = λ f s → refl
    ; good-Λ = good-Λᴸ
    ; Ω-Λ = Ω-Λᴸ
    }
```

## §3 闭项, 证书, 不动点

通用的 `Top` 给出闭项与证书. 它就是 [Diagonal](Diagonal.lagda.md) 的 `BTBOᴵ` (`≅⁰`, 比较写在 [EBOTopAccept](EBOTopAccept.lagda.md), 因为 Diagonal 的模块含记号样例).

```agda
  Low-HS : St.HS (Top.EBOᵀ inst)
  Low-HS = Top.EBO-HS inst

  -- $\psi_0(\Omega_{\Lambda})\simeq\Lambda$: 这个世界的不动点是 $x\mapsto\psi_0(\Omega_x)$ 的不动点
  Low-fix : (nx Λᴸ ⊑ᴵ Λᴸ) × (Λᴸ ⊑ᴵ nx Λᴸ)
  Low-fix = Top.fixpoint inst

-- 闭实例, 无条件
instᶜ : Stage
instᶜ = Low.inst Uniform

no-WLPO : (Stage → WLPO) → WLPO
no-WLPO f = f instᶜ

-- 闭项上的 FGH
lowBig : ℕ
lowBig = St.FGH (Top.EBOᵀ instᶜ) 99

_ : St.FGH (Top.EBOᵀ instᶜ) 0 ≡ 1
_ = refl

_ : St.FGH (Top.EBOᵀ instᶜ) 1 ≡ 2
_ = refl
```

## §4 退化实例: 接口不管强度

`triv` 也是 `Stage`: 层是第 0 层的树, $\Omega$ 与折叠都是恒等, 回灌是恒等, 塔是常值 0, 闭项是 $\lim[0,0,\dots]$. 所以**居留不等于强**. `Stage` 只说闭项与证书的结构; 折叠确实是 OCF, 要看实例 (低端实例由 [Label](Label.lagda.md), 真正的塔由 [EBOTopRaw](EBOTopRaw.lagda.md) 的折叠 `PF S` 与验收), 外部规格见 [OCFSpec](OCFSpecBase.lagda.md).

```agda
triv : Stage
triv = record
  { Lv = O₀ ; Tr = λ _ → O₀ ; base = O₀.zero ; out = λ t → t ; Ω = λ ℓ → ℓ ; ψ₀ = λ t → t
  ; GoodL = St.HS ; GoodT = St.HS
  ; seed = O₀.zero ; good-seed = St.hz
  ; good-Ω = λ g → g ; cert = λ g → g
  ; feed = λ t _ → t ; good-feed = λ t g → g
  ; _⊑_ = λ _ _ → ⊤
  ; infl = λ _ → tt
  ; lub = λ f _ → O₀.lim f
  ; ub = λ _ _ _ → tt
  ; lub-Ω = λ f s → refl
  ; good-Λ = St.hl (λ n → proj₂ (twr n)) (λ n h → h)
  ; Ω-Λ = λ _ _ → tt
  } where
  twr : ℕ → Σ O₀ St.HS
  twr = St.tow (O₀.zero , St.hz) (λ p → p)

triv-small : ∀ n → St.FGH (Top.EBOᵀ triv) n ≡ suc n
triv-small n = go n n where
  twr₀ : ℕ → O₀
  twr₀ n = Stage.L triv n
  go : ∀ m n → St.FGH (twr₀ m) n ≡ suc n
  go zero    n = refl
  go (suc m) n = go m n
```
