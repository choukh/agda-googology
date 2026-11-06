# ValC (五): 接口的实例, 嵌入再折回不降值, 闭项的第一条值定理

> 不含记号. 入口 [ValC](ValC.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 模块参数 `uipC` (`Cd` 上的 UIP) 是前提, 不是公设; 本篇的定理都是**条件定理 (条件: `Cd` 上的 UIP)**, 前提由函数外延推出 ([ValCUip](ValCUip.lagda.md) `fe→uipC`, 条件 Funext).
>
> - `valC⊥ᵖ`: 接口 [ValCIf](ValCIf.lagda.md) §3 的记录 `ValC⊥ᵖ` 的实例 (关系 `LeAt`, 值合法 `MoAt`).
> - `infl`: 嵌入一层再折回不降值, $x\le\Phi_{t+1\to t,b}(\mathrm{up}\,x)$ (不用 `uipC`).
> - `hsG`: $\Phi(x)+1\le\Phi(x+1)$.
> - **`grow`**: 可数层号上的闭项 `TC t` (第 $t+1$ 层的地板折到第 0 层) 逐站至少多一个后继: `TC t + 1 ≤ TC (t+1)`, 对一切合法 $t$; 经 `sound₀` 落到 `TLRuleSpec._≤_` (`growᴬ`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
module OCF.Lean.ValCTm (I : CRwIf) (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
open import OCF.Lean.ValCBase I
open import OCF.Lean.ValCMono I uipC
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
import OCF.Align.TLRuleSpec as TL
open import OCF.Lean.ValCIf I using (toA; ValC⊥ᵖ)
```

## §1 第 0 层: 推出标准前序

```agda
sound₀ : ∀ {x y} → LeAt hz x y → toA x TL.≤ toA y
sound₀ Rel.z≤ = TL.z≤
sound₀ (Rel.s≤s p) = TL.s≤ (sound₀ p)
sound₀ (Rel.≤s p) = TL.≤-suc (sound₀ p)
sound₀ (Rel.l≤l σ i h) = TL.l≤ (λ n → TL.≤l (σ n) (sound₀ (h n)))
sound₀ (Rel.≤l n p) = TL.≤l n (sound₀ p)
sound₀ (Rel.≤Ω {κ = ()} _ _ _ _)
sound₀ (Rel.Ω≤Ω {κ = ()} _ _)
```

## §2 接口的实例 (条件: `Cd` 上的 UIP)

```agda
valC⊥ᵖ : ValC⊥ᵖ
valC⊥ᵖ = record
  { Le = LeAt ; Mo = MoAt
  ; le-refl = λ t x → L.≤-refl t x
  ; le-trans = λ t → L.≤-trans t
  ; sound₀ = sound₀
  ; Mo-hz = λ t → tt
  ; Mo-top = λ t _ → Mo-top t
  ; one≤Φ = λ m lm t pt b x → one≤ (wf b⊥ m) lm t pt b x
  ; Mo-Φ = λ m lm t pt mb tb x mx → MoΦ (apWf m) (wf b⊥ m) lm pt mb tb x mx
  ; Φ-mono = λ m lm t pt {y = y} mb mb′ tb bb mx my p →
      monoΦ (apWf m) (wf b⊥ m) (wf b⊥ m) lm lm pt pt (mb , mb′ , tb , bb) y mx my p
  ; route = λ m lm j pj t qo pp {y = y} mb mb′ tb bb mx my p →
      route (apWf m) (s⊲→Pp pj) (wf b⊥ m) (wf b⊥ m) lm lm (wf b⊥ j) (lg↓ pj lm) (⊏⊑ pj)
        (⊲ᴮ-tr qo (⊏⊑ pj)) qo pp (mb , mb′ , tb , bb) y mx my p
  }
```

## §3 嵌入再折回不降值; 后继

第 $t+1$ 层里只有旧种类的高度 `up x` 折回第 $t$ 层: 旧种类 (层 $k$, $k+1\lhd t$) 对目标 $t$ 的决定只能是留 (`dv` 的另两种由没有真回路排除), $0\mapsto1$, 后继 $\mapsto\cdot\omega$, ℕ-极限 $\mapsto$ 部分和, 都不降.

```agda
mutual
  infl : ∀ {s} (a : Acc b⊥ (hs s)) (lm : LgB (hs s)) {b} x → LeAt s x (G a lm s (hsuc hself) b (up x))
  infl a lm hz = Rel.z≤
  infl {s} a lm {b} (hs x) =
    Rel.≤l 1 (L.≤-trans s (Rel.s≤s (infl a lm x)) (L.⊞-monoʳ s (G a lm s (hsuc hself) b (up x)) (one≤ a lm s (hsuc hself) b (up x))))
  infl {s} a lm (hl f) = Rel.l≤l (λ n → n) (L.idInc s) (λ n → L.≤-trans s (infl a lm (f n)) (Ac0.Σ-ge s _ n))
  infl {s} (acc rs) lm {b} (hΩ κ g) =
    ΦΩ {m = hs s} rs lm (hsuc hself) b (inj₁ κ) (λ c → up (g c)) (λ z → LeAt s (hΩ κ g) z)
      (iΩ rs lm g refl (toK s κ) (λ c → refl) (pK s κ) (dvK (inj₁ κ) (hsuc hself) lm))

  iΩ : ∀ {s} rs (lm : LgB (hs s)) {b} {κ} (g : E (T s) κ → H s) {k} (e : lvK s κ ≡ k)
       (to′ : H k → E (T s) κ) → (∀ c → to′ (subst H e c) ≡ toK s κ c) → hs k ⊲ s →
       ∀ {pk : hs k ⊲ hs s} {d} → DV k s to′ pk d →
       LeAt s (hΩ κ g) (caseDc d (Kc {m = hs s} rs lm {κ = inj₁ κ} (λ c → up (g c)) (hsuc hself) b)
                                  (Sc {m = hs s} rs lm {κ = inj₁ κ} (λ c → up (g c)) (hsuc hself) b)
                                  (Ac {m = hs s} rs lm {κ = inj₁ κ} (λ c → up (g c)) (hsuc hself) b))
  iΩ {s} rs lm {b} {κ} g e to′ eto u (dk κ₁ refl fr ft u′) =
    Rel.Ω≤Ω e (λ c _ → subst (λ z → LeAt s (g (toK s κ c)) (G (acc rs) lm s (hsuc hself) b (up (g z))))
      (sym (trans (cong to′ (ft (subst H e c))) (eto c)))
      (infl (acc rs) lm (g (toK s κ c))))
  iΩ rs lm g e to′ eto u ds = ⊥-elim (nos u)
  iΩ rs lm g e to′ eto u (da q pp) = ⊥-elim (nos′ u q)

hsG : ∀ {m} a lm t pt b y → LeAt t (hs (G {m} a lm t pt b y)) (G a lm t pt b (hs y))
hsG a lm t pt b y = Rel.≤l 1 (L.⊞-monoʳ t (G a lm t pt b y) (one≤ a lm t pt b y))
```

## §4 闭项: 地板逐站折到第 0 层, 逐站至少多一个后继

`TC t`: 第 $t+1$ 层的地板 $\Omega_t$ (`top b⊥ (hs t)`) 以界 $0$ 折到第 0 层. 这是 CRw 的同底折叠作用在 CRw 自己的地板上 (没有新定义); 读法同 TySup 的塔 (判断). `TC (t+1)` 的根是第 $t+1$ 层的 $\Omega$, 对目标 0 "在上", 按定义先坍缩到第 $t+1$ 层 (回灌链, 界 `top (hs t)`) 再折到 0. 证明: $\mathrm{TC}\,t+1\le\Phi(\Omega_t+1)$ (`hsG`), 再由 `monoΦ` 与 "$\Omega_t+1$ 不超过回灌链" (链第 0 点 $\ge\Omega_t$ 由 `infl`, 第 1 点再加 $\ge1$).

```agda
TC : ∀ t → LgB t → Cd
TC t lgt = G (wf b⊥ (hs t)) lgt hz (z⊲ᴮ (hs t)) hz (top b⊥ (hs t))

grow : ∀ t (lgt : LgB t) → LeAt hz (hs (TC t lgt)) (TC (hs t) lgt)
grow t lgt =
  L.≤-trans hz (hsG (wf b⊥ (hs t)) lgt hz (z⊲ᴮ (hs t)) hz (top b⊥ (hs t)))
    (monoΦ (apWf (hs t)) (wf b⊥ (hs t)) (wf b⊥ (hs t)) lgt lgt (z⊲ᴮ (hs t)) (z⊲ᴮ (hs t))
       (tt , tt , Rel.z≤ , Rel.z≤) (hl (chain (top b⊥ (hs t)) Kg)) (Mo-top (hs t))
       (Ac0.chM (hs t) (top b⊥ (hs t)) Kg (Mo-top (hs t)) (L.≤-refl (hs t) _)
          (λ b′ mb tb → MoΦ (apWf (hs (hs t))) (wf b⊥ (hs (hs t))) lgt (hsuc hself) mb tb (up b′) (Mo-up b′ mb)))
       (Rel.≤l 1 (L.≤-trans (hs t) (Rel.s≤s (infl (wf b⊥ (hs (hs t))) lgt (top b⊥ (hs t))))
          (L.⊞-monoʳ (hs t) (Kg (top b⊥ (hs t))) (one≤ (wf b⊥ (hs (hs t))) lgt (hs t) (hsuc hself) (top b⊥ (hs t) ⊞ Kg (top b⊥ (hs t))) (up (top b⊥ (hs t) ⊞ Kg (top b⊥ (hs t)))))))))
  where
  Kg : H (hs t) → H (hs t)
  Kg b′ = G (wf b⊥ (hs (hs t))) lgt (hs t) (hsuc hself) b′ (up b′)

growᴬ : ∀ t (lgt : LgB t) → asuc (toA (TC t lgt)) TL.≤ toA (TC (hs t) lgt)
growᴬ t lgt = sound₀ (grow t lgt)
```

## 结论 (按档)

- **[条件定理, 条件 `Cd` 上的 UIP]** `valC⊥ᵖ : ValC⊥ᵖ` (接口 §3 的实例); `grow` (闭项 `TC` 逐站至少多一个后继, 对一切合法 $t$), `growᴬ` (落到 `TLRuleSpec._≤_`).
- **[定理, 无条件]** `sound₀` (第 0 层推出标准前序); `infl`, `iΩ` (只用 `one≤`, 不用 `monoΦ`); `hsG`.
- **[判断]** `TC t` 的读法 (TySup 塔的 $\psi_0(\Omega_t)$ 一类); `grow` 只说 "多一个后继", 不是两站之间的定量差.
