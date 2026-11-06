# ValX (七): 根上的同坐标比较 (P1); `TX + 1 ≤ TU 1` 只差 $k_R$ 对坐标单调

> 不含记号. 入口 [ValX](ValX.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 实例 `I₁`. §1 不用 UIP; §2, §3 以 `Cd` 上的 UIP 为模块参数 (条件, 经 `ValXMono.monoX`).
>
> - `MoX-gt`: 地板的每个分支 `gt C` 值合法 (对一切可数树 $C$). 要 [ValXRel](ValXRel.lagda.md) 的 `Ω≤Ω` 允许同分量同层的不同种类: 分支 $d\mapsto\iota_c(\mathrm{up}\,d)$ 把第 $c$ 层的值关系 (ValC 的, 按层比较) 搬上来 (`ιX-mono`).
> - `U b x` $=\Phi_{\Omega_1\oplus1\to\Omega_1,b}(\mathrm{up}\,x)$ (嵌入一层再折回): 输出不低于 1, 不降 (`U-infl`), 单调 (`U-mono`), 保值合法 (`MoX-U`).
> - **`P1`** (条件: UIP): 对第 0 层的一切 $b$, $k_L\,b\le k_R\,b$ ([ValXGoal](ValXGoal.lagda.md) 的两族根分支在同一坐标处).
> - **`goal-P2`** (条件: UIP): 若 `P2` ($k_R$ 对坐标值单调: $b_1\le b_2\Rightarrow k_R\,b_1\le k_R\,b_2$), 则 $\mathrm{TX}+1\le\mathrm{TU}\,1$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
module OCF.Lean.ValXP1 (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; W₀; TX; TU1; PH-topL)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁
open import OCF.Lean.ValXRel I₁
open import OCF.Lean.ValXTm using (shLaw₁)
open import OCF.Lean.ValXBase I₁ shLaw₁
open import OCF.Lean.ValXMono I₁ uipC shLaw₁ using (monoX)
open import OCF.Lean.ValXGoal using (κΩ; g₀; nd₀; kL; kR; Hyp; goal-ifᴬ)
open import OCF.Lean.ValCIf I₁ using (toA)
open import OCF.Align.CumReadCF using (asuc)
import OCF.Align.TLRuleSpec as TL
```

## §1 地板的分支值合法; 嵌入再折回 (不用 UIP)

```agda
ιc : ∀ c → HB (Tw S⊥ (hs c)) → HX
ιc c = ι {Cd} {λ c → Tw S⊥ (hs c)} c

ιX-mono : ∀ c {a b} → LeAt (hs c) a b → ιc c a ≤X ιc c b
ιX-mono c Rel.z≤ = z≤
ιX-mono c (Rel.s≤s p) = s≤s (ιX-mono c p)
ιX-mono c (Rel.≤s p) = ≤s (ιX-mono c p)
ιX-mono c (Rel.l≤l σ i h) = l≤l σ i (λ n → ιX-mono c (h n))
ιX-mono c (Rel.≤l n p) = ≤l n (ιX-mono c p)
ιX-mono c (Rel.≤Ω {κ = κ} d bd mc p) = ≤Ω d (lle→ (hs c) κ d _ bd) (lmo→ (hs c) κ d mc) (ιX-mono c p)
ιX-mono c (Rel.Ω≤Ω {κ = κ} e h) = Ω≤Ω e (λ d md → ιX-mono c (h d (→lmo (hs c) κ d md)))

MoX-ι : ∀ c a → MoAt (hs c) a → MoX (ιc c a)
MoX-ι c hz m = tt
MoX-ι c (hs a) m = MoX-ι c a m
MoX-ι c (hl f) m = λ n → MoX-ι c (f n) (m n)
MoX-ι c (hΩ κ g) (mo , mh) =
  (λ d d′ md md′ le → ιX-mono c (mo d d′ (→lmo (hs c) κ d md) (→lmo (hs c) κ d′ md′) (→lle (hs c) κ d d′ le))) ,
  (λ d md → MoX-ι c (g (toK (hs c) κ d)) (mh d (→lmo (hs c) κ d md)))

MoX-gt : ∀ C → MoX (gt C)
MoX-gt hz = tt
MoX-gt (hs c) = MoX-⊞ (gt c) (ιc c (topT S⊥ hz (hs c))) (MoX-gt c) (MoX-ι c (topT S⊥ hz (hs c)) (Mo-top (hs c)))
MoX-gt (hl f) = λ n → MoX-gt (f n)
MoX-gt (hΩ () _)

U : HX → HX → HX
U b x = Φ bX (hs hz) (wf bX (hs hz)) tt bX hz (sm (hsuc hself)) b (up x) tt

U-one : ∀ b x → hs hz ≤X U b x
U-one b hz = s≤s z≤
U-one b (hs x) = ≤l 0 (U-one b x)
U-one b (hl f) = ≤l 0 (U-one b (f 0))
U-one b (hΩ (c , κ) g) = ≤Ω hz Rel.z≤ tt (U-one b (g (toK (hs c) κ hz)))

U-infl : ∀ b x → x ≤X U b x
U-infl b hz = z≤
U-infl b (hs x) = ≤l 1 (≤X-trans (s≤s (U-infl b x)) (⊞X-monoʳ (U b x) (U-one b x)))
U-infl b (hl f) = l≤l (λ n → n) idInc (λ n → ≤X-trans (U-infl b (f n)) (ΣX-ge (λ k → U b (f k)) n))
U-infl b (hΩ (c , κ) g) = Ω≤Ω refl (λ d _ → U-infl b (g (toK (hs c) κ d)))

U-mono : ∀ b {x y} → x ≤X y → U b x ≤X U b y
U-mono b {y = y} z≤ = U-one b y
U-mono b (s≤s p) = l≤l (λ n → n) idInc (mulX-mono (U-mono b p))
U-mono b (≤s p) = ≤l 0 (U-mono b p)
U-mono b (l≤l σ i h) = l≤l σ i (ΣX-sub _ _ σ i (λ n → U-mono b (h n)))
U-mono b {y = hl g} (≤l n p) = ≤l n (≤X-trans (U-mono b p) (ΣX-ge (λ k → U b (g k)) n))
U-mono b (≤Ω c bd mc p) = ≤Ω c bd mc (U-mono b p)
U-mono b (Ω≤Ω e h) = Ω≤Ω e (λ d md → U-mono b (h d md))

MoX-U : ∀ b x → MoX x → MoX (U b x)
MoX-U b hz m = tt
MoX-U b (hs x) m = MoX-mul (U b x) (MoX-U b x m)
MoX-U b (hl f) m = MoX-Σ (λ k → U b (f k)) (λ k → MoX-U b (f k) (m k))
MoX-U b (hΩ (c , κ) g) (mo , mh) =
  (λ d d′ md md′ le → U-mono b (mo d d′ md md′ le)) , (λ d md → MoX-U b (g (toK (hs c) κ d)) (mh d md))

g₀≡ : ∀ c → g₀ c ≡ U topL (gt c)
g₀≡ c = refl
```

## §2 同坐标比较 (P1, 条件: UIP)

```agda
pgL : PGt W₀ κΩ gt
pgL = proj₂ (PH-topL W₀ hself)

P1 : ∀ b → LeAt hz (kL b) (kR b)
P1 b = monoX (wf bX hz) (wf bX hz) {nWE κΩ tt (toX κΩ b)} {nWE κΩ tt (toX κΩ b)} (lgE κΩ tt (toX κΩ b)) (lgE κΩ tt (toX κΩ b)) (L.≤-refl hz _)
         (ptE κΩ tt (z⊲ᴮ W₀) (toX κΩ b)) (ptE κΩ tt (z⊲ᴮ W₀) (toX κΩ b)) (Ac0.bnd-refl hz (moZ b) Rel.z≤)
         (g₀ C) (pgE κΩ tt pgL (toX κΩ b)) (pgE κΩ tt (proj₂ nd₀) (toX κΩ b))
         (MoX-gt C) (MoX-U topL (gt C) (MoX-gt C)) (U-infl topL (gt C))
  where C = psh (P κΩ) W₀ (toX κΩ b)
```

## §3 归约到 P2

```agda
P2 : Set
P2 = ∀ b₁ b₂ → LeAt hz b₁ b₂ → LeAt hz (kR b₁) (kR b₂)

hyp : P2 → Hyp
hyp p2 b₁ b₂ le = L.≤-trans hz (P1 b₁) (p2 b₁ b₂ le)

goal-P2 : P2 → asuc (toA TX) TL.≤ toA TU1
goal-P2 p2 = goal-ifᴬ (hyp p2)
```

## 结论 (按档)

- **[定理, 不用 UIP]** `ιX-mono`, `MoX-ι`, **`MoX-gt`** (地板的每个分支值合法); `U-one`, **`U-infl`**, `U-mono`, `MoX-U`; `g₀≡`.
- **[条件定理, 条件: `Cd` 上的 UIP]** **`P1`**: $k_L\,b\le k_R\,b$ (一切 $b$); **`goal-P2`**: `P2` ⟹ $\mathrm{TX}+1\le\mathrm{TU}\,1$.
- **[判断]** `P2` 是第 0 层输出之间的陈述 (未证, 未否定). 经 $\Omega_1$ 层的值合法去证它, 要 `gt` 对坐标值单调, 被 `ValXObs.floor-block` 挡住.
