# 有限坐标层的Reg与相对合法族

直接取原M.F n。RegWorld记录低阶界的Reg，避免在rank≥2偷取任意raw
坐标证书；第0层RegWorld为真，所以最终位置定理仍覆盖全部P-world。
Legal与Reg分开，中间Legal不预设推出raw LgB，最终Legal0就是原LgB。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteRegIf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
import OCF.Align.BoundedFoldValueMixed as M

F : ℕ → KS
F = M.F
one : ∀ n → HB (F n)
one n = hs hz

Reg : ∀ n → HB (F n) → Set
RegWorld : ∀ n → Wd (F n) → Set
RegCoord : ∀ n κ → E (F n) κ → Set
Seed : ∀ n {D : KS} → (Wd (F n) → Wd D) → (κ : K (F n)) → (E (F n) κ → HB D) → Set

Reg zero a = ⊤
Reg (suc n) hz = ⊤
Reg (suc n) (hs a) = Reg (suc n) a
Reg (suc n) (hl f) = ∀ j → Reg (suc n) (f j)
Reg (suc n) (hΩ κ g) = Seed (suc n) (λ W → W) κ g ×
  (∀ c → RegCoord (suc n) κ c → Reg (suc n) (g c))
RegWorld zero W = ⊤
RegWorld (suc n) W = RegWorld n (proj₁ W) × Reg n (proj₂ W)
RegCoord zero κ c = ⊤
RegCoord (suc n) (inj₁ κ) c = RegCoord n κ c
RegCoord (suc n) (inj₂ _) c = Reg n c
Seed zero ext κ g = ⊤
Seed (suc n) ext (inj₁ κ) g = Seed n (λ W → ext (W , one n)) κ g
Seed (suc n) ext (inj₂ _) g = ∀ {W c d} → RegWorld n W →
  c ⊲[ W ] one n → d ⊲[ W ] one n → c ⊲[ W ] d →
  g c ⊲[ ext (W , one n) ] g d

Legal : ∀ n → HB (F n) → Set
LegalWorld : ∀ n → Wd (F n) → Set
LegalCoord : ∀ n κ → E (F n) κ → Set
Good : ∀ n → HB (F n) → Set
Good n a = Reg n a × Legal n a

Legal zero a = LgB a
Legal (suc n) hz = ⊤
Legal (suc n) (hs a) = Legal (suc n) a
Legal (suc n) (hl f) =
  (∀ {W} → RegWorld (suc n) W → ∀ j → f j ⊲[ W ] f (suc j)) ×
  (∀ j → Legal (suc n) (f j))
Legal (suc n) (hΩ κ g) =
  (∀ {W c d} → LegalWorld (suc n) W → Bd (F (suc n)) κ c W →
    Bd (F (suc n)) κ d W → Pr (F (suc n)) κ W c d → g c ⊲[ W ] g d) ×
  (∀ c → LegalCoord (suc n) κ c → Legal (suc n) (g c))
LegalWorld zero W = LgW (F zero) W
LegalWorld (suc n) W = LegalWorld n (proj₁ W) × Good n (proj₂ W)
LegalCoord zero κ c = Σ (Wd (F zero)) (λ W → LgW (F zero) W × Bd (F zero) κ c W)
LegalCoord (suc n) (inj₁ κ) c = LegalCoord n κ c
LegalCoord (suc n) (inj₂ _) c = Good n c
```

Seed每次比较的两个坐标均在同一字面one下；其下层world也明确带RegWorld。
Reg的全部raw分支仅在底P种类出现。接口是否有实际非零生成族，由后续
Closure给原flL有限分量实例；定义本身不当作该实例或fold保持定理。
