# 两种种类的 Ω-极限一步 (四): 回灌第 0 格的第一个节点, `s-hΩ`

> 入口 [TpPort2](TpPort2.lagda.md). 不含记号. 手写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 不改树、折叠、合法性.
>
> 照 `MonoPort8Om`. 输入 $h=\mathrm{h\Omega}\,\kappa\,g$, 实例 $\Lambda=1\boxplus h=\mathrm{h\Omega}\,\kappa\,(c\mapsto 1\boxplus g\,c)$. 闭项 $T^+(h)$ 的第 0 层读数是 `Stp` 的一段接回灌的极限 $\lim_n\mathrm{drp}(\Delta_n)$ (`TH≡`, `TA≡`: `refl`). 第 0 格在一个具体的世界 $U$ 里走, 它的第一个节点在最小坐标上, 层 $1\boxplus g(\mathrm{bot})$:
>
> - **新种类 `κH`** (`OmH`): 回灌一格的世界是 $(1, v_1)$, $v_1=\mathrm{rd}(0, z_1\,Y)$; $z_1\,Y = 0⨾\omega\cdot(\Omega_1⨾0)$ 与 $g$ 无关, 读回是 $\mathrm{hl}\,(\mathrm{rdp}\ldots)$, 路径定义地是 `hlim 0 hself`. 第 0 段之后的第 1 段从 $f(0)=0$ 走到 $f(1)=\mathrm{h\Omega}\,\kappa_A\,(\mathrm{nbA}\,1\ldots)$, 路径定义地是 `hLim (C.suc C.self) (hsuc hself)`: 先走到 $\mathrm{nbA}\ldots 0 = 1$, 它的后继一步就是坐标 $0$ 上的节点. 路上的 `hLim` 段 (旧种类的闭包 `KG`) 在节点之后, 不必展开.
> - **旧种类 `κA`** (`OmA`): 回灌一格的世界是 $(V_0, 0)$, $V_0=\mathrm{sum}\,1\,(z\,Y)=\lim(\mathrm{pt}\,1\ldots)$, 路径 `C.lim 0 (C.suc C.self)`, 第一个节点在坐标 $0$ (同 `MonoPort8Om`).
>
> 节点之后用 [TpPort2One](TpPort2One.lagda.md) 的 `Node.low`. 结论 **`sΩ`**: 一切种类 $\kappa$, 一切合法 $\mathrm{h\Omega}\,\kappa\,g$, 只要最小坐标上的分支 $g(\mathrm{bot})$ 不含 Ω-极限, 就有 $T^+(g(\mathrm{bot}))<T^+(\mathrm{h\Omega}\,\kappa\,g)$. 这是 `TpMonoIf.Steps.s-hΩ` 在 `Free (g bot)` 上的实例 (`s-hΩF`). 特例 (无前提): **`T0<Ω₂`** $T^+(0)<T^+(\Omega_2)$, `T0<Ω₂²` $T^+(0)<T^+(\Omega_2^2)$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPort2Om where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; LgB; _⊞_; Lg-⊞; ⊞-fst; E; LgE; bot)
open import OCF.Align.HtTowerFTree using (S₁; H₀; κA; κH; Ht; Wd₂; LgW₂; D; D₀; sL; accᴸ; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; drp; sum; pt; ≤rf)
  renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerFClosed using (module At; T⁺; top⁺; one; W₁; Ω₂ᴴ; lΩ₂; T-Ω₂; Ω₂²; Lg-Ω₂²; T-Ω₂²)
open import OCF.Align.HtTowerFGrow using (sum≥)
open import OCF.Align.TpPortSim using (Free)
open import OCF.Align.TpPortStep using (free-top)
open import OCF.Align.TpPort2One using (here; left; module One)
```

## §1 `drp` 不降和

```agda
drp≤ : ∀ {W W′} {b b′} → b ≤ b′ → (x : D₀ W) → sum b x ≤ sum b′ (drp {W} {W′} x)
pdrp : ∀ {W W′} {b b′} → b ≤ b′ → (d : ℕ → D₀ W) → ∀ n → pt b d n ≤ pt b′ (λ m → drp {W} {W′} (d m)) n
drp≤ h n0 = h
drp≤ h n1 = s≤ h
drp≤ h (x ⨾ y) = drp≤ (drp≤ h x) y
drp≤ h (nl d) = l≤ (λ n → ≤l n (pdrp h d n))
drp≤ h (ni () u)
drp≤ h (nκ () u)
drp≤ h (nμ () u)
drp≤ h (nw p x) = drp≤ h x
pdrp h d zero = h
pdrp h d (suc n) = drp≤ (pdrp h d n) (d n)

lW₁ : LgW₂ W₁
lW₁ = tt , tt

q₀₁ : (azero , hz) ≤ʷ W₁
q₀₁ = z⊲ one , hself

-- 读数的两个投影 (只用来写出被比较的那一段, 不进定义)
rgt : ∀ {W} → D₀ W → D₀ W
rgt (x ⨾ y) = y
rgt _ = n0

nth : ∀ {W} → ℕ → D₀ W → D₀ W
nth m (nl d) = d m
nth m _ = n0
```

## §2 新种类 `κH`

```agda
module OmH (g : H₀ → Ht) (lg : LgB (hΩ κH g)) where
  h : Ht
  h = hΩ κH g

  g′ : H₀ → Ht
  g′ c = hs hz ⊞ g c

  Λ : Ht
  Λ = top⁺ h

  l : LgB Λ
  l = Lg-⊞ (hs hz) h tt lg

  o : ∀ {w} → hs hz ⊲[ w ] Λ
  o = ⊞-fst (hs hz) h

  module P = At Λ l o

  u : ∀ {W′} → (azero , hz) ≤ʷ W′ → LgW₂ W′ → D Λ W′
  u {W′} _ _ = ni (sL {κ = κH} {c = proj₂ W′} hself hself) (λ _ _ _ → n1)

  w′ : D Λ W₁
  w′ = n0 ⨾ nw q₀₁ n1

  Y′ : P.St W₁
  Y′ = P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀)

  κ₁ : ℕ → P.Cl₁ W₁ (azero , hz) Λ
  κ₁ = P.κc₁ accᴸ tt u q₀₁ lW₁ hself P.Act w′ Y′

  Δ : ∀ n → P.Df (one , P.v₁ (κ₁ n))
  Δ n = P.κΔ₁ accᴸ tt u q₀₁ lW₁ hself P.Act (κ₁ n)

  Dn : ℕ → D₀ W₁
  Dn n = drp (P.yc (Δ n) (P.τ₀ (tt , P.lv₁ (κ₁ n))))

  b : A
  b = sum one (P.yc (P.Stp (P.Y₀ {W₁})) (P.τ₀ lW₁))

  TH≡ : T⁺ h lg ≡ alim (pt b Dn)
  TH≡ = refl

  -- 第 0 格: 世界 U = (1, v₁)
  c₀ : P.Cl₁ W₁ (azero , hz) Λ
  c₀ = κ₁ 0

  U : Wd₂
  U = one , P.v₁ c₀

  lU : LgW₂ U
  lU = tt , P.lv₁ c₀

  X₁ : W₁ ≤ʷ U
  X₁ = C.self , P.wv₁ c₀

  open One (inj₂ tt) g′ l o U lU X₁ using (module Node; τ; gZ₀; g⊕0; pZ₀; pfx⊕)

  -- 第一个节点: 第 1 段 (从 f 0 = 0 到 f 1) 里, 坐标 0, 层 1 ⊞ g 0
  qN : (one , hz) ≤ʷ U
  qN = C.self , hlim 1 (hLim (C.suc C.self) (hsuc hself))

  wN : D Λ U
  wN = (P.co₁ c₀ ⨾ n0) ⨾ n0

  YN : P.St U
  YN = P._⊕⟨_⟩_ (P._⊕⟨_⟩_ (P.Sv₁ c₀) lU P.zeroD) lU P.zeroD

  gN = g⊕0 {P._⊕⟨_⟩_ (P.Sv₁ c₀) lU P.zeroD} (g⊕0 {P.Sv₁ c₀} gZ₀)

  module Fz (fz : Free (g hz)) where
    module Nd = Node {c = hz} hself (free-top (g hz) fz) qN wN YN gN

    -- 节点的和不高于第 0 格的和: 读数 = 0 ⨾ nl (第 m 段), 第 0 段 = (0 ⨾ 节点) ⨾ 闭包
    node≤cell : sum b (P.yc Nd.N τ) ≤ sum b (P.yc (Δ 0) τ)
    node≤cell = ≤l 1 (sum≥ (sum b (P.yc Nd.N τ)) (rgt (nth 0 (rgt (P.yc (Δ 0) τ)))))

    cell≤T : sum b (P.yc (Δ 0) τ) ≤ T⁺ h lg
    cell≤T = ≤-trans (drp≤ (≤-refl b) (P.yc (Δ 0) τ)) (≤l 1 (≤-refl _))

    grow : ∀ (lz : LgB (g hz)) → asuc (T⁺ (g hz) lz) ≤ T⁺ h lg
    grow lz = ≤-trans (Nd.low (pfx⊕ {P._⊕⟨_⟩_ (P.Sv₁ c₀) lU P.zeroD} P.zeroD (pfx⊕ {P.Sv₁ c₀} P.zeroD pZ₀)) b
                               (sum≥ one (P.yc (P.Stp (P.Y₀ {W₁})) (P.τ₀ lW₁))) (Lg-⊞ (hs hz) (g hz) tt lz) (⊞-fst (hs hz) (g hz)))
                      (≤-trans node≤cell cell≤T)
```

## §3 旧种类 `κA`

```agda
module OmA (g : A → Ht) (lg : LgB (hΩ κA g)) where
  h : Ht
  h = hΩ κA g

  g′ : A → Ht
  g′ c = hs hz ⊞ g c

  Λ : Ht
  Λ = top⁺ h

  l : LgB Λ
  l = Lg-⊞ (hs hz) h tt lg

  o : ∀ {w} → hs hz ⊲[ w ] Λ
  o = ⊞-fst (hs hz) h

  module P = At Λ l o

  u : ∀ {c} → azero ⊲ c → Lg c → D Λ (c , hz)
  u {c} _ _ = ni (sL {κ = κA} {c = c} C.self hself) (λ _ _ _ → n1)

  w′ : D Λ W₁
  w′ = n0 ⨾ nw q₀₁ n1

  Y′ : P.St W₁
  Y′ = P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀)

  module KG = P.KG {Λ} {azero} {hz} u (λ p lc q lV ll′ A′ co′ Y″ → P.Run accᴸ (u p lc) q lV ll′ A′ co′ Y″)
  module KR = KG.KR {W₁} q₀₁ lW₁ hself P.Act w′ Y′

  Dn : ℕ → D₀ W₁
  Dn n = drp (P.yc (KR.κΔ (KR.κc n)) (P.τ₀ (KR.lWv (KR.κc n))))

  b : A
  b = sum one (P.yc (P.Stp (P.Y₀ {W₁})) (P.τ₀ lW₁))

  TA≡ : T⁺ h lg ≡ alim (pt b Dn)
  TA≡ = refl

  -- 第 0 格: 世界 U = (V₀, 0)
  c₀ : KR.Cl
  c₀ = KR.κc 0

  U : Wd₂
  U = KR.v c₀ , hz

  lU : LgW₂ U
  lU = KR.lWv c₀

  X₁ : W₁ ≤ʷ U
  X₁ = KR.wv c₀ , hself

  open One (inj₁ tt) g′ l o U lU X₁ using (module Node; τ; gZ₀; g⊕0; pZ₀; pfx⊕)

  -- 第一个节点: 坐标 0, 层 1 ⊞ g 0
  qN : (azero , hz) ≤ʷ U
  qN = C.lim 0 (C.suc C.self) , hself

  wN : D Λ U
  wN = KR.co c₀ ⨾ n0

  YN : P.St U
  YN = P._⊕⟨_⟩_ (KR.Sv c₀) lU P.zeroD

  gN = g⊕0 {KR.Sv c₀} gZ₀

  module Fz (fz : Free (g azero)) where
    module Nd = Node {c = azero} C.self (free-top (g azero) fz) qN wN YN gN

    -- 读数 = (0 ⨾ 节点) ⨾ nl (其余各段)
    node≤cell : sum b (P.yc Nd.N τ) ≤ sum b (P.yc (KR.κΔ c₀) τ)
    node≤cell = sum≥ (sum b (P.yc Nd.N τ)) (rgt (P.yc (KR.κΔ c₀) τ))

    cell≤T : sum b (P.yc (KR.κΔ c₀) τ) ≤ T⁺ h lg
    cell≤T = ≤-trans (drp≤ (≤-refl b) (P.yc (KR.κΔ c₀) τ)) (≤l 1 (≤-refl _))

    grow : ∀ (lz : LgB (g azero)) → asuc (T⁺ (g azero) lz) ≤ T⁺ h lg
    grow lz = ≤-trans (Nd.low (pfx⊕ {KR.Sv c₀} P.zeroD pZ₀) b (sum≥ one (P.yc (P.Stp (P.Y₀ {W₁})) (P.τ₀ lW₁))) (Lg-⊞ (hs hz) (g azero) tt lz) (⊞-fst (hs hz) (g azero)))
                      (≤-trans node≤cell cell≤T)
```

## §4 `s-hΩ` 在最小坐标的分支不含 Ω-极限时

```agda
sΩ : ∀ κ (g : E S₁ κ → Ht) (lg : LgB (hΩ κ g)) → Free (g (bot S₁ κ)) → ∀ (lz : LgB (g (bot S₁ κ))) →
     asuc (T⁺ (g (bot S₁ κ)) lz) ≤ T⁺ (hΩ κ g) lg
sΩ (inj₁ tt) g lg fz lz = OmA.Fz.grow g lg fz lz
sΩ (inj₂ tt) g lg fz lz = OmH.Fz.grow g lg fz lz

-- TpMonoIf.Steps.s-hΩ 的形状, 前提 Free (g bot)
s-hΩF : ∀ κ (g : E S₁ κ → Ht) (lg : LgB (hΩ κ g)) (lc : LgE S₁ κ (bot S₁ κ)) → Free (g (bot S₁ κ)) →
        asuc (T⁺ (g (bot S₁ κ)) (proj₂ lg (bot S₁ κ) lc)) ≤ T⁺ (hΩ κ g) lg
s-hΩF κ g lg lc fz = sΩ κ g lg fz (proj₂ lg (bot S₁ κ) lc)
```

## §5 特例 (无前提)

```agda
-- T⁺ 0 < T⁺ Ω₂
T0<Ω₂ : asuc (T⁺ hz tt) ≤ T-Ω₂
T0<Ω₂ = sΩ κH _ lΩ₂ tt tt

-- T⁺ 0 < T⁺ (Ω₂²)
T0<Ω₂² : asuc (T⁺ hz tt) ≤ T-Ω₂²
T0<Ω₂² = sΩ κH _ Lg-Ω₂² tt tt
```
