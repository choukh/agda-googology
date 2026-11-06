# ValX (四): 跨底折叠对世界、界与输入联合单调, 跨底路线引理, 保值合法

> 不含记号. 入口 [ValX](ValX.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 模块参数: `uipC` (`Cd` 上的 UIP, 同 ValC; 用在 ValC 的 `sameR`, `monoΦ`, `route`, 与本篇 `kcC` 的分量 0 情形), `SL : ShLaw I` (回灌与世界的值律, 实例 `I₁` 在 [ValXTm](ValXTm.lagda.md) 证出). 只导入 stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValC*` (只用, 不改), [ValXRel](ValXRel.lagda.md).
>
> **四条互递归的定理** (跨底折叠 `FXa a B l pt b x n`: $\Omega_1$ 层的 $x$ 在世界 $B$ 里折到可数层号 $t\lhd B$, 界 $b$; 两边的可达性、合法、目标证据、路径可以不同):
>
> - `monoX`: 世界 $B_1\le B_2$ (第 0 层的值关系), 界 $\mathrm{top}\,t\le b\le b'$ (值合法), 输入 $x\le_X y$ (都 `MoX`) ⟹ $\Phi^\times_{B_1,b}\,x\le\Phi^\times_{B_2,b'}\,y$.
> - `routeX` (跨底路线引理): $t$ 是 $j$ 的真第一位置 ⟹ $\Phi^\times_{B_1\to t,b}\,x\le\Phi_{j\to t,b'}(\Phi^\times_{W_2\to j,\mathrm{top}\,j}\,y)$.
> - `brX` (分支不高于结点): 在可入的回灌坐标处取分支再折, 不高于整个结点折.
> - `MoXΦ`: 跨底折叠保值合法.
>
> **`Ω≤Ω` 的两边可以是同分量同层的不同种类.** 右边的决定先沿层号相等 $e$ 搬到左边的层 (`pickTr`), 坐标经 `to′ d = toX κX′ (subst H e d)`; 两边各带坐标数据 `KD`, 两份数据之间的联合单调 `KC` 由 `kcC` 给出.
>
> **内部的世界只按值比较.** 进入 $\Omega_1$ 分支后两边的世界是 $\mathrm{nxt}_0(\mathrm{sh}_0\,B_i\,c_i)$, 只按值相关; 这是证明的内部引理. 接口的律 (同一世界) 是它的特例. 决定 (留 / 同层 / 在上) 只依赖种类的层与目标 (ValC 的视图 `DV`), 与世界无关.
>
> **适用范围.** 前提 `MoX y` 要求右边 $\Omega$-结点的分支对坐标值单调. 地板 `topL` 不满足 ([ValXObs](ValXObs.lagda.md) `¬MoX-topL`, 定理); 它的每个分支 `gt C` 满足 ([ValXP1](ValXP1.lagda.md) `MoX-gt`, 定理).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Lean.ValXRel as XR
module OCF.Lean.ValXMono (I : CRwIf) (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) (SL : XR.ShLaw I) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (refl; subst; subst₂; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
open import OCF.Lean.ValCBase I
open import OCF.Lean.ValCMono I uipC
open import OCF.Lean.ValXRel I
open ShLaw SL
open import OCF.Lean.ValXBase I SL
open CRwIf I using (sh₀; nxt₀; Adm₀)
```

## §1 决定的视图

记法、回灌引理、坐标数据与 `oneX` 在 [ValXBase](ValXBase.lagda.md). 决定的视图 (ValC 的 `DV`):

```agda
dvX : ∀ κX {B} (ev : hs (proj₁ κX) ⊲ B) {t} (pt : t ⊲ B) (l : LgB B) →
      DV (lvX κX) t (toX κX) (pkX κX ev) (pick S⊥ (toX κX) (pkX κX ev) (cmpB (pkX κX ev) pt tt l))
dvX κX ev pt l = dv (toX κX) (pkX κX ev) (cmpB (pkX κX ev) pt tt l)
```

## §2 同分量两个种类的坐标数据联合单调 (`kcC`)

同分量 $c$ 的两个种类: $c=0$ 时只有 $\Omega_1$ 本身, 两个层号相等的证明 $e : 0\equiv0$ 用 `Cd` 上的 UIP 换成 `refl`; $c\ne0$ 时两个种类都不动世界, 回灌是恒等.

```agda
kcC : ∀ c κ κ′ (e : lvK (hs c) κ ≡ lvK (hs c) κ′) → KC (kdX (c , κ)) (kdE (c , κ′) e)
kcC hz (inj₁ ()) κ′ e
kcC hz (inj₂ _) (inj₁ ()) e
kcC hz (inj₂ _) (inj₂ _) e =
  subst (λ e′ → KC (kdX (hz , inj₂ tt)) (kdE (hz , inj₂ tt) e′)) (sym (uipC e refl))
    (record { shC = shL-mono (hz , inj₂ tt) ; nC = nW-mono (hz , inj₂ tt) })
kcC (hs c₀) (inj₁ κ) (inj₁ κ′) e = record { shC = λ {B₁} {B₂} {d₁} {d₂} w le → subst (LeAt _ d₁) (sym (ssyB e d₂)) le ; nC = λ l₁ l₂ w le → w }
kcC (hs c₀) (inj₁ κ) (inj₂ _) e = record { shC = λ {B₁} {B₂} {d₁} {d₂} w le → subst (LeAt _ d₁) (sym (ssyB e d₂)) le ; nC = λ l₁ l₂ w le → w }
kcC (hs c₀) (inj₂ _) (inj₁ κ′) e = record { shC = λ {B₁} {B₂} {d₁} {d₂} w le → subst (LeAt _ d₁) (sym (ssyB e d₂)) le ; nC = λ l₁ l₂ w le → w }
kcC (hs c₀) (inj₂ _) (inj₂ _) e = record { shC = λ {B₁} {B₂} {d₁} {d₂} w le → subst (LeAt _ d₁) (sym (ssyB e d₂)) le ; nC = λ l₁ l₂ w le → w }
kcC (hl f) (inj₁ κ) (inj₁ κ′) e = record { shC = λ {B₁} {B₂} {d₁} {d₂} w le → subst (LeAt _ d₁) (sym (ssyB e d₂)) le ; nC = λ l₁ l₂ w le → w }
kcC (hl f) (inj₁ κ) (inj₂ _) e = record { shC = λ {B₁} {B₂} {d₁} {d₂} w le → subst (LeAt _ d₁) (sym (ssyB e d₂)) le ; nC = λ l₁ l₂ w le → w }
kcC (hl f) (inj₂ _) (inj₁ κ′) e = record { shC = λ {B₁} {B₂} {d₁} {d₂} w le → subst (LeAt _ d₁) (sym (ssyB e d₂)) le ; nC = λ l₁ l₂ w le → w }
kcC (hl f) (inj₂ _) (inj₂ _) e = record { shC = λ {B₁} {B₂} {d₁} {d₂} w le → subst (LeAt _ d₁) (sym (ssyB e d₂)) le ; nC = λ l₁ l₂ w le → w }
kcC (hΩ () _) κ κ′ e
```


## §3 四条互递归的定理

```agda
mutual
  monoX : ∀ (a a′ : Acc bX hz) {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ →
          ∀ {t} (pt₁ : t ⊲ B₁) (pt₂ : t ⊲ B₂) {b b′} → Ac0.Bnd t b b′ →
          ∀ {x} y (n₁ : PH PSX B₁ x) (n₂ : PH PSX B₂ y) → MoX x → MoX y → x ≤X y →
          LeAt t (FXa a B₁ l₁ pt₁ b x n₁) (FXa a′ B₂ l₂ pt₂ b′ y n₂)
  monoX a a′ l₁ l₂ w pt₁ pt₂ B y n₁ n₂ mx my z≤ = oneX a′ l₂ pt₂ _ y n₂
  monoX a a′ l₁ l₂ w {t} pt₁ pt₂ B {hs x} (hs y) n₁ n₂ mx my (s≤s p) =
    Rel.l≤l (λ n → n) (L.idInc t) (Ac0.mul-mono t (monoX a a′ l₁ l₂ w pt₁ pt₂ B y n₁ n₂ mx my p))
  monoX a a′ l₁ l₂ w {t} pt₁ pt₂ B (hs y) n₁ n₂ mx my (≤s p) =
    Rel.≤l 0 (monoX a a′ l₁ l₂ w pt₁ pt₂ B y n₁ n₂ mx my p)
  monoX a a′ l₁ l₂ w {t} pt₁ pt₂ B {hl f} (hl g) n₁ n₂ mx my (l≤l σ i h) =
    Rel.l≤l σ i (Ac0.Σ-sub t _ _ σ i (λ n → monoX a a′ l₁ l₂ w pt₁ pt₂ B (g (σ n)) (n₁ n) (n₂ (σ n)) (mx n) (my (σ n)) (h n)))
  monoX a a′ l₁ l₂ w {t} pt₁ pt₂ B (hl g) n₁ n₂ mx my (≤l n p) =
    Rel.≤l n (L.≤-trans t (monoX a a′ l₁ l₂ w pt₁ pt₂ B (g n) n₁ (n₂ n) mx (my n) p) (Ac0.Σ-ge t _ n))
  monoX a (acc rs′) {B₁} {B₂} l₁ l₂ w {t} pt₁ pt₂ {b} {b′} B {x} (hΩ κX g′) n₁ (ev₂ , pg₂) mx my (≤Ω c bd mc p) =
    ΦΩX rs′ l₂ pt₂ b′ κX g′ ev₂ pg₂ (λ z → LeAt t (FXa a B₁ l₁ pt₁ b x n₁) z)
      (mΩ1X a rs′ l₁ l₂ pt₁ pt₂ B κX g′ ev₂ pg₂ (dvX κX ev₂ pt₂ l₂) n₁ mx my c bd mc
        (λ e le me → L.≤-trans hz w (nW-up κX l₂ e) ,
                     brUp κX g′ B₂ my c e mc me (L.≤-trans (lvX κX) le (shL-infl κX B₂ e)) p))
  monoX (acc rs) (acc rs′) {B₁} {B₂} l₁ l₂ w {t} pt₁ pt₂ {b} {b′} B {hΩ (c , κ) g} (hΩ (_ , κ′) g′) (ev₁ , pg₁) (ev₂ , pg₂) mx my (Ω≤Ω e h) =
    ΦΩX rs l₁ pt₁ b (c , κ) g ev₁ pg₁ (λ z → LeAt t z (FXa (acc rs′) B₂ l₂ pt₂ b′ (hΩ (c , κ′) g′) (ev₂ , pg₂)))
      (ΦΩX rs′ l₂ pt₂ b′ (c , κ′) g′ ev₂ pg₂ (λ z → LeAt t Lft z)
        (subst (λ z → LeAt t Lft (caseDc z (KcX rs′ l₂ pt₂ b′ (c , κ′) g′ pg₂) (ScX rs′ l₂ pt₂ b′ (c , κ′) g′ pg₂) (AcX rs′ l₂ pt₂ b′ (c , κ′) g′ pg₂)))
          (sym (proj₂ PT))
          (mΩΩX rs rs′ l₁ l₂ w pt₁ pt₂ B (c , κ) (c , κ′) g g′ pg₁ pg₂ (toX (c , κ)) (λ d → toX (c , κ′) (subst H e d))
             (pkX (c , κ) ev₁) (subst (λ z → hs z ⊲ B₂) (sym e) (pkX (c , κ′) ev₂))
             (kdX (c , κ)) (kdE (c , κ′) e) (kcC c κ κ′ e) (dvX (c , κ) ev₁ pt₁ l₁) (proj₁ PT) mx (moTE (c , κ′) e g′ my) h)))
    where
    Lft = caseDc (pick S⊥ (toX (c , κ)) (pkX (c , κ) ev₁) (cmpB (pkX (c , κ) ev₁) pt₁ tt l₁))
            (KcX rs l₁ pt₁ b (c , κ) g pg₁) (ScX rs l₁ pt₁ b (c , κ) g pg₁) (AcX rs l₁ pt₁ b (c , κ) g pg₁)
    PT = pickTr e (toX (c , κ′)) (pkX (c , κ′) ev₂) (cmpB (pkX (c , κ′) ev₂) pt₂ tt l₂)
```

**`≤Ω` 一侧: 左边不高于右边结点的某个分支** (前提写成对 $c$ 之上的一切坐标 $e$: 世界 $B_1\le$ 进入 $e$ 后的世界, $x\le$ 回灌后的分支). 三种决定: 留 (取坐标 $c$ 的那一支), 同层 (链的第 0 点), 在上 (跨底路线引理接到第 $k$ 层, 再用第 $k$ 层的单调).

```agda
  mΩ1X : ∀ (a : Acc bX hz) rs′ {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) →
         ∀ {t} (pt₁ : t ⊲ B₁) (pt₂ : t ⊲ B₂) {b b′} → Ac0.Bnd t b b′ →
         ∀ κX (g′ : E XS κX → HX) (ev₂ : hs (proj₁ κX) ⊲ B₂) (pg₂ : PGt B₂ κX g′) {d} →
         DV (lvX κX) t (toX κX) (pkX κX ev₂) d → ∀ {x} (n₁ : PH PSX B₁ x) → MoX x → MoX (hΩ κX g′) →
         ∀ c → LeAt (lvX κX) c (top b⊥ (lvX κX)) → MoAt (lvX κX) c →
         (∀ e → LeAt (lvX κX) c e → MoAt (lvX κX) e → LeAt hz B₁ (nW κX l₂ e) × (x ≤X g′ (psh (P κX) B₂ (toX κX e)))) →
         LeAt t (FXa a B₁ l₁ pt₁ b x n₁) (caseDc d (KcX rs′ l₂ pt₂ b′ κX g′ pg₂) (ScX rs′ l₂ pt₂ b′ κX g′ pg₂) (AcX rs′ l₂ pt₂ b′ κX g′ pg₂))
  mΩ1X a rs′ {B₁} {B₂} l₁ l₂ {t} pt₁ pt₂ {b} {b′} B κX g′ ev₂ pg₂ (dk κ₁ e₁ fr ft u) {x} n₁ mx my c bd mc up =
    keepR t κ₁ e₁ fr ft (br (acc rs′) l₂ pt₂ κX g′ pg₂ b′) c bd mc
      (monoX a (acc rs′) l₁ (lgW κX l₂ c) (proj₁ (up c (L.≤-refl _ c) mc)) pt₁ (ptW κX l₂ pt₂ c) B
         (g′ (psh (P κX) B₂ (toX κX c))) n₁ (pgW κX l₂ pg₂ c) mx (brMo κX g′ B₂ my c mc) (proj₂ (up c (L.≤-refl _ c) mc)))
  mΩ1X a rs′ {B₁} {B₂} l₁ l₂ {t} pt₁ pt₂ {b} {b′} B@(mb , mb′ , tb , bb) κX g′ ev₂ pg₂ ds {x} n₁ mx my c bd mc up =
    Rel.≤l 0 (monoX a (acc rs′) l₁ (lgW κX l₂ b′) (proj₁ (up b′ le mb′)) pt₁ (ptW κX l₂ pt₂ b′) B
      (g′ (psh (P κX) B₂ (toX κX b′))) n₁ (pgW κX l₂ pg₂ b′) mx (brMo κX g′ B₂ my b′ mb′) (proj₂ (up b′ le mb′)))
    where le = L.≤-trans t bd (L.≤-trans t tb bb)
  mΩ1X a rs′ {B₁} {B₂} l₁ l₂ {t} pt₁ pt₂ {b} {b′} B@(mb , mb′ , tb , bb) κX g′ ev₂ pg₂ (da q pp) {x} n₁ mx my c bd mc up =
    L.≤-trans t
      (routeX a (acc rs′) l₁ (lgW κX l₂ (top b⊥ k)) (proj₁ (up (top b⊥ k) bd (Mo-top k))) (rs′ b⊥ k lx) (lg↓ pk l₂)
         (ptW κX l₂ (⊏⊑ pk) (top b⊥ k)) pt₁ q pp B (g′ (psh (P κX) B₂ (toX κX (top b⊥ k)))) n₁ (pgW κX l₂ pg₂ (top b⊥ k))
         mx (brMo κX g′ B₂ my (top b⊥ k) (Mo-top k)) (proj₂ (up (top b⊥ k) bd (Mo-top k))))
      (monoΦ (apWf k) (rs′ b⊥ k lx) (rs′ b⊥ k lx) (lg↓ pk l₂) (lg↓ pk l₂) q q (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb))
         (hl (chain (top b⊥ k) (λ b″ → br (acc rs′) l₂ (⊏⊑ pk) κX g′ pg₂ b″ b″)))
         (MoXΦ (acc rs′) (lgW κX l₂ (top b⊥ k)) (ptW κX l₂ (⊏⊑ pk) (top b⊥ k)) (Mo-top k) (L.≤-refl k _) (g′ (psh (P κX) B₂ (toX κX (top b⊥ k)))) (pgW κX l₂ pg₂ (top b⊥ k))
            (brMo κX g′ B₂ my (top b⊥ k) (Mo-top k)))
         (moChX (acc rs′) l₂ κX (⊏⊑ pk) g′ pg₂ my)
         (Rel.≤l 0 (L.≤-refl k _)))
    where
    k = lvX κX
    pk = pkX κX ev₂
```

**`Ω≤Ω` 一侧** (同分量同层的两个种类; 右边的决定已沿层号相等搬到左边的层 $k$, 坐标经 `to′`; 两边的决定一致, 同层要 `sameR`).

```agda
  mΩΩX : ∀ rs rs′ {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ →
         ∀ {t} (pt₁ : t ⊲ B₁) (pt₂ : t ⊲ B₂) {b b′} → Ac0.Bnd t b b′ →
         ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt B₂ κX′ g′) {k}
         (to : H k → E XS κX) (to′ : H k → E XS κX′) (pk : hs k ⊲ B₁) (pk′ : hs k ⊲ B₂)
         (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ → ∀ {d} →
         DV k t to pk d → (r₂ : (t ⊲ hs k) ⊎ (hs k ⊲ t)) → MoT κX k to g → MoT κX′ k to′ g′ →
         (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
         LeAt t (caseDc d (KcX rs l₁ pt₁ b κX g pg₁) (ScX rs l₁ pt₁ b κX g pg₁) (AcX rs l₁ pt₁ b κX g pg₁))
                (caseDc (pick S⊥ to′ pk′ r₂) (KcX rs′ l₂ pt₂ b′ κX′ g′ pg₂) (ScX rs′ l₂ pt₂ b′ κX′ g′ pg₂) (AcX rs′ l₂ pt₂ b′ κX′ g′ pg₂))
  mΩΩX rs rs′ l₁ l₂ w pt₁ pt₂ B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C (dk κ₁ e₁ fr₁ ft₁ u₁) r₂ mx my h =
    mΩΩkX rs rs′ l₁ l₂ w pt₁ pt₂ B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C κ₁ e₁ fr₁ ft₁ u₁ (dv to′ pk′ r₂) mx my h
  mΩΩX rs rs′ {B₁} {B₂} l₁ l₂ w {t} pt₁ pt₂ {b} {b′} B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C ds r₂ mx my h =
    subst (λ z → LeAt t (ScX rs l₁ pt₁ b κX g pg₁ to)
                        (caseDc z (KcX rs′ l₂ pt₂ b′ κX′ g′ pg₂) (ScX rs′ l₂ pt₂ b′ κX′ g′ pg₂) (AcX rs′ l₂ pt₂ b′ κX′ g′ pg₂)))
      (sym (sameR to′ pk′ r₂))
      (Ac0.chLe-hl t (λ b₁ → brT (acc rs) l₁ pt₁ κX g pg₁ to b₁ b₁) (λ b₂ → brT (acc rs′) l₂ pt₂ κX′ g′ pg₂ to′ b₂ b₂) B
        (kpT (acc rs) l₁ κX pt₁ g pg₁ to K₁ mx) (kpT (acc rs′) l₂ κX′ pt₂ g′ pg₂ to′ K₂ my)
        (λ {b₁} {b₂} Bb@(m1 , m2 , t1 , le) →
          ptCmp (acc rs) (acc rs′) l₁ l₂ w pt₁ pt₂ Bb κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h b₁ b₂ m1 m2 le))
  mΩΩX rs rs′ l₁ l₂ w pt₁ pt₂ B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C (da q pp) r₂ mx my h =
    mΩΩaX rs rs′ l₁ l₂ w pt₁ pt₂ B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C q pp (dv to′ pk′ r₂) mx my h

  mΩΩkX : ∀ rs rs′ {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ →
          ∀ {t} (pt₁ : t ⊲ B₁) (pt₂ : t ⊲ B₂) {b b′} → Ac0.Bnd t b b′ →
          ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt B₂ κX′ g′) {k}
          (to : H k → E XS κX) (to′ : H k → E XS κX′) (pk : hs k ⊲ B₁) (pk′ : hs k ⊲ B₂)
          (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ →
          (κ₁ : K (T t)) (e₁ : lvK t κ₁ ≡ k) (fr₁ : E (T t) κ₁ → H k) →
          (∀ c → fr₁ (toK t κ₁ c) ≡ subst H e₁ c) → hs k ⊲ t → ∀ {d′} → DV k t to′ pk′ d′ →
          MoT κX k to g → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
          LeAt t (KcX rs l₁ pt₁ b κX g pg₁ κ₁ (λ c → to (fr₁ c)))
                 (caseDc d′ (KcX rs′ l₂ pt₂ b′ κX′ g′ pg₂) (ScX rs′ l₂ pt₂ b′ κX′ g′ pg₂) (AcX rs′ l₂ pt₂ b′ κX′ g′ pg₂))
  mΩΩkX rs rs′ {B₁} {B₂} l₁ l₂ w {t} pt₁ pt₂ {b} {b′} B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C κ₁ e₁ fr₁ ft₁ u₁ (dk κ₂ e₂ fr₂ ft₂ u₂) mx my h =
    keepKK t κ₁ κ₂ e₁ e₂ fr₁ fr₂ ft₁ ft₂ (brT (acc rs) l₁ pt₁ κX g pg₁ to b) (brT (acc rs′) l₂ pt₂ κX′ g′ pg₂ to′ b′)
      (λ c mc → ptCmp (acc rs) (acc rs′) l₁ l₂ w pt₁ pt₂ B κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h c c mc mc (L.≤-refl _ c))
  mΩΩkX rs rs′ l₁ l₂ w pt₁ pt₂ B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C κ₁ e₁ fr₁ ft₁ u₁ ds mx my h = ⊥-elim (nos u₁)
  mΩΩkX rs rs′ l₁ l₂ w pt₁ pt₂ B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C κ₁ e₁ fr₁ ft₁ u₁ (da q pp) mx my h = ⊥-elim (nos′ u₁ q)

  mΩΩaX : ∀ rs rs′ {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ →
          ∀ {t} (pt₁ : t ⊲ B₁) (pt₂ : t ⊲ B₂) {b b′} → Ac0.Bnd t b b′ →
          ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt B₂ κX′ g′) {k}
          (to : H k → E XS κX) (to′ : H k → E XS κX′) (pk : hs k ⊲ B₁) (pk′ : hs k ⊲ B₂)
          (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ →
          (q : t ⊲ k) → Pp t k → ∀ {d′} → DV k t to′ pk′ d′ →
          MoT κX k to g → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
          LeAt t (AcX rs l₁ pt₁ b κX g pg₁ k pk q to)
                 (caseDc d′ (KcX rs′ l₂ pt₂ b′ κX′ g′ pg₂) (ScX rs′ l₂ pt₂ b′ κX′ g′ pg₂) (AcX rs′ l₂ pt₂ b′ κX′ g′ pg₂))
  mΩΩaX rs rs′ l₁ l₂ w pt₁ pt₂ B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C q pp (dk κ₂ e₂ fr₂ ft₂ u₂) mx my h = ⊥-elim (nos′ u₂ q)
  mΩΩaX rs rs′ l₁ l₂ w pt₁ pt₂ B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C q pp ds mx my h = ⊥-elim (noPP pp hself)
  mΩΩaX rs rs′ {B₁} {B₂} l₁ l₂ w {t} pt₁ pt₂ {b} {b′} B κX κX′ g g′ pg₁ pg₂ {k} to to′ pk pk′ K₁ K₂ C q pp (da q′ pp′) mx my h =
    monoΦ (apWf k) (rs b⊥ k lx) (rs′ b⊥ k lx) (lg↓ pk l₁) (lg↓ pk′ l₂) q q′ B
      (hl (chain (top b⊥ k) (λ b₂ → brT (acc rs′) l₂ (⊏⊑ pk′) κX′ g′ pg₂ to′ b₂ b₂)))
      (moChT (acc rs) l₁ κX (⊏⊑ pk) g pg₁ to K₁ mx) (moChT (acc rs′) l₂ κX′ (⊏⊑ pk′) g′ pg₂ to′ K₂ my)
      (chT (acc rs) (acc rs′) l₁ l₂ w (⊏⊑ pk) (⊏⊑ pk′) κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h)
```

**链的小件**: 两边分支的逐点比较 (`ptCmp`), 链点值合法 (`kpT`), 以地板起头的链值合法 (`moChT`), 两条以地板起头的链比较 (`chT`); 本种类的特例 `kpX`, `moChX`.

```agda
  ptCmp : ∀ (a a′ : Acc bX hz) {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ →
          ∀ {s} (ps₁ : s ⊲ B₁) (ps₂ : s ⊲ B₂) {b₁ b₂} → Ac0.Bnd s b₁ b₂ →
          ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt B₂ κX′ g′) {k}
          (to : H k → E XS κX) (to′ : H k → E XS κX′) (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ →
          MoT κX k to g → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
          ∀ d₁ d₂ → MoAt k d₁ → MoAt k d₂ → LeAt k d₁ d₂ →
          LeAt s (brT a l₁ ps₁ κX g pg₁ to b₁ d₁) (brT a′ l₂ ps₂ κX′ g′ pg₂ to′ b₂ d₂)
  ptCmp a a′ {B₁} {B₂} l₁ l₂ w ps₁ ps₂ Bb κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h d₁ d₂ m1 m2 le =
    monoX a a′ (lgE κX l₁ (to d₁)) (lgE κX′ l₂ (to′ d₂)) (nC C l₁ l₂ w le) (ptE κX l₁ ps₁ (to d₁)) (ptE κX′ l₂ ps₂ (to′ d₂)) Bb
      (g′ (psh (P κX′) B₂ (to′ d₂))) (pgE κX l₁ pg₁ (to d₁)) (pgE κX′ l₂ pg₂ (to′ d₂))
      (brMoT K₁ g B₁ mx d₁ m1) (brMoT K₂ g′ B₂ my d₂ m2) (brLeT C g g′ B₁ B₂ w my h d₁ d₂ m1 m2 le)

  kpT : ∀ (a : Acc bX hz) {B} (l : LgB B) κX {k} (ps : k ⊲ B) (g : E XS κX → HX) (pg : PGt B κX g) (to : H k → E XS κX) →
        KD κX k to → MoT κX k to g → Ac0.KP k (λ b₁ → brT a l ps κX g pg to b₁ b₁)
  kpT a {B} l κX ps g pg to K mg b₁ mb tb =
    MoXΦ a (lgE κX l (to b₁)) (ptE κX l ps (to b₁)) mb tb (g (psh (P κX) B (to b₁))) (pgE κX l pg (to b₁)) (brMoT K g B mg b₁ mb)

  moChT : ∀ (a : Acc bX hz) {B} (l : LgB B) κX {k} (ps : k ⊲ B) (g : E XS κX → HX) (pg : PGt B κX g) (to : H k → E XS κX) →
          KD κX k to → MoT κX k to g → MoAt k (hl (chain (top b⊥ k) (λ b₁ → brT a l ps κX g pg to b₁ b₁)))
  moChT a l κX {k} ps g pg to K mg = Ac0.chM k (top b⊥ k) _ (Mo-top k) (L.≤-refl k _) (kpT a l κX ps g pg to K mg)

  chT : ∀ (a a′ : Acc bX hz) {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ → ∀ {k} (ps₁ : k ⊲ B₁) (ps₂ : k ⊲ B₂) →
        ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt B₂ κX′ g′)
        (to : H k → E XS κX) (to′ : H k → E XS κX′) (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ →
        MoT κX k to g → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
        LeAt k (hl (chain (top b⊥ k) (λ b₁ → brT a l₁ ps₁ κX g pg₁ to b₁ b₁))) (hl (chain (top b⊥ k) (λ b₂ → brT a′ l₂ ps₂ κX′ g′ pg₂ to′ b₂ b₂)))
  chT a a′ l₁ l₂ w {k} ps₁ ps₂ κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h =
    Ac0.chLe-hl k _ _ (Ac0.bnd-refl k (Mo-top k) (L.≤-refl k _)) (kpT a l₁ κX ps₁ g pg₁ to K₁ mx) (kpT a′ l₂ κX′ ps₂ g′ pg₂ to′ K₂ my)
      (λ {b₁} {b₂} Bb@(m1 , m2 , t1 , le) → ptCmp a a′ l₁ l₂ w ps₁ ps₂ Bb κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h b₁ b₂ m1 m2 le)

  kpX : ∀ (a : Acc bX hz) {B} (l : LgB B) κX (ps : lvX κX ⊲ B) (g : E XS κX → HX) (pg : PGt B κX g) → MoX (hΩ κX g) →
        Ac0.KP (lvX κX) (λ b₁ → br a l ps κX g pg b₁ b₁)
  kpX a l κX ps g pg mg = kpT a l κX ps g pg (toX κX) (kdX κX) mg

  moChX : ∀ (a : Acc bX hz) {B} (l : LgB B) κX (ps : lvX κX ⊲ B) (g : E XS κX → HX) (pg : PGt B κX g) → MoX (hΩ κX g) →
          MoAt (lvX κX) (hl (chain (top b⊥ (lvX κX)) (λ b₁ → br a l ps κX g pg b₁ b₁)))
  moChX a l κX ps g pg mg = moChT a l κX ps g pg (toX κX) (kdX κX) mg
```


**保值合法.**

```agda
  MoXΦ : ∀ (a : Acc bX hz) {B} (l : LgB B) {t} (pt : t ⊲ B) {b} → MoAt t b → LeAt t (top b⊥ t) b →
         ∀ x n → MoX x → MoAt t (FXa a B l pt b x n)
  MoXΦ a l pt mb tb hz n mx = tt
  MoXΦ a l {t} pt mb tb (hs x) n mx = Ac0.Mo-mul t _ (MoXΦ a l pt mb tb x n mx)
  MoXΦ a l {t} pt mb tb (hl f) n mx = Ac0.Mo-Σ t _ (λ k → MoXΦ a l pt mb tb (f k) (n k) (mx k))
  MoXΦ (acc rs) l {t} pt {b} mb tb (hΩ κX g) (ev , pg) mx =
    ΦΩX rs l pt b κX g ev pg (MoAt t) (moΩX rs l pt mb tb κX g ev pg (dvX κX ev pt l) mx)

  moΩX : ∀ rs {B} (l : LgB B) {t} (pt : t ⊲ B) {b} → MoAt t b → LeAt t (top b⊥ t) b →
         ∀ κX (g : E XS κX → HX) (ev : hs (proj₁ κX) ⊲ B) (pg : PGt B κX g) {d} → DV (lvX κX) t (toX κX) (pkX κX ev) d → MoX (hΩ κX g) →
         MoAt t (caseDc d (KcX rs l pt b κX g pg) (ScX rs l pt b κX g pg) (AcX rs l pt b κX g pg))
  moΩX rs {B} l {t} pt {b} mb tb κX g ev pg (dk κ₁ e₁ fr ft u) mx =
    keepMo t κ₁ e₁ fr ft (br (acc rs) l pt κX g pg b)
      (λ c c′ mc mc′ p → monoX (acc rs) (acc rs) (lgW κX l c) (lgW κX l c′) (nW-mono κX l l (L.≤-refl hz B) p)
         (ptW κX l pt c) (ptW κX l pt c′) (Ac0.bnd-refl t mb tb) (g (psh (P κX) B (toX κX c′))) (pgW κX l pg c) (pgW κX l pg c′)
         (brMo κX g B mx c mc) (brMo κX g B mx c′ mc′) (brLe κX g g B B (L.≤-refl hz B) mx (λ c₀ _ → ≤X-refl _) c c′ mc mc′ p))
      (λ c mc → MoXΦ (acc rs) (lgW κX l c) (ptW κX l pt c) mb tb (g (psh (P κX) B (toX κX c))) (pgW κX l pg c) (brMo κX g B mx c mc))
  moΩX rs l {t} pt {b} mb tb κX g ev pg ds mx = Ac0.chM t b _ mb tb (kpX (acc rs) l κX pt g pg mx)
  moΩX rs l {t} pt {b} mb tb κX g ev pg (da q pp) mx =
    MoΦ (apWf (lvX κX)) (rs b⊥ (lvX κX) lx) (lg↓ (pkX κX ev) l) q mb tb (hl (chain (top b⊥ (lvX κX)) (λ b₁ → br (acc rs) l (⊏⊑ (pkX κX ev)) κX g pg b₁ b₁))) (moChX (acc rs) l κX (⊏⊑ (pkX κX ev)) g pg mx)
```

**分支不高于结点** (`brX`): 在回灌后的坐标 $c$ ($c\le\mathrm{top}$) 取分支, 以世界 `nW c` 折, 不高于整个结点在世界 $W$ 里折.

```agda
  brX : ∀ (a : Acc bX hz) {W} (l : LgB W) {s} (ps : s ⊲ W) {b b′} → Ac0.Bnd s b b′ →
        ∀ κX (g : E XS κX → HX) (ev : hs (proj₁ κX) ⊲ W) (pg : PGt W κX g) → MoX (hΩ κX g) →
        ∀ c → LeAt (lvX κX) c (top b⊥ (lvX κX)) → MoAt (lvX κX) c →
        LeAt s (br a l ps κX g pg b c) (FXa a W l ps b′ (hΩ κX g) (ev , pg))
  brX (acc rs) {W} l {s} ps {b} {b′} B κX g ev pg mg c bd mc =
    ΦΩX rs l ps b′ κX g ev pg (λ z → LeAt s (br (acc rs) l ps κX g pg b c) z)
      (mΩ1X (acc rs) rs (lgW κX l c) l (ptW κX l ps c) ps B κX g ev pg (dvX κX ev ps l) (pgW κX l pg c)
        (brMo κX g W mg c mc) mg c bd mc
        (λ e le me → nW-mono κX l l (L.≤-refl hz W) le ,
                     brLe κX g g W W (L.≤-refl hz W) mg (λ c₀ _ → ≤X-refl _) c e mc me le))
```

**跨底路线引理.** 对 $x\le_X y$ 的推导; 结构同 ValC 的 `route`, 第 $j$ 层的单调与保值合法取 ValC 的 `monoΦ`, `MoΦ` (外部定理, 不在互递归里).

```agda
  routeX : ∀ (a a′ : Acc bX hz) {B₁ W₂} (l₁ : LgB B₁) (l₂ : LgB W₂) → LeAt hz B₁ W₂ →
           ∀ {j} (aj : Acc b⊥ j) (lj : LgB j) (pj₂ : j ⊲ W₂) {t} (pt₁ : t ⊲ B₁) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
           ∀ {x} y (n₁ : PH PSX B₁ x) (n₂ : PH PSX W₂ y) → MoX x → MoX y → x ≤X y →
           LeAt t (FXa a B₁ l₁ pt₁ b x n₁) (G aj lj t qo b′ (FXa a′ W₂ l₂ pj₂ (top b⊥ j) y n₂))
  routeX a a′ l₁ l₂ w aj lj pj₂ {t} pt₁ qo pp {b} {b′} B y n₁ n₂ mx my z≤ =
    one≤ aj lj t qo b′ _
  routeX a a′ {B₁} {W₂} l₁ l₂ w {j} aj lj pj₂ {t} pt₁ qo pp {b} {b′} B@(mb , mb′ , tb , bb) {hs x} (hs y) n₁ n₂ mx my (s≤s p) =
    Rel.l≤l (λ n → n) (L.idInc t) (λ n → L.≤-trans t
      (Ac0.mul-mono t (routeX a a′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B y n₁ n₂ mx my p) n)
      (Ac0.mulΣ t (G aj lj t qo b′ Fy) (λ k → G aj lj t qo b′ (mul Fy k))
         (λ k → monoΦ (apWf j) aj aj lj lj qo qo (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb)) (mul Fy k)
            MFy (Ac0.Mo-mul j _ MFy k) (Ac0.≤mul j _ k)) n))
    where
    Fy = FXa a′ W₂ l₂ pj₂ (top b⊥ j) y n₂
    MFy = MoXΦ a′ l₂ pj₂ (Mo-top j) (L.≤-refl j _) y n₂ my
  routeX a a′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B (hs y) n₁ n₂ mx my (≤s p) =
    Rel.≤l 0 (routeX a a′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B y n₁ n₂ mx my p)
  routeX a a′ {B₁} {W₂} l₁ l₂ w {j} aj lj pj₂ {t} pt₁ qo pp {b} {b′} B@(mb , mb′ , tb , bb) {hl f} (hl g) n₁ n₂ mx my (l≤l σ i h) =
    Rel.l≤l σ i (Ac0.Σ-sub t _ _ σ i (λ n → L.≤-trans t
      (routeX a a′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B (g (σ n)) (n₁ n) (n₂ (σ n)) (mx n) (my (σ n)) (h n))
      (monoΦ (apWf j) aj aj lj lj qo qo (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb)) (Σ⁺ Fg (σ n))
         (MFg (σ n)) (Ac0.Mo-Σ j _ MFg (σ n)) (Ac0.Σ-ge j Fg (σ n)))))
    where
    Fg = λ k → FXa a′ W₂ l₂ pj₂ (top b⊥ j) (g k) (n₂ k)
    MFg = λ k → MoXΦ a′ l₂ pj₂ (Mo-top j) (L.≤-refl j _) (g k) (n₂ k) (my k)
  routeX a a′ {B₁} {W₂} l₁ l₂ w {j} aj lj pj₂ {t} pt₁ qo pp {b} {b′} B@(mb , mb′ , tb , bb) (hl g) n₁ n₂ mx my (≤l n p) =
    Rel.≤l n (L.≤-trans t (routeX a a′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B (g n) n₁ (n₂ n) mx (my n) p)
      (L.≤-trans t (monoΦ (apWf j) aj aj lj lj qo qo (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb)) (Σ⁺ Fg n)
           (MFg n) (Ac0.Mo-Σ j _ MFg n) (Ac0.Σ-ge j Fg n))
        (Ac0.Σ-ge t _ n)))
    where
    Fg = λ k → FXa a′ W₂ l₂ pj₂ (top b⊥ j) (g k) (n₂ k)
    MFg = λ k → MoXΦ a′ l₂ pj₂ (Mo-top j) (L.≤-refl j _) (g k) (n₂ k) (my k)
  routeX a a′ {B₁} {W₂} l₁ l₂ w {j} aj lj pj₂ {t} pt₁ qo pp {b} {b′} B@(mb , mb′ , tb , bb) {x} (hΩ κX g′) n₁ (ev₂ , pg₂) mx my (≤Ω c bd mc p) =
    L.≤-trans t
      (routeX a a′ l₁ (lgW κX l₂ c) (L.≤-trans hz w (nW-up κX l₂ c)) aj lj (ptW κX l₂ pj₂ c) pt₁ qo pp B
         (g′ (psh (P κX) W₂ (toX κX c))) n₁ (pgW κX l₂ pg₂ c) mx (brMo κX g′ W₂ my c mc)
         (brUp κX g′ W₂ my c c mc mc (shL-infl κX W₂ c) p))
      (monoΦ (apWf j) aj aj lj lj qo qo (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb))
         (FXa a′ W₂ l₂ pj₂ (top b⊥ j) (hΩ κX g′) (ev₂ , pg₂))
         (MoXΦ a′ (lgW κX l₂ c) (ptW κX l₂ pj₂ c) (Mo-top j) (L.≤-refl j _) (g′ (psh (P κX) W₂ (toX κX c))) (pgW κX l₂ pg₂ c) (brMo κX g′ W₂ my c mc))
         (MoXΦ a′ l₂ pj₂ (Mo-top j) (L.≤-refl j _) (hΩ κX g′) (ev₂ , pg₂) my)
         (brX a′ l₂ pj₂ (Ac0.bnd-refl j (Mo-top j) (L.≤-refl j _)) κX g′ ev₂ pg₂ my c bd mc))
  routeX (acc rs) (acc rs′) {B₁} {W₂} l₁ l₂ w {j} aj lj pj₂ {t} pt₁ qo pp {b} {b′} B {hΩ (c , κ) g} (hΩ (_ , κ′) g′) (ev₁ , pg₁) (ev₂ , pg₂) mx my (Ω≤Ω e h) =
    ΦΩX rs l₁ pt₁ b (c , κ) g ev₁ pg₁ (λ z → LeAt t z (G aj lj t qo b′ (FXa (acc rs′) W₂ l₂ pj₂ (top b⊥ j) (hΩ (c , κ′) g′) (ev₂ , pg₂))))
      (ΦΩX rs′ l₂ pj₂ (top b⊥ j) (c , κ′) g′ ev₂ pg₂ (λ z → LeAt t Lft (G aj lj t qo b′ z))
        (subst (λ z → LeAt t Lft (G aj lj t qo b′ (caseDc z (KcX rs′ l₂ pj₂ (top b⊥ j) (c , κ′) g′ pg₂)
                                                           (ScX rs′ l₂ pj₂ (top b⊥ j) (c , κ′) g′ pg₂) (AcX rs′ l₂ pj₂ (top b⊥ j) (c , κ′) g′ pg₂))))
          (sym (proj₂ PT))
          (rΩΩX rs rs′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B (c , κ) (c , κ′) g g′ pg₁ pg₂ (toX (c , κ)) to′ (pkX (c , κ) ev₁) pk′
             (kdX (c , κ)) (kdE (c , κ′) e) (kcC c κ κ′ e) (dvX (c , κ) ev₁ pt₁ l₁) (dv to′ pk′ (proj₁ PT)) mx (moTE (c , κ′) e g′ my) h)))
    where
    to′ : H (lvX (c , κ)) → E XS (c , κ′)
    to′ d = toX (c , κ′) (subst H e d)
    pk′ : hs (lvX (c , κ)) ⊲ W₂
    pk′ = subst (λ z → hs z ⊲ W₂) (sym e) (pkX (c , κ′) ev₂)
    Lft = caseDc (pick S⊥ (toX (c , κ)) (pkX (c , κ) ev₁) (cmpB (pkX (c , κ) ev₁) pt₁ tt l₁))
            (KcX rs l₁ pt₁ b (c , κ) g pg₁) (ScX rs l₁ pt₁ b (c , κ) g pg₁) (AcX rs l₁ pt₁ b (c , κ) g pg₁)
    PT = pickTr e (toX (c , κ′)) (pkX (c , κ′) ev₂) (cmpB (pkX (c , κ′) ev₂) pj₂ tt l₂)
```

**路线引理的 `Ω≤Ω`**: 按第一步 (跨底折到第 $j$ 层) 的决定 (右边已搬到左边的层 $k$).

```agda
  rΩΩX : ∀ rs rs′ {B₁ W₂} (l₁ : LgB B₁) (l₂ : LgB W₂) → LeAt hz B₁ W₂ →
         ∀ {j} (aj : Acc b⊥ j) (lj : LgB j) (pj₂ : j ⊲ W₂) {t} (pt₁ : t ⊲ B₁) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
         ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt W₂ κX′ g′) {k}
         (to : H k → E XS κX) (to′ : H k → E XS κX′) (pk : hs k ⊲ B₁) (pk′ : hs k ⊲ W₂)
         (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ → ∀ {d d″} →
         DV k t to pk d → DV k j to′ pk′ d″ → MoT κX k to g → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
         LeAt t (caseDc d (KcX rs l₁ pt₁ b κX g pg₁) (ScX rs l₁ pt₁ b κX g pg₁) (AcX rs l₁ pt₁ b κX g pg₁))
                (G aj lj t qo b′ (caseDc d″ (KcX rs′ l₂ pj₂ (top b⊥ j) κX′ g′ pg₂) (ScX rs′ l₂ pj₂ (top b⊥ j) κX′ g′ pg₂) (AcX rs′ l₂ pj₂ (top b⊥ j) κX′ g′ pg₂)))
  -- 第一步留下 (k < j)
  rΩΩX rs rs′ {B₁} {W₂} l₁ l₂ w {j} (acc rsj) lj pj₂ {t} pt₁ qo pp {b} {b′} B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C {d} D (dk κ₁ e₁ fr₁ ft₁ u₁) mx my h =
    ΦΩ rsj lj qo b′ κ₁ (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c))
      (λ z → LeAt t (caseDc d (KcX rs l₁ pt₁ b κX g pg₁) (ScX rs l₁ pt₁ b κX g pg₁) (AcX rs l₁ pt₁ b κX g pg₁)) z)
      (rKX rs rs′ l₁ l₂ w rsj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk K₁ K₂ C κ₁ fr₁ (s⊲→Pp u₁)
         (toK j κ₁) e₁ ft₁ (pK j κ₁) D (cmpB (pK j κ₁) qo tt lj) mx my h)
  -- 第一步同层 (k = j)
  rΩΩX rs rs′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C (dk κ₁ e₁ fr₁ ft₁ u) ds mx my h = ⊥-elim (nos′ u (pp→⊲ pp))
  rΩΩX rs rs′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C ds ds mx my h = ⊥-elim (noPP pp hself)
  rΩΩX rs rs′ {B₁} {W₂} l₁ l₂ w {j} aj lj pj₂ {t} pt₁ qo pp {b} {b′} B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C (da qL ppL) ds mx my h =
    monoΦ (apWf j) (rs b⊥ j lx) aj (lg↓ pk l₁) lj qL qo B
      (hl (chain (top b⊥ j) (λ b₂ → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ b₂ b₂)))
      (moChT (acc rs) l₁ κX (⊏⊑ pk) g pg₁ to K₁ mx) (moChT (acc rs′) l₂ κX′ pj₂ g′ pg₂ to′ K₂ my)
      (chT (acc rs) (acc rs′) l₁ l₂ w (⊏⊑ pk) pj₂ κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h)
  -- 第一步在上 (j < k)
  rΩΩX rs rs′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C (dk κ₁ e₁ fr₁ ft₁ u) (da q₁ pp₁) mx my h =
    ⊥-elim (nos (⊲ᴮ-tr u (⊲ᴮ-tr (pp→⊲ pp) q₁)))
  rΩΩX rs rs′ l₁ l₂ w aj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk pk′ K₁ K₂ C ds (da q₁ pp₁) mx my h = ⊥-elim (noPP pp q₁)
  rΩΩX rs rs′ {B₁} {W₂} l₁ l₂ w {j} aj lj pj₂ {t} pt₁ qo pp {b} {b′} B κX κX′ g g′ pg₁ pg₂ {k} to to′ pk pk′ K₁ K₂ C (da qL ppL) (da q₁ pp₁) mx my h =
    route (apWf k) pp₁ (rs b⊥ k lx) (rs′ b⊥ k lx) (lg↓ pk l₁) (lg↓ pk′ l₂) aj lj q₁ qL qo pp B
      (hl (chain (top b⊥ k) (λ b₂ → brT (acc rs′) l₂ (⊏⊑ pk′) κX′ g′ pg₂ to′ b₂ b₂)))
      (moChT (acc rs) l₁ κX (⊏⊑ pk) g pg₁ to K₁ mx) (moChT (acc rs′) l₂ κX′ (⊏⊑ pk′) g′ pg₂ to′ K₂ my)
      (chT (acc rs) (acc rs′) l₁ l₂ w (⊏⊑ pk) (⊏⊑ pk′) κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h)
```

**第一步留下之后**: 留下的种类 $\kappa_1$ 在第 $j$ 层, 层是 $k$; 第二步 (第 $j$ 层折到 $t$) 的决定与左边 ($\Omega_1$ 层折到 $t$) 的决定一致. 逐点用跨底路线引理 (`rPt`).

```agda
  rPt : ∀ (a a′ : Acc bX hz) {B₁ W₂} (l₁ : LgB B₁) (l₂ : LgB W₂) → LeAt hz B₁ W₂ →
        ∀ {j} (aj : Acc b⊥ j) (lj : LgB j) (pj₂ : j ⊲ W₂) {s} (ps₁ : s ⊲ B₁) (qo : s ⊲ j) (pp : Pp s j) {b₁ b₂} → Ac0.Bnd s b₁ b₂ →
        ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt W₂ κX′ g′) {k}
        (to : H k → E XS κX) (to′ : H k → E XS κX′) (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ →
        MoT κX k to g → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
        ∀ d₁ d₂ → MoAt k d₁ → MoAt k d₂ → LeAt k d₁ d₂ →
        LeAt s (brT a l₁ ps₁ κX g pg₁ to b₁ d₁) (G aj lj s qo b₂ (brT a′ l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) d₂))
  rPt a a′ {B₁} {W₂} l₁ l₂ w aj lj pj₂ ps₁ qo pp Bb κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h d₁ d₂ m1 m2 le =
    routeX a a′ (lgE κX l₁ (to d₁)) (lgE κX′ l₂ (to′ d₂)) (nC C l₁ l₂ w le) aj lj (ptE κX′ l₂ pj₂ (to′ d₂))
      (ptE κX l₁ ps₁ (to d₁)) qo pp Bb (g′ (psh (P κX′) W₂ (to′ d₂))) (pgE κX l₁ pg₁ (to d₁)) (pgE κX′ l₂ pg₂ (to′ d₂))
      (brMoT K₁ g B₁ mx d₁ m1) (brMoT K₂ g′ W₂ my d₂ m2) (brLeT C g g′ B₁ W₂ w my h d₁ d₂ m1 m2 le)

  moBrJ : ∀ (a′ : Acc bX hz) {W₂} (l₂ : LgB W₂) {j} (pj₂ : j ⊲ W₂) κX′ (g′ : E XS κX′ → HX) (pg₂ : PGt W₂ κX′ g′) {k}
          (to′ : H k → E XS κX′) → KD κX′ k to′ → MoT κX′ k to′ g′ → ∀ d → MoAt k d →
          MoAt j (brT a′ l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) d)
  moBrJ a′ {W₂} l₂ {j} pj₂ κX′ g′ pg₂ to′ K₂ my d md =
    MoXΦ a′ (lgE κX′ l₂ (to′ d)) (ptE κX′ l₂ pj₂ (to′ d)) (Mo-top j) (L.≤-refl j _) (g′ (psh (P κX′) W₂ (to′ d))) (pgE κX′ l₂ pg₂ (to′ d))
      (brMoT K₂ g′ W₂ my d md)

  rKX : ∀ rs rs′ {B₁ W₂} (l₁ : LgB B₁) (l₂ : LgB W₂) → LeAt hz B₁ W₂ →
        ∀ {j} rsj (lj : LgB j) (pj₂ : j ⊲ W₂) {t} (pt₁ : t ⊲ B₁) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
        ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt W₂ κX′ g′) {k}
        (to : H k → E XS κX) (to′ : H k → E XS κX′) (pk : hs k ⊲ B₁)
        (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ →
        (κ₁ : K (T j)) (fr₁ : E (T j) κ₁ → H k) → Pp k j →
        ∀ {k₁} (to₁ : H k₁ → E (T j) κ₁) (e₁ : k₁ ≡ k) → (∀ c → fr₁ (to₁ c) ≡ subst H e₁ c) → (pk₁ : hs k₁ ⊲ j) →
        ∀ {d} → DV k t to pk d → (r₁ : (t ⊲ hs k₁) ⊎ (hs k₁ ⊲ t)) →
        MoT κX k to g → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
        LeAt t (caseDc d (KcX rs l₁ pt₁ b κX g pg₁) (ScX rs l₁ pt₁ b κX g pg₁) (AcX rs l₁ pt₁ b κX g pg₁))
               (caseDc (pick S⊥ to₁ pk₁ r₁) (Kc rsj lj (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)) qo b′)
                          (Sc rsj lj (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)) qo b′)
                          (Ac rsj lj (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)) qo b′))
  rKX rs rs′ l₁ l₂ w rsj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk K₁ K₂ C κ₁ fr₁ pkj to₁ refl ft pk₁ (dk κL eL frL ftL uL) r₁ mx my h =
    rKkX rs rs′ l₁ l₂ w rsj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C κ₁ fr₁ pkj to₁ ft pk₁ κL eL frL ftL uL (dv to₁ pk₁ r₁) mx my h
  rKX rs rs′ {B₁} {W₂} l₁ l₂ w {j} rsj lj pj₂ {t} pt₁ qo pp {b} {b′} B κX κX′ g g′ pg₁ pg₂ to to′ pk K₁ K₂ C κ₁ fr₁ pkj to₁ refl ft pk₁ ds r₁ mx my h =
    subst (λ z → LeAt t (ScX rs l₁ pt₁ b κX g pg₁ to) (caseDc z (Kc rsj lj G1 qo b′) (Sc rsj lj G1 qo b′) (Ac rsj lj G1 qo b′)))
      (sym (sameR to₁ pk₁ r₁))
      (Ac0.chLe-hl t (λ b₁ → brT (acc rs) l₁ pt₁ κX g pg₁ to b₁ b₁) kR B (kpT (acc rs) l₁ κX pt₁ g pg₁ to K₁ mx)
        (λ b₂ m2 t2 → MoΦ (apWf j) (acc rsj) lj qo m2 t2 (G1 (to₁ b₂))
           (subst (λ z → MoAt j (brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) z)) (sym (ft b₂))
             (moBrJ (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ K₂ my b₂ m2)))
        (λ {b₁} {b₂} Bb@(m1 , m2 , t1 , le) →
           subst (λ z → LeAt t (brT (acc rs) l₁ pt₁ κX g pg₁ to b₁ b₁) (G (acc rsj) lj t qo b₂ (brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) z)))
             (sym (ft b₂))
             (rPt (acc rs) (acc rs′) l₁ l₂ w (acc rsj) lj pj₂ pt₁ qo pp Bb κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h b₁ b₂ m1 m2 le)))
    where
    G1 : E (T j) κ₁ → H j
    G1 c = brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)
    kR : H t → H t
    kR b₂ = G (acc rsj) lj t qo b₂ (G1 (to₁ b₂))
  rKX rs rs′ l₁ l₂ w rsj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk K₁ K₂ C κ₁ fr₁ pkj to₁ refl ft pk₁ (da qL ppL) r₁ mx my h =
    rKaX rs rs′ l₁ l₂ w rsj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk K₁ K₂ C κ₁ fr₁ pkj to₁ ft pk₁ qL ppL (dv to₁ pk₁ r₁) mx my h

  rKkX : ∀ rs rs′ {B₁ W₂} (l₁ : LgB B₁) (l₂ : LgB W₂) → LeAt hz B₁ W₂ →
         ∀ {j} rsj (lj : LgB j) (pj₂ : j ⊲ W₂) {t} (pt₁ : t ⊲ B₁) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
         ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt W₂ κX′ g′) {k}
         (to : H k → E XS κX) (to′ : H k → E XS κX′) (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ →
         (κ₁ : K (T j)) (fr₁ : E (T j) κ₁ → H k) → Pp k j →
         (to₁ : H k → E (T j) κ₁) → (∀ c → fr₁ (to₁ c) ≡ c) → (pk₁ : hs k ⊲ j) →
         (κL : K (T t)) (eL : lvK t κL ≡ k) (frL : E (T t) κL → H k) → (∀ c → frL (toK t κL c) ≡ subst H eL c) → hs k ⊲ t →
         ∀ {d₁} → DV k t to₁ pk₁ d₁ →
         MoT κX k to g → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
         LeAt t (KcX rs l₁ pt₁ b κX g pg₁ κL (λ c → to (frL c)))
                (caseDc d₁ (Kc rsj lj (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)) qo b′)
                           (Sc rsj lj (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)) qo b′)
                           (Ac rsj lj (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)) qo b′))
  rKkX rs rs′ {B₁} {W₂} l₁ l₂ w {j} rsj lj pj₂ {t} pt₁ qo pp {b} {b′} B κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C κ₁ fr₁ pkj to₁ ft pk₁ κL eL frL ftL uL
     (dk κR eR frR ftR uR) mx my h =
    keepKK t κL κR eL eR frL frR ftL ftR (brT (acc rs) l₁ pt₁ κX g pg₁ to b)
      (λ c → G (acc rsj) lj t qo b′ (brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ (to₁ c))))
      (λ c mc → subst (λ z → LeAt t (brT (acc rs) l₁ pt₁ κX g pg₁ to b c) (G (acc rsj) lj t qo b′ (brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) z)))
         (sym (ft c))
         (rPt (acc rs) (acc rs′) l₁ l₂ w (acc rsj) lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h c c mc mc (L.≤-refl _ c)))
  rKkX rs rs′ l₁ l₂ w rsj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C κ₁ fr₁ pkj to₁ ft pk₁ κL eL frL ftL uL ds mx my h =
    ⊥-elim (nos uL)
  rKkX rs rs′ l₁ l₂ w rsj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C κ₁ fr₁ pkj to₁ ft pk₁ κL eL frL ftL uL (da q pq) mx my h =
    ⊥-elim (nos′ uL q)

  rKaX : ∀ rs rs′ {B₁ W₂} (l₁ : LgB B₁) (l₂ : LgB W₂) → LeAt hz B₁ W₂ →
         ∀ {j} rsj (lj : LgB j) (pj₂ : j ⊲ W₂) {t} (pt₁ : t ⊲ B₁) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
         ∀ κX κX′ (g : E XS κX → HX) (g′ : E XS κX′ → HX) (pg₁ : PGt B₁ κX g) (pg₂ : PGt W₂ κX′ g′) {k}
         (to : H k → E XS κX) (to′ : H k → E XS κX′) (pk : hs k ⊲ B₁)
         (K₁ : KD κX k to) (K₂ : KD κX′ k to′) → KC K₁ K₂ →
         (κ₁ : K (T j)) (fr₁ : E (T j) κ₁ → H k) → Pp k j →
         (to₁ : H k → E (T j) κ₁) → (∀ c → fr₁ (to₁ c) ≡ c) → (pk₁ : hs k ⊲ j) →
         (qL : t ⊲ k) → Pp t k →
         ∀ {d₁} → DV k t to₁ pk₁ d₁ →
         MoT κX k to g → MoT κX′ k to′ g′ → (∀ c → MoAt k c → g (to c) ≤X g′ (to′ c)) →
         LeAt t (AcX rs l₁ pt₁ b κX g pg₁ k pk qL to)
                (caseDc d₁ (Kc rsj lj (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)) qo b′)
                           (Sc rsj lj (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)) qo b′)
                           (Ac rsj lj (λ c → brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ c)) qo b′))
  rKaX rs rs′ l₁ l₂ w rsj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk K₁ K₂ C κ₁ fr₁ pkj to₁ ft pk₁ qL ppL (dk κR eR frR ftR uR) mx my h =
    ⊥-elim (nos′ uR qL)
  rKaX rs rs′ l₁ l₂ w rsj lj pj₂ pt₁ qo pp B κX κX′ g g′ pg₁ pg₂ to to′ pk K₁ K₂ C κ₁ fr₁ pkj to₁ ft pk₁ qL ppL ds mx my h =
    ⊥-elim (noPP ppL hself)
  rKaX rs rs′ {B₁} {W₂} l₁ l₂ w {j} rsj lj pj₂ {t} pt₁ qo pp {b} {b′} B κX κX′ g g′ pg₁ pg₂ {k} to to′ pk K₁ K₂ C κ₁ fr₁ pkj to₁ ft pk₁ qL ppL
     (da qR ppR) mx my h =
    monoΦ (apWf k) (rs b⊥ k lx) (rsj b⊥ k (lt pk₁)) (lg↓ pk l₁) (lg↓ pk₁ lj) qL qR B
      (hl (chain (top b⊥ k) kR))
      (moChT (acc rs) l₁ κX (⊏⊑ pk) g pg₁ to K₁ mx)
      (Ac0.chM k (top b⊥ k) kR (Mo-top k) (L.≤-refl k _) KPR)
      (Ac0.chLe-hl k (λ b₁ → brT (acc rs) l₁ (⊏⊑ pk) κX g pg₁ to b₁ b₁) kR (Ac0.bnd-refl k (Mo-top k) (L.≤-refl k _))
         (kpT (acc rs) l₁ κX (⊏⊑ pk) g pg₁ to K₁ mx) KPR
         (λ {b₁} {b₂} Bb@(m1 , m2 , t1 , le) →
            subst (λ z → LeAt k (brT (acc rs) l₁ (⊏⊑ pk) κX g pg₁ to b₁ b₁)
                                (G (acc rsj) lj k (⊏⊑ pk₁) b₂ (brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) z)))
              (sym (ft b₂))
              (rPt (acc rs) (acc rs′) l₁ l₂ w (acc rsj) lj pj₂ (⊏⊑ pk) (⊏⊑ pk₁) pkj Bb κX κX′ g g′ pg₁ pg₂ to to′ K₁ K₂ C mx my h b₁ b₂ m1 m2 le)))
    where
    kR : H k → H k
    kR b₂ = G (acc rsj) lj k (⊏⊑ pk₁) b₂ (brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ (to₁ b₂)))
    KPR : Ac0.KP k kR
    KPR b₂ m2 t2 = MoΦ (apWf j) (acc rsj) lj (⊏⊑ pk₁) m2 t2 (brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) (fr₁ (to₁ b₂)))
      (subst (λ z → MoAt j (brT (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ (top b⊥ j) z)) (sym (ft b₂))
        (moBrJ (acc rs′) l₂ pj₂ κX′ g′ pg₂ to′ K₂ my b₂ m2))
```


## 结论 (按档)

- **[条件定理, 条件: `Cd` 上的 UIP 与 `ShLaw I`]** 对一切 `I`: **`monoX`** (跨底折叠对世界、界、输入联合单调, 两边的种类、路径、证据可不同), **`routeX`** (跨底路线引理, 目标是中间层的真第一位置), **`brX`** (回灌坐标处的分支不高于结点), **`MoXΦ`** (保值合法); 辅助 `mΩ1X`, `mΩΩX`, `mΩΩkX`, `mΩΩaX`, `rΩΩX`, `rKX`, `rKkX`, `rKaX`, `ptCmp`, `rPt`, `moBrJ`, `kpT`, `moChT`, `chT`, `kpX`, `moChX`; **`kcC`** (同分量两个种类的坐标数据联合单调; 分量 0 处用 UIP).
- 视图 `dvX`; 其余记法与引理在 [ValXBase](ValXBase.lagda.md).
