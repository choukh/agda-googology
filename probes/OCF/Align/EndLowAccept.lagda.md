# 终点下界: 主线不低于 EBO 的参照树 (验收)

> **验收文件.** 读记号: EBO 的项、`cof`、`fsn`、`fsT`、`γT`, 标签 `Lab` 与参照树 `WfFsn.EBO-tree`. 入口 [EndLow](EndLow.lagda.md). 主线的定义不在这里, 这里只比较.
>
> 编译要归档拷贝 (同 [WfFsn](WfFsn.lagda.md) §4). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EndLowAccept where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; m≤m+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import OCF.Align.Level
  using (Ordᶜ; zero; suc; lim; limᵢ; up; _≅_; z≅; s≅; l≅; ≅-sym; ≅-trans; FGH; iter-ext)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≅→≼; ≼-suc)
-- 记号与标签
import OCF.Align.EBO as E
open E using (T; ψ; 𝟏; cof; cofA; c0; c1; cω; cΩ; fsn; fsT; fsT0; γT; Ωt; natT; ΩTower; EBOψ; trm; dec)
open import OCF.Align.Correspond using (Lab; l0; l1; lω)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.NoCumsum using (BTBOᴵ)
open import OCF.Align.WfFsn using (EBO-tree; ebo-lab; module S)
open import OCF.Align.AccTreeLab using (treeᴴ)
-- 主线 (差树与高度树)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.TLRuleVar using (trA)
import OCF.Align.HtFeedClosed as HC
open import OCF.Align.HtFeedTree using (H)
open import OCF.Align.HtOutFeed using (T-fb; T-fbω; Λs; Λω; lΛω)
open import OCF.Align.HtCrossSim using (Funext)
open import OCF.Align.HtCrossInst using (module Hl)
-- 已有的验收 (ψ₀(Ω_Ω) 一站)
open import OCF.Align.SumOneClosed using (T₀; T₁)
open import OCF.Align.SumOneAccept using (T₀≈; step-T₁)
open import OCF.Align.TLRuleSum using (Top)
import OCF.Align.TLRuleSum as TS
open import OCF.Align.CumUpAcceptSim using (fr)
open import OCF.Align.TLRuleAccept using (T≈)
```

## §1 桥: 主线的闭项到 `OCF.Align.Level` 的第 0 层

主线闭项在 `A` 里 (`CumReadCF`), 经 `HtFeedClosed.ord` 到 `OCF.Free.Level` 的第 0 层. 第 0 层只有 `zero`, `suc`, `lim`, 所以到 `OCF.Align.Level` 的第 0 层是逐构造子的换名 `⟪_⟫`. 现成的同类映射: `TLRuleVar.trA` ($=$ `fr ∘ TLRuleSum.ord`), `CumUpAcceptSim.fr`, `Free.Bridge.⟦_⟧`; 它们与 `⟪_⟫` 互模拟 (`⟪⟫≅trA`, `⟪⟫≅fr`), 所以已有的 `trA` 上的验收直接搬过来.

**保持与反射.** 树侧的值序是 `TLRuleSpec._≤_` (同形的四个构造子). `≤→≼ᴬ` 是保持. 反射 `≼→≤ᴬ` 经回程 `bk`: 第 0 层的 $\preccurlyeq$ 推导里没有 `≼i`, `i≼`, `≼u`, `u≼` (没有 $j<^\mathsf I 0$, 也没有 $k\triangleleft_1 0$), 对推导递归即得 `bk x ≤ bk y`; `bk ⟪ a ⟫` 与 $a$ 不是字面相等 (极限处要函数外延), 但互相 $\le$ (`bk⟪⟫≤`, `≤bk⟪⟫`).

```agda
⟪_⟫ : A → Ordᶜ zero
⟪ azero ⟫ = zero
⟪ asuc a ⟫ = suc ⟪ a ⟫
⟪ alim f ⟫ = lim (λ n → ⟪ f n ⟫)

⟪⟫≅trA : ∀ a → ⟪ a ⟫ ≅ trA a
⟪⟫≅trA azero = z≅
⟪⟫≅trA (asuc a) = s≅ (⟪⟫≅trA a)
⟪⟫≅trA (alim f) = l≅ (λ n → ⟪⟫≅trA (f n))

⟪⟫≅fr : ∀ a → ⟪ a ⟫ ≅ fr (HC.ord a)
⟪⟫≅fr azero = z≅
⟪⟫≅fr (asuc a) = s≅ (⟪⟫≅fr a)
⟪⟫≅fr (alim f) = l≅ (λ n → ⟪⟫≅fr (f n))

⟪⟫≅frT : ∀ a → ⟪ a ⟫ ≅ fr (TS.ord a)
⟪⟫≅frT azero = z≅
⟪⟫≅frT (asuc a) = s≅ (⟪⟫≅frT a)
⟪⟫≅frT (alim f) = l≅ (λ n → ⟪⟫≅frT (f n))

-- 换名不改 FGH (副产品; 终点只管序数, FGH 不是目标)
fgh-⟪⟫ : ∀ a n → FL.FGH (HC.ord a) n ≡ FGH ⟪ a ⟫ n
fgh-⟪⟫ azero n = refl
fgh-⟪⟫ (asuc a) n = FL.iter-ext (fgh-⟪⟫ a) n n
fgh-⟪⟫ (alim f) n = fgh-⟪⟫ (f n) n

≤→≼ᴬ : ∀ {a b} → a ≤ b → ⟪ a ⟫ ≼ ⟪ b ⟫
≤→≼ᴬ z≤ = z≼
≤→≼ᴬ (s≤ p) = s≼s (≤→≼ᴬ p)
≤→≼ᴬ (≤l n p) = ≼l n (≤→≼ᴬ p)
≤→≼ᴬ (l≤ p) = l≼ (λ n → ≤→≼ᴬ (p n))

bk : Ordᶜ zero → A
bk zero = azero
bk (suc x) = asuc (bk x)
bk (lim f) = alim (λ n → bk (f n))
bk (limᵢ () f)
bk (up () x)

≼→≤ᵇ : ∀ {x y : Ordᶜ zero} → x ≼ y → bk x ≤ bk y
≼→≤ᵇ z≼ = z≤
≼→≤ᵇ (s≼s p) = s≤ (≼→≤ᵇ p)
≼→≤ᵇ (≼l n p) = ≤l n (≼→≤ᵇ p)
≼→≤ᵇ (l≼ p) = l≤ (λ n → ≼→≤ᵇ (p n))
≼→≤ᵇ (≼i {p = ()} x ex p)
≼→≤ᵇ (i≼ {p = ()} p)
≼→≤ᵇ (≼u {r = ()} p)
≼→≤ᵇ (u≼ {r = ()} p)

bk⟪⟫≤ : ∀ a → bk ⟪ a ⟫ ≤ a
bk⟪⟫≤ azero = z≤
bk⟪⟫≤ (asuc a) = s≤ (bk⟪⟫≤ a)
bk⟪⟫≤ (alim f) = l≤ (λ n → ≤l n (bk⟪⟫≤ (f n)))

≤bk⟪⟫ : ∀ a → a ≤ bk ⟪ a ⟫
≤bk⟪⟫ azero = z≤
≤bk⟪⟫ (asuc a) = s≤ (≤bk⟪⟫ a)
≤bk⟪⟫ (alim f) = l≤ (λ n → ≤l n (≤bk⟪⟫ (f n)))

≼→≤ᴬ : ∀ {a b} → ⟪ a ⟫ ≼ ⟪ b ⟫ → a ≤ b
≼→≤ᴬ {a} {b} p = ≤-trans (≤bk⟪⟫ a) (≤-trans (≼→≤ᵇ p) (bk⟪⟫≤ b))
```

## §2 参照树沿 Ω-塔

`treeE k` 是 `WfFsn` 给 $\psi_0(\Omega\text{-塔}_k)$ 的带标签树, `EBO-tree` 是它们的 ℕ-极限. $\Omega\text{-塔}_0=1$, $\Omega\text{-塔}_{k+1}=\Omega_{\Omega\text{-塔}_k}$; 所以 `treeE 0`, `treeE 1`, `treeE 2`, `treeE 3` 读 $\psi_0(1)=\omega$, $\psi_0(\Omega)$, $\psi_0(\Omega_\Omega)$, $\psi_0(\Omega_{\Omega_\Omega})$.

**`treeE` 放进 `opaque`.** 这棵树是沿良基证明 (`hc`, 归档的可达性) 算出来的; 类型检查器比较两个头不同的项时先化到弱头范式, 对 `treeE (suc k)` 那会把良基证明展开到堆耗尽 (实测, 12G). 所以只在 `opaque` 里展开一次, 导出三条接口: 标签 `treeE-lab`, `treeE≼EBO`, `EBO≼`. 这只是工程上的封装, 不改任何陈述.

```agda
opaque
  treeE : ℕ → Ordᶜ zero
  treeE k = treeᴴ (S.hc (S.p-tower k))

  treeE-lab : ∀ k → Lab (treeE k) (EBOψ k)
  treeE-lab k = ebo-lab k

  treeE≼EBO : ∀ k → treeE k ≼ EBO-tree
  treeE≼EBO k = ≼l k (≼-refl _)

  EBO≼ : ∀ {ℓ} {X : Ordᶜ ℓ} → (∀ k → treeE k ≼ X) → EBO-tree ≼ X
  EBO≼ h = l≼ h
```

**塔的第 0 个基本列项是下一级 (`fs-tower0`, 对一切 $k$).** 记号侧的句法事实: $\Omega\text{-塔}_{k+1}$ 的共尾度是 $\Omega_1$ (`cof-tower`), 所以 $\psi_0(\Omega\text{-塔}_{k+1})$ 走规则 6 的 γ-链, $\gamma_0=\Omega_0=1$; Ω-基本列沿塔是 $\eta\mapsto\Omega^{(k)}_\eta$ (`fsT-tower`), 代入 $\gamma_0$ 正好是 $\Omega\text{-塔}_k$. 带证书的基本列化到裸值用 EBO §6 的 `fsT↓-trm`, `γ↓-trm`.

```agda
Ω^ : ℕ → T → T
Ω^ zero η = η
Ω^ (suc k) η = Ωt (Ω^ k η)

cof-tower : ∀ k → cof (ΩTower (suc k)) ≡ cΩ []
cof-tower zero = refl
cof-tower (suc k) = cong (E.cofψ0 (ΩTower (suc k))) (cof-tower k)

fsT0-Ω : ∀ u c η → c ≡ cΩ [] → fsT0 u c η ≡ Ωt (fsT u η)
fsT0-Ω u .(cΩ []) η refl = refl

fsT-tower : ∀ k η → fsT (ΩTower (suc k)) η ≡ Ω^ k η
fsT-tower zero η = refl
fsT-tower (suc k) η = trans (fsT0-Ω (ΩTower (suc k)) (cof (ΩTower (suc k))) η (cof-tower k)) (cong Ωt (fsT-tower k η))

tower≡ : ∀ k → Ω^ k (natT 1) ≡ ΩTower k
tower≡ zero = refl
tower≡ (suc k) = cong Ωt (tower≡ k)

fs6 : ∀ y ys c (be : cof (y ∷ ys) ≡ c) → c ≡ cΩ [] → ∀ n →
      trm (E.fsn↓₊ [] y ys c be n) ≡ ψ [] (fsT (y ∷ ys) (γT (y ∷ ys) [] n)) ∷ []
fs6 y ys .(cΩ []) be refl n = cong (λ z → ψ [] z ∷ [])
  (trans (E.fsT↓-trm (y ∷ ys) be (dec (E.γ↓ (y ∷ ys) [] be n))) (cong (fsT (y ∷ ys)) (E.γ↓-trm (y ∷ ys) [] be n)))

fs-tower0 : ∀ k → fsn (EBOψ (suc k)) 0 ≡ EBOψ k
fs-tower0 k = trans (fs6 (ψ (ΩTower k) []) [] (cof (ΩTower (suc k))) refl (cof-tower k) 0)
                    (cong (λ z → ψ [] z ∷ []) (trans (fsT-tower k (Ωt [])) (tower≡ k)))

cof-EBOψ : ∀ k → cof (EBOψ k) ≡ cω
cof-EBOψ zero = refl
cof-EBOψ (suc k) = cong (cofA []) (cof-tower k)
```

**整条基本列: 第 $k+1$ 级是 $G_k:x\mapsto\psi_0(\Omega^{(k)}_x)$ 从 $1$ 起的 ω-迭代** (`fs-tower`, `γ-iter`, `γ0`). $\gamma_0=1$, $\gamma_{n+1}=G_k(\gamma_n)$, 而 $\psi_0(\Omega\text{-塔}_{k+1})[n]=G_k(\gamma_n)=\gamma_{n+1}$. $k=1$: $G_1(x)=\psi_0(\Omega_x)$, 这是 BTBO 的链; $k=2$: $G_2(x)=\psi_0(\Omega_{\Omega_x})$. 归纳步从第 $k+1$ 级到第 $k+2$ 级, 要的就是主线上一个不低于 $G_{k+1}$ 的算子 (下面 `step-shape`).

```agda
G : ℕ → T → T
G k x = ψ [] (Ω^ k x) ∷ []

γk : ℕ → ℕ → T
γk k n = γT (ΩTower (suc k)) [] n

γ0 : ∀ k → γk k 0 ≡ natT 1
γ0 k = refl

γ-iter : ∀ k n → γk k (suc n) ≡ G k (γk k n)
γ-iter k n = cong (λ z → ψ [] z ∷ []) (fsT-tower k (γk k n))

fs-tower : ∀ k n → fsn (EBOψ (suc k)) n ≡ G k (γk k n)
fs-tower k n = trans (fs6 (ψ (ΩTower k) []) [] (cof (ΩTower (suc k))) refl (cof-tower k) n)
                     (cong (λ z → ψ [] z ∷ []) (fsT-tower k (γk k n)))
```

**由标签读出单调.** `lab-fs≼`: $X$ 标 $t$, $t$ 的共尾度为 $\omega$, $Y$ 标 $t[n]$, 则 $Y\preccurlyeq X$ (标签唯一 `Lab-uniq` 加 `≼l`). 于是参照树沿塔单调 (`treeE-mono`), `EBO-tree` 是它们的上确界, 而且 "`EBO-tree` $\preccurlyeq X$" **恰好**等价于 "对一切 $k$, `treeE k` $\preccurlyeq X$", 也等价于 "对一切 $k\ge K$" (`EBO≼`, `EBO≼⁻`, `EBO≼-from`). 终点下界就是这些逐级的下界, 不多不少.

```agda
lab-fs≼ : ∀ {X Y t} → Lab X t → cof t ≡ cω → ∀ n → Lab Y (fsn t n) → Y ≼ X
lab-fs≼ (l0 c e) ce n ly with trans (sym c) ce
... | ()
lab-fs≼ (l1 c e l) ce n ly with trans (sym c) ce
... | ()
lab-fs≼ (lω c e h) ce n ly = ≼-trans (≅→≼ (Lab-uniq ly (h n))) (≼-trans (≼l n (≼-refl _)) (≅→≼ (≅-sym e)))

lab-lim≼ : ∀ {ℓ} {X t} {Z : Ordᶜ ℓ} → Lab X t → cof t ≡ cω →
           (∀ n → Σ (Ordᶜ zero) (λ Y → Lab Y (fsn t n) × Y ≼ Z)) → X ≼ Z
lab-lim≼ (l0 c e) ce h with trans (sym c) ce
... | ()
lab-lim≼ (l1 c e l) ce h with trans (sym c) ce
... | ()
lab-lim≼ (lω c e hl) ce h =
  ≼-trans (≅→≼ e) (l≼ (λ n → ≼-trans (≅→≼ (Lab-uniq (hl n) (proj₁ (proj₂ (h n))))) (proj₂ (proj₂ (h n)))))

-- 归纳步的形状: 第 k+1 级 ≼ Z 恰要 Z 不低于 G_k(γ_n) 的 (任一) 带标签树, 对一切 n
step-shape : ∀ k {ℓ} {Z : Ordᶜ ℓ} → (∀ n → Σ (Ordᶜ zero) (λ Y → Lab Y (G k (γk k n)) × Y ≼ Z)) → treeE (suc k) ≼ Z
step-shape k h = lab-lim≼ (treeE-lab (suc k)) (cof-EBOψ (suc k))
  (λ n → proj₁ (h n) , subst (Lab (proj₁ (h n))) (sym (fs-tower k n)) (proj₁ (proj₂ (h n))) , proj₂ (proj₂ (h n)))

lab-fs0 : ∀ k → Lab (treeE k) (fsn (EBOψ (suc k)) 0)
lab-fs0 k = subst (Lab (treeE k)) (sym (fs-tower0 k)) (treeE-lab k)

treeE-mono : ∀ k → treeE k ≼ treeE (suc k)
treeE-mono k = lab-fs≼ (treeE-lab (suc k)) (cof-EBOψ (suc k)) 0 (lab-fs0 k)

treeE-+ : ∀ d a → treeE a ≼ treeE (d + a)
treeE-+ zero a = ≼-refl _
treeE-+ (suc d) a = ≼-trans (treeE-+ d a) (treeE-mono (d + a))

diff : ∀ {j k} → j ≤ℕ k → Σ ℕ (λ d → k ≡ d + j)
diff {k = k} z≤n = k , sym (+-identityʳ k)
diff (s≤s {m} p) with diff p
... | d , refl = d , sym (+-suc d m)

treeE-≤ : ∀ {j k} → j ≤ℕ k → treeE j ≼ treeE k
treeE-≤ {j} p with diff p
... | d , refl = treeE-+ d j

EBO≼⁻ : ∀ {ℓ} {X : Ordᶜ ℓ} → EBO-tree ≼ X → ∀ k → treeE k ≼ X
EBO≼⁻ p k = ≼-trans (treeE≼EBO k) p

EBO≼-from : ∀ {ℓ} {X : Ordᶜ ℓ} K → (∀ k → treeE (k + K) ≼ X) → EBO-tree ≼ X
EBO≼-from K h = EBO≼ (λ k → ≼-trans (treeE-≤ (m≤m+n k K)) (h k))
```

**第 2 级就是 BTBO.** `treeE 2` 与 NoCumsum 的 `BTBOᴵ` 带同一个标签 $\psi_0(\Omega_\Omega)$, 所以互模拟.

```agda
treeE2≅ : treeE 2 ≅ BTBOᴵ
treeE2≅ = Lab-uniq (treeE-lab 2) BTBO-label

treeE≤2 : ∀ k → k ≤ℕ 2 → treeE k ≼ BTBOᴵ
treeE≤2 k p = ≼-trans (treeE-≤ p) (≅→≼ treeE2≅)
```

## §3 第 0, 1, 2 级: 主线差树的闭项, 无条件

`SumOneAccept.T₀≈` ($\psi_0(\Omega_\Omega)$ 一站的序数值验收) 与 `TLRuleAccept.T≈` 搬过来: 差树的这两个闭项不低于 `treeE 0`, `treeE 1`, `treeE 2`, 第 2 级互相 $\preccurlyeq$ (`T₀≈E`, `Top≈E`); `T₁` 严格高于第 2 级 (`E<T₁`). 第 3 级以上这两族没有闭项 (它们只到 $\psi_0(\Omega_{\Omega+1})$ 附近, 读法).

```agda
T₀≈E : ⟪ T₀ ⟫ ≈ᵛ treeE 2
T₀≈E = ≼-trans (≅→≼ (⟪⟫≅trA T₀)) (≼-trans (proj₁ T₀≈) (≅→≼ (≅-sym treeE2≅))) ,
       ≼-trans (≅→≼ treeE2≅) (≼-trans (proj₂ T₀≈) (≅→≼ (≅-sym (⟪⟫≅trA T₀))))

low-T₀ : ∀ k → k ≤ℕ 2 → treeE k ≼ ⟪ T₀ ⟫
low-T₀ k p = ≼-trans (treeE-≤ p) (proj₂ T₀≈E)

E<T₁ : suc (treeE 2) ≼ ⟪ T₁ ⟫
E<T₁ = ≼-trans (s≼s (≅→≼ treeE2≅)) (≼-trans step-T₁ (≅→≼ (≅-sym (⟪⟫≅trA T₁))))

Top≈E : ⟪ Top ⟫ ≈ᵛ treeE 2
Top≈E = ≼-trans (≅→≼ (⟪⟫≅frT Top)) (≼-trans (proj₁ T≈) (≅→≼ (≅-sym treeE2≅))) ,
        ≼-trans (≅→≼ treeE2≅) (≼-trans (proj₂ T≈) (≅→≼ (≅-sym (⟪⟫≅frT Top))))

low-Top : ∀ k → k ≤ℕ 2 → treeE k ≼ ⟪ Top ⟫
low-Top k p = ≼-trans (treeE-≤ p) (proj₂ Top≈E)
```

## §4 第 0, 1, 2 级: 回灌高度的闭项, 条件定理

主线现在的闭项是高度树一族 (`HtFeed`, `HtOut`). 它们**没有一站**与参照树有 $\preccurlyeq$. 这里把缺的东西写成模块参数, 类型原样:

- `Acc₁ : BTBOᴵ ≼ ⟪ T-fb 1 ⟫`. 回灌高度第 1 站 (读 $\psi_0(\Omega_{\Omega^2})$) 不低于 $\psi_0(\Omega_\Omega)$. 这是一次直接的验收 (同 `SumOneAccept.T₀≈` 那样对上旧折叠), 没有做. 只要它, 第 0, 1, 2 级对 `T-fb 1` 就成立 (`low-fb1`), **不经过** 折叠对世界的单调.
- 要把下界搬到极限闭项 `T-fbω` (终点候选的形状), 还要 `Funext` 与 `MonoL : HtCrossInst.Hl.N.MonoL (λ n → proj₁ (Λs n)) lΛω 1`: 实例 `Λω` 之内, 空状态折叠 $\Omega_{\Lambda_1}$ 不高于第 1 段的状态里折叠. 这是 `HtCross` 第一个障碍 1 (折叠对状态, 上下文, 输入世界单调); 判断它与并行的 `KVal` 所攻的 nκ 值语义同类. `hl-reduce` 由它给 `T-fb 1 ≤ T-fbω`.

```agda
module FbLow (Acc₁ : BTBOᴵ ≼ ⟪ T-fb 1 ⟫) where

  low-fb1 : ∀ k → k ≤ℕ 2 → treeE k ≼ ⟪ T-fb 1 ⟫
  low-fb1 k p = ≼-trans (treeE≤2 k p) Acc₁

  module ToLimit (fe : Funext) (mono : Hl.N.MonoL (λ n → proj₁ (Λs n)) lΛω 1) where

    fb1≤ω : T-fb 1 ≤ T-fbω
    fb1≤ω = Hl.N.hl-reduce (λ n → proj₁ (Λs n)) lΛω 1 fe mono

    low-fbω : ∀ k → k ≤ℕ 2 → treeE k ≼ ⟪ T-fbω ⟫
    low-fbω k p = ≼-trans (low-fb1 k p) (≤→≼ᴬ fb1≤ω)
```

## §5 第 3 级以上: 归纳步要的是什么

**终点等价于逐级下界** (§2 `EBO≼`, `EBO≼⁻`). 所以对任何主线闭项 $T$, "`EBO-tree` $\preccurlyeq\langle\!\langle T\rangle\!\rangle$" 恰是 "对一切 $k$, `treeE k` $\preccurlyeq\langle\!\langle T\rangle\!\rangle$", 再由单调只要对充分大的 $k$. 下面的 `Endpoint` 把归纳的形状写成参数: 一族主线闭项 $t_k$, 起点 $K$, 起点的下界, 归纳步, 都在 $T$ 之下. 结论无条件地由参数推出.

```agda
record Climb (T₊ : A) : Set where
  field
    t     : ℕ → A
    K     : ℕ
    base  : treeE K ≼ ⟪ t 0 ⟫
    step  : ∀ k → treeE (k + K) ≼ ⟪ t k ⟫ → treeE (suc (k + K)) ≼ ⟪ t (suc k) ⟫
    below : ∀ k → t k ≤ T₊

endpoint : ∀ {T₊} → Climb T₊ → EBO-tree ≼ ⟪ T₊ ⟫
endpoint {T₊} c = EBO≼-from K (λ k → ≼-trans (go k) (≤→≼ᴬ (below k)))
  where
  open Climb c
  go : ∀ k → treeE (k + K) ≼ ⟪ t k ⟫
  go zero = base
  go (suc k) = step k (go k)
```

**第一个缺口在第 3 级, 它是高度的类型, 不是单调引理.** `Climb` 的 `step` 在 $k+K=2$ 处 (从 $\psi_0(\Omega_\Omega)$ 到 $\psi_0(\Omega_{\Omega_\Omega})$) 由 `step-shape 2` 恰好化为: 主线闭项不低于 $G_2(\gamma_n)=\psi_0(\Omega_{\Omega_{\gamma_n}})$ 的带标签树, 对一切 $n$; 其中 $\gamma_0=1$, $\gamma_1=\psi_0(\Omega_\Omega)$ (定理: `γ0`, `γ-iter`, `fs-tower0`). 第 $n=1$ 项已经是 $\psi_0(\Omega_{\Omega_{\psi_0(\Omega_\Omega)}})$.

对高度树一族, 闭项都是 `TΛ Λ l` ($\Lambda$ : `H`). 下面三环只有最后一环是定理:

1. (判断, 读法) `TΛ Λ` 读 $\psi_0(\Omega_\Lambda)$, 而记号侧 $\psi_0(\Omega_a)\le\psi_0(\Omega_b)$ 要 $a\le b$; 所以 `TΛ Λ` $\succcurlyeq\psi_0(\Omega_{\Omega_{\gamma_1}})$ 要 $\Lambda\ge\Omega_{\gamma_1}>\Omega_2$.
2. (判断) `H` 的元素是第二数类的布劳威尔树 (`hΩ` 是唯一的不可数极限, 坐标取 `A`), 值都 $<\Omega_2$; $\Lambda\ge\Omega_2$ 在 `H` 里就是 "$\Lambda$ 严格高于一切高度".
3. (定理) `EndLowH.no-top : ¬ Σ H (λ Λ → ∀ h → hs h ≤ᴴ Λ)`.

所以按读法, 现有的主线闭项 (`HtFeed` 与 `HtOut` 的一切 `TΛ`, 包括 `T-fbω`, 读 $\psi_0(\Omega_{x_\omega})$, $x_\omega<\Omega_2$) 都低于 `treeE 3`, 终点下界对它们不成立; 要过第 3 级, 高度要能取 $\Omega_x$ ($x$ 是可数树, 甚至是更高的高度), 即以高度为下标的数类, 这是 `HtOut` 第一个障碍 4 ("要第三数类的高度树") 的加强: 不止第三数类, 要一切 $\Omega_x$, $x<\Omega_\Omega$. **没有编译过的定理说 "`treeE 3` $\not\preccurlyeq$ 任何主线闭项"**, 那要主线折叠的值上界 (第 1 环), 现在没有; 所以这里只写 "未走通", 不写成否定.
