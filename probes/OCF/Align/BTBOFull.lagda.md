# 已发表的 BTBO 与 `BTBOᴵ` 同值

> **验收文件, 读 `NoCumsum` 的对角线.** 判决: **HOLDS**, 档次是值验收 (互相 $\preccurlyeq$). 主定理 `BTBO≈`:
>
>     tr₀ BTBO ≈ᵛ BTBOᴵ
>
> 左边是 `src/OCF/BTBO` 的 `BTBO` 经第 0 层翻译, 右边是带字面标签 $\psi_0(\Omega_\Omega)$ 的树 (`Label.BTBO-label`). 所以文章的标签 "估计 $\psi_0(\Omega_\Omega)$" 在**序数值**上是定理. 结构值验收 (互相 $\sqsubseteq^0$) 是假的 (`BTBOValNeg.no-⊑⁰-lab`), 字面标签因此也没有.
>
> **累加在这一站被吸收.** 层号的值: `absorb-x`. 折叠: `V1`, `V2`, `V3`, 下面的 `Low`, `Upp`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOFull where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
open S using (ordᴰ; BTBO)
open import OCF.Align.Level hiding (below)
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ⊑→≼)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValDn using (τ)
open import OCF.Align.BTBOValMain using (x; x-step; row₀)
open import OCF.Align.BTBOValAbsorb using (St; stz; sts; stl)
open import OCF.Align.BTBOValNeg using (≺ᴵ→s≼)
open import OCF.Align.BTBOFullSt using (St-x)
open import OCF.Align.BTBOFullLv using (SV; svz; svs; svl; SV-L; St-≅; ⊑→≼f)
open import OCF.Align.BTBOFullEmb using (Ψ-emb)
open import OCF.Align.BTBOFullEb using (V2)
open import OCF.Align.BTBOFullV3 using (V3; bkᴵ; Fʸ)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
```

## §1 `bkᴵ`

`bkᴵ` 把层号读成 src 第 0 层的树, 值不变, 严格性不变.

```agda
tr₀-bk : ∀ a → tr₀ (bkᴵ a) ≅ forget a
tr₀-bk zero      = z≅
tr₀-bk (suc a)   = s≅ (tr₀-bk a)
tr₀-bk (lim f s) = l≅ (λ n → tr₀-bk (f n))

St-forget : ∀ {a} → SV a → St (forget a)
St-forget svz        = stz
St-forget (svs d)    = sts (St-forget d)
St-forget (svl d st) = stl (λ n → St-forget (d n))
  (λ n → let c , r , k = st n in ≼-trans (s≼s (⊑→≼f k)) (≺ᴵ→s≼ r))

St-bk : ∀ {a} → SV a → St (tr₀ (bkᴵ a))
St-bk {a} d = St-≅ (tr₀-bk a) (St-forget d)

bk≅γ : ∀ m → tr₀ (bkᴵ (N.L m)) ≅ N.γ m
bk≅γ m = ≅-trans (tr₀-bk (N.L m)) (forget-toLevel (N.γ m) (N.cert m))
```

## §2 下界

$\gamma_{k+1}=\psi^0(\Omega_{L_k})\preccurlyeq\psi^0(\Omega_{\tau\,\mathrm{ord}^\mathrm{D}(\mathrm{bk}\,L_k)})\preccurlyeq\psi^0(\Omega_{\tau\,\mathrm{ord}^\mathrm{D}x_{k+1}})\approx x_{k+2}$. 第一步 `V1`, 第二步 `V2` (要归纳假设 $\gamma_k\preccurlyeq x_{k+1}$), 第三步 `x-step`.

```agda
Low : ∀ k → N.γ k ≼ tr₀ (x (suc k))
Low zero    = row₀
Low (suc k) =
  ≼-trans (Ψ-emb (PW₃ (V1 (SV-L k))))
  (≼-trans (Ψ-emb (PW₁ (V2 (bkᴵ (N.L k)) (x (suc k)) (St-bk (SV-L k)) (St-x (suc k))
                         (≼-trans (≅→≼ (bk≅γ k)) (Low k)))))
           (proj₂ (x-step (suc k))))
```

## §3 上界

$x_{k+1}\approx\psi^0(\Omega_{\tau\,\mathrm{ord}^\mathrm{D}x_k})\preccurlyeq\psi^0(\Omega_{\tau\,\mathrm{ord}^\mathrm{D}(\mathrm{bk}\,L_m)})\preccurlyeq\psi^0(\Omega_{L_{m+1}})=\gamma_{m+2}$. 第二步 `V2`, 第三步 `V3`.

```agda
g : ℕ → ℕ
g zero    = 0
g (suc k) = suc (suc (g k))

Upp : ∀ k → tr₀ (x k) ≼ N.γ (g k)
Upp zero    = z≼
Upp (suc k) =
  ≼-trans (proj₁ (x-step k))
  (≼-trans (Ψ-emb (PW₁ (V2 (x k) (bkᴵ (N.L (g k))) (St-x k) (St-bk (SV-L (g k)))
                         (≼-trans (Upp k) (≅→≼ (≅-sym (bk≅γ (g k))))))))
           (Ψ-emb (PW₂ (N.cert (suc (g k))) (V3 (SV-L (g k))))))
```

## §4 主定理

```agda
γ-step : ∀ m → N.γ m ≼ N.γ (suc m)
γ-step m = ⊑→≼ _ (N.D.diag-step m)

BTBO≈ : tr₀ BTBO ≈ᵛ BTBOᴵ
BTBO≈ = l≼ (λ n → ≼l (g n) (≼-trans (Upp n) (γ-step (g n)))) , l≼ (λ m → ≼l (suc (suc m)) (Low (suc m)))
```

## §5 FGH (有限测试与判断)

同值不等于 FGH 相同. `S.FGH BTBO n` 走 $x_n$, `FGH BTBOᴵ n` 走 $\gamma_{n+1}$, 基本列不同. 下面两个 `refl` 是有限测试: 参数 0, 1 恰好相等. 参数 2 两边都算不完 (`NoCumsum` §2, `BTBOValTest` §1). 逐点是否不同: **未证**, 判断是不同, 没有 `≢` 也没有增长比较. `FGH-tr₀` 只说翻译不改 FGH.

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

_ : S.FGH BTBO 0 ≡ FGH BTBOᴵ 0
_ = refl

_ : S.FGH BTBO 1 ≡ FGH BTBOᴵ 1
_ = refl
```

## §6 对应到任务的逐项

- `St-x` (`BTBOFullSt`): $x_k$ 严格, 定理.
- $\gamma_2\preccurlyeq x_3$: `Low 2`. $x_3\preccurlyeq\gamma_6$: `Upp 3`. `g k = 2k` 不紧, 紧的 $x_3\preccurlyeq\gamma_3$ 这里不需要.
- 嵌入 $E$: `V1` (层号到累加), `V2` (累加到累加), `V3` (累加到折叠的基本列). 全部是保序映射, 没有用值的判定, 不触壁垒: 比较都在同一个字面上界之下 (`two-preds`, `<-dec`).

## §7 字面标签没有

```agda
open import Data.Empty using (⊥)
open import OCF.Align.Correspond using (Lab)
import OCF.Align.EBO as E
open import OCF.Align.BTBOValNeg using (no-⊑⁰-lab)

no-lab : Lab (tr₀ BTBO) (E.EBOψ 2) → ⊥
no-lab L = no-⊑⁰-lab L (≅→⊑ (≅-refl⁰ (tr₀ BTBO)))
```
