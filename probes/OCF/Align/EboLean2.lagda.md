# EboLean2: 路线 (ii) 的设计与可行性检查 (暂停, 未完成)

> **记号侧验收工作**, 读记号, 不进成品.
>
> **任务** (作者 2026-11-05): 不经 τ, 不用 Setzer 的 OT_I 语法, 对 EBO 的项直接用突出集 (distinguished sets) 证可数标准形的良基, 得到真正没有水分的第 3 层行数.
>
> **判决: 暂停 (未完成), 不是否定.** 本次没有做完路线 (ii) 的良基证明. 原因是工作量: 按 Setzer 的证明结构, EBO 版要新写约 1600–1900 行 (§3, 判断档), 本会话的预算不够把它写完并逐条编译; 做到一半交出的半成品对标杆没有用. 没有发现数学障碍, 也没有否定定理. 本文给出:
>
> 1. §1: 编译过的 EBO 原生底座: 层号索引的 $C$-集、$M$、$\tau$、$\mathcal W$、`Ag`、$\mathbb W$ 的定义; 可数层 $C$-集是全体项 (`C-all`); Setzer Remark 2.15 (c) 的 EBO 版 (`lt⇒GB`, `GB⇒lt`), 这是 Lemma 4.17 (c) 的句法核心. 它在 EBO 上 25 行, 归档的 OT_I 版 (Facts3) 241 行. **编译过的定理.**
> 2. §2: 为什么基本列版的 $W$ (不用序, 只沿基本列) 绕不开 "突出集可比较" 或 "共尾性", 所以仍走 Setzer 的序版 (判断档).
> 3. §3: EBO 版逐引理的清单与行数估计, 第 3 层约 **2700–3300 行** (中位约 3000; EboLean 的 6524 里约 3500 行是 φ, I 与 Setzer 序论的水分). **判断档, 不是定理.**
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean2 where

open import Level using (Level; 0ℓ) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.EboLeanDef using (T; ψ; Ωt; Ωs; sucT; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-trans; <sucT; ≤¬>; NF; NFP; n[]; n∷;
  InG; InGP; gp; gtl; gh; gw; gc; GB; noG-le; tail<; nfp-u; nfp-g)
```

**复用的定义 (都是 EBO 原生的).** 项、序 `_<ᵀ_`、`cof`/`pred`/`fsT`/`γT` 取自 `OCF.Align.EBO` (经 [EboLeanDef](EboLeanDef.lagda.md)); 归纳的标准形 `NF` 与 $G_u$ 的成员关系 `InG`/`GB` 取自 [EboLeanBase](EboLeanBase.lagda.md). 计划中封闭性部分 (EboLeanView/Trian/Omega/Bach/Closure, 约 820 行) 也原样复用: 它们本来就是对 EBO 写的 (WfFsn), 重写一遍只会得到同样的代码.

## §1 EBO 原生的底座 (编译过的定义与定理)

**$C$-集按层号索引.** Setzer 的 $C^a(A)$ 由 $A\cap a$ 的元素出发, 用和、$\Omega$ 与 "$a<\kappa$ 的 $\psi_\kappa$" 生成, 并证 $C^a(A)\cong C^{\tilde a}(A)$ (Lemma 4.7 (a), 约 130 行). EBO 里 $\tilde a=\Omega_{\mathrm{hs}(a)}$ ($\mathrm{hs}$: 首项下标), $a<\Omega_{w+1}$ 恰当 $\mathrm{hs}(a)\le w$, 所以直接按层号 $l=\mathrm{hs}(a)$ 定义, 叶子取 $A$ 中 $<\Omega_l$ 的元素: 4.7 (a) 变成定义. 没有 φ 与 I, 构造子只有 5 个 (Setzer 的 `K`/`FinFin` 与 `CLemmas` 的拆合约 170 行, 这里由模式匹配代替).

```agda
Pred : (ℓ : Level) → Set (lsuc ℓ)
Pred ℓ = T → Set ℓ

hs : T → T                      -- 首项下标 (0 的下标记为 0)
hs []          = []
hs (ψ w _ ∷ _) = w

data C {ℓ} (A : Pred ℓ) (l : T) : T → Set ℓ where
  cl : ∀ {y} → A y → y <ᵀ Ωt l → C A l y                       -- 叶子: A 中 Ω_l 以下的元素
  c0 : C A l []
  c+ : ∀ {x y ys} → C A l (x ∷ []) → C A l (y ∷ ys) → C A l (x ∷ y ∷ ys)
  cΩ : ∀ {w} → C A l w → C A l (ψ w [] ∷ [])                   -- Ω_w (含 1 = ψ₀(0))
  cψ : ∀ {w c} → l ≤ᵀ w → C A l w → C A l c → C A l (ψ w c ∷ [])  -- 只在 a < Ω_{w+1} 时拆 ψ_w

module _ {ℓ} (A : Pred ℓ) where
  M : Pred ℓ                    -- y ∈ C^y(A)
  M y = C A (hs y) y

  τ : T → Pred ℓ                -- τ^A(a) = C^a(A) ∩ a
  τ a y = NF y × C A (hs a) y × y <ᵀ a

data 𝒲 {ℓ} (A : Pred ℓ) : Pred ℓ where
  sup : ∀ {a} → NF a → M A a → (∀ {y} → τ A a y → 𝒲 A y) → 𝒲 A a

-- A ⊑ 𝒲(A): A ⊆ NF, 且对 x ∈ A, A 与 𝒲(A) 在 ≤ x 处一致 (Setzer Def 4.18)
Ag : ∀ {ℓ} → Pred ℓ → Set ℓ
Ag A = (∀ {x} → A x → NF x)
     × (∀ {x} → A x → ∀ {z} → (z <ᵀ x ⊎ z ≡ x) → (A z → 𝒲 A z) × (𝒲 A z → A z))

𝕎 : Pred (lsuc 0ℓ)             -- 一切突出集的并 (Setzer Def 4.25)
𝕎 y = Σ (Pred 0ℓ) λ X → Ag X × X y
```

**可数层的 $C$-集是全体项** (Setzer `C-Ω₁`): 层号为 0 时一切 $\psi_w$ 都可拆.

```agda
[]≤ : ∀ a → [] ≤ᵀ a
[]≤ []      = inj₂ refl
[]≤ (_ ∷ _) = inj₁ []<

C-all  : ∀ {ℓ} {A : Pred ℓ} y → C A [] y
C-allP : ∀ {ℓ} {A : Pred ℓ} w c → C A [] (ψ w c ∷ [])
C-all [] = c0
C-all (ψ w c ∷ []) = C-allP w c
C-all (ψ w c ∷ y ∷ ys) = c+ (C-allP w c) (C-all (y ∷ ys))
C-allP w []       = cΩ (C-all w)
C-allP w (c ∷ cs) = cψ ([]≤ w) (C-all w) (C-all (c ∷ cs))
```

**Remark 2.15 (c) 的 EBO 版.** 对 $y<\Omega_{w+1}$: $y<\psi_w(c)\iff G_w(y)<c$. Setzer 的 $\tilde C_\kappa(a)$ 在 EBO 上就是 `GB` (bot 的 $G$ 条件), 这条是 Lemma 4.17 (c) 里 "$u\in\tilde C_\kappa(y)\cap\kappa\iff u<\psi_\kappa y$" 的句法核心. 证明是对 $y$ 的列表结构归纳, 用到的只有降序 (`tail<`) 与 "下标自身没有 $w$-可见参数" (`noG-le`).

```agda
lt⇒GB : ∀ {w c y} → NF y → y <ᵀ (ψ w c ∷ []) → GB w y c
lt⇒GB n[] _ ()
lt⇒GB {w} {c} (n∷ {x = ψ v e} {xs = ys} pv h nys) q (gp i) = head q i
  where
    head : ∀ {z} → (ψ v e ∷ ys) <ᵀ (ψ w c ∷ []) → InGP w z (ψ v e) → z <ᵀ c
    head (hd< (lv< v<w)) (gh l)   = ⊥-elim (≤¬> l v<w)
    head (hd< (lv< v<w)) (gw l _) = ⊥-elim (≤¬> l v<w)
    head (hd< (lv< v<w)) (gc l _) = ⊥-elim (≤¬> l v<w)
    head (hd< (ar< e<c)) (gh l)   = e<c
    head (hd< (ar< e<c)) (gw l j) = ⊥-elim (noG-le (nfp-u pv) (inj₂ refl) j)
    head (hd< (ar< e<c)) (gc l j) = <ᵀ-trans (nfp-g pv j) e<c
lt⇒GB (n∷ {x = x} {xs = ys} pv h nys) q (gtl i) = lt⇒GB nys (<ᵀ-trans (tail< x ys h nys) q) i

GB⇒lt : ∀ {w c y} → y <ᵀ Ωs w → GB w y c → y <ᵀ (ψ w c ∷ [])
GB⇒lt {y = []} _ _ = []<
GB⇒lt {w} {y = ψ v e ∷ ys} (hd< (lv< p)) g with <sucT w p
... | inj₁ v<w  = hd< (lv< v<w)
... | inj₂ refl = hd< (ar< (g (gp (gh (inj₂ refl)))))
GB⇒lt {y = ψ v e ∷ ys} (hd< (ar< ())) g
GB⇒lt {y = ψ v e ∷ ys} (tl< ()) g
```

## §2 为什么不用基本列版的 $W$ (判断档)

基本列版: $W_X(t)$ 是沿 `pred`/`fsn`/`fsT` 的可达性, Ω-分支只取 $X$ 中的 $\eta$. 它不用序, 对 ψ 的封闭性证明很短 (按规则 4, 5ω, 5Ω, 6 各一行; 规则 6 要 γ-链 $\gamma_k\in X$), 可数项上 $W_X$ 就是 `HC`. 问题在 $X$ 的分层: $X$ 在层 $\nu$ 必须是 "$W_X$ 在层 $\le\nu$ 的全体" (不动点), 而 $W$ 对 $X$ 是反变的, 只能用突出集或对层号的超限递归来造. 两条都卡在同一处:

- **突出集要可比较** (Setzer Lemma 4.24). 序版的证明对突出集的元素做 $<$-归纳; 基本列版里两边的 Ω-分支互相调用, 递归落在层号的下降上 ($\mu>\mu'>\cdots$, 任意的标准形), 不是结构递归, 要层号上的良基, 即要证的东西本身.
- **对层号递归** 要层号 (不可数标准形) 的 $<$-良基; 从基本列可达推 $<$-可达要 **共尾性** ($y<x\Rightarrow y\le x[k]$ 或 $y<x[\eta]$). 规则 6 那一支要从 $y$ 里抽出与 $x$ 的叶子对齐的部分 (Standard 的 `Ωcof`/`Cof6` 只对可数下标做过), 另外还要对深度做 ℕ-自举 (下标的深度更小), 而 Ω-分支的元素会把深度带进下标, 记账复杂.

所以本文按 Setzer 的序版结构设计 (§3). 这是判断, 没有编译过的否定.

## §3 EBO 版的引理清单与行数估计 (判断档)

左列是 Setzer 的模块 (EboLean 切片行数), 右列是 EBO 版的估计. 依据: 没有 φ (二元 Veblen) 与 I, 删去 `W-φ`, `W-I`, `Fi′`, `x^{−Fi}`, `x^{−I}`, Lemma 4.7 (e)(f), `CTilde`, Lemma 4.17 (c) 与 4.31 的 $\psi_I$ 支; EBO 的基数算术是显式的 ($\tilde x=\Omega_{\mathrm{hs}(x)}$, $x^+=\Omega_{\mathrm{hs}(x)+1}$, $\Omega_{w+1}^-=\Omega_w$); 序是句法字典序, 线性、传递约 60 行 (EboLeanBase §1), 不要 Setzer 的燃料序论.

| Setzer | 行 | EBO 版 | 估计 |
|---|---|---|---|
| K, CLemmas (`FinFin`, C 的拆合) | 168 | 归纳的 `C` (§1) | 50 |
| Base, OrderLemmas | 188 | 同 (§1 已有定义) | 80 |
| Lemma 4.7 (a)(b) (C-shift, C-anti) | 132 | (a) 是定义; (b) 对项结构的平移 | 60 |
| Lemma 4.13 (𝒲 的同余) | 37 | 同 | 30 |
| Dist (4.21, 4.24) | 108 | 同 (通用) | 100 |
| Union (4.26–4.29) | 115 | 同 (通用) | 105 |
| Closed, Closed2 (WDC/WUC, Remark 4.15) | 477 | 只有和与 ψ (含 Ω) | 180 |
| Lemma 4.17 (b) | 241 | (ii) 和, (iv) Ω | 120 |
| Lemma 4.17 (c) | 208 | 无 I 支 | 150 |
| Lemma 4.7 (e)(f), CTilde | 134 | 删 | 20 |
| Lemma 4.23, 4.23 (c) | 248 | 同 | 210 |
| Lemma 4.30, 4.31 (a) | 244 | 同, 无 (b) | 200 |
| 句法事实 (Setzer: 序论 1990 + 44 条事实 960) | 2950 | tilde/plus/κ⁻, 和的前后缀, `between-app`, Remark 2.15 (c)(e) 等 | 350–600 |
| **良基部分合计** | **5240** | | **约 1650–1900** |

加上 EBO 定义 (156)、封闭性 (820, 复用)、`hc`/树 (约 60)、结构归纳 "一切标准形在 $\mathbb W$ 里" 与可达性 (约 80): **第 3 层约 2700–3300 行, 中位约 3000.** 不可靠之处: 句法事实的行数 (Setzer 的 44 条里哪些在 EBO 上变平凡, 只在 Remark 2.15 (c) 上核对过一条: 241 → 25 行); Remark 4.15 与 Lemma 4.30 的 EBO 版有没有新的分支.

**做的顺序** (给接手的人): 先补 §1 的通用层 (`Ag-ind`, `Ag-Prog₁`, 4.24, `𝕎`, `Ag𝕎`), 它们只用 `C` 的单调与 4.13; 再写 EBO 的基数算术与 Remark 4.15; 然后 4.17 (b)(c), 4.23, 4.30, 4.31 (a); 最后照 [EboLeanTau](EboLeanTau.lagda.md) §3–§4 的样子组装 (把 τ 换成恒等: 一切标准形属于 $\mathbb W$, 可数部分可达), 再接 [EboLeanTree](EboLeanTree.lagda.md) 的 `hcA`. 工程上照 EboLean §5 的两处坑: 隐参写明; 不加 `--lossy-unification` 也许更稳.
