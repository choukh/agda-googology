> **机械克隆, 验收用.** 由 `ScafLadderZStandardOmega` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名, 加 `sψ`, `singψ`; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `StandardOmega` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# EBO 标准形理论 (下标 $\Omega$): 下标可见性、共尾性与闭包

> 接 [Standard](Standard.lagda.md) 与 [Stage2](Stage2.lagda.md) §10 第 4 条. Standard 的标准形 `NF` 要求 $\psi$-下标可数 (`Ctbl`), 所以 $\Omega_\Omega=\psi_\Omega(0)$ 不在其中, 而阶段 2 的每一项 ($\psi_0(\Omega_\Omega\cdot2)$, 它的链 $\gamma'$, $\psi_0(\Omega_{\Omega+1})$, …) 都含它. 本文把标准形理论推广到唯一的不可数下标 $\Omega$ 及 $\Omega+$可数, 全部在记号侧 (不导入树族). 树侧派发要的记号事实与 "逐步给出的上界" 在 [SystemOmega](SystemOmega.lagda.md).
>
> 结论先说:
>
> 1. **标准形 (§1).** `NF₁` 与 Standard 的 `NF` 同形, 下标条件从 `Ctbl u` 换成 `Sb u`: $u$ 可数, 或 $u=\Omega+c$ 且 $c$ 可数 ($\Omega=\psi_1(0)$ 本身是 $c=0$). 可见参数 `Vis₁` 比 Standard 的 `Vis` 多一个构造子 `vs`: 穿过下标 $\ge$ 门槛的节点时也进入它的**下标** (扩展 Buchholz 的 $C_u(\alpha)$ 要求节点的下标也在 $C_u(\alpha)$ 里). 门槛为 $0$ 时 `vs` 看到可数下标里的一切参数; 门槛 $\ge1$ 时它只经 $\Omega_{\Omega+c}$ 之类的节点进入 $\Omega+c$, 只看到 $0$. `Bnd₁` 与 `NF₁` 的其余子句不变.
> 2. **`vs` 不可少 (§7, 已编译的反例).** $v=\psi_0(\Omega_{\psi_0(\Omega_\Omega+1)})<^\mathsf T\psi_0(\Omega_\Omega)$, 但 $v$ 不小于任何 $\psi_0(\Omega_\Omega)[n]$ (`vX≮`). $v$ 满足 Standard 式 (不进下标) 的有界条件 (`vX-oldBnd`), 只在 `vs` 处失败 (`vX-notNF₁`). Standard 里没有这种项: 那里可数下标里不会出现 $\Omega_\Omega$.
> 3. **共尾性 (§2).** `cofin₁ : NF₁ u → cof u ≡ cω → NF₁ v → v <ᵀ u → Σ n. v <ᵀ fsn u n` 对一切标准形成立. 与 Standard 相比, `Ωcof` 只多一种叶子: 奇异叶 $\Omega_\Omega$ (共尾度 $\Omega_1$, $\nu=0$, $\Omega_\Omega[\eta]=\Omega_\eta$; `singΩ`), 取 $\theta$ 为 $c$ 的首项**下标** $x<\Omega$, $x$ 的首项参数经 `vs` 是 $c$ 的 $0$-可见参数. `Cof6` 字面不变. 层 $\Omega$ 的规则 6 ($\psi_0(\Omega_{\Omega+1})$ 的链 $\Omega_\Omega,\psi_\Omega(\Omega_\Omega),\ldots$) 是正规叶 $\nu=\Omega$ 的普通情形; $\psi_\delta$ 穿透前缀 $\Omega_\Omega+\zeta$ 是 Standard 的穿透情形. **共尾性不需要新的自界引理.**
> 4. **闭包 (§3–§5).** `NF₁-pred`, `NF₁-fsn`, `NF₁-fsT` (含 $\Omega_\Omega$ 与 $\Omega_{\Omega+1}$ 处的 $\Omega$-基本列), `NF₁-γ`, `desc-NF₁`. 新的数学都在 "可见参数在基本列下仍有界": 极限叶 $\Omega_w$ ($w$ 极限, 如 $w=\gamma'_k$) 变成 $\Omega_{w[n]}$, 下标里新出现的可见参数要对**经过下标位置**的上下文有界. 上下文因此多一种框架 `sb` ($H\mapsto\Omega_H$), 自界引理多一个下标框架情形, 只比较首项下标: 首项不变时用大小核 `hdC` 提升, 极限叶时对下标递归. `DESCΩ` 在下标框架下遇到两种叶子: 奇异叶由 `swapΩ` ($\Omega<C[\Omega_\Omega]$ 且 $\eta<\Omega$ $\Rightarrow$ $\eta<C[\Omega_\eta]$); 正规叶由 `regSb`, 它要求 $\eta$ 的首项下标恰是 $\nu$ (`HdIs ν η`, 链点总满足, `hdγ`), 于是 $\nu+1<C[\Omega_{\nu+1}]$ 经大小核 `leafC` 推出 $\nu<C[\eta]$. 这就是 **$\Omega$ 情形的新自界引理**: `SELFΩ` 带前提 `NoSb S ⊎ HdIs ν η` (上下文不穿过下标, 或 $\eta$ 是 $\nu$ 层的链点), 全部调用点都满足它. 另一处新内容是链点 $\gamma_k=\psi_\nu(\cdots)$ 的下标 $\nu$ 里的可见参数 (`Gγ` 的 `vs` 情形): `visLeaf` (它们也是 $d$ 的可见参数) 与 `leafLift` (上界从 $S[d]$ 搬到 $S[d[\psi_\nu(\cdots)]]$).
> 5. **对角线 (§6).** `t2-NF : NF₁ ψ₀(Ω_Ω·2)` 与 **`diag₁-desc-NF : Desc t2 t → NF₁ t`**; 链 `γ′-NF : ∀ k → NF₁ (γ′ᴱ k)` (其中 $\gamma'_1=\psi_0(\Omega_\Omega+\Omega)$), `nfts` ($\psi_0(\Omega_\Omega+1)$), `tO-NF`/`tO-desc-NF` ($\psi_0(\Omega_{\Omega+1})$ 及其全部后代), `fsT-ΩΩ-NF`/`fsT-ΩΩ+1-NF`. 共尾性检验: `cofin-t2` (第 $n$ 项写成 $\gamma'_{n+1}$), **`cofin-γ′2`** ($u=\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\psi_0(\Omega_\Omega+\Omega)})$), `cofin-tO`, `cofin-tP` (Stage2 §9 的前缀暴露项 $\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$, 它是 $t_2$ 的 9 步后代); 具体的 $n$ 由 `refl` 算出.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件. Standard 的 `Vis`/`NF`/上下文/自界引理因类型改变不能复用, 本文以新名字重写 (`Vis₁`, `NF₁`, 框架 `Fr` 多 `sb`; 证明逐行照抄再补新情形); 大小、`split`/`PFX`、`inv1`、`Ctbl`、`penInv`、`viewA` 等与标准形无关的部分直接导入.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZStandardOmega where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; <⇒≤; <-irrefl;
  ≤-<-trans; <-≤-trans; ≤-pred) renaming (<-trans to <ℕ-trans)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂)

open import OCF.Align.Closure using (Pen; cmpᴾ-refl; cmpᵀ-refl; lt→<; lt→<ᴾ; eq→≡; eq→≡ᴾ; <→lt;
  <ᵀ-trans; <ᴾ-trans; fsT₊-pen′)
open import OCF.Align.Bachmann using (<ᵀ-irrefl; <ᵀ-asym; <sucT; pen→<; gt→≤; Hd≤; Hd≤-desc;
  cofA≢c1; fs-gt; fs<ᵀ)
open import OCF.Align.Correspond using (cof-ne; fs-rep; fs-ω; fsT-c1; γᴱ; βᴱ; diag-fs)
open import OCF.Align.Standard using (_≤ᵀ_; Pen→≤; <≤-trans; ≤-trans′; <→≱; ++-mono;
  sz; szᴾ; sz-++; sz-hd; sz-tl; sz-hdarg; sz-suffix; split; inS; past; PFX; V1; v[]; vlv; var; inv1;
  fsn-++; fsT-++; cof-++;
  Ctbl; c[]; c∷; Ctbl-cof; Ctbl-pred; Ctbl-fsn; PenΩ; penΩ; penInv; γ<Ωs;
  <++′; fsT-desc; ViewA; v4; v5; v6; viewA; viewL; belowΩ; cof[]≢ω; cof[]≢Ω; fsT-ne; cofψ0≢c1;
  tail<; []≤; Desc; d₀; dω; d₁)
open import OCF.Align.Stage2 using (Ωᵗ; t2; b₂; γ′ᴱ; tO; ts; diag2-fs)
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; Ωs; natT; fsn; fsT; fsT0; γT; dec;
              _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
       renaming (ψ to ψᵗ)
```

记号: $\Omega=\Omega_1$ 是项 `Ωᵗ = ψ (natT 1) [] ∷ []`, 作为下标它就是 "$\Omega$"; $\Omega_\Omega$ 是 `βᴱ = ψ Ωᵗ [] ∷ []`; $\Omega+c$ 是 `Ω₁ ∷ c`. EBO 的 $\Omega_0=1$. $t[n]$ 是 `fsn t n`, $t[\eta]$ 是 `fsT t η`, $\gamma_k$ 是 `γT b ν k`. `t2`, `b₂`, `γ′ᴱ`, `tO`, `ts` 取自 Stage2.

## §1 下标类与可见参数

`Sb u`: 下标可数 (`sC`), 或 $\Omega+c$ 且 $c$ 可数 (`sΩ`). `Vis₁ w ζ a`: $\zeta$ 是 $a$ 的 $w$-可见参数. 前三个构造子与 Standard 同 (`vh` 节点的参数, `vd` 进参数, `vt` 后续加项); 新的 `vs` 在下标 $x\ge w$ 的节点处进入下标 $x$. 这就是扩展 Buchholz 的 $G_u$: $G_u(\psi_x(b))=\{b\}\cup G_u(b)\cup G_u(x)$ 若 $x\ge u$, 否则为空. `NF₁` 的主项条件: `NF₁ u`, `Sb u`, `NF₁ a`, `Bnd₁ u a`.

```agda
Ω₁ : PT
Ω₁ = ψᵗ (natT 1) []

_ : Ωᵗ ≡ Ω₁ ∷ []
_ = refl

_ : βᴱ ≡ ψᵗ Ωᵗ [] ∷ []
_ = refl

Ωᵐ : ℕ → T → T
Ωᵐ zero    c = c
Ωᵐ (suc n) c = Ω₁ ∷ Ωᵐ n c

-- ψ₁(1) 这一项. `ψ¹ ∷ Ωᵐ n c` 是 ψ₁(1) + Ω·n + c
ψ¹ : PT
ψ¹ = ψᵗ (natT 1) (natT 1)

data Sb : T → Set where
  sψ : ∀ n {c} → Ctbl c → Sb (ψ¹ ∷ Ωᵐ n c)
  sC : ∀ {w} → Ctbl w → Sb w
  sΩ : ∀ {c} → Ctbl c → Sb (Ω₁ ∷ c)
  sΩ² : ∀ n {c} → Ctbl c → Sb (Ω₁ ∷ Ω₁ ∷ Ωᵐ n c)

data Vis₁ (w : T) : T → T → Set where
  vh : ∀ {x a xs}   → w ≤ᵀ x → Vis₁ w a (ψᵗ x a ∷ xs)
  vd : ∀ {x a xs ζ} → w ≤ᵀ x → Vis₁ w ζ a → Vis₁ w ζ (ψᵗ x a ∷ xs)
  vs : ∀ {x a xs ζ} → w ≤ᵀ x → Vis₁ w ζ x → Vis₁ w ζ (ψᵗ x a ∷ xs)
  vt : ∀ {x xs ζ}   → Vis₁ w ζ xs → Vis₁ w ζ (x ∷ xs)

Bnd₁ : T → T → Set
Bnd₁ w a = ∀ {ζ} → Vis₁ w ζ a → ζ <ᵀ a

data NF₁ : T → Set
data NFᴾ₁ : PT → Set
data NF₁ where
  n[] : NF₁ []
  n∷  : ∀ {x xs} → NFᴾ₁ x → NF₁ xs → Hd≤ xs x → NF₁ (x ∷ xs)
data NFᴾ₁ where
  nψ : ∀ {u a} → NF₁ u → Sb u → NF₁ a → Bnd₁ u a → NFᴾ₁ (ψᵗ u a)

bnd[] : ∀ {w} → Bnd₁ w []
bnd[] ()
```

两个 `refl` 记下 Stage2 的 `Ωᵗ`/`βᴱ` 的字面形状. 下面是 Standard 的三条组合工具补上 `vs` 情形: 可见参数是真子项 (`Vis-sz`; `vs` 用新的 `sz-sub`, 下标比整项小), 门槛单调 (`Vis-mono`), 传递 (`Vis-trans`); 外加前缀里的可见参数在整个和里仍可见 (`Vis-++`).

```agda
sz-sub : ∀ x a xs → sz x <ℕ sz (ψᵗ x a ∷ xs)
sz-sub x a xs = <-≤-trans (s≤s (m≤m+n (sz x) (sz a))) (sz-hd (ψᵗ x a) xs)

Vis-sz : ∀ {w ζ t} → Vis₁ w ζ t → sz ζ <ℕ sz t
Vis-sz (vh {x = x} {a = a} {xs = xs} _)   = sz-hdarg x a xs
Vis-sz (vd {x = x} {a = a} {xs = xs} _ v) = <ℕ-trans (Vis-sz v) (sz-hdarg x a xs)
Vis-sz (vs {x = x} {a = a} {xs = xs} _ v) = <ℕ-trans (Vis-sz v) (sz-sub x a xs)
Vis-sz (vt {x = x} {xs = xs} v)           = <-≤-trans (Vis-sz v) (sz-tl x xs)

Vis-mono : ∀ {w w′ ζ t} → w ≤ᵀ w′ → Vis₁ w′ ζ t → Vis₁ w ζ t
Vis-mono h (vh h′)   = vh (≤-trans′ h h′)
Vis-mono h (vd h′ v) = vd (≤-trans′ h h′) (Vis-mono h v)
Vis-mono h (vs h′ v) = vs (≤-trans′ h h′) (Vis-mono h v)
Vis-mono h (vt v)    = vt (Vis-mono h v)

Vis-trans : ∀ {w ζ d t} → Vis₁ w ζ d → Vis₁ w d t → Vis₁ w ζ t
Vis-trans v (vh h)    = vd h v
Vis-trans v (vd h v′) = vd h (Vis-trans v v′)
Vis-trans v (vs h v′) = vs h (Vis-trans v v′)
Vis-trans v (vt v′)   = vt (Vis-trans v v′)

Vis-++ : ∀ {w ζ s} t → Vis₁ w ζ s → Vis₁ w ζ (s ++ t)
Vis-++ t (vh h)   = vh h
Vis-++ t (vd h v) = vd h v
Vis-++ t (vs h v) = vs h v
Vis-++ t (vt v)   = vt (Vis-++ t v)

≤<-trans : ∀ {a b c} → a ≤ᵀ b → b <ᵀ c → a <ᵀ c
≤<-trans (inj₁ p) q = <ᵀ-trans p q
≤<-trans (inj₂ refl) q = q
```

**叶子的分类.** 下标 `Sb u` 的叶子 $\Omega_u$ 若共尾度为 $\Omega_{\nu+1}$, 只有两种: $u$ 后继 (正规叶, $\nu=u-1$, `reg`), 或 $u=\Omega$ (奇异叶 $\Omega_\Omega$, $\nu=0$, `sing`). 可数下标没有 $\Omega$-共尾度 (Standard 的 `Ctbl-cof`), $\Omega+c$ ($c\ne0$) 的共尾度就是 $c$ 的. `Leaf₁` 是索引式的, 匹配 `sing` 时 $u$ 与 $\nu$ 被字面地合一为 `Ωᵗ` 与 `[]`, 其后 $\Omega_\Omega[\eta]=\Omega_\eta$ 是定义性的. 随后: `Sb` 对 `pred`/`fsn` 封闭; `ctblΩ` ($<\Omega$ 的标准形可数; 奇异叶的新下标 $\eta$ 由它是 `Sb`); `NF₁-pred` (与 Standard 同); `NF-ν₁` (从叶子读出 $\nu$ 是标准形下标, 奇异叶给 $\nu=0$).

```agda
data Leaf₁ : T → T → Set where
  reg  : ∀ {u} → cof u ≡ c1 → Leaf₁ u (pred u)
  sing : Leaf₁ Ωᵗ []
  sing² : ∀ n → Leaf₁ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) []
  singψ : ∀ n → Leaf₁ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) []

cof-Ωᵐ[] : ∀ n → cof (Ω₁ ∷ Ωᵐ n []) ≡ cΩ []
cof-Ωᵐ[] zero = refl
cof-Ωᵐ[] (suc n) = cof-Ωᵐ[] n

cof-Ωᵐ+ : ∀ n x xs → cof (Ω₁ ∷ Ωᵐ n (x ∷ xs)) ≡ cof (x ∷ xs)
cof-Ωᵐ+ zero x xs = refl
cof-Ωᵐ+ (suc n) x xs = cof-Ωᵐ+ n x xs

pred-Ωᵐ[] : ∀ n → pred (Ω₁ ∷ Ωᵐ n []) ≡ Ω₁ ∷ Ωᵐ n []
pred-Ωᵐ[] zero = refl
pred-Ωᵐ[] (suc n) = cong (Ω₁ ∷_) (pred-Ωᵐ[] n)

pred-Ωᵐ+ : ∀ n x xs → pred (Ω₁ ∷ Ωᵐ n (x ∷ xs)) ≡ Ω₁ ∷ Ωᵐ n (pred (x ∷ xs))
pred-Ωᵐ+ zero x xs = refl
pred-Ωᵐ+ (suc n) x xs = cong (Ω₁ ∷_) (pred-Ωᵐ+ n x xs)

fsn-Ωᵐ+ : ∀ n x xs k → fsn (Ω₁ ∷ Ωᵐ n (x ∷ xs)) k ≡ Ω₁ ∷ Ωᵐ n (fsn (x ∷ xs) k)
fsn-Ωᵐ+ zero x xs k = refl
fsn-Ωᵐ+ (suc n) x xs k = cong (Ω₁ ∷_) (fsn-Ωᵐ+ n x xs k)

fsT-Ωᵐ : ∀ n η → fsT (Ω₁ ∷ Ωᵐ n []) η ≡ Ωᵐ n η
fsT-Ωᵐ zero η = refl
fsT-Ωᵐ (suc n) η = cong (Ω₁ ∷_) (fsT-Ωᵐ n η)

fsT0-sing : ∀ u k η → k ≡ cΩ [] → E.fsT0 u k η ≡ ψᵗ (fsT u η) [] ∷ []
fsT0-sing u .(cΩ []) η refl = refl

fsT-sing : ∀ n η → fsT (ψᵗ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) η ≡ Ωt (Ω₁ ∷ Ωᵐ n η)
fsT-sing n η = trans (fsT0-sing (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) _ η (cof-Ωᵐ[] (suc n))) (cong (λ z → ψᵗ (Ω₁ ∷ z) [] ∷ []) (fsT-Ωᵐ n η))

leaf-sing : ∀ n {μ ν} → cof (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) ≡ cΩ μ → cΩ μ ≡ cΩ ν → Leaf₁ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) ν
leaf-sing n ue e with trans (sym (cof-Ωᵐ[] (suc n))) ue
leaf-sing n ue refl | refl = sing² n

cof-ψ¹+ : ∀ n x xs → cof (ψ¹ ∷ Ωᵐ n (x ∷ xs)) ≡ cof (x ∷ xs)
cof-ψ¹+ zero x xs = refl
cof-ψ¹+ (suc n) x xs = cof-Ωᵐ+ n x xs

pred-ψ¹[] : ∀ n → pred (ψ¹ ∷ Ωᵐ n []) ≡ ψ¹ ∷ Ωᵐ n []
pred-ψ¹[] zero = refl
pred-ψ¹[] (suc n) = cong (ψ¹ ∷_) (pred-Ωᵐ[] n)

pred-ψ¹+ : ∀ n x xs → pred (ψ¹ ∷ Ωᵐ n (x ∷ xs)) ≡ ψ¹ ∷ Ωᵐ n (pred (x ∷ xs))
pred-ψ¹+ zero x xs = refl
pred-ψ¹+ (suc n) x xs = cong (ψ¹ ∷_) (pred-Ωᵐ+ n x xs)

fsn-ψ¹+ : ∀ n x xs k → fsn (ψ¹ ∷ Ωᵐ n (x ∷ xs)) k ≡ ψ¹ ∷ Ωᵐ n (fsn (x ∷ xs) k)
fsn-ψ¹+ zero x xs k = refl
fsn-ψ¹+ (suc n) x xs k = cong (ψ¹ ∷_) (fsn-Ωᵐ+ n x xs k)

fsT-singψ : ∀ n η → fsT (ψᵗ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) η ≡ Ωt (ψ¹ ∷ Ωᵐ n η)
fsT-singψ n η = trans (fsT0-sing (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) _ η (cof-Ωᵐ[] n)) (cong (λ z → ψᵗ (ψ¹ ∷ z) [] ∷ []) (fsT-Ωᵐ n η))

leaf-singψ : ∀ n {μ ν} → cof (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) ≡ cΩ μ → cΩ μ ≡ cΩ ν → Leaf₁ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) ν
leaf-singψ n ue e with trans (sym (cof-Ωᵐ[] n)) ue
leaf-singψ n ue refl | refl = singψ n

leafInv₁ : ∀ u → Sb u → ∀ k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → Leaf₁ u ν
leafInv₁ u su c0 _ ()
leafInv₁ u su c1 ue refl = reg ue
leafInv₁ u su cω _ ()
leafInv₁ u (sC cu) (cΩ μ) ue e = ⊥-elim (Ctbl-cof cu ue)
leafInv₁ .(ψ¹ ∷ []) (sψ zero c[]) (cΩ μ) () e
leafInv₁ .(ψ¹ ∷ ψᵗ [] _ ∷ _) (sψ zero (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) ue)
leafInv₁ .(ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) (sψ (suc n) c[]) (cΩ μ) ue e = leaf-singψ n ue e
leafInv₁ .(ψ¹ ∷ Ω₁ ∷ Ωᵐ n (ψᵗ [] _ ∷ _)) (sψ (suc n) (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) (trans (sym (cof-ψ¹+ (suc n) _ _)) ue))
leafInv₁ .(Ω₁ ∷ []) (sΩ c[]) (cΩ .[]) refl refl = sing
leafInv₁ .(Ω₁ ∷ ψᵗ [] _ ∷ _) (sΩ (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) ue)
leafInv₁ .(Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) (sΩ² n c[]) (cΩ μ) ue e = leaf-sing n ue e
leafInv₁ .(Ω₁ ∷ Ω₁ ∷ Ωᵐ n (ψᵗ [] _ ∷ _)) (sΩ² n (c∷ cc)) (cΩ μ) ue e = ⊥-elim (Ctbl-cof (c∷ cc) (trans (sym (cof-Ωᵐ+ (suc n) _ _)) ue))

Sb-pred : ∀ {u} → Sb u → Sb (pred u)
Sb-pred (sψ n c[])     = subst Sb (sym (pred-ψ¹[] n)) (sψ n c[])
Sb-pred (sψ n (c∷ cc)) = subst Sb (sym (pred-ψ¹+ n _ _)) (sψ n (Ctbl-pred (c∷ cc)))
Sb-pred (sC c)       = sC (Ctbl-pred c)
Sb-pred (sΩ c[])     = sΩ c[]
Sb-pred (sΩ (c∷ cc)) = sΩ (Ctbl-pred (c∷ cc))
Sb-pred (sΩ² n c[])     = subst Sb (sym (pred-Ωᵐ[] (suc n))) (sΩ² n c[])
Sb-pred (sΩ² n (c∷ cc)) = subst Sb (sym (pred-Ωᵐ+ (suc n) _ _)) (sΩ² n (Ctbl-pred (c∷ cc)))

SbΩᵐ[] : ∀ k → Sb (Ωᵐ k [])
SbΩᵐ[] zero = sC c[]
SbΩᵐ[] (suc zero) = sΩ c[]
SbΩᵐ[] (suc (suc k)) = sΩ² k c[]

rep-Ωᵐ : ∀ k → replicate k Ω₁ ≡ Ωᵐ k []
rep-Ωᵐ zero = refl
rep-Ωᵐ (suc k) = cong (Ω₁ ∷_) (rep-Ωᵐ k)

fsn-ψ¹ : ∀ k → fsn (ψ¹ ∷ []) k ≡ Ωᵐ k []
fsn-ψ¹ k = trans (fs-rep (natT 1) E.𝟏 [] refl k) (rep-Ωᵐ k)

Sb-fsn : ∀ {u} → Sb u → cof u ≡ cω → ∀ n → Sb (fsn u n)
Sb-fsn (sψ zero c[]) e k = subst Sb (sym (fsn-ψ¹ k)) (SbΩᵐ[] k)
Sb-fsn (sψ (suc m) c[]) e k with trans (sym (cof-Ωᵐ[] m)) e
... | ()
Sb-fsn (sψ m (c∷ cc)) e k = subst Sb (sym (fsn-ψ¹+ m _ _ k)) (sψ m (Ctbl-fsn (c∷ cc) (trans (sym (cof-ψ¹+ m _ _)) e) k))
Sb-fsn (sC c) e n       = sC (Ctbl-fsn c e n)
Sb-fsn (sΩ c[]) () n
Sb-fsn (sΩ (c∷ cc)) e n = sΩ (Ctbl-fsn (c∷ cc) e n)
Sb-fsn (sΩ² m c[]) e n with trans (sym (cof-Ωᵐ[] (suc m))) e
... | ()
Sb-fsn (sΩ² m (c∷ cc)) e n = subst Sb (sym (fsn-Ωᵐ+ (suc m) _ _ n)) (sΩ² m (Ctbl-fsn (c∷ cc) (trans (sym (cof-Ωᵐ+ (suc m) _ _)) e) n))

ctblΩ : ∀ {η} → NF₁ η → η <ᵀ Ωᵗ → Ctbl η
ctblΩ n[] p = c[]
ctblΩ (n∷ {x = ψᵗ z b} nz nzs hz) (hd< (lv< q)) with <sucT [] q
... | inj₁ ()
... | inj₂ refl = c∷ (ctblΩ nzs (tail< hz (lv< q)))
ctblΩ (n∷ _ _ _) (hd< (ar< ()))
ctblΩ (n∷ _ _ _) (tl< ())

NF₁-pred : ∀ {t} → NF₁ t → cof t ≡ c1 → NF₁ (pred t)
NF₁-pred n[] ()
NF₁-pred (n∷ nx (n∷ {x = y} {xs = ys} ny nys hy) hx) e =
  n∷ nx (NF₁-pred (n∷ ny nys hy) e) (Hd≤-desc (E.pred-< (y ∷ ys) e) hx)
NF₁-pred (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) e = n[]
NF₁-pred (n∷ (nψ {u = w ∷ ws} {a = []} _ _ _ _) n[] _) e = ⊥-elim (cofψ0≢c1 (w ∷ ws) (cof (w ∷ ws)) e)
NF₁-pred (n∷ (nψ {u = u} {a = y ∷ ys} _ _ _ _) n[] _) e = ⊥-elim (cofA≢c1 u (cof (y ∷ ys)) e)

NF-ν₁ : ∀ {b ν} → NF₁ b → cof b ≡ cΩ ν → NF₁ ν × Sb ν
NF-ν₁ n[] ()
NF-ν₁ (n∷ nx (n∷ ny nys hy) hx) e = NF-ν₁ (n∷ ny nys hy) e
NF-ν₁ (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) ()
NF-ν₁ (n∷ (nψ {u = w ∷ ws} {a = []} nw sw _ _) n[] _) e with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = NF₁-pred nw ue , Sb-pred sw
... | sing   = n[] , sC c[]
... | sing² _ = n[] , sC c[]
... | singψ _ = n[] , sC c[]
NF-ν₁ (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) e with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = NF-ν₁ nb be
```

`Leaf₁` 第五行的两个 `refl` 就是 "`cof Ωᵗ` 归约到 `cΩ []`": $\Omega$ 作为下标是后继 $0+1$, $\Omega_\Omega$ 因此共尾度 $\Omega_1$.

## §2 共尾性

`repb` 与 Standard 同. `Ωcof` 的记录 `ΩC b ν c` 不变: 一个 $\theta<\Omega_{\nu+1}$, 使得对一切 $\eta>\theta$ 有 $c<b[\eta]$, 且 $\theta$ 的首项若是 $\psi_x(\zeta)$ ($x\ge\nu$) 则 $\zeta$ 是 $c$ 的 $\nu$-可见参数. 新的是奇异叶 `singΩ`: $c<\Omega_\Omega$ 时 $c$ 的首项下标 $x<\Omega$, 取 $\theta=x$; 对 $\eta>x$ 有 $c<\Omega_\eta=\Omega_\Omega[\eta]$ (`hd< (lv< r)`); $x$ 的首项参数经 `vs` (下标) 再 `vh` 是 $c$ 的 $0$-可见参数. 没有 `vs` 就断在这里: $\theta$ 来自 $c$ 的下标, 而 Standard 的可见性不进下标.

```agda
repb : ∀ x {vs} → NF₁ vs → Hd≤ vs x → Σ ℕ λ m → vs <ᵀ replicate m x
repb x n[] h = 1 , []<
repb x (n∷ {x = y} ny nzs hz₀) (inj₁ e) = 1 , hd< (lt→<ᴾ y x e)
repb x (n∷ {x = y} ny nzs hz₀) (inj₂ e) with eq→≡ᴾ y x e
... | refl with repb x nzs hz₀
...   | m , q = suc m , tl< q

HdV : T → T → T → Set
HdV ν θ c = ∀ {x ζ θs} → θ ≡ ψᵗ x ζ ∷ θs → ν ≤ᵀ x → Vis₁ ν ζ c

record ΩC (b ν c : T) : Set where
  constructor ωc
  field
    θ  : T
    θ< : θ <ᵀ Ωs ν
    fθ : ∀ {η} → θ <ᵀ η → c <ᵀ fsT b η
    hv : HdV ν θ c

hv[] : ∀ {ν c} → HdV ν [] c
hv[] () _

singΩ : ∀ {c} → c <ᵀ βᴱ → ΩC βᴱ [] c
singΩ []< = ωc [] []< (λ _ → []<) hv[]
singΩ {c = ψᵗ x a ∷ cs} (hd< (lv< q)) =
  ωc x q (λ r → hd< (lv< r)) (λ {y} {ζ} {θs} eθ h → vs ([]≤ x) (subst (Vis₁ [] ζ) (sym eθ) (vh h)))
singΩ (hd< (ar< ()))
singΩ (tl< ())

record Pk² (n : ℕ) (e : T) : Set where
  constructor pk²
  field
    θ′ : T
    θ<′ : θ′ <ᵀ Ωs []
    fθ′ : ∀ {η} → θ′ <ᵀ η → e <ᵀ Ωᵐ n η
    hv′ : ∀ {y ζ θs} → θ′ ≡ ψᵗ y ζ ∷ θs → [] ≤ᵀ y → Vis₁ [] ζ e

pick² : ∀ n {e} → e <ᵀ Ω₁ ∷ Ωᵐ n [] → Pk² n e
pick² zero {e} q = pk² e q (λ r → r) (λ {y} {ζ} {θs} eθ h → subst (Vis₁ [] ζ) (sym eθ) (vh h))
pick² (suc n) []< = pk² [] []< (λ _ → []<) (λ ())
pick² (suc n) {x ∷ e} (hd< p) = pk² [] []< (λ _ → hd< p) (λ ())
pick² (suc n) {x ∷ e} (tl< q) with pick² n q
... | pk² θ θ< f h = pk² θ θ< (λ r → tl< (f r)) (λ eθ hh → vt (h eθ hh))

singΩ² : ∀ n {c} → c <ᵀ (ψᵗ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) → ΩC (ψᵗ (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) [] c
singΩ² n []< = ωc [] []< (λ {η} _ → subst ([] <ᵀ_) (sym (fsT-sing n η)) []<) hv[]
singΩ² n {c = ψᵗ [] a ∷ cs} (hd< (lv< q)) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-sing n η)) (hd< (lv< []<))) hv[]
singΩ² n {c = ψᵗ (ψᵗ y b ∷ ys) a ∷ cs} (hd< (lv< (hd< p))) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-sing n η)) (hd< (lv< (hd< p)))) hv[]
singΩ² n {c = ψᵗ (x₀ ∷ e) a ∷ cs} (hd< (lv< (tl< q))) with pick² n q
... | pk² θ θ< f h = ωc θ θ< (λ {η} r → subst (_ <ᵀ_) (sym (fsT-sing n η)) (hd< (lv< (tl< (f r))))) (λ eθ hh → vs ([]≤ _) (vt (h eθ hh)))
singΩ² n (hd< (ar< ()))
singΩ² n (tl< ())

singΩψ : ∀ n {c} → c <ᵀ (ψᵗ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) → ΩC (ψᵗ (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) [] ∷ []) [] c
singΩψ n []< = ωc [] []< (λ {η} _ → subst ([] <ᵀ_) (sym (fsT-singψ n η)) []<) hv[]
singΩψ n {c = ψᵗ [] a ∷ cs} (hd< (lv< q)) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-singψ n η)) (hd< (lv< []<))) hv[]
singΩψ n {c = ψᵗ (ψᵗ y b ∷ ys) a ∷ cs} (hd< (lv< (hd< p))) = ωc [] []< (λ {η} _ → subst (_ <ᵀ_) (sym (fsT-singψ n η)) (hd< (lv< (hd< p)))) hv[]
singΩψ n {c = ψᵗ (x₀ ∷ e) a ∷ cs} (hd< (lv< (tl< q))) with pick² n q
... | pk² θ θ< f h = ωc θ θ< (λ {η} r → subst (_ <ᵀ_) (sym (fsT-singψ n η)) (hd< (lv< (tl< (f r))))) (λ eθ hh → vs ([]≤ _) (vt (h eθ hh)))
singΩψ n (hd< (ar< ()))
singΩψ n (tl< ())

Ωcof : ∀ {b ν} → NF₁ b → cof b ≡ cΩ ν → ∀ {c} → c <ᵀ b → ΩC b ν c
Ωcof n[] () p
Ωcof (n∷ nx (n∷ ny nys hy) hx) e []<      = ωc [] []< (λ _ → []<) hv[]
Ωcof (n∷ nx (n∷ ny nys hy) hx) e (hd< q)  = ωc [] []< (λ _ → hd< q) hv[]
Ωcof (n∷ nx (n∷ ny nys hy) hx) e (tl< q) with Ωcof (n∷ ny nys hy) e q
... | ωc θ θ< fθ hv = ωc θ θ< (λ r → tl< (fθ r)) (λ eθ h → vt (hv eθ h))
Ωcof (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () p
Ωcof (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e {c} p
  with leafInv₁ (w ∷ ws) cw (cof (w ∷ ws)) refl e
... | reg ue =
  ωc c (subst (λ z → c <ᵀ ψᵗ z [] ∷ []) (sym (E.pred-suc (w ∷ ws) ue)) p)
       (λ {η} r → subst (c <ᵀ_) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η)) r)
       (λ {x} {ζ} {θs} eθ h → subst (Vis₁ _ ζ) (sym eθ) (vh h))
... | sing = singΩ p
... | sing² n = singΩ² n p
... | singψ n = singΩψ n p
Ωcof {ν = ν} (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e {c} p
  with penInv w (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = go p
  where
  fsT≡ : ∀ η → fsT (ψᵗ w (y ∷ ys) ∷ []) η ≡ ψᵗ w (fsT (y ∷ ys) η) ∷ []
  fsT≡ η = fsT₊-pen′ w (y ∷ ys) ν (cof (y ∷ ys)) be pn η
  go : c <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → ΩC (ψᵗ w (y ∷ ys) ∷ []) ν c
  go []<           = ωc [] []< (λ {η} _ → subst ([] <ᵀ_) (sym (fsT≡ η)) []<) hv[]
  go (hd< (lv< q)) = ωc [] []< (λ {η} _ → subst (c <ᵀ_) (sym (fsT≡ η)) (hd< (lv< q))) hv[]
  go (hd< (ar< q)) with Ωcof na be q
  ... | ωc θ θ< fθ hv =
    ωc θ θ< (λ {η} r → subst (c <ᵀ_) (sym (fsT≡ η)) (hd< (ar< (fθ r))))
       (λ eθ h → vd (inj₁ (pen→< ν w pn)) (hv eθ h))
  go (tl< ())
```

`Cof6` 与 `cofin₁` 逐字照抄 Standard (只换 `NF₁`/`Vis₁`/`Sb`). `Cof6` 的递归在奇异叶处这样走: $\nu=0$, $\theta=x$ 的首项是 $\psi_0(\zeta')$, $\zeta'$ 是 $c$ 的 $0$-可见参数, 故 $\zeta'<b$ (由 $c$ 的 `Bnd₁`), 对 $\zeta'$ 递归得 $\zeta'<b[\gamma_m]$, 于是 $x<\psi_0(b[\gamma_m])=\gamma_{m+1}$, 从而 $c<b[\gamma_{m+1}]$. 层 $\Omega$ 的规则 6 (例如 $\psi_0(\Omega_{\Omega+1})$, $\nu=\Omega$) 是正规叶; $\psi_\delta$ 穿透 $\Omega_\Omega+\zeta$ 是 `Ωcof` 的穿透分支. 都不需要新的引理.

```agda
Cof6 : ∀ m {b ν w c} → NF₁ b → cof b ≡ cΩ ν → w ≤ᵀ ν → sz c ≤ℕ m → c <ᵀ b →
       (∀ {ζ} → Vis₁ w ζ c → ζ <ᵀ b) → Σ ℕ λ n → c <ᵀ fsT b (γT b ν n)
Cof6 m {b} {ν} {w} {c} nb be wν hm p H with Ωcof nb be p
... | ωc [] θ< fθ hv = 0 , fθ []<
... | ωc (ψᵗ x ζ′ ∷ θs) (hd< (lv< q)) fθ hv with <sucT ν q
...   | inj₁ r = 0 , fθ (hd< (lv< r))
...   | inj₂ refl = go m hm
  where
  vz : Vis₁ ν ζ′ c
  vz = hv refl (inj₂ refl)
  go : ∀ m′ → sz c ≤ℕ m′ → Σ ℕ λ n → c <ᵀ fsT b (γT b ν n)
  go zero h = ⊥-elim (<-irrefl refl (<-≤-trans (≤-<-trans z≤n (Vis-sz vz)) h))
  go (suc m′) h with Cof6 m′ nb be wν (≤-pred (≤-trans (Vis-sz vz) h)) (H (Vis-mono wν vz))
                         (λ v → H (Vis-trans v (Vis-mono wν vz)))
  ... | k , r = suc k , fθ (hd< (ar< r))
Cof6 m nb be wν hm p H | ωc (ψᵗ x ζ′ ∷ θs) (hd< (ar< ())) fθ hv
Cof6 m nb be wν hm p H | ωc (ψᵗ x ζ′ ∷ θs) (tl< ()) fθ hv

cofin₁  : ∀ {u} → NF₁ u → cof u ≡ cω → ∀ {v} → NF₁ v → v <ᵀ u → Σ ℕ λ n → v <ᵀ fsn u n
cofinL : ∀ {w ws} → NF₁ (w ∷ ws) → ∀ k → cof (w ∷ ws) ≡ k → cofψ0 (w ∷ ws) k ≡ cω →
         ∀ {v} → NF₁ v → v <ᵀ Ωt (w ∷ ws) → Σ ℕ λ n → v <ᵀ fsn (Ωt (w ∷ ws)) n
cofinA : ∀ {w y ys} → NF₁ (y ∷ ys) → ∀ k → cof (y ∷ ys) ≡ k → cofA w k ≡ cω →
         ∀ {v} → NF₁ v → v <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → Σ ℕ λ n → v <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n

cofin₁ n[] () nv p
cofin₁ (n∷ nx (n∷ ny nys hy) hx) e nv []<     = 0 , []<
cofin₁ (n∷ nx (n∷ ny nys hy) hx) e nv (hd< q) = 0 , hd< q
cofin₁ (n∷ nx (n∷ ny nys hy) hx) e (n∷ _ nvs _) (tl< q) with cofin₁ (n∷ ny nys hy) e nvs q
... | n , r = n , tl< r
cofin₁ (n∷ (nψ {u = []} {a = []} nw cw na g) n[] hx) () nv p
cofin₁ (n∷ (nψ {u = w ∷ ws} {a = []} nw cw na g) n[] hx) e nv p = cofinL nw (cof (w ∷ ws)) refl e nv p
cofin₁ (n∷ (nψ {u = w} {a = y ∷ ys} nw cw na g) n[] hx) e nv p = cofinA na (cof (y ∷ ys)) refl e nv p

cofinL nw c0 ke () nv p
cofinL nw c1 ke () nv p
cofinL {w} {ws} nw cω ke e nv []< = 0 , subst ([] <ᵀ_) (sym (E.fsn0-eq w ws 0 ke)) []<
cofinL {w} {ws} nw cω ke e (n∷ (nψ nx _ _ _) _ _) (hd< (lv< q)) with cofin₁ nw ke nx q
... | n , r = n , subst (_ <ᵀ_) (sym (E.fsn0-eq w ws n ke)) (hd< (lv< r))
cofinL nw cω ke e nv (hd< (ar< ()))
cofinL nw cω ke e nv (tl< ())
cofinL nw (cΩ μ) ke () nv p

cofinA nb c0 ke e nv p = ⊥-elim (cof-ne _ _ ke)
cofinA {w} {y} {ys} nb c1 ke e n[] []< = 1 , subst ([] <ᵀ_) (sym (fs-rep w y ys ke 1)) []<
cofinA {w} {y} {ys} nb c1 ke e nv (hd< (lv< q)) = 1 , subst (_ <ᵀ_) (sym (fs-rep w y ys ke 1)) (hd< (lv< q))
cofinA {w} {y} {ys} nb c1 ke e (n∷ {x = ψᵗ _ c} {xs = vs′} nc nvs hv) (hd< (ar< q))
  with <sucT (pred (y ∷ ys)) (subst (c <ᵀ_) (sym (E.pred-suc (y ∷ ys) ke)) q)
... | inj₁ r = 1 , subst (_ <ᵀ_) (sym (fs-rep w y ys ke 1)) (hd< (ar< r))
... | inj₂ refl with repb (ψᵗ w c) nvs hv
...   | m , r = suc m , subst (_ <ᵀ_) (sym (fs-rep w y ys ke (suc m))) (tl< r)
cofinA nb c1 ke e nv (tl< ())
cofinA {w} {y} {ys} nb cω ke e nv []< = 0 , subst ([] <ᵀ_) (sym (fs-ω w y ys ke 0)) []<
cofinA {w} {y} {ys} nb cω ke e nv (hd< (lv< q)) = 0 , subst (_ <ᵀ_) (sym (fs-ω w y ys ke 0)) (hd< (lv< q))
cofinA {w} {y} {ys} nb cω ke e (n∷ (nψ _ _ nc _) _ _) (hd< (ar< q)) with cofin₁ nb ke nc q
... | n , r = n , subst (_ <ᵀ_) (sym (fs-ω w y ys ke n)) (hd< (ar< r))
cofinA nb cω ke e nv (tl< ())
cofinA {w} {y} {ys} nb (cΩ ν) ke e nv p = go (cmpᵀ (sucT ν) w) refl e
  where
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → cofψ₊ w ν m ≡ cω → Σ ℕ λ n → _ <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n
  go lt em ()
  go eq em ()
  go gt em _ = h nv p
    where
    h : ∀ {v} → NF₁ v → v <ᵀ (ψᵗ w (y ∷ ys) ∷ []) → Σ ℕ λ n → v <ᵀ fsn (ψᵗ w (y ∷ ys) ∷ []) n
    h nv []< = 0 , subst ([] <ᵀ_) (sym (fs-gt w y ys ν ke em 0)) []<
    h nv (hd< (lv< q)) = 0 , subst (_ <ᵀ_) (sym (fs-gt w y ys ν ke em 0)) (hd< (lv< q))
    h (n∷ (nψ {a = c} _ _ nc gc) _ _) (hd< (ar< q))
      with Cof6 (sz c) nb ke (gt→≤ ν w em) ≤-refl q (λ vz → <ᵀ-trans (gc vz) q)
    ... | n , r = n , subst (_ <ᵀ_) (sym (fs-gt w y ys ν ke em n)) (hd< (ar< r))
    h nv (tl< ())
```

**读法.** 共尾性只对 $u$ 作形状递归, 对 $v$ 用全部标准形条件. 新叶子唯一的需求是 "$v$ 的下标里的参数也受 `Bnd₁` 约束", 即 `vs`; §7 的反例说明它必要.

## §3 上下文与提升

闭包证明要谈论项在另一个项里的位置. 框架 `Fr` 比 Standard 多一个 `sb`: $H\mapsto\Omega_H=[\psi_H(0)]$, 即叶子的下标位置. 只需要参数为 $0$ 的下标框架: 基本列只在叶子处改动下标 ($\Omega_w[n]=\Omega_{w[n]}$, $\Omega_\Omega[\eta]=\Omega_\eta$), 带非零参数的节点的下标在基本列下不动. `LIFT` 的 `sb` 情形: $\zeta<\Omega_{K[H]}$ 要么 $\zeta=0$, 要么首项下标 $<K[H]$ (比 $\zeta$ 小, 递归提升); 参数比较 "$\cdot<0$" 不可能. 所以下标框架不需要额外的大小前提.

```agda
data Fr : Set where
  pre : T → Fr
  nd  : T → Fr
  sb  : Fr

Ctx : Set
Ctx = List Fr

plug : Ctx → T → T
plug []          H = H
plug (pre s ∷ K) H = s ++ plug K H
plug (nd x ∷ K)  H = ψᵗ x (plug K H) ∷ []
plug (sb ∷ K)    H = ψᵗ (plug K H) [] ∷ []

plug-++ : ∀ K K′ H → plug (K ++ K′) H ≡ plug K (plug K′ H)
plug-++ []          K′ H = refl
plug-++ (pre s ∷ K) K′ H = cong (s ++_) (plug-++ K K′ H)
plug-++ (nd x ∷ K)  K′ H = cong (λ z → ψᵗ x z ∷ []) (plug-++ K K′ H)
plug-++ (sb ∷ K)    K′ H = cong (λ z → ψᵗ z [] ∷ []) (plug-++ K K′ H)

Core : T → T → ℕ → Set
Core H H′ m = ∀ {ζ} → sz ζ ≤ℕ m → ζ <ᵀ H → ζ <ᵀ H′

LIFT : ∀ K {H H′} m → Core H H′ m → Core (plug K H) (plug K H′) m
LIFT [] m c h p = c h p
LIFT (pre s ∷ K) m c h p with split s p
... | inS f = f _
... | past ζ′ refl q = ++-mono s (LIFT K m c (≤-trans (sz-suffix s ζ′) h) q)
LIFT (nd x ∷ K) m c h []<              = []<
LIFT (nd x ∷ K) m c h (hd< (lv< q))    = hd< (lv< q)
LIFT (nd x ∷ K) m c {ψᵗ v a ∷ ys} h (hd< (ar< q)) =
  hd< (ar< (LIFT K m c (≤-trans (<⇒≤ (sz-hdarg v a ys)) h) q))
LIFT (nd x ∷ K) m c h (tl< ())
LIFT (sb ∷ K) m c h []<              = []<
LIFT (sb ∷ K) m c {ψᵗ v a ∷ ys} h (hd< (lv< q)) =
  hd< (lv< (LIFT K m c (≤-trans (<⇒≤ (sz-sub v a ys)) h) q))
LIFT (sb ∷ K) m c h (hd< (ar< ()))
LIFT (sb ∷ K) m c h (tl< ())

plugR : Ctx → T → T
plugR []          H = H
plugR (pre s ∷ S) H = plugR S (s ++ H)
plugR (nd x ∷ S)  H = plugR S (ψᵗ x H ∷ [])
plugR (sb ∷ S)    H = plugR S (ψᵗ H [] ∷ [])

LIFTR : ∀ S {H H′} m → Core H H′ m → Core (plugR S H) (plugR S H′) m
LIFTR []          m c = c
LIFTR (pre s ∷ S) m c = LIFTR S m (LIFT (pre s ∷ []) m c)
LIFTR (nd x ∷ S)  m c = LIFTR S m (LIFT (nd x ∷ []) m c)
LIFTR (sb ∷ S)    m c = LIFTR S m (LIFT (sb ∷ []) m c)
```

四个核. `pfxC` (前缀) 与 `c4C` (规则 4) 与 Standard 同. 新的 `hdC`: 大小 $\le\mathrm{sz}(x)$ 的 $\zeta<\psi_x(d)$ 也 $<\psi_x(d')+T'$ (首项下标相同的比较要求 $\zeta$ 含 $x$, 大小矛盾); 它处理 "下标不动、参数变了" 的节点 (规则 4、5ω、6、穿透) 在下标框架下的比较与在 `vs` 可见参数里的上界. `leafC`: 大小 $\le\mathrm{sz}(\nu)$ 的 $\zeta<\Omega_{\nu+1}$ 也 $<\psi_\nu(e)+r$ (离散性 `<sucT`: 首项下标 $<\nu$ 直接成立, $=\nu$ 则 $\zeta$ 含 $\nu$, 大小矛盾); 它是正规叶在下标框架下的核, 也是链点下标里的可见参数的核.

```agda
pfxC : ∀ s {R R′} m → m <ℕ sz s → Core (s ++ R) (s ++ R′) m
pfxC s m hm h p = PFX s p (≤-<-trans h hm) _

c4C : ∀ {y d} → cof d ≡ c1 → ∀ T′ → Core (ψᵗ y d ∷ []) (ψᵗ y (pred d) ∷ T′) (sz (pred d))
c4C ce T′ h []<            = []<
c4C ce T′ h (hd< (lv< q))  = hd< (lv< q)
c4C {y} {d} ce T′ {ψᵗ _ e ∷ ζs} h (hd< (ar< q))
  with <sucT (pred d) (subst (e <ᵀ_) (sym (E.pred-suc d ce)) q)
... | inj₁ r    = hd< (ar< r)
... | inj₂ refl = ⊥-elim (<-irrefl refl (<-≤-trans (sz-hdarg y (pred d) ζs) h))
c4C ce T′ h (tl< ())

hdC : ∀ {x d} d′ T′ m → m ≤ℕ sz x → Core (ψᵗ x d ∷ []) (ψᵗ x d′ ∷ T′) m
hdC d′ T′ m hm h []< = []<
hdC d′ T′ m hm h (hd< (lv< q)) = hd< (lv< q)
hdC {x} d′ T′ m hm {ψᵗ _ e ∷ ζs} h (hd< (ar< q)) =
  ⊥-elim (<-irrefl refl (<-≤-trans (sz-sub x e ζs) (≤-trans h hm)))
hdC d′ T′ m hm h (tl< ())

leafC : ∀ {u ν} → sucT ν ≡ u → ∀ e r m → m ≤ℕ sz ν → Core (ψᵗ u [] ∷ []) (ψᵗ ν e ∷ r) m
leafC eu e r m hm h []< = []<
leafC {ν = ν} eu e r m hm {ψᵗ z a ∷ ζs} h (hd< (lv< q)) with <sucT ν (subst (z <ᵀ_) (sym eu) q)
... | inj₁ q′  = hd< (lv< q′)
... | inj₂ refl = ⊥-elim (<-irrefl refl (<-≤-trans (sz-sub ν a ζs) (≤-trans h hm)))
leafC eu e r m hm h (hd< (ar< ()))
leafC eu e r m hm h (tl< ())
```

`HasNd` (上下文含严格缩小的框架, `nd` 或 `sb`), `NoSb` (不含下标框架), 以及两种方向的上下文互换 (`rv`, `plug-rv`, `plugR-rv`, `plugR-mix`, 新的 `plugKS`), 与 Standard 同法, 多 `sb` 情形.

```agda
data HasNd : Ctx → Set where
  here  : ∀ {x K} → HasNd (nd x ∷ K)
  hsb   : ∀ {K} → HasNd (sb ∷ K)
  there : ∀ {f K} → HasNd K → HasNd (f ∷ K)

data NoSb : Ctx → Set where
  ns[]  : NoSb []
  nspre : ∀ {s K} → NoSb K → NoSb (pre s ∷ K)
  nsnd  : ∀ {x K} → NoSb K → NoSb (nd x ∷ K)

rv : Ctx → Ctx
rv []      = []
rv (f ∷ S) = rv S ++ (f ∷ [])

HasNd-++ʳ : ∀ K {K′} → HasNd K′ → HasNd (K ++ K′)
HasNd-++ʳ []      h = h
HasNd-++ʳ (f ∷ K) h = there (HasNd-++ʳ K h)

HasNd-++ˡ : ∀ {K} K′ → HasNd K → HasNd (K ++ K′)
HasNd-++ˡ K′ here      = here
HasNd-++ˡ K′ hsb       = hsb
HasNd-++ˡ K′ (there h) = there (HasNd-++ˡ K′ h)

HasNd-rv : ∀ {S} → HasNd S → HasNd (rv S)
HasNd-rv {nd x ∷ S} here      = HasNd-++ʳ (rv S) here
HasNd-rv {sb ∷ S}   hsb       = HasNd-++ʳ (rv S) hsb
HasNd-rv {f ∷ S}    (there h) = HasNd-++ˡ (f ∷ []) (HasNd-rv h)

NoSb-++ : ∀ {K K′} → NoSb K → NoSb K′ → NoSb (K ++ K′)
NoSb-++ ns[]      n′ = n′
NoSb-++ (nspre n) n′ = nspre (NoSb-++ n n′)
NoSb-++ (nsnd n)  n′ = nsnd (NoSb-++ n n′)

NoSb-rv : ∀ {S} → NoSb S → NoSb (rv S)
NoSb-rv ns[]      = ns[]
NoSb-rv (nspre n) = NoSb-++ (NoSb-rv n) (nspre ns[])
NoSb-rv (nsnd n)  = NoSb-++ (NoSb-rv n) (nsnd ns[])
```

```agda
plugR-++ : ∀ S S′ H → plugR (S ++ S′) H ≡ plugR S′ (plugR S H)
plugR-++ []          S′ H = refl
plugR-++ (pre s ∷ S) S′ H = plugR-++ S S′ (s ++ H)
plugR-++ (nd x ∷ S)  S′ H = plugR-++ S S′ (ψᵗ x H ∷ [])
plugR-++ (sb ∷ S)    S′ H = plugR-++ S S′ (ψᵗ H [] ∷ [])

plug-rv : ∀ S H → plug (rv S) H ≡ plugR S H
plug-rv []          H = refl
plug-rv (pre s ∷ S) H = trans (plug-++ (rv S) (pre s ∷ []) H) (plug-rv S (s ++ H))
plug-rv (nd x ∷ S)  H = trans (plug-++ (rv S) (nd x ∷ []) H) (plug-rv S (ψᵗ x H ∷ []))
plug-rv (sb ∷ S)    H = trans (plug-++ (rv S) (sb ∷ []) H) (plug-rv S (ψᵗ H [] ∷ []))

plugR-rv : ∀ K H → plugR (rv K) H ≡ plug K H
plugR-rv []          H = refl
plugR-rv (pre s ∷ K) H = trans (plugR-++ (rv K) (pre s ∷ []) H) (cong (s ++_) (plugR-rv K H))
plugR-rv (nd x ∷ K)  H = trans (plugR-++ (rv K) (nd x ∷ []) H) (cong (λ z → ψᵗ x z ∷ []) (plugR-rv K H))
plugR-rv (sb ∷ K)    H = trans (plugR-++ (rv K) (sb ∷ []) H) (cong (λ z → ψᵗ z [] ∷ []) (plugR-rv K H))

plugR-mix : ∀ S K H → plugR (S ++ rv K) H ≡ plug K (plugR S H)
plugR-mix S K H = trans (plugR-++ S (rv K) H) (plugR-rv K (plugR S H))

plugKS : ∀ K S H → plug (K ++ rv S) H ≡ plug K (plugR S H)
plugKS K S H = trans (plug-++ K (rv S) H) (cong (plug K) (plug-rv S H))

sz-plugR≤ : ∀ S W → sz W ≤ℕ sz (plugR S W)
sz-plugR≤ []          W = ≤-refl
sz-plugR≤ (pre s ∷ S) W = ≤-trans (sz-suffix s W) (sz-plugR≤ S (s ++ W))
sz-plugR≤ (nd x ∷ S)  W = ≤-trans (<⇒≤ (sz-hdarg x W [])) (sz-plugR≤ S (ψᵗ x W ∷ []))
sz-plugR≤ (sb ∷ S)    W = ≤-trans (<⇒≤ (sz-sub W [] [])) (sz-plugR≤ S (ψᵗ W [] ∷ []))

sz-plugR< : ∀ S W → HasNd S → sz W <ℕ sz (plugR S W)
sz-plugR< (nd x ∷ S)  W here      = <-≤-trans (sz-hdarg x W []) (sz-plugR≤ S (ψᵗ x W ∷ []))
sz-plugR< (sb ∷ S)    W hsb       = <-≤-trans (sz-sub W [] []) (sz-plugR≤ S (ψᵗ W [] ∷ []))
sz-plugR< (pre s ∷ S) W (there h) = ≤-<-trans (sz-suffix s W) (sz-plugR< S (s ++ W) h)
sz-plugR< (nd x ∷ S)  W (there h) = <ℕ-trans (sz-hdarg x W []) (sz-plugR< S (ψᵗ x W ∷ []) h)
sz-plugR< (sb ∷ S)    W (there h) = <ℕ-trans (sz-sub W [] []) (sz-plugR< S (ψᵗ W [] ∷ []) h)

[]<plug : ∀ K {x xs} → [] <ᵀ plug K (x ∷ xs)
[]<plug []                = []<
[]<plug (pre [] ∷ K)      = []<plug K
[]<plug (pre (a ∷ s) ∷ K) = []<
[]<plug (nd y ∷ K)        = []<
[]<plug (sb ∷ K)          = []<

[]<plugR : ∀ S {x xs} → [] <ᵀ plugR S (x ∷ xs)
[]<plugR []                = []<
[]<plugR (pre [] ∷ S)      = []<plugR S
[]<plugR (pre (a ∷ s) ∷ S) = []<plugR S
[]<plugR (nd y ∷ S)        = []<plugR S
[]<plugR (sb ∷ S)          = []<plugR S

plugR-mono : ∀ S {A B} → A <ᵀ B → plugR S A <ᵀ plugR S B
plugR-mono []          p = p
plugR-mono (pre s ∷ S) p = plugR-mono S (++-mono s p)
plugR-mono (nd x ∷ S)  p = plugR-mono S (hd< (ar< p))
plugR-mono (sb ∷ S)    p = plugR-mono S (hd< (lv< p))
```

**下标框架下的交换引理.** `sub<`: $t<\psi_t(a)+r$ (对 $t$ 的首项下标递归; "下标小于它所在的节点" 的句法形式). `swapΩ`: 若 $\Omega<C[\Omega_\Omega]$ 且 $\eta<\Omega$, 则 $\eta<C[\Omega_\eta]$. 证明对 $C$ 下降, 只用 $\eta$ 的首项下标是 $0$: 前缀框架里比较要么在前缀首项处决定 (前缀首项 $\ge\Omega$), 要么前缀首项就是 $\Omega$; 节点框架 $\psi_y$ 有 $y\ge1$; 下标框架的目标是 $\Omega_{C'[\Omega_\eta]}$, 下标非空即可. 它是奇异叶 $\Omega_\Omega$ 在下标框架下的全部内容.

```agda
sub< : ∀ t a r → t <ᵀ ψᵗ t a ∷ r
sub< []            a r = []<
sub< (ψᵗ y b ∷ ys) a r = hd< (lv< (sub< y b ys))

η<Ω-hd : ∀ {η} → η <ᵀ Ωᵗ → ∀ {y} → natT 1 ≤ᵀ y → ∀ R T′ → η <ᵀ ψᵗ y R ∷ T′
η<Ω-hd []< h R T′ = []<
η<Ω-hd (hd< (lv< q)) h R T′ = hd< (lv< (<≤-trans q h))
η<Ω-hd (hd< (ar< ())) h R T′
η<Ω-hd (tl< ()) h R T′

swapΩ : ∀ C {η} → Ωᵗ <ᵀ plug C βᴱ → η <ᵀ Ωᵗ → η <ᵀ plug C (Ωt η)
swapΩ [] p η< = sub< _ [] []
swapΩ (pre [] ∷ C) p η< = swapΩ C p η<
swapΩ (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = η<Ω-hd η< (inj₁ q) R _
swapΩ (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = η<Ω-hd η< (inj₂ refl) R _
swapΩ (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = η<Ω-hd η< (inj₂ refl) [] _
swapΩ (nd y ∷ C) p η< with inv1 p
... | vlv q = η<Ω-hd η< (inj₁ q) _ []
... | var q = η<Ω-hd η< (inj₂ refl) _ []
swapΩ (sb ∷ C) p []< = []<
swapΩ (sb ∷ C) p (hd< (lv< q)) with <sucT [] q
... | inj₁ ()
... | inj₂ refl = hd< (lv< ([]<plug C))
swapΩ (sb ∷ C) p (hd< (ar< ()))
swapΩ (sb ∷ C) p (tl< ())
```

```agda
1<plug : ∀ C {η} → natT 1 <ᵀ plug C (Ωt (Ω₁ ∷ η))
1<plug [] = hd< (lv< []<)
1<plug (pre [] ∷ C) = 1<plug C
1<plug (pre (ψᵗ [] [] ∷ s) ∷ C) {η} = tl< ([]<++ s C {η})
  where
  []<++ : ∀ s C {η} → [] <ᵀ s ++ plug C (Ωt (Ω₁ ∷ η))
  []<++ [] C {η} = []<plug C
  []<++ (_ ∷ _) C = []<
1<plug (pre (ψᵗ [] (_ ∷ _) ∷ s) ∷ C) = hd< (ar< []<)
1<plug (pre (ψᵗ (_ ∷ _) R ∷ s) ∷ C) = hd< (lv< []<)
1<plug (nd [] ∷ C) {η} = hd< (ar< ([]<plug C))
1<plug (nd (_ ∷ _) ∷ C) = hd< (lv< []<)
1<plug (sb ∷ C) = hd< (lv< ([]<plug C))

Ωᵐ-η : ∀ n {η} → η <ᵀ Ωᵗ → Ωᵐ n η <ᵀ Ω₁ ∷ Ωᵐ n []
Ωᵐ-η zero q = q
Ωᵐ-η (suc n) q = tl< (Ωᵐ-η n q)

Ωᵐ-mono : ∀ n {η η′} → η <ᵀ η′ → Ωᵐ n η <ᵀ Ωᵐ n η′
Ωᵐ-mono zero p = p
Ωᵐ-mono (suc n) p = tl< (Ωᵐ-mono n p)

SW : ∀ a b C {η} → Ωᵐ (suc a) [] <ᵀ plug C (Ωt (Ωᵐ (suc (suc b)) [])) → η <ᵀ Ωᵗ → Ωᵐ a η <ᵀ plug C (Ωt (Ωᵐ (suc b) η))
SW zero b [] p []< = []<
SW zero b [] p (hd< (lv< q)) = hd< (lv< (<ᵀ-trans q (hd< (lv< []<))))
SW zero b [] p (hd< (ar< ()))
SW zero b [] p (tl< ())
SW (suc a) b [] p η< = hd< (lv< (hd< (lv< []<)))
SW a b (pre [] ∷ C) p η< = SW a b C p η<
SW zero b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = η<Ω-hd η< (inj₁ q) R _
SW zero b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = η<Ω-hd η< (inj₂ refl) R _
SW zero b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = η<Ω-hd η< (inj₂ refl) [] _
SW (suc a) b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = hd< (lv< q)
SW (suc a) b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = hd< (ar< q)
SW (suc a) b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = tl< (SW a b (pre s ∷ C) q η<)
SW zero b (nd y ∷ C) p η< with inv1 p
... | vlv q = η<Ω-hd η< (inj₁ q) _ []
... | var q = η<Ω-hd η< (inj₂ refl) _ []
SW (suc a) b (nd y ∷ C) p η< with inv1 p
... | vlv q = hd< (lv< q)
... | var q = hd< (ar< ([]<plug C))
SW zero b (sb ∷ C) p []< = []<
SW zero b (sb ∷ C) p (hd< (lv< q)) with <sucT [] q
... | inj₁ ()
... | inj₂ refl = hd< (lv< ([]<plug C))
SW zero b (sb ∷ C) p (hd< (ar< ()))
SW zero b (sb ∷ C) p (tl< ())
SW (suc a) b (sb ∷ C) p η< = hd< (lv< (1<plug C))

1<plug′ : ∀ C {H} → natT 1 <ᵀ H → natT 1 <ᵀ plug C H
1<plug′ [] p = p
1<plug′ (pre [] ∷ C) p = 1<plug′ C p
1<plug′ (pre (ψᵗ [] [] ∷ s) ∷ C) {H} p = tl< (go s)
  where
  ne : ∀ {K} → natT 1 <ᵀ K → [] <ᵀ plug C K
  ne {x ∷ xs} q = []<plug C
  go : ∀ s → [] <ᵀ s ++ plug C H
  go [] = ne p
  go (_ ∷ _) = []<
1<plug′ (pre (ψᵗ [] (_ ∷ _) ∷ s) ∷ C) p = hd< (ar< []<)
1<plug′ (pre (ψᵗ (_ ∷ _) R ∷ s) ∷ C) p = hd< (lv< []<)
1<plug′ (nd [] ∷ C) {x ∷ xs} p = hd< (ar< ([]<plug C))
1<plug′ (nd (_ ∷ _) ∷ C) p = hd< (lv< []<)
1<plug′ (sb ∷ C) {x ∷ xs} p = hd< (lv< ([]<plug C))

SWψ₀ : ∀ a b C {η} → Ωᵐ (suc a) [] <ᵀ plug C (Ωt (ψ¹ ∷ Ωᵐ (suc b) [])) → η <ᵀ Ωᵗ → Ωᵐ a η <ᵀ plug C (Ωt (ψ¹ ∷ Ωᵐ b η))
SWψ₀ zero b [] p []< = []<
SWψ₀ zero b [] p (hd< (lv< q)) = hd< (lv< (<ᵀ-trans q (hd< (lv< []<))))
SWψ₀ zero b [] p (hd< (ar< ()))
SWψ₀ zero b [] p (tl< ())
SWψ₀ (suc a) b [] p η< = hd< (lv< (hd< (lv< []<)))
SWψ₀ a b (pre [] ∷ C) p η< = SWψ₀ a b C p η<
SWψ₀ zero b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = η<Ω-hd η< (inj₁ q) R _
SWψ₀ zero b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = η<Ω-hd η< (inj₂ refl) R _
SWψ₀ zero b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = η<Ω-hd η< (inj₂ refl) [] _
SWψ₀ (suc a) b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = hd< (lv< q)
SWψ₀ (suc a) b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = hd< (ar< q)
SWψ₀ (suc a) b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = tl< (SWψ₀ a b (pre s ∷ C) q η<)
SWψ₀ zero b (nd y ∷ C) p η< with inv1 p
... | vlv q = η<Ω-hd η< (inj₁ q) _ []
... | var q = η<Ω-hd η< (inj₂ refl) _ []
SWψ₀ (suc a) b (nd y ∷ C) p η< with inv1 p
... | vlv q = hd< (lv< q)
... | var q = hd< (ar< ([]<plug C))
SWψ₀ zero b (sb ∷ C) p []< = []<
SWψ₀ zero b (sb ∷ C) p (hd< (lv< q)) with <sucT [] q
... | inj₁ ()
... | inj₂ refl = hd< (lv< ([]<plug C))
SWψ₀ zero b (sb ∷ C) p (hd< (ar< ()))
SWψ₀ zero b (sb ∷ C) p (tl< ())
SWψ₀ (suc a) b (sb ∷ C) p η< = hd< (lv< (1<plug′ C (hd< (lv< []<))))

SWψ : ∀ b C {η} → (ψ¹ ∷ Ωᵐ (suc b) []) <ᵀ plug C (Ωt (ψ¹ ∷ Ωᵐ (suc b) [])) → η <ᵀ Ωᵗ → (ψ¹ ∷ Ωᵐ b η) <ᵀ plug C (Ωt (ψ¹ ∷ Ωᵐ b η))
SWψ b [] p η< = hd< (lv< (hd< (lv< []<)))
SWψ b (pre [] ∷ C) p η< = SWψ b C p η<
SWψ b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (lv< q)) η< = hd< (lv< q)
SWψ b (pre (ψᵗ y R ∷ s) ∷ C) (hd< (ar< q)) η< = hd< (ar< q)
SWψ b (pre (ψᵗ y R ∷ s) ∷ C) (tl< q) η< = tl< (SWψ₀ b b (pre s ∷ C) q η<)
SWψ b (nd y ∷ C) p η< with inv1 p
... | vlv q = hd< (lv< q)
... | var q = hd< (ar< (1<plug′ C (hd< (lv< []<))))
SWψ b (sb ∷ C) p η< = hd< (lv< (1<plug′ C (hd< (lv< []<))))
```

**读法.** `swapΩ` 在下标框架子句里甚至不用前提: $\eta$ 的首项是 $\psi_0(\cdot)$, 而任何非空项都 $>0$. 前提只在前缀与节点框架里用来排除 "$C$ 的首项比 $\Omega$ 小".

## §4 自界引理

`inv0` 是参数为 $0$ 的单项的比较视图 (左边为空, 或首项下标更小). 下标框架的目标是 $\Omega_{K[S[W]]}$, 下标里含有 $W$ 本身; 直接用 Standard 的 `inv1` 报

    [SplitError.UnificationStuck] I'm not sure if there should be a case for the constructor var,
    because I get stuck when trying to solve the following unification
    problems (inferred index ≟ expected index):
      ψᵗ (plug Kr (plugR S W)) a ∷ xs ≟ W
    Possible reason why unification failed:
      Cannot solve variable W of type T with solution
      ψᵗ (plug Kr (plugR S W)) a ∷ xs because the variable occurs in the
      solution, or in the type of one of the variables in the solution.

(`var` 情形要合一出一个出现检查失败的方程; 它其实不可能, 因为参数 $<0$.) `inv0` 不列这个构造子, 即过; §7 的 `vX≮` 用它绕过同型的 `[SplitError.UnificationStuck]` (下标 `γᴱ n` 不归约). 然后是 `HdIs ν η` ($\eta$ 的首项下标是 $\nu$; 链点 $\gamma_k$ 总满足, `hdγ`), 传递它的 `OkΩ` 小引理, 与标准形的投影.

```agda
n≮0 : ∀ {n} → n <ℕ 0 → ⊥
n≮0 ()

data V0 (y : T) : T → Set where
  w[] : V0 y []
  wlv : ∀ {x a xs} → x <ᵀ y → V0 y (ψᵗ x a ∷ xs)

inv0 : ∀ {W y} → W <ᵀ (ψᵗ y [] ∷ []) → V0 y W
inv0 []<           = w[]
inv0 (hd< (lv< q)) = wlv q
inv0 (hd< (ar< ()))
inv0 (tl< ())

c1≢cω : c1 ≡ cω → ⊥
c1≢cω ()

c1≢cΩ : ∀ {ν} → c1 ≡ cΩ ν → ⊥
c1≢cΩ ()

stepPre : ∀ {S s Kr} → HasNd S ⊎ HasNd (pre s ∷ Kr) → HasNd (pre s ∷ S) ⊎ HasNd Kr
stepPre (inj₁ h)         = inj₁ (there h)
stepPre (inj₂ (there h)) = inj₂ h

HdIs : T → T → Set
HdIs ν η = Σ T λ e → Σ T λ r → η ≡ ψᵗ ν e ∷ r

hdγ : ∀ d ν n → HdIs ν (γT d ν n)
hdγ d ν zero    = [] , [] , refl
hdγ d ν (suc n) = _ , [] , refl

OkΩ : Ctx → Ctx → T → T → Set
OkΩ S Kr ν η = (NoSb S × NoSb Kr) ⊎ HdIs ν η

okH : ∀ {S ν η} → OkΩ S [] ν η → NoSb S ⊎ HdIs ν η
okH (inj₁ (a , _)) = inj₁ a
okH (inj₂ h)       = inj₂ h

okPre : ∀ {S s Kr ν η} → OkΩ S (pre s ∷ Kr) ν η → OkΩ (pre s ∷ S) Kr ν η
okPre (inj₁ (a , nspre b)) = inj₁ (nspre a , b)
okPre (inj₂ h)             = inj₂ h

okNd : ∀ {S y Kr ν η} → OkΩ S (nd y ∷ Kr) ν η → OkΩ (nd y ∷ S) Kr ν η
okNd (inj₁ (a , nsnd b)) = inj₁ (nsnd a , b)
okNd (inj₂ h)            = inj₂ h

okR : ∀ {S ν η} → NoSb S ⊎ HdIs ν η → OkΩ [] (rv S) ν η
okR (inj₁ a) = inj₁ (ns[] , NoSb-rv a)
okR (inj₂ h) = inj₂ h

okP : ∀ {S s ν η} → NoSb S ⊎ HdIs ν η → NoSb (pre s ∷ S) ⊎ HdIs ν η
okP (inj₁ a) = inj₁ (nspre a)
okP (inj₂ h) = inj₂ h

okN : ∀ {S x ν η} → NoSb S ⊎ HdIs ν η → NoSb (nd x ∷ S) ⊎ HdIs ν η
okN (inj₁ a) = inj₁ (nsnd a)
okN (inj₂ h) = inj₂ h
```

```agda
nf-arg : ∀ {x a xs} → NF₁ (ψᵗ x a ∷ xs) → NF₁ a
nf-arg (n∷ (nψ _ _ na _) _ _) = na

nf-sub : ∀ {x a xs} → NF₁ (ψᵗ x a ∷ xs) → NF₁ x
nf-sub (n∷ (nψ nx _ _ _) _ _) = nx

nf-sb : ∀ {x a xs} → NF₁ (ψᵗ x a ∷ xs) → Sb x
nf-sb (n∷ (nψ _ sx _ _) _ _) = sx

NF₁-suf : ∀ s {t} → NF₁ (s ++ t) → NF₁ t
NF₁-suf []      n          = n
NF₁-suf (x ∷ s) (n∷ _ n _) = NF₁-suf s n
```

**下标框架处的辅助.** `sbHd`/`sbPfx`/`sbRep`: 节点首项下标不变时, 由 `hdC`/`pfxC` 经 `LIFT`/`LIFTR` 把 "$x<K[S[W]]$" 搬到 "$x<K[S[W']]$". `regSb`: 正规叶 $\Omega_{\nu+1}$ 在下标框架下, $W[\eta]=\eta$; 若 $\eta=\psi_\nu(e)+r$, 则 $\nu<\nu+1<K[S[\Omega_{\nu+1}]]$ 经 `leafC` 提升为 $\nu<K[S[\eta]]$; 若 `OkΩ` 只给出 "无下标框架", 与当前框架是 `sb` 矛盾 (`()`). `sbLeafΩ` 把正规叶 (`regSb`) 与奇异叶 (`swapΩ`) 合在一起. `leafVar` 是节点框架下的叶子 (Standard 的 `leafΩ′`, 多奇异叶一行: $\Omega_\eta<\psi_\Omega(\cdots)$ 由 $\eta<\Omega$). 这些都写成顶层函数: 它们要在 `refl` 上匹配外层的 $\eta$ 或让 `Leaf₁` 合一外层的 $\nu$, where 块里的参数不能被细化.

```agda
sbHd : ∀ Kr S {x a} a′ T′ → x <ᵀ plug Kr (plugR S (ψᵗ x a ∷ [])) →
       (ψᵗ x a′ ∷ T′) <ᵀ plug (sb ∷ Kr) (plugR S (ψᵗ x a′ ∷ T′))
sbHd Kr S {x} a′ T′ q = hd< (lv< (LIFT Kr (sz x) (LIFTR S (sz x) (hdC a′ T′ (sz x) ≤-refl)) ≤-refl q))

sbPfx : ∀ Kr S {x a} R R′ → x <ᵀ plug Kr (plugR S (ψᵗ x a ∷ R)) →
        (ψᵗ x a ∷ R′) <ᵀ plug (sb ∷ Kr) (plugR S (ψᵗ x a ∷ R′))
sbPfx Kr S {x} {a} R R′ q =
  hd< (lv< (LIFT Kr (sz x) (LIFTR S (sz x) (pfxC (ψᵗ x a ∷ []) (sz x) (sz-sub x a []))) ≤-refl q))

sbRep : ∀ Kr S {x a} pd n → x <ᵀ plug Kr (plugR S (ψᵗ x a ∷ [])) →
        replicate n (ψᵗ x pd) <ᵀ plug (sb ∷ Kr) (plugR S (replicate n (ψᵗ x pd)))
sbRep Kr S pd zero    q = []<
sbRep Kr S pd (suc n) q = sbHd Kr S pd (replicate n (ψᵗ _ pd)) q

regSb : ∀ Kr S {u ν} → sucT ν ≡ u → ∀ {η} → OkΩ S (sb ∷ Kr) ν η →
        u <ᵀ plug Kr (plugR S (ψᵗ u [] ∷ [])) → η <ᵀ plug (sb ∷ Kr) (plugR S η)
regSb Kr S eu (inj₁ (_ , ())) q
regSb Kr S {u} {ν} eu (inj₂ (e′ , r , refl)) q =
  hd< (lv< (LIFT Kr (sz ν) (LIFTR S (sz ν) (leafC eu e′ r (sz ν) ≤-refl)) ≤-refl
           (<ᵀ-trans (subst (ν <ᵀ_) eu (E.<-sucT ν)) q)))

sbLeafΩ : ∀ Kr S {w ws ν η} → Sb (w ∷ ws) → cof (ψᵗ (w ∷ ws) [] ∷ []) ≡ cΩ ν → η <ᵀ Ωs ν →
          OkΩ S (sb ∷ Kr) ν η → (w ∷ ws) <ᵀ plug Kr (plugR S (ψᵗ (w ∷ ws) [] ∷ [])) →
          fsT (ψᵗ (w ∷ ws) [] ∷ []) η <ᵀ plug (sb ∷ Kr) (plugR S (fsT (ψᵗ (w ∷ ws) [] ∷ []) η))
sbLeafΩ Kr S {w} {ws} {η = η} s e η< ok q with leafInv₁ (w ∷ ws) s (cof (w ∷ ws)) refl e
... | reg ue = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η))
                     (regSb Kr S (E.pred-suc (w ∷ ws) ue) ok q)
... | sing = hd< (lv< (subst (η <ᵀ_) (plugKS Kr S (Ωt η))
                        (swapΩ (Kr ++ rv S) (subst (Ωᵗ <ᵀ_) (sym (plugKS Kr S βᴱ)) q) η<)))
... | sing² n = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fsT-sing n η))
                 (hd< (lv< (subst (Ωᵐ (suc n) η <ᵀ_) (plugKS Kr S (Ωt (Ωᵐ (suc n) η)))
                    (SW (suc n) n (Kr ++ rv S) (subst (Ωᵐ (suc (suc n)) [] <ᵀ_) (sym (plugKS Kr S (Ωt (Ωᵐ (suc (suc n)) [])))) q) η<))))
... | singψ n = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fsT-singψ n η))
                 (hd< (lv< (subst ((ψ¹ ∷ Ωᵐ n η) <ᵀ_) (plugKS Kr S (Ωt (ψ¹ ∷ Ωᵐ n η)))
                    (SWψ n (Kr ++ rv S) (subst ((ψ¹ ∷ Ωᵐ (suc n) []) <ᵀ_) (sym (plugKS Kr S (Ωt (ψ¹ ∷ Ωᵐ (suc n) [])))) q) η<))))

leafVar : ∀ Kr S {y₀ ν η} → Sb y₀ → cof (ψᵗ y₀ [] ∷ []) ≡ cΩ ν → η <ᵀ Ωs ν →
          fsT (ψᵗ y₀ [] ∷ []) η <ᵀ plug (nd y₀ ∷ Kr) (plugR S (fsT (ψᵗ y₀ [] ∷ []) η))
leafVar Kr S {y₀ = []} s () η<
leafVar Kr S {y₀ = w ∷ ws} {η = η} s e η< with leafInv₁ (w ∷ ws) s (cof (w ∷ ws)) refl e
... | reg ue = subst (λ z → z <ᵀ plug (nd (w ∷ ws) ∷ Kr) (plugR S z)) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η))
                     (belowΩ _ (subst (λ z → η <ᵀ ψᵗ z [] ∷ []) (E.pred-suc (w ∷ ws) ue) η<) (inj₂ refl))
... | sing = hd< (lv< η<)
... | sing² n = subst (λ z → z <ᵀ plug (nd (Ω₁ ∷ Ω₁ ∷ Ωᵐ n []) ∷ Kr) (plugR S z)) (sym (fsT-sing n η)) (hd< (lv< (tl< (Ωᵐ-η n η<))))
... | singψ n = subst (λ z → z <ᵀ plug (nd (ψ¹ ∷ Ω₁ ∷ Ωᵐ n []) ∷ Kr) (plugR S z)) (sym (fsT-singψ n η)) (hd< (lv< (tl< (Ωᵐ-η n η<))))
```

**`SELF`/`SELFΩ`.** 陈述与 Standard 相同, `SELFΩ` 多一个前提 `NoSb S ⊎ HdIs ν η`. 这就是 $\Omega$ 情形需要的新自界引理: 若 $Z<S[Z]$ ($S$ 可以穿过叶子的下标), 且 $S$ 不穿过下标或 $\eta$ 是 $\nu$ 层的链点, 则 $Z[\eta]<S[Z[\eta]]$. 证明仍是对外层上下文下降的 `DESC`/`DESCΩ`.

```agda
SELF  : ∀ m S {Z} → sz Z ≤ℕ m → HasNd S → NF₁ Z → cof Z ≡ cω → Z <ᵀ plugR S Z →
        ∀ n → fsn Z n <ᵀ plugR S (fsn Z n)
SELFΩ : ∀ m S {Z ν η} → sz Z ≤ℕ m → HasNd S → NF₁ Z → cof Z ≡ cΩ ν → η <ᵀ Ωs ν →
        NoSb S ⊎ HdIs ν η → Z <ᵀ plugR S Z → fsT Z η <ᵀ plugR S (fsT Z η)
DESC  : ∀ m S Kr {W} n → sz (plugR S W) ≤ℕ m → HasNd S ⊎ HasNd Kr → NF₁ W → cof W ≡ cω →
        W <ᵀ plug Kr (plugR S W) → fsn W n <ᵀ plug Kr (plugR S (fsn W n))
DESCΩ : ∀ m S Kr {W ν η} → sz (plugR S W) ≤ℕ m → HasNd S ⊎ HasNd Kr → NF₁ W → cof W ≡ cΩ ν →
        η <ᵀ Ωs ν → OkΩ S Kr ν η →
        W <ᵀ plug Kr (plugR S W) → fsT W η <ᵀ plug Kr (plugR S (fsT W η))
```

```agda
SELF m S {Z} h hs nZ e p n =
  subst (fsn Z n <ᵀ_) (plug-rv S (fsn Z n))
        (DESC m [] (rv S) n h (inj₂ (HasNd-rv hs)) nZ e (subst (Z <ᵀ_) (sym (plug-rv S Z)) p))

SELFΩ m S {Z} {η = η} h hs nZ e η< ok p =
  subst (fsT Z η <ᵀ_) (plug-rv S (fsT Z η))
        (DESCΩ m [] (rv S) h (inj₂ (HasNd-rv hs)) nZ e η< (okR ok) (subst (Z <ᵀ_) (sym (plug-rv S Z)) p))
```

前缀框架与节点框架两组子句与 Standard 逐字相同, 只在规则 6 调用 `SELFΩ` 处补上 `inj₂ (hdγ d ν n)`. 下标框架 (新): $W<\Omega_{K[S[W]]}$ 只能是首项下标 $x<K[S[W]]$. 和、以及参数改变的单项 (规则 4、5ω、6) 首项下标不变, 由 `sbPfx`/`sbHd`/`sbRep`; 极限叶 $W=\Omega_w$ 时 $W[n]=\Omega_{w[n]}$, 要证的 $w[n]<K[S[\Omega_{w[n]}]]$ 正是同一陈述在 $w$ 上、上下文多一层 `sb` 的情形, 于是 `DESC m (sb ∷ S) Kr` (外层上下文 `Kr` 变短, 停机检查通过).

```agda
-- hole
DESC zero    S [] {W} n h (inj₁ hs) nW e p = ⊥-elim (n≮0 (<-≤-trans (sz-plugR< S W hs) h))
DESC (suc m) S [] {W} n h (inj₁ hs) nW e p =
  SELF m S (≤-pred (≤-trans (sz-plugR< S W hs) h)) hs nW e p n
DESC m S [] n h (inj₂ ()) nW e p
-- prefix frame
DESC m S (pre s ∷ Kr) {W} n h hk nW e p with split s p
... | inS f = <ᵀ-trans (fs<ᵀ e n) (f _)
... | past [] refl q = <++′ s _ (fs<ᵀ e n)
... | past (x ∷ xs) refl q =
  subst (λ z → z <ᵀ s ++ plug Kr (plugR S z)) (sym (fsn-++ s x xs n))
        (++-mono s (DESC m (pre s ∷ S) Kr n h (stepPre hk) (NF₁-suf s nW) (trans (sym (cof-++ s x xs)) e) q))
-- node frame
DESC m S (nd y₀ ∷ Kr) {W} n h hk nW e p with inv1 p
... | v[] = ⊥-elim (cof[]≢ω e)
... | vlv q = <ᵀ-trans (fs<ᵀ e n) (hd< (lv< q))
... | var {a = d} {xs = x ∷ xs} q =
  hd< (ar< (LIFT Kr (sz d) (LIFTR S (sz d) (pfxC (ψᵗ y₀ d ∷ []) (sz d) (sz-hdarg y₀ d []))) ≤-refl q))
... | var {a = []} {xs = []} q = leafω y₀ e
  where
  leafω : ∀ y₀ → cof (ψᵗ y₀ [] ∷ []) ≡ cω →
          fsn (ψᵗ y₀ [] ∷ []) n <ᵀ plug (nd y₀ ∷ Kr) (plugR S (fsn (ψᵗ y₀ [] ∷ []) n))
  leafω [] ()
  leafω (w ∷ ws) e′ =
    subst (λ z → z <ᵀ plug (nd (w ∷ ws) ∷ Kr) (plugR S z)) (sym (E.fsn0-eq w ws n ke)) (hd< (lv< (fs<ᵀ ke n)))
    where ke = viewL w ws e′
... | var {a = y ∷ ys} {xs = []} q with viewA y₀ y ys e
...   | v4 ke = subst (λ z → z <ᵀ plug (nd y₀ ∷ Kr) (plugR S z)) (sym (fs-rep y₀ y ys ke n)) (rep4 n)
  where
  pd = pred (y ∷ ys)
  rep4 : ∀ k → replicate k (ψᵗ y₀ pd) <ᵀ (ψᵗ y₀ (plug Kr (plugR S (replicate k (ψᵗ y₀ pd)))) ∷ [])
  rep4 zero    = []<
  rep4 (suc k) = hd< (ar< (LIFT Kr (sz pd) (LIFTR S (sz pd) (c4C ke (replicate k (ψᵗ y₀ pd)))) ≤-refl
                                (<ᵀ-trans (E.pred-< (y ∷ ys) ke) q)))
...   | v5 ke = subst (λ z → z <ᵀ plug (nd y₀ ∷ Kr) (plugR S z)) (sym (fs-ω y₀ y ys ke n))
                      (hd< (ar< (DESC m (nd y₀ ∷ S) Kr n h (inj₁ here) (nf-arg nW) ke q)))
...   | v6 ν ke em = subst (λ z → z <ᵀ plug (nd y₀ ∷ Kr) (plugR S z)) (sym (fs-gt y₀ y ys ν ke em n)) (go m h)
  where
  d = y ∷ ys
  γ = γT d ν n
  go : ∀ m′ → sz (plugR S (ψᵗ y₀ d ∷ [])) ≤ℕ m′ →
       (ψᵗ y₀ (fsT d γ) ∷ []) <ᵀ (ψᵗ y₀ (plug Kr (plugR S (ψᵗ y₀ (fsT d γ) ∷ []))) ∷ [])
  go zero h′ = ⊥-elim (n≮0 (<-≤-trans (sz-plugR< (nd y₀ ∷ S) d here) h′))
  go (suc m′) h′ = hd< (ar< (subst (fsT d γ <ᵀ_) (plugR-mix (nd y₀ ∷ S) Kr (fsT d γ))
    (SELFΩ m′ (nd y₀ ∷ S ++ rv Kr) (≤-pred (≤-trans (sz-plugR< (nd y₀ ∷ S) d here) h′))
           here (nf-arg nW) ke (γ<Ωs d ν n) (inj₂ (hdγ d ν n))
           (subst (d <ᵀ_) (sym (plugR-mix (nd y₀ ∷ S) Kr d)) q))))
```

`DESCΩ` 的前缀与节点框架同 Standard, 前提 `OkΩ` 随框架从 `Kr` 移到 `S` (`okPre`, `okNd`), 到洞时交还 `SELFΩ` (`okH`). 下标框架: 首项不变的情形同上; 叶子由 `sbLeafΩ`.

```agda
-- subscript frame
DESC m S (sb ∷ Kr) {W} n h hk nW e p with inv0 p
... | w[] = ⊥-elim (cof[]≢ω e)
... | wlv {x = x} {a = a} {xs = y ∷ ys} q = sbPfx Kr S (y ∷ ys) (fsn (y ∷ ys) n) q
... | wlv {x = []} {a = []} {xs = []} q = ⊥-elim (c1≢cω e)
... | wlv {x = w ∷ ws} {a = []} {xs = []} q =
  subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (E.fsn0-eq w ws n (viewL w ws e)))
        (hd< (lv< (DESC m (sb ∷ S) Kr n h (inj₁ hsb) (nf-sub nW) (viewL w ws e) q)))
... | wlv {x = x} {a = y ∷ ys} {xs = []} q with viewA x y ys e
...   | v4 ke = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fs-rep x y ys ke n)) (sbRep Kr S _ n q)
...   | v5 ke = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fs-ω x y ys ke n)) (sbHd Kr S _ [] q)
...   | v6 ν ke em = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z)) (sym (fs-gt x y ys ν ke em n)) (sbHd Kr S _ [] q)
```

```agda
-- Ω version
DESCΩ zero    S [] {W} h (inj₁ hs) nW e η< ok p = ⊥-elim (n≮0 (<-≤-trans (sz-plugR< S W hs) h))
DESCΩ (suc m) S [] {W} h (inj₁ hs) nW e η< ok p =
  SELFΩ m S (≤-pred (≤-trans (sz-plugR< S W hs) h)) hs nW e η< (okH ok) p
DESCΩ m S [] h (inj₂ ()) nW e η< ok p
DESCΩ m S (pre s ∷ Kr) {W} {η = η} h hk nW e η< ok p with split s p
... | inS f = <ᵀ-trans (fsT-desc e η<) (f _)
... | past [] refl q = <++′ s _ (fsT-desc e η<)
... | past (x ∷ xs) refl q =
  subst (λ z → z <ᵀ s ++ plug Kr (plugR S z)) (sym (fsT-++ s x xs η))
        (++-mono s (DESCΩ m (pre s ∷ S) Kr h (stepPre hk) (NF₁-suf s nW) (trans (sym (cof-++ s x xs)) e) η<
                          (okPre ok) q))
DESCΩ m S (nd y₀ ∷ Kr) {W} {ν} {η} h hk nW e η< ok p with inv1 p
... | v[] = ⊥-elim (cof[]≢Ω e)
... | vlv q = <ᵀ-trans (fsT-desc e η<) (hd< (lv< q))
... | var {a = d} {xs = x ∷ xs} q =
  hd< (ar< (LIFT Kr (sz d) (LIFTR S (sz d) (pfxC (ψᵗ y₀ d ∷ []) (sz d) (sz-hdarg y₀ d []))) ≤-refl q))
... | var {a = []} {xs = []} q = leafVar Kr S (nf-sb nW) e η<
... | var {a = y ∷ ys} {xs = []} q with penInv y₀ (y ∷ ys) (cof (y ∷ ys)) refl e
...   | penΩ be pn =
  subst (λ z → z <ᵀ plug (nd y₀ ∷ Kr) (plugR S z)) (sym (fsT₊-pen′ y₀ (y ∷ ys) ν (cof (y ∷ ys)) be pn η))
        (hd< (ar< (DESCΩ m (nd y₀ ∷ S) Kr h (inj₁ here) (nf-arg nW) be η< (okNd ok) q)))
DESCΩ m S (sb ∷ Kr) {W} {ν} {η} h hk nW e η< ok p with inv0 p
... | w[] = ⊥-elim (cof[]≢Ω e)
... | wlv {x = x} {a = a} {xs = y ∷ ys} q = sbPfx Kr S (y ∷ ys) (fsT (y ∷ ys) η) q
... | wlv {x = []} {a = []} {xs = []} q = ⊥-elim (c1≢cΩ e)
... | wlv {x = w ∷ ws} {a = []} {xs = []} q = sbLeafΩ Kr S (nf-sb nW) e η< ok q
... | wlv {x = x} {a = y ∷ ys} {xs = []} q with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
...   | penΩ be pn = subst (λ z → z <ᵀ plug (sb ∷ Kr) (plugR S z))
                           (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η)) (sbHd Kr S _ [] q)
```

**读法.** 自界引理的新情形只有三种, 都不递归进参数: 首项下标不变 (大小核), 极限叶 (对下标递归), $\Omega$-叶 (`swapΩ` 或 `regSb`). 正规叶的 `regSb` 是唯一用到 `HdIs` 的地方; 对任意 $\eta<\Omega_{\nu+1}$ 的版本本文没有证, 也不需要: §5 的调用点里, 上下文穿过下标时 $\eta$ 总是链点 (`GFS6`), 不穿过下标的调用点给 `inj₁`.

## §5 闭包

Standard §6 的辅助, 换成 `NF₁`/`Vis₁`: `fsT-mono₁` 多奇异叶 ($\Omega_\eta<\Omega_{\eta'}$), `Vis-pred`/`Vis-rep`/`noVis₁` 多 `vs` 情形 (`noVis₁`: $\eta<\Omega_{\nu+1}$ 的标准形在门槛 $>\nu$ 下没有可见参数; `vs` 同样要求门槛 $\le$ 某个首项下标 $\le\nu$).

```agda
fsT-mono₁ : ∀ {d ν η η′} → NF₁ d → cof d ≡ cΩ ν → η <ᵀ η′ → fsT d η <ᵀ fsT d η′
fsT-mono₁ n[] () p
fsT-mono₁ (n∷ nx (n∷ ny nys hy) hx) e p = tl< (fsT-mono₁ (n∷ ny nys hy) e p)
fsT-mono₁ (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () p
fsT-mono₁ {η = η} {η′ = η′} (n∷ (nψ {u = w ∷ ws} {a = []} _ sw _ _) n[] _) e p
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = subst₂ _<ᵀ_ (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η)) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η′)) p
... | sing   = hd< (lv< p)
... | sing² n = subst₂ _<ᵀ_ (sym (fsT-sing n η)) (sym (fsT-sing n η′)) (hd< (lv< (tl< (Ωᵐ-mono n p))))
... | singψ n = subst₂ _<ᵀ_ (sym (fsT-singψ n η)) (sym (fsT-singψ n η′)) (hd< (lv< (tl< (Ωᵐ-mono n p))))
fsT-mono₁ {ν = ν} {η = η} {η′ = η′} (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) e p
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = subst₂ _<ᵀ_ (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η))
                               (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η′))
                               (hd< (ar< (fsT-mono₁ nb be p)))

γ-mono₁ : ∀ {d ν} → NF₁ d → cof d ≡ cΩ ν → ∀ k → γT d ν k <ᵀ γT d ν (suc k)
γ-mono₁ nD e zero    = hd< (ar< (fsT-ne e []<))
γ-mono₁ nD e (suc k) = hd< (ar< (fsT-mono₁ nD e (γ-mono₁ nD e k)))

Vis-pred : ∀ {w ζ d} → cof d ≡ c1 → Vis₁ w ζ (pred d) → Vis₁ w ζ d
Vis-pred {d = []} e v = v
Vis-pred {d = x ∷ y ∷ ys} e (vh h)   = vh h
Vis-pred {d = x ∷ y ∷ ys} e (vd h v) = vd h v
Vis-pred {d = x ∷ y ∷ ys} e (vs h v) = vs h v
Vis-pred {d = x ∷ y ∷ ys} e (vt v)   = vt (Vis-pred e v)
Vis-pred {d = ψᵗ [] [] ∷ []} e ()
Vis-pred {d = ψᵗ [] (y ∷ ys) ∷ []} e v = v
Vis-pred {d = ψᵗ (w ∷ ws) a ∷ []} e v = v

Vis-rep : ∀ k {w ζ y} → Vis₁ w ζ (replicate (suc k) y) → Vis₁ w ζ (y ∷ [])
Vis-rep zero    v        = v
Vis-rep (suc k) (vh h)   = vh h
Vis-rep (suc k) (vd h v) = vd h v
Vis-rep (suc k) (vs h v) = vs h v
Vis-rep (suc k) (vt v)   = Vis-rep k v

Bnd-pred : ∀ {w d} → Bnd₁ w d → cof d ≡ c1 → Bnd₁ w (pred d)
Bnd-pred {d = d} g e {ζ} v with <sucT (pred d) (subst (ζ <ᵀ_) (sym (E.pred-suc d e)) (g (Vis-pred e v)))
... | inj₁ r    = r
... | inj₂ refl = ⊥-elim (<-irrefl refl (Vis-sz v))

NF₁-rep : ∀ {x} → NFᴾ₁ x → ∀ n → NF₁ (replicate n x)
NF₁-rep nx zero          = n[]
NF₁-rep nx (suc zero)    = n∷ nx n[] tt
NF₁-rep {x = x} nx (suc (suc n)) = n∷ nx (NF₁-rep nx (suc n)) (inj₂ (cmpᴾ-refl x))

noVis₁ : ∀ {η ν x ζ} → NF₁ η → η <ᵀ Ωs ν → sucT ν ≤ᵀ x → Vis₁ x ζ η → ⊥
noVis₁ nη (hd< (lv< q)) h (vh h′)   = <→≱ q (≤-trans′ h h′)
noVis₁ nη (hd< (lv< q)) h (vd h′ _) = <→≱ q (≤-trans′ h h′)
noVis₁ nη (hd< (lv< q)) h (vs h′ _) = <→≱ q (≤-trans′ h h′)
noVis₁ (n∷ _ nzs hz) (hd< p) h (vt v) = noVis₁ nzs (tail< hz p) h v
noVis₁ nη (hd< (ar< ())) h v
noVis₁ nη (tl< ()) h v
```

**链点下标里的可见参数.** $\gamma_k=\psi_\nu(\cdots)$, 门槛 $u\le\nu$ 时 `vs` 进入 $\nu$. `visLeaf`: $\nu$ 的 $u$-可见参数也是 $d$ 的 (沿穿透节点 $y\ge\nu+1>u$ 走到正规叶 $\Omega_{\nu+1}$, 再进下标 $\nu+1=\nu\mathbin{+\!\!+}[1]$; 奇异叶 $\nu=0$ 没有可见参数). `leafLift`: 大小 $\le\mathrm{sz}(\nu)$ 的 $\zeta<S[d]$ 也 $<S[d[\psi_\nu(e)+r]]$ (沿 $d$ 的 $\Omega$-脊递归, 正规叶处 `leafC`, 奇异叶处 $\zeta=0$). 合起来 `gLeaf`: $\nu$ 的可见参数对每个 $S[d[\gamma_k]]$ 有界.

```agda
visLeaf : ∀ {d ν u ζ} → NF₁ d → cof d ≡ cΩ ν → u ≤ᵀ ν → Vis₁ u ζ ν → Vis₁ u ζ d
visLeaf n[] () h v
visLeaf (n∷ nx (n∷ ny nys hy) hx) e h v = vt (visLeaf (n∷ ny nys hy) e h v)
visLeaf (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () h v
visLeaf {u = u} {ζ = ζ} (n∷ (nψ {u = w ∷ ws} {a = []} _ sw _ _) n[] _) e h v
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = vs (inj₁ (≤<-trans h (subst (pred (w ∷ ws) <ᵀ_) (E.pred-suc (w ∷ ws) ue) (E.<-sucT _))))
                  (subst (Vis₁ u ζ) (E.pred-suc (w ∷ ws) ue) (Vis-++ (E.𝟏 ∷ []) v))
... | sing² n = ⊥-elim (noV′ v)
  where noV′ : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV′ ()
... | singψ n = ⊥-elim (noV″ v)
  where noV″ : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV″ ()
... | sing = ⊥-elim (noV v)
  where noV : ∀ {u ζ} → Vis₁ u ζ [] → ⊥
        noV ()
visLeaf {ν = ν} (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) e h v
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = vd (inj₁ (≤<-trans h (pen→< ν x pn))) (visLeaf nb be h v)

sz0< : ∀ {ζ} → sz ζ ≤ℕ 0 → ∀ S {x xs} → ζ <ᵀ plugR S (x ∷ xs)
sz0< {ζ = []} h S = []<plugR S
sz0< {ζ = ψᵗ _ _ ∷ _} () S

leafLift : ∀ S {d ν ζ} → NF₁ d → cof d ≡ cΩ ν → sz ζ ≤ℕ sz ν → ζ <ᵀ plugR S d →
           ∀ e r → ζ <ᵀ plugR S (fsT d (ψᵗ ν e ∷ r))
leafLift S n[] () hz p e r
leafLift S {d = x ∷ _} (n∷ nx (n∷ ny nys hy) hx) ce hz p e r =
  leafLift (pre (x ∷ []) ∷ S) (n∷ ny nys hy) ce hz p e r
leafLift S (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () hz p e r
leafLift S {ζ = ζ} (n∷ (nψ {u = w ∷ ws} {a = []} _ sw _ _) n[] _) ce hz p e r
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl ce
... | reg ue = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue _))
                     (LIFTR S (sz ζ) (leafC (E.pred-suc (w ∷ ws) ue) e r (sz ζ) hz) ≤-refl p)
... | sing = sz0< hz S
... | sing² n = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-sing n _)) (sz0< hz S)
... | singψ n = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT-singψ n _)) (sz0< hz S)
leafLift S {ν = ν} {ζ = ζ} (n∷ (nψ {u = x} {a = y ∷ ys} _ _ nb _) n[] _) ce hz p e r
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl ce
... | penΩ be pn = subst (λ z → ζ <ᵀ plugR S z) (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn _))
                         (leafLift (nd x ∷ S) nb be hz p e r)

gLeaf : ∀ u S {d ν} → NF₁ d → cof d ≡ cΩ ν → (∀ {ζ} → Vis₁ u ζ d → ζ <ᵀ plugR S d) →
        u ≤ᵀ ν → ∀ {ζ} → Vis₁ u ζ ν → ∀ e r → ζ <ᵀ plugR S (fsT d (ψᵗ ν e ∷ r))
gLeaf u S nD e H h v e′ r = leafLift S nD e (<⇒≤ (Vis-sz v)) (H (visLeaf nD e h v)) e′ r
```

**可见参数的保持** `GFS`/`GΩ`/`Gγ` 与 Standard 同构. 新增: 每个节点的 `vs` 情形 (下标不动: `fixSb` 即 `hdC` 经 `LIFTR`; 首项 `fixHd` 多一行); 极限叶的下标 (`GFSL`: $\Omega_{w[n]}$ 的 `vs` 可见参数在 $w[n]$ 里, 对 $w$ 递归, 上下文加 `sb`, 门槛 $u\le w[n]<w$); 奇异叶的 $\Omega$-基本列 (`singG`: $\Omega_\eta$ 的 `vs` 可见参数在 $\eta$ 里, 由前提 `Hη`); 链点下标 (`Gγ` 的 `vs` 情形, `gLeaf`). `GΩ`/`GΩp` 多带 `NoSb S ⊎ HdIs ν η` 并在 `vh` 处交给 `SELFΩ`; `GFS6` 给 `inj₂ (hdγ …)`, 顶层调用 (`NF₁-fsT`, `NF₁-γ`, `NF₁-fsn`) 给 `inj₁ ns[]`. 极限叶写成顶层互递归的 `GFSL`, 直接接收子推导 `nw` (Standard 的工程注记: where 局部函数经 `subst` 传出会触发 `TerminationIssue`).

```agda
GFS : ∀ u S {X} n → NF₁ X → cof X ≡ cω → (∀ {ζ} → Vis₁ u ζ X → ζ <ᵀ plugR S X) →
      ∀ {ζ′} → Vis₁ u ζ′ (fsn X n) → ζ′ <ᵀ plugR S (fsn X n)
GFSL : ∀ u S {w ws} n → NF₁ (w ∷ ws) → cof (w ∷ ws) ≡ cω →
       (∀ {ζ} → Vis₁ u ζ (Ωt (w ∷ ws)) → ζ <ᵀ plugR S (Ωt (w ∷ ws))) →
       ∀ {ζ′} → Vis₁ u ζ′ (Ωt (fsn (w ∷ ws) n)) → ζ′ <ᵀ plugR S (Ωt (fsn (w ∷ ws) n))
GFS5 : ∀ u S x {d} n → NF₁ d → cof d ≡ cω → (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
       ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ x (fsn d n) ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x (fsn d n) ∷ [])
GFS6 : ∀ u S x {d ν} n → NF₁ d → cof d ≡ cΩ ν → (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
       ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ x (fsT d (γT d ν n)) ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x (fsT d (γT d ν n)) ∷ [])
GΩ  : ∀ u S {X ν η} → NF₁ X → cof X ≡ cΩ ν → η <ᵀ Ωs ν → NoSb S ⊎ HdIs ν η →
      (∀ {ζ} → Vis₁ u ζ X → ζ <ᵀ plugR S X) →
      (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (fsT X η)) →
      ∀ {ζ′} → Vis₁ u ζ′ (fsT X η) → ζ′ <ᵀ plugR S (fsT X η)
GΩp : ∀ u S x {d ν η} → NF₁ d → cof d ≡ cΩ ν → η <ᵀ Ωs ν → NoSb S ⊎ HdIs ν η →
      (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
      (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (ψᵗ x (fsT d η) ∷ [])) →
      ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ x (fsT d η) ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x (fsT d η) ∷ [])
Gγ  : ∀ u S {d ν} → NF₁ d → cof d ≡ cΩ ν → (∀ {ζ} → Vis₁ u ζ d → ζ <ᵀ plugR S d) →
      (∀ k → fsT d (γT d ν k) ≤ᵀ plugR S (fsT d (γT d ν k))) →
      ∀ k {ζ} → Vis₁ u ζ (γT d ν k) → ζ <ᵀ plugR S (fsT d (γT d ν k))
```

```agda
fixHd : ∀ u S {x₀ a R R′ ζ} → (∀ {ζ} → Vis₁ u ζ (ψᵗ x₀ a ∷ R) → ζ <ᵀ plugR S (ψᵗ x₀ a ∷ R)) →
        Vis₁ u ζ (ψᵗ x₀ a ∷ []) → ζ <ᵀ plugR S (ψᵗ x₀ a ∷ R′)
fixHd u S {x₀ = x₀} {a = a} H (vh h) = LIFTR S (sz a) (pfxC (ψᵗ x₀ a ∷ []) (sz a) (sz-hdarg x₀ a [])) ≤-refl (H (vh h))
fixHd u S {x₀ = x₀} {a = a} {ζ = ζ} H (vd h v) =
  LIFTR S (sz ζ) (pfxC (ψᵗ x₀ a ∷ []) (sz ζ) (<ℕ-trans (Vis-sz v) (sz-hdarg x₀ a []))) ≤-refl (H (vd h v))
fixHd u S {x₀ = x₀} {a = a} {ζ = ζ} H (vs h v) =
  LIFTR S (sz ζ) (pfxC (ψᵗ x₀ a ∷ []) (sz ζ) (<ℕ-trans (Vis-sz v) (sz-sub x₀ a []))) ≤-refl (H (vs h v))
fixHd u S H (vt ())

-- a subscript-visible argument of a node whose subscript is unchanged
fixSb : ∀ u S {x d} d′ T′ {ζ} → (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
        u ≤ᵀ x → Vis₁ u ζ x → ζ <ᵀ plugR S (ψᵗ x d′ ∷ T′)
fixSb u S d′ T′ {ζ} H h v = LIFTR S (sz ζ) (hdC d′ T′ (sz ζ) (<⇒≤ (Vis-sz v))) ≤-refl (H (vs h v))

GFS4 : ∀ u S x {d} n → cof d ≡ c1 → (∀ {ζ} → Vis₁ u ζ (ψᵗ x d ∷ []) → ζ <ᵀ plugR S (ψᵗ x d ∷ [])) →
       ∀ {ζ′} → Vis₁ u ζ′ (replicate n (ψᵗ x (pred d))) → ζ′ <ᵀ plugR S (replicate n (ψᵗ x (pred d)))
GFS4 u S x {d} (suc m) ke H v′ = k1 (Vis-rep m v′)
  where
  pd = pred d
  k1 : ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ x pd ∷ []) → ζ′ <ᵀ plugR S (ψᵗ x pd ∷ replicate m (ψᵗ x pd))
  k1 (vh h)    = LIFTR S (sz pd) (c4C ke _) ≤-refl (<ᵀ-trans (E.pred-< d ke) (H (vh h)))
  k1 (vd h v″) = LIFTR S (sz pd) (c4C ke _) (<⇒≤ (Vis-sz v″)) (H (vd h (Vis-pred ke v″)))
  k1 (vs h v″) = fixSb u S pd _ H h v″
  k1 (vt ())
```

```agda
GFS u S n n[] () v
GFS u S n (n∷ nx (n∷ ny nys hy) hx) e H (vh h)   = fixHd u S H (vh h)
GFS u S n (n∷ nx (n∷ ny nys hy) hx) e H (vd h v) = fixHd u S H (vd h v)
GFS u S n (n∷ nx (n∷ ny nys hy) hx) e H (vs h v) = fixHd u S H (vs h v)
GFS u S {X = x ∷ _} n (n∷ nx (n∷ ny nys hy) hx) e H (vt v) =
  GFS u (pre (x ∷ []) ∷ S) n (n∷ ny nys hy) e (λ v′ → H (vt v′)) v
GFS u S n (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () v
GFS u S {X = ψᵗ (w ∷ ws) [] ∷ []} n (n∷ (nψ nw sw na g) n[] hx) e H {ζ′} v =
  subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym (E.fsn0-eq w ws n (viewL w ws e)))
        (GFSL u S n nw (viewL w ws e) H) v
GFS u S {X = ψᵗ x (y ∷ ys) ∷ []} n (n∷ (nψ nx cx nb g) n[] hx) e H {ζ′} v with viewA x y ys e
... | v4 ke = subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym (fs-rep x y ys ke n)) (GFS4 u S x n ke H) v
... | v5 ke = subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym (fs-ω x y ys ke n)) (GFS5 u S x n nb ke H) v
... | v6 ν ke em = subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym (fs-gt x y ys ν ke em n)) (GFS6 u S x n nb ke H) v

GFSL u S n nw ke H (vh h) = []<plugR S
GFSL u S n nw ke H (vd h ())
GFSL u S n nw ke H (vt ())
GFSL u S n nw ke H (vs h v′) =
  GFS u (sb ∷ S) n nw ke (λ v → H (vs (inj₁ (≤<-trans h (fs<ᵀ ke n))) v)) v′
```

```agda
GFS5 u S x {d} n nb ke H (vh h)    = SELF (sz d) (nd x ∷ S) ≤-refl here nb ke (H (vh h)) n
GFS5 u S x n nb ke H (vd h v′) = GFS u (nd x ∷ S) n nb ke (λ v″ → H (vd h v″)) v′
GFS5 u S x n nb ke H (vs h v′) = fixSb u S _ [] H h v′
GFS5 u S x n nb ke H (vt ())

GFS6 u S x {d} {ν} n nb ke H (vh h) =
  SELFΩ (sz d) (nd x ∷ S) ≤-refl here nb ke (γ<Ωs d ν n) (inj₂ (hdγ d ν n)) (H (vh h))
GFS6 u S x {d} {ν} n nb ke H (vd h v′) =
  GΩ u (nd x ∷ S) nb ke (γ<Ωs d ν n) (inj₂ (hdγ d ν n)) (λ v″ → H (vd h v″))
     (Gγ u (nd x ∷ S) nb ke (λ v″ → H (vd h v″))
         (λ j → inj₁ (SELFΩ (sz d) (nd x ∷ S) ≤-refl here nb ke (γ<Ωs d ν j) (inj₂ (hdγ d ν j)) (H (vh h)))) n) v′
GFS6 u S x n nb ke H (vs h v′) = fixSb u S _ [] H h v′
GFS6 u S x n nb ke H (vt ())
```

```agda
singG : ∀ u S {η} → (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (ψᵗ η [] ∷ [])) →
        ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ η [] ∷ []) → ζ′ <ᵀ plugR S (ψᵗ η [] ∷ [])
singG u S Hη (vh h)   = []<plugR S
singG u S Hη (vd h ())
singG u S Hη (vs h v) = Hη v
singG u S Hη (vt ())

visΩᵐ : ∀ {u ζ′ η x xs} n S → (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (x ∷ xs)) → Vis₁ u ζ′ (Ωᵐ n η) → ζ′ <ᵀ plugR S (x ∷ xs)
visΩᵐ zero S Hη v = Hη v
visΩᵐ (suc n) S Hη (vh h) = []<plugR S
visΩᵐ (suc n) S Hη (vd h ())
visΩᵐ (suc n) S Hη (vs h (vh h′)) = []<plugR S
visΩᵐ (suc n) S Hη (vs h (vd h′ ()))
visΩᵐ (suc n) S Hη (vs h (vs h′ ()))
visΩᵐ (suc n) S Hη (vs h (vt ()))
visΩᵐ (suc n) S Hη (vt v) = visΩᵐ n S Hη v

singG² : ∀ n u S {η} → (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (ψᵗ (Ω₁ ∷ Ωᵐ n η) [] ∷ [])) →
         ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ (Ω₁ ∷ Ωᵐ n η) [] ∷ []) → ζ′ <ᵀ plugR S (ψᵗ (Ω₁ ∷ Ωᵐ n η) [] ∷ [])
singG² n u S Hη (vh h)   = []<plugR S
singG² n u S Hη (vd h ())
singG² n u S Hη (vs h v) = visΩᵐ (suc n) S Hη v
singG² n u S Hη (vt ())

1<plugR : ∀ S {H} → natT 1 <ᵀ H → natT 1 <ᵀ plugR S H
1<plugR [] p = p
1<plugR (pre [] ∷ S) p = 1<plugR S p
1<plugR (pre (ψᵗ [] [] ∷ s) ∷ S) {x ∷ xs} p = 1<plugR S (tl< (go s))
  where
  go : ∀ s → [] <ᵀ s ++ (x ∷ xs)
  go [] = []<
  go (_ ∷ _) = []<
1<plugR (pre (ψᵗ [] (_ ∷ _) ∷ s) ∷ S) p = 1<plugR S (hd< (ar< []<))
1<plugR (pre (ψᵗ (_ ∷ _) R ∷ s) ∷ S) p = 1<plugR S (hd< (lv< []<))
1<plugR (nd [] ∷ S) {x ∷ xs} p = 1<plugR S (hd< (ar< []<))
1<plugR (nd (_ ∷ _) ∷ S) p = 1<plugR S (hd< (lv< []<))
1<plugR (sb ∷ S) {x ∷ xs} p = 1<plugR S (hd< (lv< []<))

singGψ : ∀ n u S {η} → (∀ {ζ} → Vis₁ u ζ η → ζ <ᵀ plugR S (ψᵗ (ψ¹ ∷ Ωᵐ n η) [] ∷ [])) →
         ∀ {ζ′} → Vis₁ u ζ′ (ψᵗ (ψ¹ ∷ Ωᵐ n η) [] ∷ []) → ζ′ <ᵀ plugR S (ψᵗ (ψ¹ ∷ Ωᵐ n η) [] ∷ [])
singGψ n u S Hη (vh h)   = []<plugR S
singGψ n u S Hη (vd h ())
singGψ n u S Hη (vs h (vh h′)) = 1<plugR S (hd< (lv< []<))
singGψ n u S Hη (vs h (vd h′ (vh h″))) = []<plugR S
singGψ n u S Hη (vs h (vd h′ (vd h″ ())))
singGψ n u S Hη (vs h (vd h′ (vs h″ ())))
singGψ n u S Hη (vs h (vd h′ (vt ())))
singGψ n u S Hη (vs h (vs h′ (vh h″))) = []<plugR S
singGψ n u S Hη (vs h (vs h′ (vd h″ ())))
singGψ n u S Hη (vs h (vs h′ (vs h″ ())))
singGψ n u S Hη (vs h (vs h′ (vt ())))
singGψ n u S Hη (vs h (vt v)) = visΩᵐ n S Hη v
singGψ n u S Hη (vt ())

GΩ u S n[] () η< ok H Hη v
GΩ u S (n∷ nx (n∷ ny nys hy) hx) e η< ok H Hη (vh h)   = fixHd u S H (vh h)
GΩ u S (n∷ nx (n∷ ny nys hy) hx) e η< ok H Hη (vd h v) = fixHd u S H (vd h v)
GΩ u S (n∷ nx (n∷ ny nys hy) hx) e η< ok H Hη (vs h v) = fixHd u S H (vs h v)
GΩ u S {X = x ∷ _} (n∷ nx (n∷ ny nys hy) hx) e η< ok H Hη (vt v) =
  GΩ u (pre (x ∷ []) ∷ S) (n∷ ny nys hy) e η< (okP ok) (λ v′ → H (vt v′)) Hη v
GΩ u S (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () η< ok H Hη v
GΩ u S {X = ψᵗ (w ∷ ws) [] ∷ []} {η = η} (n∷ (nψ nw sw _ _) n[] _) e η< ok H Hη {ζ′} v
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = Hη (subst (Vis₁ u ζ′) (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η) v)
... | sing   = singG u S Hη v
... | sing² n = subst (λ z → ζ′ <ᵀ plugR S z) (sym (fsT-sing n η)) (singG² n u S (λ v′ → subst (λ z → _ <ᵀ plugR S z) (fsT-sing n η) (Hη v′)) (subst (Vis₁ u ζ′) (fsT-sing n η) v))
... | singψ n = subst (λ z → ζ′ <ᵀ plugR S z) (sym (fsT-singψ n η)) (singGψ n u S (λ v′ → subst (λ z → _ <ᵀ plugR S z) (fsT-singψ n η) (Hη v′)) (subst (Vis₁ u ζ′) (fsT-singψ n η) v))
GΩ u S {X = ψᵗ x (y ∷ ys) ∷ []} {ν = ν} {η = η} (n∷ (nψ nx cx nb g) n[] hx) e η< ok H Hη {ζ′} v
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = subst (λ z → Vis₁ u ζ′ z → ζ′ <ᵀ plugR S z) (sym eqT)
                         (GΩp u S x nb be η< ok H (λ {ζ} vη → subst (λ z → ζ <ᵀ plugR S z) eqT (Hη vη))) v
  where
  eqT : fsT (ψᵗ x (y ∷ ys) ∷ []) η ≡ ψᵗ x (fsT (y ∷ ys) η) ∷ []
  eqT = fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η

GΩp u S x {d} nb be η< ok H Hη (vh h)    = SELFΩ (sz d) (nd x ∷ S) ≤-refl here nb be η< (okN ok) (H (vh h))
GΩp u S x nb be η< ok H Hη (vd h v′) = GΩ u (nd x ∷ S) nb be η< (okN ok) (λ v″ → H (vd h v″)) Hη v′
GΩp u S x nb be η< ok H Hη (vs h v′) = fixSb u S _ [] H h v′
GΩp u S x nb be η< ok H Hη (vt ())
```

```agda
Gγ u S nD e H Sγ zero (vh h) = <≤-trans (fsT-ne e []<) (Sγ zero)
Gγ u S nD e H Sγ zero (vd h ())
Gγ u S nD e H Sγ zero (vs h v) = gLeaf u S nD e H h v [] []
Gγ u S nD e H Sγ zero (vt ())
Gγ u S nD e H Sγ (suc k) (vh h) = <≤-trans (fsT-mono₁ nD e (γ-mono₁ nD e k)) (Sγ (suc k))
Gγ u S {d = d} {ν = ν} nD e H Sγ (suc k) (vd h v) =
  <ᵀ-trans (GΩ u S nD e (γ<Ωs d ν k) (inj₂ (hdγ d ν k)) H (Gγ u S nD e H Sγ k) v)
           (plugR-mono S (fsT-mono₁ nD e (γ-mono₁ nD e k)))
Gγ u S nD e H Sγ (suc k) (vs h v) = gLeaf u S nD e H h v _ []
Gγ u S nD e H Sγ (suc k) (vt ())
```

**闭包定理.** 与 Standard 同形; 新子句是奇异叶的 `NF₁-fsT` ($\Omega_\Omega[\eta]=\Omega_\eta$, 下标 $\eta$ 由 `ctblΩ` 是 `Sb`) 与极限叶的 `NF₁-fsn` (下标 $w[n]$ 由 `Sb-fsn`; 外层节点的 `Bnd₁` 由 `GFS`, 其中经 `GFSL` 进入下标). `desc-NF₁`: 标准形的一切基本列后代 (Standard 的 `Desc`) 是标准形.

```agda
nf1′ : NF₁ (natT 1)
nf1′ = n∷ (nψ n[] (sC c[]) n[] bnd[]) n[] tt

hdΩ : ∀ {θ} → Ctbl θ → Hd≤ θ Ω₁
hdΩ c[] = tt
hdΩ (c∷ ct) = inj₁ refl

nfΩ₁ : NFᴾ₁ Ω₁
nfΩ₁ = nψ nf1′ (sC (c∷ c[])) n[] bnd[]

hdΩᵐ : ∀ n {θ} → Ctbl θ → Hd≤ (Ωᵐ n θ) Ω₁
hdΩᵐ zero c = hdΩ c
hdΩᵐ (suc n) c = inj₂ refl

NFΩᵐ : ∀ n {θ} → NF₁ θ → Ctbl θ → NF₁ (Ωᵐ n θ)
NFΩᵐ zero nθ c = nθ
NFΩᵐ (suc n) nθ c = n∷ nfΩ₁ (NFΩᵐ n nθ c) (hdΩᵐ n c)

SbΩᵐ : ∀ n {θ} → Ctbl θ → Sb (Ω₁ ∷ Ωᵐ n θ)
SbΩᵐ zero c = sΩ c
SbΩᵐ (suc n) c = sΩ² n c

nfψ¹ : NFᴾ₁ ψ¹
nfψ¹ = nψ nf1′ (sC (c∷ c[])) nf1′ b
  where
  b : Bnd₁ (natT 1) (natT 1)
  b (vh (inj₁ ()))
  b (vh (inj₂ ()))
  b (vd (inj₁ ()) _)
  b (vd (inj₂ ()) _)
  b (vs (inj₁ ()) _)
  b (vs (inj₂ ()) _)
  b (vt ())

hdψ¹ : ∀ n {θ} → Ctbl θ → Hd≤ (Ωᵐ n θ) ψ¹
hdψ¹ zero c[] = tt
hdψ¹ zero (c∷ ct) = inj₁ refl
hdψ¹ (suc n) c = inj₁ refl

NFψ¹ : ∀ n {θ} → NF₁ θ → Ctbl θ → NF₁ (ψ¹ ∷ Ωᵐ n θ)
NFψ¹ n nθ c = n∷ nfψ¹ (NFΩᵐ n nθ c) (hdψ¹ n c)

NF₁-fsT : ∀ {d ν η} → NF₁ d → cof d ≡ cΩ ν → NF₁ η → η <ᵀ Ωs ν → NF₁ (fsT d η)
NF₁-fsT n[] () nη η<
NF₁-fsT (n∷ nx (n∷ {x = y} {xs = ys} ny nys hy) hx) e nη η< =
  n∷ nx (NF₁-fsT (n∷ ny nys hy) e nη η<) (Hd≤-desc (fsT-desc {W = y ∷ ys} e η<) hx)
NF₁-fsT (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () nη η<
NF₁-fsT {η = η} (n∷ (nψ {u = w ∷ ws} {a = []} _ sw _ _) n[] _) e nη η<
  with leafInv₁ (w ∷ ws) sw (cof (w ∷ ws)) refl e
... | reg ue = subst NF₁ (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ue η)) nη
... | sing   = n∷ (nψ nη (sC (ctblΩ nη η<)) n[] bnd[]) n[] tt
... | sing² n = subst NF₁ (sym (fsT-sing n η)) (n∷ (nψ (NFΩᵐ (suc n) nη (ctblΩ nη η<)) (SbΩᵐ n (ctblΩ nη η<)) n[] bnd[]) n[] tt)
... | singψ n = subst NF₁ (sym (fsT-singψ n η)) (n∷ (nψ (NFψ¹ n nη (ctblΩ nη η<)) (sψ n (ctblΩ nη η<)) n[] bnd[]) n[] tt)
NF₁-fsT {ν = ν} {η = η} (n∷ (nψ {u = x} {a = y ∷ ys} nx cx nb g) n[] _) e nη η<
  with penInv x (y ∷ ys) (cof (y ∷ ys)) refl e
... | penΩ be pn = subst NF₁ (sym (fsT₊-pen′ x (y ∷ ys) ν (cof (y ∷ ys)) be pn η))
  (n∷ (nψ nx cx (NF₁-fsT nb be nη η<)
          (λ v → GΩ x [] nb be η< (inj₁ ns[]) g (λ vη → ⊥-elim (noVis₁ nη η< (Pen→≤ (sucT ν) x pn) vη)) v)) n[] tt)

NF₁-γ : ∀ {d ν} → NF₁ d → cof d ≡ cΩ ν → NF₁ ν → Sb ν → Bnd₁ ν d → ∀ k → NF₁ (γT d ν k)
NF₁-γ nD e nν sν g zero    = n∷ (nψ nν sν n[] bnd[]) n[] tt
NF₁-γ {d = d} {ν = ν} nD e nν sν g (suc k) =
  n∷ (nψ nν sν (NF₁-fsT nD e (NF₁-γ nD e nν sν g k) (γ<Ωs d ν k))
         (λ v → GΩ ν [] nD e (γ<Ωs d ν k) (inj₁ ns[]) g (Gγ ν [] nD e g (λ _ → inj₂ refl) k) v)) n[] tt

NF₁-fsn : ∀ {t} → NF₁ t → cof t ≡ cω → ∀ n → NF₁ (fsn t n)
NF₁-fsn n[] () n
NF₁-fsn (n∷ nx (n∷ {x = y} {xs = ys} ny nys hy) hx) e n =
  n∷ nx (NF₁-fsn (n∷ ny nys hy) e n) (Hd≤-desc (fs<ᵀ {u = y ∷ ys} e n) hx)
NF₁-fsn (n∷ (nψ {u = []} {a = []} _ _ _ _) n[] _) () n
NF₁-fsn (n∷ (nψ {u = w ∷ ws} {a = []} nw sw _ _) n[] _) e n =
  subst NF₁ (sym (E.fsn0-eq w ws n (viewL w ws e)))
        (n∷ (nψ (NF₁-fsn nw (viewL w ws e) n) (Sb-fsn sw (viewL w ws e) n) n[] bnd[]) n[] tt)
NF₁-fsn (n∷ (nψ {u = x} {a = y ∷ ys} nx cx nb g) n[] _) e n with viewA x y ys e
... | v4 ke = subst NF₁ (sym (fs-rep x y ys ke n)) (NF₁-rep (nψ nx cx (NF₁-pred nb ke) (Bnd-pred g ke)) n)
... | v5 ke = subst NF₁ (sym (fs-ω x y ys ke n)) (n∷ (nψ nx cx (NF₁-fsn nb ke n) (λ v → GFS x [] n nb ke g v)) n[] tt)
... | v6 ν ke em = subst NF₁ (sym (fs-gt x y ys ν ke em n))
  (n∷ (nψ nx cx (NF₁-fsT nb ke (NF₁-γ nb ke (proj₁ (NF-ν₁ nb ke)) (proj₂ (NF-ν₁ nb ke))
                                       (λ v → g (Vis-mono (gt→≤ ν x em) v)) n) (γ<Ωs (y ∷ ys) ν n))
          (λ v → GΩ x [] nb ke (γ<Ωs (y ∷ ys) ν n) (inj₁ ns[]) g (Gγ x [] nb ke g (λ _ → inj₂ refl) n) v)) n[] tt)

desc-NF₁ : ∀ {t₀ t} → NF₁ t₀ → Desc t₀ t → NF₁ t
desc-NF₁ n₀ d₀         = n₀
desc-NF₁ n₀ (dω d e n) = NF₁-fsn (desc-NF₁ n₀ d) e n
desc-NF₁ n₀ (d₁ d e)   = NF₁-pred (desc-NF₁ n₀ d) e
```

**读法.** `NF₁-fsn` 在 $\gamma'_{k+1}=\psi_0(\Omega_\Omega+\Omega_{\gamma'_k})$ 上的一步: 末项 $\Omega_{\gamma'_k}$ 是极限叶, `GFS` 经 `GFSL` 进入 $\gamma'_k$ 的下标位置, 在那里 $\gamma'_k=\psi_0(\cdots)$ 的规则 5ω/6 由 `GFS5`/`GFS6` 在含 `sb` 的上下文里处理, 自界引理经过下标框架. 这正是 Standard 没有的路径.

## §6 对角线与检验

`Flat`: 一切参数 (含下标里的) 都是 $0$ 的项; 它的可见参数只有 $0$ (`flatVis`), 故非零的 flat 项满足任何门槛的 `Bnd₁` (`flatBnd`). $1$, $\Omega$, $\Omega_\Omega$, $\Omega_\Omega\cdot2$, $\Omega_{\Omega+1}$ 都是 flat 的.

```agda
data Flat : T → Set where
  f[] : Flat []
  f∷  : ∀ {u xs} → Flat u → Flat xs → Flat (ψᵗ u [] ∷ xs)

flatVis : ∀ {w ζ t} → Flat t → Vis₁ w ζ t → ζ ≡ []
flatVis (f∷ fu fx) (vh h)   = refl
flatVis (f∷ fu fx) (vd h ())
flatVis (f∷ fu fx) (vs h v) = flatVis fu v
flatVis (f∷ fu fx) (vt v)   = flatVis fx v

flatBnd : ∀ {w x xs} → Flat (x ∷ xs) → Bnd₁ w (x ∷ xs)
flatBnd f v with flatVis f v
... | refl = []<
```

```agda
f1 : Flat (natT 1)
f1 = f∷ f[] f[]

fΩ : Flat Ωᵗ
fΩ = f∷ f1 f[]

nf1 : NF₁ (natT 1)
nf1 = n∷ (nψ n[] (sC c[]) n[] bnd[]) n[] tt

nfΩ : NF₁ Ωᵗ
nfΩ = n∷ (nψ nf1 (sC (c∷ c[])) n[] bnd[]) n[] tt

nfβ : NFᴾ₁ (ψᵗ Ωᵗ [])
nfβ = nψ nfΩ (sΩ c[]) n[] bnd[]

nfβᴱ : NF₁ βᴱ
nfβᴱ = n∷ nfβ n[] tt

nfb₂ : NF₁ b₂
nfb₂ = n∷ nfβ nfβᴱ (inj₂ (cmpᴾ-refl (ψᵗ Ωᵗ [])))

fb₂ : Flat b₂
fb₂ = f∷ fΩ (f∷ fΩ f[])

t2-NF : NF₁ t2
t2-NF = n∷ (nψ n[] (sC c[]) nfb₂ (flatBnd fb₂)) n[] tt

diag₁-desc-NF : ∀ {t} → Desc t2 t → NF₁ t
diag₁-desc-NF = desc-NF₁ t2-NF

γ′-NF : ∀ k → NF₁ (γ′ᴱ k)
γ′-NF = NF₁-γ nfb₂ refl n[] (sC c[]) (flatBnd fb₂)

_ : ∀ k → γ′ᴱ (suc k) ≡ ψᵗ [] (ψᵗ Ωᵗ [] ∷ Ωt (γ′ᴱ k)) ∷ []
_ = λ k → refl

γ′-mono : ∀ k → γ′ᴱ k <ᵀ γ′ᴱ (suc k)
γ′-mono = γ-mono₁ nfb₂ refl
```

**检验 (i)** `t2-NF` 与 `diag₁-desc-NF` 成立: $\psi_0(\Omega_\Omega\cdot2)$ 的每个基本列后代都是 `NF₁`. 链 $\gamma'$ 的每一点由 `NF₁-γ` (参数 $b_2=\Omega_\Omega\cdot2$, $\nu=0$), 严格递增由 `γ-mono₁`. 下面用 `walk`/`walkD` 把一条具体路径变成 `Desc`. `tP` 是 Stage2 §9 的前缀暴露项 $\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$, 字面上是 $t_2$ 沿 $[1][0][1][0][0][2][1][0][1]$ 的后代, 故是标准形 (`tP-NF`); 它的第 1 项 $\psi_0(\Omega_\Omega+\psi_1(\Omega_{\eta_1}))$ 的下标 $\eta_1=\psi_0(\Omega_\Omega+\psi_1(\Omega_1))$ 来自层 $0$ 的上下文链 (EBO 穿透 $\psi_1$ 再由外层 $\psi_0$ 的链计值). 另有 $\Omega_\Omega$ 与 $\Omega_{\Omega+1}$ 处的 $\Omega$-基本列 (`fsT-ΩΩ-NF`, `fsT-ΩΩ+1-NF`).

```agda
walk : T → List ℕ → T
walk t []       = t
walk t (n ∷ ns) = walk (fsn t n) ns

AllLim : T → List ℕ → Set
AllLim t []       = ⊤
AllLim t (n ∷ ns) = (cof t ≡ cω) × AllLim (fsn t n) ns

walkD : ∀ {t₀ t} → Desc t₀ t → ∀ ns → AllLim t ns → Desc t₀ (walk t ns)
walkD d []       _        = d
walkD d (n ∷ ns) (e , es) = walkD (dω d e n) ns es

ctxᵗ : T → T
ctxᵗ y = ψᵗ [] (ψᵗ Ωᵗ [] ∷ y) ∷ []

tP : T
tP = ctxᵗ (ψᵗ (natT 1) βᴱ ∷ [])

path8 : List ℕ
path8 = 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 1 ∷ []

_ : walk t2 (1 ∷ path8) ≡ tP
_ = refl

tP-NF : NF₁ tP
tP-NF = diag₁-desc-NF (walkD d₀ (1 ∷ path8) (refl , refl , refl , refl , refl , refl , refl , refl , refl , tt))

_ : cof tP ≡ cω
_ = refl

_ : fsn tP 1 ≡ ctxᵗ (ψᵗ (natT 1) (Ωt (ctxᵗ (ψᵗ (natT 1) (Ωt (natT 1)) ∷ []))) ∷ [])
_ = refl

cofin-tP : ∀ {v} → NF₁ v → v <ᵀ tP → Σ ℕ λ n → v <ᵀ fsn tP n
cofin-tP = cofin₁ tP-NF refl

_ : proj₁ (cofin-tP (NF₁-fsn tP-NF refl 1) (fs<ᵀ {u = tP} refl 1)) ≡ 2
_ = refl

fsT-ΩΩ-NF : ∀ {η} → NF₁ η → η <ᵀ Ωᵗ → NF₁ (fsT βᴱ η)
fsT-ΩΩ-NF nη η< = NF₁-fsT nfβᴱ refl nη η<

ΩΩ+1 : T
ΩΩ+1 = Ωt (Ω₁ ∷ natT 1)

nfΩΩ+1 : NF₁ ΩΩ+1
nfΩΩ+1 = n∷ (nψ (n∷ (nψ nf1 (sC (c∷ c[])) n[] bnd[]) nf1 (inj₁ refl)) (sΩ (c∷ c[])) n[] bnd[]) n[] tt

_ : cof ΩΩ+1 ≡ cΩ Ωᵗ
_ = refl

fsT-ΩΩ+1-NF : ∀ {η} → NF₁ η → η <ᵀ Ωs Ωᵗ → NF₁ (fsT ΩΩ+1 η)
fsT-ΩΩ+1-NF nη η< = NF₁-fsT nfΩΩ+1 refl nη η<
```

**检验 (ii)** `cofin-t2` 与 `cofin-γ′2` 是 `cofin₁` 的实例 (前者把 $t_2[n]$ 经 Stage2 的 `diag2-fs` 写成 $\gamma'_{n+1}$); `cofin-tP` 是穿透前缀的情形, `cofin-tO` 是层 $\Omega$ 的规则 6. `refl` 算出的四个下标: $\psi_0(\Omega_\Omega+1)<\gamma'_1$ ($n=0$), $\gamma'_2<\gamma'_3$ ($n=2$), $\gamma'_2[0]<\gamma'_2[1]$ ($n=1$), $tP[1]<tP[2]$ ($n=2$). 这些计算走完整个 `cofin₁`/`Cof6` (含奇异叶与下标可见性), 耗时可忽略.

```agda
cofin-t2 : ∀ {v} → NF₁ v → v <ᵀ t2 → Σ ℕ λ n → v <ᵀ γ′ᴱ (suc n)
cofin-t2 {v} nv p with cofin₁ t2-NF refl nv p
... | n , q = n , subst (v <ᵀ_) (diag2-fs n) q

_ : cof (γ′ᴱ 2) ≡ cω
_ = refl

cofin-γ′2 : ∀ {v} → NF₁ v → v <ᵀ γ′ᴱ 2 → Σ ℕ λ n → v <ᵀ fsn (γ′ᴱ 2) n
cofin-γ′2 = cofin₁ (γ′-NF 2) refl

nfts : NF₁ ts
nfts = n∷ (nψ n[] (sC c[]) (n∷ nfβ nf1 (inj₁ refl)) (flatBnd (f∷ fΩ f1))) n[] tt

ts<t2 : ts <ᵀ t2
ts<t2 = hd< (ar< (tl< (hd< (lv< []<))))

_ : proj₁ (cofin-t2 nfts ts<t2) ≡ 0
_ = refl

_ : proj₁ (cofin-t2 (γ′-NF 2) (fs<ᵀ {u = t2} refl 1)) ≡ 2
_ = refl

_ : proj₁ (cofin-γ′2 (NF₁-fsn (γ′-NF 2) refl 0) (fs<ᵀ {u = γ′ᴱ 2} refl 0)) ≡ 1
_ = refl
```

```agda
tO-NF : NF₁ tO
tO-NF = n∷ (nψ n[] (sC c[]) (n∷ (nψ (n∷ (nψ nf1 (sC (c∷ c[])) n[] bnd[]) nf1 (inj₁ refl)) (sΩ (c∷ c[])) n[] bnd[]) n[] tt)
                 (flatBnd (f∷ (f∷ f1 f1) f[]))) n[] tt

cofin-tO : ∀ {v} → NF₁ v → v <ᵀ tO → Σ ℕ λ n → v <ᵀ fsn tO n
cofin-tO = cofin₁ tO-NF refl

tO-desc-NF : ∀ {t} → Desc tO t → NF₁ t
tO-desc-NF = desc-NF₁ tO-NF
```

## §7 反例: 下标可见性不可去

$v=\psi_0(\Omega_x)$, $x=\psi_0(\Omega_\Omega+1)$. 句法上 $v<\psi_0(\Omega_\Omega)$ (因 $x<\Omega$), 但 $v$ 不小于任何 $\psi_0(\Omega_\Omega)[n]=\gamma^\mathsf E_{n+1}=\psi_0(\Omega_{\gamma^\mathsf E_n})$: 那要求 $x<\gamma^\mathsf E_n$, 即 $\Omega_\Omega+1<\Omega_{\gamma^\mathsf E_{n-1}}$, 而 $\Omega>\gamma^\mathsf E_{n-1}$ (`vX≮`). $v$ 的唯一失败: $x$ 的参数 $\Omega_\Omega+1$ 经 `vs` 是 $0$-可见参数, 却大于 $\Omega_x$ (`vX-notNF₁`). 不进下标的可见性 (Standard 的 `Std.Vis`) 下 $\Omega_x$ 唯一的可见参数是 $0$, 有界条件成立 (`vX-oldBnd`), 下标 $x$ 本身是标准形且可数. 值的意义: 扩展 Buchholz 中 $x\notin C_0(\Omega_x)$, $\psi_0(\Omega_x)$ 不是标准记号.

```agda
import OCF.Align.Standard as Std

vX : T
vX = ψᵗ [] (Ωt ts) ∷ []

vX<BTBO : vX <ᵀ E.EBOψ 2
vX<BTBO = hd< (ar< (hd< (lv< (hd< (lv< []<)))))

Ω≮γ : ∀ k → Ωᵗ <ᵀ γᴱ k → ⊥
Ω≮γ zero    (hd< (lv< ()))
Ω≮γ (suc k) (hd< (lv< ()))

sb≮ : ∀ k → sucT βᴱ <ᵀ Ωt (γᴱ k) → ⊥
sb≮ zero    (hd< (lv< q)) = Ω≮γ zero q
sb≮ (suc k) (hd< (lv< q)) = Ω≮γ (suc k) q

ts≮γ : ∀ k → ts <ᵀ γᴱ k → ⊥
ts≮γ zero    (hd< (ar< ()))
ts≮γ (suc k) (hd< (ar< p)) = sb≮ k p

vX≮ : ∀ n → vX <ᵀ fsn (E.EBOψ 2) n → ⊥
vX≮ n p with inv1 (subst (vX <ᵀ_) (diag-fs n) p)
... | vlv ()
... | var q with inv0 q
...   | wlv r = ts≮γ n r

vX-notNF₁ : NF₁ vX → ⊥
vX-notNF₁ (n∷ (nψ _ _ _ g) _ _) with g (vs ([]≤ ts) (vh (inj₂ refl)))
... | hd< (lv< (hd< (lv< ())))

vX-oldBnd : ∀ {ζ} → Std.Vis [] ζ (Ωt ts) → ζ <ᵀ Ωt ts
vX-oldBnd (Std.vh h) = []<
vX-oldBnd (Std.vd h ())
vX-oldBnd (Std.vt ())
```

**读法.** 反例说明 Standard 的标准形定义 "下标只经 `lv<` 整体比较, 不与外层参数比较" 在 $\Omega$ 出现后不再够用: 一旦可数下标能含 $\Omega_\Omega$, 下标就可以从 "下面" 越过它所在的上下文. `vs` 把这类下标排除, 而对角线上的项 (§6) 都满足它, 因为 $\gamma'_k$ 里的 $\Omega_\Omega$ 总被外层参数的前缀 $\Omega_\Omega$ 界住.

## §8 对比表

| | Standard (`NF`) | 本文 (`NF₁`) |
|---|---|---|
| $\psi$-下标 | 可数 (`Ctbl`) | 可数或 $\Omega+$可数 (`Sb`) |
| 可见参数 | `vh`/`vd`/`vt` (不进下标) | 多 `vs`: 门槛 $\le x$ 时进下标 $x$ |
| 叶子的 $\Omega$-共尾度 | 只有正规叶 $\Omega_{\nu+1}$ | 正规叶 + 奇异叶 $\Omega_\Omega$ ($\nu=0$, $\Omega_\Omega[\eta]=\Omega_\eta$) |
| 共尾性 | `Ωcof` + `Cof6` | 同; `Ωcof` 多 `singΩ` ($\theta$ = 首项下标) |
| 上下文框架 | `pre`, `nd` | 多 `sb` ($H\mapsto\Omega_H$) |
| 核 | `pfxC`, `c4C` | 多 `hdC` (首项下标不变), `leafC` ($\Omega_{\nu+1}\to\psi_\nu(\cdots)$) |
| 自界引理 | `SELF`/`SELFΩ` | 多下标框架情形; `SELFΩ` 带 `NoSb S ⊎ HdIs ν η`; 新引理 `swapΩ`, `regSb` |
| 链点 | 下标 $\nu$ 的可见参数不出现 | 出现; `visLeaf` + `leafLift` |
| 反例 | $\psi_0(\psi_1(\Omega_2))$ (`Bnd` 不可去) | $\psi_0(\Omega_{\psi_0(\Omega_\Omega+1)})$ (`vs` 不可去) |
| 对角线 | `diag-desc-NF` ($\psi_0(\Omega_\Omega)$) | `diag₁-desc-NF` ($\psi_0(\Omega_\Omega\cdot2)$), `tO-desc-NF` ($\psi_0(\Omega_{\Omega+1})$) |

## §9 结论与边界

**字面成立 (`refl`):** `Ωᵗ`/`βᴱ` 的形状; `γ′ᴱ (k+1) ≡ ψ₀(Ω_Ω + Ω_{γ′ᴱ k})`; `cof (γ′ᴱ 2) ≡ cω`, `cof ΩΩ+1 ≡ cΩ Ωᵗ`, `cof tP ≡ cω`; `walk t2 (1 ∷ path8) ≡ tP` 与 `fsn tP 1` 的形状; 四个 `cofin` 下标; 奇异叶 $\Omega_\Omega[\eta]=\Omega_\eta$ (`sing` 匹配后定义性).

**定理 (句法的构造性证明, 对一切 EBO 项):**

1. 标准形 `NF₁` (§1): 扩展 Buchholz 的 $G_u(a)<a$ (含下标里的参数) 加下标属于 可数 $\cup$ ($\Omega+$可数).
2. **共尾性** `cofin₁` (§2); `Ωcof` (含奇异叶 `singΩ`), `Cof6`.
3. **闭包** `NF₁-pred`, `NF₁-fsn`, `NF₁-fsT`, `NF₁-γ`, `desc-NF₁` (§5); 工具 `SELF`/`SELFΩ`/`DESC`/`DESCΩ` (含下标框架), `swapΩ`, `regSb`, `hdC`, `leafC`, `visLeaf`, `leafLift`, `GFS`/`GFSL`/`GΩ`/`Gγ`.
4. **对角线** (§6): `t2-NF`, **`diag₁-desc-NF`**, `γ′-NF`, `γ′-mono`, `nfts`, `tO-NF`, `tO-desc-NF`, `tP-NF`, `fsT-ΩΩ-NF`, `fsT-ΩΩ+1-NF`; 共尾性 `cofin-t2`, **`cofin-γ′2`**, `cofin-tO`, `cofin-tP`.
5. **否定 (已编译)**: `vX≮`, `vX-notNF₁`, `vX-oldBnd`.

**边界.**

- 下标只到 $\Omega+$可数. $\psi_\Omega(\cdots)$ 节点在标准形里, 但 $\Omega\cdot2$, $\Omega_\Omega$ 之类的下标不在; $\psi_0(\Omega_{\Omega\cdot2})$, $\psi_0(\Omega_{\Omega_\Omega})$ 需要再推广 `Sb`, 那时奇异叶不止一种 (共尾度 $\Omega_{\mu+1}$ 的一般 $\Omega_u$), `singΩ`/`swapΩ` 要对一般的 $\mu$ 重做.
- `SELFΩ` 只在 `NoSb S ⊎ HdIs ν η` 下证明; 上下文穿过下标且 $\eta$ 任意的版本没有证, 也没有反例. 全部闭包定理不需要它.
- 与 Standard 一样, `NF₁` 不要求下标本身与外层参数的其余大小关系; `_<ᵀ_` 在 `NF₁` 上的良基性与值序一致性没有证. Standard 的 `NF` 是否包含于 `NF₁` (即无 $\Omega_\Omega$ 时 `vs` 是否自动成立) 没有证.
- 树侧的序对应不在本文; [SystemOmega](SystemOmega.lagda.md) 给出树侧派发所需的记号事实与逐步上界.
- 不改 `src/`、`archive/` 与已有文件 (README 未改).
