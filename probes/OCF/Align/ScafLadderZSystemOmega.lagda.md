> **机械克隆.** 由 `SystemOmega` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 带 $\Omega$ 下标的下标系统: 派发表与逐步给出的上界

> 接 [StandardOmega](StandardOmega.lagda.md) (标准形 `NF₁`, 共尾性 `cofin₁`, 闭包) 与 [Label](Label.lagda.md) (`System`, `Next`). 树侧的下一阶段 (另一路并行, 带符号构造子 $\Omega_\Omega$ 的新树族) 要在 $\psi_w$ 节点派发: 比较叶子的 $\nu+1$ 与 $w$, `lt`/`eq` 穿透, `gt` 折叠. 本文在记号侧回答两件事: 当一个或两个下标含 $\Omega$ 时派发需要哪些序事实 (§1–§2), 以及阶段上界如何沿上下文链逐步给出 (§3–§4).
>
> 结论先说:
>
> 1. **派发表 (§1).** 下标属于 `Sb` (可数, 或 $\Omega+c$ 且 $c$ 可数), 一对下标 $(v,w)$ 只有四种情形 (`dsp`): 两个可数 (交给上一阶段的 `Slt`/`Seq`); $v$ 可数而 $w=\Omega+c$: **恒为 `lt`** (`cmp-CΩ`, 对任意可数 $v$, 连标准形都不要); $v=\Omega+c$ 而 $w$ 可数: 恒为 `gt` (`cmp-ΩC`); 两个都是 $\Omega+\cdot$: `cmpᵀ (Ω+c) (Ω+c′) ≡ cmpᵀ c c′` (`refl`). 叶子给出的 $\nu+1$ 总在 `Sb` 里 (`leafSb`; 奇异叶 $\Omega_\Omega$ 给 $\nu+1=1$). 所以树侧在 $\Omega$-下标处**不需要判定**: 可数对 $\Omega+c$ 的答案是常数, 与 Stage2 的 `dec→WLPO` (D1 要对任意可数树判定 $a\prec\delta$) 不矛盾, 那里的判定是 "可数对可数", 这里仍由有公共上界的 `Slt`/`Seq` 承担.
> 2. **`System₁` (§2).** 记录: 上一阶段的 `System` (`base`) 加十二个字段: 可数性 `ctbl`, `one : Sub 1` (奇异叶), 三类派发 `C<Ω`/`Ω>C`/`ΩΩlt`/`ΩΩeq`/`ΩΩgt`, $\Omega+c$ 的形状跟随 $c$ (`sucΩ`, `cofΩ`, `preΩ`, `fsnΩ`), 奇异叶 `ΩΩlf` (`cof Ωᵗ ≡ cΩ []`, $\Omega_\Omega[\eta]=\Omega_\eta$). **全部字段由 `mk₁` 从任意 `base` 证出** (只要 `base` 的下标可数且含 $1$); Label 的每个阶段都是实例 (`St₁ k`).
> 3. **出现与支配 (§3).** `Occ x t`: $x$ 是 $t$ 中某节点的下标 (任意深度, 含下标里的下标). **`occ<`: 可数标准形 $t$ 里出现的每个可数下标 $x$ 都 $<t$.** 证明: 每个出现都 $0$-可见, $x=\psi_0(e)+\cdots$ 的 $e$ 经 `vs` 是 $t$ 的某个主项参数的可见参数, 由 `Bnd₁` 小于该参数. 推论 `dominate`: 可数标准形 $t_0$ 的一切基本列后代里出现的可数下标都 $<t_0$.
> 4. **逐步上界 (§4).** `Next₁`: 一列界 $\beta_k$ (可数标准形) 与**序见证** `β-up : β k <ᵀ β (k+1)` (Stage2 的 `ev`/`pre` 在记号侧的对应), 一列上下文 $\mathrm{ctx}_k\le\beta_k$; 第 $k$ 步的下标 `Sub₁ k w = NF₁ w × Ctbl w × w ≤ᵀ β k`, 由见证单调 (`up`), 对 `pred`/`fsn` 封闭, 有共尾性 (`Sub-cofin`, 即 `oc` 要的), 且**支配上下文** (`dom`: $\mathrm{ctx}_k$ 的一切后代里出现的可数下标都属于 `Sub₁ k`). 实例 `t2-chain`: $\beta_k=\gamma'_{k+1}$, $\mathrm{ctx}_k=t_2[k]$; 检验 (iii) `dom-t2 : Desc (γ′ᴱ (k+1)) t → Occ x t → Ctbl x → x <ᵀ γ′ᴱ (k+1)` 与 `γ′-mono`.
> 5. **界必须是当前链点 (§4, 已编译).** Label 的 `Next` 用上一点作界 ($\gamma^\mathsf E_{k+1}$ 的下标 $\le\gamma^\mathsf E_k$). 阶段 2 不行: $\gamma'_2$ 沿 9 步到达 $\psi_0(\Omega_\Omega+\psi_1(\Omega_{\eta_1}))$, 下标 $\eta_1=\psi_0(\Omega_\Omega+\psi_1(\Omega_1))$ 满足 $\gamma'_1<\eta_1$ (`prev-fails`), 而 $\eta_1<\gamma'_2$ (`cur-holds`). 新下标来自层 $0$ 的上下文链 (前缀 $\Omega_\Omega$ 在 $\psi_1$ 下暴露后由外层 $\psi_0$ 计值), 它只被链的当前点界住: 上界随链逐点产生.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块与 StandardOmega, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZSystemOmega where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import OCF.Align.Level using (Ordᴵ; _≺ᴵ_; _≅ᴵ_)
open import OCF.Align.Label using (System; module GS; St; prev)
open import OCF.Align.Closure using (lt→<; lt→<ᴾ; <→lt; eq→≡ᴾ; <ᵀ-trans)
open import OCF.Align.Bachmann using (fs<ᵀ; gt→<)
open import OCF.Align.Correspond using (γᴱ; βᴱ)
open import OCF.Align.Standard using (_≤ᵀ_; <≤-trans; []≤; Ctbl; c[]; c∷; Ctbl-pred; Ctbl-fsn; Ctbl-≤; Ctbl-cof;
  Desc; d₀; dω; d₁; diag-Ctbl)
import OCF.Align.Standard as Std
open import OCF.Align.Stage2 using (Ωᵗ; t2; γ′ᴱ; diag2-fs)
open import OCF.Align.ScafLadderZStandardOmega
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; pred; sucT; Ωt; natT; fsn; fsT;
              _<ᵀ_; []<; hd<; tl<; lv<; ar<)
       renaming (ψ to ψᵗ)
```

## §1 派发事实

$\Omega+c$ 是 `Ω₁ ∷ c`, $\Omega$ 本身是 $c=0$. 四条比较都是 `refl`: `cmpᵀ` 先比首项, 可数项的首项是 $\psi_0(\cdot)$, 而 $\psi_0(\cdot)<\psi_1(0)$ 只看下标 $0<1$; 两个 $\Omega+\cdot$ 首项相同, 比较落到尾巴. $\Omega+c$ ($c\ne0$) 的共尾度、前驱、基本列都只动尾巴, 也是 `refl`; 奇异叶 $\Omega_\Omega$ 的共尾度 $\Omega_1$ 与 $\Omega_\Omega[\eta]=\Omega_\eta$ 同样.

```agda
Ω+ : T → T
Ω+ c = Ω₁ ∷ c

_ : Ω+ [] ≡ Ωᵗ
_ = refl

cmp-CΩ : ∀ {v} → Ctbl v → ∀ c → cmpᵀ v (Ω+ c) ≡ lt
cmp-CΩ c[]      c = refl
cmp-CΩ (c∷ cv)  c = refl

cmp-ΩC : ∀ {v} → Ctbl v → ∀ c → cmpᵀ (Ω+ c) v ≡ gt
cmp-ΩC c[]      c = refl
cmp-ΩC (c∷ cv)  c = refl

cmp-ΩΩ : ∀ c c′ → cmpᵀ (Ω+ c) (Ω+ c′) ≡ cmpᵀ c c′
cmp-ΩΩ c c′ = refl

suc-Ω+ : ∀ c → sucT (Ω+ c) ≡ Ω+ (sucT c)
suc-Ω+ c = refl

cof-Ω+  : ∀ y ys → cof (Ω+ (y ∷ ys)) ≡ cof (y ∷ ys)
cof-Ω+ y ys = refl

pred-Ω+ : ∀ y ys → pred (Ω+ (y ∷ ys)) ≡ Ω+ (pred (y ∷ ys))
pred-Ω+ y ys = refl

fsn-Ω+  : ∀ y ys n → fsn (Ω+ (y ∷ ys)) n ≡ Ω+ (fsn (y ∷ ys) n)
fsn-Ω+ y ys n = refl

cof-Ω : cof Ωᵗ ≡ cΩ []
cof-Ω = refl

fsT-Ω : ∀ η → fsT Ωᵗ η ≡ η
fsT-Ω η = refl

fsT-ΩΩ : ∀ η → fsT βᴱ η ≡ Ωt η
fsT-ΩΩ η = refl
```

**读法.** 这些等式对**任意**项成立 (`cmp-CΩ`/`cmp-ΩC` 只用 $v$ 可数, 其余连这都不用), 不依赖标准形. `cmp-CΩ` 是本文的要点: 可数的叶子 $\nu+1$ 遇到 $\psi_{\Omega+c}$ 总是穿透.

`dsp` 把一对 `Sb` 下标分到四种派发情形; `leafSb`: 叶子给出的 $\nu+1$ 在 `Sb` 里 (正规叶是叶子下标本身, 奇异叶是 $1$). 于是 $\psi_w$ 节点处的派发 `cmpᵀ (sucT ν) w` 总落在 `dsp` 的某一格.

```agda
Ctbl-suc : ∀ {c} → Ctbl c → Ctbl (sucT c)
Ctbl-suc c[]     = c∷ c[]
Ctbl-suc (c∷ c)  = c∷ (Ctbl-suc c)

suc-Ωᵐ : ∀ n c → sucT (Ωᵐ n c) ≡ Ωᵐ n (sucT c)
suc-Ωᵐ zero c = refl
suc-Ωᵐ (suc n) c = cong (Ω₁ ∷_) (suc-Ωᵐ n c)

Sb-suc : ∀ {v} → Sb v → Sb (sucT v)
Sb-suc (sC c) = sC (Ctbl-suc c)
Sb-suc (sΩ c) = sΩ (Ctbl-suc c)
Sb-suc (sΩ² n c) = subst Sb (sym (suc-Ωᵐ (suc (suc n)) _)) (sΩ² n (Ctbl-suc c))

data Dsp (v w : T) : Set where
  dCC : Ctbl v → Ctbl w → Dsp v w
  dCΩ : cmpᵀ v w ≡ lt → Dsp v w
  dΩC : cmpᵀ v w ≡ gt → Dsp v w
  dΩΩ : ∀ {c c′} → v ≡ Ω+ c → w ≡ Ω+ c′ → Ctbl c → Ctbl c′ → cmpᵀ v w ≡ cmpᵀ c c′ → Dsp v w

leafSb : ∀ {u ν} → Sb u → Leaf₁ u ν → Sb (sucT ν)
leafSb su (reg ue) = subst Sb (sym (E.pred-suc _ ue)) su
leafSb su sing     = sC (c∷ c[])
leafSb su (sing² n) = sC (c∷ c[])
```

## §2 `System₁`

字段就是树侧在含 $\Omega$ 的派发处需要从记号拿到的全部序事实. `base` 是上一阶段的可数下标系统 (Label 的 `System`: 层号、公共上界、形状、`Slt`/`Seq`). 新字段:

- `ctbl`, `one`: `base` 的下标可数, 且 $1$ 是下标 (奇异叶的 $\nu+1$).
- `C<Ω`, `Ω>C`: 可数对 $\Omega+c$ 恒 `lt`, 反之恒 `gt`; 树侧不比较层号.
- `ΩΩlt`/`ΩΩeq`/`ΩΩgt`: 两个 $\Omega+\cdot$ 的比较结果给出尾巴层号的 $\prec^\mathsf I$/$\cong^\mathsf I$ (树侧若以 "符号 $\hat\Omega$ + 层号 `lvS c`" 表示 $\Omega+c$, 这就是它要的序对应).
- `sucΩ`, `cofΩ`, `preΩ`, `fsnΩ`: $\Omega+c$ 的后继、共尾度、前驱、基本列跟随 $c$ (树侧的 `S1`/`Sω` 对 $\Omega+c$ 从 $c$ 的读出).
- `ΩΩlf`: 奇异叶 $\Omega_\Omega$ 共尾度 $\Omega_1$, $\Omega_\Omega[\eta]=\Omega_\eta$ (树侧的符号构造子按上下文链计值的记号侧规定).

`mk₁` 从任意 `base` 证出全部字段: 前两类由 §1 的 `refl`, `ΩΩ*` 由 `base` 的 `Slt`/`Seq` (因 `cmp-ΩΩ` 是 `refl`, `gt` 情形经 Bachmann 的 `gt→<` 翻成反向的 `lt`).

```agda
record System₁ : Set₁ where
  field
    base : System
  open System base using (Sub; lvS)
  field
    ctbl : ∀ {w} → Sub w → Ctbl w
    one  : Sub (natT 1)
    C<Ω  : ∀ {v} → Sub v → ∀ {c} → Sub c → cmpᵀ v (Ω+ c) ≡ lt
    Ω>C  : ∀ {v} → Sub v → ∀ {c} → Sub c → cmpᵀ (Ω+ c) v ≡ gt
    ΩΩlt : ∀ {c c′} (sc : Sub c) (sc′ : Sub c′) → cmpᵀ (Ω+ c) (Ω+ c′) ≡ lt → lvS sc ≺ᴵ lvS sc′
    ΩΩeq : ∀ {c c′} (sc : Sub c) (sc′ : Sub c′) → cmpᵀ (Ω+ c) (Ω+ c′) ≡ eq → lvS sc ≅ᴵ lvS sc′
    ΩΩgt : ∀ {c c′} (sc : Sub c) (sc′ : Sub c′) → cmpᵀ (Ω+ c) (Ω+ c′) ≡ gt → lvS sc′ ≺ᴵ lvS sc
    sucΩ : ∀ {c} → Sub c → sucT (Ω+ c) ≡ Ω+ (sucT c)
    cofΩ : ∀ {c y ys} → Sub c → c ≡ y ∷ ys → cof (Ω+ c) ≡ cof c
    preΩ : ∀ {c y ys} → Sub c → c ≡ y ∷ ys → pred (Ω+ c) ≡ Ω+ (pred c)
    fsnΩ : ∀ {c y ys} → Sub c → c ≡ y ∷ ys → ∀ n → fsn (Ω+ c) n ≡ Ω+ (fsn c n)
    ΩΩlf : (cof Ωᵗ ≡ cΩ []) × (∀ η → fsT βᴱ η ≡ Ωt η)

mk₁ : (S : System) → (∀ {w} → System.Sub S w → Ctbl w) → System.Sub S (natT 1) → System₁
mk₁ S ct o = record
  { base = S ; ctbl = ct ; one = o
  ; C<Ω  = λ sv {c} _ → cmp-CΩ (ct sv) c
  ; Ω>C  = λ sv {c} _ → cmp-ΩC (ct sv) c
  ; ΩΩlt = λ sc sc′ e → System.Slt S sc sc′ e
  ; ΩΩeq = λ sc sc′ e → System.Seq S sc sc′ e
  ; ΩΩgt = λ {c} {c′} sc sc′ e → System.Slt S sc′ sc (<→lt (gt→< c c′ e))
  ; sucΩ = λ _ → refl
  ; cofΩ = λ { _ refl → refl }
  ; preΩ = λ { _ refl → refl }
  ; fsnΩ = λ { _ refl n → refl }
  ; ΩΩlf = refl , λ η → refl
  }
```

**实例.** Label 的阶段 `St k` (下标 $\le\gamma^\mathsf E_k$ 的 Standard 标准形) 都满足 `mk₁` 的两个前提: 可数性由 Standard 的 `Ctbl-≤`, $1$ 的推导是 `a∷ (aψ s0 a[]) a[]`, $1\le\gamma^\mathsf E_k$. 这些阶段里没有 $\Omega$-下标, `C<Ω` 等字段对它们是空洞地成立的; 实例只说明记录可以居留, 且 `mk₁` 对 Label 的整个对角线一致.

```agda
ctblSt : ∀ k {w} → System.Sub (St k) w → Ctbl w
ctblSt k (_ , n , le) = Ctbl-≤ n (diag-Ctbl k) le

nf1ˢ : Std.NF (natT 1)
nf1ˢ = Std.n∷ (Std.nψ Std.n[] c[] Std.n[] Std.bnd[]) Std.n[] tt

one≤ : ∀ k → natT 1 ≤ᵀ γᴱ k
one≤ zero    = inj₂ refl
one≤ (suc k) = inj₁ (hd< (ar< []<))

oneSt : ∀ k → System.Sub (St k) (natT 1)
oneSt k = GS.a∷ {S = prev k} (GS.aψ {S = prev k} (System.s0 (prev k)) (GS.a[] {S = prev k})) (GS.a[] {S = prev k})
        , nf1ˢ , one≤ k

St₁ : ℕ → System₁
St₁ k = mk₁ (St k) (ctblSt k) (oneSt k)
```

## §3 出现与支配

`Occ x t`: $x$ 是 $t$ 中某个节点的下标 (经参数 `od`、下标 `os`、后续加项 `ot` 到达). 门槛为 $0$ 时每个节点都可见, 所以出现的下标的首项参数是 $0$-可见参数 (`occVis`); 标准形的下标都是标准形 (`Occ-NF`).

```agda
data TailOf (x : T) : T → Set where
  th : ∀ {y} → TailOf x (y ∷ x)
  ts : ∀ {y u} → TailOf x u → TailOf x (y ∷ u)

data Occ (x : T) : T → Set where
  oh : ∀ {a xs}   → Occ x (ψᵗ x a ∷ xs)
  od : ∀ {y a xs} → Occ x a → Occ x (ψᵗ y a ∷ xs)
  os : ∀ {y a xs} → Occ x y → Occ x (ψᵗ y a ∷ xs)
  oτ : ∀ {u a xs} → TailOf x u → Occ x (ψᵗ u a ∷ xs)
  ot : ∀ {y xs}   → Occ x xs → Occ x (y ∷ xs)

tailVis : ∀ {y e xs u} → TailOf (ψᵗ y e ∷ xs) u → Vis₁ [] e u
tailVis th = vt (vh ([]≤ _))
tailVis (ts t) = vt (tailVis t)

occ-tailNF : ∀ {x u} → TailOf x u → NF₁ u → NF₁ x
occ-tailNF th (n∷ _ r _) = r
occ-tailNF (ts t) (n∷ _ r _) = occ-tailNF t r

occVis : ∀ {y e xs t} → Occ (ψᵗ y e ∷ xs) t → Vis₁ [] e t
occVis oh     = vs ([]≤ _) (vh ([]≤ _))
occVis (od o) = vd ([]≤ _) (occVis o)
occVis (os o) = vs ([]≤ _) (occVis o)
occVis (oτ t) = vs ([]≤ _) (tailVis t)
occVis (ot o) = vt (occVis o)

Occ-NF : ∀ {x t} → NF₁ t → Occ x t → NF₁ x
Occ-NF (n∷ (nψ nx _ _ _) _ _) oh     = nx
Occ-NF (n∷ (nψ _ _ na _) _ _) (od o) = Occ-NF na o
Occ-NF (n∷ (nψ nx _ _ _) _ _) (os o) = Occ-NF nx o
Occ-NF (n∷ (nψ nx _ _ _) _ _) (oτ t) = occ-tailNF t nx
Occ-NF (n∷ _ nxs _)           (ot o) = Occ-NF nxs o
```

`occ<`: 可数标准形 $t=\psi_0(a)+\cdots$ 里出现的可数下标 $x<t$. 顶层节点的下标是 $0$; 出现在参数 $a$ 里的 $x=\psi_0(e)+\cdots$ 有 $e<a$ (`occVis` 与 `Bnd₁ 0 a`), 故 $x<\psi_0(a)$; 后续加项里的由递归与 `tl<₁` (标准形的尾巴小于整个和).

```agda
tl<₁ : ∀ {x ts} → NF₁ (x ∷ ts) → ts <ᵀ x ∷ ts
tl<₁ (n∷ _ n[] _) = []<
tl<₁ {x} (n∷ _ (n∷ {x = y} ny nys hy) (inj₁ e)) = hd< (lt→<ᴾ y x e)
tl<₁ {x} (n∷ _ (n∷ {x = y} ny nys hy) (inj₂ e)) with eq→≡ᴾ y x e
... | refl = tl< (tl<₁ (n∷ ny nys hy))

occ< : ∀ {x t} → NF₁ t → Ctbl t → Occ x t → Ctbl x → x <ᵀ t
occ< nt (c∷ ct) oh cx = []<
occ< (n∷ (nψ _ _ na g) _ _) (c∷ ct) (od o) c[]      = []<
occ< (n∷ (nψ _ _ na g) _ _) (c∷ ct) (od o) (c∷ cx)  = hd< (ar< (g (occVis o)))
occ< nt (c∷ ct) (os ()) cx
occ< nt (c∷ ct) (oτ ()) cx
occ< (n∷ nx nts h) (c∷ ct) (ot o) cx = <ᵀ-trans (occ< nts ct o cx) (tl<₁ (n∷ nx nts h))
```

`dominate`: 后代都 $\le t_0$ (`desc≤`, 由 EBO 的递减证书), 且仍是可数标准形 (`desc-NF₁`, `desc-Ctbl`), 于是由 `occ<` 得 $x<t\le t_0$.

```agda
desc≤ : ∀ {t₀ t} → Desc t₀ t → t ≤ᵀ t₀
desc≤ d₀         = inj₂ refl
desc≤ (dω d e n) = inj₁ (<≤-trans (fs<ᵀ e n) (desc≤ d))
desc≤ (d₁ d e)   = inj₁ (<≤-trans (E.pred-< _ e) (desc≤ d))

desc-Ctbl : ∀ {t₀ t} → Ctbl t₀ → Desc t₀ t → Ctbl t
desc-Ctbl c d₀         = c
desc-Ctbl c (dω d e n) = Ctbl-fsn (desc-Ctbl c d) e n
desc-Ctbl c (d₁ d e)   = Ctbl-pred (desc-Ctbl c d)

dominate : ∀ {t₀} → NF₁ t₀ → Ctbl t₀ → ∀ {t} → Desc t₀ t → ∀ {x} → Occ x t → Ctbl x → x <ᵀ t₀
dominate n₀ c₀ d o cx = <≤-trans (occ< (desc-NF₁ n₀ d) (desc-Ctbl c₀ d) o cx) (desc≤ d)
```

**读法.** `occ<` 是 "每个项界住自己的下标": 不需要预先给定的上界, 被比较的可数下标都在当前项之下. 这是 Stage2 §10 第 2 条 "链从第 1 点起支配上下文里的一切可数下标" 在记号侧的精确形式.

## §4 `Next₁`: 逐步给出的上界

Label 的 `Next S β` 一次给定上界 $\beta$, 阶段的公共上界是 `suc (lvS′ β)`. `Next₁` 把上界换成一列 $\beta_k$, 带序见证 `β-up` (每一步严格上升), 以及第 $k$ 步要计值的上下文 $\mathrm{ctx}_k\le\beta_k$. 派生出的是 Label 的 `Next` 在记号侧用到的全部事实, 逐步版本:

- `Sub₁ k w`: 第 $k$ 步的下标 (可数标准形, $\le\beta_k$); `sβ`: $\beta_k$ 本身.
- `up`: 第 $k$ 步的下标也是第 $k+1$ 步的 (由 `β-up`). 树侧的层号 $M_k$ 以 $\mathtt{lvl}\,\beta_k$ 为界时, 它的步进证据从这里来, 对应 Stage2 的 `ev : lim γ ⊑ χₖ`.
- `dom`: $\mathrm{ctx}_k$ 的一切基本列后代里出现的可数下标都是第 $k$ 步的下标 (§3 的 `dominate`).
- `Sub-pred`, `Sub-fsn`, `Sub-cofin`, `Sub-Ω`: Label 的 `oc` (序对应的树递归) 消费的全部记号事实: 闭包 (`NF₁-pred`/`NF₁-fsn` 与 `pred-<`/`fs<ᵀ` 保持 $\le\beta_k$), 共尾性 (`cofin₁`), 可数性排除 $\Omega$-共尾度.

```agda
record Next₁ : Set₁ where
  field
    β      : ℕ → T
    β-NF   : ∀ k → NF₁ (β k)
    β-ct   : ∀ k → Ctbl (β k)
    β-up   : ∀ k → β k <ᵀ β (suc k)
    ctx    : ℕ → T
    ctx-NF : ∀ k → NF₁ (ctx k)
    ctx-ct : ∀ k → Ctbl (ctx k)
    ctx≤   : ∀ k → ctx k ≤ᵀ β k

  Sub₁ : ℕ → T → Set
  Sub₁ k w = NF₁ w × Ctbl w × (w ≤ᵀ β k)

  sβ : ∀ k → Sub₁ k (β k)
  sβ k = β-NF k , β-ct k , inj₂ refl

  up : ∀ {k w} → Sub₁ k w → Sub₁ (suc k) w
  up {k} (n , c , le) = n , c , inj₁ (≤<-trans le (β-up k))

  dom : ∀ k {t} → Desc (ctx k) t → ∀ {x} → Occ x t → Ctbl x → Sub₁ k x
  dom k d o cx = Occ-NF (desc-NF₁ (ctx-NF k) d) o , cx ,
                 inj₁ (<≤-trans (dominate (ctx-NF k) (ctx-ct k) d o cx) (ctx≤ k))

  Sub-pred : ∀ {k w} → Sub₁ k w → cof w ≡ c1 → Sub₁ k (pred w)
  Sub-pred (n , c , le) e = NF₁-pred n e , Ctbl-pred c , inj₁ (<≤-trans (E.pred-< _ e) le)

  Sub-fsn : ∀ {k w} → Sub₁ k w → cof w ≡ cω → ∀ n → Sub₁ k (fsn w n)
  Sub-fsn (nw , c , le) e n = NF₁-fsn nw e n , Ctbl-fsn c e n , inj₁ (<≤-trans (fs<ᵀ e n) le)

  Sub-cofin : ∀ {k u v} → Sub₁ k u → cof u ≡ cω → Sub₁ k v → v <ᵀ u → Σ ℕ λ n → v <ᵀ fsn u n
  Sub-cofin (nu , _ , _) e (nv , _ , _) p = cofin₁ nu e nv p

  Sub-Ω : ∀ {k w μ} → Sub₁ k w → cof w ≡ cΩ μ → ⊥
  Sub-Ω (_ , c , _) e = Ctbl-cof c e
```

**实例 `t2-chain`.** $\beta_k=\gamma'_{k+1}$, $\mathrm{ctx}_k=t_2[k]$ ($=\gamma'_{k+1}$, Stage2 的 `diag2-fs`), 见证是 `γ′-mono`. **检验 (iii)** `dom-t2`: $\gamma'_{k+1}$ 的一切后代里出现的可数下标都 $<\gamma'_{k+1}$.

```agda
t2-chain : Next₁
t2-chain = record
  { β = λ k → γ′ᴱ (suc k) ; β-NF = λ k → γ′-NF (suc k) ; β-ct = λ k → c∷ c[] ; β-up = λ k → γ′-mono (suc k)
  ; ctx = fsn t2 ; ctx-NF = NF₁-fsn t2-NF refl ; ctx-ct = λ k → Ctbl-fsn (c∷ c[]) refl k
  ; ctx≤ = λ k → inj₂ (diag2-fs k) }

dom-t2 : ∀ k {t} → Desc (γ′ᴱ (suc k)) t → ∀ {x} → Occ x t → Ctbl x → x <ᵀ γ′ᴱ (suc k)
dom-t2 k = dominate (γ′-NF (suc k)) (c∷ c[])
```

**界必须是当前链点.** 下面沿 $\gamma'_2$ 的 9 步路径 (两侧 `refl`): $[0]$ 到 $\psi_0(\Omega_\Omega+\Omega_{\psi_0(\Omega_\Omega+1)})$, $[1][0][0][2]$ 把下标降到 $2$, $[1]$ 是层 $1$ 的链 $\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega+\Omega_1))$, $[0][1]$ 到 $\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$ (Stage2 §9 的前缀暴露), 最后 $[1]$ 是层 $0$ 的上下文链, 新下标 $\eta_1=\psi_0(\Omega_\Omega+\psi_1(\Omega_1))$. 它大于上一个链点 $\gamma'_1=\psi_0(\Omega_\Omega+\Omega_1)$ (`prev-fails`, 因 $\psi_1(\Omega_1)>\psi_1(0)$), 小于当前链点 $\gamma'_2$ (`cur-holds`, 由 `dom-t2`).

```agda
η₁ : T
η₁ = ctxᵗ (ψᵗ (natT 1) (Ωt (natT 1)) ∷ [])

path : List ℕ
path = 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ []

_ : walk (γ′ᴱ 2) path ≡ ctxᵗ (ψᵗ (natT 1) (Ωt η₁) ∷ [])
_ = refl

pathD : Desc (γ′ᴱ 2) (walk (γ′ᴱ 2) path)
pathD = walkD d₀ path (refl , refl , refl , refl , refl , refl , refl , refl , refl , tt)

occη₁ : Occ η₁ (walk (γ′ᴱ 2) path)
occη₁ = od (ot (od oh))

prev-fails : γ′ᴱ 1 <ᵀ η₁
prev-fails = lt→< (γ′ᴱ 1) η₁ refl

cur-holds : η₁ <ᵀ γ′ᴱ 2
cur-holds = dom-t2 1 pathD occη₁ (c∷ c[])
```

**读法.** 与 Label 对比: 那里 $\gamma^\mathsf E_{k+1}=\psi_0(\Omega_{\gamma^\mathsf E_k})$ 的后代里只出现 $\le\gamma^\mathsf E_k$ 的下标 (新下标只来自已有下标的基本列), 所以上界可以是上一点并一次给定. 阶段 2 的后代里, 被外层 $\psi_0$ 折叠的 $\Omega_\Omega$ 会把上下文链的点变成新下标, 它们越过上一点, 只被当前点界住. 所以树侧的层号必须**每一步现造**: 第 $k$ 步以 $\mathtt{lvl}\,\gamma'_{k+1}$ (即 $\chi_{k+1}$ 本身) 为界, 步进由 `β-up`.

## §5 对比表

| | Label `Next` | 本文 `Next₁` |
|---|---|---|
| 下标 | Standard `NF`, 可数, $\le\beta$ | `NF₁`, 可数, $\le\beta_k$ (可含 $\Omega_\Omega$) |
| 上界 | 一次给定: $\beta=\gamma^\mathsf E_k$ (上一点) | 逐步: $\beta_k=\gamma'_{k+1}$ (当前点), 见证 `β-up` |
| 支配 | 隐含 (新下标都来自已有下标) | `dom`/`dominate`/`occ<`, 且上一点不够 (`prev-fails`) |
| 共尾性 | `cofin` | `cofin₁` (`Sub-cofin`) |
| $\Omega$-下标派发 | 无 | `System₁`: 可数 vs $\Omega+c$ 恒 `lt`, $\Omega+c$ 对 $\Omega+c'$ 归于 $c$ 对 $c'$ |
| 树侧 | `oc`, `Slt′`/`Seq′`, `A′` 已证 | 未做 (另一路), 记号侧接口齐备 |

## §6 结论与边界

**字面成立 (`refl`):** `cmp-CΩ`/`cmp-ΩC` 的每一行, `cmp-ΩΩ`, `suc-Ω+`, `cof-Ω+`, `pred-Ω+`, `fsn-Ω+`, `cof-Ω`, `fsT-Ω`, `fsT-ΩΩ`; 9 步路径的终点 `walk (γ′ᴱ 2) path`; `prev-fails` 的比较.

**定理:**

1. 派发表 `dsp : Sb v → Sb w → Dsp v w`, `leafSb`.
2. `System₁` 与 `mk₁` (全部字段从 `base` 证出), 实例 `St₁ : ℕ → System₁`.
3. `occVis`, `Occ-NF`, `tl<₁`, **`occ<`**, `desc≤`, `desc-Ctbl`, **`dominate`**.
4. `Next₁` 及其派生 (`up`, `dom`, `Sub-pred`, `Sub-fsn`, `Sub-cofin`, `Sub-Ω`), 实例 `t2-chain`, **`dom-t2`**; 否定的见证 `prev-fails` 与 `cur-holds`.

**树侧要自己提供的 (不在本文):** 第 $k$ 步下标的层号 `lvS` (这些可数下标里含 $\Omega_\Omega$, 例如 $\gamma'_1$, 要用新树族翻译并带 `Good`/`HS` 证书), 它们之间的序对应 `Slt`/`Seq` (按 Label 的 `oc` 递归, 消费 `Sub-cofin`/`Sub-pred`/`Sub-fsn` 与 Bachmann 的 `<sucT`), 以 `β-up` 为步进的层号 $M_k$ (上界 $\mathtt{lvl}\,\gamma'_{k+1}$), $\Omega+c$ 下标的表示 (满足 `System₁` 的形状字段), 以及符号构造子 $\Omega_\Omega$ 在穿透 ($\psi_{\delta\ge1}$, `C<Ω` 与 `one`) 与折叠 (外层 $\psi_0$ 的上下文链) 处的计值与 Good 封闭.

**边界.**

- `System₁` 只覆盖 $\Omega+$可数的下标; 不可数下标的更高层 ($\Omega\cdot2$, $\Omega_\Omega$) 需要 StandardOmega 先推广.
- `occ<` 只对**可数**标准形陈述 (顶层主项是 $\psi_0$); $\psi_0(\Omega_{\Omega+1})$ 的后代里的 $\psi_\Omega(\cdots)$ 节点所需的 "$\Omega$-下标层" 的支配 (下标 $\le\Omega+c$) 由 `Sb` 本身给出, 未单独陈述.
- `Next₁` 的实例只做了 $t_2$ 的链; $\psi_0(\Omega_{\Omega+1})$ 的链在层 $\Omega$ 上 ($\Omega_\Omega,\psi_\Omega(\Omega_\Omega),\ldots$, 不可数), 不是可数界的序列, 树侧需要以不可数目标层折叠, 本文只提供 StandardOmega 的 `cofin-tO`/`tO-desc-NF`.
- 不改 `src/`、`archive/` 与已有文件 (README 未改).
