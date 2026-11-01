# Bachmann 性质与 $\gamma_2=\psi_0(\Omega_{\varepsilon_0})$ 的遗传标签

> 接 [Closure](Closure.lagda.md) §9–§11 与 [Correspond](Correspond.lagda.md) §8. Closure 按 "基本列闭包" 归纳, 证据 ($\trianglelefteq^\mathsf I$ 与不变量 `Inv`) 随推导历史传递, 在 $\gamma^\mathsf E_2$ 的第 20 步撞墙: 项 $P[n]$ 的 $\psi_5$ 节点要比较 $n-1$ 与 $5$, 二者是 $\omega$ 的不同分支后代, 历史证据推不出它们的关系. Closure §11 说缺的是 $\varepsilon_0$ 片段 $\mathbb E$ 上的 Bachmann 性质. 本文把它补上, 并换一种组织方式: 不再让证据跟着推导走, 而是证明**序的对应** (下标的句法比较决定层号的比较), 于是任何两个下标在任何位置都能现场比较, 不变量整个取消.
>
> 结论先说:
>
> 1. **要标准形 (§2).** $\mathbb E$ 不强制 Cantor 标准形: $1+\omega\in\mathbb E$, `cmpᵀ (1+ω) ω ≡ lt`, 但两棵树既不 $\prec$ 也不 $\cong$ (`nf-fail₁`/`nf-fail₂`/`nf-fail₃`, §4 末). 定义 `N0` (指数非增的 Cantor 标准形, 只约束相邻两项, `Hd≤`) 与 `NF` (`N0`, 或恰为 $\varepsilon_0=\psi_0(\Omega_1)$). `pred`/`fsn` 保持它 (`NF-pred`, `NF-fsn`); 对角线的下标 $\gamma^\mathsf E_0=1$, $\gamma^\mathsf E_1=\varepsilon_0$ 在 `NF` 里, $\gamma^\mathsf E_2$ 不在 (`diag-NF₀`, `diag-NF₁`, `γᴱ₂∉NF`).
> 2. **序的对应 (§3–§4).** `OC< : v <ᵀ u → T⟦ sv ⟧ ≺ T⟦ su ⟧` (对 `NF` 的 $u,v$; 右边是 Level 的结构序 $\prec$, 第 0 层), 推论 `OC-lt`/`OC-eq`/`OC-gt`: `cmpᵀ v u` 为 `lt`/`eq`/`gt` 时 `lvN sv ≺ᴵ lvN su` / `lvN sv ≅ᴵ lvN su` / `lvN su ≺ᴵ lvN sv`. 证明对**树**递归 (Correspond `lab` 的手法), 只用两条句法事实: 离散性 (`<sucT`, $a<\nu+1\Rightarrow a<\nu\lor a=\nu$, 对一切项) 与**共尾性** (`cofin`: 标准形 $v<u$, $u$ 极限 $\Rightarrow\exists n.\ v<u[n]$). Bachmann 性质不是输入而是推论.
> 3. **Bachmann 性质 (§3, §4).** 句法 `bach-syn : m <ᴺ m′ → fsn u m <ᵀ fsn u m′`, 树 `bach : m <ᴺ m′ → T⟦ NF-fsn su m ⟧ ≺ T⟦ NF-fsn su m′ ⟧`, 以及 `fs≺`/`pred≺` (基本列各项与前驱在树上严格在下). 句法递降 (`fs<ᵀ`, EBO 的 `pred-<`) 对一切项成立.
> 4. **证据替换不变量 (§5).** 通用模块 `Generic` 以下标系统为参数, 接口七条: 层号与公共上界 `A`、零/后继/极限下标的层号形状、可数性、序的对应 `Slt`/`Seq`. 在其上, 一切 $\psi$-下标属于该系统的 EBO 项 (类 `𝔸`; 和与参数**不要求**标准形) 有翻译 `⟦_⟧ᵃ` (全部参数放在公共上界层 `A`, 主项经 `lift` 嵌入) 与无前提的形状定理 `corr : ∀ (d : 𝔸 t) → Sh ⟦ d ⟧ᵃ (cof t) t` (四行, 含 $\Omega_{\nu+1}$ 行). 任意 $\psi_w$ 节点的派发由 `dispatch` 现场决定: `cmpᵀ (ν+1) w` 为 `lt`/`eq` 时穿透 (Closure 的 `pen⁺`, 字面), 为 `gt` 时折叠 (`fold⁺`, 字面), 折叠的 $\gamma$-链逐项 $\cong$ 记号的 `γT` (`chainM`). 规则 4 产生的和由 `sum` 处理, 不要单独的闭包子句. Closure 的 `Cx`/`Inv`/$\trianglelefteq^\mathsf I$ 全部不需要.
> 5. **检验二通过 (§6–§7).** 以 `NF` 实例化 (环境层 $A_0=\mathtt{lvl}(\varepsilon_0)+1$), **`γ₂-label : Lab (N.γ 2) (γᴱ 2)` 是定理**: NoCumsum 的树 $\gamma_2$ 带 EBO 项 $\psi_0(\Omega_{\varepsilon_0})$ 的遗传标签. $\gamma^\mathsf E_2$ 的整个基本列闭包 (`Reach`: 极限处取 `fsn`, 后继处取 `pred`) 落在 `𝔸` 里 (`reach-𝔸`) 且每项都有标签 (`reach-lab`); Closure 的墙项 $P$ 在闭包里 (`wall-reach`, 19 步的共尾度全部 `refl`), `wall-label : ∀ n → Σ X. Lab X (P[n])`; $\psi_5$ 处 $(n-1,5)$ 的比较由 `OC-lt`/`OC-eq` 现场给出 (`wall-ev5`, `wall-ev7`).
> 6. **BTBO 仍是估计 (§9).** 由 Correspond 的 `diag-label`, BTBO $=\psi_0(\Omega_\Omega)$ 归约为一切 $k$ 的 $\gamma_{k+1}$ 的遗传标签. 现在 $k=0,1$ 是定理 (`ε₀-label`, `γ₂-label`); $k\ge2$ 的下标 $\gamma^\mathsf E_k$ 已不是 $\mathbb E$ 的项, 要 EBO 下标上的标准形与共尾性. §9 逐条列出 `Generic` 的接口里哪些已对一般项成立.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件 (没有需要复制的私有定义).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Bachmann where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; module Trich; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.Level
open import OCF.Align.Uniform using (≅-reflˡ; ≅-reflʳ; s-inv; l-inv; i-resp)
open import OCF.Align.Correspond using (𝔾; g[]; g∷; gψ; gΩ; ⟦_⟧; lvl; cert; 𝔼; 𝔼ᴾ; e[]; e∷; eψ; eΩ₁; emb; embᴾ;
  corrE; ShE; MatchE; cof-ne; ch; fs-rep; fs-ω; fs-Ω1; fsT-c1; fsn↓c-gt; γᴱ; gγ; diag-≅;
  Lab; l0; l1; lω; FGH-Lab1; FGH-Labω; ωᵗ; z≇s; l≇s; z≇l; s≇l)
open import OCF.Align.Closure using (Pen; cmpᵀ-refl; cmpᴾ-refl; <→lt; <ᴾ→lt; lt→<; lt→<ᴾ; eq→≡; eq→≡ᴾ;
  <ᵀ-trans; <ᴾ-trans; <◃; pen⁺; fsT₊-pen′; ΩshE1; ΩshEω; Pw; walk; base; wall-path)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; cofP; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; natT; fsn; fsT; fsT0; γT; trm; dec; εₒ;
              _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
       renaming (ψ to ψᵗ)
```

## §1 记号侧: 任意项上的序引理

Closure §1 证了 `cmpᵀ` 与句法序 $<^\mathsf T$ 在 `lt`/`eq` 上的两向对应与传递. 这里补上 `gt` 一向 (`gt→<`)、无自反 (由 `cmpᵀ-refl` 一行得到) 与非对称, 以及派发要用的**离散性** `<sucT`: $a<^\mathsf T\nu+1\Rightarrow a<^\mathsf T\nu$ 或 $a=\nu$ (字典序在 $\nu$ 与 $\nu+1=\nu\mathbin{+\!\!+}[\mathbf 1]$ 之间没有项, 因为 $\mathbf 1=\psi_0(0)$ 是最小的主项). 它的两个用法: `cmpᵀ (ν+1) w` 为 `lt`/`eq` (规则 5Ω, 穿透) 推出 $\nu<^\mathsf T w$ (`pen→<`); 为 `gt` (规则 6, 折叠) 推出 $w<^\mathsf T\nu$ 或 $w=\nu$ (`gt→≤`). 这些对**一切**项成立, 不要标准形.

```agda
<ᵀ-irrefl : ∀ {a} → a <ᵀ a → ⊥
<ᵀ-irrefl {a} p with trans (sym (<→lt p)) (cmpᵀ-refl a)
... | ()

<ᵀ-asym : ∀ {a b} → a <ᵀ b → b <ᵀ a → ⊥
<ᵀ-asym p q = <ᵀ-irrefl (<ᵀ-trans p q)

gt→<  : ∀ a b → cmpᵀ a b ≡ gt → b <ᵀ a
gt→<ᴾ : ∀ x y → E.cmpᴾ x y ≡ gt → y <ᴾ x
gt→< [] [] ()
gt→< [] (y ∷ ys) ()
gt→< (x ∷ xs) [] e = []<
gt→< (x ∷ xs) (y ∷ ys) e with E.cmpᴾ x y in ex
... | gt = hd< (gt→<ᴾ x y ex)
... | eq rewrite eq→≡ᴾ x y ex = tl< (gt→< xs ys e)
gt→<ᴾ (ψᵗ u a) (ψᵗ v b) e with cmpᵀ u v in eu
... | gt = lv< (gt→< u v eu)
... | eq rewrite eq→≡ u v eu = ar< (gt→< a b e)

<sucT : ∀ {a} ν → a <ᵀ sucT ν → (a <ᵀ ν) ⊎ (a ≡ ν)
<sucT [] []< = inj₂ refl
<sucT [] (hd< (lv< ()))
<sucT [] (hd< (ar< ()))
<sucT [] (tl< ())
<sucT (y ∷ ys) []< = inj₁ []<
<sucT (y ∷ ys) (hd< p) = inj₁ (hd< p)
<sucT (y ∷ ys) (tl< p) with <sucT ys p
... | inj₁ q = inj₁ (tl< q)
... | inj₂ refl = inj₂ refl

pen→< : ∀ ν w → Pen (cmpᵀ (sucT ν) w) → ν <ᵀ w
pen→< ν w (inj₁ e) = <ᵀ-trans (E.<-sucT ν) (lt→< (sucT ν) w e)
pen→< ν w (inj₂ e) = subst (ν <ᵀ_) (eq→≡ (sucT ν) w e) (E.<-sucT ν)

gt→≤ : ∀ ν w → cmpᵀ (sucT ν) w ≡ gt → (w <ᵀ ν) ⊎ (w ≡ ν)
gt→≤ ν w e = <sucT ν (gt→< (sucT ν) w e)
```

`<sucT` 的 `[]` 情形里三个荒谬子句就是 "$\mathbf 1$ 最小": $x<^\mathsf P\psi_0(0)$ 要求下标或参数 $<^\mathsf T[\,]$, 没有构造子. (这个名字最初是 `<suc`, 报 `[ClashingDefinition] Multiple definitions of <suc` — Level 第 226 行已有同名引理.)

## §2 标准形

$\mathbb E$ (Correspond §8) 由 $0$、和、$\psi_0(a)$、$\psi_0(\Omega_1)$ 生成, 和的各项次序不受限制: $1+\omega$ 有推导 `g1+ω`. 句法上 `cmpᵀ (1+ω) ω ≡ lt` (首项 $1<\omega$), 而树上 $1+\omega$ 的翻译是 $\lim_n(1+n)$, $\omega$ 的是 $\lim_n n$, 两者在 Level 的结构序下**不可比** (§4 末). 所以序的对应要标准形前提. 取最直接的 Cantor 范式: `N0` 要求每个主项都是 $\psi_0(a)$ ($a$ 本身是 `N0`), 且相邻两项非增 (`Hd≤ xs x`: 尾巴的首项 $\le x$; 只约束相邻项, 需要的传递性在用到处由 `<ᴾ-trans` 现场补). `NF` 再加上唯一的顶 $\varepsilon_0=\psi_0(\Omega_1)$ (`nε`, EBO 的 `εₒ`). $\psi_0(\varepsilon_0)$、$\varepsilon_0+1$ 之类不是标准形 (Buchholz 意义下 $\psi_0(\varepsilon_0)=\varepsilon_0$), 不在 `NF` 里; 它们也不会出现在 $\gamma^\mathsf E_2$ 的闭包的下标里.

```agda
Hd≤ : T → PT → Set
Hd≤ []      x = ⊤
Hd≤ (y ∷ _) x = Pen (E.cmpᴾ y x)

data N0 : T → Set where
  n[] : N0 []
  n∷  : ∀ {a xs} → N0 a → N0 xs → Hd≤ xs (ψᵗ [] a) → N0 (ψᵗ [] a ∷ xs)

data NF : T → Set where
  n0 : ∀ {t} → N0 t → NF t
  nε : NF εₒ
```

`N0`/`NF` 是项上的谓词. `toE` 把它们的证明送进 $\mathbb E$, 下标的层号就是 Correspond 的 `lvl` 作用在它的翻译上 (§4 的 `lvN`).

```agda
toE0 : ∀ {t} → N0 t → 𝔼 t
toE0 n[]           = e[]
toE0 (n∷ na nxs _) = e∷ (eψ (toE0 na)) (toE0 nxs)

toE : ∀ {t} → NF t → 𝔼 t
toE (n0 x) = toE0 x
toE nε     = e∷ eΩ₁ e[]

𝔼-≡  : ∀ {t} (g g′ : 𝔼 t) → g ≡ g′
𝔼ᴾ-≡ : ∀ {x} (g g′ : 𝔼ᴾ x) → g ≡ g′
𝔼-≡ e[] e[] = refl
𝔼-≡ (e∷ x xs) (e∷ x′ xs′) = cong₂ e∷ (𝔼ᴾ-≡ x x′) (𝔼-≡ xs xs′)
𝔼ᴾ-≡ (eψ a) (eψ a′) = cong eψ (𝔼-≡ a a′)
𝔼ᴾ-≡ (eψ (e∷ () _)) eΩ₁
𝔼ᴾ-≡ eΩ₁ (eψ (e∷ () _))
𝔼ᴾ-≡ eΩ₁ eΩ₁ = refl

noΩ : ∀ {t μ} (g : 𝔼 t) → cof t ≡ cΩ μ → ⊥
noΩ {t} g e = subst (λ c → ShE ⟦ emb g ⟧ c t) e (corrE g)
```

$\mathbb E$ 的推导字面唯一 (`𝔼-≡`; `eψ` 对 `eΩ₁` 的两个交叉情形由下标 $[\mathbf 1]\ne[\,]$ 排除), 所以层号只依赖项本身. `noΩ` 是 Correspond `corrE` 的 $\Omega$ 行 ($\bot$) 的改写: $\mathbb E$ 项的共尾度不是 $\Omega_{\mu+1}$.

**封闭性.** `Hd≤-desc`: 若 $t<^\mathsf T y\mathbin{::}ys$ 且 $y\le x$, 则 $t$ 的首项 $\le x$. `pred` 与 `fsn` 的输出都 $<^\mathsf T$ 输入 (EBO 的 `pred-<` 与 `fsn↓` 的 `dec` 证书, 对一切项), 所以和的情形 ($\psi_0(a)+y+\cdots$, 基本列只动尾巴) 的相邻条件由 `Hd≤-desc` 一行保持. 单项 $\psi_0(a)$: $a$ 后继时规则 4 给 $\psi_0(a-1)\cdot n$ (`N0-rep`, 相邻相等), $a$ 极限时规则 5ω 给 $\psi_0(a[n])$ (归纳), `c0`/`cΩ` 由 `cof-ne`/`noΩ` 排除. `cofA≢c1`: $\psi_u(b)$ ($b\ne0$) 永远不是后继, 所以单项的 `pred` 情形是空的.

```agda
Hd≤-desc : ∀ {t y ys x} → t <ᵀ (y ∷ ys) → Pen (E.cmpᴾ y x) → Hd≤ t x
Hd≤-desc []< h = tt
Hd≤-desc {y = y} {x = x} (hd< p) (inj₁ e) = inj₁ (<ᴾ→lt (<ᴾ-trans p (lt→<ᴾ y x e)))
Hd≤-desc {y = y} {x = x} (hd< p) (inj₂ e) = inj₁ (<ᴾ→lt (subst (_ <ᴾ_) (eq→≡ᴾ y x e) p))
Hd≤-desc (tl< p) h = h

cofA≢c1 : ∀ u c → cofA u c ≡ c1 → ⊥
cofA≢c1 u c0 ()
cofA≢c1 u c1 ()
cofA≢c1 u cω ()
cofA≢c1 u (cΩ μ) e = go (cmpᵀ (sucT μ) u) e where
  go : ∀ m → cofψ₊ u μ m ≡ c1 → ⊥
  go lt ()
  go eq ()
  go gt ()

N0-pred : ∀ {t} → N0 t → cof t ≡ c1 → N0 (pred t)
N0-pred n[] ()
N0-pred (n∷ {a = []} n[] n[] _) e = n[]
N0-pred (n∷ {a = y ∷ ys} na n[] _) e = ⊥-elim (cofA≢c1 [] (cof (y ∷ ys)) e)
N0-pred (n∷ {xs = y ∷ ys} na nxs h) e = n∷ na (N0-pred nxs e) (Hd≤-desc (E.pred-< (y ∷ ys) e) h)

N0-rep : ∀ {b} → N0 b → ∀ n → N0 (replicate n (ψᵗ [] b))
N0-rep nb zero          = n[]
N0-rep nb (suc zero)    = n∷ nb n[] tt
N0-rep {b} nb (suc (suc n)) = n∷ nb (N0-rep nb (suc n)) (inj₂ (cmpᴾ-refl (ψᵗ [] b)))

N0-fsn  : ∀ {t} → N0 t → ∀ n → N0 (fsn t n)
N0-fsnψ : ∀ {y ys} → N0 (y ∷ ys) → ∀ c → cof (y ∷ ys) ≡ c → ∀ n → N0 (fsn (ψᵗ [] (y ∷ ys) ∷ []) n)
N0-fsn n[] n = n[]
N0-fsn (n∷ {a = []} n[] n[] _) n = n[]
N0-fsn (n∷ {a = y ∷ ys} na n[] _) n = N0-fsnψ na (cof (y ∷ ys)) refl n
N0-fsn (n∷ {xs = y ∷ ys} na nxs h) n = n∷ na (N0-fsn nxs n) (Hd≤-desc (dec (E.fsn↓ y ys n)) h)
N0-fsnψ {y} {ys} na c0 e n = ⊥-elim (cof-ne y ys e)
N0-fsnψ {y} {ys} na c1 e n = subst N0 (sym (fs-rep [] y ys e n)) (N0-rep (N0-pred na e) n)
N0-fsnψ {y} {ys} na cω e n = subst N0 (sym (fs-ω [] y ys e n)) (n∷ (N0-fsn na n) n[] tt)
N0-fsnψ na (cΩ μ) e n = ⊥-elim (noΩ (toE0 na) e)
```

$\varepsilon_0$ 的基本列是塔 $\psi_0^{n+1}(1)$ (`fsε`, 由 Correspond 的 `fs-Ω1`), 每一项都是 `N0` (`N0-ch`). 对角线的前两个下标在 `NF` 里, 第三个不在: $\gamma^\mathsf E_2=\psi_0(\Omega_{\varepsilon_0})$ 的参数里有非零下标的 $\Omega$, 不是 `N0`, 也不是 $\varepsilon_0$.

```agda
N0-ch : ∀ k → N0 (ch [] k)
N0-ch zero    = n∷ n[] n[] tt
N0-ch (suc k) = n∷ (N0-ch k) n[] tt

fsε : ∀ n → fsn εₒ n ≡ ch [] (suc n)
fsε n = fs-Ω1 (ψᵗ [] []) [] refl n

NF-fsn : ∀ {t} → NF t → ∀ n → NF (fsn t n)
NF-fsn (n0 x) n = n0 (N0-fsn x n)
NF-fsn nε     n = n0 (subst N0 (sym (fsε n)) (N0-ch (suc n)))

NF-pred : ∀ {t} → NF t → cof t ≡ c1 → NF (pred t)
NF-pred (n0 x) e = n0 (N0-pred x e)
NF-pred nε ()

diag-NF₀ : NF (γᴱ 0)
diag-NF₀ = n0 (n∷ n[] n[] tt)

diag-NF₁ : NF (γᴱ 1)
diag-NF₁ = nε

γᴱ₂∉NF : NF (γᴱ 2) → ⊥
γᴱ₂∉NF (n0 (n∷ () _ _))
```

`γᴱ₂∉NF` 就是本文的边界: $\gamma_3=\psi_0(\Omega_{\gamma_2})$ 的下标不在本文的下标系统里 (§9).

## §3 共尾性与句法 Bachmann 性质

序的对应 (§4) 在极限步只需要一条句法事实, **共尾性** `cofin`: 标准形 $v<u$ 且 $u$ 的共尾度为 $\omega$ 时, 某个 $u[n]$ 已经 $>v$. 先是位置引理: 一切 `N0` 项 $<\Omega_1$ (`N0<Ω₁`), 从而 $<\varepsilon_0$ (`N0<ε`); $\varepsilon_0$ 不小于任何 `N0` 项 (`ε≮N0`; `tl<` 情形要求 $\Omega_1$ 是 `N0`, 构造子不匹配).

```agda
N0<Ω₁ : ∀ {a} → N0 a → a <ᵀ Ωt (natT 1)
N0<Ω₁ n[]        = []<
N0<Ω₁ (n∷ _ _ _) = hd< (lv< []<)

N0<ε : ∀ {a} → N0 a → a <ᵀ εₒ
N0<ε n[]         = []<
N0<ε (n∷ na _ _) = hd< (ar< (N0<Ω₁ na))

ε≮N0 : ∀ {a} → N0 a → εₒ <ᵀ a → ⊥
ε≮N0 (n∷ na _ _) (hd< (lv< ()))
ε≮N0 (n∷ na _ _) (hd< (ar< p)) = <ᵀ-asym p (N0<Ω₁ na)
ε≮N0 (n∷ () _ _) (tl< _)
```

`ht a` 是首项的指数塔高度, `tw`: $a<$ 高为 `ht a` 的塔 (`ch [] (ht a)`), 塔严格递增 (`ch<`), 而 $\varepsilon_0[n]=$ `ch [] (suc n)`; 这是 $\varepsilon_0$ 处的共尾性. `repb` 是规则 4 处的共尾性: 首项都 $\le x$ 的标准形 $vs$ 小于某个 $x\cdot m$ (对 $vs$ 归纳: 与 $x$ 相等的首项消去, 第一个严格更小的首项结束比较); `rep<`: $x\cdot m<x\cdot(m+1)$. 工程注记: `repb` 里的变量最初叫 `hz`, 被当成 Level 的构造子 `hz : HS zero`, 报 `[SplitError.NotADatatype] Cannot split on argument of non-datatype Hd≤ xs (ψᵗ [] a)`; 改名 `hz₀`.

```agda
ht : T → ℕ
ht []           = zero
ht (ψᵗ u a ∷ _) = suc (ht a)

tw : ∀ {a} → N0 a → a <ᵀ ch [] (ht a)
tw n[]         = []<
tw (n∷ na _ _) = hd< (ar< (tw na))

ch< : ∀ k → ch [] k <ᵀ ch [] (suc k)
ch< zero    = hd< (ar< []<)
ch< (suc k) = hd< (ar< (ch< k))

repb : ∀ x {vs} → N0 vs → Hd≤ vs x → Σ ℕ λ m → vs <ᵀ replicate m x
repb x n[] h = 1 , []<
repb x (n∷ {a} na nzs hz₀) (inj₁ e) = 1 , hd< (lt→<ᴾ (ψᵗ [] a) x e)
repb x (n∷ {a} na nzs hz₀) (inj₂ e) with eq→≡ᴾ (ψᵗ [] a) x e
... | refl with repb x nzs hz₀
...   | m , q = suc m , tl< q

rep< : ∀ x m → replicate m x <ᵀ replicate (suc m) x
rep< x zero    = []<
rep< x (suc m) = tl< (rep< x m)
```

**共尾性.** `cofin0` 对 $u$ 的 `N0` 证明归纳. 和 $\psi_0(a)+y+\cdots$: $v$ 在首项处已小 (`[]<`/`hd<`) 时取 $n=0$; 首项相等 (`tl<`) 时对尾巴归纳. 单项 $\psi_0(a)$ (`cofinψ`, 按 `cof a` 分): $a$ 后继时 $u[n]=\psi_0(a-1)\cdot n$, $v=\psi_0(b)+\cdots$ 且 $b<a$, 由离散性 $b<a-1$ (取 $n=1$) 或 $b=a-1$ (由 `repb` 取 $n=m+1$); $a$ 极限时 $u[n]=\psi_0(a[n])$, 对 $a$ 递归得 $b<a[n]$. $v$ 的标准形只在 `repb` 处用到 (尾巴的首项 $\le\psi_0(b)$), 非标准项正是在这里失败: $1+\omega<\omega$, 但 $1+\omega$ 不小于任何 $\omega[n]=n$. `cofin` 把 `NF` 的四种组合拼起来 ($\varepsilon_0$ 对 $\varepsilon_0$ 与 $\varepsilon_0<$ `N0` 都荒谬).

```agda
cofin0  : ∀ {u} → N0 u → cof u ≡ cω → ∀ {v} → N0 v → v <ᵀ u → Σ ℕ λ n → v <ᵀ fsn u n
cofinψ  : ∀ {y ys} → N0 (y ∷ ys) → ∀ c → cof (y ∷ ys) ≡ c →
          ∀ {v} → N0 v → v <ᵀ (ψᵗ [] (y ∷ ys) ∷ []) → Σ ℕ λ n → v <ᵀ fsn (ψᵗ [] (y ∷ ys) ∷ []) n
cofin0 n[] () _ _
cofin0 (n∷ {a = []} n[] n[] _) () _ _
cofin0 (n∷ {a = y ∷ ys} na n[] _) e nv p = cofinψ na (cof (y ∷ ys)) refl nv p
cofin0 (n∷ {xs = y ∷ ys} na nxs h) e nv []< = 0 , []<
cofin0 (n∷ {xs = y ∷ ys} na nxs h) e nv (hd< q) = 0 , hd< q
cofin0 (n∷ {xs = y ∷ ys} na nxs h) e (n∷ _ nvs _) (tl< q) with cofin0 nxs e nvs q
... | n , q′ = n , tl< q′
cofinψ {y} {ys} na c0 ce nv p = ⊥-elim (cof-ne y ys ce)
cofinψ {y} {ys} na c1 ce n[] p = 1 , subst ([] <ᵀ_) (sym (fs-rep [] y ys ce 1)) []<
cofinψ {y} {ys} na c1 ce (n∷ {a = b} nb nvs hv) (hd< (lv< ()))
cofinψ {y} {ys} na c1 ce (n∷ {a = b} nb nvs hv) (tl< ())
cofinψ {y} {ys} na c1 ce (n∷ {a = b} {xs = vs} nb nvs hv) (hd< (ar< q))
  with <sucT (pred (y ∷ ys)) (subst (b <ᵀ_) (sym (E.pred-suc (y ∷ ys) ce)) q)
... | inj₁ r = 1 , subst ((ψᵗ [] b ∷ vs) <ᵀ_) (sym (fs-rep [] y ys ce 1)) (hd< (ar< r))
... | inj₂ refl with repb (ψᵗ [] b) nvs hv
...   | m , r = suc m , subst ((ψᵗ [] b ∷ vs) <ᵀ_) (sym (fs-rep [] y ys ce (suc m))) (tl< r)
cofinψ {y} {ys} na cω ce n[] p = 0 , subst ([] <ᵀ_) (sym (fs-ω [] y ys ce 0)) []<
cofinψ {y} {ys} na cω ce (n∷ {a = b} nb nvs hv) (hd< (lv< ()))
cofinψ {y} {ys} na cω ce (n∷ {a = b} nb nvs hv) (tl< ())
cofinψ {y} {ys} na cω ce (n∷ {a = b} {xs = vs} nb nvs hv) (hd< (ar< q)) with cofin0 na ce nb q
... | n , r = n , subst ((ψᵗ [] b ∷ vs) <ᵀ_) (sym (fs-ω [] y ys ce n)) (hd< (ar< r))
cofinψ na (cΩ μ) ce nv p = ⊥-elim (noΩ (toE0 na) ce)

cofin : ∀ {u} → NF u → cof u ≡ cω → ∀ {v} → NF v → v <ᵀ u → Σ ℕ λ n → v <ᵀ fsn u n
cofin (n0 nu) e (n0 nv) p = cofin0 nu e nv p
cofin (n0 nu) e nε      p = ⊥-elim (ε≮N0 nu p)
cofin nε      e {v} (n0 nv) p = ht v , subst (v <ᵀ_) (sym (fsε (ht v))) (<ᵀ-trans (tw nv) (ch< (ht v)))
cofin nε      e nε      p = ⊥-elim (<ᵀ-irrefl p)
```

**句法 Bachmann 性质.** 对 `NF` 极限 $u$, `fs-mono`: $u[m]<^\mathsf T u[m+1]$ (塔、$x\cdot m$、对指数归纳、对尾巴归纳四种情形); 迭代得 `bach-syn`: $m<m'\Rightarrow u[m]<^\mathsf T u[m']$ (`_<ᴺ_` 是 BTBO `Trich` 的自然数序).

```agda
fs-mono0 : ∀ {u} → N0 u → cof u ≡ cω → ∀ m → fsn u m <ᵀ fsn u (suc m)
fs-monoψ : ∀ {y ys} → N0 (y ∷ ys) → ∀ c → cof (y ∷ ys) ≡ c → ∀ m →
           fsn (ψᵗ [] (y ∷ ys) ∷ []) m <ᵀ fsn (ψᵗ [] (y ∷ ys) ∷ []) (suc m)
fs-mono0 n[] ()
fs-mono0 (n∷ {a = []} n[] n[] _) ()
fs-mono0 (n∷ {a = y ∷ ys} na n[] _) e m = fs-monoψ na (cof (y ∷ ys)) refl m
fs-mono0 (n∷ {xs = y ∷ ys} na nxs h) e m = tl< (fs-mono0 nxs e m)
fs-monoψ {y} {ys} na c0 ce m = ⊥-elim (cof-ne y ys ce)
fs-monoψ {y} {ys} na c1 ce m =
  subst₂ _<ᵀ_ (sym (fs-rep [] y ys ce m)) (sym (fs-rep [] y ys ce (suc m))) (rep< _ m)
fs-monoψ {y} {ys} na cω ce m =
  subst₂ _<ᵀ_ (sym (fs-ω [] y ys ce m)) (sym (fs-ω [] y ys ce (suc m))) (hd< (ar< (fs-mono0 na ce m)))
fs-monoψ na (cΩ μ) ce m = ⊥-elim (noΩ (toE0 na) ce)

fs-mono : ∀ {u} → NF u → cof u ≡ cω → ∀ m → fsn u m <ᵀ fsn u (suc m)
fs-mono (n0 x) e m = fs-mono0 x e m
fs-mono nε     e m = subst₂ _<ᵀ_ (sym (fsε m)) (sym (fsε (suc m))) (ch< (suc m))

bach-syn : ∀ {u} → NF u → cof u ≡ cω → ∀ {m m′} → m <ᴺ m′ → fsn u m <ᵀ fsn u m′
bach-syn su e zero    = fs-mono su e _
bach-syn su e (suc p) = <ᵀ-trans (bach-syn su e p) (fs-mono su e _)
```

`bach-syn` 在本文的证明链里没有被用到 (序的对应只要共尾性). 它与 §4 的树版 `bach` 是 Closure §9 末设想的 "按路径首个分叉比较" 所需的事实, 现在都是推论.

## §4 序的对应 (树侧)

`T⟦ s ⟧` 是标准形下标在 Correspond 翻译下的第 0 层树, `lvN s` 是它的层号 (Correspond 的 `lvl`: `toLevel` 加 `good` 的证书). `T-≡`: 同一个项的两个 `NF` 证明给出 $\cong$ 的树 (经 `𝔼-≡`).

```agda
T⟦_⟧ : ∀ {t} → NF t → Ordᶜ zero
T⟦ s ⟧ = ⟦ emb (toE s) ⟧

lvN : ∀ {t} → NF t → Ordᴵ
lvN s = lvl (emb (toE s))

E-≅ : ∀ {t} (g g′ : 𝔼 t) → ⟦ emb g ⟧ ≅ ⟦ emb g′ ⟧
E-≅ g g′ = subst (λ h → ⟦ emb g ⟧ ≅ ⟦ emb h ⟧) (𝔼-≡ g g′) (≅-refl⁰ _)

T-≡ : ∀ {v v′} → v ≡ v′ → (sv : NF v) (sv′ : NF v′) → T⟦ sv ⟧ ≅ T⟦ sv′ ⟧
T-≡ refl sv sv′ = E-≅ (toE sv) (toE sv′)
```

**主引理** `oc`: 若第 0 层的树 $X\cong$ `T⟦ su ⟧` 且 $v<^\mathsf T u$, 则 `T⟦ sv ⟧` $\prec X$. 对 $X$ 结构递归 (表记侧不需要 `Acc`), 由 `corrE` 读 $u$ 的形状:

- $u$ 后继: $X=\mathrm{suc}\,Y$, $Y\cong\llbracket u-1\rrbracket$. 由离散性, $v<u-1$ 时对 $Y$ 递归再 `≺s`; $v=u-1$ 时 `≺z` (叶子 $\cong$, 经 `T-≡`).
- $u$ 极限: $X=\lim F$, $F\,n\cong\llbracket u[n]\rrbracket$. 由共尾性取 $n$ 使 $v<u[n]$, 对 $F\,n$ 递归再 `≺l n`.
- $u=0$ 时无 $v<u$; $\Omega$ 行由 `corrE` 排除; 形状与 $X$ 的构造子不符的情形由 Correspond 的 `z≇s` 等排除.

极限步**不**需要 Bachmann 性质. Closure §2 说的困难 (`toLevel (lim F)` 的第 $n$ 项与整体只差 `self n`, 要严格性需要某个 $F\,n\prec F\,m$, 而 `HS` 只给 $\sqsubseteq$) 在这里不出现: 要证的是 $v\prec\lim F$, 而 $v$ 严格小于**某个** $u[n]$ (共尾性), 严格性来自对 $F\,n$ 的递归, 不来自步进.

```agda
oc   : ∀ (X : Ordᶜ zero) {u} (su : NF u) → X ≅ T⟦ su ⟧ → ∀ {v} (sv : NF v) → v <ᵀ u → T⟦ sv ⟧ ≺ X
ocSh : ∀ (X : Ordᶜ zero) {u} (su : NF u) c → cof u ≡ c → ShE T⟦ su ⟧ c u → X ≅ T⟦ su ⟧ →
       ∀ {v} (sv : NF v) → v <ᵀ u → T⟦ sv ⟧ ≺ X
oc X {u} su d sv p = ocSh X su (cof u) refl (corrE (toE su)) d sv p

ocSh X {u = []} su c ce sh d sv ()
ocSh X {u = x ∷ xs} su c0 ce sh d sv p = ⊥-elim (cof-ne x xs ce)
ocSh zero    {u = x ∷ xs} su c1 ce (g′ , eg) d sv p = ⊥-elim (z≇s (≅-trans d eg))
ocSh (lim F) {u = x ∷ xs} su c1 ce (g′ , eg) d sv p = ⊥-elim (l≇s (≅-trans d eg))
ocSh (suc Y) {u = u@(x ∷ xs)} su c1 ce (g′ , eg) d {v} sv p
  with <sucT (pred u) (subst (v <ᵀ_) (sym (E.pred-suc u ce)) p)
... | inj₁ q = ≺s (oc Y sp hY sv q)
  where sp = NF-pred su ce
        hY = ≅-trans (s-inv (≅-trans d eg)) (E-≅ g′ (toE sp))
... | inj₂ e = ≺z (≅-trans (T-≡ e sv sp) (≅-sym hY))
  where sp = NF-pred su ce
        hY = ≅-trans (s-inv (≅-trans d eg)) (E-≅ g′ (toE sp))
ocSh zero    {u = x ∷ xs} su cω ce (G , eG , hG) d sv p = ⊥-elim (z≇l (≅-trans d eG))
ocSh (suc Y) {u = x ∷ xs} su cω ce (G , eG , hG) d sv p = ⊥-elim (s≇l (≅-trans d eG))
ocSh (lim F) {u = u@(x ∷ xs)} su cω ce (G , eG , hG) d sv p with cofin su ce sv p
... | n , q = ≺l n (oc (F n) (NF-fsn su n) hn sv q)
  where hn = ≅-trans (l-inv (≅-trans d eG) n) (≅-trans (proj₂ (hG n)) (E-≅ (proj₁ (hG n)) (toE (NF-fsn su n))))
ocSh X {u = x ∷ xs} su (cΩ μ) ce () d sv p
ocSh (limᵢ () f) {u = x ∷ xs} su c1 ce sh d sv p
ocSh (up () y)   {u = x ∷ xs} su c1 ce sh d sv p
ocSh (limᵢ () f) {u = x ∷ xs} su cω ce sh d sv p
ocSh (up () y)   {u = x ∷ xs} su cω ce sh d sv p
```

`OC<` 是 $X=$ `T⟦ su ⟧` 的特例 (第 0 层 $\cong$ 自反). 经 Level 的 `toLevel-≺`/`toLevel-≅` 搬到层号, 得到下标层的**序的对应** `OC-lt`/`OC-eq`/`OC-gt`. 严格性来自树的 $\prec$, 不来自 `HS` 的步进 (任务坑表的要求).

```agda
OC< : ∀ {v u} (sv : NF v) (su : NF u) → v <ᵀ u → T⟦ sv ⟧ ≺ T⟦ su ⟧
OC< sv su p = oc T⟦ su ⟧ su (≅-refl⁰ _) sv p

OC-lt : ∀ {v u} (sv : NF v) (su : NF u) → cmpᵀ v u ≡ lt → lvN sv ≺ᴵ lvN su
OC-lt {v} {u} sv su e = toLevel-≺ (cert (emb (toE sv))) (cert (emb (toE su))) (OC< sv su (lt→< v u e))

OC-eq : ∀ {v u} (sv : NF v) (su : NF u) → cmpᵀ v u ≡ eq → lvN sv ≅ᴵ lvN su
OC-eq {v} {u} sv su e = toLevel-≅ (cert (emb (toE sv))) (cert (emb (toE su))) (T-≡ (eq→≡ v u e) sv su)

OC-gt : ∀ {v u} (sv : NF v) (su : NF u) → cmpᵀ v u ≡ gt → lvN su ≺ᴵ lvN sv
OC-gt {v} {u} sv su e = toLevel-≺ (cert (emb (toE su))) (cert (emb (toE sv))) (OC< su sv (gt→< v u e))
```

**树上的 Bachmann 性质**是推论: `bach` ($m<m'\Rightarrow\llbracket u[m]\rrbracket\prec\llbracket u[m']\rrbracket$), `fs≺` ($\llbracket u[n]\rrbracket\prec\llbracket u\rrbracket$), `pred≺` ($\llbracket u-1\rrbracket\prec\llbracket u\rrbracket$). `fs<ᵀ` (句法 $u[n]<u$) 对一切极限项成立.

```agda
bach : ∀ {u} (su : NF u) (e : cof u ≡ cω) {m m′} → m <ᴺ m′ → T⟦ NF-fsn su m ⟧ ≺ T⟦ NF-fsn su m′ ⟧
bach su e p = OC< (NF-fsn su _) (NF-fsn su _) (bach-syn su e p)

fs<ᵀ : ∀ {u} → cof u ≡ cω → ∀ n → fsn u n <ᵀ u
fs<ᵀ {u = []} () n
fs<ᵀ {u = x ∷ xs} e n = dec (E.fsn↓ x xs n)

fs≺ : ∀ {u} (su : NF u) (e : cof u ≡ cω) n → T⟦ NF-fsn su n ⟧ ≺ T⟦ su ⟧
fs≺ su e n = OC< (NF-fsn su n) su (fs<ᵀ e n)

pred≺ : ∀ {u} (su : NF u) (e : cof u ≡ c1) → T⟦ NF-pred su e ⟧ ≺ T⟦ su ⟧
pred≺ {u} su e = OC< (NF-pred su e) su (E.pred-< u e)
```

**非标准形处失败.** $1+\omega$ 不是 `NF` (`1+ω∉NF`: `Hd≤` 要 `cmpᴾ ω 1` 为 `lt`/`eq`, 实际是 `gt`). 树上 $\llbracket 1+\omega\rrbracket=\lim_n(1+n)$, $\llbracket\omega\rrbracket=\lim_n n$ (定义性展开, 下面直接对 `≺l`/`l≅` 匹配). 极限树不能 $\prec$ 或 $\cong$ 一个只由 `zero`/`suc` 构成的树 (`lim≺Fin`, `lim≅Fin`), 于是:

```agda
1+ω : T
1+ω = ψᵗ [] [] ∷ ωᵗ

g1+ω : 𝔼 1+ω
g1+ω = e∷ (eψ e[]) (e∷ (eψ (e∷ (eψ e[]) e[])) e[])

gω′ : 𝔼 ωᵗ
gω′ = e∷ (eψ (e∷ (eψ e[]) e[])) e[]

_ : cmpᵀ 1+ω ωᵗ ≡ lt
_ = refl

1+ω∉NF : NF 1+ω → ⊥
1+ω∉NF (n0 (n∷ _ _ (inj₁ ())))
1+ω∉NF (n0 (n∷ _ _ (inj₂ ())))

data Fin : Ordᶜ zero → Set where
  fz : Fin zero
  fs : ∀ {x} → Fin x → Fin (suc x)

Fin-1+ : ∀ {x} → Fin x → Fin (suc zero + x)
Fin-1+ fz     = fs fz
Fin-1+ (fs h) = fs (Fin-1+ h)

Fin-it : ∀ n → Fin (iter (suc zero +_) zero n)
Fin-it zero    = fz
Fin-it (suc n) = Fin-1+ (Fin-it n)

lim≅Fin : ∀ {K} {F : ℕ → Ordᶜ K} {y} → Fin y → lim F ≅ y → ⊥
lim≅Fin fz     ()
lim≅Fin (fs h) ()

lim≺Fin : ∀ {K} {F : ℕ → Ordᶜ K} {y} → Fin y → lim F ≺ y → ⊥
lim≺Fin fz     ()
lim≺Fin (fs h) (≺z e) = lim≅Fin h e
lim≺Fin (fs h) (≺s p) = lim≺Fin h p

nf-fail₁ : ⟦ emb g1+ω ⟧ ≺ ⟦ emb gω′ ⟧ → ⊥
nf-fail₁ (≺l n p) = lim≺Fin (Fin-it n) p

nf-fail₂ : ⟦ emb gω′ ⟧ ≺ ⟦ emb g1+ω ⟧ → ⊥
nf-fail₂ (≺l n p) = lim≺Fin (Fin-1+ (Fin-it n)) p

nf-fail₃ : ⟦ emb g1+ω ⟧ ≅ ⟦ emb gω′ ⟧ → ⊥
nf-fail₃ (l≅ h) with h 0
... | ()
```

`nf-fail₁`/`nf-fail₂`/`nf-fail₃`: 两者既不 $\prec$ 也不 $\cong$, 而 `cmpᵀ (1+ω) ω ≡ lt`. 序的对应对非标准项是假的, 标准形前提不可去. (句法上 $1+\omega<\omega$ 而两者的值相等; 树的结构序又比值的序更细. 两层 "偏差" 叠加成不可比.)

## §5 通用形状定理: 证据由序的对应现场制造

先是与下标系统无关的树侧与记号侧引理 (对一切层号、一切项):

- `fold⁺`: 若目标层 $i$ 与 `limᵢ` 节点的指标层 $j$ 满足 $i\prec^\mathsf I j$ 或 $i\cong^\mathsf I j$, 则 `ψ p σ (limᵢ q f)` **字面地** (`with` 抽象后 `refl`) 等于规则 6 的折叠 `lim (λ n → ψ p σ (f (chainT q f n)))`, $\gamma$-链 `chainT` 起点 $\Omega_j$, 每步 `ψ q id`. 穿透分支由 `clash` ($\prec^\mathsf I$ 无自反) 排除. 它与 Closure 的 `pen⁺` 是树的派发的两半.
- `fs-gt`: 记号的规则 6 的裸值 $\psi_u(b)[n]=\psi_u(b[\gamma_n])$ (`cmpᵀ (ν+1) u ≡ gt`), 由 EBO 的 J-对齐引理得到 (与 Closure `K-suc` 内的 `fsS` 同法).
- 跨层的构造子不符 (`zs`/`ls`/`zl`/`sl`), 以及第 0 层的树不 $\cong$ 任何 `limᵢ` (`noΩ0`).

```agda
clash : ∀ {i j} → j ≺ᴵ i → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ⊥
clash s (inj₁ t) = ≺ᴵ-irrefl (≺ᴵ-trans s t)
clash s (inj₂ c) = ≺ᴵ-irrefl (≺ᴵ-respʳ s c)

chainT : ∀ {j K} (q : j <ᴵ K) (f : U j (<→◃ q) → Ordᶜ K) → ℕ → Ordᶜ j
chainT {j} q f = iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j)

fold⁺ : ∀ {i k K j} {p : i <ᴵ k} {σ : Simᴵ K k} {q : j <ᴵ K} {f : U j (<→◃ q) → Ordᶜ K} →
        (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ψ p σ (limᵢ q f) ≡ lim (λ n → ψ p σ (f (into (<→◃ q) (chainT q f n))))
fold⁺ {p = p} {σ = σ} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

fs-gt : ∀ u y ys ν (be : cof (y ∷ ys) ≡ cΩ ν) → cmpᵀ (sucT ν) u ≡ gt → ∀ n →
        fsn (ψᵗ u (y ∷ ys) ∷ []) n ≡ ψᵗ u (fsT (y ∷ ys) (γT (y ∷ ys) ν n)) ∷ []
fs-gt u y ys ν be em n =
  trans (E.fsn₊-eq u y ys n be)
  (trans (fsn↓c-gt u y ys ν be (cmpᵀ (sucT ν) u) em n)
         (cong (λ z → ψᵗ u z ∷ [])
               (trans (E.fsT↓-trm (y ∷ ys) be (dec (E.γ↓ (y ∷ ys) ν be n)))
                      (cong (fsT (y ∷ ys)) (E.γ↓-trm (y ∷ ys) ν be n)))))

zs : ∀ {K K′} {Y : Ordᶜ K′} → 𝟎 {K} ≅ suc Y → ⊥
zs ()
ls : ∀ {K K′} {F : ℕ → Ordᶜ K} {Y : Ordᶜ K′} → lim F ≅ suc Y → ⊥
ls ()
zl : ∀ {K K′} {G : ℕ → Ordᶜ K′} → 𝟎 {K} ≅ lim G → ⊥
zl ()
sl : ∀ {K K′} {Y : Ordᶜ K} {G : ℕ → Ordᶜ K′} → suc Y ≅ lim G → ⊥
sl ()

noΩ0 : ∀ {j K} {q : j <ᴵ K} {f : U j (<→◃ q) → Ordᶜ K} (X : Ordᶜ zero) → X ≅ limᵢ q f → ⊥
noΩ0 zero ()
noΩ0 (suc X) ()
noΩ0 (lim F) ()
noΩ0 (limᵢ () f) e
noΩ0 (up () x) e
```

**接口.** `Generic` 的参数: 下标谓词 `Sub` 与层号 `lvS`; 公共上界 `A` (`inA`: 每个下标的层号 $\prec^\mathsf I A$); 下标 $0$ 的层号 $\cong^\mathsf I 0$ (`S0`); 后继下标 $w$ 的层号 $\cong^\mathsf I$ `suc (lvS (w−1))` 且 $w-1$ 仍是下标 (`S1`); 极限下标的层号 $\cong^\mathsf I$ 某个字面的 `lim g st`, 且 `g n` $\cong^\mathsf I$ 下标 $w[n]$ 的层号 (`Sω`); 下标可数 (`SΩ`); **序的对应** `Slt`/`Seq`. `S0`/`S1`/`Sω`/`SΩ` 是 Correspond/Closure 已有形状事实 (`Ω-shape1`/`Ω-shapeω`/`ΩshE1`/`ΩshEω`) 的层号版; 新的是 `inA` 与 `Slt`/`Seq`, 都来自序的对应. 这正是交替总方向的不变量的形式化: 被比较的下标有公共上界 (`inA`), 比较由句法决定 (`Slt`/`Seq`).

```agda
module Generic
  (Sub : T → Set)
  (lvS : ∀ {w} → Sub w → Ordᴵ)
  (A : Ordᴵ)
  (inA : ∀ {w} (s : Sub w) → lvS s ≺ᴵ A)
  (S0 : (s : Sub []) → lvS s ≅ᴵ zero)
  (S1 : ∀ {w} (s : Sub w) → cof w ≡ c1 → Σ (Sub (pred w)) λ s′ → lvS s ≅ᴵ suc (lvS s′))
  (Sω : ∀ {w} (s : Sub w) → cof w ≡ cω → Σ (ℕ → Ordᴵ) λ g → Σ (∀ n → g n ⊑ᴵ g (suc n)) λ st →
        (lvS s ≅ᴵ lim g st) × (∀ n → Σ (Sub (fsn w n)) λ s′ → g n ≅ᴵ lvS s′))
  (SΩ : ∀ {w μ} → Sub w → cof w ≡ cΩ μ → ⊥)
  (Slt : ∀ {v u} (sv : Sub v) (su : Sub u) → cmpᵀ v u ≡ lt → lvS sv ≺ᴵ lvS su)
  (Seq : ∀ {v u} (sv : Sub v) (su : Sub u) → cmpᵀ v u ≡ eq → lvS sv ≅ᴵ lvS su)
  where
```

**类与翻译.** `𝔸`: 一切 $\psi$-下标都满足 `Sub` 的 EBO 项; 和与参数不要求标准形 (与 FiniteAll 的 `corr` 一样, 形状定理对任意主项成立, 标准形只在下标的比较里起作用). 翻译把每个项放在**同一个环境层 $A$**: 和是 $A$ 层的 `_+_`; 主项 $\psi_w(a)$ 取 `inA` 给出的代表元 ($\mathtt{lvS}\,w\cong^\mathsf I W'<^\mathsf I A$), 以 `ψ q id` 把 $A$ 层的参数折叠到 $W'$, 再 `lift` 回 $A$ (`node`).

```agda
  data 𝔸  : T → Set
  data 𝔸ᴾ : PT → Set
  data 𝔸 where
    a[] : 𝔸 []
    a∷  : ∀ {x xs} → 𝔸ᴾ x → 𝔸 xs → 𝔸 (x ∷ xs)
  data 𝔸ᴾ where
    aψ : ∀ {w a} → Sub w → 𝔸 a → 𝔸ᴾ (ψᵗ w a)

  node : ∀ {M} → M ≺ᴵ A → Ordᶜ A → Ordᶜ A
  node (via e q) x = lift (<→◃ q) (ψ q (λ r → r) x)

  ⟦_⟧ᵃ : ∀ {t} → 𝔸 t → Ordᶜ A
  ⟦_⟧ᵖ : ∀ {x} → 𝔸ᴾ x → Ordᶜ A
  ⟦ a[] ⟧ᵃ     = zero
  ⟦ a∷ x xs ⟧ᵃ = ⟦ x ⟧ᵖ + ⟦ xs ⟧ᵃ
  ⟦ aψ s d ⟧ᵖ  = node (inA s) ⟦ d ⟧ᵃ
```

不同证据、不同代表元给出的节点都 $\cong$ (`node-≅`: 任何目标层 $\cong^\mathsf I$ `lvS` 的折叠, 作用在 $\cong$ 的参数上, 都 $\cong$ 翻译的节点; Level 的 `ψ-≅` 允许 $\cong^\mathsf I$-相关的目标层与任意 `σ`), 所以翻译只依赖项 (模 $\cong$). `Ω-node` 是参数为 $0$ 的情形 ($\psi_w(0)=\Omega_{W'}$, 定义性). 翻译自反 (`⟦⟧-refl`) 在 $A$ 层不是白给的 (`≅` 只是 PER). 与 Closure 对照: 那里的节点形状取决于子节点与本节点的相对位置 (`nodeᵇ` 经 `emb⊴`, `nodeᵃ` 经 `tr⁻`), 需要相应的位置证据并随推导维护; 这里参数总在公共上界层, 没有相对位置.

```agda
  node-≅ : ∀ {M} (ev : M ≺ᴵ A) {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordᶜ k} {Y : Ordᶜ A} →
           i ≅ᴵ M → X ≅ Y → ψ p σ X ≅ node ev Y
  node-≅ (via e q) {p = p} {σ = σ} ei d =
    ≅-sym (lift-≅ (<→◃ q) (ψ-≅ {p = q} {σ = λ r → r} {p′ = p} {σ′ = σ} (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-sym ei)) (≅-sym d)))

  Ω-node : ∀ {M} (ev : M ≺ᴵ A) {i} → i ≅ᴵ M → Ω i ≅ node ev zero
  Ω-node (via e q) ei = ≅-sym (lift-≅ (<→◃ q) (Ω-≅ (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-sym ei))))

  node-refl : ∀ {M} (ev : M ≺ᴵ A) {X : Ordᶜ A} → X ≅ X → node ev X ≅ node ev X
  node-refl (via e q) d = lift-≅ (<→◃ q) (node-≅ (via e q) {p = q} {σ = λ r → r} (≅ᴵ-sym e) d)

  ⟦⟧-refl  : ∀ {t} (d : 𝔸 t) → ⟦ d ⟧ᵃ ≅ ⟦ d ⟧ᵃ
  ⟦⟧ᴾ-refl : ∀ {x} (d : 𝔸ᴾ x) → ⟦ d ⟧ᵖ ≅ ⟦ d ⟧ᵖ
  ⟦⟧-refl a[]       = z≅
  ⟦⟧-refl (a∷ x xs) = add-≅ (⟦⟧ᴾ-refl x) (⟦⟧-refl xs)
  ⟦⟧ᴾ-refl (aψ s d) = node-refl (inA s) (⟦⟧-refl d)
```

**形状** `Sh X c t` 与 FiniteAll §6 同形, 四行由 `cof t` 决定. `lim`/`limᵢ` 在 $X$ **自己的层**上 (后面要把 `ψ p σ X` 换成 `ψ p σ (limᵢ q f)` 让派发计算, 要同一个 `σ`), 匹配的翻译 `⟦ d ⟧ᵃ` 在 $A$ 层 (跨层 $\cong$). $\Omega_{\nu+1}$ 行: 下标 $\nu$ 满足 `Sub`, 指标层 $j\cong^\mathsf I$ `lvS sν`, 分支在任何 "$\cong$ 某个 `𝔸` 项 $\eta$ 的翻译" 的树 $x$ 处匹配 $t[\eta]$ (`fsT t η`). 只对项陈述 (Closure 的 `ShΩ` 对任意树), 因为规则 6 的 $\gamma$-链的每一项都是项.

```agda
  Match : T → ∀ {K} → Ordᶜ K → Set
  Match s Y = Σ (𝔸 s) λ d → Y ≅ ⟦ d ⟧ᵃ

  Match-≡ : ∀ {s s′ K} {Y : Ordᶜ K} → s ≡ s′ → Match s′ Y → Match s Y
  Match-≡ refl m = m

  Sh : ∀ {K} → Ordᶜ K → Cof → T → Set
  Sh     X c0     t = X ≅ 𝟎 {A}
  Sh {K} X c1     t = Σ (Ordᶜ K) λ Y → (X ≅ suc Y) × Match (pred t) Y
  Sh {K} X cω     t = Σ (ℕ → Ordᶜ K) λ G → (X ≅ lim G) × (∀ n → Match (fsn t n) (G n))
  Sh {K} X (cΩ ν) t = Σ (Sub ν) λ sν → Σ Ordᴵ λ j → Σ (j <ᴵ K) λ q → Σ (U j (<→◃ q) → Ordᶜ K) λ f →
    (j ≅ᴵ lvS sν) × (X ≅ limᵢ q f) ×
    (∀ η (dη : 𝔸 η) (x : Ordᶜ j) → x ≅ ⟦ dη ⟧ᵃ → Match (fsT t η) (f (into (<→◃ q) x)))
```

`Sh-lift`: 形状沿 `lift r` 搬到上层. `limᵢ` 行用 Closure 的 `<◃` ($j<^\mathsf I K\triangleleft\ell\Rightarrow j<^\mathsf I\ell$) 把节点挂到上层, 分支经 `out-into` 对齐, 互模拟的分支条件由 Uniform 的 `i-resp` 给出.

```agda
  Sh-lift : ∀ c {t K ℓ} (r : K ◃ ℓ) {X : Ordᶜ K} → Sh X c t → Sh (lift r X) c t
  Sh-lift c0 r e = lift-≅ r e
  Sh-lift c1 r (Y , eY , d , ed) =
    lift r Y , lift-≅ r (≅-trans eY (s≅ (≅-sym (lift-≅ r (≅-reflˡ ed))))) , d , lift-≅ r ed
  Sh-lift cω r (G , eG , hG) =
    (λ n → lift r (G n)) , lift-≅ r (≅-trans eG (l≅ (λ n → ≅-sym (lift-≅ r (≅-reflˡ (proj₂ (hG n))))))) ,
    λ n → proj₁ (hG n) , lift-≅ r (proj₂ (hG n))
  Sh-lift (cΩ ν) {t} r {X} (sν , j , q , f , ej , eX , sp) =
    sν , j , q′ , f′ , ej ,
    lift-≅ r (≅-trans eX (lᵢ≅ (≅ᴵ-refl j) λ x y d →
      subst (λ w → f (into (<→◃ q) x) ≅ lift r (f (into (<→◃ q) w))) (sym (out-into (<→◃ q′) y))
            (≅-sym (lift-≅ r (≅-sym (i-resp (≅-sym eX) (R→≅ (<→◃ q) d))))))) ,
    λ η dη x ex → subst (λ w → Match (fsT t η) (lift r (f (into (<→◃ q) w)))) (sym (out-into (<→◃ q′) x))
                        (proj₁ (sp η dη x ex) , lift-≅ r (proj₂ (sp η dη x ex)))
    where
    q′ = <◃ q r
    f′ : U j (<→◃ q′) → Ordᶜ _
    f′ y = lift r (f (into (<→◃ q) (out (<→◃ q′) y)))
```

**派发 (`dispatch`).** 对任意两个下标 $w$ (节点) 与 $\nu$ (参数的共尾度 $\Omega_{\nu+1}$): `cmpᵀ (ν+1) w` 为 `lt`/`eq` 时得 `lvS sν ≺ᴵ lvS sw` (喂给 `pen⁺`), 为 `gt` 时得 `lvS sw ≺ᴵ lvS sν` 或 `≅ᴵ` (喂给 `fold⁺`). 证据只依赖两个下标本身 (`pen→<`/`gt→≤` 加 `Slt`/`Seq`), 不依赖它们是怎样出现的. 这就是 Closure §9 缺的东西: 墙上 $(\nu,w)=(n-1,5)$ 分别来自 $\omega$ 的不同分支, 但都是标准形下标, `dispatch` 直接比较 (§7 `wall-ev5`/`wall-ev7`). 工程注记: 局部函数 `go` 最初以 `_` 作返回类型, 报 `[CannotGenerateHCompClause] Cannot generate hcomp clause at type _1986 (Sub = @11) … (m = gt)` (`with … | inj₂ refl` 要在元变量类型上生成子句); 改为显式的 `Disp` 即过.

```agda
  Disp : ∀ {w ν} → Sub w → Sub ν → Set
  Disp {w} {ν} sw sν = (Pen (cmpᵀ (sucT ν) w) × (lvS sν ≺ᴵ lvS sw)) ⊎
                       ((cmpᵀ (sucT ν) w ≡ gt) × ((lvS sw ≺ᴵ lvS sν) ⊎ (lvS sw ≅ᴵ lvS sν)))

  dispatch : ∀ {w ν} (sw : Sub w) (sν : Sub ν) → Disp sw sν
  dispatch {w} {ν} sw sν = go (cmpᵀ (sucT ν) w) refl where
    go : ∀ m → cmpᵀ (sucT ν) w ≡ m → Disp sw sν
    go lt em = inj₁ (inj₁ em , Slt sν sw (<→lt (pen→< ν w (inj₁ em))))
    go eq em = inj₁ (inj₂ em , Slt sν sw (<→lt (pen→< ν w (inj₂ em))))
    go gt em with gt→≤ ν w em
    ... | inj₁ p    = inj₂ (em , inj₁ (Slt sw sν (<→lt p)))
    ... | inj₂ refl = inj₂ (em , inj₂ (Seq sw sν (cmpᵀ-refl w)))
```

**叶子 $\Omega_w=\psi_w(0)$** (`leaf`). $w=0$: $\Omega_0=1$, 树 $\cong\mathrm{suc}\,0$ (`S0`). $w$ 后继: 代表元 $W'\cong^\mathsf I\mathrm{suc}(\mathtt{lvS}(w-1))$ 迫使 $W'$ 字面为 `suc W″` (对 `s≅` 匹配), 于是 $\Omega_{W'}$ 字面是 `limᵢ zero (up zero)`, 分支在 $x$ 处是 `up zero x` $\cong x$, 记号侧 $\Omega_w[\eta]=\eta$ (`fsT-c1`) (`leaf1`). $w$ 极限: 同理 $W'$ 字面为 `lim`, $\Omega$ 逐项展开, 第 $n$ 项 $\cong\Omega_{w[n]}$ 的翻译, 记号侧 $\Omega_w[n]=\Omega_{w[n]}$ (`fsn0-eq`) (`leafω`). 最后 `Sh-lift` 搬到 $A$ 层. `c0` 由 `cof-ne`、`cΩ` 由 `SΩ` 排除.

```agda
  leaf1 : ∀ {w ws W′} (s′ : Sub (pred (w ∷ ws))) → suc (lvS s′) ≅ᴵ W′ → cof (w ∷ ws) ≡ c1 →
          Sh (Ω W′) (cΩ (pred (w ∷ ws))) (ψᵗ (w ∷ ws) [] ∷ [])
  leaf1 {w} {ws} s′ (s≅ e′) ce = s′ , _ , zero , up zero , ≅ᴵ-sym e′ , Ω-refl _ ,
    λ η dη x ex → Match-≡ (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) ce η) (dη , upˡ ex)

  leafω : ∀ {w ws W′} {g : ℕ → Ordᴵ} {st : ∀ n → g n ⊑ᴵ g (suc n)} →
          (∀ n → Σ (Sub (fsn (w ∷ ws) n)) λ s′ → g n ≅ᴵ lvS s′) → lim g st ≅ᴵ W′ → cof (w ∷ ws) ≡ cω →
          Sh (Ω W′) cω (ψᵗ (w ∷ ws) [] ∷ [])
  leafω {w} {ws} hg (l≅ h) ce = _ , Ω-refl _ , λ n →
    Match-≡ (E.fsn0-eq w ws n ce)
      (a∷ (aψ (proj₁ (hg n)) a[]) a[] , upˡ (Ω-node (inA (proj₁ (hg n))) (≅ᴵ-trans (≅ᴵ-sym (h n)) (proj₂ (hg n)))))

  leafC : ∀ {w ws} (sw : Sub (w ∷ ws)) (ev : lvS sw ≺ᴵ A) c → cof (w ∷ ws) ≡ c →
          Sh (node ev zero) (cofψ0 (w ∷ ws) c) (ψᵗ (w ∷ ws) [] ∷ [])
  leafC sw ev c0 ce = ⊥-elim (cof-ne _ _ ce)
  leafC sw (via e q) c1 ce with S1 sw ce
  ... | s′ , es = Sh-lift (cΩ _) (<→◃ q) (leaf1 s′ (≅ᴵ-trans (≅ᴵ-sym es) e) ce)
  leafC sw (via e q) cω ce with Sω sw ce
  ... | g , st , eg , hg = Sh-lift cω (<→◃ q) (leafω hg (≅ᴵ-trans (≅ᴵ-sym eg) e) ce)
  leafC sw ev (cΩ μ) ce = ⊥-elim (SΩ sw ce)

  leaf : ∀ {w} (sw : Sub w) (ev : lvS sw ≺ᴵ A) → Sh (node ev zero) (cofP (ψᵗ w [])) (ψᵗ w [] ∷ [])
  leaf {w = []} sw (via e q) =
    zero , lift-≅ (<→◃ q) (≅-trans (Ω-≅ (≅ᴵ-trans (≅ᴵ-sym e) (S0 sw))) (s≅ z≅)) , a[] , z≅
  leaf {w = w ∷ ws} sw ev = leafC sw ev (cof (w ∷ ws)) refl
```

**主项 $\psi_w(b)$, $b\ne0$**, 按 `cof b` 分: 后继 (规则 4; `aRep`/`rep-≅`: 树的 `iter (ψ(b−1) +_) zero n` 与 `replicate n` 的翻译 $\cong$), $\omega$ (规则 5ω), $\Omega_{\nu+1}$ (再按 `cmpᵀ (ν+1) w` 分). 穿透 `penC`: Closure 的 `pen⁺` 给出字面的穿透节点, 新指标层 $j'\cong j\cong$ `lvS sν`, 分支在 $x$ 处经 `tr⁻` 回到 $b$ 的分支, 匹配 $\psi_w(b[\eta])$ (Closure 的 `fsT₊-pen′`).

```agda
  aRep : ∀ {x} → 𝔸ᴾ x → ∀ n → 𝔸 (replicate n x)
  aRep dx zero    = a[]
  aRep dx (suc n) = a∷ dx (aRep dx n)

  rep-≅ : ∀ {x K} {c : Ordᶜ K} (dx : 𝔸ᴾ x) → c ≅ ⟦ dx ⟧ᵖ → ∀ n → iter (c +_) zero n ≅ ⟦ aRep dx n ⟧ᵃ
  rep-≅ dx ec zero    = z≅
  rep-≅ dx ec (suc n) = add-≅ ec (rep-≅ dx ec n)


  penC : ∀ {w y ys ν} (sw : Sub w) (ev : lvS sw ≺ᴵ A) {X : Ordᶜ A} → cof (y ∷ ys) ≡ cΩ ν →
         Sh X (cΩ ν) (y ∷ ys) → Pen (cmpᵀ (sucT ν) w) → Sh (node ev X) (cΩ ν) (ψᵗ w (y ∷ ys) ∷ [])
  penC {w} {y} {ys} {ν} sw (via e q) {X} ce (sν , j , q′ , f , ej , eX , sp) pn
    with pen⁺ {p = q} {σ = λ r → r} {q = q′} {f = f} ej (≺ᴵ-respʳ (Slt sν sw (<→lt (pen→< ν w pn))) e)
  ... | j′ , e₁ , r , eqn = Sh-lift (cΩ ν) (<→◃ q)
    (sν , j′ , r , f′ , ≅ᴵ-trans (≅ᴵ-sym e₁) ej ,
     subst (λ Z → ψ q (λ r → r) X ≅ Z) eqn (ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl _) eX) ,
     λ η dη x ex → subst (λ u → Match (fsT (ψᵗ w (y ∷ ys) ∷ []) η) (ψ q (λ r → r) (f (into (<→◃ q′) (tr⁻ e₁ u)))))
                         (sym (out-into (<→◃ r) x))
                         (Match-≡ (fsT₊-pen′ w (y ∷ ys) ν (cof (y ∷ ys)) ce pn η)
                                  (a∷ (aψ sw (proj₁ (m η dη x ex))) a[] ,
                                   node-≅ (inA sw) {p = q} {σ = λ r → r} (≅ᴵ-sym e) (proj₂ (m η dη x ex)))))
    where
    f′ : U j′ (<→◃ r) → Ordᶜ _
    f′ y = ψ q (λ r → r) (f (into (<→◃ q′) (tr⁻ e₁ (out (<→◃ r) y))))
    m : ∀ η (dη : 𝔸 η) (x : Ordᶜ j′) → x ≅ ⟦ dη ⟧ᵃ → Match (fsT (y ∷ ys) η) (f (into (<→◃ q′) (tr⁻ e₁ x)))
    m η dη x ex = sp η dη (tr⁻ e₁ x) (tr⁻-≅ e₁ ex)
```

折叠 `foldC`: `fold⁺` 给出字面的规则 6 树. 树的 $\gamma$-链逐项匹配记号的 `γT b ν n` (`chainM`: $\gamma_0=\Omega_\nu$ 由 `Ω-node`; $\gamma_{k+1}=\psi_\nu(b[\gamma_k])$ 由 $b$ 的 $\Omega$ 行与 `node-≅`, 两边 $\psi_\nu$ 的目标层经 $j\cong^\mathsf I$ `lvS sν` 相关), 第 $n$ 项匹配 $\psi_w(b[\gamma_n])$ (`fs-gt`). `gt-ev`/`gt-ev′` 把 `gt` 的句法信息经 `Slt`/`Seq` 变成 `fold⁺` 要的 $W'\prec^\mathsf I j$ 或 $W'\cong^\mathsf I j$.

```agda
  chainM : ∀ {b ν j} (sν : Sub ν) {q : j <ᴵ A} {f : U j (<→◃ q) → Ordᶜ A} → j ≅ᴵ lvS sν →
           (∀ η (dη : 𝔸 η) (x : Ordᶜ j) → x ≅ ⟦ dη ⟧ᵃ → Match (fsT b η) (f (into (<→◃ q) x))) →
           ∀ n → Match (γT b ν n) (chainT q f n)
  chainM sν ej sp zero = a∷ (aψ sν a[]) a[] , Ω-node (inA sν) ej
  chainM sν {q} {f} ej sp (suc n) =
    a∷ (aψ sν (proj₁ m)) a[] , node-≅ (inA sν) {p = q} {σ = λ r → r} ej (proj₂ m)
    where
    mγ = chainM sν ej sp n
    m = sp _ (proj₁ mγ) (chainT q f n) (proj₂ mγ)

  gt-ev : ∀ {w ν} (sw : Sub w) (sν : Sub ν) → cmpᵀ (sucT ν) w ≡ gt → (lvS sw ≺ᴵ lvS sν) ⊎ (lvS sw ≅ᴵ lvS sν)
  gt-ev {w} {ν} sw sν em with gt→≤ ν w em
  ... | inj₁ p    = inj₁ (Slt sw sν (<→lt p))
  ... | inj₂ refl = inj₂ (Seq sw sν (cmpᵀ-refl w))

  gt-ev′ : ∀ {M N W′ j} → M ≅ᴵ W′ → j ≅ᴵ N → (M ≺ᴵ N) ⊎ (M ≅ᴵ N) → (W′ ≺ᴵ j) ⊎ (W′ ≅ᴵ j)
  gt-ev′ e ej (inj₁ s) = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym e) s) (≅ᴵ-sym ej))
  gt-ev′ e ej (inj₂ c) = inj₂ (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans c (≅ᴵ-sym ej)))

  foldC : ∀ {w y ys ν} (sw : Sub w) (ev : lvS sw ≺ᴵ A) {X : Ordᶜ A} → cof (y ∷ ys) ≡ cΩ ν →
          Sh X (cΩ ν) (y ∷ ys) → cmpᵀ (sucT ν) w ≡ gt → Sh (node ev X) cω (ψᵗ w (y ∷ ys) ∷ [])
  foldC {w} {y} {ys} {ν} sw (via e q) {X} ce (sν , j , q′ , f , ej , eX , sp) em = Sh-lift cω (<→◃ q)
    ((λ n → ψ q (λ r → r) (f (into (<→◃ q′) (chainT q′ f n)))) ,
     subst (λ Z → ψ q (λ r → r) X ≅ Z) (fold⁺ {p = q} {σ = λ r → r} {q = q′} {f = f} (gt-ev′ e ej (gt-ev sw sν em)))
           (ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl _) eX) ,
     λ n → Match-≡ (fs-gt w y ys ν ce em n)
             (a∷ (aψ sw (proj₁ (m n))) a[] , node-≅ (inA sw) {p = q} {σ = λ r → r} (≅ᴵ-sym e) (proj₂ (m n))))
    where
    m : ∀ n → Match (fsT (y ∷ ys) (γT (y ∷ ys) ν n)) (f (into (<→◃ q′) (chainT q′ f n)))
    m n = sp _ (proj₁ (chainM sν ej sp n)) (chainT q′ f n) (proj₂ (chainM sν ej sp n))
```

`corrΩ` 按比较结果分派, `corrψ` 组装主项的三种情形 (`c0` 由 `cof-ne` 排除).

```agda
  corrΩ : ∀ {w y ys ν} (sw : Sub w) (ev : lvS sw ≺ᴵ A) {X : Ordᶜ A} → cof (y ∷ ys) ≡ cΩ ν →
          Sh X (cΩ ν) (y ∷ ys) → ∀ m → cmpᵀ (sucT ν) w ≡ m → Sh (node ev X) (cofψ₊ w ν m) (ψᵗ w (y ∷ ys) ∷ [])
  corrΩ sw ev ce sh lt em = penC sw ev ce sh (inj₁ em)
  corrΩ sw ev ce sh eq em = penC sw ev ce sh (inj₂ em)
  corrΩ sw ev ce sh gt em = foldC sw ev ce sh em

  corrψ : ∀ {w y ys} (sw : Sub w) (ev : lvS sw ≺ᴵ A) (db : 𝔸 (y ∷ ys)) → ∀ c → cof (y ∷ ys) ≡ c →
          Sh ⟦ db ⟧ᵃ c (y ∷ ys) → Sh (node ev ⟦ db ⟧ᵃ) (cofA w c) (ψᵗ w (y ∷ ys) ∷ [])
  corrψ sw ev db c0 ce sh = ⊥-elim (cof-ne _ _ ce)
  corrψ {w} {y} {ys} sw (via e q) db c1 ce (Y , eY , d′ , e′) = Sh-lift cω (<→◃ q)
    (iter (ψ q (λ r → r) Y +_) zero , ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl _) eY ,
     λ n → Match-≡ (fs-rep w y ys ce n)
             (aRep (aψ sw d′) n , rep-≅ (aψ sw d′) (node-≅ (inA sw) {p = q} {σ = λ r → r} (≅ᴵ-sym e) e′) n))
  corrψ {w} {y} {ys} sw (via e q) db cω ce (G , eG , hG) = Sh-lift cω (<→◃ q)
    ((λ n → ψ q (λ r → r) (G n)) , ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl _) eG ,
     λ n → Match-≡ (fs-ω w y ys ce n)
             (a∷ (aψ sw (proj₁ (hG n))) a[] , node-≅ (inA sw) {p = q} {σ = λ r → r} (≅ᴵ-sym e) (proj₂ (hG n))))
  corrψ {w} sw ev db (cΩ ν) ce sh = corrΩ sw ev ce sh (cmpᵀ (sucT ν) w) refl
```

**和** (`sum`, 规则 1): 树的 `a + suc b`、`a + lim f`、`a + limᵢ q f` 与句法的 `pred`/`fsn`/`fsT` 同步, 都只动末项; 规则 4 产生的 $\psi_w(b)\cdot n$ (Closure 的出口 `exit-0`) 由它处理. **形状定理** `corr`: 对每个 `𝔸` 推导, 无前提. 单项和 $x+0$ 的翻译定义性地就是 $x$ 的 (`add a σ zero = a`).

```agda
  sum : ∀ {x y ys} (dx : 𝔸ᴾ x) (dys : 𝔸 (y ∷ ys)) → ∀ c → cof (y ∷ ys) ≡ c →
        Sh ⟦ dys ⟧ᵃ c (y ∷ ys) → Sh (⟦ dx ⟧ᵖ + ⟦ dys ⟧ᵃ) c (x ∷ y ∷ ys)
  sum dx dys c0 ce _ = ⊥-elim (cof-ne _ _ ce)
  sum dx dys c1 ce (Y , eY , d′ , e′) =
    ⟦ dx ⟧ᵖ + Y , add-≅ (⟦⟧ᴾ-refl dx) eY , a∷ dx d′ , add-≅ (⟦⟧ᴾ-refl dx) e′
  sum dx dys cω ce (G , eG , hG) =
    (λ n → ⟦ dx ⟧ᵖ + G n) , add-≅ (⟦⟧ᴾ-refl dx) eG ,
    λ n → a∷ dx (proj₁ (hG n)) , add-≅ (⟦⟧ᴾ-refl dx) (proj₂ (hG n))
  sum {x} {y} {ys} dx dys (cΩ ν) ce (sν , j , q , f , ej , eX , sp) =
    sν , j , q , (λ z → ⟦ dx ⟧ᵖ + f (coe (<→◃ q) (<→◃ q) z)) , ej , add-≅ (⟦⟧ᴾ-refl dx) eX ,
    λ η dη z ez → subst (λ w → Match (x ∷ fsT (y ∷ ys) η) (⟦ dx ⟧ᵖ + f (into (<→◃ q) w))) (sym (out-into (<→◃ q) z))
                        (a∷ dx (proj₁ (sp η dη z ez)) , add-≅ (⟦⟧ᴾ-refl dx) (proj₂ (sp η dη z ez)))


  corr  : ∀ {t} (d : 𝔸 t) → Sh ⟦ d ⟧ᵃ (cof t) t
  corrᴾ : ∀ {x} (d : 𝔸ᴾ x) → Sh ⟦ d ⟧ᵖ (cofP x) (x ∷ [])
  corr a[] = z≅
  corr (a∷ dx a[]) = corrᴾ dx
  corr (a∷ dx (a∷ {x = y} {xs = ys} dy dys)) = sum dx (a∷ dy dys) (cof (y ∷ ys)) refl (corr (a∷ dy dys))
  corrᴾ (aψ {a = []} sw a[]) = leaf sw (inA sw)
  corrᴾ (aψ {a = y ∷ ys} sw db) = corrψ sw (inA sw) db (cof (y ∷ ys)) refl (corr db)
```

**遗传标签** (`lab`): 与 Correspond 的 `lab` 同一个对树的递归, 形状来自 `corr`; $\Omega$ 行与第 0 层的树不相容 (`noΩ0`). 于是**每个** `𝔸` 项 $t$ 与第 0 层的每个 $X\cong\llbracket t\rrbracket$ 都有 `Lab X t`.

```agda
  lab   : ∀ (X : Ordᶜ zero) {t} (d : 𝔸 t) → X ≅ ⟦ d ⟧ᵃ → Lab X t
  labSh : ∀ (X : Ordᶜ zero) {t} (d : 𝔸 t) c → cof t ≡ c → Sh ⟦ d ⟧ᵃ c t → X ≅ ⟦ d ⟧ᵃ → Lab X t
  lab X {t} d e = labSh X d (cof t) refl (corr d) e
  labSh X d c0 ce sh e = l0 ce (≅-trans (≅-trans e sh) z≅)
  labSh zero    d c1 ce (Y , eY , _) e = ⊥-elim (zs (≅-trans e eY))
  labSh (lim F) d c1 ce (Y , eY , _) e = ⊥-elim (ls (≅-trans e eY))
  labSh (suc X) d c1 ce (Y , eY , d′ , e′) e = l1 ce (s≅ (≅-reflˡ h)) (lab X d′ (≅-trans h e′))
    where h = s-inv (≅-trans e eY)
  labSh zero    d cω ce (G , eG , _) e = ⊥-elim (zl (≅-trans e eG))
  labSh (suc X) d cω ce (G , eG , _) e = ⊥-elim (sl (≅-trans e eG))
  labSh (lim F) d cω ce (G , eG , hG) e =
    lω ce (l≅ (λ n → ≅-reflˡ (h n))) (λ n → lab (F n) (proj₁ (hG n)) (≅-trans (h n) (proj₂ (hG n))))
    where h = l-inv (≅-trans e eG)
  labSh X d (cΩ ν) ce (_ , _ , _ , _ , _ , eX , _) e = ⊥-elim (noΩ0 X (≅-trans e eX))
  labSh (limᵢ () f) d c1 ce sh e
  labSh (up () x)   d c1 ce sh e
  labSh (limᵢ () f) d cω ce sh e
  labSh (up () x)   d cω ce sh e
```

闭包: `𝔸` 对极限处的 `fsn` 与后继处的 `pred` 封闭 (形状定理的投影).

```agda
  𝔸-fsn : ∀ {t} → 𝔸 t → cof t ≡ cω → ∀ n → 𝔸 (fsn t n)
  𝔸-fsn {t} d e n = proj₁ (proj₂ (proj₂ (subst (λ c → Sh ⟦ d ⟧ᵃ c t) e (corr d))) n)

  𝔸-pred : ∀ {t} → 𝔸 t → cof t ≡ c1 → 𝔸 (pred t)
  𝔸-pred {t} d e = proj₁ (proj₂ (proj₂ (subst (λ c → Sh ⟦ d ⟧ᵃ c t) e (corr d))))
```



## §6 实例化: $\varepsilon_0$ 片段的标准形

环境层 $A_0=E_0+1$, $E_0$ 是 $\varepsilon_0$ 的层号 (`lvN nε`; 定义性地就是 Correspond 的 `lvl (gγ 1)`, 且 $\cong^\mathsf I$ NoCumsum 的 `L 1`, 见下面的 `L₁≅E₀`). 七条接口: `inA₀` (`N0` 下标 $<\varepsilon_0$, 由 `OC-lt`; $\varepsilon_0$ 自己由 `zero : E₀ <ᴵ suc E₀`); `S0₀` (`lvN (n0 n[])` 定义性地是 `zero`); `S1₀`/`Sω₀` (Closure 的 `ΩshE1`/`ΩshEω`, 经 `𝔼-≡` 对齐到 `NF-pred`/`NF-fsn` 的推导; 极限的 `lim g st` 就是 `toLevel (lim F) hF` 定义性展开的字面形状); `SΩ₀` (`noΩ`); `Slt`/`Seq` 是 §4 的 `OC-lt`/`OC-eq`.

```agda
E₀ A₀ : Ordᴵ
E₀ = lvN nε
A₀ = suc E₀

inA₀ : ∀ {w} (s : NF w) → lvN s ≺ᴵ A₀
inA₀ (n0 x) = ≺-suc (OC-lt (n0 x) nε (<→lt (N0<ε x)))
inA₀ nε     = via (≅ᴵ-refl E₀) zero

S0₀ : (s : NF []) → lvN s ≅ᴵ zero
S0₀ (n0 n[]) = z≅

S1₀ : ∀ {w} (s : NF w) → cof w ≡ c1 → Σ (NF (pred w)) λ s′ → lvN s ≅ᴵ suc (lvN s′)
S1₀ {w = []} s ()
S1₀ {w = x ∷ xs} s e with ΩshE1 (toE s) e
... | g′ , eL = NF-pred s e ,
  ≅ᴵ-trans eL (s≅ (toLevel-≅ (cert (emb g′)) (cert (emb (toE (NF-pred s e)))) (E-≅ g′ (toE (NF-pred s e)))))

Sω₀ : ∀ {w} (s : NF w) → cof w ≡ cω → Σ (ℕ → Ordᴵ) λ g → Σ (∀ n → g n ⊑ᴵ g (suc n)) λ st →
      (lvN s ≅ᴵ lim g st) × (∀ n → Σ (NF (fsn w n)) λ s′ → g n ≅ᴵ lvN s′)
Sω₀ {w = []} s ()
Sω₀ {w = x ∷ xs} s e with ΩshEω (toE s) e
... | F , hF , eL , hM =
  (λ n → toLevel (F n) (hl₁ hF n)) , (λ n → toLevel-⊑ (hl₁ hF n) (hl₁ hF (suc n)) (hl₂ hF n)) , eL ,
  λ n → NF-fsn s n , toLevel-≅ (hl₁ hF n) (cert (emb (toE (NF-fsn s n))))
                                (≅-trans (proj₂ (hM n)) (E-≅ (proj₁ (hM n)) (toE (NF-fsn s n))))

SΩ₀ : ∀ {w μ} → NF w → cof w ≡ cΩ μ → ⊥
SΩ₀ s e = noΩ (toE s) e

module G = Generic NF lvN A₀ inA₀ S0₀ S1₀ Sω₀ SΩ₀ OC-lt OC-eq

L₁≅E₀ : N.L 1 ≅ᴵ E₀
L₁≅E₀ = toLevel-≅ (N.cert 1) (cert (gγ 1)) (diag-≅ 1)
```

`module G` 之后, `G.corr`/`G.lab` 对一切以 `NF` 项为 $\psi$-下标的 EBO 项可用. `L₁≅E₀` 说环境层的核心 $E_0$ 就是 NoCumsum 对角线第一个层号 (模 $\cong^\mathsf I$), 不是另造的层号.

## §7 检验二: $\gamma_2=\psi_0(\Omega_{\varepsilon_0})$ 的遗传标签

`d₂` 是 $\gamma^\mathsf E_2$ 的 `𝔸` 推导 (下标 $0$ 与 $\varepsilon_0$). `top`: 目标层字面为 `zero` 的节点与 `ψ⁰` 一致 (对 `via z≅ q` 匹配后用 Level 的 `ψ⁰≅ψ`). `agree₂`: Correspond 的翻译 $\psi^0(\Omega_{\mathtt{lvl}\,\varepsilon_0})$ 与本文的翻译 $\cong$. 与 `diag-≅ 2` 合成, `lab` 给出标签.

```agda
s₀ : NF []
s₀ = n0 n[]

d₂ : G.𝔸 (γᴱ 2)
d₂ = G.a∷ (G.aψ s₀ (G.a∷ (G.aψ nε G.a[]) G.a[])) G.a[]

top : ∀ (ev : zero ≺ᴵ A₀) {K} {a : Ordᶜ K} {b : Ordᶜ A₀} → a ≅ b → ψ⁰ a ≅ G.node ev b
top (via z≅ q) d = ≅-sym (lift-≅ (<→◃ q) (≅-sym (ψ⁰≅ψ {p = q} {σ = λ r → r} d)))

agree₂ : ⟦ gγ 2 ⟧ ≅ G.⟦ d₂ ⟧ᵃ
agree₂ = top (inA₀ s₀) (G.Ω-node (inA₀ nε) (≅ᴵ-refl _))

γ₂-label : Lab (N.γ 2) (γᴱ 2)
γ₂-label = G.lab (N.γ 2) d₂ (≅-trans (diag-≅ 2) agree₂)
```

**定理 `γ₂-label : Lab (N.γ 2) (γᴱ 2)`.** 由 Correspond §8, 树 `N.γ 2` 的 FGH 满足 EBO 沿 $\psi_0(\Omega_{\varepsilon_0})$ 的**全部**递归方程 (`FGH-Lab0`/`FGH-Lab1`/`FGH-Labω` 一路读出).

**整个基本列闭包.** `Reach` 是 $\gamma^\mathsf E_2$ 在 "极限取 `fsn`, 后继取 `pred`" 下的闭包 (FGH 的递归实际访问的项). `reach-𝔸`: 闭包落在 `𝔸` 里 (下标全是 `NF`); `reach-lab`: 每个闭包项都有遗传标签 (由 `γ₂-label` 经 Correspond 的 `FGH-Labω`/`FGH-Lab1` 反演). Closure 的墙项 $P$ 在闭包里: `walkR` 沿 Closure 的 `base` 路径走 19 步, 每步的共尾度 `cω` 由 `refl` 计算核实, 再经 Closure 的 `wall-path` 改写. 于是 `wall-label`: 对每个 $n$, $P[n]$ 有标签; Closure 卡住的 $n=5$ (穿透) 与 $n=6$ (折叠) 都在其中.

```agda
data Reach : T → Set where
  r₀ : Reach (γᴱ 2)
  rω : ∀ {t} → Reach t → cof t ≡ cω → ∀ n → Reach (fsn t n)
  r₁ : ∀ {t} → Reach t → cof t ≡ c1 → Reach (pred t)

reach-𝔸 : ∀ {t} → Reach t → G.𝔸 t
reach-𝔸 r₀         = d₂
reach-𝔸 (rω r e n) = G.𝔸-fsn (reach-𝔸 r) e n
reach-𝔸 (r₁ r e)   = G.𝔸-pred (reach-𝔸 r) e

reach-lab : ∀ {t} → Reach t → Σ (Ordᶜ zero) λ X → Lab X t
reach-lab r₀ = N.γ 2 , γ₂-label
reach-lab (rω r e n) with FGH-Labω (proj₂ (reach-lab r)) e
... | F , h , _ = F n , h n
reach-lab (r₁ r e) with FGH-Lab1 (proj₂ (reach-lab r)) e
... | Y , l , _ = Y , l

Lims : T → List ℕ → Set
Lims t []       = ⊤
Lims t (n ∷ ns) = (cof t ≡ cω) × Lims (fsn t n) ns

walkR : ∀ {t} → Reach t → ∀ ns → Lims t ns → Reach (walk t ns)
walkR r []       _       = r
walkR r (n ∷ ns) (e , l) = walkR (rω r e n) ns l

wall-reach : Reach (Pw (Ωt ωᵗ))
wall-reach = subst Reach wall-path (walkR r₀ base
  (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl ,
   refl , refl , refl , refl , refl , refl , refl , refl , refl , tt))

wall-label : ∀ n → Σ (Ordᶜ zero) λ X → Lab X (fsn (Pw (Ωt ωᵗ)) n)
wall-label n = reach-lab (rω wall-reach refl n)
```

墙上的具体证据: 节点 $\psi_5$, 参数共尾度 $\Omega_n$ ($\nu=n-1$). `wall-disp ν` 是 `dispatch` 对 $(w,\nu)=(5,\nu)$ 的实例 ($P[\nu+1]$ 用的就是它) (`snat` 把自然数的项标为标准形, `N0-nat`). $n=5$: `cmpᵀ 5 5 ≡ eq`, 穿透, 证据 `wall-ev5 : lvl 4 ≺ᴵ lvl 5`; $n=7$: `cmpᵀ 7 5 ≡ gt`, 折叠, 证据 `wall-ev7 : lvl 5 ≺ᴵ lvl 6`; $n=6$ 是 $\nu=w$, 走 `Seq`. 它们都由 `OC-lt`/`OC-eq` 对**下标本身**现场得到, 不看下标从 $\omega$ 的哪个分支来.

```agda
N0-nat : ∀ k → N0 (natT k)
N0-nat zero          = n[]
N0-nat (suc zero)    = n∷ n[] n[] tt
N0-nat (suc (suc k)) = n∷ n[] (N0-nat (suc k)) (inj₂ refl)

snat : ∀ k → NF (natT k)
snat k = n0 (N0-nat k)

wall-disp : ∀ ν → G.Disp (snat 5) (snat ν)
wall-disp ν = G.dispatch (snat 5) (snat ν)

wall-ev5 : lvN (snat 4) ≺ᴵ lvN (snat 5)
wall-ev5 = OC-lt (snat 4) (snat 5) refl

wall-ev7 : lvN (snat 5) ≺ᴵ lvN (snat 6)
wall-ev7 = OC-lt (snat 5) (snat 6) refl

_ : cmpᵀ (sucT (natT 4)) (natT 5) ≡ eq
_ = refl
_ : cmpᵀ (sucT (natT 6)) (natT 5) ≡ gt
_ = refl
```



## §8 对比表

| | Closure (路线 B) | 本文 |
|---|---|---|
| 证据 | 随推导传递: 每层 $\trianglelefteq^\mathsf I$/$\prec^\mathsf I$ + 不变量 `Inv` | 由下标现场计算: `dispatch` = 离散性 + 序的对应 |
| 证据的来源 | 基本列历史 (`self n`, `pred⊴`, `suc⊴→≺`) | 对树递归的 `oc`: 后继步用离散性, 极限步用共尾性 `cofin` |
| 下标 | $\mathbb E$, 不要求标准形 | `NF` = Cantor 标准形 $\cup\{\varepsilon_0\}$; 非标准反例 `nf-fail₁₂₃` |
| 翻译 | 节点形状依赖相对位置 (`nodeᵇ`/`nodeᵃ`) | 参数统一放在公共上界层 $A$, 节点统一为 `lift ∘ ψ q id` |
| 类 | 脊 $\psi_0(\psi_{w_1}(\cdots\psi_{w_k}(\Omega_v)))$, 叶子非零 | 一切下标为 `NF` 的项 `𝔸` (和、嵌套、非标准参数均可) |
| 规则 4 的和 | 出口 (`exit-0`) | 类内 (`sum`) |
| 派发 | 穿透 `pen⁺` + 最外层 $\psi_0$ 的链 | 任意层: 穿透 `pen⁺` 与折叠 `fold⁺`, 都字面 |
| 墙 $P[n]$ | 卡在 $(n-1,5)$ | `wall-label`, 证据 `wall-ev5`/`wall-ev7` |
| 遗传标签 | 无新的 | **`γ₂-label`**, 闭包 `reach-lab` |
| Bachmann 性质 | 设想为所需的新不变量 | 推论 (`bach-syn`/`bach`), 证明链不用它 |

## §9 结论与边界

**字面成立 (`refl` 或定义性):** `fold⁺` 的折叠节点等式 (给定比较证据), 与 Closure `pen⁺` 的穿透节点等式; `cmpᵀ (1+ω) ω ≡ lt`, `cmpᵀ 5 5 ≡ eq`, `cmpᵀ 7 5 ≡ gt`; 墙路径 19 步的共尾度; `S0₀` (`lvN` 在 $0$ 处定义性地是 `zero`); 翻译的定义性展开 (`⟦ a∷ x a[] ⟧ᵃ` 即 `⟦ x ⟧ᵖ`, $\psi_w(0)$ 即 $\Omega_{W'}$, $\llbracket 1+\omega\rrbracket=\lim_n(1+n)$); `𝔼-≡` (推导字面唯一). 记号侧的规则化简 (`fs-gt`, `fsε`, 以及 `fs-rep`/`fs-ω`/`fsT₊-pen′`/`fsn0-eq` 的使用) 是命题等式, 只用 J-对齐. §1–§3 的句法引理都是 `<ᵀ` 的构造性证明.

**模 $\cong$ 成立 (定理):**

1. 序的对应 (`NF` 下标): `OC< : v <ᵀ u → T⟦ sv ⟧ ≺ T⟦ su ⟧`; `OC-lt`/`OC-eq`/`OC-gt` (层号的 $\prec^\mathsf I$/$\cong^\mathsf I$).
2. Bachmann 性质: 句法 `bach-syn` (`NF` 极限 $u$, $m<m'\Rightarrow u[m]<^\mathsf T u[m']$), 树 `bach`, `fs≺`, `pred≺`; 共尾性 `cofin`; 封闭性 `NF-pred`/`NF-fsn`.
3. 通用形状定理 `Generic.corr : ∀ (d : 𝔸 t) → Sh ⟦ d ⟧ᵃ (cof t) t` 与 `Generic.lab`, 对满足七条接口的任意下标系统; 派发一致 `dispatch`/`penC`/`foldC`/`chainM`.
4. **`γ₂-label : Lab (N.γ 2) (γᴱ 2)`**; 闭包 `reach-𝔸`/`reach-lab`; 墙 `wall-label`.

**否定 (已编译):** `nf-fail₁`/`nf-fail₂`/`nf-fail₃` (非标准项上序的对应为假), `1+ω∉NF`, `γᴱ₂∉NF`.

**关于标签, 现在证了什么.** 新树族上 $\gamma_1=\varepsilon_0$ (Correspond `ε₀-label`) 与 $\gamma_2=\psi_0(\Omega_{\varepsilon_0})$ (`γ₂-label`) 的遗传标签是定理: 树的 FGH 满足 EBO 沿它们整个基本列闭包的递归方程. 由 `diag-label`, BTBO $=\psi_0(\Omega_\Omega)$ 等价于一切 $k$ 的 `Lab (N.γ (suc k)) (γᴱ (suc k))`; $k\ge2$ ($\gamma_3=\psi_0(\Omega_{\gamma_2})$ 起) **未证**, 所以 **BTBO $=\psi_0(\Omega_\Omega)$ 仍是估计**.

**下一步缺什么 (精确).** 对 $\gamma_{k+2}$ 用 `Generic`, 下标系统要取 "$\gamma^\mathsf E_{k+1}$ 闭包里的标准形项" (下标本身是含 $\psi_u$, $u\ne0$ 的 Buchholz 型项), 公共上界取 $\gamma_{k+1}$ 的层号加一. 逐条看:

- 对一般项**已成立**: 离散性 `<sucT`, `pen→<`, `gt→≤`, `gt→<`, `<ᵀ-irrefl`/`<ᵀ-asym`, `Hd≤-desc`, `rep<`, `fs<ᵀ` 与 EBO 的 `pred-<` (句法递降); 树侧 `fold⁺`/`chainT`/`clash`/`noΩ0` (任意层号); 记号侧 `fs-gt` (任意项); 以及整个 `Generic` 模块 (主项任意, 只对下标系统有要求). `S0`/`S1`/`Sω`/`SΩ` 对上一阶段的 `𝔸` 由其 `corr` 给出 (层号经 `toLevel`, 与 §6 用 `ΩshE1`/`ΩshEω` 同法), 不需要新数学.
- **未做**: 那个下标系统上的标准形谓词 (Buchholz 的 $a\in C_u(a)$ 条件加降序), `pred`/`fsn` 保持它, 以及**共尾性** (`cofin` 的推广). 有了这三条, `oc` 的树递归原样给出 `Slt`/`Seq` (它只用离散性、共尾性与形状定理), `inA` 随之. 这正是 EBO §9 未做的标准形理论的核心; 本文只在 Cantor 范式上做了它.

**其他边界.**

- 公共上界层 $A$ 是交替总方向不变量 ("被比较的下标有公共上界") 的直接实现; 本文所有比较都在 $A_0=\mathtt{lvl}(\varepsilon_0)+1$ 之下.
- 翻译依赖推导与证据, 唯一性只模 $\cong$ (`node-≅`, `T-≡`); $\mathbb E$ 的推导字面唯一 (`𝔼-≡`).
- 不改 `src/`、`archive/` 与已有的 Align 文件 (README 的文件列表也未改动).
