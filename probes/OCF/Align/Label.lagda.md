# 对角线上的遗传标签: BTBO $=\psi_0(\Omega_\Omega)$

> 接 [Standard](Standard.lagda.md) (EBO 可数下标的标准形、闭包、共尾性) 与 [Bachmann](Bachmann.lagda.md) §5 的通用形状定理 `Generic`. Bachmann 用 Cantor 标准形实例化 `Generic` 得到 $\gamma_2$ 的遗传标签, 并说对 $\gamma_{k+2}$ 只缺标准形理论; Standard 补上了它. 本文是阶段 3: 沿对角线逐阶段实例化, 每一阶段的下标系统由上一阶段的 `Generic` 生成.
>
> 结论先说:
>
> 1. **下标系统作为值 (§1).** `Generic` 的七个参数 (加一个 `s0 : Sub []`) 打包成记录 `System`; `module GS (S : System) = Generic …` 原样应用, **`Generic` 不重新参数化, 不复制**.
> 2. **下一阶段 (§3–§4).** `Next S β`: 新的下标是 "有 `GS.𝔸 S` 推导、是标准形、且 $\le\beta$" 的项 (`Sub′`). 它们都可数 (`Ctbl-≤`), 于是有第 0 层的树 `T⟦ d ⟧` (每个加项 $\psi_0(a)$ 译为 `ψ⁰ ⟦ a ⟧ᵃ`), 证书由 Uniform 的 `Good` 对推导归纳 (`goodT`, 新增 `Good-lift`), 层号 `lvS′ = toLevel T⟦ d ⟧ (certT d)`. 七条接口全部证出: 序的对应 `Slt′`/`Seq′` 由 Bachmann `oc` 的同一个树递归 (`oc`), 形状读自上一阶段的 `corr`, 极限步用 Standard 的 `cofin`, 后继步用离散性 `<sucT`, 闭包用 `NF-pred`/`NF-fsn`/`Ctbl-fsn`; `S1′`/`Sω′` 从 `corr` 的形状经 `toLevel-≅` 读出; `SΩ′` 是 `Ctbl-cof`. **公共上界** $A'=\mathrm{suc}(\mathtt{lvS}'\,\beta)$, `inA′` 由 `Slt′`/`Seq′` 与 $w\le\beta$.
> 3. **阶段 (§5).** `prev 0 = triv` (下标只有 $0$), `St k = Next (prev k) (γᴱ k) (dB k)`, `prev (k+1) = St k`; $\gamma^\mathsf E_{k+1}=\psi_0(\Omega_{\gamma^\mathsf E_k})$ 的推导 `dγ` 用到两个下标 $0$ 与 $\gamma^\mathsf E_k$, 后者正是阶段 $k$ 的 $\beta$. 第 $k$ 阶段的公共上界 `A-L : System.A (St k) ≅ᴵ suc (N.L k)`: 就是 NoCumsum 对角线第 $k$ 个层号加一 (Bachmann 的 $A_0=\mathrm{suc}(E_0)$ 是 $k=1$ 的情形).
> 4. **标签 (§6).** **`γ-label : ∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))` 与 `BTBO-label : Lab N.BTBOᴵ (E.EBOψ 2)` 是定理.** 依 [probes/README](../../README.md) 的认证准则, NoCumsum 的树 `BTBOᴵ` 的 FGH 满足 EBO 沿 $\psi_0(\Omega_\Omega)$ 的全部递归方程 (任意深度: `Lab` 是归纳的, 每层由 `FGH-Lab0/1/ω` 读出 ℕ 上的字面等式), **BTBO $=\psi_0(\Omega_\Omega)$ 从估计变为定理** (对 probes 的无 cumsum 树族 `N.BTBOᴵ`; 对 src 的 BTBO 见 §8).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块 (加 Standard), 不改任何已有文件, 没有复制私有定义.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Label where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import OCF.Align.Level
open import OCF.Align.Uniform using (Good; Good-add; Good-ψ; Good-ψ⁰; Good→HS; gz; gu; s-inv; l-inv)
open import OCF.Align.Correspond using (⟦_⟧; lvl; cert; gγ; diag-≅; Lab; diag-label; γᴱ; cof-ne;
  FGH-Labω; FGH-Lab1)
open import OCF.Align.Closure using (cmpᵀ-refl; lt→<; eq→≡; <→lt)
open import OCF.Align.Bachmann using (module Generic; zs; ls; zl; sl; <sucT; fs<ᵀ)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; pred; fsn; _<ᵀ_; []<)
       renaming (ψ to ψᵗ)
open import OCF.Align.Standard using (NF; n[]; Ctbl; c[]; c∷; _≤ᵀ_; <≤-trans; cofin; NF-pred; NF-fsn;
  Ctbl-pred; Ctbl-fsn; Ctbl-≤; Ctbl-cof; diag-NF; diag-Ctbl; []≤; Desc; d₀; dω; d₁)
```

## §1 下标系统

`System` 的前十个字段与 `Generic` 的参数逐一相同 (类型逐字照抄), 外加 `s0 : Sub []` (每个阶段都要 $\psi_0$). `GS S` 是 `Generic` 在 `S` 上的应用: 类 `GS.𝔸 S`、翻译 `GS.⟦_⟧ᵃ S`、形状定理 `GS.corr S`、标签 `GS.lab S` 都直接来自 Bachmann. 工程注记: 模块应用的构造子把 `S` 当隐式参数, 第一次写 `GS.a∷ S …` 报

    [UnequalTerms] System !=< (Generic.𝔸ᴾ (System.Sub _S_986) (System.lvS _S_986) …)
    when checking that the expression S has type Generic.𝔸ᴾ …

改写成 `GS.a∷ {S = S} …` 即过 (§5 的 `dγ`).

```agda
record System : Set₁ where
  field
    Sub : T → Set
    lvS : ∀ {w} → Sub w → Ordᴵ
    A   : Ordᴵ
    inA : ∀ {w} (s : Sub w) → lvS s ≺ᴵ A
    S0  : (s : Sub []) → lvS s ≅ᴵ zero
    S1  : ∀ {w} (s : Sub w) → cof w ≡ c1 → Σ (Sub (pred w)) λ s′ → lvS s ≅ᴵ suc (lvS s′)
    Sω  : ∀ {w} (s : Sub w) → cof w ≡ cω → Σ (ℕ → Ordᴵ) λ g → Σ (∀ n → g n ⊑ᴵ g (suc n)) λ st →
          (lvS s ≅ᴵ lim g st) × (∀ n → Σ (Sub (fsn w n)) λ s′ → g n ≅ᴵ lvS s′)
    SΩ  : ∀ {w μ} → Sub w → cof w ≡ cΩ μ → ⊥
    Slt : ∀ {v u} (sv : Sub v) (su : Sub u) → cmpᵀ v u ≡ lt → lvS sv ≺ᴵ lvS su
    Seq : ∀ {v u} (sv : Sub v) (su : Sub u) → cmpᵀ v u ≡ eq → lvS sv ≅ᴵ lvS su
    s0  : Sub []

module GS (S : System) = Generic (System.Sub S) (System.lvS S) (System.A S) (System.inA S) (System.S0 S)
  (System.S1 S) (System.Sω S) (System.SΩ S) (System.Slt S) (System.Seq S)
```

## §2 树侧的三个小引理

`Good-lift`: 提升保持 Uniform 的遗传好性 (对 $\triangleleft$ 的证明递归, 每层一个 `gu`). `top″`: 目标层 $\cong^\mathsf I 0$ 的节点就是 `ψ⁰` (Bachmann `top` 的一般形: 先对 $W\cong^\mathsf I0$ 匹配 `z≅` 迫使 $W$ 字面为 `zero`, 再用 Level 的 `ψ⁰≅ψ`). `asLim`: 第 0 层的树若 $\cong$ 某个 `lim G`, 它字面就是 `lim F` 且 $F\,n\cong G\,n$.

```agda
Good-lift : ∀ {k ℓ} (r : k ◃ ℓ) {x : Ordᶜ k} → Good x → Good (lift r x)
Good-lift zero      g = gu g
Good-lift (suc r)   g = gu (Good-lift r g)
Good-lift (self n)  g = gu g
Good-lift (lim n r) g = gu (Good-lift r g)

top″ : ∀ {W A K} (q : W <ᴵ A) → W ≅ᴵ zero → {a : Ordᶜ K} {b : Ordᶜ A} → a ≅ b → ψ⁰ a ≅ lift (<→◃ q) (ψ q (λ r → r) b)
top″ q z≅ d = ≅-sym (lift-≅ (<→◃ q) (≅-sym (ψ⁰≅ψ {p = q} {σ = λ r → r} d)))

asLim : ∀ (X : Ordᶜ zero) {K} {G : ℕ → Ordᶜ K} → X ≅ lim G →
        Σ (ℕ → Ordᶜ zero) λ F → (X ≡ lim F) × (∀ n → F n ≅ G n)
asLim (lim F) e = F , refl , l-inv e
asLim zero ()
asLim (suc X) ()
asLim (limᵢ () f) e
asLim (up () x) e
```

## §3 下标的第 0 层树

`Tree S`: 对 `GS.𝔸 S` 的推导, `goodA` 给翻译 `⟦ d ⟧ᵃ` (在公共上界层 $A$) 的遗传好性 (`Good-add`/`Good-ψ`/`Good-lift`, 与 Correspond 的 `good` 同法); `T⟦ d ⟧` 是第 0 层的树: 每个加项 $\psi_w(a)$ 译成 `ψ⁰ ⟦ a ⟧ᵃ` (忽略 $w$; 只对可数的项使用, 那时 $w=0$), 证书 `certT` 来自 `Good→HS`. `T≅`: 可数的项上 `T⟦ d ⟧ ≅ ⟦ d ⟧ᵃ` (每项由 `top‴`, 用 `S0` 把下标 $0$ 的层号化成字面的 `zero`). `uniq`: 同一个项的两个推导的翻译 $\cong$ (每个节点由 `node-≅`, 两个下标证明的层号由 `Seq` 与 `cmpᵀ-refl` 相关); Bachmann 那里推导字面唯一 (`𝔼-≡`), 这里不唯一, 只模 $\cong$.

```agda
module Tree (S : System) where
  open System S
  open GS S

  Good-node : ∀ {M} (ev : M ≺ᴵ A) {x : Ordᶜ A} → Good x → x ≅ x → Good (node ev x)
  Good-node (via e q) g r = Good-lift (<→◃ q) (Good-ψ g r)

  goodA  : ∀ {t} (d : 𝔸 t) → Good ⟦ d ⟧ᵃ
  goodAᴾ : ∀ {x} (d : 𝔸ᴾ x) → Good ⟦ d ⟧ᵖ
  goodA a[]       = gz
  goodA (a∷ x xs) = Good-add (goodAᴾ x) (⟦⟧ᴾ-refl x) (goodA xs)
  goodAᴾ (aψ s d) = Good-node (inA s) (goodA d) (⟦⟧-refl d)

  T⟦_⟧ : ∀ {t} → 𝔸 t → Ordᶜ zero
  T⟦ a[] ⟧            = zero
  T⟦ a∷ (aψ s d) xs ⟧ = ψ⁰ ⟦ d ⟧ᵃ + T⟦ xs ⟧

  goodT : ∀ {t} (d : 𝔸 t) → Good T⟦ d ⟧
  goodT a[]              = gz
  goodT (a∷ (aψ s d) xs) = Good-add (Good-ψ⁰ (goodA d) (⟦⟧-refl d)) (≅-refl⁰ _) (goodT xs)

  certT : ∀ {t} (d : 𝔸 t) → HS T⟦ d ⟧
  certT d = Good→HS (goodT d)

  top‴ : ∀ {M} (ev : M ≺ᴵ A) → M ≅ᴵ zero → ∀ {K} {a : Ordᶜ K} {b : Ordᶜ A} → a ≅ b → ψ⁰ a ≅ node ev b
  top‴ (via e q) h d = top″ q (≅ᴵ-trans (≅ᴵ-sym e) h) d

  T≅ : ∀ {t} → Ctbl t → (d : 𝔸 t) → T⟦ d ⟧ ≅ ⟦ d ⟧ᵃ
  T≅ c[] a[] = z≅
  T≅ (c∷ c) (a∷ (aψ s d) xs) = add-≅ (top‴ (inA s) (S0 s) (⟦⟧-refl d)) (T≅ c xs)

  nodeU : ∀ {M M′} (ev : M ≺ᴵ A) (ev′ : M′ ≺ᴵ A) → M ≅ᴵ M′ → ∀ {X Y : Ordᶜ A} → X ≅ Y → node ev X ≅ node ev′ Y
  nodeU (via e q) ev′ m d = lift-≅ (<→◃ q) (node-≅ ev′ {p = q} {σ = λ r → r} (≅ᴵ-trans (≅ᴵ-sym e) m) d)

  uniq  : ∀ {t} (d d′ : 𝔸 t) → ⟦ d ⟧ᵃ ≅ ⟦ d′ ⟧ᵃ
  uniqᴾ : ∀ {x} (d d′ : 𝔸ᴾ x) → ⟦ d ⟧ᵖ ≅ ⟦ d′ ⟧ᵖ
  uniq a[] a[] = z≅
  uniq (a∷ x xs) (a∷ x′ xs′) = add-≅ (uniqᴾ x x′) (uniq xs xs′)
  uniqᴾ (aψ {w = w} s d) (aψ s′ d′) = nodeU (inA s) (inA s′) (Seq s s′ (cmpᵀ-refl w)) (uniq d d′)
```

## §4 下一阶段

`Next S β dβ nβ cβ`: 给定上一阶段的系统 `S` 与一个可数标准形 $\beta$ (带 `GS.𝔸 S` 推导), 新的下标是 `Sub′ w = 𝔸 w × NF w × (w ≤ᵀ β)`, 层号 `lvS′` 是第 0 层树的 `toLevel`.

**序的对应** `oc`: 若第 0 层的树 $X\cong$ `⟦ du ⟧ᵃ` 且 $v<^\mathsf T u$ (都是可数标准形), 则 `T⟦ dv ⟧` $\prec X$. 与 Bachmann `oc` 逐行同构, 只是形状来自上一阶段的 `corr` (在层 $A$, 跨层 $\cong$):

- $u$ 后继: $X=\mathrm{suc}\,X'$, $X'\cong\llbracket u-1\rrbracket$. 离散性 `<sucT`: $v<u-1$ 时对 $X'$ 递归再 `≺s` (闭包 `NF-pred`/`Ctbl-pred`); $v=u-1$ 时 `≺z`, 叶子经 `T≅` 与 `uniq`.
- $u$ 极限: $X=\lim F$, $F\,n\cong\llbracket u[n]\rrbracket$. **共尾性** (Standard 的 `cofin`) 取 $n$ 使 $v<u[n]$, 对 $F\,n$ 递归再 `≺l n` (闭包 `NF-fsn`/`Ctbl-fsn`).
- $u=0$ 无 $v<u$; $\Omega$ 行由可数性排除 (`Ctbl-cof`); 与 $X$ 构造子不符的情形由 Bachmann 的 `zs`/`ls`/`zl`/`sl` 排除.

对树 $X$ 结构递归, 记号侧不用 `Acc`.

```agda
module Next (S : System) (β : T) (dβ : GS.𝔸 S β) (nβ : NF β) (cβ : Ctbl β) where
  open System S
  open GS S
  open Tree S

  Sub′ : T → Set
  Sub′ w = 𝔸 w × NF w × (w ≤ᵀ β)

  lvS′ : ∀ {w} → Sub′ w → Ordᴵ
  lvS′ (d , _ , _) = toLevel T⟦ d ⟧ (certT d)

  ctbl : ∀ {w} → Sub′ w → Ctbl w
  ctbl (_ , n , le) = Ctbl-≤ n cβ le

  oc   : ∀ (X : Ordᶜ zero) {u} (du : 𝔸 u) → NF u → Ctbl u → X ≅ ⟦ du ⟧ᵃ →
         ∀ {v} (dv : 𝔸 v) → NF v → Ctbl v → v <ᵀ u → T⟦ dv ⟧ ≺ X
  ocSh : ∀ (X : Ordᶜ zero) {u} (du : 𝔸 u) → NF u → Ctbl u → ∀ c → cof u ≡ c → Sh ⟦ du ⟧ᵃ c u → X ≅ ⟦ du ⟧ᵃ →
         ∀ {v} (dv : 𝔸 v) → NF v → Ctbl v → v <ᵀ u → T⟦ dv ⟧ ≺ X
  oc X {u} du nu cu h dv nv cv p = ocSh X du nu cu (cof u) refl (corr du) h dv nv cv p

  ocSh X {u = []} du nu cu c ce sh h dv nv cv ()
  ocSh X {u = x ∷ xs} du nu cu c0 ce sh h dv nv cv p = ⊥-elim (cof-ne x xs ce)
  ocSh X {u = x ∷ xs} du nu cu (cΩ μ) ce sh h dv nv cv p = ⊥-elim (Ctbl-cof cu ce)
  ocSh zero    {u = x ∷ xs} du nu cu c1 ce (Y , eY , _) h dv nv cv p = ⊥-elim (zs (≅-trans h eY))
  ocSh (lim F) {u = x ∷ xs} du nu cu c1 ce (Y , eY , _) h dv nv cv p = ⊥-elim (ls (≅-trans h eY))
  ocSh (suc X′) {u = u@(x ∷ xs)} du nu cu c1 ce (Y , eY , d′ , e′) h {v} dv nv cv p
    with <sucT (pred u) (subst (v <ᵀ_) (sym (E.pred-suc u ce)) p)
  ... | inj₁ q    = ≺s (oc X′ d′ (NF-pred nu ce) (Ctbl-pred cu) hX′ dv nv cv q)
    where hX′ = ≅-trans (s-inv (≅-trans h eY)) e′
  ... | inj₂ refl = ≺z (≅-trans (T≅ cv dv) (≅-trans (uniq dv d′) (≅-sym hX′)))
    where hX′ = ≅-trans (s-inv (≅-trans h eY)) e′
  ocSh zero    {u = x ∷ xs} du nu cu cω ce (G , eG , _) h dv nv cv p = ⊥-elim (zl (≅-trans h eG))
  ocSh (suc X′) {u = x ∷ xs} du nu cu cω ce (G , eG , _) h dv nv cv p = ⊥-elim (sl (≅-trans h eG))
  ocSh (lim F) {u = u@(x ∷ xs)} du nu cu cω ce (G , eG , hG) h dv nv cv p with cofin nu ce nv p
  ... | n , q = ≺l n (oc (F n) (proj₁ (hG n)) (NF-fsn nu ce n) (Ctbl-fsn cu ce n)
                         (≅-trans (l-inv (≅-trans h eG) n) (proj₂ (hG n))) dv nv cv q)
  ocSh (limᵢ () f) {u = x ∷ xs} du nu cu c1 ce sh h dv nv cv p
  ocSh (up () y)   {u = x ∷ xs} du nu cu c1 ce sh h dv nv cv p
  ocSh (limᵢ () f) {u = x ∷ xs} du nu cu cω ce sh h dv nv cv p
  ocSh (up () y)   {u = x ∷ xs} du nu cu cω ce sh h dv nv cv p
```

由 `oc` 与 Level 的 `toLevel-≺`/`toLevel-≅` 得到层号上的序的对应 `Slt′`/`Seq′` (严格性来自树的 $\prec$, 不来自证书的步进).

```agda
  OC< : ∀ {v u} (sv : Sub′ v) (su : Sub′ u) → v <ᵀ u → T⟦ proj₁ sv ⟧ ≺ T⟦ proj₁ su ⟧
  OC< sv@(dv , nv , _) su@(du , nu , _) p = oc T⟦ du ⟧ du nu (ctbl su) (T≅ (ctbl su) du) dv nv (ctbl sv) p

  Slt′ : ∀ {v u} (sv : Sub′ v) (su : Sub′ u) → cmpᵀ v u ≡ lt → lvS′ sv ≺ᴵ lvS′ su
  Slt′ {v} {u} sv su e = toLevel-≺ (certT (proj₁ sv)) (certT (proj₁ su)) (OC< sv su (lt→< v u e))

  TT : ∀ {v} (sv sv′ : Sub′ v) → T⟦ proj₁ sv ⟧ ≅ T⟦ proj₁ sv′ ⟧
  TT sv@(d , _ , _) sv′@(d′ , _ , _) = ≅-trans (T≅ (ctbl sv) d) (≅-trans (uniq d d′) (≅-sym (T≅ (ctbl sv′) d′)))

  Seq′ : ∀ {v u} (sv : Sub′ v) (su : Sub′ u) → cmpᵀ v u ≡ eq → lvS′ sv ≅ᴵ lvS′ su
  Seq′ {v} {u} sv su e with eq→≡ v u e
  ... | refl = toLevel-≅ (certT (proj₁ sv)) (certT (proj₁ su)) (TT sv su)
```

其余接口. **公共上界** $A'=\mathrm{suc}(\mathtt{lvS}'\,\beta)$: $w<\beta$ 时 `Slt′` 再 `≺-suc`, $w=\beta$ 时 `Seq′` 与 `zero`. `S1′`/`Sω′`: 从 `corr` 的后继/极限形状经 `T≅` 搬到第 0 层, 再 `toLevel-≅`; 极限的 `lim g st` 就是 `toLevel (lim F) hL` 的定义性展开 (`asLim` 把 `T⟦ d ⟧` 化成字面的 `lim F`). 新下标的闭包: `NF-pred`/`NF-fsn` 与 `pred-<`/`fs<ᵀ` (保持 $\le\beta$). `SΩ′` 是 `Ctbl-cof`. `s0`: 推导 `a[]`.

```agda
  sβ : Sub′ β
  sβ = dβ , nβ , inj₂ refl

  A′ : Ordᴵ
  A′ = suc (lvS′ sβ)

  inA′ : ∀ {w} (s : Sub′ w) → lvS′ s ≺ᴵ A′
  inA′ s@(d , n , inj₁ p)    = ≺-suc (Slt′ s sβ (<→lt p))
  inA′ s@(d , n , inj₂ refl) = via (Seq′ s sβ (cmpᵀ-refl β)) zero

  S0′ : (s : Sub′ []) → lvS′ s ≅ᴵ zero
  S0′ (a[] , _ , _) = z≅

  S1′ : ∀ {w} (s : Sub′ w) → cof w ≡ c1 → Σ (Sub′ (pred w)) λ s′ → lvS′ s ≅ᴵ suc (lvS′ s′)
  S1′ {w} s@(d , n , le) ce with subst (λ c → Sh ⟦ d ⟧ᵃ c w) ce (corr d)
  ... | Y , eY , d′ , e′ = s′ , toLevel-≅ (certT d) (hs (certT d′)) eT
    where
    s′ : Sub′ (pred w)
    s′ = d′ , NF-pred n ce , inj₁ (<≤-trans (E.pred-< w ce) le)
    eT : T⟦ d ⟧ ≅ suc T⟦ d′ ⟧
    eT = ≅-trans (T≅ (ctbl s) d) (≅-trans eY (s≅ (≅-trans e′ (≅-sym (T≅ (ctbl s′) d′)))))

  Sω′ : ∀ {w} (s : Sub′ w) → cof w ≡ cω → Σ (ℕ → Ordᴵ) λ g → Σ (∀ n → g n ⊑ᴵ g (suc n)) λ st →
        (lvS′ s ≅ᴵ lim g st) × (∀ n → Σ (Sub′ (fsn w n)) λ s′ → g n ≅ᴵ lvS′ s′)
  Sω′ {w} s@(d , n , le) ce with subst (λ c → Sh ⟦ d ⟧ᵃ c w) ce (corr d)
  ... | G , eG , hG with asLim T⟦ d ⟧ (≅-trans (T≅ (ctbl s) d) eG)
  ...   | F , eqF , hF =
    (λ m → toLevel (F m) (hl₁ hL m)) , (λ m → toLevel-⊑ (hl₁ hL m) (hl₁ hL (suc m)) (hl₂ hL m)) ,
    toLevel-≅ (certT d) hL (subst (T⟦ d ⟧ ≅_) eqF (≅-refl⁰ _)) ,
    λ m → sm m , toLevel-≅ (hl₁ hL m) (certT (proj₁ (hG m)))
                   (≅-trans (hF m) (≅-trans (proj₂ (hG m)) (≅-sym (T≅ (ctbl (sm m)) (proj₁ (hG m))))))
    where
    hL : HS (lim F)
    hL = subst HS eqF (certT d)
    sm : ∀ m → Sub′ (fsn w m)
    sm m = proj₁ (hG m) , NF-fsn n ce m , inj₁ (<≤-trans (fs<ᵀ ce m) le)

  SΩ′ : ∀ {w μ} → Sub′ w → cof w ≡ cΩ μ → ⊥
  SΩ′ s ce = Ctbl-cof (ctbl s) ce

  next : System
  next = record { Sub = Sub′ ; lvS = lvS′ ; A = A′ ; inA = inA′ ; S0 = S0′ ; S1 = S1′ ; Sω = Sω′ ; SΩ = SΩ′
                ; Slt = Slt′ ; Seq = Seq′ ; s0 = a[] , n[] , []≤ β }
```

## §5 对角线上的阶段

`triv`: 下标只有 $0$ (`w ≡ []`), 层号 `zero`, 上界 `suc zero`. `dγ S k sγ`: $\gamma^\mathsf E_{k+1}=\psi_0(\Omega_{\gamma^\mathsf E_k})$ 在 `GS.𝔸 S` 里的推导, 用 `s0` 与 `sγ : Sub S (γᴱ k)`. 阶段: `St k = Next (prev k) (γᴱ k) (dB k)`, 其 $\beta$ 是 $\gamma^\mathsf E_k$, `sγ k` 是 $\beta$ 自己的下标证明 (`Next.sβ`); `prev (suc k) = St k`, `dB (suc k) = dγ (St k) k (sγ k)`. 四个函数互递归, 通过停机检查 (`St k → prev k → St (k−1)`).

于是 `St 0` 的下标是 $\le1$ 的标准形 ($0$ 与 $1$), `St 1` 的是 $\le\varepsilon_0$ 的 (纸面: 与 Bachmann 的 `NF` 是同一个项集合, Cantor 标准形与 $\varepsilon_0$; 因为 $a<\Omega_1$ 而 $\psi_0(a)$ 满足 `Bnd` 时 $a$ 里不能有 $\Omega_1$), `St 2` 的是 $\le\gamma_2=\psi_0(\Omega_{\varepsilon_0})$ 的 Buchholz 型标准形 (下标 $\le\varepsilon_0$), 依此类推: 第 $k+1$ 阶段的下标是第 $k$ 阶段 `Generic` 的类里 $\le\gamma^\mathsf E_{k+1}$ 的标准形, 其中的 $\psi$-下标属于第 $k$ 阶段.

```agda
triv : System
triv = record
  { Sub = λ w → w ≡ []
  ; lvS = λ _ → zero
  ; A   = suc zero
  ; inA = λ _ → via z≅ zero
  ; S0  = λ _ → z≅
  ; S1  = λ { refl () }
  ; Sω  = λ { refl () }
  ; SΩ  = λ { refl () }
  ; Slt = λ { refl refl () }
  ; Seq = λ _ _ _ → z≅
  ; s0  = refl
  }

dγ : ∀ (S : System) k → System.Sub S (γᴱ k) → GS.𝔸 S (γᴱ (suc k))
dγ S k sγ = GS.a∷ {S = S} (GS.aψ {S = S} (System.s0 S) (GS.a∷ {S = S} (GS.aψ {S = S} sγ (GS.a[] {S = S})) (GS.a[] {S = S}))) (GS.a[] {S = S})

dγ₀ : GS.𝔸 triv (γᴱ 0)
dγ₀ = GS.a∷ {S = triv} (GS.aψ {S = triv} refl (GS.a[] {S = triv})) (GS.a[] {S = triv})

prev : ℕ → System
dB   : ∀ k → GS.𝔸 (prev k) (γᴱ k)
St   : ℕ → System
sγ   : ∀ k → System.Sub (St k) (γᴱ k)

St k = Next.next (prev k) (γᴱ k) (dB k) (diag-NF k) (diag-Ctbl k)
sγ k = Next.sβ (prev k) (γᴱ k) (dB k) (diag-NF k) (diag-Ctbl k)
prev zero    = triv
prev (suc k) = St k
dB zero    = dγ₀
dB (suc k) = dγ (St k) k (sγ k)
```

## §6 遗传标签

`agreeT k`: Correspond 的翻译 `⟦ gγ k ⟧` 与第 $k$ 阶段的 $\beta$ 的第 0 层树 $\cong$ (对 $k$ 归纳: 两边都是 $\psi^0(\Omega_{L})$ 对 $\psi^0(\mathtt{node}\,\cdots)$, 由 Generic 的 `Ω-node` 与 `toLevel-≅`). `agree k`: `⟦ gγ (suc k) ⟧` 与 `dγ` 的翻译 $\cong$ (外层的 $\psi_0$ 节点由 `top‴`). 与 Correspond 的 `diag-≅` 合成, `GS.lab` 给出标签; `diag-label` 把它们合成 BTBO 的标签.

```agda
agreeT : ∀ k → ⟦ gγ k ⟧ ≅ Tree.T⟦_⟧ (prev k) (dB k)
agreeT zero    = ≅-refl⁰ _
agreeT (suc k) = ψ⁰-≅ (GS.Ω-node (St k) (System.inA (St k) (sγ k))
                        (toLevel-≅ (cert (gγ k)) (Tree.certT (prev k) (dB k)) (agreeT k)))

agree : ∀ k → ⟦ gγ (suc k) ⟧ ≅ GS.⟦_⟧ᵃ (St k) (dγ (St k) k (sγ k))
agree k = Tree.top‴ (St k) (System.inA (St k) (System.s0 (St k))) (System.S0 (St k) (System.s0 (St k)))
            (GS.Ω-node (St k) (System.inA (St k) (sγ k))
               (toLevel-≅ (cert (gγ k)) (Tree.certT (prev k) (dB k)) (agreeT k)))

γ-label : ∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))
γ-label k = GS.lab (St k) (N.γ (suc k)) (dγ (St k) k (sγ k)) (≅-trans (diag-≅ (suc k)) (agree k))

BTBO-label : Lab N.BTBOᴵ (E.EBOψ 2)
BTBO-label = diag-label γ-label
```

**定理 `γ-label : ∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))` 与 `BTBO-label : Lab N.BTBOᴵ (E.EBOψ 2)`.** $k=0,1$ 分别重新得到 Correspond 的 `ε₀-label` 与 Bachmann 的 `γ₂-label` (同一类型的另一个证明); $k\ge2$ 是新的.

**推论.** `lvγ-L`/`A-L`: 第 $k$ 阶段 $\beta$ 的层号 $\cong^\mathsf I$ NoCumsum 的 `N.L k`, 公共上界 $\cong^\mathsf I$ `suc (N.L k)` (字面上是 `suc (lvS (sγ k))`, 最后一行 `refl`). `BTBO-step`: 外层一步 (ℕ 上字面等式). `desc-lab`: $\gamma^\mathsf E_{k+1}$ 的每个基本列后代 (Standard 的 `Desc`) 都有带标签的树, 由 `FGH-Labω`/`FGH-Lab1` 反演 (Bachmann `reach-lab` 的一般形); Closure 的墙项 $P$ 是 $\gamma^\mathsf E_2$ 的后代 (19 步, Bachmann 的 `wall-reach` 同法, 本文未重复), 故 $P$ 及其后代都有标签.

```agda
lvγ-L : ∀ k → System.lvS (St k) (sγ k) ≅ᴵ N.L k
lvγ-L k = toLevel-≅ (Tree.certT (prev k) (dB k)) (N.cert k) (≅-sym (≅-trans (diag-≅ k) (agreeT k)))

A-L : ∀ k → System.A (St k) ≅ᴵ suc (N.L k)
A-L k = s≅ (lvγ-L k)

BTBO-step : ∀ n → FGH N.BTBOᴵ n ≡ FGH (N.γ (suc n)) n
BTBO-step n = proj₂ (proj₂ (FGH-Labω BTBO-label refl)) n

γ₃-label : Lab (N.γ 3) (γᴱ 3)
γ₃-label = γ-label 2

_ : System.A (St 1) ≡ suc (System.lvS (St 1) (sγ 1))
_ = refl

desc-lab : ∀ k {t} → Desc (γᴱ (suc k)) t → Σ (Ordᶜ zero) λ X → Lab X t
desc-lab k d₀ = N.γ (suc k) , γ-label k
desc-lab k (dω d e n) with FGH-Labω (proj₂ (desc-lab k d)) e
... | F , h , _ = F n , h n
desc-lab k (d₁ d e) with FGH-Lab1 (proj₂ (desc-lab k d)) e
... | Y , l , _ = Y , l
```

## §7 对比表

| | Bachmann ($\gamma_2$) | 本文 (一切 $\gamma_{k+1}$) |
|---|---|---|
| 下标系统 | `NF` (Cantor ∪ {ε₀}), 手写七条接口 | `Next S β`: 由上一阶段 `Generic` 生成, 七条接口一次证完 |
| 下标的树 | Correspond 的 `⟦ emb ⟧` (第 0 层) | `T⟦ d ⟧ = Σ ψ⁰ ⟦ aᵢ ⟧ᵃ`, 证书由 `Good` 归纳 |
| 推导唯一性 | 字面 (`𝔼-≡`) | 模 $\cong$ (`uniq`, 用上一阶段的 `Seq`) |
| 序的对应 | `oc` + Cantor 的 `cofin` | 同一个 `oc` + Standard 的 `cofin` (规则 6) |
| 公共上界 | $A_0=\mathrm{suc}(E_0)$, `L₁≅E₀` | $A_k=\mathrm{suc}(\mathtt{lvS}\,\gamma_k)$, `A-L : A ≅ᴵ suc (N.L k)` |
| `Generic` | 定义 | 原样应用 (`module GS (S : System) = Generic …`) |
| 标签 | `γ₂-label` | **`γ-label : ∀ k`**, **`BTBO-label`** |

## §8 结论与边界

**字面成立:** `System.A (St 1) ≡ suc (lvS (sγ 1))` (`refl`); 翻译的定义性展开 (`T⟦ dγ … ⟧` 即 `ψ⁰ (node …)`, `⟦ gγ (suc k) ⟧` 即 `ψ⁰ (Ω (lvl (gγ k)))`); `BTBO-step` 是 ℕ 上的字面等式.

**模 $\cong$ 成立 (定理):** 每一阶段的序的对应 `Slt′`/`Seq′` (层号的 $\prec^\mathsf I$/$\cong^\mathsf I$) 与树侧 `OC<`; `T≅`, `uniq`; `agreeT`, `agree`; `lvγ-L`, `A-L`.

**关于标签, 现在证了什么.** `γ-label k` 对**一切** $k$ 成立, `BTBO-label` 由 Correspond 的 `diag-label` 得到. `Lab X t` 是 README 认证准则的归纳形式化: 由它逐层读出 FGH 的 EBO 递归方程 ($t=0$: $n+1$; $t$ 后继: $f^n_{t-1}(n)$; $t$ 极限: $f_{t[n]}(n)$), 每一层都是 ℕ 上的字面等式, 对应的树只模 $\cong$ 确定 (`FGH-≅` 保证 FGH 不受影响). 所以: **NoCumsum 的树 `BTBOᴵ` 的 FGH 满足 EBO 沿 $\psi_0(\Omega_\Omega)$ 的全部递归方程, 在任意深度; 标签 BTBO $=\psi_0(\Omega_\Omega)$ 对 `N.BTBOᴵ` 是定理.**

**边界.**

- 定理是关于 probes 的无 cumsum 树族 (Level/Uniform/NoCumsum) 上的 `N.BTBOᴵ`. `src/OCF/BTBO.lagda.md` (已封存, 含四行补丁) 的树与它的关系没有在本文证明; README 记录的 src 标签仍按原文口吻.
- 证明链用到的标准形是 Standard 的可数下标标准形; 对角线的一切后代都在其中. EBO 中更大的段落 (不可数下标) 不在本文范围.
- 每个阶段的翻译依赖推导与证据, 唯一性只模 $\cong$ (`uniq`); 层号 `lvS` 依赖证书, 不同证书之间只 $\cong^\mathsf I$.
- 不改 `src/`、`archive/` 与已有的 Align 文件 (README 未改).
