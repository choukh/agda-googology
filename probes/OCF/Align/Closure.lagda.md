# 基本列闭包: 带层号证据的推导类与阶段 2 的墙

> 接 [Correspond](Correspond.lagda.md) §10–§12. 那里证了纯片段 $\mathbb G$ 的形状定理、对角线的外层一致与 $\gamma_1=\varepsilon_0$ 的遗传标签, 并把 "BTBO $=\psi_0(\Omega_\Omega)$" 归约为 `∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))`. 缺口是阶段 2: 翻译 $\psi_u(\alpha)$ 时, $\alpha$ 里的 $\Omega_v$/$\psi_v$ ($v\ne u$) 要 (a) 层号证据才能放进 $\psi_u$ 的参数层, (b) 树的派发 `<ᴵ-dec` 与记号的派发 `cmpᵀ (ν+1) u` 一致. Correspond §12 末段提出的路线是: 不建标准形理论, 而按 "基本列闭包" 归纳, 让证据随形状一起传递, 新下标的证据在它被基本列造出来的那一刻现场制造. 本文走这条路, 走到哪里就停在哪里, 并把停下的地方精确地写出来.
>
> 结论先说:
>
> 1. **证据的正确形状是 $\trianglelefteq^\mathsf I$, 不是 $\prec^\mathsf I$ (§2).** 任务设想用 `Ω-shapeω` + `toLevel-≺` 给 $u[n]$ 造 `lvl (u[n]) ≺ᴵ lvl u`. 这做不到: `HS` 的步进只是 $\sqsubseteq$ (非严格), `toLevel (lim F)` 的第 $n$ 项 `toLevel (F n)` 不是它的字面严格子项 ($<^\mathsf I$ 只穿过 `lim` 的分支之下). 现场能造的是 "模 $\cong^\mathsf I$ 的结构子项或相等" $a\trianglelefteq^\mathsf I b$ (`self n : f n ◃ lim f s`), 它对极限步与传递封闭 (`⊴-trans`). 树的派发真正消费严格性的地方只有一处: 后继叶子 $\Omega_{\nu+1}$ 的指标层 $\nu$, 而 $\nu+1\trianglelefteq w\Rightarrow\nu\prec w$ (`suc⊴→≺`, 因为 $c<a\triangleleft b\Rightarrow c<b$). 所以证据只在 $\trianglelefteq$ 里传递, 在派发处现场转成 $\prec$.
> 2. **派发一致引理 (§5).** `pen⁺`: 只要目标层 $i$ 与 `limᵢ` 节点的指标层 $j$ 满足 $j\cong^\mathsf I N\prec^\mathsf I i$ (任意代表元), `ψ p σ (limᵢ q f)` **字面地** (`≡`, 由 `with` 抽象出的 `refl`) 等于穿透节点; 其余两支由 $\prec^\mathsf I$ 无自反排除. 层引理 `ΩL-be`/`ΩL-ab`/`LL-be`/`LL-ab` 把 "$\Omega$-形状" `ShΩ` 与 "$\omega$-形状" `ShL` 穿过一层 $\psi_w$ 节点, `Ψ⁰Ω`/`Ψ⁰L` 处理最外层的 $\psi_0$ (规则 6 的链逐项 $\cong$).
> 3. **检验一 (出口路径) 全部通过 (§6).** 三个项 $\psi_0(\Omega_{\omega+1})$, $\psi_0(\psi_\omega(\Omega_\omega))$, $\psi_0(\psi_\omega(\Omega_2))$ 都有带证据的推导与一步形状: `shape₁` (Correspond 的 `corr`), `shape₂ = K1-lim …` (第 $n$ 项是 $\psi_0(\psi_\omega(\Omega_{\omega[n]}))$, 证据 `lvl (ω[n]) ⊴ᴵ lvl ω` 由 `Ω-shapeω` 现场造出), `shape₃ = K1-suc …` (第 $n$ 项是 $\psi_0(\psi_\omega(\gamma_n))$, $\gamma_{k+1}=\psi_1(\psi_\omega(\gamma_k))$; $\psi_\omega$ 处的派发由 `pen⁺` 证为穿透, 证据 `lvl 1 ≺ᴵ lvl ω` 由 `suc⊴→≺` 造出). `c₃ : lvl g2 ⊴ᴵ lvl gω` 正是从 `shape₂` 的第 2 项取出来的.
> 4. **一般的脊片段 $\mathbb K^+$ 对 `fsn` 封闭 (§7–§8).** $\mathbb K^+$: $\psi_0(\psi_{w_1}(\cdots\psi_{w_k}(\Omega_v)))$, 下标都在 $\varepsilon_0$ 片段 $\mathbb E$ 里, 每层带位置证据 ($w\prec^\mathsf I$ 子节点顶层, 或子节点顶层 $\trianglelefteq^\mathsf I w$), 不变量 `Inv`: 叶子 $v$ 对每一层 $w$ 都有句法 $v\le w$ (`Pen (cmpᵀ v w)`) 与树侧 `lvl v ⊴ᴵ lvl w`. **`K-shape`: 叶子 $v\ne0$ 时, 项的共尾度是 $\omega$, 树 $\cong\lim F$, 每个 $F\,n$ 匹配 `fsn t n` 的一个 $\mathbb K^+$ 推导.** 极限叶子走 `CxL`, 后继叶子走 `CxΩ` + `pen⁺` + 规则 6 的链 (新层由 `plug` 拼接), 不变量逐项现场重建 (句法侧用 `dec`/`pred-<` 与 §1 的 `Pen-desc`). Correspond 的链项 $\psi_0(\psi_\nu^{k+1}(\Omega_\nu))$ 都是 $\mathbb K^+$ 项 (`entry`), 出口路径上的 `K-shape′` 可以机械地迭代 (`shape-k₂`, `shape-k₃`, 证据全自动).
> 5. **检验二被挡住 (§9), 墙在这里.** $\mathbb K^+$ 的唯一出口是叶子到 $0$ ($\Omega_0=1$, 之后规则 4 产生和). 出了 $\mathbb K^+$ 以后, 会出现目标下标在叶子**之下**的层 ($\psi_u$ 走规则 6 链, $u\ne0$), 叶子再下降时要与这种层比较, 而二者不在同一条基本列路径上. 精确实例 (全部 `refl`): 从 $\gamma^\mathsf E_2=\psi_0(\Omega_{\varepsilon_0})$ 沿路径 `base` (19 步: 1,2,2,2,1,1,1,0,2,1,6,1,0,0,0,0,0,1,1) 到达
>    $$P=\psi_0(\psi_{\omega+1}(\psi_\omega(\Omega_{\omega+1}+\psi_\omega(\Omega_{\omega+1}+\psi_5(\psi_{\omega+1}(\psi_\omega(\Omega_{\omega+1}+\psi_\omega(\psi_\omega(\Omega_\omega)))))))))$$
>    (`wall-path`), 再走一步 $[n]$ 得到叶子 $\Omega_n$. $\psi_5$ 节点的派发是 `cmpᵀ (sucT ν) 5`, $\nu=n-1$: $n=5$ 穿透 (`node-5`), $n=6$ 折叠 (`node-6`). 树侧要的是 **$(\nu,u)=(n-1,5)$ 的比较证据**: $n\le5$ 时 `lvl (n-1) ≺ᴵ lvl 5`, $n\ge6$ 时 `lvl 5 ≺ᴵ lvl (n-1)` 或 $\cong^\mathsf I$. 这两个下标都是 $\omega$ 的基本列后代, 但在不同分支上: $5=\mathrm{pred}(\omega[6])$ (第 11–12 步, `step₁₁`/`step₁₂`), $n=\omega[n]$ (第 20 步). "后代路径" 不变量只给出 `lvl 5 ⊴ᴵ lvl ω` 与 `lvl n ⊴ᴵ lvl ω`, 两者之间没有任何关系可推. 能制造它的更强不变量是 **Bachmann 性质**: 对闭包里的极限下标 $u$, $u[m]$ 是 $u[m+1]$ 的基本列后代 (句法) 且 $\llbracket u[m]\rrbracket\prec\llbracket u[m+1]\rrbracket$ (树; `HS` 只给 $\sqsubseteq$), 再加 "按路径首个分叉处比较". 对 $\omega$ 它平凡 (自然数), 对一般的 $\mathbb E$ 下标 (检验二要的 $<\varepsilon_0$) 它是 Cantor 标准形的一段标准形理论, 对检验三 (下标 $<\gamma_k$) 是 EBO 的标准形理论. 本文没有做它. **所以 `Lab (N.γ 2) (γᴱ 2)` 未证, BTBO $=\psi_0(\Omega_\Omega)$ 仍是估计.**
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件 (没有需要复制的私有定义; `Restr` 的字段以 `R.rep` 等限定名使用).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Closure where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Uniform using (≅-reflˡ; ≅-reflʳ; self-tr; self-tr⁻)
open import OCF.Align.Correspond using (𝔾; g[]; g∷; gψ; gΩ; ⟦_⟧; lvl; cert; Pure; Match; Sh; corr;
  Ω-shape1; Ω-shapeω; HS-≅; ωᵗ; cmp-suc[]; fsT-c1; fsn↓c-gt; fs-ω; γᴱ; Lab; gH; hψ; hΩ; Shape;
  𝔼; e[]; e∷; eψ; eΩ₁; emb; corrE; ShE; MatchE; cof-ne; ch; hch; ⟦_⟧ᴴ)
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; cofP; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; natT; fsn; fsT; fsT0; γT; trm; dec)
       renaming (ψ to ψᵗ)
module R = Restr

```

## §1 记号侧: 句法序与 "可穿透" 判定

`Pen m` 说比较结果 $m$ 是 `lt` 或 `eq`, 即记号在 $\psi_w$ 处对共尾度 $\Omega_{\nu+1}$ 穿透 (规则 5Ω, $\nu+1\le w$). 脊片段的不变量要把 "叶子 $v\le$ 每一层 $w$" 随基本列传下去, 需要 `cmpᵀ` 与句法序 $<^\mathsf T$ 的四条对应 (`cmpᵀ-refl`, `<→lt`, `lt→<`, `eq→≡`) 与 $<^\mathsf T$ 的传递. 证明对 `cmpᵀ` 内部的 `with` 用 `with … in` 与 `rewrite` 对齐. 这些在一切项上成立 (字典序), 不要标准形.

```agda
open E using (_<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)

cmpᵀ-refl : ∀ a → cmpᵀ a a ≡ eq
cmpᴾ-refl : ∀ x → E.cmpᴾ x x ≡ eq
cmpᵀ-refl []       = refl
cmpᵀ-refl (x ∷ xs) rewrite cmpᴾ-refl x = cmpᵀ-refl xs
cmpᴾ-refl (ψᵗ u a) rewrite cmpᵀ-refl u = cmpᵀ-refl a

<→lt  : ∀ {a b} → a <ᵀ b → cmpᵀ a b ≡ lt
<ᴾ→lt : ∀ {x y} → x <ᴾ y → E.cmpᴾ x y ≡ lt
<→lt []< = refl
<→lt (hd< p) rewrite <ᴾ→lt p = refl
<→lt (tl< {x = x} p) rewrite cmpᴾ-refl x = <→lt p
<ᴾ→lt (lv< p) rewrite <→lt p = refl
<ᴾ→lt (ar< {u = u} p) rewrite cmpᵀ-refl u = <→lt p

lt→<  : ∀ a b → cmpᵀ a b ≡ lt → a <ᵀ b
lt→<ᴾ : ∀ x y → E.cmpᴾ x y ≡ lt → x <ᴾ y
eq→≡  : ∀ a b → cmpᵀ a b ≡ eq → a ≡ b
eq→≡ᴾ : ∀ x y → E.cmpᴾ x y ≡ eq → x ≡ y
lt→< [] [] ()
lt→< [] (y ∷ ys) e = []<
lt→< (x ∷ xs) [] ()
lt→< (x ∷ xs) (y ∷ ys) e with E.cmpᴾ x y in ex
... | lt = hd< (lt→<ᴾ x y ex)
... | eq rewrite eq→≡ᴾ x y ex = tl< (lt→< xs ys e)
lt→<ᴾ (ψᵗ u a) (ψᵗ v b) e with cmpᵀ u v in eu
... | lt = lv< (lt→< u v eu)
... | eq rewrite eq→≡ u v eu = ar< (lt→< a b e)
eq→≡ [] [] e = refl
eq→≡ [] (y ∷ ys) ()
eq→≡ (x ∷ xs) [] ()
eq→≡ (x ∷ xs) (y ∷ ys) e with E.cmpᴾ x y in ex
... | eq rewrite eq→≡ᴾ x y ex | eq→≡ xs ys e = refl
eq→≡ᴾ (ψᵗ u a) (ψᵗ v b) e with cmpᵀ u v in eu
... | eq rewrite eq→≡ u v eu | eq→≡ a b e = refl

<ᵀ-trans : ∀ {a b c} → a <ᵀ b → b <ᵀ c → a <ᵀ c
<ᴾ-trans : ∀ {x y z} → x <ᴾ y → y <ᴾ z → x <ᴾ z
<ᵀ-trans []< (hd< q) = []<
<ᵀ-trans []< (tl< q) = []<
<ᵀ-trans (hd< p) (hd< q) = hd< (<ᴾ-trans p q)
<ᵀ-trans (hd< p) (tl< q) = hd< p
<ᵀ-trans (tl< p) (hd< q) = hd< q
<ᵀ-trans (tl< p) (tl< q) = tl< (<ᵀ-trans p q)
<ᴾ-trans (lv< p) (lv< q) = lv< (<ᵀ-trans p q)
<ᴾ-trans (lv< p) (ar< q) = lv< p
<ᴾ-trans (ar< p) (lv< q) = lv< q
<ᴾ-trans (ar< p) (ar< q) = ar< (<ᵀ-trans p q)

Pen : Cmp → Set
Pen m = (m ≡ lt) ⊎ (m ≡ eq)

Pen-desc : ∀ {a v w} → a <ᵀ v → Pen (cmpᵀ v w) → cmpᵀ a w ≡ lt
Pen-desc {v = v} {w} p (inj₁ e) = <→lt (<ᵀ-trans p (lt→< v w e))
Pen-desc {a} {v} {w} p (inj₂ e) = subst (λ z → cmpᵀ a z ≡ lt) (eq→≡ v w e) (<→lt p)
```

`Pen-desc` 是句法侧的 "现场制造": $a<^\mathsf T v$ (由 `fsn↓` 的 `dec` 证书或 `pred-<` 给出) 且 $v\le w$, 则 `cmpᵀ a w ≡ lt`.

## §2 下标层的证据 $\trianglelefteq^\mathsf I$

$a\trianglelefteq^\mathsf I b$: $a\cong^\mathsf I b$, 或 $a\cong^\mathsf I a'$ 且 $a'\triangleleft b$ (Level 的结构子项, 含 `self n : f n ◃ lim f s`). 它是 `Ω` 与 `lift` 实际放置子层所用的关系. 引理: `<◃` ($c<a\triangleleft b\Rightarrow c<b$), `◃-trans`, `◃-≅` (结构子项沿 $\cong^\mathsf I$ 搬运, 与 Level 的 `<-≅` 同形), `⊴-trans`, `pred⊴` ($N\trianglelefteq N+1$), 以及把非严格证据转成派发所需严格证据的唯一一处 `suc⊴→≺`: $A\cong N+1$ 且 $A\trianglelefteq B$ 推出 $N\prec^\mathsf I B$.

```agda
infix 4 _⊴ᴵ_
data _⊴ᴵ_ (a b : Ordᴵ) : Set where
  eqv : a ≅ᴵ b → a ⊴ᴵ b
  sub : ∀ {a′} → a ≅ᴵ a′ → a′ ◃ b → a ⊴ᴵ b

<◃ : ∀ {c a b} → c <ᴵ a → a ◃ b → c <ᴵ b
<◃ p zero      = suc p
<◃ p (suc r)   = suc (<◃ p r)
<◃ p (self n)  = lim n p
<◃ p (lim n r) = lim n (<◃ p r)

◃-trans : ∀ {a b c} → a ◃ b → b ◃ c → a ◃ c
◃-trans r zero      = suc r
◃-trans r (suc r′)  = suc (◃-trans r r′)
◃-trans r (self n)  = lim n r
◃-trans r (lim n r′) = lim n (◃-trans r r′)

◃-≅ : ∀ {c a a′} → c ◃ a → a ≅ᴵ a′ → Σ Ordᴵ λ c′ → (c ≅ᴵ c′) × (c′ ◃ a′)
◃-≅ zero      (s≅ e) = _ , e , zero
◃-≅ (suc r)   (s≅ e) with ◃-≅ r e
... | c′ , d , r′ = c′ , d , suc r′
◃-≅ (self n)  (l≅ h) = _ , h n , self n
◃-≅ (lim n r) (l≅ h) with ◃-≅ r (h n)
... | c′ , d , r′ = c′ , d , lim n r′

⊴-trans : ∀ {a b c} → a ⊴ᴵ b → b ⊴ᴵ c → a ⊴ᴵ c
⊴-trans (eqv e)   (eqv e′)   = eqv (≅ᴵ-trans e e′)
⊴-trans (eqv e)   (sub e′ r) = sub (≅ᴵ-trans e e′) r
⊴-trans (sub e r) (eqv e′) with ◃-≅ r e′
... | _ , d , r′ = sub (≅ᴵ-trans e d) r′
⊴-trans (sub e r) (sub e′ r′) with ◃-≅ r e′
... | _ , d , r″ = sub (≅ᴵ-trans e d) (◃-trans r″ r′)

pred⊴ : ∀ N → N ⊴ᴵ suc N
pred⊴ N = sub (≅ᴵ-refl N) zero

suc⊴→≺ : ∀ {A N B} → A ≅ᴵ suc N → A ⊴ᴵ B → N ≺ᴵ B
suc⊴→≺ {N = N} e (eqv e′) = ≺ᴵ-respʳ (via (≅ᴵ-refl N) zero) (≅ᴵ-trans (≅ᴵ-sym e) e′)
suc⊴→≺ {N = N} e (sub e′ r) with ≺ᴵ-respʳ (via (≅ᴵ-refl N) zero) (≅ᴵ-trans (≅ᴵ-sym e) e′)
... | via d q = via d (<◃ q r)
```

**为什么不是 $\prec^\mathsf I$.** 对极限下标 $u$, `Ω-shapeω` 给出 `lvl u ≅ᴵ toLevel (lim F) hF`, 后者定义性地是 `lim (λ n → toLevel (F n) _) _`; 第 $n$ 项与它的关系是 `self n` ($\triangleleft$), 不是 $<^\mathsf I$ (`lim n p` 要 $a<f\,n$). 要得到严格的 `lvl (u[n]) ≺ᴵ lvl u` 需要某个 $m$ 使 `F n ≺ F m`, 而 `HS` 的步进 `F n ⊑⁰ F (suc n)` 是非严格的. 所以 "Ω-shapeω + toLevel-≺" 的设想在极限步不成立; 用 $\trianglelefteq$ 代替后, 极限步就是 `sub _ (self n)`, 一行.

## §3 节点的翻译

$\psi_w$ 节点有两种位置: 子节点 (顶层 $H$) $\trianglelefteq^\mathsf I$ `lvl w` 时 (`nodeᵇ`), 参数放在 `suc (lvl w)` 层, 子树经 `emb⊴` (搬运 `tr` 再 `lift`) 嵌入, 折叠证明是 `zero`, 与 Correspond 的 `⟦hψ d⟧ᴴ` 同形; `lvl w` $\prec^\mathsf I H$ 时 (`nodeᵃ`), 直接以 `r : w′ <ᴵ H` 折叠子树, 再 `tr⁻` 回到 `lvl w`. 两种节点的顶层都**恰好**是 `lvl w`, 所以翻译的层号只由下标决定, 不随证据变. `norm⊴`: `nodeᵇ` 模 $\cong$ 等于 "以 `simE c : Simᴵ (rep⊴ c) (suc W)` 直接折叠搬运后的子树", 这是后面所有层引理的入口.

```agda
emb⊴ : ∀ {a b} → a ⊴ᴵ b → Ordᶜ a → Ordᶜ b
emb⊴ (eqv e)   x = tr e x
emb⊴ (sub e r) x = lift r (tr e x)

rep⊴ : ∀ {a b} → a ⊴ᴵ b → Ordᴵ
rep⊴ {b = b} (eqv e) = b
rep⊴ (sub {a′} e r) = a′

toRep : ∀ {a b} (c : a ⊴ᴵ b) → a ≅ᴵ rep⊴ c
toRep (eqv e)   = e
toRep (sub e r) = e

simE : ∀ {a b} (c : a ⊴ᴵ b) → Simᴵ (rep⊴ c) (suc b)
simE (eqv e)   q = suc q
simE (sub e r) q = suc (<◃ q r)

emb⊴-≅ : ∀ {a b ℓ} (c : a ⊴ᴵ b) {x : Ordᶜ a} {y : Ordᶜ ℓ} → x ≅ y → emb⊴ c x ≅ y
emb⊴-≅ (eqv e)   d = tr-≅ e d
emb⊴-≅ (sub e r) d = lift-≅ r (tr-≅ e d)

nodeᵇ : ∀ {H W} → H ⊴ᴵ W → Ordᶜ H → Ordᶜ W
nodeᵇ c x = ψ zero (λ q → q) (up zero (emb⊴ c x))

nodeᵃ : ∀ {K W} → W ≺ᴵ K → Ordᶜ K → Ordᶜ W
nodeᵃ (via e r) x = tr⁻ e (ψ r (λ q → q) x)

norm⊴ : ∀ {a b} (c : a ⊴ᴵ b) {x : Ordᶜ a} → x ≅ x → nodeᵇ c x ≅ ψ zero (simE c) (tr (toRep c) x)
norm⊴ {b = b} c ex = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = simE c} (≅ᴵ-refl b)
  (emb⊴-≅ c (≅-tr (toRep c) ex))
```

`norm⊴` 第一次写成 `ψ-≅ {σ = λ q → q} … (upˡ (emb⊴-≅ …))` 时报 `[UnsolvedConstraints] ψ zero (λ q → q) (up _r_301 _x_302) = ψ zero suc (emb⊴ c x)` (blocked on `_r_301`), 即 Correspond §2 记录的同一个坑: `ψ p σ (up zero x)` 定义性地归约成 `ψ p (λ q → σ (suc q)) x`, 引理必须直接以 `σ = λ q → suc q` 陈述.

## §4 两种形状谓词

`ShΩ X N S`: 树 $X$ (在它自己的层 $K$) $\cong$ 某个 `limᵢ q f`, 指标层 $j\cong^\mathsf I N$, 且分支在 $x\cong y$ 处 $\cong S\,y$ ($S$ 是 "把叶子换成 $y$ 后的翻译"). `ShL X Mf Z`: $X\cong\lim G$ 且 $G\,n\cong Z\,n$, $Z\,n$ 的层号可随 $n$ 变 (极限叶子 $\Omega_{u[n]}$ 的层号正是如此). 要求 `limᵢ`/`lim` 在 $X$ **自己的层**上, 是因为后面要把 `ψ p σ X` 换成 `ψ p σ (limᵢ q f)` 再让派发计算, 这要同一个 `σ`. 换层用搬运: `tr e (limᵢ q f)` 字面上又是 `limᵢ` (`ShΩ-tr`, 经 `back-≅`), `tr e (lim G)` 字面上是 `lim` (`ShL-tr`). 基础情形: $\Omega_{N+1}$ 字面上是 `limᵢ zero (up zero)` (`ShΩ-Ω`, 分支在 $x$ 处就是 $x$), $\Omega_{\lim f}$ 字面上是 `lim` (`ShL-Ω`).

```agda
ShΩ : ∀ {K M} → Ordᶜ K → (N : Ordᴵ) → (Ordᶜ N → Ordᶜ M) → Set
ShΩ {K} X N S = Σ Ordᴵ λ j → Σ (j <ᴵ K) λ q → Σ (U j (<→◃ q) → Ordᶜ K) λ f →
  (j ≅ᴵ N) × (X ≅ limᵢ q f) × (∀ (x : Ordᶜ j) (y : Ordᶜ N) → x ≅ y → f (into (<→◃ q) x) ≅ S y)

ShL : ∀ {K} → Ordᶜ K → (Mf : ℕ → Ordᴵ) → ((n : ℕ) → Ordᶜ (Mf n)) → Set
ShL {K} X Mf Z = Σ (ℕ → Ordᶜ K) λ G → (X ≅ lim G) × (∀ n → G n ≅ Z n)

ShΩ-resp : ∀ {K M N} {X X′ : Ordᶜ K} {S : Ordᶜ N → Ordᶜ M} → X′ ≅ X → ShΩ X N S → ShΩ X′ N S
ShΩ-resp d (j , q , f , ej , eX , hf) = j , q , f , ej , ≅-trans d eX , hf

ShL-resp : ∀ {K Mf Z} {X X′ : Ordᶜ K} → X′ ≅ X → ShL X Mf Z → ShL X′ Mf Z
ShL-resp d (G , eX , hG) = G , ≅-trans d eX , hG

ShΩ-tr : ∀ {a b N M} (e : a ≅ᴵ b) {X : Ordᶜ a} {S : Ordᶜ N → Ordᶜ M} → ShΩ X N S → ShΩ (tr e X) N S
ShΩ-tr e {S = S} (j , q , f , ej , eX , hf) =
  R.rep (res q e) , q′ , _ , ≅ᴵ-trans (≅ᴵ-sym (R.eq (res q e))) ej , ≅-tr e (tr-≅ e eX) ,
  λ x y d → subst (λ w → tr e (f (into (<→◃ q) (R.back (res q e) w))) ≅ S y) (sym (out-into (<→◃ q′) x))
                  (tr-≅ e (hf _ y (back-≅ q e d)))
  where q′ = R.lt (res q e)

ShL-tr : ∀ {a b Mf Z} (e : a ≅ᴵ b) {X : Ordᶜ a} → ShL X Mf Z → ShL (tr e X) Mf Z
ShL-tr e (G , eX , hG) = (λ n → tr e (G n)) , ≅-tr e (tr-≅ e eX) , λ n → tr-≅ e (hG n)

ShΩ-Ω : ∀ {A N} → A ≅ᴵ suc N → ShΩ (Ω A) N (λ y → y)
ShΩ-Ω {suc A′} (s≅ e) = A′ , zero , up zero , e , Ω-refl (suc A′) , λ x y d → upˡ d

ShL-Ω : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} → ShL (Ω (lim f s)) f (λ n → Ω (f n))
ShL-Ω {f} = (λ n → up (self n) (Ω (f n))) , Ω-refl (lim _ _) , λ n → upˡ (Ω-refl (f n))
```

## §5 派发一致引理与层引理

**`pen⁺`.** 对任意 `p : i <ᴵ k`, `σ`, `q : j <ᴵ K`: 若 $j\cong^\mathsf I N$ 且 $N\prec^\mathsf I i$, 则 `ψ p σ (limᵢ q f)` 字面地等于穿透节点 (`refl`, `with <ᴵ-dec (σ q) p` 把目标里同一个调用一起抽象掉). 第二、三支 ($i\prec j$ 或 $i\cong j$) 都与 $N\prec i$ 矛盾 ($\prec^\mathsf I$ 无自反). 这就是 Correspond §9 `pen` 的一般形式: 证据可以是任意代表元, 树侧的选择 (哪个 `via`) 无关紧要. 记号侧对应的是 `Pen (cmpᵀ (sucT ν) w)` (§6 的 `fsTc-pen`/`cofψ₊-pen`).

```agda
pen⁺ : ∀ {i k K j N} {p : i <ᴵ k} {σ : Simᴵ K k} {q : j <ᴵ K} {f : U j (<→◃ q) → Ordᶜ K} →
       j ≅ᴵ N → N ≺ᴵ i →
       Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
       ψ p σ (limᵢ q f) ≡ limᵢ r (λ y → ψ p σ (f (into (<→◃ q) (tr⁻ e (out (<→◃ r) y)))))
pen⁺ {p = p} {σ = σ} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))
```

层引理. `ΩL-be`: 子树有 $\Omega$-形状且 $N\prec^\mathsf I W$, 则 be-节点仍有 $\Omega$-形状, 分支是 "同一个节点作用在 $S\,y$ 上" (子节点证据可换成任意 `c′`, 因为叶子换成 $y$ 后子节点的层号变了). `LL-be` 是极限版. `Ψ⁰L`/`Ψ⁰Ω` 是最外层的 $\psi_0$: 后者把 `ψ⁰ (limᵢ q f)` 的链 `iter (λ x → ψ q id (f x)) (Ω j)` 逐项对到 `chainᵃ ab S` (每步是一个 ab-节点 $\psi_\nu(S\,\cdot)$), 即规则 6 的 $\gamma_{k+1}=\psi_\nu(b[\gamma_k])$.

```agda
ΩL-be : ∀ {H W N M} (c : H ⊴ᴵ W) (c′ : M ⊴ᴵ W) {X : Ordᶜ H} {S : Ordᶜ N → Ordᶜ M} →
        ShΩ X N S → N ≺ᴵ W → ShΩ (nodeᵇ c X) N (λ y → nodeᵇ c′ (S y))
ΩL-be {W = W} c c′ {X} {S} sh νW with sh | ShΩ-tr (toRep c) sh
... | (_ , _ , _ , _ , eX₀ , _) | (j , q , f , ej , eX , hf)
  with pen⁺ {p = zero} {σ = simE c} {q = q} {f = f} ej νW
... | j′ , e , r , eqn = j′ , r , _ , ≅ᴵ-trans (≅ᴵ-sym e) ej ,
  ≅-trans (norm⊴ c (≅-reflˡ eX₀))
          (subst (λ Z → ψ zero (simE c) (tr (toRep c) X) ≅ Z) eqn
                 (ψ-≅ {p = zero} {σ = simE c} {p′ = zero} {σ′ = simE c} (≅ᴵ-refl W) eX)) ,
  λ x y d → subst (λ w → ψ zero (simE c) (f (into (<→◃ q) (tr⁻ e w))) ≅ nodeᵇ c′ (S y))
                  (sym (out-into (<→◃ r) x))
                  (ψ-≅ {p = zero} {σ = simE c} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl W)
                       (fix (hf _ y (tr⁻-≅ e d))))
  where
  fix : ∀ {ℓ} {Z : Ordᶜ ℓ} {y} → Z ≅ S y → Z ≅ emb⊴ c′ (S y)
  fix h = ≅-trans h (≅-sym (emb⊴-≅ c′ (≅-reflʳ h)))

LL-be : ∀ {H W Mf Z} (c : H ⊴ᴵ W) (cs : ∀ n → Mf n ⊴ᴵ W) {X : Ordᶜ H} →
        ShL X Mf Z → ShL (nodeᵇ c X) (λ _ → W) (λ n → nodeᵇ (cs n) (Z n))
LL-be {W = W} {Z = Z} c cs {X} (G , eX , hG) =
  (λ n → ψ zero (simE c) (tr (toRep c) (G n))) ,
  ≅-trans (norm⊴ c (≅-reflˡ eX))
          (ψ-≅ {p = zero} {σ = simE c} {p′ = zero} {σ′ = simE c} (≅ᴵ-refl W) (≅-tr (toRep c) (tr-≅ (toRep c) eX))) ,
  λ n → ψ-≅ {p = zero} {σ = simE c} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl W)
            (≅-trans (tr-≅ (toRep c) (hG n)) (≅-sym (emb⊴-≅ (cs n) (≅-reflʳ (hG n)))))

Ψ⁰L : ∀ {K Mf Z} {X : Ordᶜ K} → ShL X Mf Z → ψ⁰ X ≅ lim (λ n → ψ⁰ (Z n))
Ψ⁰L (G , eX , hG) = ≅-trans (ψ⁰-≅ eX) (l≅ (λ n → ψ⁰-≅ (hG n)))

chainᵃ : ∀ {N M} → N ≺ᴵ M → (Ordᶜ N → Ordᶜ M) → ℕ → Ordᶜ N
chainᵃ {N} ab S = iter (λ y → nodeᵃ ab (S y)) (Ω N)

Ψ⁰Ω : ∀ {K N M} {X : Ordᶜ K} {S : Ordᶜ N → Ordᶜ M} (ab : N ≺ᴵ M) → ShΩ X N S →
      ψ⁰ X ≅ lim (λ n → ψ⁰ (S (chainᵃ ab S n)))
Ψ⁰Ω {N = N} {S = S} (via e r) (j , q , f , ej , eX , hf) =
  ≅-trans (ψ⁰-≅ eX) (l≅ (λ n → ψ⁰-≅ (hf _ _ (chn n))))
  where
  chn : ∀ n → iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n ≅ chainᵃ (via e r) S n
  chn zero    = Ω-≅ ej
  chn (suc n) = ≅-tr⁻ e (ψ-≅ {p = q} {σ = λ r → r} {p′ = r} {σ′ = λ r → r} (≅ᴵ-trans ej e) (hf _ _ (chn n)))
```

ab-节点 (`nodeᵃ = tr⁻ e ∘ ψ r id`) 的层引理先对裸的 `ψ p σ` 证 (`ΩL-ψ`, `LL-ψ`), 再经 `ShΩ-tr⁻`/`ShL-tr⁻` 搬回. 第一次直接写 `ΩL-ab (via e r) sh νW = ShΩ-tr⁻ e (ΩL-ψ sh …)` 报 `[UnequalTerms] a′ != W of type Ordᴵ`: 搬运不改分支规格, 规格仍是 `ψ r id (S y)` 而不是 `nodeᵃ ab (S y)`; 修复是规格的 $\cong$-重写 `ShΩ-spec`/`ShL-spec` (只要求 "$\cong S\,y$ 的都 $\cong S'\,y$", 不要求 $S\,y$ 自反).

```agda
ShΩ-spec : ∀ {K M M′ N} {X : Ordᶜ K} {S : Ordᶜ N → Ordᶜ M} {S′ : Ordᶜ N → Ordᶜ M′} →
           (∀ {ℓ} {Z : Ordᶜ ℓ} y → Z ≅ S y → Z ≅ S′ y) → ShΩ X N S → ShΩ X N S′
ShΩ-spec k (j , q , f , ej , eX , hf) = j , q , f , ej , eX , λ x y d → k y (hf x y d)

ShL-spec : ∀ {K Mf Mf′ Z Z′} {X : Ordᶜ K} → (∀ {ℓ} {Y : Ordᶜ ℓ} n → Y ≅ Z n → Y ≅ Z′ n) →
           ShL X Mf Z → ShL {K} X Mf′ Z′
ShL-spec k (G , eX , hG) = G , eX , λ n → k n (hG n)

ShΩ-tr⁻ : ∀ {a b N M} (e : a ≅ᴵ b) {X : Ordᶜ b} {S : Ordᶜ N → Ordᶜ M} → ShΩ X N S → ShΩ (tr⁻ e X) N S
ShΩ-tr⁻ e {S = S} (j , q , f , ej , eX , hf) =
  R.rep (res⁻ q e) , q′ , _ , ≅ᴵ-trans (≅ᴵ-sym (R.eq (res⁻ q e))) ej , ≅-tr⁻ e (tr⁻-≅ e eX) ,
  λ x y d → subst (λ w → tr⁻ e (f (into (<→◃ q) (R.back (res⁻ q e) w))) ≅ S y) (sym (out-into (<→◃ q′) x))
                  (tr⁻-≅ e (hf _ y (back⁻-≅ q e d)))
  where q′ = R.lt (res⁻ q e)

ShL-tr⁻ : ∀ {a b Mf Z} (e : a ≅ᴵ b) {X : Ordᶜ b} → ShL X Mf Z → ShL (tr⁻ e X) Mf Z
ShL-tr⁻ e (G , eX , hG) = (λ n → tr⁻ e (G n)) , ≅-tr⁻ e (tr⁻-≅ e eX) , λ n → tr⁻-≅ e (hG n)

ΩL-ψ : ∀ {i k K N} {p : i <ᴵ k} {σ : Simᴵ K k} {X : Ordᶜ K} {S : Ordᶜ N → Ordᶜ K} →
       ShΩ X N S → N ≺ᴵ i → ShΩ (ψ p σ X) N (λ y → ψ p σ (S y))
ΩL-ψ {i} {p = p} {σ = σ} {X} {S} (j , q , f , ej , eX , hf) νi
  with pen⁺ {p = p} {σ = σ} {q = q} {f = f} ej νi
... | j′ , e , r , eqn = j′ , r , _ , ≅ᴵ-trans (≅ᴵ-sym e) ej ,
  subst (λ Z → ψ p σ X ≅ Z) eqn (ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) eX) ,
  λ x y d → subst (λ w → ψ p σ (f (into (<→◃ q) (tr⁻ e w))) ≅ ψ p σ (S y)) (sym (out-into (<→◃ r) x))
                  (ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) (hf _ y (tr⁻-≅ e d)))

LL-ψ : ∀ {i k K} {p : i <ᴵ k} {σ : Simᴵ K k} {X : Ordᶜ K} {Z : ℕ → Ordᶜ K} →
       ShL X (λ _ → K) Z → ShL (ψ p σ X) (λ _ → i) (λ n → ψ p σ (Z n))
LL-ψ {i} {p = p} {σ = σ} (G , eX , hG) =
  (λ n → ψ p σ (G n)) , ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) eX ,
  λ n → ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) (hG n)

ΩL-ab : ∀ {W K N} (ab : W ≺ᴵ K) {X : Ordᶜ K} {S : Ordᶜ N → Ordᶜ K} →
        ShΩ X N S → N ≺ᴵ W → ShΩ (nodeᵃ ab X) N (λ y → nodeᵃ ab (S y))
ΩL-ab (via e r) sh νW = ShΩ-spec (λ y h → ≅-tr⁻ e h) (ShΩ-tr⁻ e (ΩL-ψ sh (≺ᴵ-respʳ νW e)))

LL-ab : ∀ {W K} (ab : W ≺ᴵ K) {X : Ordᶜ K} {Z : ℕ → Ordᶜ K} →
        ShL X (λ _ → K) Z → ShL (nodeᵃ ab X) (λ _ → W) (λ n → nodeᵃ ab (Z n))
LL-ab (via e r) sh = ShL-spec (λ n h → ≅-tr⁻ e h) (ShL-tr⁻ e (LL-ψ sh))
```

## §6 检验一: 出口路径

**单层的带证据推导.** 为了先单独检验三个出口项, 这里用一个最小的类: 脊 `Sp` (叶子 `sΩ`, be-节点 `sᵇ`, ab-节点 `sᵃ`, 下标用 Correspond 的 $\mathbb G$ 推导) 与 $\psi_0$ 包装 `𝕂`. `K1 gw gv c` 是 $\psi_0(\psi_w(\Omega_v))$ 带证据 `c : lvl gv ⊴ᴵ lvl gw` 的推导. `K1-lim` ($v$ 极限): 树 $\cong\lim F$, 第 $n$ 项 $\cong$ `K1 gw gₙ cₙ`, 其中 $g_n$ 是 `Ω-shapeω` 给的 $v[n]$ 的推导, **证据 `cₙ` 现场制造**: `sub (≅ᴵ-sym eₙ) (self n)` 接 `lvl gv ⊴ᴵ lvl gw`. `K1-suc` ($v=\nu+1$): 第 $n$ 项 $\cong$ $\psi_0(\psi_w(\gamma_n))$ 的推导, $\gamma_0=\Omega_\nu$, $\gamma_{k+1}=\psi_\nu(\psi_w(\gamma_k))$ (`chD`, ab-节点 $\psi_\nu$ 的证据 `ab = suc⊴→≺ eL c`, be-节点 $\psi_w$ 的证据 `cN`), 证明是 `Ψ⁰Ω ab (ΩL-be c cN (ShΩ-Ω eL) ab)`: 唯一的派发 ($\psi_w$ 处) 由 `pen⁺` 判为穿透.

```agda
data Sp : T → Ordᴵ → Set where
  sΩ : ∀ {v} (g : 𝔾 v) → Sp (Ωt v) (lvl g)
  sᵇ : ∀ {w h H} (gw : 𝔾 w) → Sp h H → H ⊴ᴵ lvl gw → Sp (ψᵗ w h ∷ []) (lvl gw)
  sᵃ : ∀ {w h H} (gw : 𝔾 w) → Sp h H → lvl gw ≺ᴵ H → Sp (ψᵗ w h ∷ []) (lvl gw)

⟦_⟧ˢ : ∀ {h H} → Sp h H → Ordᶜ H
⟦ sΩ g ⟧ˢ      = Ω (lvl g)
⟦ sᵇ gw d c ⟧ˢ = nodeᵇ c ⟦ d ⟧ˢ
⟦ sᵃ gw d a ⟧ˢ = nodeᵃ a ⟦ d ⟧ˢ

data 𝕂 : T → Set where
  k0 : ∀ {h H} → Sp h H → 𝕂 (ψᵗ [] h ∷ [])

⟦_⟧ᵏ : ∀ {t} → 𝕂 t → Ordᶜ zero
⟦ k0 d ⟧ᵏ = ψ⁰ ⟦ d ⟧ˢ

nodeᵇ-≅ : ∀ {H H′ W W′} (c : H ⊴ᴵ W) (c′ : H′ ⊴ᴵ W′) {x : Ordᶜ H} {y : Ordᶜ H′} → W ≅ᴵ W′ → x ≅ y → nodeᵇ c x ≅ nodeᵇ c′ y
nodeᵇ-≅ c c′ eW d = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} eW
  (emb⊴-≅ c (≅-sym (emb⊴-≅ c′ (≅-sym d))))

K1 : ∀ {w v} (gw : 𝔾 w) (gv : 𝔾 v) → lvl gv ⊴ᴵ lvl gw → 𝕂 (ψᵗ [] (ψᵗ w (Ωt v) ∷ []) ∷ [])
K1 gw gv c = k0 (sᵇ gw (sΩ gv) c)

K1-lim : ∀ {w x xs} (gw : 𝔾 w) (gv : 𝔾 (x ∷ xs)) → Pure gv → cof (x ∷ xs) ≡ cω → (c : lvl gv ⊴ᴵ lvl gw) →
  Σ (ℕ → Ordᶜ zero) λ F → (⟦ K1 gw gv c ⟧ᵏ ≅ lim F) ×
  (∀ n → Σ (𝔾 (fsn (x ∷ xs) n)) λ gn → Σ (lvl gn ⊴ᴵ lvl gw) λ cn → F n ≅ ⟦ K1 gw gn cn ⟧ᵏ)
K1-lim {w} gw gv pv e c with Ω-shapeω gv pv e
... | F′ , hF , eL , hM , _ =
  (λ n → ψ⁰ (nodeᵇ (cs n) (Ω (Ln n)))) ,
  Ψ⁰L (LL-be c cs (ShL-resp (≅-tr (≅ᴵ-sym eL) (Ω-≅ eL)) (ShL-tr (≅ᴵ-sym eL) ShL-Ω))) ,
  λ n → proj₁ (hM n) , cn n , ψ⁰-≅ (nodeᵇ-≅ (cs n) (cn n) (≅ᴵ-refl (lvl gw)) (Ω-≅ (en n)))
  where
  Ln : ℕ → Ordᴵ
  Ln n = toLevel (F′ n) (hl₁ hF n)
  toW : toLevel (lim F′) hF ⊴ᴵ lvl gw
  toW = ⊴-trans (eqv (≅ᴵ-sym eL)) c
  cs : ∀ n → Ln n ⊴ᴵ lvl gw
  cs n = ⊴-trans (sub (≅ᴵ-refl (Ln n)) (self n)) toW
  en : ∀ n → Ln n ≅ᴵ lvl (proj₁ (hM n))
  en n = toLevel-≅ (hl₁ hF n) (cert (proj₁ (hM n))) (proj₂ (hM n))
  cn : ∀ n → lvl (proj₁ (hM n)) ⊴ᴵ lvl gw
  cn n = ⊴-trans (sub (≅ᴵ-sym (en n)) (self n)) toW

chT : T → T → ℕ → T
chT w ν zero    = Ωt ν
chT w ν (suc k) = ψᵗ ν (ψᵗ w (chT w ν k) ∷ []) ∷ []

chD : ∀ {w ν} (gw : 𝔾 w) (g′ : 𝔾 ν) → lvl g′ ≺ᴵ lvl gw → lvl g′ ⊴ᴵ lvl gw → ∀ n → Sp (chT w ν n) (lvl g′)
chD gw g′ ab cN zero    = sΩ g′
chD gw g′ ab cN (suc n) = sᵃ g′ (sᵇ gw (chD gw g′ ab cN n) cN) ab

chD-eq : ∀ {w ν} (gw : 𝔾 w) (g′ : 𝔾 ν) ab cN n → ⟦ chD gw g′ ab cN n ⟧ˢ ≡ chainᵃ ab (nodeᵇ cN) n
chD-eq gw g′ ab cN zero    = refl
chD-eq gw g′ ab cN (suc n) = cong (λ y → nodeᵃ ab (nodeᵇ cN y)) (chD-eq gw g′ ab cN n)

K1-suc : ∀ {w x xs} (gw : 𝔾 w) (gv : 𝔾 (x ∷ xs)) → Pure gv → cof (x ∷ xs) ≡ c1 → (c : lvl gv ⊴ᴵ lvl gw) →
  Σ (𝔾 (pred (x ∷ xs))) λ g′ → Pure g′ × Σ (lvl g′ ≺ᴵ lvl gw) λ ab → Σ (lvl g′ ⊴ᴵ lvl gw) λ cN →
  ⟦ K1 gw gv c ⟧ᵏ ≅ lim (λ n → ⟦ k0 (sᵇ gw (chD gw g′ ab cN n) cN) ⟧ᵏ)
K1-suc gw gv pv e c with Ω-shape1 gv pv e
... | g′ , p′ , eL , _ , _ = g′ , p′ , ab , cN ,
  ≅-trans (Ψ⁰Ω ab (ΩL-be c cN (ShΩ-Ω eL) ab))
          (l≅ (λ n → subst (λ Z → ψ⁰ (nodeᵇ cN (chainᵃ ab (nodeᵇ cN) n)) ≅ ψ⁰ (nodeᵇ cN Z))
                            (sym (chD-eq gw g′ ab cN n)) (≅-refl⁰ _)))
  where
  ab = suc⊴→≺ eL c
  cN = ⊴-trans (pred⊴ (lvl g′)) (⊴-trans (eqv (≅ᴵ-sym eL)) c)
```

记号侧的两条规则化简 (与 Correspond §4 一样只用 J-对齐): `fs-K1lim` ($\psi_0(\psi_w(\Omega_v))[n]=\psi_0(\psi_w(\Omega_{v[n]}))$, 两次规则 5ω 加奇异叶) 与 `Suc.fs-K1suc` ($v=\nu+1\le w$ 时 $\psi_0(\psi_w(\Omega_v))[n]=\psi_0(\psi_w(\gamma_n))$: 先 `fsn₊-eq`/`fsn↓c-gt` 化到规则 6, 再 `fsTb` 证 $b[\eta]=\psi_w(\eta)$, 用的正是 `Pen` 判定的穿透 `fsTc-pen`).

```agda
fs-K1lim : ∀ w x xs → cof (x ∷ xs) ≡ cω → ∀ n →
  fsn (ψᵗ [] (ψᵗ w (Ωt (x ∷ xs)) ∷ []) ∷ []) n ≡ ψᵗ [] (ψᵗ w (Ωt (fsn (x ∷ xs) n)) ∷ []) ∷ []
fs-K1lim w x xs e n =
  trans (fs-ω [] (ψᵗ w (Ωt (x ∷ xs))) [] (cong (cofA w) e₂) n)
        (cong (λ z → ψᵗ [] z ∷ [])
              (trans (fs-ω w (ψᵗ (x ∷ xs) []) [] e₂ n) (cong (λ z → ψᵗ w z ∷ []) (E.fsn0-eq x xs n e))))
  where e₂ = cong (cofψ0 (x ∷ xs)) e


cofψ₊-pen : ∀ u ν m → Pen m → cofψ₊ u ν m ≡ cΩ ν
cofψ₊-pen u ν .lt (inj₁ refl) = refl
cofψ₊-pen u ν .eq (inj₂ refl) = refl

fsTc-pen : ∀ u b ν m → Pen m → ∀ η → E.fsTc u b ν m η ≡ ψᵗ u (fsT b η) ∷ []
fsTc-pen u b ν .lt (inj₁ refl) η = refl
fsTc-pen u b ν .eq (inj₂ refl) η = refl

module Suc (w : T) (x : PT) (xs : T) (e : cof (x ∷ xs) ≡ c1) (hm : Pen (cmpᵀ (sucT (pred (x ∷ xs))) w)) where
  v = x ∷ xs
  ν = pred v
  b = ψᵗ w (Ωt v) ∷ []

  cofΩ : cof (Ωt v) ≡ cΩ ν
  cofΩ = cong (cofψ0 v) e

  cofb : cof b ≡ cΩ ν
  cofb = trans (cong (cofA w) cofΩ) (cofψ₊-pen w ν (cmpᵀ (sucT ν) w) hm)

  fsT₊-pen : ∀ c → c ≡ cΩ ν → ∀ η → E.fsT₊ w (Ωt v) c η ≡ ψᵗ w (fsT (Ωt v) η) ∷ []
  fsT₊-pen .(cΩ ν) refl η = fsTc-pen w (Ωt v) ν (cmpᵀ (sucT ν) w) hm η

  fsTb : ∀ η → fsT b η ≡ ψᵗ w η ∷ []
  fsTb η = trans (fsT₊-pen (cof (Ωt v)) cofΩ η) (cong (λ z → ψᵗ w z ∷ []) (fsT-c1 v (cof v) e η))

  γ-ch : ∀ n → γT b ν n ≡ chT w ν n
  γ-ch zero    = refl
  γ-ch (suc n) = cong (λ z → ψᵗ ν z ∷ []) (trans (fsTb _) (cong (λ z → ψᵗ w z ∷ []) (γ-ch n)))

  fs-K1suc : ∀ n → fsn (ψᵗ [] b ∷ []) n ≡ ψᵗ [] (ψᵗ w (chT w ν n) ∷ []) ∷ []
  fs-K1suc n =
    trans (E.fsn₊-eq [] (ψᵗ w (Ωt v)) [] n cofb)
    (trans (fsn↓c-gt [] (ψᵗ w (Ωt v)) [] ν cofb (cmpᵀ (sucT ν) []) (cmp-suc[] ν) n)
           (cong (λ z → ψᵗ [] z ∷ [])
                 (trans (E.fsT↓-trm b cofb (dec g))
                 (trans (cong (fsT b) (E.γ↓-trm b ν cofb n))
                 (trans (fsTb _) (cong (λ z → ψᵗ w z ∷ []) (γ-ch n)))))))
    where g = E.γ↓ b ν cofb n
```

**三个项.** `exit₁`–`exit₃` 是 Correspond §10 的路径 ($\gamma^\mathsf E_2[1][2][2][1]=\psi_0(\Omega_{\omega+1})$, 再 $[1]$, 再 $[2]$). `shape₁` 是纯片段的 `corr`. $\psi_0(\psi_\omega(\Omega_\omega))$ 在 Correspond 里的推导是链项 `gH`, `agree₂` 说它的翻译与本文的 `K₂` 模 $\cong$ 相同. `shape₂ = K1-lim gω gω pω refl _`. 第三项的证据 `c₃` 直接从 `shape₂` 的第 2 项取出 (那里的 $g_2$ 归约后与手写的 `g2` 有同一棵树, `≅-refl⁰ _` 由定义性相等通过); 第一次用 `with proj₂ (proj₂ shape₂) 2` 取, 报 `[UnequalTerms] suc (add … zero) != ⟦ gn ⟧` (`with` 把 $g_n$ 抽象成变量), 改用投影即过. `shape₃ = K1-suc gω g2 p2 refl c₃`, `fs₃` 是它的记号侧 (句法证据 `inj₁ refl`: `cmpᵀ 2 ω ≡ lt`).

```agda
ω+1ᵗ : T
ω+1ᵗ = ψᵗ [] (ψᵗ [] [] ∷ []) ∷ ψᵗ [] [] ∷ []

gω : 𝔾 ωᵗ
gω = g∷ (gψ (g∷ (gψ g[]) g[])) g[]

pω : Pure gω
pω = (tt , tt) , tt

gω+1 : 𝔾 ω+1ᵗ
gω+1 = g∷ (gψ (g∷ (gψ g[]) g[])) (g∷ (gψ g[]) g[])

g2 : 𝔾 (natT 2)
g2 = g∷ (gψ g[]) (g∷ (gψ g[]) g[])

p2 : Pure g2
p2 = tt , tt , tt

t₁ t₂ t₃ : T
t₁ = ψᵗ [] (Ωt ω+1ᵗ) ∷ []
t₂ = ψᵗ [] (ψᵗ ωᵗ (Ωt ωᵗ) ∷ []) ∷ []
t₃ = ψᵗ [] (ψᵗ ωᵗ (Ωt (natT 2)) ∷ []) ∷ []

exit₁ : fsn (fsn (fsn (fsn (γᴱ 2) 1) 2) 2) 1 ≡ t₁
exit₁ = refl
exit₂ : fsn t₁ 1 ≡ t₂
exit₂ = refl
exit₃ : fsn t₂ 2 ≡ t₃
exit₃ = refl

shape₁ : Shape (g∷ (gΩ gω+1) g[])
shape₁ = corr (g∷ (gΩ gω+1) g[]) (((tt , tt) , (tt , tt)) , tt)

K₂ : 𝕂 t₂
K₂ = K1 gω gω (eqv (≅ᴵ-refl (lvl gω)))

agree₂ : ⟦ g∷ (gH gω (hψ hΩ)) g[] ⟧ ≅ ⟦ K₂ ⟧ᵏ
agree₂ = ψ⁰-≅ (ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl (lvl gω))
                   (≅-tr (≅ᴵ-refl (lvl gω)) (Ω-refl (lvl gω))))

shape₂ = K1-lim gω gω pω refl (eqv (≅ᴵ-refl (lvl gω)))

fs₂ : ∀ n → fsn t₂ n ≡ ψᵗ [] (ψᵗ ωᵗ (Ωt (fsn ωᵗ n)) ∷ []) ∷ []
fs₂ = fs-K1lim ωᵗ (ψᵗ [] (ψᵗ [] [] ∷ [])) [] refl

c₃ : lvl g2 ⊴ᴵ lvl gω
c₃ = ⊴-trans (eqv (toLevel-≅ (cert g2) (cert (proj₁ b₂)) (≅-refl⁰ _))) (proj₁ (proj₂ b₂))
  where b₂ = proj₂ (proj₂ shape₂) 2

K₃ : 𝕂 t₃
K₃ = K1 gω g2 c₃

shape₃ = K1-suc gω g2 p2 refl c₃

fs₃ : ∀ n → fsn t₃ n ≡ ψᵗ [] (ψᵗ ωᵗ (chT ωᵗ (natT 1) n) ∷ []) ∷ []
fs₃ = Suc.fs-K1suc ωᵗ (ψᵗ [] []) (ψᵗ [] [] ∷ []) refl (inj₁ refl)

_ : fsn t₃ 1 ≡ ψᵗ [] (ψᵗ ωᵗ (ψᵗ (natT 1) (ψᵗ ωᵗ (Ωt (natT 1)) ∷ []) ∷ []) ∷ []) ∷ []
_ = refl
```

**检验一的结论.** 三个项都有带证据的推导, 一步形状模 $\cong$ 与记号逐项一致; 第三项正是 Correspond §12 说 "要 `lvl 2 ≺ᴵ lvl ω` 才能 lift" 的那个项. 实际需要的是 $2\trianglelefteq^\mathsf I\omega$ (放置 $\Omega_2$, 来自 `self 2`) 与 $1\prec^\mathsf I\omega$ (派发, 来自 `suc⊴→≺`), 都是现场造的.

## §7 一般的脊片段 $\mathbb K^+$

把 §6 推广到任意多层. 下标改用 $\varepsilon_0$ 片段 $\mathbb E$ 的推导 (Correspond §8): `corrE` 给出的后继/各项推导仍在 $\mathbb E$ 里, 所以叶子可以无限次地下降 (用 $\mathbb G$ 的话, `Ω-shapeω` 给的 `Match` 不保证纯, 第二步就接不上 `corr`). 层号 `lvlE g = lvl (emb g)`; `ΩshE1`/`ΩshEω` 是 Correspond `Ω-shape1`/`Ω-shapeω` 的 $\mathbb E$ 版.

上下文 `Cx C H I`: 以 `C : T → PT` 为项 (项是 `C h ∷ []`, $h$ 是洞), $H$ 是最外层层号, $I$ 是最内层层号; 构造子 `one` (最内层, 洞在 be-位置), `cᵇ`, `cᵃ`. `fillC c ev x` 把第 $L$ 层的树 $x$ 放进洞 (`ev : L ⊴ᴵ I`). 不变量 `Inv c v L`: 每一层 $w$ 都有 `Le v w` (句法 $v\le w$) 与 $L\trianglelefteq^\mathsf I$ `lvlE gw`. `CxΩ`/`CxL` 对上下文归纳地使用 §5 的层引理; `plug` 把一个上下文插进另一个的洞 (`fillC-plug` 是 `refl` 的归纳).

```agda
lvlE : ∀ {t} → 𝔼 t → Ordᴵ
lvlE g = lvl (emb g)

ΩshE1 : ∀ {x xs} (g : 𝔼 (x ∷ xs)) → cof (x ∷ xs) ≡ c1 → Σ (𝔼 (pred (x ∷ xs))) λ g′ → lvlE g ≅ᴵ suc (lvlE g′)
ΩshE1 {x} {xs} g e with subst (λ c → ShE ⟦ emb g ⟧ c (x ∷ xs)) e (corrE g)
... | g′ , eg = g′ , toLevel-≅ (cert (emb g)) (hs (cert (emb g′))) eg

ΩshEω : ∀ {x xs} (g : 𝔼 (x ∷ xs)) → cof (x ∷ xs) ≡ cω →
        Σ (ℕ → Ordᶜ zero) λ F → Σ (HS (lim F)) λ hF → (lvlE g ≅ᴵ toLevel (lim F) hF) × (∀ n → MatchE (fsn (x ∷ xs) n) (F n))
ΩshEω {x} {xs} g e with subst (λ c → ShE ⟦ emb g ⟧ c (x ∷ xs)) e (corrE g)
... | F , eF , hF = F , HS-≅ eF (cert (emb g)) , toLevel-≅ (cert (emb g)) (HS-≅ eF (cert (emb g))) eF , hF

data Cx : (T → PT) → Ordᴵ → Ordᴵ → Set where
  one : ∀ {w} (gw : 𝔼 w) → Cx (λ h → ψᵗ w h) (lvlE gw) (lvlE gw)
  cᵇ  : ∀ {w C H I} (gw : 𝔼 w) → Cx C H I → H ⊴ᴵ lvlE gw → Cx (λ h → ψᵗ w (C h ∷ [])) (lvlE gw) I
  cᵃ  : ∀ {w C H I} (gw : 𝔼 w) → Cx C H I → lvlE gw ≺ᴵ H → Cx (λ h → ψᵗ w (C h ∷ [])) (lvlE gw) I

fillC : ∀ {C H I} → Cx C H I → ∀ {L} → L ⊴ᴵ I → Ordᶜ L → Ordᶜ H
fillC (one gw)     ev x = nodeᵇ ev x
fillC (cᵇ gw c e)  ev x = nodeᵇ e (fillC c ev x)
fillC (cᵃ gw c a)  ev x = nodeᵃ a (fillC c ev x)

nodeᵃ-≅ : ∀ {K W} (a : W ≺ᴵ K) {x y : Ordᶜ K} → x ≅ y → nodeᵃ a x ≅ nodeᵃ a y
nodeᵃ-≅ (via e r) d = tr⁻-≅ e (≅-tr⁻ e (ψ-≅ {p = r} {σ = λ q → q} {p′ = r} {σ′ = λ q → q} (≅ᴵ-refl _) d))

fillC-≅ : ∀ {C H I} (c : Cx C H I) {L L′} (ev : L ⊴ᴵ I) (ev′ : L′ ⊴ᴵ I) {x : Ordᶜ L} {y : Ordᶜ L′} →
          x ≅ y → fillC c ev x ≅ fillC c ev′ y
fillC-≅ (one gw)    ev ev′ d = nodeᵇ-≅ ev ev′ (≅ᴵ-refl _) d
fillC-≅ (cᵇ gw c e) ev ev′ d = nodeᵇ-≅ e e (≅ᴵ-refl _) (fillC-≅ c ev ev′ d)
fillC-≅ (cᵃ gw c a) ev ev′ d = nodeᵃ-≅ a (fillC-≅ c ev ev′ d)

Le : T → T → Set
Le v w = Pen (cmpᵀ v w)

Inv : ∀ {C H I} → Cx C H I → T → Ordᴵ → Set
Inv (one {w} gw)    v L = Le v w × (L ⊴ᴵ lvlE gw)
Inv (cᵇ {w} gw c _) v L = Le v w × (L ⊴ᴵ lvlE gw) × Inv c v L
Inv (cᵃ {w} gw c _) v L = Le v w × (L ⊴ᴵ lvlE gw) × Inv c v L

innerEv : ∀ {C H I} (c : Cx C H I) {v L} → Inv c v L → L ⊴ᴵ I
innerEv (one gw)    i = proj₂ i
innerEv (cᵇ gw c _) i = innerEv c (proj₂ (proj₂ i))
innerEv (cᵃ gw c _) i = innerEv c (proj₂ (proj₂ i))

outerEv : ∀ {C H I} (c : Cx C H I) {v L} → Inv c v L → L ⊴ᴵ H
outerEv (one gw)    i = proj₂ i
outerEv (cᵇ gw c _) i = proj₁ (proj₂ i)
outerEv (cᵃ gw c _) i = proj₁ (proj₂ i)

Inv-map : ∀ {C H I} (c : Cx C H I) {v v′ L L′} →
          (∀ {w W} → Le v w → L ⊴ᴵ W → Le v′ w × (L′ ⊴ᴵ W)) → Inv c v L → Inv c v′ L′
Inv-map (one gw)    k (le , lw)     = k le lw
Inv-map (cᵇ gw c _) k (le , lw , i) = proj₁ (k le lw) , proj₂ (k le lw) , Inv-map c k i
Inv-map (cᵃ gw c _) k (le , lw , i) = proj₁ (k le lw) , proj₂ (k le lw) , Inv-map c k i

CxΩ : ∀ {C H I} (c : Cx C H I) {v L N} → Inv c v L → L ≅ᴵ suc N →
      ∀ {L′} (ev : L′ ⊴ᴵ I) {X : Ordᶜ L′} {M} {S : Ordᶜ N → Ordᶜ M} (evS : M ⊴ᴵ I) →
      ShΩ X N S → ShΩ (fillC c ev X) N (λ y → fillC c evS (S y))
CxΩ (one gw)    (_ , lw)     eL ev evS sh = ΩL-be ev evS sh (suc⊴→≺ eL lw)
CxΩ (cᵇ gw c e) (_ , lw , i) eL ev evS sh = ΩL-be e e (CxΩ c i eL ev evS sh) (suc⊴→≺ eL lw)
CxΩ (cᵃ gw c a) (_ , lw , i) eL ev evS sh = ΩL-ab a (CxΩ c i eL ev evS sh) (suc⊴→≺ eL lw)

CxL : ∀ {C H I} (c : Cx C H I) {L′} (ev : L′ ⊴ᴵ I) {X : Ordᶜ L′} {Mf Z} (evs : ∀ n → Mf n ⊴ᴵ I) →
      ShL X Mf Z → ShL (fillC c ev X) (λ _ → H) (λ n → fillC c (evs n) (Z n))
CxL (one gw)    ev evs sh = LL-be ev evs sh
CxL (cᵇ gw c e) ev evs sh = LL-be e (λ _ → e) (CxL c ev evs sh)
CxL (cᵃ gw c a) ev evs sh = LL-ab a (CxL c ev evs sh)

plug : ∀ {C H I D H′ I′} → Cx C H I → Cx D H′ I′ → H′ ⊴ᴵ I → Cx (λ h → C (D h ∷ [])) H I′
plug (one gw)    d ev = cᵇ gw d ev
plug (cᵇ gw c e) d ev = cᵇ gw (plug c d ev) e
plug (cᵃ gw c a) d ev = cᵃ gw (plug c d ev) a

fillC-plug : ∀ {C H I D H′ I′} (c : Cx C H I) (d : Cx D H′ I′) (ev : H′ ⊴ᴵ I) {L} (evL : L ⊴ᴵ I′) (x : Ordᶜ L) →
             fillC (plug c d ev) evL x ≡ fillC c ev (fillC d evL x)
fillC-plug (one gw)    d ev evL x = refl
fillC-plug (cᵇ gw c e) d ev evL x = cong (nodeᵇ e) (fillC-plug c d ev evL x)
fillC-plug (cᵃ gw c a) d ev evL x = cong (nodeᵃ a) (fillC-plug c d ev evL x)

Inv-plug : ∀ {C H I D H′ I′} (c : Cx C H I) {d : Cx D H′ I′} {ev : H′ ⊴ᴵ I} {v L} →
           Inv c v L → Inv d v L → Inv (plug c d ev) v L
Inv-plug (one gw)    (le , lw)     id = le , lw , id
Inv-plug (cᵇ gw c e) (le , lw , i) id = le , lw , Inv-plug c i id
Inv-plug (cᵃ gw c a) (le , lw , i) id = le , lw , Inv-plug c i id
```

记号侧: `fsC` (极限叶子: 每层规则 5ω), `fsTC` (后继叶子: 每层规则 5Ω, 用 `Inv` 的句法部分), `Cn` 是规则 6 链的上下文 ($C_{k+1}(h)=C(\psi_\nu(C_k(h)))$). `Chain` 模块里: `Bc n` 是第 $n$ 项的上下文 (`plug c (cᵃ gν (Bc k) ab) evN`), `Bc-fill` 说它的翻译字面地是 `Ψ⁰Ω` 的链, `Inv-Bc` 现场重建不变量 (新层 $\psi_\nu$: `cmpᵀ-refl`, `≅ᴵ-refl`). $\mathbb K^+$ 与形状 `ShK`.

```agda
fsC : ∀ {C H I} (c : Cx C H I) {y ys} → cof (y ∷ ys) ≡ cω →
      (cof (C (y ∷ ys) ∷ []) ≡ cω) × (∀ n → fsn (C (y ∷ ys) ∷ []) n ≡ C (fsn (y ∷ ys) n) ∷ [])
fsC (one {w} gw) {y} {ys} e = cong (cofA w) e , fs-ω w y ys e
fsC (cᵇ {w} {C} gw c _) {y} {ys} e with fsC c e
... | ec , fc = cong (cofA w) ec , λ n → trans (fs-ω w (C (y ∷ ys)) [] ec n) (cong (λ z → ψᵗ w z ∷ []) (fc n))
fsC (cᵃ {w} {C} gw c _) {y} {ys} e with fsC c e
... | ec , fc = cong (cofA w) ec , λ n → trans (fs-ω w (C (y ∷ ys)) [] ec n) (cong (λ z → ψᵗ w z ∷ []) (fc n))

fsT₊-pen′ : ∀ u b ν c → c ≡ cΩ ν → Pen (cmpᵀ (sucT ν) u) → ∀ η → E.fsT₊ u b c η ≡ ψᵗ u (fsT b η) ∷ []
fsT₊-pen′ u b ν .(cΩ ν) refl hm η = fsTc-pen u b ν _ hm η

fsTC : ∀ {C H I} (c : Cx C H I) {ν L} → Inv c (sucT ν) L → ∀ {y ys} → cof (y ∷ ys) ≡ cΩ ν →
       (cof (C (y ∷ ys) ∷ []) ≡ cΩ ν) × (∀ η → fsT (C (y ∷ ys) ∷ []) η ≡ C (fsT (y ∷ ys) η) ∷ [])
fsTC (one {w} gw) {ν} (le , _) {y} {ys} e =
  trans (cong (cofA w) e) (cofψ₊-pen w ν _ le) , fsT₊-pen′ w (y ∷ ys) ν _ e le
fsTC (cᵇ {w} {C} gw c _) {ν} (le , _ , i) {y} {ys} e with fsTC c i e
... | ec , fc = trans (cong (cofA w) ec) (cofψ₊-pen w ν _ le) ,
  λ η → trans (fsT₊-pen′ w (C (y ∷ ys) ∷ []) ν _ ec le η) (cong (λ z → ψᵗ w z ∷ []) (fc η))
fsTC (cᵃ {w} {C} gw c _) {ν} (le , _ , i) {y} {ys} e with fsTC c i e
... | ec , fc = trans (cong (cofA w) ec) (cofψ₊-pen w ν _ le) ,
  λ η → trans (fsT₊-pen′ w (C (y ∷ ys) ∷ []) ν _ ec le η) (cong (λ z → ψᵗ w z ∷ []) (fc η))

Cn : (T → PT) → T → ℕ → (T → PT)
Cn C ν zero    = C
Cn C ν (suc k) = λ h → C (ψᵗ ν (Cn C ν k h ∷ []) ∷ [])

module Chain {C H I ν} (c : Cx C H I) (gν : 𝔼 ν) (ab : lvlE gν ≺ᴵ H) (evN : lvlE gν ⊴ᴵ I)
             (iν : Inv c ν (lvlE gν)) where
  N = lvlE gν
  S : Ordᶜ N → Ordᶜ H
  S y = fillC c evN y

  Bc : ∀ n → Cx (Cn C ν n) H I
  Bc zero    = c
  Bc (suc k) = plug c (cᵃ gν (Bc k) ab) evN

  Bc-fill : ∀ n → fillC (Bc n) evN (Ω N) ≡ S (chainᵃ ab S n)
  Bc-fill zero    = refl
  Bc-fill (suc k) = trans (fillC-plug c (cᵃ gν (Bc k) ab) evN evN (Ω N))
                          (cong (λ z → fillC c evN (nodeᵃ ab z)) (Bc-fill k))

  Inv-Bc : ∀ n → Inv (Bc n) ν N
  Inv-Bc zero    = iν
  Inv-Bc (suc k) = Inv-plug c iν (inj₂ (cmpᵀ-refl ν) , eqv (≅ᴵ-refl N) , Inv-Bc k)

data K⁺ : T → Set where
  kk : ∀ {C H I v} (c : Cx C H I) (gv : 𝔼 v) → Inv c v (lvlE gv) → K⁺ (ψᵗ [] (C (Ωt v) ∷ []) ∷ [])

⟦_⟧⁺ : ∀ {t} → K⁺ t → Ordᶜ zero
⟦ kk c gv i ⟧⁺ = ψ⁰ (fillC c (innerEv c i) (Ω (lvlE gv)))

MatchK : T → Ordᶜ zero → Set
MatchK s X = Σ (K⁺ s) λ k → X ≅ ⟦ k ⟧⁺

MatchK-≡ : ∀ {s s′ X} → s ≡ s′ → MatchK s′ X → MatchK s X
MatchK-≡ refl m = m

ShK : T → Ordᶜ zero → Set
ShK t X = (cof t ≡ cω) × Σ (ℕ → Ordᶜ zero) λ F → (X ≅ lim F) × (∀ n → MatchK (fsn t n) (F n))
```

**闭包定理.** `K-lim`: 叶子 $v$ 极限, 第 $n$ 项是 $\psi_0(C(\Omega_{v[n]}))$, 新不变量 `i′ n` 现场制造 (句法 `Pen-desc (dec (fsn↓ x xs n))`, 树侧 `⊴-trans (cn n)`). `K-suc`: 叶子 $v=\nu+1$, 每一层由 `CxΩ` 穿透 (派发经 `pen⁺`), 最外层 $\psi_0$ 折叠, 第 $n$ 项是 $\psi_0(C_n(\Omega_\nu))$ (`Bc n`), 新不变量 `iν` (句法 `Pen-desc (pred-< v e)`) 与 `Inv-Bc`. `K-shape` 合起来: 对每个叶子非零的 $\mathbb K^+$ 推导, `cof t ≡ cω`, 树 $\cong\lim F$, 每个 $F\,n$ 匹配 `fsn t n` 的 $\mathbb K^+$ 推导. `c0` 由 `cof-ne` 排除, `cΩ` 由 `corrE` 排除 ($\mathbb E$ 项可数).

```agda
K-lim : ∀ {C H I x xs} (c : Cx C H I) (gv : 𝔼 (x ∷ xs)) (i : Inv c (x ∷ xs) (lvlE gv)) → cof (x ∷ xs) ≡ cω →
        ShK (ψᵗ [] (C (Ωt (x ∷ xs)) ∷ []) ∷ []) ⟦ kk c gv i ⟧⁺
K-lim {C} {H} {I} {x} {xs} c gv i e with ΩshEω gv e | fsC c {y = ψᵗ (x ∷ xs) []} {ys = []} (cong (cofψ0 (x ∷ xs)) e)
... | F′ , hF , eL , hM | ec , fc =
  cong (cofA []) ec ,
  (λ n → ψ⁰ (fillC c (evs n) (Ω (Ln n)))) ,
  Ψ⁰L (CxL c ev evs (ShL-resp (≅-tr (≅ᴵ-sym eL) (Ω-≅ eL)) (ShL-tr (≅ᴵ-sym eL) ShL-Ω))) ,
  λ n → MatchK-≡ (fsE n) (kk c (gn n) (i′ n) , ψ⁰-≅ (fillC-≅ c (evs n) (innerEv c (i′ n)) (Ω-≅ (en n))))
  where
  v = x ∷ xs
  ev = innerEv c i
  Ln : ℕ → Ordᴵ
  Ln n = toLevel (F′ n) (hl₁ hF n)
  toI : toLevel (lim F′) hF ⊴ᴵ I
  toI = ⊴-trans (eqv (≅ᴵ-sym eL)) ev
  evs : ∀ n → Ln n ⊴ᴵ I
  evs n = ⊴-trans (sub (≅ᴵ-refl (Ln n)) (self n)) toI
  gn : ∀ n → 𝔼 (fsn v n)
  gn n = proj₁ (hM n)
  en : ∀ n → Ln n ≅ᴵ lvlE (gn n)
  en n = toLevel-≅ (hl₁ hF n) (cert (emb (gn n))) (proj₂ (hM n))
  cn : ∀ n → lvlE (gn n) ⊴ᴵ lvlE gv
  cn n = ⊴-trans (sub (≅ᴵ-sym (en n)) (self n)) (eqv (≅ᴵ-sym eL))
  i′ : ∀ n → Inv c (fsn v n) (lvlE (gn n))
  i′ n = Inv-map c (λ le lw → inj₁ (Pen-desc (dec (E.fsn↓ x xs n)) le) , ⊴-trans (cn n) lw) i
  fsE : ∀ n → fsn (ψᵗ [] (C (Ωt v) ∷ []) ∷ []) n ≡ ψᵗ [] (C (Ωt (fsn v n)) ∷ []) ∷ []
  fsE n = trans (fs-ω [] (C (Ωt v)) [] ec n)
                (cong (λ z → ψᵗ [] z ∷ []) (trans (fc n) (cong (λ z → C z ∷ []) (E.fsn0-eq x xs n e))))

K-suc : ∀ {C H I x xs} (c : Cx C H I) (gv : 𝔼 (x ∷ xs)) (i : Inv c (x ∷ xs) (lvlE gv)) → cof (x ∷ xs) ≡ c1 →
        ShK (ψᵗ [] (C (Ωt (x ∷ xs)) ∷ []) ∷ []) ⟦ kk c gv i ⟧⁺
K-suc {C} {H} {I} {x} {xs} c gv i e with ΩshE1 gv e
... | g′ , eL = cofT , (λ n → ψ⁰ (S (chainᵃ ab S n))) , Ψ⁰Ω ab (CxΩ c i eL ev evN (ShΩ-Ω eL)) ,
  λ n → MatchK-≡ (fsS n) (kk (Bc n) g′ (Inv-Bc n) ,
     subst (λ Z → ψ⁰ Z ≅ ⟦ kk (Bc n) g′ (Inv-Bc n) ⟧⁺) (Bc-fill n)
           (ψ⁰-≅ (fillC-≅ (Bc n) evN (innerEv (Bc n) (Inv-Bc n)) (Ω-refl (lvlE g′)))))
  where
  v = x ∷ xs
  ν = pred v
  ev = innerEv c i
  ab = suc⊴→≺ eL (outerEv c i)
  N⊴V : lvlE g′ ⊴ᴵ lvlE gv
  N⊴V = ⊴-trans (pred⊴ (lvlE g′)) (eqv (≅ᴵ-sym eL))
  evN = ⊴-trans N⊴V ev
  iν : Inv c ν (lvlE g′)
  iν = Inv-map c (λ le lw → inj₁ (Pen-desc (E.pred-< v e) le) , ⊴-trans N⊴V lw) i
  open Chain c g′ ab evN iν
  is : Inv c (sucT ν) (lvlE gv)
  is = subst (λ z → Inv c z (lvlE gv)) (sym (E.pred-suc v e)) i
  b = C (Ωt v) ∷ []
  cofΩ : cof (Ωt v) ≡ cΩ ν
  cofΩ = cong (cofψ0 v) e
  cofb : cof b ≡ cΩ ν
  cofb = proj₁ (fsTC c is cofΩ)
  fsTb : ∀ η → fsT b η ≡ C η ∷ []
  fsTb η = trans (proj₂ (fsTC c is cofΩ) η) (cong (λ z → C z ∷ []) (fsT-c1 v (cof v) e η))
  γ-C : ∀ n → C (γT b ν n) ≡ Cn C ν n (Ωt ν)
  γ-C zero    = refl
  γ-C (suc k) = cong (λ z → C (ψᵗ ν z ∷ [])) (trans (fsTb _) (cong (λ z → z ∷ []) (γ-C k)))
  cofT : cof (ψᵗ [] b ∷ []) ≡ cω
  cofT = trans (cong (cofA []) cofb) (cong (cofψ₊ [] ν) (cmp-suc[] ν))
  fsS : ∀ n → fsn (ψᵗ [] b ∷ []) n ≡ ψᵗ [] (Cn C ν n (Ωt ν) ∷ []) ∷ []
  fsS n = trans (E.fsn₊-eq [] (C (Ωt v)) [] n cofb)
          (trans (fsn↓c-gt [] (C (Ωt v)) [] ν cofb (cmpᵀ (sucT ν) []) (cmp-suc[] ν) n)
                 (cong (λ z → ψᵗ [] z ∷ [])
                       (trans (E.fsT↓-trm b cofb (dec (E.γ↓ b ν cofb n)))
                       (trans (cong (fsT b) (E.γ↓-trm b ν cofb n))
                       (trans (fsTb _) (cong (λ z → z ∷ []) (γ-C n)))))))

K-shape : ∀ {C H I x xs} (c : Cx C H I) (gv : 𝔼 (x ∷ xs)) (i : Inv c (x ∷ xs) (lvlE gv)) →
          ShK (ψᵗ [] (C (Ωt (x ∷ xs)) ∷ []) ∷ []) ⟦ kk c gv i ⟧⁺
K-shape {C} {x = x} {xs} c gv i = go (cof (x ∷ xs)) refl where
  go : ∀ cc → cof (x ∷ xs) ≡ cc → ShK (ψᵗ [] (C (Ωt (x ∷ xs)) ∷ []) ∷ []) ⟦ kk c gv i ⟧⁺
  go c0     e = ⊥-elim (cof-ne x xs e)
  go c1     e = K-suc c gv i e
  go cω     e = K-lim c gv i e
  go (cΩ μ) e = ⊥-elim (subst (λ cc → ShE ⟦ emb gv ⟧ cc (x ∷ xs)) e (corrE gv))
```

## §8 入口与迭代

`entry`: Correspond 的纯片段离开时的链项 $\psi_0(\psi_\nu^{k+1}(\Omega_\nu))$ (`gH`, 由 `chainMatch` 产生) 都是 $\mathbb K^+$ 项 (be-节点叠成的上下文 `Hc`), 翻译模 $\cong$ 相同. 所以 Correspond 的 `corr` 与本文的 `K-shape` 首尾相接: 纯片段 → (规则 6) → $\mathbb K^+$.

```agda
Hf : T → ℕ → (T → PT)
Hf ν zero    = λ h → ψᵗ ν h
Hf ν (suc k) = λ h → ψᵗ ν (Hf ν k h ∷ [])

Hc : ∀ {ν} (gν : 𝔼 ν) k → Cx (Hf ν k) (lvlE gν) (lvlE gν)
Hc gν zero    = one gν
Hc gν (suc k) = cᵇ gν (Hc gν k) (eqv (≅ᴵ-refl _))

Inv-Hc : ∀ {ν} (gν : 𝔼 ν) k → Inv (Hc gν k) ν (lvlE gν)
Inv-Hc {ν} gν zero    = inj₂ (cmpᵀ-refl ν) , eqv (≅ᴵ-refl _)
Inv-Hc {ν} gν (suc k) = inj₂ (cmpᵀ-refl ν) , eqv (≅ᴵ-refl _) , Inv-Hc gν k

Hf-ch : ∀ ν k → Hf ν k (Ωt ν) ∷ [] ≡ ch ν (suc k)
Hf-ch ν zero    = refl
Hf-ch ν (suc k) = cong (λ z → ψᵗ ν z ∷ []) (Hf-ch ν k)

Hc-≅ : ∀ {ν} (gν : 𝔼 ν) k (ev : lvlE gν ⊴ᴵ lvlE gν) → ⟦ hch ν (suc k) ⟧ᴴ (lvlE gν) ≅ fillC (Hc gν k) ev (Ω (lvlE gν))
Hc-≅ gν zero ev = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl _)
  (≅-sym (emb⊴-≅ ev (Ω-refl _)))
Hc-≅ gν (suc k) ev = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl _)
  (≅-trans h (≅-sym (emb⊴-≅ (eqv (≅ᴵ-refl _)) (≅-reflʳ h))))
  where h = Hc-≅ gν k ev

entry : ∀ {ν} (gν : 𝔼 ν) k → MatchK (ψᵗ [] (ch ν (suc k)) ∷ []) ⟦ g∷ (gH (emb gν) (hch ν (suc k))) g[] ⟧
entry {ν} gν k = MatchK-≡ (cong (λ z → ψᵗ [] z ∷ []) (sym (Hf-ch ν k)))
  (kk (Hc gν k) gν (Inv-Hc gν k) , ψ⁰-≅ (Hc-≅ gν k (innerEv (Hc gν k) (Inv-Hc gν k))))
```

`K-shape′` 对任意 $\mathbb K^+$ 推导 (叶子非零由 `NZ` 计算). 沿出口路径迭代: `k₂` 是 $\psi_0(\psi_\omega(\Omega_\omega))$, `shape-k₂` 的第 2 项 `k₃` 就是 $\psi_0(\psi_\omega(\Omega_2))$ 的推导, 证据全部来自上一步; `shape-k₃ = K-shape′ (proj₁ k₃) tt` 中的 `tt` 由计算得到 (叶子是 $2\ne0$). 这就是 "证据随形状传递" 在机器上的样子.

```agda
NZ : ∀ {t} → K⁺ t → Set
NZ (kk {v = []}    c gv i) = ⊥
NZ (kk {v = _ ∷ _} c gv i) = ⊤

K-shape′ : ∀ {t} (k : K⁺ t) → NZ k → ShK t ⟦ k ⟧⁺
K-shape′ (kk {v = x ∷ xs} c gv i) _ = K-shape c gv i

ωE : 𝔼 ωᵗ
ωE = e∷ (eψ (e∷ (eψ e[]) e[])) e[]

k₂ : K⁺ t₂
k₂ = kk (one ωE) ωE (inj₂ (cmpᵀ-refl ωᵗ) , eqv (≅ᴵ-refl _))

shape-k₂ : ShK t₂ ⟦ k₂ ⟧⁺
shape-k₂ = K-shape′ k₂ tt

k₃ : MatchK t₃ _
k₃ = proj₂ (proj₂ (proj₂ shape-k₂)) 2

shape-k₃ : ShK t₃ ⟦ proj₁ k₃ ⟧⁺
shape-k₃ = K-shape′ (proj₁ k₃) tt
```

## §9 检验二: 墙

**$\mathbb K^+$ 的出口.** `K-shape` 只对叶子非零陈述. 叶子是 $\Omega_0=1$ 时, 最内层是 $\psi_w(1)$, 规则 4 给出 $\psi_w(0)\cdot n=\Omega_w+\cdots$, 参数里出现和 (`exit-0`). 出了脊片段, 参数里会有不在脊上的大 $\Omega$ (如 $\Omega_{\omega+1}+\cdots$), 它们之后再回到脊端时, 包住它们的层的下标可以**小于**脊端的叶子, 于是该层走规则 6 链且目标非零. 这样的层以后还要与下降中的叶子比较.

**精确实例.** 下面全部是 `refl` (EBO 的裸值 `fsn`, 计算很快). `walk` 沿路径取基本列. 从 $\gamma^\mathsf E_2$ 出发:

| 步 | 路径前缀 | 项 (`Rw L` = $\psi_0(\psi_{\omega+1}(\psi_\omega(\Omega_{\omega+1}+\psi_\omega(\Omega_{\omega+1}+L))))$) |
|---|---|---|
| 10 | 1,2,2,2,1,1,1,0,2,1 | `Rw (Ωt ω)` (`step₁₀`) |
| 11 | …,6 | `Rw (Ωt 6)`: $\Omega_\omega[6]=\Omega_6$ (`step₁₁`) |
| 12 | …,1 | `Rw (ψ_5(…Ω_5))`: 规则 6 在第 5 层折叠, 造出层 $\psi_5$ (`step₁₂`) |
| 19 | …,0,0,0,0,0,1,1 | `Pw (Ωt ω)` $=P$ (`wall-path`) |
| 20 | …,$n$ | `Pw (Ωt n)` (`wall-5`, `wall-6`) |

在 $P[n]$ 里, $\psi_5$ 的参数 `Q (Ωt n)` 的共尾度是 $\Omega_n$ (`arg-5`, `arg-6`, 叶子 $\Omega_n$ 已穿透 $\psi_\omega,\psi_\omega,\psi_\omega,\psi_{\omega+1}$), 而 $\psi_5$ 节点本身: $n=5$ 时穿透 (`node-5`, `cmp-5 : cmpᵀ 5 5 ≡ eq`), $n=6$ 时折叠 (`node-6`, `cmp-6 : cmpᵀ 6 5 ≡ gt`).

```agda
ψ¹ : T → T → T
ψ¹ u a = ψᵗ u a ∷ []

Q : T → T
Q L = ψ¹ ω+1ᵗ (ψ¹ ωᵗ (ψᵗ ω+1ᵗ [] ∷ ψ¹ ωᵗ (ψ¹ ωᵗ L)))

Pw : T → T
Pw L = ψ¹ [] (ψ¹ ω+1ᵗ (ψ¹ ωᵗ (ψᵗ ω+1ᵗ [] ∷ ψ¹ ωᵗ (ψᵗ ω+1ᵗ [] ∷ ψ¹ (natT 5) (Q L)))))

walk : T → List ℕ → T
walk t []       = t
walk t (n ∷ ns) = walk (fsn t n) ns

base : List ℕ
base = 1 ∷ 2 ∷ 2 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 2 ∷ 1 ∷ 6 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ []

wall-path : walk (γᴱ 2) base ≡ Pw (Ωt ωᵗ)
wall-path = refl

wall-5 : fsn (Pw (Ωt ωᵗ)) 5 ≡ Pw (Ωt (natT 5))
wall-5 = refl

wall-6 : fsn (Pw (Ωt ωᵗ)) 6 ≡ Pw (Ωt (natT 6))
wall-6 = refl

arg-5 : cof (Q (Ωt (natT 5))) ≡ cΩ (natT 4)
arg-5 = refl
arg-6 : cof (Q (Ωt (natT 6))) ≡ cΩ (natT 5)
arg-6 = refl
node-5 : cof (ψ¹ (natT 5) (Q (Ωt (natT 5)))) ≡ cΩ (natT 4)
node-5 = refl
node-6 : cof (ψ¹ (natT 5) (Q (Ωt (natT 6)))) ≡ cω
node-6 = refl
cmp-5 : cmpᵀ (sucT (natT 4)) (natT 5) ≡ eq
cmp-5 = refl
cmp-6 : cmpᵀ (sucT (natT 5)) (natT 5) ≡ gt
cmp-6 = refl

Rw : T → T
Rw L = ψ¹ [] (ψ¹ ω+1ᵗ (ψ¹ ωᵗ (ψᵗ ω+1ᵗ [] ∷ ψ¹ ωᵗ (ψᵗ ω+1ᵗ [] ∷ L))))

_ : ∀ L → Pw L ≡ Rw (ψ¹ (natT 5) (Q L))
_ = λ L → refl

base₁₀ base₁₁ base₁₂ : List ℕ
base₁₀ = 1 ∷ 2 ∷ 2 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 2 ∷ 1 ∷ []
base₁₁ = 1 ∷ 2 ∷ 2 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 2 ∷ 1 ∷ 6 ∷ []
base₁₂ = 1 ∷ 2 ∷ 2 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 2 ∷ 1 ∷ 6 ∷ 1 ∷ []

step₁₀ : walk (γᴱ 2) base₁₀ ≡ Rw (Ωt ωᵗ)
step₁₀ = refl
step₁₁ : walk (γᴱ 2) base₁₁ ≡ Rw (Ωt (natT 6))
step₁₁ = refl
step₁₂ : walk (γᴱ 2) base₁₂ ≡ Rw (ψ¹ (natT 5) (ψ¹ ω+1ᵗ (ψ¹ ωᵗ (ψᵗ ω+1ᵗ [] ∷ ψ¹ ωᵗ (ψᵗ ω+1ᵗ [] ∷ Ωt (natT 5))))))
step₁₂ = refl

exit-0 : fsn (ψ¹ [] (ψ¹ ωᵗ (Ωt []))) 2 ≡ ψ¹ [] (ψᵗ ωᵗ [] ∷ ψᵗ ωᵗ [] ∷ [])
exit-0 = refl
```

**缺的证据.** 在 $P[n]$ 的 $\psi_5$ 节点上, 记号按 `cmpᵀ (sucT ν) 5` ($\nu=n-1$) 派发; 树按 `<ᴵ-dec` 在 `lvl ν` 与 `lvl 5` 的代表元之间派发. 两者一致需要 **$(\nu,u)=(n-1,\;5)$ 的比较证据**: $n\le5$ 时 `lvl ν ≺ᴵ lvl 5` (喂给 `pen⁺`), $n\ge6$ 时 `lvl 5 ≺ᴵ lvl ν` 或 `lvl 5 ≅ᴵ lvl ν` (喂给对称的链引理). 这里 $5=\mathrm{pred}(\omega[6])$ (路径第 11–12 步), $\nu+1=n=\omega[n]$ (第 20 步); 二者是同一个下标 $\omega$ 沿不同分支 ($[6]$ 再 pred, 对 $[n]$) 的后代, 互不为后代. §2–§8 的不变量只能给出 `lvl 5 ⊴ᴵ lvl ω` 与 `lvl n ⊴ᴵ lvl ω`, 由此推不出它们之间的任何关系 (两者都只 $\trianglelefteq$ 同一个上界). 所以检验二在这里停下: `Lab (N.γ 2) (γᴱ 2)` 未证.

**能制造它的更强不变量.** 把每个下标连同它从根 (对角项的下标) 出发的基本列路径一起记录, 比较两个下标时看路径的第一个分叉 $u[m]$ 对 $u[m']$. 所需的唯一新事实是 **Bachmann 性质**: 对闭包里的极限下标 $u$ 与 $m<m'$, $u[m]$ 是 $u[m']$ 的基本列后代 (句法侧给 $<^\mathsf T$, 树侧经 Lab 结构给 $\llbracket u[m]\rrbracket\prec\llbracket u[m']\rrbracket$; 注意 `HS` 只给非严格的 $\sqsubseteq$, 不够). 有了它, 本例两种情况都能造出: $n\ge6$ 时 $5\prec\omega[6]\trianglelefteq\omega[n]$; $n\le5$ 时 $\omega[n]\trianglelefteq\omega[5]=5$ (再经 `suc⊴→≺`). 对 $\omega$ 这是自然数上的计算; 检验二要的是 $\mathbb E$ (即 $<\varepsilon_0$ 的 Cantor 标准形) 上的 Bachmann 性质, 检验三要的是一般 EBO 下标 ($<\gamma_k$) 上的, 后者正是 EBO §9 未做的标准形理论的核心部分 (需要标准形谓词与 `fsn` 保持标准形). 本文没有做.

## §10 对比表

| | Correspond | 本文 |
|---|---|---|
| 片段 | 纯 $\mathbb G$: $\psi_0$ 与 $\psi_0(\Omega_u)$ | 脊片段 $\mathbb K^+$: $\psi_0(\psi_{w_1}(\cdots\psi_{w_k}(\Omega_v)))$, 下标 $\in\mathbb E$ |
| 下标证据 | 不需要 (只有目标层 0) | 每层位置证据 (be: $\trianglelefteq^\mathsf I$, ab: $\prec^\mathsf I$) + 不变量 `Inv` (句法 `Pen` + 树侧 $\trianglelefteq^\mathsf I$) |
| 证据来源 | — | 现场制造: 极限步 `self n`, 后继步 `pred⊴`/`suc⊴→≺`, 句法 `dec`/`pred-<` + `Pen-desc` |
| 派发 | 只有 `ψ⁰` (总是规则 6) | 一般 `ψ p σ`, `pen⁺` 字面判为穿透 |
| 对 `fsn` 封闭 | 否, 出口 $\psi_0(\Omega_{\nu+1})$, $\nu\ne0$ | 叶子非零时是 (`K-shape`); 出口: 叶子到 $0$ |
| 入口 | — | `entry`: Correspond 的出口项都在 $\mathbb K^+$ 里 |
| 遗传标签 | $\gamma_1=\varepsilon_0$ (`ε₀-label`) | 无新的 (片段不闭); $\gamma_2$ 被 §9 的 $(n-1,5)$ 挡住 |

## §11 结论与边界

**字面成立 (`refl` 或定义性):** `pen⁺` 的穿透节点等式 (给定证据); `Bc-fill` (链上下文的翻译就是 `Ψ⁰Ω` 的链); `fillC-plug`; 出口路径 `exit₁`–`exit₃`; 墙的全部计算 `wall-path`, `step₁₀`–`step₁₂`, `wall-5`, `wall-6`, `arg-5/6`, `node-5/6`, `cmp-5/6`, `exit-0`; `c₃` 的取出 (定义性地同一棵树). 记号侧的规则化简 (`fs-K1lim`, `Suc.fs-K1suc`, `fsC`, `fsTC`, `K-lim`/`K-suc` 内的 `fsE`/`fsS`) 是命题等式, 只用 J-对齐.

**模 $\cong$ 成立 (定理):**

1. 检验一: `shape₁`, `shape₂ : …` (`K1-lim`), `shape₃` (`K1-suc`), `agree₂`; 证据 `c₃ : lvl g2 ⊴ᴵ lvl gω` 现场取得.
2. 一般脊片段: `K-shape : ∀ (c : Cx C H I) (gv : 𝔼 (x ∷ xs)) (i : Inv c (x ∷ xs) (lvlE gv)) → ShK (ψᵗ [] (C (Ωt (x ∷ xs)) ∷ []) ∷ []) ⟦ kk c gv i ⟧⁺`, 即 $\mathbb K^+$ (叶子非零) 对 `fsn` 封闭, 翻译逐项匹配. 子句: `K-lim` (`fsn` 极限叶子), `K-suc` (`fsn` 后继叶子, 规则 5Ω 逐层 + 规则 6), `pred` 子句不出现 ($\mathbb K^+$ 项的共尾度总是 $\omega$).
3. 派发一致: `pen⁺` (任意层、任意 `σ`), 层引理 `ΩL-be`/`ΩL-ab`/`ΩL-ψ`/`LL-be`/`LL-ab`/`LL-ψ`, `Ψ⁰Ω`/`Ψ⁰L`.
4. 入口 `entry` 与迭代 `shape-k₂`/`shape-k₃`.

**关于标签, 证了什么:** 没有新的遗传标签. 检验二 (`Lab (N.γ 2) (γᴱ 2)`) 与检验三 (`∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))`, 从而 `Lab N.BTBOᴵ (E.EBOψ 2)`) **未证**; BTBO $=\psi_0(\Omega_\Omega)$ 仍是估计. 精确的障碍是 §9 的一对 $(\nu,u)=(n-1,5)$: 项 $P[n]$ (从 $\gamma^\mathsf E_2$ 沿 `base` 19 步再 $[n]$), $\psi_5$ 节点的派发 `cmpᵀ (sucT (n-1)) 5`, 两下标是 $\omega$ 的不同分支后代. 补上它要 Bachmann 性质 (§9 末), 这是标准形理论的一段; 对 $\omega$ 平凡, 对 $\mathbb E$ 与一般 EBO 下标未做.

**其他边界.**

- 树侧的 $\prec$ 证据只在派发处由 `suc⊴→≺` 生成; 任务设想的 "`toLevel-≺` 给 `lvl (u[n]) ≺ᴵ lvl u`" 对极限 $u$ 不成立 (§2), 本文改用 $\trianglelefteq^\mathsf I$.
- §6 的单层类 (`Sp`, 下标 $\mathbb G$) 与 §7 的 $\mathbb K^+$ (下标 $\mathbb E$) 是两套推导; 前者只为单独检验出口项, 后者是一般定理, §8 的 `k₃` 说明两者在出口路径上给出同样的证据.
- 翻译依赖推导与证据; 唯一性只在用到处以 $\cong$ 核对 (`agree₂`, `entry`, `fillC-≅`).
- 不改 `src/`、`archive/` 与已有的 Align 文件.
