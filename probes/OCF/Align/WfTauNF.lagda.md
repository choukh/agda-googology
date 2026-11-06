# WfTauNF: τ 保标准形, 可数 EBO 标准形的良基

> 记号侧验收工作: 读记号 (EBO 的项与 bot 的标准形谓词 `isOTᵉ`, 归档 Setzer OT_I 的 `isOT`), 不是最终定义, 不进成品. 接 [WfScoutTau](WfScoutTau.lagda.md) 与 [WfScoutPull](WfScoutPull.lagda.md), 报告在 [NotationWF](../../Survey/NotationWF.md) (本文件不改它们).
>
> **结论 (都是编译过的定理, 无前提, 对一切项).**
>
> 1. **`τ-NF : isOTᵉ t ≡ true → OT (τ t)`** (§3). 侦察报告的义务 3. 陈述原样成立, 不必限于可数项, 不必改 τ. §1–§3 共 134 行非空代码 (不含导入), 低于报告的 400 到 800 行估计. 反方向 (`isOT (τ t)` 推 `isOTᵉ t`) 没有证, 也用不到.
> 2. **报告的 (G5) 引理成立, 而且比报告说的弱一点就够了 (`Gnil`, §2).** 要的只是: $w$ 标准且 $w$ 的首项下标 $<X$ 时, $G_{\Omega'_{\tau X+1}}(\tau w)=\emptyset$. 用到标准形的地方只有和的降序 (经 `hd-desc` 把 "首项下标 $<X$" 传给每一项) 与遗传性 (下标、参数也标准).
> 3. **`cl-pred` 成立, 不要 `cof t ≡ c1` 前提** (§4): `pred` 只剥末尾的 $\mathbf 1$ 或不动, 标准形对它无条件封闭. 约 15 行.
> 4. **可数 EBO 标准形上 $<^\mathsf T$ 良基, 无条件** (`wfNF`, §5). 量词限于 "标准 × 可数" 的可达性 `AccNF`, 不要求类对基本列封闭. 即 EBO 记号可数段的良基性 ("可数标准形上良基" 的形式), 无前提.
> 5. **`Std` 只剩 `cl-fsn` 一个前提** (`StdFsn`, §6): 给定标准形对可数项 `fsn` 封闭, Ω-塔 `EBOψ k` 对一切 $k$ 有带标签的树, 极限树的 FGH 逐点等于记号的 FGH.
>
> **没有做:** `cl-fsn` (报告的义务 4, 主要成本). 文末给出修订后的估计 (判断档).
>
> 编译要把归档的拷贝加进 `-i` (见文末). 本文件 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示, 无 `trustMe`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WfTauNF where

open import Data.Bool.Base using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

import OCF.Align.EBO as E
open E using (T; PT; _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<; cof; c1; cω; pred; fsn; EBOψ)
open import OCF.Align.EBOI using (isOTᵉ; isOTᵉᴾ; descᵉ; Gᵉ; Gᵉᴾ; leEᵇ; ltEᵇ; leᵇ; ltᵇ)
open import OCF.Align.Closure using (lt→<; lt→<ᴾ; eq→≡; eq→≡ᴾ; <ᵀ-trans)
open import OCF.Align.Bachmann using (gt→<)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.Level using (Ordᶜ; zero; FGH)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.AccTree using (fghₙ)
open import OCF.Align.AccTreeLab using (treeᴴ; HC→Acc)

open import Mahlo.Inacc.Syntax using (Tm; PTm; Reg; zer; _▹_; ⟨_⟩; phi; psi; Om; ΩR; eqP; isZero; isFi; isFiT)
open import Mahlo.Inacc.Order using (lt; le; _≺_)
open import Mahlo.Inacc.Closure using (isOT; isOTP; OT; ot!; G; GP; allLt)
open import Mahlo.Inacc.BoolLemmas using (∧-true; ∧-intro; if-true; if-false; eqT-refl)
open import Mahlo.Inacc.Linear using (goL)
open import Mahlo.Inacc.Lex using (leˡ; leʳ; one≺P)
open import Mahlo.Inacc.FactsImpl using (facts)
import Mahlo.Inacc.WO.Main facts as M
open import OCF.Align.WfScoutTau using (φ1; τ; τL; τP; τ-lt; τ-mono; τ-bd; monoP; notle; Ωlt; s1<)
open import OCF.Align.WfScoutPull using (module Std)
```

## §1 小工具

布尔拆合; EBO 一侧的比较分情形 (`le?`: $X\le w$ 或 $w<X$, 连同 `leEᵇ` 的值); 降序的一步 (`desc-cases`). 这些在一切项上成立.

```agda
∧₁ : ∀ {x y} → x ∧ y ≡ true → x ≡ true
∧₁ h = proj₁ (∧-true h)

∧₂ : ∀ {x y} → x ∧ y ≡ true → y ≡ true
∧₂ h = proj₂ (∧-true h)

ltᵇ→ : ∀ {m} → ltᵇ m ≡ true → m ≡ E.lt
ltᵇ→ {E.lt} _ = refl
ltᵇ→ {E.eq} ()
ltᵇ→ {E.gt} ()

data LeE (a b : T) : Set where
  yes : leEᵇ a b ≡ true  → (a <ᵀ b) ⊎ (a ≡ b) → LeE a b
  no  : leEᵇ a b ≡ false → b <ᵀ a → LeE a b

le? : ∀ a b → LeE a b
le? a b = go (E.cmpᵀ a b) refl where
  go : ∀ m → E.cmpᵀ a b ≡ m → LeE a b
  go E.lt e = yes (cong leᵇ e) (inj₁ (lt→< a b e))
  go E.eq e = yes (cong leᵇ e) (inj₂ (eq→≡ a b e))
  go E.gt e = no  (cong leᵇ e) (gt→< a b e)

desc-cases : ∀ x y → leᵇ (E.cmpᴾ y x) ≡ true → (y <ᴾ x) ⊎ (y ≡ x)
desc-cases x y d = go (E.cmpᴾ y x) refl d where
  go : ∀ m → E.cmpᴾ y x ≡ m → leᵇ m ≡ true → (y <ᴾ x) ⊎ (y ≡ x)
  go E.lt e _ = inj₁ (lt→<ᴾ y x e)
  go E.eq e _ = inj₂ (eq→≡ᴾ y x e)
  go E.gt e ()
```

Setzer 一侧: τ 把下标 $X$ 送到正则基数 $\pi_X=\Omega'_{\tau X+1}$. 门槛 $\pi_X\preceq'\Omega'_{\tau w+1}$ 恰好当 $X\le w$ (`leΩ`, `nleΩ`): 经 `τ-mono` 与 WfScoutTau 的 $+1$、$\Omega'$ 保序. 这就是报告说的 "门槛经 τ 保序且反射".

```agda
πX : T → Reg
πX X = ΩR (τ X ▹ φ1)

ΩS : T → Tm
ΩS X = ⟨ Om (τ X ▹ φ1) ⟩

leΩ : ∀ X w → (X <ᵀ w) ⊎ (X ≡ w) → le (ΩS X) (ΩS w) ≡ true
leΩ X w (inj₁ p)    = leˡ (ΩS X) (ΩS w) (Ωlt (τ X ▹ φ1) (τ w ▹ φ1) (s1< (τ X) (τ w) (τ-lt p)))
leΩ X w (inj₂ refl) = leʳ (ΩS X) (ΩS X) (eqT-refl (ΩS X))

nleΩ : ∀ X w → w <ᵀ X → le (ΩS X) (ΩS w) ≡ false
nleΩ X w p = notle (ΩS w) (ΩS X) (Ωlt (τ w ▹ φ1) (τ X ▹ φ1) (s1< (τ w) (τ X) (τ-lt p)))
```

**$G$ 沿 τ 拆成分量** (报告的两个小引理之一). Setzer 的和是 snoc 表, τ 经 `fromL = goL zer` 建成; $G_\pi$ 对 `goL` 是逐项的拼接. 另一个 (`allLt` 对 `++`) 只要引入方向.

```agda
Gs : Reg → List PTm → List Tm
Gs ρ [] = []
Gs ρ (p ∷ ps) = GP ρ p ++ Gs ρ ps

G-goL : ∀ ρ a ps → G ρ (goL a ps) ≡ G ρ a ++ Gs ρ ps
G-goL ρ a [] = sym (++-identityʳ (G ρ a))
G-goL ρ a (p ∷ ps) = trans (G-goL ρ (a ▹ p) ps) (++-assoc (G ρ a) (GP ρ p) (Gs ρ ps))

G-τ∷ : ∀ ρ x xs → G ρ (τ (x ∷ xs)) ≡ GP ρ (τP x) ++ G ρ (τ xs)
G-τ∷ ρ x xs = trans (G-goL ρ zer (τP x ∷ τL xs)) (cong (GP ρ (τP x) ++_) (sym (G-goL ρ zer (τL xs))))

all++ : ∀ xs ys b → allLt xs b ≡ true → allLt ys b ≡ true → allLt (xs ++ ys) b ≡ true
all++ [] ys b _ h = h
all++ (x ∷ xs) ys b h g = ∧-intro (∧₁ h) (all++ xs ys b (∧₂ h) g)

allLt≡ : ∀ {L L′} b → L ≡ L′ → allLt L′ b ≡ true → allLt L b ≡ true
allLt≡ b e h = subst (λ L → allLt L b ≡ true) (sym e) h
```

## §2 (G5): 首项下标在门槛之下时 $G$ 为空

Setzer 的 (G5) 是 $G_\pi(\Omega'_c)=G_\pi(c)$, 无条件地钻进 $\Omega$ 的下标; bot 的谓词在 $\psi_w(0)$ 且 $w<X$ 时直接给真. 所以要补: $w$ 标准, 首项下标 $<X$ 时 $G_{\pi_X}(\tau w)=\emptyset$.

论证 (编译在下面): 和的每一项 $\psi_v(b)$ 的下标都 $<X$. 首项由假设; 后项经降序 $\psi_{v'}(b')\le\psi_v(b)\Rightarrow v'\le v$ (`hd-desc`). 对一项 $\psi_v(b)$: $b\ne0$ 时 τ 像是 $\psi_{\Omega'_{\tau v+1}}(\tau b)$, 门槛 $\pi_X\preceq'\Omega'_{\tau v+1}$ 不成立 (`nleΩ`), 收集为空; $b=0$, $v\ne0$ 时像是 $\Omega'_{\tau v}$, (G5) 钻进 $v$, 而 $v$ 的首项下标 $<v<X$ (`idx<`: 首项下标小于项本身, 对一切项, 句法事实), 递归; $\mathbf 1$ 的像 $\varphi'_00$ 收集为空.

```agda
HdLt : T → T → Set
HdLt X [] = ⊤
HdLt X (E.ψ v b ∷ _) = v <ᵀ X

idx< : ∀ v a vs → v <ᵀ (E.ψ v a ∷ vs)
idx< [] a vs = []<
idx< (E.ψ v′ a′ ∷ vs′) a vs = hd< (lv< (idx< v′ a′ vs′))

hd-lt : ∀ X W → W <ᵀ X → HdLt X W
hd-lt X [] _ = tt
hd-lt X (E.ψ v a ∷ vs) p = <ᵀ-trans (idx< v a vs) p

hd-desc : ∀ X v b ws → descᵉ (E.ψ v b) ws ≡ true → v <ᵀ X → HdLt X ws
hd-desc X v b [] _ _ = tt
hd-desc X v b (E.ψ v′ b′ ∷ ws) d p with desc-cases (E.ψ v b) (E.ψ v′ b′) d
... | inj₁ (lv< q) = <ᵀ-trans q p
... | inj₁ (ar< q) = p
... | inj₂ refl    = p

Gnil  : ∀ X W → isOTᵉ W ≡ true → HdLt X W → G (πX X) (τ W) ≡ []
GPnil : ∀ X v b → isOTᵉᴾ (E.ψ v b) ≡ true → v <ᵀ X → GP (πX X) (τP (E.ψ v b)) ≡ []
Gnil X [] _ _ = refl
Gnil X (E.ψ v b ∷ ws) n h = trans (G-τ∷ (πX X) (E.ψ v b) ws)
  (cong₂ _++_ (GPnil X v b (∧₁ n) h) (Gnil X ws (∧₂ (∧₂ n)) (hd-desc X v b ws (∧₁ (∧₂ n)) h)))
GPnil X [] [] _ _ = refl
GPnil X (w ∷ ws) [] n h = Gnil X (w ∷ ws) n (hd-lt X (w ∷ ws) h)
GPnil X v (c ∷ cs) _ h = if-false (nleΩ X v h)
```

## §3 $G$ 条件与 τ-NF

**$G$ 条件经 τ.** bot 的 $G(X,Y)\triangleleft Z$ 推出 Setzer 的 $G_{\pi_X}(\tau Y)\prec'\tau Z$, 前提 $Y$ 标准. 逐主项: $\psi_v(c)$, $c\ne0$ 时两边的门槛一致 (`le?` 两支), 收集到的 $\tau c\prec'\tau Z$ 来自 `τ-mono`; $\psi_v(0)$ 在 $X\le v$ 时两边都钻进 $v$, 在 $v<X$ 时左边平凡真, 右边由 §2 为空. 标准形只在最后这一支用到.

```agda
Gτ  : ∀ X Y Z → isOTᵉ Y ≡ true → Gᵉ X Y Z ≡ true → allLt (G (πX X) (τ Y)) (τ Z) ≡ true
GτP : ∀ X v b Z → isOTᵉᴾ (E.ψ v b) ≡ true → Gᵉᴾ X (E.ψ v b) Z ≡ true →
      allLt (GP (πX X) (τP (E.ψ v b))) (τ Z) ≡ true
GΩ  : ∀ X W Z → isOTᵉ W ≡ true → Gᵉᴾ X (E.ψ W []) Z ≡ true → LeE X W →
      allLt (G (πX X) (τ W)) (τ Z) ≡ true
Gψ  : ∀ X v C Z → isOTᵉ v ≡ true → isOTᵉ C ≡ true → Gᵉᴾ X (E.ψ v C) Z ≡ true → LeE X v →
      allLt (GP (πX X) (psi (ΩR (τ v ▹ φ1)) (τ C))) (τ Z) ≡ true

Gτ X [] Z _ _ = refl
Gτ X (E.ψ v b ∷ ys) Z n g = allLt≡ (τ Z) (G-τ∷ (πX X) (E.ψ v b) ys)
  (all++ _ _ (τ Z) (GτP X v b Z (∧₁ n) (∧₁ g)) (Gτ X ys Z (∧₂ (∧₂ n)) (∧₂ g)))

GτP X [] [] Z _ _ = refl
GτP X (w ∷ ws) [] Z n g = GΩ X (w ∷ ws) Z n g (le? X (w ∷ ws))
GτP X v (c ∷ cs) Z n g = Gψ X v (c ∷ cs) Z (∧₁ n) (∧₁ (∧₂ n)) g (le? X v)

GΩ X W Z n g (yes l _) = Gτ X W Z n (∧₁ (∧₂ (trans (sym (if-true l)) g)))
GΩ X W Z n g (no _ p)  = allLt≡ (τ Z) (Gnil X W n (hd-lt X W p)) refl

Gψ X v C Z nv nC g (yes l q) = allLt≡ (τ Z) (if-true (leΩ X v q))
  (∧-intro (τ-lt (lt→< C Z (ltᵇ→ (∧₁ g′))))
    (all++ _ _ (τ Z) (all++ _ [] (τ Z) (Gτ X v Z nv (∧₁ (∧₂ g′))) refl) (Gτ X C Z nC (∧₂ (∧₂ g′)))))
  where g′ = trans (sym (if-true l)) g
Gψ X v C Z nv nC g (no _ p) = allLt≡ (τ Z) (if-false (nleΩ X v p)) refl
```

**侧条件.** τ 的像里没有 $I$ 与 $\psi_I$, 所以 (OT5) 的 "非 Fi′、非零" 与 (OT4) 的 "下标 $\in R'\cap$ OT" 都是形状上的事实: 和的 snoc 结构 (`goL`) 非零, 两项以上的和不是 Fi′, 单项看主项; $\tau u+1$ 的末项是 $\varphi'_00$, 在 Suc′ 里; $1\preceq'$ 任何主项 (`le1`).

```agda
fiP : ∀ w → isFi (τP w) ≡ false
fiP (E.ψ [] []) = refl
fiP (E.ψ (_ ∷ _) []) = refl
fiP (E.ψ u (_ ∷ _)) = refl

fi-goL2 : ∀ a q p ps → isFiT (goL (a ▹ q ▹ p) ps) ≡ false
fi-goL2 a q p [] = refl
fi-goL2 a q p (r ∷ rs) = fi-goL2 (a ▹ q) p r rs

fi-τ : ∀ w ws → isFiT (τ (w ∷ ws)) ≡ false
fi-τ w [] = fiP w
fi-τ w (v ∷ vs) = fi-goL2 zer (τP w) (τP v) (τL vs)

zero-goL : ∀ a p ps → isZero (goL (a ▹ p) ps) ≡ false
zero-goL a p [] = refl
zero-goL a p (r ∷ rs) = zero-goL (a ▹ p) r rs

fi1 : ∀ s → isFiT (s ▹ φ1) ≡ false
fi1 zer = refl
fi1 (a ▹ p) = refl

le1 : ∀ p → le ⟨ φ1 ⟩ ⟨ p ⟩ ≡ true
le1 p = go (eqP φ1 p) refl where
  go : ∀ b → eqP φ1 p ≡ b → le ⟨ φ1 ⟩ ⟨ p ⟩ ≡ true
  go true  e = leʳ ⟨ φ1 ⟩ ⟨ p ⟩ e
  go false e = leˡ ⟨ φ1 ⟩ ⟨ p ⟩ (one≺P p e)

snoc1 : ∀ s → isOT s ≡ true → isOT (s ▹ φ1) ≡ true
snoc1 zer _ = refl
snoc1 (a ▹ p) h = ∧-intro h (le1 p)

desc-le : ∀ x y → leᵇ (E.cmpᴾ y x) ≡ true → le ⟨ τP y ⟩ ⟨ τP x ⟩ ≡ true
desc-le x y d with desc-cases x y d
... | inj₁ p    = leˡ ⟨ τP y ⟩ ⟨ τP x ⟩ (monoP p)
... | inj₂ refl = leʳ ⟨ τP y ⟩ ⟨ τP y ⟩ (eqT-refl ⟨ τP y ⟩)
```

**主定理.** 对 `isOTᵉ` 的合取项逐一对应 (OT2)–(OT5): 和的降序 (`desc-le`, 经 `monoP`), 主项 (`τP-NF`), $G$ 条件 (`Gτ`). `nf-sum` 沿 snoc 表的累加器递归.

```agda
τ-NFᵇ  : ∀ t → isOTᵉ t ≡ true → isOT (τ t) ≡ true
τP-NF  : ∀ x → isOTᵉᴾ x ≡ true → isOTP (τP x) ≡ true
nf-sum : ∀ a x xs → isOT (a ▹ τP x) ≡ true → descᵉ x xs ≡ true → isOTᵉ xs ≡ true →
         isOT (goL (a ▹ τP x) (τL xs)) ≡ true

τ-NFᵇ [] _ = refl
τ-NFᵇ (x ∷ xs) n = nf-sum zer x xs (τP-NF x (∧₁ n)) (∧₁ (∧₂ n)) (∧₂ (∧₂ n))

nf-sum a x [] h _ _ = h
nf-sum a x (y ∷ ys) h d n =
  nf-sum (a ▹ τP x) y ys (∧-intro h (∧-intro (τP-NF y (∧₁ n)) (desc-le x y d))) (∧₁ (∧₂ n)) (∧₂ (∧₂ n))

τP-NF (E.ψ [] []) _ = refl
τP-NF (E.ψ (w ∷ ws) []) n =
  ∧-intro (τ-NFᵇ (w ∷ ws) n) (∧-intro (cong not (fi-τ w ws)) (cong not (zero-goL zer (τP w) (τL ws))))
τP-NF (E.ψ u (y ∷ ys)) n =
  ∧-intro (τ-NFᵇ (y ∷ ys) (∧₁ (∧₂ n)))
    (∧-intro (∧-intro (snoc1 (τ u) (τ-NFᵇ u (∧₁ n))) (∧-intro (cong not (fi1 (τ u))) refl))
             (Gτ u (y ∷ ys) (y ∷ ys) (∧₁ (∧₂ n)) (∧₂ (∧₂ n))))

τ-NF : ∀ {t} → isOTᵉ t ≡ true → OT (τ t)
τ-NF {t} n = ot! (τ-NFᵇ t n)
```

## §4 `cl-pred`

`pred` 剥末尾的 $\mathbf 1$, 其余情形不动 (哑值). 新的末项前面的降序关系不变, 所以标准形无条件封闭. Std 的前提带 `cof t ≡ c1`, 这里不需要.

```agda
desc-pred : ∀ x y ys → descᵉ x (y ∷ ys) ≡ true → descᵉ x (pred (y ∷ ys)) ≡ true
desc-pred x y (z ∷ zs) d = d
desc-pred x (E.ψ [] []) [] d = refl
desc-pred x (E.ψ [] (c ∷ cs)) [] d = d
desc-pred x (E.ψ (w ∷ ws) a) [] d = d

cl-pred : ∀ t → isOTᵉ t ≡ true → isOTᵉ (pred t) ≡ true
cl-pred [] _ = refl
cl-pred (x ∷ y ∷ ys) n = ∧-intro (∧₁ n) (∧-intro (desc-pred x y ys (∧₁ (∧₂ n))) (cl-pred (y ∷ ys) (∧₂ (∧₂ n))))
cl-pred (E.ψ [] [] ∷ []) _ = refl
cl-pred (E.ψ [] (c ∷ cs) ∷ []) n = n
cl-pred (E.ψ (w ∷ ws) a ∷ []) n = n
```

## §5 可数 EBO 标准形上 $<^\mathsf T$ 良基 (无前提)

可达性的分支限于 "标准且可数" 的项. 这个形式不要求类对 `pred`/`fsn` 封闭 (WfScoutPull 的 `Pull` 要, 因为它要的是 `Class.AccP`), 所以只用 `τ-NF`, `τ-mono`, `τ-bd`: 沿 τ 拉回归档的 `Acc-endpt 1`.

```agda
data AccNF (t : T) : Set where
  accNF : (∀ {b} → isOTᵉ b ≡ true → Ctbl b → b <ᵀ t → AccNF b) → AccNF t

goNF : ∀ {t} → M.Acc (τ t) → AccNF t
goNF (M.acc rs) = accNF (λ nb _ b<t → goNF (rs (τ-NF nb) (τ-mono b<t)))

wfNF : ∀ {t} → isOTᵉ t ≡ true → Ctbl t → AccNF t
wfNF n c = goNF (M.Acc-endpt 1 (τ-NF n) (τ-bd c))
```

这是 "可数标准形上良基" 的形式 (报告 §2.1 第一种). 要的是第二种 (基本列下降的良基, 进而 `HC` 与 `Lab`) 时, 还要知道 `fsn` 不离开标准形, 即 `cl-fsn`.

## §6 `Std` 只剩 `cl-fsn`

```agda
module StdFsn
  (cl-fsn : ∀ {t} → isOTᵉ t ≡ true → Ctbl t → cof t ≡ cω → ∀ n → isOTᵉ (fsn t n) ≡ true) where

  open Std (λ {t} n _ → cl-pred t n) cl-fsn τ-NF public

  -- 条件定理 (前提只有 cl-fsn), 原样重述类型
  ebo-lab′ : ∀ k → Lab (treeᴴ (hc (p-tower k))) (EBOψ k)
  ebo-lab′ = ebo-lab

  EBO-tree′ : Ordᶜ zero
  EBO-tree′ = EBO-tree

  fgh-EBO′ : ∀ n → FGH EBO-tree n ≡ fghₙ (EBOψ n) (HC→Acc (hc (p-tower n))) n
  fgh-EBO′ = fgh-EBO

  lab-NF : ∀ {t} (nf : isOTᵉ t ≡ true) (c : Ctbl t) → Lab (treeᴴ (hc (nf , c))) t
  lab-NF nf c = lab (nf , c)
```

## 结论与估计

**定理表.**

| 名字 | 陈述 | 档 |
|---|---|---|
| `τ-NF` | `isOTᵉ t ≡ true → OT (τ t)`, 一切项 | 定理, 无前提 |
| `Gnil` | $w$ 标准, 首项下标 $<X$ ⟹ $G_{\Omega'_{\tau X+1}}(\tau w)=\emptyset$ | 定理 |
| `Gτ` | $Y$ 标准, $G(X,Y)\triangleleft Z$ ⟹ $G_{\Omega'_{\tau X+1}}(\tau Y)\prec'\tau Z$ | 定理 |
| `cl-pred` | `isOTᵉ t ≡ true → isOTᵉ (pred t) ≡ true`, 不要 `cof` 前提 | 定理, 无前提 |
| `wfNF` | 可数标准形上 $<^\mathsf T$ 的可达性 `AccNF`, 对一切可数标准形 | 定理, 无前提 |
| `StdFsn.ebo-lab′`, `fgh-EBO′`, `lab-NF` | Ω-塔对一切 $k$ 有 `Lab`; 极限树 FGH 逐点等于记号 FGH; 一切可数标准形有 `Lab` | 定理, 前提只有 `cl-fsn` |

**第一个障碍** 现在是 `cl-fsn` (标准形对可数项的 `fsn` 封闭). τ 一侧的义务全部是定理.

**`cl-fsn` 的修订估计 (判断档, 不是定理).** 本次只有第 1 条是新信息, 它让外壳变便宜, 不碰核心.

1. **τ-NF 的实际成本约是报告估计的 1/4** (约 130 行代码 vs 400–800). 原因: 归档的序论 (`lt` 的线性、传递, `Lex`) 已把 Setzer 一侧的比较变成几个现成引理, 证明几乎全是逐形状的布尔拆合. 同类的布尔拆合在 `cl-fsn` 里也占大头 (`isOTᵉ` 的合取项对每条基本列规则), 这部分可以按本文件的写法 (以 `LeE` 一类视图代替 `with` 改写目标) 压缩.
2. **`cl-fsn` 的数学核心不在布尔拆合, 本次的引理帮不上.** 核心是 Buchholz 3.4–3.6 的 $G$ 界: 规则 6 的输出 $\psi_u(b[\gamma_n])$ 要 $G_u(b[\gamma_n])<b[\gamma_n]$, Lean 用相对不变量 `Trian` ($b\lhd_z a$: $b<a$ 且对 $c\in(b,a]$ 有 $G_u(b)\preceq G_u(c)\cup G^0_u(z)$, 手册 §5.3). 本次的 `Gnil` 是静态的 (固定的项、门槛之下为空), 形状不同, 不能推广成 `Trian`. 可复用的只有 τ 一侧的 $G$ 拆分 (`G-τ∷`, `all++`) 与比较视图 (`LeE`, `desc-cases`).
3. **Ω-基本列绕不开.** 规则 6 的 `fsT`/`γT` 链要对一般项下标一起归纳. 这一条沿用报告 §2.3 的判断, 本次没有重新考察.

据此: `cl-fsn` 判断 **2500 到 5000 行** (报告是 3000 到 7000), 其中 $G$ 界与 `Trian` 一路 2000 到 4000, `Sum` 与布尔外壳 500 到 1000. 下调的依据只有第 1 条 (外壳更便宜), 核心部分的倍数仍不可靠. 全路线剩余约 2500 到 5000 行.

**编译.** 归档只读, 用拷贝: 把 `archive/src/Mahlo` 拷到个人临时目录 `<arch>/`, 加 `<arch>/arch.agda-lib`:

```text
name: wftaunf-arch
depend: standard-library-2.4
include: .
flags: --hidden-argument-puns -W noUnsupportedIndexedMatch
```

然后在仓库根 `agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes -i <arch> probes/OCF/Align/WfTauNF.lagda.md`.
