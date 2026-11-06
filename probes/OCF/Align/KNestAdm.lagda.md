# 嵌套 `nκ` (三): 领先量, 判据的形状

> 不含记号, 不提折叠 (只用 $A$ 上的序与加法 `⊞`). 入口 [KNest](KNest.lagda.md).
>
> [KNestNeg](KNestNeg.lagda.md) 的反例里两边回灌层相同 ($\ell=\ell'=2$), 而内层的区间是 $[1,2)$ 对 $[2,2)$: 右边起点高, 长度不够. 一个 `nκ` 在第 0 格走 $[\alpha,\ell)$ ($\alpha$ 是它的树世界), 所以两边可比要的不是 $\ell\le\ell'$, 而是**左边区间的长度放得进右边**:
>
> $$\mathrm{Adm}(\alpha,\alpha';\ell,\ell')\ :=\ \exists\delta.\ \ \ell\le\alpha\oplus\delta\ \wedge\ \alpha'\oplus\delta\le\ell'.$$
>
> 本文证它的代数 (都是定理):
>
> - **排除反例, 包含已知情形.** `¬adm-cex`: $\mathrm{Adm}(1,2;2,2)$ 不成立 (反例里 `Hℓ` 成立而它不成立, 所以它正是缺的那一条). `adm-cont`: 包含式 ($\alpha'\le\alpha$, $\ell\le\ell'$, $\alpha$ 到 $\ell$ 有字面路径) 推出它; `KVal` 的单层 `κ⊑` ($V'\le V$, `Hℓ`) 落在这里.
> - **推进与复合.** `adm-adv`: 两边各加可比的一段 (状态 $\oplus$ 可比的输出) 保持. `adm-tr`: 下标对本身满足 Adm 时可以复合 (内层 `nκ` 的树世界对 $(\beta,\beta')$ 被外层的对 $(\alpha,\alpha')$ "支配"). `adm→hℓ`: 右边起点不低时推出 `Hℓ`.
> - **只降左边的下标不保持** (`lower-left`): $\mathrm{Adm}(\beta,\alpha';\alpha,\alpha')$ ⇒ $\alpha\le\beta$. 所以若下标取 "树的世界", `nwˡ` (左边树世界降低, 折叠不变) 在这种语义下不可靠; 这是 `DVal` §3 判断 "`nw` 的两条透明律不能同时成立" 的编译形式. 出路 (判断): 下标不取树世界, 作为关系的指标单独记, `nw` 不动它.
> - **尾对齐破坏领先** (`¬adm-end`): $\mathrm{Adm}(0,\omega;\omega,\omega+1)$ 不成立. `KValCut.CutM` 在极限处把左边每个前缀的末层对到右边的末层 (尾对齐): 左边 $[0,\omega)$ 的层对到右边 $[0,\omega+1)$ 的层 $\omega$, 那一对正是这个形状 (对应关系是判断, 数值上的否定是定理). 所以嵌套时 `CutM` 的对齐要换成**首对齐** (平移).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KNestAdm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤lim⁻; irr; _⊞_; ≤⊞; ⊞-mono; ⊞-asso; ⊞-assoʳ)
open import OCF.Align.BrwMidZero using (toA; dif; dif-ok)
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KNestNeg using (two)
```

## §1 定义与代数

```agda
Adm : A → A → A → A → Set
Adm α α′ ℓ ℓ′ = Σ A (λ δ → (ℓ ≤ α ⊞ δ) × (α′ ⊞ δ ≤ ℓ′))

adm-tr : ∀ {β β′ α α′ ℓ ℓ′} → Adm β β′ α α′ → Adm α α′ ℓ ℓ′ → Adm β β′ ℓ ℓ′
adm-tr {β} {β′} (ε , a≤ , a′≥) (δ , l≤′ , l′≥) =
  (ε ⊞ δ) , ≤-trans l≤′ (≤-trans (⊞-mono a≤ (≤-refl δ)) (⊞-assoʳ β ε δ)) ,
            ≤-trans (⊞-asso β′ ε δ) (≤-trans (⊞-mono a′≥ (≤-refl δ)) l′≥)

adm-adv : ∀ {α α′ ℓ ℓ′ p p′} → Adm α α′ ℓ ℓ′ → p ≤ p′ → Adm α α′ (ℓ ⊞ p) (ℓ′ ⊞ p′)
adm-adv {α} {α′} {p = p} (δ , h , h′) pp =
  (δ ⊞ p) , ≤-trans (⊞-mono h (≤-refl p)) (⊞-assoʳ α δ p) , ≤-trans (⊞-asso α′ δ p) (⊞-mono h′ pp)

-- 字面路径给出长度 (BrwMidZero.dif)
split : ∀ {α ℓ} (q : α ⊲ ℓ) (lℓ : Lg ℓ) → Σ A (λ δ → (ℓ ≤ α ⊞ δ) × (α ⊞ δ ≤ ℓ))
split {ℓ = ℓ} q lℓ = proj₁ (toA {azero} (dif ℓ q lℓ)) , proj₂ (dif-ok {azero} ℓ q lℓ) , proj₁ (dif-ok {azero} ℓ q lℓ)

-- 包含式
adm-cont : ∀ {α α′ ℓ ℓ′} → α ⊲ ℓ → Lg ℓ → α′ ≤ α → ℓ ≤ ℓ′ → Adm α α′ ℓ ℓ′
adm-cont q lℓ a≤ le with split q lℓ
... | δ , h , h′ = δ , h , ≤-trans (⊞-mono a≤ (≤-refl δ)) (≤-trans h′ le)

-- 平移式 (右边起点不低): 领先推出 Hℓ
adm→hℓ : ∀ {α α′ ℓ ℓ′} → α ≤ α′ → Adm α α′ ℓ ℓ′ → ℓ ≤ ℓ′
adm→hℓ a≤ (δ , h , h′) = ≤-trans h (≤-trans (⊞-mono a≤ (≤-refl δ)) h′)
```

## §2 否定: 反例, 只降左边, 尾对齐

```agda
no-lead : ∀ a δ → asuc a ≤ a ⊞ δ → asuc a ⊞ δ ≤ asuc a → ⊥
no-lead a azero h _ = irr a h
no-lead a (asuc δ) _ (s≤ h) = irr a (≤-trans (≤⊞ (asuc a) δ) h)
no-lead a (alim g) h h′ with ≤lim⁻ h
... | n , hn = no-lead a (g n) hn (≤-trans (≤l n (≤-refl _)) h′)

¬adm-cex : ¬ Adm one two two two
¬adm-cex (δ , h , h′) = no-lead one δ h h′

-- a ⊞ ε ≤ a ⇒ ε 是零
absorb : ∀ a ε → a ⊞ ε ≤ a → ε ≤ azero
absorb a azero h = z≤
absorb a (asuc ε) h = ⊥-elim′ (irr a (≤-trans (s≤ (≤⊞ a ε)) h))
  where ⊥-elim′ : ⊥ → asuc ε ≤ azero
        ⊥-elim′ ()
absorb a (alim g) h = l≤ (λ n → absorb a (g n) (≤-trans (≤l n (≤-refl _)) h))

lower-left : ∀ {β α α′} → Adm β α′ α α′ → α ≤ β
lower-left {β} {α} {α′} (ε , h , h′) = ≤-trans h (⊞-mono (≤-refl β) (absorb α′ ε h′))

-- 尾对齐的那一对
fin : ℕ → A
fin zero = azero
fin (suc n) = asuc (fin n)

ωA : A
ωA = alim fin

z⊞ : ∀ δ → azero ⊞ δ ≤ δ
z⊞ azero = z≤
z⊞ (asuc δ) = s≤ (z⊞ δ)
z⊞ (alim g) = l≤ (λ n → ≤l n (z⊞ (g n)))

¬adm-end : ¬ Adm azero ωA ωA (asuc ωA)
¬adm-end (δ , h , h′) = irr (asuc ωA) (≤-trans (≤l 2 (≤-refl _)) (≤-trans (⊞-mono (≤-refl ωA) (≤-trans h (z⊞ δ))) h′))
```
