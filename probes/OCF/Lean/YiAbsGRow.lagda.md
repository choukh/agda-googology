# 抽象理论 (十): 行律推出保持与读法

> 判决: 编译定理, 无前提; 只导入标准库与 `YiAbs*`. 某层的关系若由六条规则生成 (`Gen`: 零, 后继, ℕ 极限, 结点, 嵌入, 放宽), 则折到低层的保持归约到折叠像对这六条封闭 (`gen→low`), 树读成层号归约到读法对这六条封闭 (`gen→lift`).
> 每条封闭各有一步的充分条件, 分成参照一侧的等式与树一侧的行: 零行 (`row-zero`), 放宽 (`row-weak`), ℕ 极限 (`row-lim`), 结点保留 (`row-node-keep`), 结点对角 (`row-node-diag`, 用回灌链), 嵌入经一致目标的交接 (`row-up`), 折到自身的嵌入经上折 (`row-self-up`).
> 读法除四条外还要两条: 嵌入读成和 (`lU`), 沿第一位置序放宽 (`lw`). 不给出什么: 后继行没有分解, 作前提; 不构造任何关系.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsGRow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface

module Row {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
           (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
```

## 生成

`Rules ℓ Q`: 谓词 Q 对第 ℓ 层的六条规则封闭 (每条规则同时给出 R 的前提与 Q 的归纳假设). `Gen ℓ`: 第 ℓ 层的关系含于每个这样的 Q, 即 R 由这六条生成.

```agda
  record Rules (ℓ : Lv) (Q : T → Tr ℓ → Set) : Set where
    field
      qz : ∀ {t x} → C0 t → Q t x
      q1 : ∀ {t x} → C1 t → R ℓ (pred t) x → Q (pred t) x → Q t (sc x)
      qL : ∀ {t x} → Cω t → (∀ n → R ℓ (fsn t n) x) → (∀ n → Q (fsn t n) x) → Q t x
      qΩ : (p : Sl ℓ) {t κ : T} (g : SlT ℓ p → Tr ℓ) → CΩ t κ → Nu ℓ p κ
         → (∀ η c → R (slL ℓ p) η (slT ℓ p c) → R ℓ (fsT t η) (g c))
         → (∀ η c → R (slL ℓ p) η (slT ℓ p c) → Q (fsT t η) (g c)) → Q t (nd p g)
      qU : (c : Ch ℓ) {t s : T} {x : Tr ℓ} (y : ChT ℓ c) → R ℓ t x → Q t x → R (chL ℓ c) s (chT ℓ c y)
         → Q (t ⊕ s) (up x c y)
      qw : ∀ {t x x′} → R ℓ t x → Q t x → x ◃ x′ → Q t x′

  Gen : Lv → Set₁
  Gen ℓ = (Q : T → Tr ℓ → Set) → Rules ℓ Q → ∀ {t x} → R ℓ t x → Q t x

  wk⊴ : Weak → ∀ {ℓ t} {x x′ : Tr ℓ} → R ℓ t x → x ⊴ x′ → R ℓ t x′
  wk⊴ wk r (inj₁ refl) = r
  wk⊴ wk r (inj₂ d)    = wk r d
```

## 折到低层

固定层号 ℓ, 目标 j, 底, 路径, 底值, 上下文. 折叠像 `Q t x`: 折叠后的树对着 `app K t`.

```agda
  module Low {ℓ j : Lv} (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (K : Cx ℓ j) where

    F : Tr ℓ → Tr j
    F x = ψ ℓ b j w β x

    Q : T → Tr ℓ → Set
    Q t x = R j (app K t) (F x)

    gen→low : Gen ℓ → Rules ℓ Q → ∀ {a x} → R ℓ a x → R j (app K a) (ψ ℓ b j w β x)
    gen→low G rs = G Q rs
```

零行: 上下文作用在零上对着底值, 折叠的输出不低于底值.

```agda
    row-zero : Weak → (∀ {t} → C0 t → R j (app K t) (bt β)) → (∀ x → bt β ⊴ F x) → ∀ {t x} → C0 t → Q t x
    row-zero wk kz dom {x = x} e = wk⊴ wk (kz e) (dom x)
```

放宽: 折叠单调.

```agda
    row-weak : Weak → (∀ {x y} → x ◃ y → F x ◃ F y) → ∀ {t x x′} → Q t x → x ◃ x′ → Q t x′
    row-weak wk mono q d = wk q (mono d)
```

ℕ 极限: 参照一侧上下文保持余尾 ω, 基本列逐项穿过上下文.

```agda
    row-lim : Lim → (∀ {t} → Cω t → Cω (app K t) × (∀ n → fsn (app K t) n ≡ app K (fsn t n)))
            → ∀ {t x} → Cω t → (∀ n → Q (fsn t n) x) → Q t x
    row-lim lm cf {x = x} e h =
      lm (proj₁ (cf e)) (λ n → subst (λ s → R j s (F x)) (sym (proj₂ (cf e) n)) (h n))
```

结点保留: 槽位 p 搬到目标层的槽位 p′, 分支下标经 `mvc` 搬回; 参照一侧上下文保持余尾 Ω, 代入穿过上下文; 树一侧结点的折叠不低于逐分支折叠的结点.

```agda
    row-node-keep : Node → Weak → (p : Sl ℓ) (p′ : Sl j) (mvc : SlT j p′ → SlT ℓ p)
      → (∀ {t κ} → CΩ t κ → Nu ℓ p κ → CΩ (app K t) κ × (∀ η → fsT (app K t) η ≡ app K (fsT t η)))
      → (∀ {κ} → Nu ℓ p κ → Nu j p′ κ)
      → (∀ η c → R (slL j p′) η (slT j p′ c) → R (slL ℓ p) η (slT ℓ p (mvc c)))
      → (∀ g → nd p′ (λ c → F (g (mvc c))) ⊴ F (nd p g))
      → ∀ {t κ} (g : SlT ℓ p → Tr ℓ) → CΩ t κ → Nu ℓ p κ
      → (∀ η c → R (slL ℓ p) η (slT ℓ p c) → Q (fsT t η) (g c)) → Q t (nd p g)
    row-node-keep nod wk p p′ mvc cf nu′ rel tr g e nu h =
      wk⊴ wk
        (nod p′ (λ c → F (g (mvc c))) (proj₁ (cf e nu)) (nu′ nu)
          (λ η c l → subst (λ s → R j s (F (g (mvc c)))) (sym (proj₂ (cf e nu) η)) (h η (mvc c) (rel η c l))))
        (tr g)
```

结点对角: 上下文把余尾 Ω 降成 ω, 基本列第 k 项是代入参照链 `γ k`; 树一侧有回灌链 `z`, 链点对着参照链, 结点的折叠不低于链点分支的折叠.

```agda
    row-node-diag : Lim → Weak → (p : Sl ℓ) {t κ : T} (g : SlT ℓ p → Tr ℓ)
      → (γ : ℕ → T) (z : ℕ → SlT ℓ p)
      → Cω (app K t) → (∀ k → fsn (app K t) k ≡ app K (fsT t (γ k)))
      → (∀ k → R (slL ℓ p) (γ k) (slT ℓ p (z k)))
      → (∀ k → F (g (z k)) ⊴ F (nd p g))
      → (∀ η c → R (slL ℓ p) η (slT ℓ p c) → Q (fsT t η) (g c)) → Q t (nd p g)
    row-node-diag lm wk p g γ z cω fs ch tr h =
      lm cω (λ k → subst (λ s → R j s (F (nd p g))) (sym (fs k)) (wk⊴ wk (h (γ k) (z k) (ch k)) (tr k)))
```

## 嵌入行: 一致目标的交接

路径是 `incU ℓ c₁ ws` (对每个孩子各给一条). `HandU` 把嵌入的折叠交给孩子; 底沿嵌入交接 (`bstep`: 孩子的底与新底值对着上下文 `K′`, `app K′ s = app K (t ⊕ s)`); 孩子层上同一条保持成立. 不比较孩子.

```agda
  module UpRow {ℓ j : Lv} (b : Bs ℓ) (c₁ : Ch ℓ) (ws : (c : Ch ℓ) → j ⊑ chL ℓ c) (β : Bt j) (K : Cx ℓ j) where
    open Low b (incU ℓ c₁ ws) β K

    row-up : HandU ℓ
      → (∀ c {t x} → R ℓ t x → Q t x → Σ (Cx (chL ℓ c) j) λ K′ →
           Bd (dn ℓ b c x) (ws c) (ψβ ℓ b j (incU ℓ c₁ ws) β x) K′ × (∀ s → app K′ s ≡ app K (t ⊕ s)))
      → (∀ c (b′ : Bs (chL ℓ c)) (β′ : Bt j) (K′ : Cx (chL ℓ c) j) → Bd b′ (ws c) β′ K′
           → ∀ {s y} → R (chL ℓ c) s y → R j (app K′ s) (ψ (chL ℓ c) b′ j (ws c) β′ y))
      → (c : Ch ℓ) {t s : T} {x : Tr ℓ} (y : ChT ℓ c) → R ℓ t x → Q t x → R (chL ℓ c) s (chT ℓ c y)
      → Q (t ⊕ s) (up x c y)
    row-up hu bstep child c {t} {s} {x} y r q ry with bstep c r q
    ... | K′ , bd′ , eq =
      subst (λ o → R j (app K (t ⊕ s)) o) (sym (hu b j c₁ ws β x c y))
        (subst (λ u → R j u (ψ (chL ℓ c) (dn ℓ b c x) j (ws c) (ψβ ℓ b j (incU ℓ c₁ ws) β x) (chT ℓ c y)))
          (eq s) (child c (dn ℓ b c x) (ψβ ℓ b j (incU ℓ c₁ ws) β x) K′ bd′ ry))
```

## 折到自身

`Qs t x`: 折到自身的树对着 `cl ℓ (P ⊕ t)`. 嵌入行: 折到自身在嵌入上是上折 (底值是 x 的折叠), 参照一侧的和结合.

```agda
  module SelfRow {ℓ : Lv} (b : Bs ℓ) (β : Bt ℓ) (P : T) where

    Fs : Tr ℓ → Tr ℓ
    Fs x = ψ ℓ b ℓ self β x

    Qs : T → Tr ℓ → Set
    Qs t x = R ℓ (cl ℓ (P ⊕ t)) (Fs x)

    gen→self : Gen ℓ → Rules ℓ Qs → ∀ {a x} → R ℓ a x → R ℓ (cl ℓ (P ⊕ a)) (ψ ℓ b ℓ self β x)
    gen→self G rs = G Qs rs

    row-self-up : UpKeep → (d : (c : Ch ℓ) → Dn ℓ (chL ℓ c))
      → (∀ c x y → Fs (up x c y) ≡ upf (d c) (ψβ ℓ b ℓ self β x) (chT ℓ c y))
      → (∀ x → bt (ψβ ℓ b ℓ self β x) ≡ Fs x)
      → (∀ t s → P ⊕ (t ⊕ s) ≡ (P ⊕ t) ⊕ s)
      → (c : Ch ℓ) {t s : T} {x : Tr ℓ} (y : ChT ℓ c) → Qs t x → R (chL ℓ c) s (chT ℓ c y) → Qs (t ⊕ s) (up x c y)
    row-self-up uk d te be as c {t} {s} {x} y q ry =
      subst (λ o → R ℓ (cl ℓ (P ⊕ (t ⊕ s))) o) (sym (te c x y))
        (subst (λ u → R ℓ (cl ℓ u) (upf (d c) (ψβ ℓ b ℓ self β x) (chT ℓ c y))) (sym (as t s))
          (uk (d c) (ψβ ℓ b ℓ self β x)
            (subst (λ o → R ℓ (cl ℓ (P ⊕ t)) o) (sym (be x)) q) ry))
```

## 树读成层号

读法对六条规则封闭就给出 `Lift`. 四条读法各管一条: 零 (`Rd0`), 后继 (`RdS` 加 `ls`), ℕ 极限 (`RdL`), 结点 (`lΩ`: 结点读成 Ω 形状层号). 另两条是嵌入读成和 (`lU`) 与沿第一位置序放宽 (`lw`).

```agda
  module LiftRow (k : Lv) where

    Ql : T → Tr k → Set
    Ql s x = Rd (lift k x) s

    gen→lift : Gen k → Rd0 → RdS → RdL
      → (∀ {x ν} → Rd (sucL (lift k x)) ν → Rd (lift k (sc x)) ν)
      → ((p : Sl k) {ν κ : T} (g : SlT k p → Tr k) → CΩ ν κ → Nu k p κ
           → (∀ s c → R (slL k p) s (slT k p c) → Rd (lift k (g c)) (fsT ν s)) → Rd (lift k (nd p g)) ν)
      → ((c : Ch k) {t s : T} {x : Tr k} (y : ChT k c) → Rd (lift k x) t → R (chL k c) s (chT k c y)
           → Rd (lift k (up x c y)) (t ⊕ s))
      → (∀ {x x′ ν} → x ◃ x′ → Rd (lift k x) ν → Rd (lift k x′) ν)
      → ∀ {s x} → R k s x → Rd (lift k x) s
    gen→lift G r0 rS rL ls lΩ lU lw = G Ql (record
      { qz = λ e → r0 e
      ; q1 = λ e _ q → ls (rS e q)
      ; qL = λ e _ h → rL e h
      ; qΩ = λ p g e nu _ h → lΩ p g e nu h
      ; qU = λ c y _ q ry → lU c y q ry
      ; qw = λ _ q d → lw d q })
```

结点读成 Ω 形状层号, 由第四条读法 `RdΩ` 导出: 要分支下标取遍槽位层的一切树 (`un` 是 `slT` 的截面), 槽位允许的余尾下标不高于槽位层, 结点的层号以分支的层号为孩子族.

```agda
    node-read : RdΩ → (p : Sl k) (un : Tr (slL k p) → SlT k p) → (∀ c′ → slT k p (un c′) ≡ c′)
      → (∀ {κ} → Nu k p κ → Rd (slL k p) κ)
      → (g : SlT k p → Tr k)
      → (∀ {ν} → Rd (ΩL (slL k p) (λ c′ → lift k (g (un c′)))) ν → Rd (lift k (nd p g)) ν)
      → ∀ {ν κ} → CΩ ν κ → Nu k p κ
      → (∀ s c → R (slL k p) s (slT k p c) → Rd (lift k (g c)) (fsT ν s)) → Rd (lift k (nd p g)) ν
    node-read rΩ p un sec nuR g wkn {ν} e nu h =
      wkn (rΩ (λ c′ → lift k (g (un c′))) e (nuR nu)
        (λ s c′ l → h s (un c′) (subst (R (slL k p) s) (sym (sec c′)) l)))
```
