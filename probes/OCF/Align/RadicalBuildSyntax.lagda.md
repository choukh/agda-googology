# 全部原 Ω 行的单字段编码

新语法对普通同层子树递归编码，mark 不存 body。低层坐标暂保留原
Us/Vs 域；本篇没有完整执行器或自产 Good 证书，不能称高闭项替换完成。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.RadicalBuildSyntax (𝕊 : HtB) where
open import Data.Nat using (ℕ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ordˢ)
open import OCF.Free.Floor using (Flr; Ev; _⊔_; fk)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.RadicalBuildGenerated 𝕊

module _ (m : Ht) (α : Ordᴵ) where
  data Program : Flr → Fv → Set where
    q0   : ∀ {φ χ} → Program φ χ
    qs   : ∀ {φ χ} → Program φ χ → Program φ χ
    ql   : ∀ {φ χ} → (ℕ → Program φ χ) → Program φ χ
    qi   : ∀ {φ χ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → Program φ χ) → Program φ χ
    qŝ   : ∀ {φ χ} (c₀ : Ordᴵ) → Program φ χ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Program φ χ) → Program φ χ
    qĉ   : ∀ {φ χ} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → Program φ χ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Program φ χ) → Program φ χ
    qclo : ∀ {φ χ} → Program (φ ⊔ fk zero) χ → ((η : Ordᴵ) → Program (φ ⊔ fk η) χ) → Program (φ ⊔ fk zero) χ
    qcl  : ∀ {φ χ n} (q : n <ᴸ m) (ψ : Flr) → (∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (ψ ⊔ fk zero)) → Program φ χ → ((η : Ordᴵ) → Program φ (upd χ n (ψ ⊔ fk η))) → Program φ χ
    qwk  : ∀ {φ φ′ χ χ′} → (∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ) → Sub m χ′ χ → Program φ χ → Program φ′ χ′
    qΩ↓  : ∀ {φ χ n k} (q : n <ᴸ m) → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (∀ {ℓ} → Ev ℓ (χ n) → k <ᴵ ℓ) → (∀ ξ ζ → Vs m q k ξ ζ → Program (ξ ⊔ φ) (lo n ζ ∪ χ)) → Program φ χ
    qΩ   : ∀ {φ χ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : k <ᴵ α) → (∀ ξ ζ → Us m k (<→◃ q) ξ ζ → Program (ξ ⊔ φ) (lo m ζ ∪ χ)) → Program φ χ
    mark : ∀ {φ χ k} → (r : k ◃₁ α) → Us m k (◃₁→◃ r) φ χ → Program φ χ

compile : ∀ {m α φ χ} → Q m α φ χ → Program m α φ χ
compile q0 = q0
compile (qs x) = qs (compile x)
compile (ql f) = ql (λ n → compile (f n))
compile (qi ac f) = qi ac (λ x → compile (f x))
compile (qŝ c t g) = qŝ c (compile t) (λ η e → compile (g η e))
compile (qĉ c t g o h) = qĉ c t g (compile o) (λ η e → compile (h η e))
compile (qclo t g) = qclo (compile t) (λ η → compile (g η))
compile (qcl q ψ s t g) = qcl q ψ s (compile t) (λ η → compile (g η))
compile (qwk le lc x) = qwk le lc (compile x)
compile (qΩ↓ q fe ac h) = qΩ↓ q fe ac (λ ξ ζ z → compile (h ξ ζ z))
compile (qΩ fe r h) = qΩ fe r (λ ξ ζ z → compile (h ξ ζ z))
compile (omk r z x) = mark r z

-- compile 对裸不平衡输入可能改变读法；实际全 Ω 行有已证准入。
floor-program : ∀ m α → Program m α Fl (κ Fl)
floor-program m α = compile (Ω̇ m α)

floor-admitted : ∀ m α → Balanced (Ω̇ m α)
floor-admitted = omega-balanced
```

完整 encode 不只一个首标记：包含所有 rowC/rowL 的子树和所有高阶
回调的结果。尚未编码低层坐标载体，也未证明任意 compile 源保值。
已证值方程只在 Kernel 的单字段执行和全部原生成标记分支处。
