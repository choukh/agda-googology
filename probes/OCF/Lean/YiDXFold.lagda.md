# 定义改动的候选原型: 字面地板保留与上折回退

> 定义候选, 未经作者采纳, 不进主线; 不读记号. 折叠复制自 `YiTBRow` (表与 `dW` 照搬), 改两处, 各由一个开关决定: (A) 保留判定 `K` 作模块参数, 候选 `kpᴬ` 在 `kp` 走链且槽位层号字面是第 0 层、目标非零时, 在目标的地板槽位保留; (B) 表缺项的退路行 (`lifted = true`) 把孩子树上折进本层再朝原目标折 (`ψˡ`), 不再折到第 0 层加可数尾巴.
> 合法性是类型, 单调 `mono`、`monoˡ` 对一切 `K`、两种开关编译. Ω 形状行上 `kpᴬ` 与目标经过哪个孩子无关 (`rowA`, `rowA-indep`), 原有的保留不变 (`keep-kp`), 退路两种写法的形状是 `refl` (`row-fb`, `row-lift`); 闭项 `twᴬᴮ`, `EBOᴬᴮ`.
> 不否定什么; 不处理槽位层号非零的情形 (塔第 1 项前缀下 d ≥ 2 仍走链, 见 `YiDXTest`). 测试在 [YiDXTest](YiDXTest.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDXFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; node⁺; nodeLe)
open import OCF.Lean.YiTBRow using (Rb; dW; dW-ind; dW-ind₂)
open import OCF.Lean.YiMTTab using (rbᶻ)
```

## (A) 字面地板保留

`flr a f j`: 槽位层号 a 字面是第 0 层且目标 j 非零时, 取 j 沿第一孩子降到第 0 层的槽位 (`psh (z≤ …)`), 换型是 `pshBr`; 其余情形不保留. 第 0 层低于一切非零层号, 这是 "低于目标保留" 在字面可知处的实例.

```agda
KeepFn : Set
KeepFn = (ℓ : L) → Ok ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Keep j (Br ℓ p) (fromBr ℓ p zero)

alt : ∀ {j X x₀} → Keep j X x₀ → Keep j X x₀ → Keep j X x₀
alt (just K) m = just K
alt nothing  m = m

flr : (a : L) {X : Set} (f : Tr a → X) (j : L) → Keep j X (f zero)
flr zero     f zero     = nothing
flr zero     f (nd s h) = just (inj₂ (c₀ s , psh (z≤ (h (c₀ s))) (inj₁ tt)) ,
  (λ z → f (pshBr (z≤ (h (c₀ s))) (inj₁ tt) z)) , cong f (pshFirst (z≤ (h (c₀ s))) (inj₁ tt)))
flr (nd _ _) f j        = nothing

kpᴬ : KeepFn
kpᴬ ℓ o p {j} w = alt (kp ℓ o p w) (flr (at ℓ p) (fromBr ℓ p) j)
```

Ω 形状层号, 槽位在孩子 c, 目标经孩子 c′: 结果只看槽位的层号与目标 j, 不看 c′ 与孩子里的路径.

```agda
rowA : ∀ k h (o : Ok (nd (sΩ k) h)) c t {j} c′ (v : j ≤ h c′)
  → kpᴬ (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) ≡ flr (proj₁ (sl⁼ (h c) t)) (fromBr (nd (sΩ k) h) (inj₂ (c , t))) j
rowA k h o c t c′ v = refl

rowA-indep : ∀ k h (o : Ok (nd (sΩ k) h)) c t {j} c′ c″ (v : j ≤ h c′) (v′ : j ≤ h c″)
  → kpᴬ (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) ≡ kpᴬ (nd (sΩ k) h) o (inj₂ (c , t)) (inc c″ v′)
rowA-indep k h o c t c′ c″ v v′ = refl

keep-kp : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) (K : Σ (Pos j) λ q → Σ (Br j q → Br ℓ p) λ cv → cv (fromBr j q zero) ≡ fromBr ℓ p zero)
  → kp ℓ o p w ≡ just K → kpᴬ ℓ o p w ≡ just K
keep-kp ℓ o p w K e rewrite e = refl
```

## 折叠

`ψ` 逐行复制 `YiTBRow.ψ`, 只把 `kp` 换成 `K`, 把表缺项的退路写成 `sel lifted …` (两种写法都算出, 由开关选一个; 不另设互递归的函数, 以免层号参数在调用链上丢失). `ψˡ ℓ o X j w β a d y`: 第 a 层 (经下行链 d 在 ℓ 之下) 的树 y 当作上折进 ℓ 的树, 朝 j 折; X 是前缀 x 朝各低层的折叠, 结点的回灌从 X 起步, 所以回灌折的是 "x 加上折后的分支". 嵌入 `up` 沿链下行, 与 `Up` 同形.

```agda
sel : {X : Set} → Bool → X → X → X
sel false a b = a
sel true  a b = b

sel-ind : {X : Set} (Q : X → Set) (l : Bool) {a b : X} → Q a → Q b → Q (sel l a b)
sel-ind Q false qa qb = qa
sel-ind Q true  qa qb = qb

sel-ind₂ : {X : Set} (Q : X → X → Set) (l : Bool) {a a′ b b′ : X} → Q a a′ → Q b b′ → Q (sel l a b) (sel l a′ b′)
sel-ind₂ Q false qa qb = qa
sel-ind₂ Q true  qa qb = qb

module Fold (K : KeepFn) (lifted : Bool) where
  mutual
    ψ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
    ψ ℓ o r B j w β zero      = β
    ψ ℓ o r B j w β (suc x)   = next⁺ (ψ ℓ o r B j w β x)
    ψ ℓ o r B j w β (lim f a) = lim⁺ (λ n → ψ ℓ o r B j w β (f n)) (λ n → mono ℓ o r B j w β (a n))
    ψ ℓ o r B j w β (Ω p g)   = node⁺ (K ℓ o p w) (λ z → ψ ℓ o r B j w β (g z))
      (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
    ψ (nd s h) o r B _ self β (up x c y e) = Up (h c) (down stop c) (ψ (nd s h) o r B _ self β x) y
    ψ (nd s h) o r B j (inu ws) β (up x c y e) =
      ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) y
    ψ (nd (sΩ k) h) o r B j (ink v) β (up x c y e) =
      ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ (nd (sΩ k) h) o r B j (ink v) β x) y
    ψ (nd sS h) o r B j (inc c′ v) β (up x c y e) =
      ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) y
    ψ (nd sL g) o r B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
      (λ u → ψ (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o r B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → ψ (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o r B j (inc n v) β x) y)
    ψ (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e) = dW (proj₁ r c c′)
      (λ u → ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
               (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) y)
      (λ u → ψ (h c′) (proj₂ o c′) (proj₂ r c′) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ u′) (B i (inc c′ u′)) x) j v
               (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (proj₁ (emb (h c′) (proj₂ o c′) u (y , e))))
      (sel lifted (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)
                  (ψˡ (nd (sΩ k) h) o (λ i u → ψ (nd (sΩ k) h) o r B i u (B i u) x) j (inc c′ v)
                     (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (h c) (down stop c) y))

    ψˡ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → (a : L) → Dn ℓ a → Tr a → Tr⁺ j
    ψˡ ℓ o X j w β a d zero      = β
    ψˡ ℓ o X j w β a d (suc y)   = next⁺ (ψˡ ℓ o X j w β a d y)
    ψˡ ℓ o X j w β a d (lim f e) = lim⁺ (λ n → ψˡ ℓ o X j w β a d (f n)) (λ n → monoˡ ℓ o X j w β a d (e n))
    ψˡ ℓ o X j w β a d (Ω p g)   = node⁺ (K ℓ o (mv d p) w) (λ z → ψˡ ℓ o X j w β a d (g (mvBr d p z)))
      (λ z → fromBr ℓ (mv d p) (proj₁ (ψˡ ℓ o X (at ℓ (mv d p)) (posW ℓ (mv d p)) (X (at ℓ (mv d p)) (posW ℓ (mv d p)))
                                        a d (g (mvBr d p z)))))
    ψˡ ℓ o X j w β (nd s h) d (up y c y′ e) =
      ψˡ ℓ o (λ i u → ψˡ ℓ o X i u (X i u) (nd s h) d y) j w (ψˡ ℓ o X j w β (nd s h) d y) (h c) (down d c) y′

    monoˡ : (ℓ : L) (o : Ok ℓ) (X : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (a : L) (d : Dn ℓ a) {x y : Tr a}
          → a ⊢ x ◃ y → j ⊢ proj₁ (ψˡ ℓ o X j w β a d x) ◃ proj₁ (ψˡ ℓ o X j w β a d y)
    monoˡ ℓ o X j w β a d ◃s     = ◃l zero
    monoˡ ℓ o X j w β a d (◃l n) = ◃l n
    monoˡ ℓ o X j w β a d (◃w {p = p} {g = g}) =
      subst (λ t → j ⊢ proj₁ (ψˡ ℓ o X j w β a d (g t)) ◃ proj₁ (ψˡ ℓ o X j w β a d (Ω p g))) (mvFirst d p)
        (nodeLe (K ℓ o (mv d p) w) (λ z → ψˡ ℓ o X j w β a d (g (mvBr d p z)))
          (λ z → fromBr ℓ (mv d p) (proj₁ (ψˡ ℓ o X (at ℓ (mv d p)) (posW ℓ (mv d p)) (X (at ℓ (mv d p)) (posW ℓ (mv d p)))
                                             a d (g (mvBr d p z))))))
    monoˡ ℓ o X j w β (nd s h) d (◃u x c y e) =
      monoˡ ℓ o (λ i u → ψˡ ℓ o X i u (X i u) (nd s h) d x) j w (ψˡ ℓ o X j w β (nd s h) d x) (h c) (down d c) e
    monoˡ ℓ o X j w β (nd s h) d (◃c x c r) =
      monoˡ ℓ o (λ i u → ψˡ ℓ o X i u (X i u) (nd s h) d x) j w (ψˡ ℓ o X j w β (nd s h) d x) (h c) (down d c) r
    monoˡ ℓ o X j w β a d (◃t e f) = ◃t (monoˡ ℓ o X j w β a d e) (monoˡ ℓ o X j w β a d f)

    mono : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
         → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o r B j w β x) ◃ proj₁ (ψ ℓ o r B j w β y)
    mono ℓ o r B j w β ◃s           = ◃l zero
    mono ℓ o r B j w β (◃l n)       = ◃l n
    mono ℓ o r B j w β (◃w {p = p}) = nodeLe (K ℓ o p w) _ _
    mono (nd s h) o r B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) e
    mono (nd s h) o r B j (inu ws) β (◃u x c y e) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) e
    mono (nd (sΩ k) h) o r B j (ink v) β (◃u x c y e) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ (nd (sΩ k) h) o r B j (ink v) β x) e
    mono (nd sS h) o r B j (inc c′ v) β (◃u x c y e) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) e
    mono (nd sL g) o r B j (inc n v) β (◃u x m y e) =
      cW-ind (λ Z → j ⊢ proj₁ (ψ (nd sL g) o r B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
        (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
                 (ψ (nd sL g) o r B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
        (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
                 (ψ (nd sL g) o r B j (inc n v) β x) e)
    mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃u x c y e) =
      dW-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (proj₁ r c c′)
        (λ u → mono (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
                 (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) e)
        (λ u → mono (h c′) (proj₂ o c′) (proj₂ r c′) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ u′) (B i (inc c′ u′)) x) j v
                 (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (proj₂ (emb (h c′) (proj₂ o c′) u (y , e))))
        (sel-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) lifted
          (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))
          (monoˡ (nd (sΩ k) h) o (λ i u → ψ (nd (sΩ k) h) o r B i u (B i u) x) j (inc c′ v)
            (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (h c) (down stop c) e))
    mono (nd s h) o r B _ self β (◃c x c d) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) d
    mono (nd s h) o r B j (inu ws) β (◃c x c d) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) d
    mono (nd (sΩ k) h) o r B j (ink v) β (◃c x c d) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ (nd (sΩ k) h) o r B j (ink v) β x) d
    mono (nd sS h) o r B j (inc c′ v) β (◃c x c d) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) d
    mono (nd sL g) o r B j (inc n v) β (◃c x m d) =
      cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
        (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
                 (ψ (nd sL g) o r B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u d))
        (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
                 (ψ (nd sL g) o r B j (inc n v) β x) d)
    mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃c x c d) =
      dW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (proj₁ r c c′)
        (λ u → mono (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
                 (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) d)
        (λ u → mono (h c′) (proj₂ o c′) (proj₂ r c′) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ u′) (B i (inc c′ u′)) x) j v
                 (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (emb-mono (h c′) (proj₂ o c′) u d))
        (sel-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) lifted
          (+-mono _ (ι-mono j (mono (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d)))
          (monoˡ (nd (sΩ k) h) o (λ i u → ψ (nd (sΩ k) h) o r B i u (B i u) x) j (inc c′ v)
            (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (h c) (down stop c) d))
    mono ℓ o r B j w β (◃t d d′) = ◃t (mono ℓ o r B j w β d) (mono ℓ o r B j w β d′)
```

## 退路行的两种形状, 三个候选

```agda
row-fb : ∀ (K : KeepFn) k h (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) β x c y e
  → Fold.ψ K false (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B j (inc c′ v) β (up x c y e)
  ≡ Fold.ψ K false (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B j (inc c′ v) β x
    ⊞ Fold.ψ K false (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y
row-fb K k h o rc B j c′ v β x c y e = refl

row-lift : ∀ (K : KeepFn) k h (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) β x c y e
  → Fold.ψ K true (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B j (inc c′ v) β (up x c y e)
  ≡ Fold.ψˡ K true (nd (sΩ k) h) o (λ i u → Fold.ψ K true (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B i u (B i u) x) j (inc c′ v)
      (Fold.ψ K true (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B j (inc c′ v) β x) (h c) (down stop c) y
row-lift K k h o rc B j c′ v β x c y e = refl

module FA  = Fold kpᴬ false
module FB  = Fold kp  true
module FAB = Fold kpᴬ true
```

闭项: 最小表 `rbᶻ`, 默认底, 目标第 0 层.

```agda
twᴬᴮ : ℕ → Tr zero
twᴬᴮ n = proj₁ (FAB.ψ (tw n) (Ok-tw n) (rbᶻ (tw n)) (B₀ (tw n)) zero (z≤ (tw n)) (Ωt zero) (proj₁ (Ωt (tw n))))

EBOᴬᴮ : Tr zero
EBOᴬᴮ = proj₁ (FAB.ψ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) zero (z≤ Λ) (Ωt zero) (proj₁ (Ωt Λ)))
```
